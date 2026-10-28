-- Prove2me | solution 1 for OAI.KServer.JointBudget.quota_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T15:01:52.481797+00:00
-- url     : https://prove2.me/submissions/395e38b5-6a06-401c-9c42-7de3af3b8729

import Mathlib
import Definitions.Def_KServer
import Definitions.Def_OAIQ17Ks000

section
-- module Solutions.OAIQ17_KS.KServer_Ranks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
namespace KServer.RankTracking

variable {Ω : Type*} [Fintype Ω]

lemma avg_add (w f g : Ω → ℝ) : avg w (fun ω => f ω+g ω)=avg w f+avg w g := by
  simp [avg,mul_add,sum_add_distrib]
lemma avg_mul (w f : Ω → ℝ) (c : ℝ) : avg w (fun ω => c*f ω)=c*avg w f := by
  simp only [avg,mul_sum,mul_left_comm (w _) c]
lemma avg_sum (w : Ω → ℝ) {ι : Type*} [Fintype ι] (f : ι → Ω → ℝ) :
    avg w (fun ω => ∑ i, f i ω)=∑ i, avg w (f i) := by
  simp only [avg,mul_sum]; rw [sum_comm]
lemma avg_mono {w f g : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (h : ∀ ω, f ω ≤ g ω) :
    avg w f ≤ avg w g := sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (hw ω)
lemma avg_const (w : Ω → ℝ) (hw : ∑ ω, w ω=1) (c : ℝ) : avg w (fun _ => c)=c := by
  simp [avg,←sum_mul,hw]

lemma filtering_affine {w : Ω → ℝ} (R : FilteredRanks w) (t : ℕ) (f : Ω → ℝ)
    (hf : Adapted (R.history t) f) :
    avg w (fun ω => f ω*(R.before (t+1) ω-R.p t ω))=0 := by
  unfold avg
  simp_rw [mul_left_comm (w _) (f _)]
  exact fiber_weighted_zero (R.history t) f _ hf (R.filtering t)

end KServer.RankTracking

/-! Construction of the rank martingales from the actual finite hidden law.
No filtering identity is postulated in the construction below. -/
namespace KServer.PosteriorRanks
open Finset
open RankTracking
variable {Ω : Type*} [Fintype Ω]

lemma posterior_avg {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (H : Ω → ℕ) (f : Ω → ℝ) :
    avg w (posterior w H f)=avg w f := by
  simpa only [one_mul] using weighted_posterior hw H f (fun _ => 1) (by intro _ _ _; rfl)

lemma posterior_sub (w : Ω → ℝ) (H : Ω → ℕ) (f g : Ω → ℝ) (ω : Ω) :
    posterior w H (fun z => f z-g z) ω = posterior w H f ω-posterior w H g ω := by
  simp only [posterior,numerator,mul_sub,sum_sub_distrib,sub_div]

lemma abs_posterior_le {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (H : Ω → ℕ) (f : Ω → ℝ) (ω : Ω) :
    |posterior w H f ω| ≤ posterior w H (fun z => |f z|) ω := by
  have hn : |numerator w H f (H ω)| ≤ numerator w H (fun z => |f z|) (H ω) := by
    unfold numerator
    calc _ ≤ ∑ z ∈ fiber H (H ω), |w z*f z| := abs_sum_le_sum_abs _ _
         _ = _ := by apply sum_congr rfl; intro z _; rw [abs_mul,abs_of_nonneg (hw z)]
  unfold posterior
  rw [abs_div,abs_of_nonneg (mass_nonneg hw H (H ω))]
  exact div_le_div_of_nonneg_right hn (mass_nonneg hw H (H ω))

/-- Conditional averaging cannot increase the drift, even at zero-mass
histories, where the quotient convention simply chooses zero. -/
theorem posterior_drift {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (H : Ω → ℕ) (f g : Ω → ℝ) :
    avg w (fun ω => |posterior w H f ω-posterior w H g ω|) ≤
      avg w (fun ω => |f ω-g ω|) := by
  calc _ = avg w (fun ω => |posterior w H (fun z => f z-g z) ω|) := by simp only [posterior_sub]
       _ ≤ avg w (posterior w H (fun z => |f z-g z|)) :=
        avg_mono hw (abs_posterior_le hw H (fun z => f z-g z))
       _ = _ := posterior_avg hw H _

lemma sum_below {k N : ℕ} (hN : N ≤ k) :
    (∑ a : Fin k, if a.val < N then (1 : ℝ) else 0) = N := by
  rw [Fin.sum_univ_eq_sum_range (fun a => if a < N then (1 : ℝ) else 0), ← sum_filter]
  have h : (range k).filter (fun a => a < N) = range N := by
    ext a
    simp only [mem_filter, mem_range]
    omega
  rw [h]
  simp

lemma sum_above {k N : ℕ} (hN : N ≤ k) :
    (∑ a : Fin k, if N ≤ a.val then (1 : ℝ) else 0) = (k:ℝ)-N := by
  have hsum : (∑ a : Fin k, if N ≤ a.val then (1 : ℝ) else 0)+
      (∑ a : Fin k, if a.val < N then (1 : ℝ) else 0) = k := by
    rw [←sum_add_distrib]
    have hterm (a : Fin k) : (if N ≤ a.val then (1:ℝ) else 0)+(if a.val < N then (1:ℝ) else 0)=1 := by
      split_ifs <;> first | (exfalso; omega) | norm_num
    simp_rw [hterm]
    simp
  rw [sum_below hN] at hsum
  linarith

lemma indicator_count_distance {k n m : ℕ} (hn : n ≤ k) (hm : m ≤ k) :
    (∑ a : Fin k, |(if n ≤ a.val then (1:ℝ) else 0)-(if m ≤ a.val then (1:ℝ) else 0)|) =
      |(n:ℝ)-m| := by
  wlog hnm : n ≤ m generalizing n m
  · rw [abs_sub_comm (n:ℝ) m]
    rw [←this hm hn (le_of_not_ge hnm)]
    exact sum_congr rfl fun a _ => abs_sub_comm _ _
  have hnmR : (n:ℝ) ≤ m := by exact_mod_cast hnm
  calc _ = ∑ a : Fin k, ((if n ≤ a.val then (1:ℝ) else 0)-(if m ≤ a.val then (1:ℝ) else 0)) := by
        apply sum_congr rfl
        intro a _
        apply abs_of_nonneg
        split_ifs <;> first | (exfalso; omega) | norm_num
       _ = (m:ℝ)-n := by rw [sum_sub_distrib,sum_above hn,sum_above hm]; ring
       _ = |(n:ℝ)-m| := by rw [abs_of_nonpos (sub_nonpos.mpr hnmR)]; ring

/-- The exact §03 all-rank drift budget, derived from the finite hidden count
process rather than assumed as an interface. -/
theorem rank_drift_count {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (H : Ω → ℕ) {k : ℕ} (N M : Ω → ℕ) (hN : ∀ ω, N ω ≤ k) (hM : ∀ ω, M ω ≤ k) :
    (∑ a : Fin k, avg w (fun ω => |posterior w H (rank N a.val) ω-
      posterior w H (rank M a.val) ω|)) ≤ avg w (fun ω => |(N ω:ℝ)-M ω|) := by
  calc _ ≤ ∑ a : Fin k, avg w (fun ω => |rank N a.val ω-rank M a.val ω|) :=
          sum_le_sum fun a _ => posterior_drift hw H _ _
       _ = avg w (fun ω => ∑ a : Fin k, |rank N a.val ω-rank M a.val ω|) :=
          (avg_sum w _).symm
       _ = _ := by
          congr 1
          funext ω
          exact indicator_count_distance (hN ω) (hM ω)

/-- The instantiated process defined above obeys the source estimate with
actual one-step hidden-count motion on its right-hand side. -/
theorem rankProcess_drift {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (H : ℕ → Ω → ℕ) (hr : ∀ t ω z, H (t+1) ω=H (t+1) z → H t ω=H t z)
    {k : ℕ} (N : ℕ → Ω → ℕ) (hN : ∀ t ω, N t ω ≤ k) (t : ℕ) :
    (∑ a : Fin k, avg w (fun ω => |(rankProcess hw H hr N a.val).p (t+1) ω-
      (rankProcess hw H hr N a.val).before (t+1) ω|)) ≤
      avg w (fun ω => |(N (t+1) ω:ℝ)-N t ω|) := by
  simpa only [rankProcess,Nat.add_sub_cancel] using
    rank_drift_count hw (H (t+1)) (N (t+1)) (N t) (hN (t+1)) (hN t)

end KServer.PosteriorRanks


/-! ## The actual finite hidden experiment of §02

The input is drawn once. Its selected optimum is hidden, whereas a finite
independent partition tape and the true request prefix are observed. No
conditioning on rounding outcomes enters this experiment. -/

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Minimization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
namespace KServer.AdaptiveMinimization
open Finset KServer.RankTracking
variable {I J Θ : Type*} [Fintype I] [Fintype J]

lemma avg_sum_any {Ω : Type} [Fintype Ω] (w : Ω → ℝ) {ι : Type*} [Fintype ι] (f : ι → Ω → ℝ) :
    avg w (fun ω => ∑ i, f i ω)=∑ i, avg w (f i) := by
  simp only [avg,mul_sum]; rw [sum_comm]

lemma movement_self (a : J → ℝ) : movement a a=0 := by simp [movement]

lemma Family.update_payment (F : Family Θ I J) (θ : Θ) (p : I → ℝ) (c : ℝ)
    {a : J → ℝ} (ha : a ∈ F.domain θ) :
    c*movement (F.update θ p c a) a ≤ F.value θ p a-F.value θ p (F.update θ p c a) := by
  have h := (F.exists_update θ p c a).choose_spec.2 ha
  change F.value θ p (F.update θ p c a)+c*movement (F.update θ p c a) a ≤
    F.value θ p a+c*movement a a at h
  rw [movement_self,mul_zero,add_zero] at h
  linarith

lemma Family.input_difference (F : Family Θ I J) (θ : Θ) (p q : I → ℝ) (a : J → ℝ) :
    F.value θ p a-F.value θ q a=∑ i, F.coefficient θ a i*(p i-q i) := by
  simp only [Family.value,mul_sub,sum_sub_distrib]
  ring

lemma Family.input_lipschitz (F : Family Θ I J) (θ : Θ) (p q : I → ℝ)
    (a : J → ℝ) {L : ℝ} (hL : ∀ i, |F.coefficient θ a i| ≤ L) :
    |F.value θ p a-F.value θ q a| ≤ L*∑ i, |p i-q i| := by
  rw [F.input_difference,mul_sum]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hL i) (abs_nonneg _))

variable {Ω : Type} [Fintype Ω]

omit [Fintype Ω] in
/-- Causality is proved from the recursion (not a fictitious prefix interface). -/
lemma state_adapted (F : Family Θ I J) (T : Transport F) (θ : ℕ → Ω → Θ)
    (p : ℕ → Ω → I → ℝ) (c : ℕ → Ω → ℝ) (H : ℕ → Ω → ℕ)
    (hr : ∀ t ω z, H (t+1) ω=H (t+1) z → H t ω=H t z)
    (hθ : ∀ t ω z, H t ω=H t z → θ t ω=θ t z)
    (hp : ∀ t ω z, H t ω=H t z → p t ω=p t z)
    (hc : ∀ t, Adapted (H t) (c t)) :
    ∀ t ω z, H t ω=H t z → state F T θ p c t ω=state F T θ p c t z := by
  intro t
  induction t with
  | zero =>
      intro ω z hz
      exact congrArg (fun u => (F.seed u).val) (hθ 0 ω z hz)
  | succ t ih =>
      intro ω z hz
      have hprev := hr t ω z hz
      simp only [state,hθ (t+1) ω z hz,hp (t+1) ω z hz,hc (t+1) ω z hz,
        hθ t ω z hprev,ih ω z hprev]

end KServer.AdaptiveMinimization


/-! Actual zero-extension and synthetic-input operations in §04.  In particular
zero weight and singleton transitions are included, not divided away. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ChangingDomains
variable {J R : Type*} [Fintype J] [DecidableEq J] [Fintype R]

omit [DecidableEq J] in
lemma variation_self (a : J → ℝ) : variation a a=0 := by simp [variation]
omit [DecidableEq J] in
lemma variation_triangle (a b c : J → ℝ) : variation a c ≤ variation a b+variation b c := by
  rw [variation,variation,variation,←sum_add_distrib]
  exact sum_le_sum fun i _ => abs_sub_le _ _ _

omit [DecidableEq J] in
lemma simplex_variation {A B : Finset J} {a b : J → ℝ}
    (ha : a ∈ simplex A) (hb : b ∈ simplex B) : variation a b ≤ 2 := by
  calc _ ≤ ∑ i, (a i+b i) := sum_le_sum fun i _ => by
        calc |a i-b i| ≤ |a i|+|b i| := abs_sub _ _
             _ = _ := by rw [abs_of_nonneg (ha.1 i),abs_of_nonneg (hb.1 i)]
       _ ≤ 2 := by
        rw [sum_add_distrib,ha.2.1,hb.2.1]
        split_ifs <;> norm_num

lemma transposeSimplex_mem {A B : Finset J} {S : ℝ} {a v γ : J → ℝ}
    (hA : A.Nonempty) (hB : B.Nonempty) (ha : a ∈ simplex A) (hS : 0 ≤ S)
    (hc : ∀ i, S*a i ≤ γ i*v i) (hv : ∀ i ∉ B, v i=0) :
    transposeSimplex B S a ∈ simplex B := by
  by_cases hs : S=0
  · simpa [transposeSimplex,hs] using canonical_mem B
  · have hsp : 0 < S := lt_of_le_of_ne hS (Ne.symm hs)
    simp only [transposeSimplex,ite_eq_right hs]
    refine ⟨ha.1,?_,?_⟩
    · simpa only [ite_eq_left hA,ite_eq_left hB] using ha.2.1
    · intro i hi
      have hh := hc i
      rw [hv i hi,mul_zero] at hh
      nlinarith [ha.1 i]

lemma transposeSimplex_payment (A : Finset J) (S : ℝ) (a : J → ℝ) :
    S*variation (transposeSimplex A S a) a=0 := by
  by_cases h : S=0
  · simp [h]
  · simp [transposeSimplex,h,variation_self]

omit [DecidableEq J] in
/-- Literal §04 weight comparison for the prepared and final minimizers. -/
lemma prepared_weight_comparison {A₀ A₁ A₂ : Finset J} {a₀ a₁ a₂ a₃ : J → ℝ}
    (ha₀ : a₀ ∈ simplex A₀) (ha₁ : a₁ ∈ simplex A₁)
    (ha₂ : a₂ ∈ simplex A₂)
    {S T : ℝ} (hS : 0 ≤ S) (hST : S ≤ T)
    (hzero : S*variation a₂ a₁=0) :
    T*variation a₃ a₀ ≤ S*variation a₁ a₀+T*variation a₃ a₂+4*(T-S) := by
  have ht := variation_triangle a₃ a₂ a₀
  have ht' := variation_triangle a₂ a₁ a₀
  have hd₁ := simplex_variation ha₁ ha₀
  have hd₂ := simplex_variation ha₂ ha₁
  have htn : 0 ≤ T := hS.trans hST
  have hp := mul_le_mul_of_nonneg_left ht htn
  have hp' := mul_le_mul_of_nonneg_left ht' htn
  have hδ : 0 ≤ T-S := sub_nonneg.mpr hST
  have h₁ := mul_le_mul_of_nonneg_left hd₁ hδ
  have h₂ := mul_le_mul_of_nonneg_left hd₂ hδ
  nlinarith

lemma transposeSide_payment {B : Finset J} {D : ℝ} {a v γ : J → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hD : 0 ≤ D)
    (hc : ∀ i, D*a i ≤ γ i*v i) (hv : ∀ i ∉ B, v i=0) :
    D*variation (transposeSide B a) a=0 := by
  by_cases hd : D=0
  · simp [hd]
  · have hdp : 0 < D := lt_of_le_of_ne hD (Ne.symm hd)
    have he : transposeSide B a=a := by
      funext i
      by_cases hi : i∈B
      · simp [transposeSide,hi]
      · have hh := hc i
        rw [hv i hi,mul_zero] at hh
        have haz : a i=0 := by nlinarith [ha i]
        simp [transposeSide,hi,haz]
    simp [he,variation_self]

omit [Fintype J] in
lemma synthetic_zero {A B : Finset J} (f : J → R → Bool) (p : J → R → ℝ)
    {i : J} (hi : i∉A∩B) : core (syntheticFlags A B f) p i=0 := by
  simp [core,syntheticFlags,hi]

omit [Fintype J] [Fintype R] in
lemma synthetic_error_terms {A B : Finset J} {f g : J → R → Bool}
    {p : J → R → ℝ} (hp : ∀ i a, p i a ∈ Set.Icc 0 1)
    (hf : ∀ i ∉ A, ∀ a, f i a=false) (hg : ∀ i ∉ B, ∀ a, g i a=false)
    (i : J) (a : R) :
    |(if f i a then p i a else 0)-(if syntheticFlags A B g i a then p i a else 0)| ≤
      (if f i a=g i a then (0:ℝ) else 1) ∧
    |(if g i a then p i a else 0)-(if syntheticFlags A B g i a then p i a else 0)| ≤
      (if f i a=g i a then (0:ℝ) else 1) := by
  have hn := (hp i a).1
  have hu := (hp i a).2
  by_cases hi : i∈A <;> by_cases hj : i∈B
  · cases hfi : f i a <;> cases hgi : g i a <;>
      simp [syntheticFlags,hi,hj,hgi,abs_of_nonneg hn,abs_of_nonpos (neg_nonpos.mpr hn),hu]
  · have hgi := hg i hj a
    cases hfi : f i a <;>
      simp [syntheticFlags,hi,hj,hgi,abs_of_nonneg hn,hu]
  · have hfi := hf i hi a
    cases hgi : g i a <;>
      simp [syntheticFlags,hi,hj,hfi,abs_of_nonneg hn,hu]
  · have hfi := hf i hi a
    have hgi := hg i hj a
    simp [syntheticFlags,hi,hj,hfi,hgi]

/-- Both synthetic-core discrepancies are paid by the actual number of flags
that changed, even when the observed rank probabilities changed drastically. -/
theorem synthetic_errors {A B : Finset J} {f g : J → R → Bool}
    {p : J → R → ℝ} (hp : ∀ i a, p i a ∈ Set.Icc 0 1)
    (hf : ∀ i ∉ A, ∀ a, f i a=false) (hg : ∀ i ∉ B, ∀ a, g i a=false) :
    variation (core f p) (core (syntheticFlags A B g) p) ≤ changedFlags f g ∧
    variation (core g p) (core (syntheticFlags A B g) p) ≤ changedFlags f g := by
  constructor
  all_goals
    apply sum_le_sum
    intro i _
    unfold core
    rw [←sum_sub_distrib]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro a _
  · exact (synthetic_error_terms hp hf hg i a).1
  · exact (synthetic_error_terms hp hf hg i a).2

lemma synthetic_total {A B : Finset J} {g : J → R → Bool} {p : J → R → ℝ}
    (hp : ∀ i a, 0 ≤ p i a) :
    0 ≤ (∑ i, core g p i)-(∑ i, core (syntheticFlags A B g) p i) := by
  apply sub_nonneg.mpr
  apply sum_le_sum
  intro i _
  by_cases hi : i∈A∩B
  · simp [core,syntheticFlags,hi]
  · rw [synthetic_zero g p hi]
    exact core_nonneg hp i

end KServer.ChangingDomains

end
end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Simplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Finset

/-! Exact analytic kernels of §04, necessary for the simplex minimization.
Only the point values of integrands at zero are irrelevant to the integrals. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace KServer.SimplexAnalytic

lemma regularTail_zero (h : ℝ) : regularTail h 0 = 0 := by simp [regularTail]

lemma regular_singular_integral {h : ℝ} (hh : 0 < h) :
    ∫ s in (0 : ℝ)..1, singularKernel (regularF h) s = 1 := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (show (0 : ℝ) ≤ 1 by norm_num)
    (regularTail_continuousOn hh)
    (fun s (hs : s ∈ Set.Ioo 0 1) => by
      rw [regular_singular_formula]
      exact regularTail_derivative hh ⟨hs.1, hs.2.le⟩)
    (regular_singular_intervalIntegrable hh)
  simpa [regularTail, hh.ne'] using he

lemma affineLogTail_derivative {u H s : ℝ} (hu : 0 < u) (hH : 0 < H)
    (hs : s ∈ Set.Ioc 0 1) :
    HasDerivAt (affineLogTail u H) (1 / (s * (u - H * Real.log s))) s := by
  have hx : 0 < u - H * Real.log s := by
    have := mul_nonpos_of_nonneg_of_nonpos hH.le (Real.log_nonpos hs.1.le hs.2)
    linarith
  have hd := (((hasDerivAt_const s u).sub
    ((Real.hasDerivAt_log hs.1.ne').const_mul H)).log hx.ne').neg.div_const H
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | (dsimp; field_simp [hH.ne', hs.1.ne', hx.ne']; ring)

lemma marked_lower_half_bound {u H s : ℝ} (hu : 0 ≤ u) (hH : 0 < H)
    (hs : s ∈ Set.Icc 0 (Real.exp (-1))) :
    singularKernel (markedF u H) s ≤ (4 / H) * singularKernel (regularF 1) s := by
  rcases eq_or_lt_of_le hs.1 with hz | hp
  · subst s; simp [singularKernel]
  have hy : 1 ≤ Real.log (1 / s) := by
    have ht := Real.log_le_log hp hs.2
    rw [Real.log_exp] at ht
    rw [one_div, Real.log_inv]
    linarith
  have hden : (H / 4) * (1 + Real.log (1 / s))^2 ≤ markedF u H (Real.log (1 / s)) := by
    dsimp [markedF]
    have hq : (1 + Real.log (1 / s))^2 ≤ 4 * Real.log (1 / s) * (1 + Real.log (1 / s)) := by
      nlinarith
    have := mul_le_mul_of_nonneg_left hq hH.le
    nlinarith
  have hpos : 0 < (H / 4) * (1 + Real.log (1 / s))^2 := by positivity
  have hi := div_le_div_of_nonneg_right (one_div_le_one_div_of_le hpos hden) hp.le
  have he : (1 / ((H / 4) * (1 + Real.log (1 / s))^2)) / s =
      (4 / H) * singularKernel (regularF 1) s := by
    dsimp [singularKernel, kernel, regularF]
    simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
    ring
  rw [he] at hi
  exact hi

lemma marked_singular_integral_bound {u H : ℝ} (hu : 0 < u) (hu1 : u ≤ 1)
    (hH : H = 1 + Real.log (1 / u)) :
    ∫ s in (0 : ℝ)..1, singularKernel (markedF u H) s ≤ 4 := by
  have hlogu : Real.log u ≤ 0 := Real.log_nonpos hu.le hu1
  have hHe : H = 1 - Real.log u := by rw [hH, one_div, Real.log_inv]; ring
  have hH1 : 1 ≤ H := by linarith
  have hHp : 0 < H := by linarith
  let b := Real.exp (-1)
  have hb0 : 0 < b := Real.exp_pos _
  have hb1 : b ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hbm : b ∈ Set.Icc (0 : ℝ) 1 := ⟨hb0.le, hb1⟩
  have hlogb : Real.log b = -1 := Real.log_exp _
  have hir := regular_singular_intervalIntegrable (by norm_num : (0 : ℝ) < 1)
  have him := marked_singular_intervalIntegrable hu hHp
  have hsub0 : Set.uIcc (0 : ℝ) b ⊆ Set.uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    exact uIcc_subset_Icc ⟨le_rfl, by norm_num⟩ hbm
  have hsub1 : Set.uIcc b 1 ⊆ Set.uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    exact uIcc_subset_Icc hbm ⟨by norm_num, le_rfl⟩
  have hregval : ∫ s in (0 : ℝ)..b, singularKernel (regularF 1) s = 1 / 2 := by
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb0.le
      ((regularTail_continuousOn (by norm_num : (0 : ℝ) < 1)).mono (Icc_subset_Icc le_rfl hb1))
      (fun s (hs : s ∈ Set.Ioo 0 b) => by
        rw [regular_singular_formula]
        exact regularTail_derivative (by norm_num) ⟨hs.1, hs.2.le.trans hb1⟩)
      (hir.mono_set hsub0)
    rw [regularTail_zero, regularTail_of_ne hb0.ne', hlogb] at he
    norm_num at he
    exact he
  have hlow : ∫ s in (0 : ℝ)..b, singularKernel (markedF u H) s ≤ 2 / H := by
    have he := intervalIntegral.integral_mono_on hb0.le (him.mono_set hsub0)
      ((hir.mono_set hsub0).const_mul (4 / H))
      (fun s hs => marked_lower_half_bound hu.le hHp hs)
    rw [intervalIntegral.integral_const_mul, hregval] at he
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hafc : ContinuousOn (fun s => 1 / (s * (u - H * Real.log s))) (Set.Icc b 1) := by
    intro s hs
    have hs0 : 0 < s := hb0.trans_le hs.1
    have hden : u - H * Real.log s ≠ 0 := by
      have := mul_nonpos_of_nonneg_of_nonpos hHp.le (Real.log_nonpos hs0.le hs.2)
      linarith
    exact ((continuousAt_const.div
      (continuousAt_id.mul (continuousAt_const.sub
        ((Real.continuousAt_log hs0.ne').const_mul H))) (mul_ne_zero hs0.ne' hden))).continuousWithinAt
  have hafint : IntervalIntegrable
      (fun s => 1 / (s * (u - H * Real.log s))) volume b 1 :=
    hafc.intervalIntegrable_of_Icc hb1
  have hafval : ∫ s in b..1, 1 / (s * (u - H * Real.log s)) =
      (Real.log (u + H) - Real.log u) / H := by
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb1
      (fun s hs => (affineLogTail_derivative hu hHp ⟨hb0.trans_le hs.1, hs.2⟩).continuousAt.continuousWithinAt)
      (fun s hs => affineLogTail_derivative hu hHp ⟨hb0.trans hs.1, hs.2.le⟩) hafint
    dsimp [affineLogTail] at he
    rw [Real.log_one, hlogb] at he
    simp only [mul_zero, sub_zero, mul_neg_one, sub_neg_eq_add] at he
    rw [he]
    ring
  have hup : ∫ s in b..1, singularKernel (markedF u H) s ≤
      (Real.log (u + H) - Real.log u) / H := by
    rw [← hafval]
    apply intervalIntegral.integral_mono_on hb1 (him.mono_set hsub1) hafint
    intro s hs
    have hs0 : 0 < s := hb0.trans_le hs.1
    have hy := log_inverse_nonneg ⟨hs0, hs.2⟩
    have he : u - H * Real.log s = u + H * Real.log (1 / s) := by
      rw [one_div, Real.log_inv]; ring
    rw [he]
    have hp : 0 < u + H * Real.log (1 / s) := by positivity
    have hf : u + H * Real.log (1 / s) ≤ markedF u H (Real.log (1 / s)) := by
      dsimp [markedF]; nlinarith [mul_nonneg hHp.le (sq_nonneg (Real.log (1 / s)))]
    have hi := div_le_div_of_nonneg_right (one_div_le_one_div_of_le hp hf) hs0.le
    convert hi using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | simp [div_eq_mul_inv, mul_inv_rev, mul_comm]
  have hlog : Real.log (u + H) ≤ H := by
    have h₁ := Real.log_le_log (show 0 < u + H by positivity) (show u + H ≤ 1 + H by linarith)
    have h₂ := Real.log_le_sub_one_of_pos (show 0 < 1 + H by positivity)
    linarith
  have hfup : (Real.log (u + H) - Real.log u) / H ≤ 2 := by
    apply (div_le_iff₀ hHp).mpr
    linarith
  have hflow : 2 / H ≤ 2 := by apply (div_le_iff₀ hHp).mpr; linarith
  have htotal := intervalIntegral.integral_add_adjacent_intervals (him.mono_set hsub0) (him.mono_set hsub1)
  linarith

open scoped BigOperators

end KServer.SimplexAnalytic

namespace KServer.SimplexAnalytic
open Set MeasureTheory
open scoped BigOperators

lemma log_inverse_nonneg_closed {s : ℝ} (hs : s ∈ Set.Icc 0 1) :
    0 ≤ Real.log (1 / s) := by
  rcases eq_or_lt_of_le hs.1 with hz | hp
  · subst s; simp
  · exact log_inverse_nonneg ⟨hp, hs.2⟩

lemma regular_kernel_bounds {h s : ℝ} (hh : 1 ≤ h) (hs : s ∈ Set.Icc 0 1) :
    0 ≤ kernel (regularF h) s ∧ kernel (regularF h) s ≤ 1 := by
  have hp : 0 < h := by linarith
  have hf := regularF_lower hp (log_inverse_nonneg_closed hs)
  constructor
  · exact div_nonneg (by norm_num) (hp.le.trans hf)
  · dsimp [kernel]
    exact (div_le_one (hp.trans_le hf)).mpr (hh.trans hf)

lemma regular_coefficients {h a : ℝ} (hh : 1 ≤ h) (ha : a ∈ Set.Icc 0 1) :
    (∫ s in (0 : ℝ)..a, kernel (regularF h) s) ∈ Set.Icc 0 a ∧
    (∫ s in (0 : ℝ)..a, singularKernel (regularF h) s) ∈ Set.Icc 0 1 := by
  have hp : 0 < h := by linarith
  have hF : ∀ y, 0 ≤ y → 0 < regularF h y := fun y hy => hp.trans_le (regularF_lower hp hy)
  have hi := regular_singular_intervalIntegrable hp
  have hki := kernel_intervalIntegrable (by unfold regularF; fun_prop) hF hi
  have hsub : Set.uIcc (0 : ℝ) a ⊆ Set.uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    exact uIcc_subset_Icc ⟨le_rfl, by norm_num⟩ ha
  have hn : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ singularKernel (regularF h) s := by
    intro s hs
    exact div_nonneg (regular_kernel_bounds hh hs).1 hs.1
  constructor
  · constructor
    · exact intervalIntegral.integral_nonneg ha.1 fun s hs => (regular_kernel_bounds hh ⟨hs.1, hs.2.trans ha.2⟩).1
    · have he := intervalIntegral.integral_mono_on ha.1 (hki.mono_set hsub)
        (intervalIntegrable_const (μ := volume)) (fun s hs => (regular_kernel_bounds hh ⟨hs.1, hs.2.trans ha.2⟩).2)
      simpa using he
  · constructor
    · exact intervalIntegral.integral_nonneg ha.1 fun s hs => hn s ⟨hs.1, hs.2.trans ha.2⟩
    · rw [← regular_singular_integral hp]
      apply intervalIntegral.integral_mono_interval le_rfl ha.1 ha.2 _ hi
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact hn s ⟨hs.1.le, hs.2⟩

lemma regular_component_bound {h a Cα ell η S B : ℝ}
    (hh : 1 ≤ h) (ha : a ∈ Set.Icc 0 1) (hC : 0 ≤ Cα) (hl : 0 ≤ ell)
    (hη : 0 ≤ η) (hS : 0 ≤ S) (hB : 0 ≤ B) :
    |primitive (regularF h) Cα ell η S B 0 a| ≤
      Cα * ell * (S * a + (1 + η) * B) := by
  have hp : 0 < h := by linarith
  rw [primitive_affine (by unfold regularF; fun_prop)
    (fun y hy => hp.trans_le (regularF_lower hp hy))
    (regular_singular_intervalIntegrable hp) Cα ell η S B ⟨le_rfl, by norm_num⟩ ha]
  obtain ⟨hK, hJ⟩ := regular_coefficients hh ha
  rw [abs_mul, abs_of_nonneg (mul_nonneg hC hl)]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hl)
  exact (abs_sub _ _).trans (by
    rw [abs_of_nonneg (mul_nonneg hS hK.1),
      abs_of_nonneg (mul_nonneg (mul_nonneg (by linarith) hB) hJ.1)]
    nlinarith [mul_le_mul_of_nonneg_left hK.2 hS,
      mul_le_mul_of_nonneg_left hJ.2 (show 0 ≤ (1 + η) * B by positivity)])

lemma marked_coefficients {u H a : ℝ} (hu : 0 < u) (hu1 : u ≤ 1)
    (hH : H = 1 + Real.log (1 / u)) (ha : a ∈ Set.Icc 0 1) :
    (∫ s in a..1, kernel (markedF u H) s) ∈ Set.Icc 0 4 ∧
    (∫ s in a..1, singularKernel (markedF u H) s) ∈ Set.Icc 0 4 := by
  have hH1 : 1 ≤ H := by rw [hH]; linarith [log_inverse_nonneg ⟨hu, hu1⟩]
  have hp : 0 < H := by linarith
  have hi := marked_singular_intervalIntegrable hu hp
  have hsub : Set.uIcc a 1 ⊆ Set.uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    exact uIcc_subset_Icc ha ⟨by norm_num, le_rfl⟩
  have hn : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ kernel (markedF u H) s := by
    intro s hs
    exact div_nonneg (by norm_num) (marked_positive hu hp.le _ (log_inverse_nonneg_closed hs)).le
  have hjn : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ singularKernel (markedF u H) s := by
    intro s hs
    exact div_nonneg (hn s hs) hs.1
  have hji : (∫ s in a..1, singularKernel (markedF u H) s) ∈ Set.Icc 0 4 := by
    constructor
    · exact intervalIntegral.integral_nonneg ha.2 fun s hs => hjn s ⟨ha.1.trans hs.1, hs.2⟩
    · apply le_trans _ (marked_singular_integral_bound hu hu1 hH)
      apply intervalIntegral.integral_mono_interval ha.1 ha.2 le_rfl _ hi
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact hjn s ⟨hs.1.le, hs.2⟩
  refine ⟨⟨intervalIntegral.integral_nonneg ha.2 (fun s hs => hn s ⟨ha.1.trans hs.1, hs.2⟩), ?_⟩, hji⟩
  apply le_trans _ hji.2
  apply intervalIntegral.integral_mono_on_of_le_Ioo ha.2
    ((kernel_intervalIntegrable (by unfold markedF; fun_prop) (marked_positive hu hp.le) hi).mono_set hsub)
    (hi.mono_set hsub)
  intro s hs
  have hs0 : 0 < s := ha.1.trans_lt hs.1
  apply (le_div_iff₀ hs0).mpr
  exact mul_le_of_le_one_right (hn s ⟨hs0.le, hs.2.le⟩) hs.2.le

lemma marked_component_bound {u H a Cα ell η S B Bside : ℝ}
    (hu : 0 < u) (hu1 : u ≤ 1) (hH : H = 1 + Real.log (1 / u))
    (ha : a ∈ Set.Icc 0 1) (hC : 0 ≤ Cα) (hl : 0 ≤ ell)
    (hη : 0 ≤ η) (hηu : η ≤ u) (hB : 0 ≤ B) (hside : 0 ≤ Bside)
    (hS : S = B + Bside) :
    |primitive (markedF u H) Cα ell η S B 1 a| ≤
      4 * Cα * ell * (S * (1 - a) + Bside + u * S) := by
  have hS0 : 0 ≤ S := by linarith
  have hH1 : 1 ≤ H := by rw [hH]; linarith [log_inverse_nonneg ⟨hu, hu1⟩]
  have hHp : 0 < H := by linarith
  let f := fun s => (S - (1 + η) * B / s) / markedF u H (Real.log (1 / s))
  let M := S * (1 - a) + Bside + u * S
  have hM : 0 ≤ M := by
    dsimp [M]
    exact add_nonneg (add_nonneg (mul_nonneg hS0 (sub_nonneg.mpr ha.2)) hside) (mul_nonneg hu.le hS0)
  have hint := marked_singular_intervalIntegrable hu hHp
  have hsub : Set.uIcc a 1 ⊆ Set.uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    exact uIcc_subset_Icc ha ⟨by norm_num, le_rfl⟩
  have hfi : IntervalIntegrable f volume a 1 :=
    (integrand_intervalIntegrable (by unfold markedF; fun_prop)
      (marked_positive hu hHp.le) hint η S B).mono_set hsub
  have habs : IntervalIntegrable (fun s => |f s|) volume a 1 := by
    simpa only [Real.norm_eq_abs] using hfi.norm
  have hfbound : ∀ s ∈ Set.Ioo a 1, |f s| ≤ M * singularKernel (markedF u H) s := by
    intro s hs
    have hs0 : 0 < s := ha.1.trans_lt hs.1
    have hs1 : s ≤ 1 := hs.2.le
    have hj : 0 ≤ singularKernel (markedF u H) s :=
      div_nonneg (div_nonneg (by norm_num)
        (marked_positive hu hHp.le _ (log_inverse_nonneg ⟨hs0, hs1⟩)).le) hs0.le
    have he : f s = (S * (s - 1) + Bside - η * B) * singularKernel (markedF u H) s := by
      dsimp [f, singularKernel, kernel]
      rw [hS]
      field_simp
      ring
    rw [he, abs_mul, abs_of_nonneg hj]
    apply mul_le_mul_of_nonneg_right _ hj
    have hm := (abs_sub (S * (s - 1) + Bside) (η * B)).trans
      (add_le_add (abs_add_le (S * (s - 1)) Bside) le_rfl)
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hS0 (by linarith)),
      abs_of_nonneg hside, abs_of_nonneg (mul_nonneg hη hB)] at hm
    dsimp [M]
    have hsa := mul_le_mul_of_nonneg_left hs.1.le hS0
    have hηS := mul_le_mul_of_nonneg_left (show B ≤ S by linarith) hη
    have huS := mul_le_mul_of_nonneg_right hηu hS0
    linarith
  have hi : |∫ s in a..1, f s| ≤ 4 * M := by
    calc
      _ ≤ ∫ s in a..1, |f s| := intervalIntegral.abs_integral_le_integral_abs ha.2
      _ ≤ ∫ s in a..1, M * singularKernel (markedF u H) s :=
        intervalIntegral.integral_mono_on_of_le_Ioo ha.2 habs ((hint.mono_set hsub).const_mul M) hfbound
      _ = M * ∫ s in a..1, singularKernel (markedF u H) s := intervalIntegral.integral_const_mul _ _
      _ ≤ 4 * M := by
        have hj := (marked_coefficients hu hu1 hH ha).2.2
        nlinarith
  unfold primitive
  rw [intervalIntegral.integral_symm, abs_mul, abs_neg,
    abs_of_nonneg (mul_nonneg hC hl)]
  have hm := mul_le_mul_of_nonneg_left hi (mul_nonneg hC hl)
  change Cα * ell * |∫ s in a..1, f s| ≤ _
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | (dsimp [M]; ring)

/-- Dimension-free input bound for an affine sum of the exact primitives.
The scalar assumptions are the integral coefficient bounds established above. -/
lemma affine_sum_input_bound {ι : Type*} [Fintype ι]
    {K J η B B' : ι → ℝ} {L ηmax CK CJ : ℝ}
    (hL : 0 ≤ L) (hη : ∀ i, 0 ≤ η i) (hηmax : ∀ i, η i ≤ ηmax)
    (hK : ∑ i, |K i| ≤ CK) (hJ : ∀ i, |J i| ≤ CJ) :
    |(∑ i, L * ((∑ j, B j) * K i - (1 + η i) * B i * J i)) -
      (∑ i, L * ((∑ j, B' j) * K i - (1 + η i) * B' i * J i))| ≤
      L * (CK + (1 + ηmax) * CJ) * ∑ i, |B i - B' i| := by
  let T := ∑ i, |B i - B' i|
  have hT : 0 ≤ T := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hS : |(∑ j, B j) - ∑ j, B' j| ≤ T := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  have hCK : 0 ≤ CK := (Finset.sum_nonneg fun i _ => abs_nonneg _).trans hK
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |L * ((∑ j, B j) * K i - (1 + η i) * B i * J i) -
      L * ((∑ j, B' j) * K i - (1 + η i) * B' i * J i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, L * (T * |K i| + (1 + ηmax) * |B i - B' i| * CJ) := by
      apply Finset.sum_le_sum
      intro i _
      have he : L * ((∑ j, B j) * K i - (1 + η i) * B i * J i) -
          L * ((∑ j, B' j) * K i - (1 + η i) * B' i * J i) =
          L * (((∑ j, B j) - ∑ j, B' j) * K i - (1 + η i) * (B i - B' i) * J i) := by ring
      rw [he, abs_mul, abs_of_nonneg hL]
      apply mul_le_mul_of_nonneg_left _ hL
      apply (abs_sub _ _).trans
      simp only [abs_mul, abs_of_nonneg (show 0 ≤ 1 + η i by linarith [hη i])]
      apply add_le_add (mul_le_mul_of_nonneg_right hS (abs_nonneg _))
      have he := mul_le_mul_of_nonneg_right (show 1 + η i ≤ 1 + ηmax by linarith [hηmax i]) (abs_nonneg (B i - B' i))
      exact mul_le_mul he (hJ i) (abs_nonneg _)
        (mul_nonneg (by linarith [hη i, hηmax i]) (abs_nonneg _))
    _ ≤ L * (CK + (1 + ηmax) * CJ) * T := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      have hm := mul_le_mul_of_nonneg_left hK (mul_nonneg hL hT)
      dsimp [T] at *
      calc
        _ = (L * ∑ i, |B i - B' i|) * (∑ i, |K i|) + L * ((1 + ηmax) * (∑ i, |B i - B' i|) * CJ) := by ring
        _ ≤ (L * ∑ i, |B i - B' i|) * CK + L * ((1 + ηmax) * (∑ i, |B i - B' i|) * CJ) := add_le_add hm le_rfl
        _ = _ := by ring


/-- The exact regular-domain version of (alpha-input-slopes), with constant 3. -/
lemma regular_input_slopes {ι : Type*} [Fintype ι]
    {h η B B' a : ι → ℝ} {Cα ell : ℝ}
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∑ i, a i = 1)
    (hh : ∀ i, 1 ≤ h i) (hη0 : ∀ i, 0 ≤ η i) (hη1 : ∀ i, η i ≤ 1)
    (hC : 0 ≤ Cα) (hl : 0 ≤ ell) :
    |(∑ i, primitive (regularF (h i)) Cα ell (η i) (∑ j, B j) (B i) 0 (a i)) -
      (∑ i, primitive (regularF (h i)) Cα ell (η i) (∑ j, B' j) (B' i) 0 (a i))| ≤
      3 * Cα * ell * ∑ i, |B i - B' i| := by
  have ha : ∀ i, a i ∈ Set.Icc 0 1 := by
    intro i
    refine ⟨ha0 i, ?_⟩
    rw [← ha1]
    exact Finset.single_le_sum (fun j _ => ha0 j) (Finset.mem_univ _)
  let K := fun i => ∫ s in (0 : ℝ)..a i, kernel (regularF (h i)) s
  let J := fun i => ∫ s in (0 : ℝ)..a i, singularKernel (regularF (h i)) s
  have hb := fun i => regular_coefficients (hh i) (ha i)
  have hK : ∑ i, |K i| ≤ 1 := by
    rw [← ha1]
    apply Finset.sum_le_sum
    intro i _
    rw [abs_of_nonneg (hb i).1.1]
    exact (hb i).1.2
  have hJ : ∀ i, |J i| ≤ 1 := by
    intro i
    rw [abs_of_nonneg (hb i).2.1]
    exact (hb i).2.2
  have he (V : ι → ℝ) :
      (∑ i, primitive (regularF (h i)) Cα ell (η i) (∑ j, V j) (V i) 0 (a i)) =
      ∑ i, (Cα * ell) * ((∑ j, V j) * K i - (1 + η i) * V i * J i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact primitive_affine (by unfold regularF; fun_prop)
      (fun y hy => (show 0 < h i by linarith [hh i]).trans_le
        (regularF_lower (by linarith [hh i]) hy))
      (regular_singular_intervalIntegrable (by linarith [hh i]))
      Cα ell (η i) (∑ j, V j) (V i) ⟨le_rfl, by norm_num⟩ (ha i)
  rw [he B, he B']
  have ht := affine_sum_input_bound (B := B) (B' := B') (mul_nonneg hC hl)
    hη0 hη1 hK hJ
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  ring

/-- The source marked-domain affine input bound, also uniform as u tends to 0. -/
lemma marked_input_slopes {ι : Type*} [Fintype ι] [DecidableEq ι] (o : ι)
    {h η B B' a : ι → ℝ} {Cα ell u H : ℝ}
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∑ i, a i = 1)
    (hh : ∀ i, i ≠ o → 1 ≤ h i) (hu : 0 < u) (hu1 : u ≤ 1)
    (hH : H = 1 + Real.log (1 / u))
    (hη0 : ∀ i, 0 ≤ η i) (hη1 : ∀ i, η i ≤ 1)
    (hC : 0 ≤ Cα) (hl : 0 ≤ ell) :
    let F := fun i => if i = o then markedF u H else regularF (h i)
    let base := fun i => if i = o then (1 : ℝ) else 0
    |(∑ i, primitive (F i) Cα ell (η i) (∑ j, B j) (B i) (base i) (a i)) -
      (∑ i, primitive (F i) Cα ell (η i) (∑ j, B' j) (B' i) (base i) (a i))| ≤
      13 * Cα * ell * ∑ i, |B i - B' i| := by
  intro F base
  have ha : ∀ i, a i ∈ Set.Icc 0 1 := by
    intro i
    refine ⟨ha0 i, ?_⟩
    rw [← ha1]
    exact Finset.single_le_sum (fun j _ => ha0 j) (Finset.mem_univ _)
  have hH0 : 0 < H := by rw [hH]; linarith [log_inverse_nonneg ⟨hu, hu1⟩]
  let K := fun i => ∫ s in base i..a i, kernel (F i) s
  let J := fun i => ∫ s in base i..a i, singularKernel (F i) s
  have hKa : ∀ i, |K i| ≤ a i + if i = o then 4 else 0 := by
    intro i
    by_cases hi : i = o
    · subst i
      simp only [K, base, F, ite_true]
      rw [intervalIntegral.integral_symm, abs_neg,
        abs_of_nonneg (marked_coefficients hu hu1 hH (ha o)).1.1]
      linarith [(marked_coefficients hu hu1 hH (ha o)).1.2, ha0 o]
    · simp only [K, base, F, ite_eq_right hi, add_zero]
      rw [abs_of_nonneg (regular_coefficients (hh i hi) (ha i)).1.1]
      exact (regular_coefficients (hh i hi) (ha i)).1.2
  have hK : ∑ i, |K i| ≤ 5 := by
    have ht := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hKa i)
    norm_num [Finset.sum_add_distrib, ha1] at ht ⊢
    exact ht
  have hJ : ∀ i, |J i| ≤ 4 := by
    intro i
    by_cases hi : i = o
    · subst i
      simp only [J, base, F, ite_true]
      rw [intervalIntegral.integral_symm, abs_neg,
        abs_of_nonneg (marked_coefficients hu hu1 hH (ha o)).2.1]
      exact (marked_coefficients hu hu1 hH (ha o)).2.2
    · simp only [J, base, F, ite_eq_right hi]
      rw [abs_of_nonneg (regular_coefficients (hh i hi) (ha i)).2.1]
      linarith [(regular_coefficients (hh i hi) (ha i)).2.2]
  have he (V : ι → ℝ) :
      (∑ i, primitive (F i) Cα ell (η i) (∑ j, V j) (V i) (base i) (a i)) =
      ∑ i, (Cα * ell) * ((∑ j, V j) * K i - (1 + η i) * V i * J i) := by
    apply Finset.sum_congr rfl
    intro i _
    have hp : ∀ y, 0 ≤ y → 0 < F i y := by
      intro y hy
      dsimp [F]
      split_ifs with hi
      · exact marked_positive hu hH0.le y hy
      · exact (show 0 < h i by linarith [hh i hi]).trans_le
          (regularF_lower (by linarith [hh i hi]) hy)
    apply primitive_affine _ hp _ Cα ell (η i) (∑ j, V j) (V i) _ (ha i)
    · dsimp [F]; split_ifs
      · unfold markedF; fun_prop
      · unfold regularF; fun_prop
    · dsimp [F]; split_ifs with hi
      · exact marked_singular_intervalIntegrable hu hH0
      · exact regular_singular_intervalIntegrable (by linarith [hh i hi])
    · dsimp [base]; split_ifs <;> constructor <;> norm_num
  rw [he B, he B']
  have ht := affine_sum_input_bound (B := B) (B' := B') (mul_nonneg hC hl)
    hη0 hη1 hK hJ
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  ring

end KServer.SimplexAnalytic

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Allocation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Finset Set Filter MeasureTheory

/-! The exact source primitives installed in the actual affine minimizer
recursion. The coefficients use raw core flags; fine caps are deliberately
absent. The zero-potential cases do not evaluate the marked denominator. -/
namespace KServer.SimplexFamilies
open scoped BigOperators
open Finset Set MeasureTheory
open KServer.SimplexAnalytic KServer.AdaptiveMinimization
variable {J R : Type*} [Fintype J] [DecidableEq J] [Fintype R]

omit [DecidableEq J] [Fintype R] in
lemma regular_coefficient_bound (A : Finset J) (flags : J → R → Bool) (h eta : J → ℝ)
    (hh : ∀ i, 1 ≤ h i) (heta : ∀ i, eta i ∈ Set.Icc 0 1)
    {C ell : ℝ} (hC : 0 ≤ C) (hell : 0 ≤ ell) {a : J → ℝ}
    (ha : a ∈ ChangingDomains.simplex A) (ir : J × R) :
    |coefficient C ell (regular A flags h eta hh) a ir| ≤ 3*C*ell := by
  have hai i := ChangingDomains.simplex_coordinate ha i
  have hb i := regular_coefficients (hh i) (hai i)
  have hs : (∑ i, K (regular A flags h eta hh) a i) ∈ Set.Icc 0 1 := by
    constructor
    · exact sum_nonneg fun i _ => (hb i).1.1
    · have hm := sum_le_sum fun i (_ : i∈Finset.univ) => (hb i).1.2
      change (∑ i, K (regular A flags h eta hh) a i) ≤ ∑ i, a i at hm
      rw [ha.2.1] at hm
      split_ifs at hm <;> linarith
  change |if flags ir.1 ir.2=true then C*ell*((∑ i, K (regular A flags h eta hh) a i)-(1+eta ir.1)*Z (regular A flags h eta hh) a ir.1) else 0| ≤ _
  split_ifs with hf
  · rw [abs_mul,abs_of_nonneg (mul_nonneg hC hell)]
    have hj : Z (regular A flags h eta hh) a ir.1 ∈ Set.Icc 0 1 := (hb ir.1).2
    have hprod := mul_le_mul (show 1+eta ir.1 ≤ 2 by linarith [(heta ir.1).2]) hj.2 hj.1 (by norm_num : (0:ℝ)≤2)
    have hprodn := mul_nonneg (show 0 ≤ 1+eta ir.1 by linarith [(heta ir.1).1]) hj.1
    have hab : |(∑ i, K (regular A flags h eta hh) a i)-(1+eta ir.1)*Z (regular A flags h eta hh) a ir.1| ≤ 3 := by
      rw [abs_le]
      constructor <;> linarith [hs.1,hs.2]
    nlinarith [mul_le_mul_of_nonneg_left hab (mul_nonneg hC hell)]
  · simp only [abs_zero]; positivity


omit [Fintype R] in
lemma marked_coefficient_bound (A : Finset J) (flags : J → R → Bool) (o : J) (h eta : J → ℝ)
    {u C ell : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (hh : ∀ i ≠ o, 1 ≤ h i)
    (heta : ∀ i, eta i ∈ Set.Icc 0 1) (hC : 0 ≤ C) (hell : 0 ≤ ell) {a : J → ℝ}
    (ha : a ∈ ChangingDomains.simplex A) (ir : J × R) :
    |coefficient C ell (marked A flags o h eta u hu hu1 hh) a ir| ≤ 13*C*ell := by
  let d := marked A flags o h eta u hu hu1 hh
  have hai i := ChangingDomains.simplex_coordinate ha i
  have hK (i : J) : |K d a i| ≤ a i+if i=o then 4 else 0 := by
    by_cases hi : i=o
    · subst i
      simp only [K,d,marked,ite_true]
      rw [intervalIntegral.integral_symm,abs_neg,
        abs_of_nonneg (marked_coefficients hu hu1 rfl (hai o)).1.1]
      linarith [(marked_coefficients hu hu1 rfl (hai o)).1.2,ha.1 o]
    · simp only [K,d,marked,ite_eq_right hi,add_zero]
      rw [abs_of_nonneg (regular_coefficients (hh i hi) (hai i)).1.1]
      exact (regular_coefficients (hh i hi) (hai i)).1.2
  have hs : |∑ i, K d a i| ≤ 5 := by
    apply (abs_sum_le_sum_abs _ _).trans
    have ht := sum_le_sum fun i (_ : i∈Finset.univ) => hK i
    classical
    have he : (∑ i : J, if i=o then (4:ℝ) else 0)=4 := by simp
    rw [sum_add_distrib,he,ha.2.1] at ht
    split_ifs at ht <;> linarith
  have hZ (i : J) : |Z d a i| ≤ 4 := by
    by_cases hi : i=o
    · subst i
      simp only [Z,d,marked,ite_true]
      rw [intervalIntegral.integral_symm,abs_neg,
        abs_of_nonneg (marked_coefficients hu hu1 rfl (hai o)).2.1]
      exact (marked_coefficients hu hu1 rfl (hai o)).2.2
    · simp only [Z,d,marked,ite_eq_right hi]
      rw [abs_of_nonneg (regular_coefficients (hh i hi) (hai i)).2.1]
      linarith [(regular_coefficients (hh i hi) (hai i)).2.2]
  change |if flags ir.1 ir.2=true then C*ell*((∑ i, K d a i)-(1+eta ir.1)*Z d a ir.1) else 0| ≤ _
  split_ifs
  · rw [abs_mul,abs_of_nonneg (mul_nonneg hC hell)]
    have hprod : |(1+eta ir.1)*Z d a ir.1| ≤ 8 := by
      rw [abs_mul,abs_of_nonneg (show 0 ≤ 1+eta ir.1 by linarith [(heta ir.1).1])]
      have := mul_le_mul (show 1+eta ir.1 ≤ 2 by linarith [(heta ir.1).2])
        (hZ ir.1) (abs_nonneg _) (by norm_num : (0:ℝ)≤2)
      linarith
    have hab : |(∑ i, K d a i)-(1+eta ir.1)*Z d a ir.1| ≤ 13 :=
      (abs_sub _ _).trans (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hab (mul_nonneg hC hell)]
  · simp only [abs_zero]; positivity

end KServer.SimplexFamilies


noncomputable section
open scoped BigOperators Topology
open Set Filter

/-! The literal two-stage update of §04: prepare with the new core flags on
common coordinates, minimize on the old simplex, transpose at exactly zero
cost, then minimize on the new simplex. The bounds below calculate its edit
charge from the actual flags and held parameters, not from an assumed drift
or policy bound. -/
namespace KServer.AdaptiveAllocation
open Finset SimplexAnalytic SimplexFamilies AdaptiveMinimization
variable {J R : Type*} [Fintype J] [DecidableEq J] [Fintype R]

omit [Fintype J] [Fintype R] in
lemma prepared_flags_outside (A B : Finset J) (g : J → R → Bool) :
    ∀ i∉A, ∀ r, preparedFlags A B g i r=false := by
  intro i hi r
  simp [preparedFlags,ChangingDomains.syntheticFlags,hi]

omit [Fintype J] in
lemma prepared_input_outside (A B : Finset J) (g : J → R → Bool) (p : J × R → ℝ) :
    ∀ i∉B, preparedInput A B g p i=0 := by
  intro i hi
  simp [preparedInput,preparedFlags,ChangingDomains.core,ChangingDomains.syntheticFlags,hi]

omit [DecidableEq J] [Fintype R] in
lemma regular_potential_zero (A : Finset J) (f : J → R → Bool) (h eta : J → ℝ)
    (hh : ∀ i, 1≤h i) (C ell : ℝ) (a : J → ℝ) :
    potential C ell (regular A f h eta hh) (fun _ => 0) a=0 := by
  simp [potential,regular,primitive]

omit [DecidableEq J] in
lemma nonneg_total_zero {B : J → ℝ} (hB : ∀ i, 0≤B i) (hS : (∑ i, B i)=0) :
    B=(fun _ => 0) := by
  funext i
  exact le_antisymm (by simpa [hS] using (single_le_sum (fun j _ => hB j) (mem_univ i))) (hB i)

omit [Fintype R] in
lemma regular_transpose_value (A B : Finset J) (f : J → R → Bool) (h eta : J → ℝ)
    (hh : ∀ i, 1≤h i) (C ell : ℝ) (v a : J → ℝ) (hv : ∀ i, 0≤v i) :
    potential C ell (regular A f h eta hh) v
      (ChangingDomains.transposeSimplex B (∑ i, v i) a)=
    potential C ell (regular A f h eta hh) v a := by
  by_cases hS : (∑ i, v i)=0
  · rw [nonneg_total_zero hv hS]
    simp only [regular_potential_zero]
  · simp [ChangingDomains.transposeSimplex,hS]

end KServer.AdaptiveAllocation

namespace KServer.AdaptiveAllocation
open Finset SimplexAnalytic SimplexFamilies AdaptiveMinimization
variable {J R : Type*} [Fintype J] [DecidableEq J] [Fintype R]

omit [DecidableEq J] [Fintype R] in
lemma regular_input_bound (A : Finset J) (hA : A.Nonempty) (f : J → R → Bool)
    (h eta : J → ℝ) (hh : ∀ i, 1≤h i) (he : ∀ i, eta i∈Set.Icc 0 1)
    {C ell : ℝ} (hC : 0≤C) (hl : 0≤ell) {B B' a : J → ℝ}
    (ha : a∈ChangingDomains.simplex A) :
    |potential C ell (regular A f h eta hh) B a-
      potential C ell (regular A f h eta hh) B' a| ≤
      3*C*ell*ChangingDomains.variation B B' := by
  have hs : (∑ i, a i)=1 := by simpa only [ite_eq_left hA] using ha.2.1
  exact regular_input_slopes ha.1 hs hh (fun i => (he i).1) (fun i => (he i).2) hC hl

omit [DecidableEq J] [Fintype R] in
lemma regular_parameter_jump (A A' : Finset J) (f g : J → R → Bool)
    (h h' eta eta' : J → ℝ) (hh : ∀ i, 1≤h i) (hh' : ∀ i, 1≤h' i)
    (he : ∀ i, eta i∈Set.Icc 0 1) (he' : ∀ i, eta' i∈Set.Icc 0 1)
    (heq : ∀ i, h i=h' i → eta i=eta' i)
    {C ell : ℝ} (hC : 0≤C) (hl : 0≤ell) {B a : J → ℝ}
    (hB : ∀ i, 0≤B i) (ha : ∀ i, a i∈Set.Icc 0 1)
    (hcap : ∀ i, (∑ j, B j)*a i≤(1+eta i)*B i) :
    |potential C ell (regular A' g h' eta' hh') B a-
      potential C ell (regular A f h eta hh) B a| ≤
      8*C*ell*(∑ i, if h i=h' i then 0 else B i) := by
  have hS : 0≤∑ i, B i := sum_nonneg fun i _ => hB i
  have hi (i : J) :
      |primitive (regularF (h' i)) C ell (eta' i) (∑ j, B j) (B i) 0 (a i)-
        primitive (regularF (h i)) C ell (eta i) (∑ j, B j) (B i) 0 (a i)| ≤
        8*C*ell*(if h i=h' i then 0 else B i) := by
    by_cases hhx : h i=h' i
    · simp [hhx,heq i hhx]
    · rw [ite_eq_right hhx]
      have ho := regular_component_bound (hh i) (ha i) hC hl (he i).1 hS (hB i)
      have hn := regular_component_bound (hh' i) (ha i) hC hl (he' i).1 hS (hB i)
      have hep := mul_le_mul_of_nonneg_right (he i).2 (hB i)
      have he'p := mul_le_mul_of_nonneg_right (he' i).2 (hB i)
      have hc' := hcap i
      have hlo : (∑ j, B j)*a i+(1+eta i)*B i≤4*B i := by nlinarith
      have hln : (∑ j, B j)*a i+(1+eta' i)*B i≤4*B i := by nlinarith
      have hco := mul_le_mul_of_nonneg_left hlo (mul_nonneg hC hl)
      have hcn := mul_le_mul_of_nonneg_left hln (mul_nonneg hC hl)
      have hab := abs_sub
        (primitive (regularF (h' i)) C ell (eta' i) (∑ j, B j) (B i) 0 (a i))
        (primitive (regularF (h i)) C ell (eta i) (∑ j, B j) (B i) 0 (a i))
      nlinarith
  change |(∑ i, primitive (regularF (h' i)) C ell (eta' i) (∑ j, B j) (B i) 0 (a i))-
    ∑ i, primitive (regularF (h i)) C ell (eta i) (∑ j, B j) (B i) 0 (a i)| ≤ _
  rw [←sum_sub_distrib,mul_sum]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => hi i)

omit [DecidableEq J] in
lemma total_variation_bound (B B' : J → ℝ) :
    |(∑ i, B i)-(∑ i, B' i)|≤ChangingDomains.variation B B' := by
  rw [←sum_sub_distrib]
  exact abs_sum_le_sum_abs _ _

omit [Fintype J] in
lemma transpose_cap {B : Finset J} {S : ℝ} {a v gamma : J → ℝ}
    (hv : ∀ i, 0≤v i) (hg : ∀ i, 0≤gamma i)
    (hcap : ∀ i, S*a i≤gamma i*v i) :
    ∀ i, S*(ChangingDomains.transposeSimplex B S a) i≤gamma i*v i := by
  intro i
  by_cases hs : S=0
  · simp only [hs,zero_mul]
    exact mul_nonneg (hg i) (hv i)
  · simpa [ChangingDomains.transposeSimplex,hs] using hcap i

lemma regular_transport_mem {A B : Finset J} (hA : A.Nonempty) (hB : B.Nonempty)
    (g : J → R → Bool) (h : J → ℝ) (hh : ∀ i, 1≤h i)
    {C ell ct ηmax Cexp : ℝ} (hC : 0<C) (hl : 0<ell) (hc : 0 < ct)
    (hmax : ∀ i∈A, ct*h i/ell≤ηmax) (hCexp : 0≤Cexp)
    (htail : ∑ i∈A, Real.exp (-h i)≤Cexp)
    (hgap : 2*(25+32*Cexp)*(1+ηmax)<C*ct)
    (p : J × R → ℝ) (hp : ∀ ir, 0≤p ir) (a : J → ℝ)
    (ha : a∈ChangingDomains.simplex A) :
    regularTransport C ell ct A B g h hh p a∈ChangingDomains.simplex B := by
  have hp' : ∀ i r, 0≤p (i,r) := fun i r => hp (i,r)
  have hcap := regular_update_feasible hA (preparedFlags A B g) h hh hC hl hc hmax
    hCexp htail hgap p hp (prepared_flags_outside A B g) a ha
  exact ChangingDomains.transposeSimplex_mem (v := preparedInput A B g p)
    hA hB ((family C ell).update_mem _ _ _ _)
    (sum_nonneg fun i _ => ChangingDomains.core_nonneg hp' i) hcap
    (prepared_input_outside A B g p)

end KServer.AdaptiveAllocation

namespace KServer.AdaptiveAllocation
open Finset SimplexAnalytic SimplexFamilies AdaptiveMinimization
variable {J R : Type*} [Fintype J] [DecidableEq J] [Fintype R]

lemma literal_update_payment (C ell : ℝ) (d : Data J R) (p : J × R → ℝ) (c : ℝ)
    {a : J → ℝ} (ha : a∈ChangingDomains.simplex d.active) :
    c*ChangingDomains.variation ((family C ell).update d p c a) a ≤
      potential C ell d (core d p) a-
      potential C ell d (core d p) ((family C ell).update d p c a) := by
  have hm := update_isMin C ell d p c a ha
  change potential C ell d (core d p) ((family C ell).update d p c a)+
    c*ChangingDomains.variation ((family C ell).update d p c a) a ≤
    potential C ell d (core d p) a+c*ChangingDomains.variation a a at hm
  rw [ChangingDomains.variation_self,mul_zero,add_zero] at hm
  linarith

lemma regular_step_payment {A B : Finset J} (hA : A.Nonempty) (hB : B.Nonempty)
    (f g : J → R → Bool) (h h' : J → ℝ)
    (hh : ∀ i, 1≤h i) (hh' : ∀ i, 1≤h' i)
    {C ell ct ηmax Cexp : ℝ} (hC : 0<C) (hl : 0<ell) (hc : 0 < ct)
    (he : ∀ i, ct*h i/ell∈Set.Icc 0 1) (he' : ∀ i, ct*h' i/ell∈Set.Icc 0 1)
    (hmax : ∀ i∈A, ct*h i/ell≤ηmax) (hCexp : 0≤Cexp)
    (htail : ∑ i∈A, Real.exp (-h i)≤Cexp)
    (hgap : 2*(25+32*Cexp)*(1+ηmax)<C*ct)
    (p : J × R → ℝ) (hp : ∀ ir, p ir∈Set.Icc 0 1)
    (hf : ∀ i∉A, ∀ r, f i r=false) (hg : ∀ i∉B, ∀ r, g i r=false)
    (a : J → ℝ) (ha : a∈ChangingDomains.simplex A) :
    let d₀ := regular A f h (fun i => ct*h i/ell) hh
    let d₃ := regular B g h' (fun i => ct*h' i/ell) hh'
    let B₀ := core d₀ p
    let B₃ := core d₃ p
    let B₁ := preparedInput A B g p
    let a₃ := regularStep C ell ct A B g h h' hh hh' p a
    (∑ i, B₃ i)*ChangingDomains.variation a₃ a ≤
      potential C ell d₀ B₀ a-potential C ell d₃ B₃ a₃+
      (6*C*ell+4)*ChangingDomains.changedFlags f g+
      8*C*ell*(∑ i, if h i=h' i then 0 else B₁ i) := by
  intro d₀ d₃ B₀ B₃ B₁ a₃
  let d₁ := regular A (preparedFlags A B g) h (fun i => ct*h i/ell) hh
  let a₁ := regularPrepare C ell ct A B g h hh p a
  let a₂ := regularTransport C ell ct A B g h hh p a
  have hp₀ : ∀ ir, 0≤p ir := fun ir => (hp ir).1
  have hp₀' : ∀ i r, 0≤p (i,r) := fun i r => (hp (i,r)).1
  have hB₁ : ∀ i, 0≤B₁ i := fun i => ChangingDomains.core_nonneg hp₀' i
  have hS₁ : 0≤∑ i, B₁ i := sum_nonneg fun i _ => hB₁ i
  have ha₁ : a₁∈ChangingDomains.simplex A := (family C ell).update_mem _ _ _ _
  have ha₂ : a₂∈ChangingDomains.simplex B :=
    regular_transport_mem hA hB g h hh hC hl hc hmax hCexp htail hgap p hp₀ a ha
  have hcap₁ : ∀ i, (∑ j, B₁ j)*a₁ i≤(1+ct*h i/ell)*B₁ i :=
    regular_update_feasible hA (preparedFlags A B g) h hh hC hl hc hmax hCexp htail hgap
      p hp₀ (prepared_flags_outside A B g) a ha
  have hcap₂ : ∀ i, (∑ j, B₁ j)*a₂ i≤(1+ct*h i/ell)*B₁ i :=
    transpose_cap hB₁ (fun i => by linarith [(he i).1]) hcap₁
  have hin := ChangingDomains.synthetic_errors (fun i r => hp (i,r)) hf hg
  have herr₀ : ChangingDomains.variation B₀ B₁≤ChangingDomains.changedFlags f g := hin.1
  have herr₃ : ChangingDomains.variation B₃ B₁≤ChangingDomains.changedFlags f g := hin.2
  have hST : (∑ i, B₁ i)≤∑ i, B₃ i :=
    sub_nonneg.mp (ChangingDomains.synthetic_total (A := A) (B := B) (g := g) hp₀')
  have hδ : (∑ i, B₃ i)-(∑ i, B₁ i)≤ChangingDomains.changedFlags f g :=
    (le_abs_self _).trans ((total_variation_bound B₃ B₁).trans herr₃)
  have him₀ := regular_input_bound A hA f h (fun i => ct*h i/ell) hh he hC.le hl.le
    (B := B₀) (B' := B₁) ha
  have him₃ := regular_input_bound B hB g h' (fun i => ct*h' i/ell) hh' he' hC.le hl.le
    (B := B₃) (B' := B₁) ha₂
  have ht := regular_parameter_jump A B f g h h' (fun i => ct*h i/ell)
    (fun i => ct*h' i/ell) hh hh' he he' (fun i hi => by rw [hi]) hC.le hl.le
    hB₁ (fun i => ChangingDomains.simplex_coordinate ha₂ i) hcap₂
  have hpm₁ : (∑ i, B₁ i)*ChangingDomains.variation a₁ a ≤
      potential C ell d₀ B₁ a-potential C ell d₀ B₁ a₁ :=
    literal_update_payment C ell d₁ p (∑ i, B₁ i) ha
  have hpm₃ : (∑ i, B₃ i)*ChangingDomains.variation a₃ a₂ ≤
      potential C ell d₃ B₃ a₂-potential C ell d₃ B₃ a₃ :=
    literal_update_payment C ell d₃ p (∑ i, B₃ i) ha₂
  have htrans : potential C ell d₀ B₁ a₂=potential C ell d₀ B₁ a₁ :=
    regular_transpose_value A B f h (fun i => ct*h i/ell) hh C ell B₁ a₁ hB₁
  have hweight := ChangingDomains.prepared_weight_comparison ha ha₁ ha₂ hS₁ hST
    (ChangingDomains.transposeSimplex_payment B (∑ i, B₁ i) a₁) (a₃ := a₃)
  have hinput₀ := mul_le_mul_of_nonneg_left herr₀ (by positivity : 0≤3*C*ell)
  have hinput₃ := mul_le_mul_of_nonneg_left herr₃ (by positivity : 0≤3*C*ell)
  have he₀ := (neg_le_of_abs_le him₀)
  have he₃ := (le_of_abs_le him₃)
  have hep := le_of_abs_le ht
  change _ ≤ 8*C*ell*(∑ i, if h i=h' i then 0 else B₁ i) at hep
  change -(3*C*ell*ChangingDomains.variation B₀ B₁) ≤
    potential C ell d₀ B₀ a-potential C ell d₀ B₁ a at he₀
  change potential C ell d₃ B₃ a₂-potential C ell d₃ B₁ a₂ ≤
    3*C*ell*ChangingDomains.variation B₃ B₁ at he₃
  change potential C ell d₃ B₁ a₂-potential C ell d₀ B₁ a₂ ≤ _ at hep
  nlinarith

end KServer.AdaptiveAllocation

namespace KServer.AdaptiveAllocation
open Finset SimplexAnalytic SimplexFamilies AdaptiveMinimization
variable {J R : Type*} [Fintype J] [DecidableEq J] [Fintype R]

omit [Fintype R] in
lemma marked_input_bound (A : Finset J) (hA : A.Nonempty) (f : J → R → Bool)
    (o : J) (h eta : J → ℝ) {u : ℝ} (hu : 0<u) (hu1 : u≤1)
    (hh : ∀ i≠o, 1≤h i) (he : ∀ i, eta i∈Set.Icc 0 1)
    {C ell : ℝ} (hC : 0≤C) (hl : 0≤ell) {B B' a : J → ℝ}
    (ha : a∈ChangingDomains.simplex A) :
    |potential C ell (marked A f o h eta u hu hu1 hh) B a-
      potential C ell (marked A f o h eta u hu hu1 hh) B' a| ≤
      13*C*ell*ChangingDomains.variation B B' := by
  have hs : (∑ i, a i)=1 := by simpa only [ite_eq_left hA] using ha.2.1
  exact marked_input_slopes o ha.1 hs hh hu hu1 rfl (fun i => (he i).1)
    (fun i => (he i).2) hC hl

omit [Fintype R] in
lemma marked_potential_zero (A : Finset J) (f : J → R → Bool) (o : J)
    (h eta : J → ℝ) {u : ℝ} (hu : 0<u) (hu1 : u≤1) (hh : ∀ i≠o, 1≤h i)
    (C ell : ℝ) (a : J → ℝ) :
    potential C ell (marked A f o h eta u hu hu1 hh) (fun _ => 0) a=0 := by
  simp [potential,marked,primitive]

omit [Fintype R] in
lemma marked_transpose_value (A B : Finset J) (f : J → R → Bool) (o : J)
    (h eta : J → ℝ) {u : ℝ} (hu : 0<u) (hu1 : u≤1) (hh : ∀ i≠o, 1≤h i)
    (C ell : ℝ) (v a : J → ℝ) (hv : ∀ i, 0≤v i) :
    potential C ell (marked A f o h eta u hu hu1 hh) v
      (ChangingDomains.transposeSimplex B (∑ i, v i) a)=
    potential C ell (marked A f o h eta u hu hu1 hh) v a := by
  by_cases hS : (∑ i, v i)=0
  · rw [nonneg_total_zero hv hS]
    simp only [marked_potential_zero]
  · simp [ChangingDomains.transposeSimplex,hS]

lemma simplex_side_weight {A : Finset J} (hA : A.Nonempty) {a B eta : J → ℝ}
    (ha : a∈ChangingDomains.simplex A) (hB : ∀ i, 0≤B i)
    (he : ∀ i, eta i≤1) (hcap : ∀ i, (∑ j, B j)*a i≤(1+eta i)*B i) (o : J) :
    (∑ j, B j)*(1-a o)≤2*(∑ i∈Finset.univ.erase o, B i) := by
  have hs : (∑ i, a i)=1 := by simpa only [ite_eq_left hA] using ha.2.1
  have hx : 1-a o=∑ i∈Finset.univ.erase o, a i := by
    have ht := Finset.add_sum_erase Finset.univ (fun i => a i) (Finset.mem_univ o)
    rw [hs] at ht
    linarith
  rw [hx,mul_sum,mul_sum]
  exact sum_le_sum fun i _ => (hcap i).trans
    (mul_le_mul_of_nonneg_right (by linarith [he i]) (hB i))

omit [Fintype R] in
/-- Marked parameter edits charge the dominant component only when `u`
changes, and charge it to the side total, not the dominant mass. -/
lemma marked_parameter_jump (A A' : Finset J) (hA' : A'.Nonempty)
    (f g : J → R → Bool) (o : J) (h h' eta eta' : J → ℝ)
    {u u' : ℝ} (hu : 0<u) (hu1 : u≤1) (hu' : 0<u') (hu1' : u'≤1)
    (hh : ∀ i≠o, 1≤h i) (hh' : ∀ i≠o, 1≤h' i)
    (he : ∀ i, eta i∈Set.Icc 0 1) (he' : ∀ i, eta' i∈Set.Icc 0 1)
    (heq : ∀ i, h i=h' i → eta i=eta' i)
    (heqo : u=u' → eta o=eta' o) (heo : eta o≤u) (heo' : eta' o≤u')
    {C ell : ℝ} (hC : 0≤C) (hl : 0≤ell) {B a : J → ℝ}
    (hB : ∀ i, 0≤B i) (ha : a∈ChangingDomains.simplex A')
    (hcap : ∀ i, (∑ j, B j)*a i≤(1+eta i)*B i) :
    |potential C ell (marked A' g o h' eta' u' hu' hu1' hh') B a-
      potential C ell (marked A f o h eta u hu hu1 hh) B a| ≤
      8*C*ell*(∑ i∈Finset.univ.erase o, if h i=h' i then 0 else B i)+
      24*C*ell*(if u=u' then 0 else
        (∑ i∈Finset.univ.erase o, B i)+(u+u')*(∑ i, B i)) := by
  let d₀ := marked A f o h eta u hu hu1 hh
  let d₁ := marked A' g o h' eta' u' hu' hu1' hh'
  let term := fun i => primitive (d₁.F i) C ell (eta' i) (∑ j, B j) (B i) (d₁.base i) (a i)-
    primitive (d₀.F i) C ell (eta i) (∑ j, B j) (B i) (d₀.base i) (a i)
  have hS : 0≤∑ i, B i := sum_nonneg fun i _ => hB i
  have hBs : 0≤∑ i∈Finset.univ.erase o, B i := sum_nonneg fun i _ => hB i
  have hai := fun i => ChangingDomains.simplex_coordinate ha i
  have hside := simplex_side_weight hA' ha hB (fun i => (he i).2) hcap o
  have hSpr : (∑ j, B j)=B o+∑ i∈Finset.univ.erase o, B i :=
    (Finset.add_sum_erase Finset.univ B (Finset.mem_univ o)).symm
  have hregular (i : J) (hi : i∈Finset.univ.erase o) :
      |term i|≤8*C*ell*(if h i=h' i then 0 else B i) := by
    have hio : i≠o := (Finset.mem_erase.mp hi).1
    change |primitive (if i=o then markedF u' (1+Real.log (1/u')) else regularF (h' i))
       C ell (eta' i) (∑ j, B j) (B i) (if i=o then 1 else 0) (a i)-
      primitive (if i=o then markedF u (1+Real.log (1/u)) else regularF (h i))
       C ell (eta i) (∑ j, B j) (B i) (if i=o then 1 else 0) (a i)|≤_
    simp only [ite_eq_right hio]
    by_cases hx : h i=h' i
    · simp [hx,heq i hx]
    · rw [ite_eq_right hx]
      have ho := regular_component_bound (hh i hio) (hai i) hC hl (he i).1 hS (hB i)
      have hn := regular_component_bound (hh' i hio) (hai i) hC hl (he' i).1 hS (hB i)
      have hep := mul_le_mul_of_nonneg_right (he i).2 (hB i)
      have he'p := mul_le_mul_of_nonneg_right (he' i).2 (hB i)
      have hlo : (∑ j, B j)*a i+(1+eta i)*B i≤4*B i := by nlinarith [hcap i]
      have hln : (∑ j, B j)*a i+(1+eta' i)*B i≤4*B i := by nlinarith [hcap i]
      have hco := mul_le_mul_of_nonneg_left hlo (mul_nonneg hC hl)
      have hcn := mul_le_mul_of_nonneg_left hln (mul_nonneg hC hl)
      have hab := abs_sub
        (primitive (regularF (h' i)) C ell (eta' i) (∑ j, B j) (B i) 0 (a i))
        (primitive (regularF (h i)) C ell (eta i) (∑ j, B j) (B i) 0 (a i))
      nlinarith
  have hmarked : |term o|≤24*C*ell*(if u=u' then 0 else
      (∑ i∈Finset.univ.erase o, B i)+(u+u')*(∑ i, B i)) := by
    change |primitive (if o=o then markedF u' (1+Real.log (1/u')) else regularF (h' o))
       C ell (eta' o) (∑ j, B j) (B o) (if o=o then 1 else 0) (a o)-
      primitive (if o=o then markedF u (1+Real.log (1/u)) else regularF (h o))
       C ell (eta o) (∑ j, B j) (B o) (if o=o then 1 else 0) (a o)|≤_
    simp only [ite_true]
    by_cases hx : u=u'
    · simp [hx,heqo hx]
    · rw [ite_eq_right hx]
      have ho := marked_component_bound hu hu1 rfl (hai o) hC hl (he o).1 heo (hB o) hBs hSpr
      have hn := marked_component_bound hu' hu1' rfl (hai o) hC hl (he' o).1 heo' (hB o) hBs hSpr
      have hab := abs_sub
        (primitive (markedF u' (1+Real.log (1/u'))) C ell (eta' o) (∑ j, B j) (B o) 1 (a o))
        (primitive (markedF u (1+Real.log (1/u))) C ell (eta o) (∑ j, B j) (B o) 1 (a o))
      have hs := mul_le_mul_of_nonneg_left hside (by positivity : 0≤8*C*ell)
      have hpos : 0≤C*ell*(u+u')*(∑ j, B j) := by positivity
      nlinarith
  change |(∑ i, primitive (d₁.F i) C ell (eta' i) (∑ j, B j) (B i) (d₁.base i) (a i))-
    ∑ i, primitive (d₀.F i) C ell (eta i) (∑ j, B j) (B i) (d₀.base i) (a i)|≤_
  rw [←sum_sub_distrib]
  change |∑ i, term i|≤_
  have ht := (abs_sum_le_sum_abs term Finset.univ)
  rw [←Finset.add_sum_erase Finset.univ (fun i => |term i|) (Finset.mem_univ o)] at ht
  have hr := sum_le_sum hregular
  rw [←mul_sum] at hr
  linarith

end KServer.AdaptiveAllocation

namespace KServer.AdaptiveAllocation
open Finset SimplexAnalytic SimplexFamilies AdaptiveMinimization
variable {J R : Type*} [Fintype J] [DecidableEq J] [Fintype R]

lemma marked_transport_mem {A B : Finset J} {o : J} (hoA : o∈A) (hB : B.Nonempty)
    (g : J → R → Bool) (h : J → ℝ) {u : ℝ} (hu : 0<u) (hu1 : u≤1)
    (ho : h o=u) (hh : ∀ i≠o, 1≤h i)
    {C ell ct ηmax Cexp c : ℝ} (hC : 0<C) (hl : 0<ell) (hc : 0 < ct)
    (hmax : ∀ i∈A, ct*h i/ell≤ηmax) (hCexp : 0≤Cexp)
    (hsideC : 0 < c) (hsideC1 : c≤1)
    (hside : ∀ i∈A, i≠o → c*(1+Real.log (1/u))≤h i)
    (htail : ∑ i∈A.erase o, Real.exp (-h i)≤Cexp*u)
    (hgap : 2*((25*c+2+32*Cexp)/c)*(1+ηmax)<C*ct)
    (p : J × R → ℝ) (hp : ∀ ir, 0≤p ir) (a : J → ℝ)
    (ha : a∈ChangingDomains.simplex A) :
    markedTransport C ell ct A B g o h u hu hu1 hh p a∈ChangingDomains.simplex B := by
  have hp' : ∀ i r, 0≤p (i,r) := fun i r => hp (i,r)
  have hcap := marked_update_feasible hoA (preparedFlags A B g) h hu hu1 ho hh
    hC hl hc hmax hCexp hsideC hsideC1 hside htail hgap p hp
    (prepared_flags_outside A B g) a ha
  exact ChangingDomains.transposeSimplex_mem (v := preparedInput A B g p)
    ⟨o,hoA⟩ hB ((family C ell).update_mem _ _ _ _)
    (sum_nonneg fun i _ => ChangingDomains.core_nonneg hp' i) hcap
    (prepared_input_outside A B g p)

lemma marked_step_payment {A B : Finset J} {o : J} (hoA : o∈A) (hB : B.Nonempty)
    (f g : J → R → Bool) (h h' : J → ℝ) {u u' : ℝ}
    (hu : 0<u) (hu1 : u≤1) (hu' : 0<u') (hu1' : u'≤1)
    (ho : h o=u) (ho' : h' o=u') (hh : ∀ i≠o, 1≤h i) (hh' : ∀ i≠o, 1≤h' i)
    {C ell ct ηmax Cexp c : ℝ} (hC : 0<C) (hl : 0<ell) (hc : 0 < ct)
    (he : ∀ i, ct*h i/ell∈Set.Icc 0 1) (he' : ∀ i, ct*h' i/ell∈Set.Icc 0 1)
    (hoeta : ct*u/ell≤u) (hoeta' : ct*u'/ell≤u')
    (hmax : ∀ i∈A, ct*h i/ell≤ηmax) (hCexp : 0≤Cexp)
    (hsideC : 0 < c) (hsideC1 : c≤1)
    (hside : ∀ i∈A, i≠o → c*(1+Real.log (1/u))≤h i)
    (htail : ∑ i∈A.erase o, Real.exp (-h i)≤Cexp*u)
    (hgap : 2*((25*c+2+32*Cexp)/c)*(1+ηmax)<C*ct)
    (p : J × R → ℝ) (hp : ∀ ir, p ir∈Set.Icc 0 1)
    (hf : ∀ i∉A, ∀ r, f i r=false) (hg : ∀ i∉B, ∀ r, g i r=false)
    (a : J → ℝ) (ha : a∈ChangingDomains.simplex A) :
    let d₀ := marked A f o h (fun i => ct*h i/ell) u hu hu1 hh
    let d₃ := marked B g o h' (fun i => ct*h' i/ell) u' hu' hu1' hh'
    let B₀ := core d₀ p
    let B₃ := core d₃ p
    let B₁ := preparedInput A B g p
    let a₃ := markedStep C ell ct A B g o h h' u u' hu hu1 hu' hu1' hh hh' p a
    (∑ i, B₃ i)*ChangingDomains.variation a₃ a ≤
      potential C ell d₀ B₀ a-potential C ell d₃ B₃ a₃+
      (26*C*ell+4)*ChangingDomains.changedFlags f g+
      8*C*ell*(∑ i∈Finset.univ.erase o, if h i=h' i then 0 else B₁ i)+
      24*C*ell*(if u=u' then 0 else
        (∑ i∈Finset.univ.erase o, B₁ i)+(u+u')*(∑ i, B₁ i)) := by
  intro d₀ d₃ B₀ B₃ B₁ a₃
  let d₁ := marked A (preparedFlags A B g) o h (fun i => ct*h i/ell) u hu hu1 hh
  let a₁ := markedPrepare C ell ct A B g o h u hu hu1 hh p a
  let a₂ := markedTransport C ell ct A B g o h u hu hu1 hh p a
  have hA : A.Nonempty := ⟨o,hoA⟩
  have hp₀ : ∀ ir, 0≤p ir := fun ir => (hp ir).1
  have hp₀' : ∀ i r, 0≤p (i,r) := fun i r => (hp (i,r)).1
  have hB₁ : ∀ i, 0≤B₁ i := fun i => ChangingDomains.core_nonneg hp₀' i
  have hS₁ : 0≤∑ i, B₁ i := sum_nonneg fun i _ => hB₁ i
  have ha₁ : a₁∈ChangingDomains.simplex A := (family C ell).update_mem _ _ _ _
  have ha₂ : a₂∈ChangingDomains.simplex B :=
    marked_transport_mem hoA hB g h hu hu1 ho hh hC hl hc hmax hCexp
      hsideC hsideC1 hside htail hgap p hp₀ a ha
  have hcap₁ : ∀ i, (∑ j, B₁ j)*a₁ i≤(1+ct*h i/ell)*B₁ i :=
    marked_update_feasible hoA (preparedFlags A B g) h hu hu1 ho hh hC hl hc hmax hCexp
      hsideC hsideC1 hside htail hgap p hp₀ (prepared_flags_outside A B g) a ha
  have hcap₂ : ∀ i, (∑ j, B₁ j)*a₂ i≤(1+ct*h i/ell)*B₁ i :=
    transpose_cap hB₁ (fun i => by linarith [(he i).1]) hcap₁
  have hin := ChangingDomains.synthetic_errors (fun i r => hp (i,r)) hf hg
  have herr₀ : ChangingDomains.variation B₀ B₁≤ChangingDomains.changedFlags f g := hin.1
  have herr₃ : ChangingDomains.variation B₃ B₁≤ChangingDomains.changedFlags f g := hin.2
  have hST : (∑ i, B₁ i)≤∑ i, B₃ i :=
    sub_nonneg.mp (ChangingDomains.synthetic_total (A := A) (B := B) (g := g) hp₀')
  have hδ : (∑ i, B₃ i)-(∑ i, B₁ i)≤ChangingDomains.changedFlags f g :=
    (le_abs_self _).trans ((total_variation_bound B₃ B₁).trans herr₃)
  have him₀ := marked_input_bound A hA f o h (fun i => ct*h i/ell) hu hu1 hh he
    hC.le hl.le (B := B₀) (B' := B₁) ha
  have him₃ := marked_input_bound B hB g o h' (fun i => ct*h' i/ell) hu' hu1' hh' he'
    hC.le hl.le (B := B₃) (B' := B₁) ha₂
  have ht := marked_parameter_jump A B hB f g o h h' (fun i => ct*h i/ell)
    (fun i => ct*h' i/ell) hu hu1 hu' hu1' hh hh' he he'
    (fun i hi => by rw [hi]) (fun hi => by rw [ho,ho',hi])
    (by simpa [ho] using hoeta) (by simpa [ho'] using hoeta') hC.le hl.le hB₁ ha₂ hcap₂
  have hpm₁ : (∑ i, B₁ i)*ChangingDomains.variation a₁ a ≤
      potential C ell d₀ B₁ a-potential C ell d₀ B₁ a₁ :=
    literal_update_payment C ell d₁ p (∑ i, B₁ i) ha
  have hpm₃ : (∑ i, B₃ i)*ChangingDomains.variation a₃ a₂ ≤
      potential C ell d₃ B₃ a₂-potential C ell d₃ B₃ a₃ :=
    literal_update_payment C ell d₃ p (∑ i, B₃ i) ha₂
  have htrans : potential C ell d₀ B₁ a₂=potential C ell d₀ B₁ a₁ :=
    marked_transpose_value A B f o h (fun i => ct*h i/ell) hu hu1 hh C ell B₁ a₁ hB₁
  have hweight := ChangingDomains.prepared_weight_comparison ha ha₁ ha₂ hS₁ hST
    (ChangingDomains.transposeSimplex_payment B (∑ i, B₁ i) a₁) (a₃ := a₃)
  have hinput₀ := mul_le_mul_of_nonneg_left herr₀ (by positivity : 0≤13*C*ell)
  have hinput₃ := mul_le_mul_of_nonneg_left herr₃ (by positivity : 0≤13*C*ell)
  have he₀ := neg_le_of_abs_le him₀
  have he₃ := le_of_abs_le him₃
  have hep := le_of_abs_le ht
  change -(13*C*ell*ChangingDomains.variation B₀ B₁) ≤
    potential C ell d₀ B₀ a-potential C ell d₀ B₁ a at he₀
  change potential C ell d₃ B₃ a₂-potential C ell d₃ B₁ a₂ ≤
    13*C*ell*ChangingDomains.variation B₃ B₁ at he₃
  change potential C ell d₃ B₁ a₂-potential C ell d₀ B₁ a₂ ≤ _ at hep
  nlinarith

end KServer.AdaptiveAllocation

/-! Exact side primitive and compact minimizing update of §04,
    eq:side-primitive-explicit and lem:side-tracker. This is an allocation
    dependency of the absent main, not a separately counted main theorem. -/
noncomputable section
open scoped BigOperators
open Set Filter

namespace KServer.SideTracker
open scoped BigOperators

lemma log_factors {z w : ℝ} (hz : 0 < z) (hw : 0 ≤ w) :
    0 ≤ Real.log (1 + w / z) ∧
    0 ≤ z * Real.log (1 + w / z) ∧
    z * Real.log (1 + w / z) ≤ w := by
  have hq : 0 ≤ w / z := div_nonneg hw hz.le
  have hl : 0 ≤ Real.log (1 + w / z) := Real.log_nonneg (by linarith)
  refine ⟨hl, mul_nonneg hz.le hl, ?_⟩
  have hh := Real.log_le_sub_one_of_pos (show 0 < 1 + w / z by positivity)
  have hh' : Real.log (1 + w / z) ≤ w / z := by linarith
  have := mul_le_mul_of_nonneg_left hh' hz.le
  simpa [mul_div_cancel₀ _ hz.ne'] using this

lemma side_log_bound {h W w : ℝ} (hh : 1 ≤ h) (hW : 0 ≤ W)
    (hw : w ∈ Set.Icc 0 W) :
    Real.log (1 + w / (Real.exp (1 - h) / h)) ≤
      (Real.log (1 + W) + 2) * h := by
  have hp : 0 < h := lt_of_lt_of_le zero_lt_one hh
  have hw0 : 0 ≤ w := hw.1
  have he : 1 ≤ Real.exp (h - 1) := Real.one_le_exp (by linarith)
  have hh' : h ≤ Real.exp (h - 1) := by
    have := Real.add_one_le_exp (h - 1)
    linarith
  have hE := Real.exp_pos (h - 1)
  have heq : 1 + w / (Real.exp (1 - h) / h) =
      1 + w * h * Real.exp (h - 1) := by
    have hn : 1 - h = -(h - 1) := by ring
    rw [hn, Real.exp_neg]
    field_simp
  rw [heq]
  have hmul : w * h * Real.exp (h - 1) ≤ W * Real.exp (h - 1) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hw.2 hp.le,
      mul_le_mul_of_nonneg_left hh' hW,
      mul_le_mul_of_nonneg_right
        (mul_le_mul hw.2 hh' hp.le hW) hE.le]
  have hs : 1 ≤ Real.exp (h - 1) ^ 2 := by nlinarith
  have hbound : 1 + w * h * Real.exp (h - 1) ≤
      (1 + W) * Real.exp (2 * (h - 1)) := by
    rw [show 2 * (h - 1) = (h - 1) + (h - 1) by ring, Real.exp_add]
    nlinarith
  have hlog := Real.log_le_log (show 0 < 1 + w * h * Real.exp (h - 1) by positivity) hbound
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp] at hlog
  have hLW : 0 ≤ Real.log (1 + W) := Real.log_nonneg (by linarith)
  nlinarith

lemma coefficients_nonneg {c b θ z w : ℝ} (hc : 0 ≤ c) (hb : 0 ≤ b)
    (hθ : 0 < θ) (hz : 0 < z) (hw : 0 ≤ w) :
    0 ≤ Dcoef c θ z w ∧ 0 ≤ Bcoef c b θ z w := by
  obtain ⟨hL, hzL, hLw⟩ := log_factors hz hw
  constructor
  · exact mul_nonneg hc (add_nonneg (div_nonneg (sub_nonneg.mpr hLw) hθ.le)
      (by positivity))
  · exact div_nonneg (mul_nonneg (mul_nonneg hc (by positivity)) hL) hθ.le

lemma Dcoef_bound {c θ z w cw ell h : ℝ} (hc : 0 ≤ c)
    (hz : 0 < z) (hw : 0 ≤ w) (hcw : 0 < cw) (hell : 1 ≤ ell)
    (hh : 1 ≤ h) (hθ : θ = cw * h / ell) :
    Dcoef c θ z w ≤ c * (1 / cw + 1) * ell * w := by
  have hellp : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have hp : 0 < h := lt_of_lt_of_le zero_lt_one hh
  have hθp : 0 < θ := by rw [hθ]; positivity
  obtain ⟨hL, hzL, hLw⟩ := log_factors hz hw
  have hi : 1 / θ ≤ ell / cw := by
    rw [div_le_div_iff₀ hθp hcw]
    rw [hθ]
    have he : ell * (cw * h / ell) = cw * h := by field_simp
    rw [he]
    nlinarith
  have ht : (w - z * Real.log (1 + w / z)) / θ ≤ w * (ell / cw) := by
    calc
      _ ≤ w / θ := div_le_div_of_nonneg_right (by linarith) hθp.le
      _ = w * (1 / θ) := by ring
      _ ≤ w * (ell / cw) := mul_le_mul_of_nonneg_left hi hw
  have hq : z * Real.log (1 + w / z) / 2 ≤ ell * w := by nlinarith
  unfold Dcoef
  calc
    _ ≤ c * (w * (ell / cw) + ell * w) :=
      mul_le_mul_of_nonneg_left (add_le_add ht hq) hc
    _ = c * (1 / cw + 1) * ell * w := by ring

lemma Bcoef_bound {c b θ z w cw ell h K M : ℝ} (hc : 0 ≤ c)
    (hb : 0 ≤ b) (hz : 0 < z) (hw : 0 ≤ w) (hcw : 0 < cw)
    (hell : 0 < ell) (hh : 0 < h) (hθ : θ = cw * h / ell)
    (hBM : b + θ / 2 ≤ M)
    (hLK : Real.log (1 + w / z) ≤ K * h) :
    Bcoef c b θ z w ≤ c * M * K / cw * ell := by
  have hθp : 0 < θ := by rw [hθ]; positivity
  obtain ⟨hL, _, _⟩ := log_factors hz hw
  have hM : 0 ≤ M := (by positivity : 0 ≤ b + θ / 2).trans hBM
  unfold Bcoef
  calc
    _ ≤ c * M * (K * h) / θ := div_le_div_of_nonneg_right
      (mul_le_mul (mul_le_mul_of_nonneg_left hBM hc) hLK hL (mul_nonneg hc hM)) hθp.le
    _ = c * M * K / cw * ell := by rw [hθ]; field_simp

lemma primitive_component_bound {c b θ z w cw ell h K M B D : ℝ}
    (hc : 0 ≤ c) (hb : 0 ≤ b) (hz : 0 < z) (hw : 0 ≤ w)
    (hcw : 0 < cw) (hell : 1 ≤ ell) (hh : 1 ≤ h)
    (hθ : θ = cw * h / ell) (hBM : b + θ / 2 ≤ M)
    (hLK : Real.log (1 + w / z) ≤ K * h) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    |primitive c b θ z B D w| ≤
      c * (1 / cw + 1) * ell * (D * w) + c * M * K / cw * ell * B := by
  have he : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have hp : 0 < h := lt_of_lt_of_le zero_lt_one hh
  have hθp : 0 < θ := by rw [hθ]; positivity
  have hn := coefficients_nonneg hc hb hθp hz hw
  rw [primitive_coefficients]
  calc
    _ ≤ |Dcoef c θ z w * D| + |Bcoef c b θ z w * B| := abs_sub _ _
    _ = Dcoef c θ z w * D + Bcoef c b θ z w * B := by
      rw [abs_of_nonneg (mul_nonneg hn.1 hD), abs_of_nonneg (mul_nonneg hn.2 hB)]
    _ ≤ (c * (1 / cw + 1) * ell * w) * D + (c * M * K / cw * ell) * B :=
      add_le_add (mul_le_mul_of_nonneg_right (Dcoef_bound hc hz hw hcw hell hh hθ) hD)
        (mul_le_mul_of_nonneg_right (Bcoef_bound hc hb hz hw hcw he hp hθ hBM hLK) hB)
    _ = _ := by ring

lemma potential_input_bound {ι : Type*} [Fintype ι]
    {c b cw ell K M Cw : ℝ} {θ z h w : ι → ℝ}
    (hc : 0 ≤ c) (hb : 0 ≤ b) (hcw : 0 < cw) (hell : 1 ≤ ell)
    (hz : ∀ i, 0 < z i) (hh : ∀ i, 1 ≤ h i)
    (hθ : ∀ i, θ i = cw * h i / ell)
    (hBM : ∀ i, b + θ i / 2 ≤ M)
    (hLK : ∀ i, Real.log (1 + w i / z i) ≤ K * h i)
    (hw : w ∈ domain Cw) (B B' : ι → ℝ) (D D' : ℝ) :
    |potential c b θ z B D w - potential c b θ z B' D' w| ≤
      c * (1 / cw + 1) * ell * Cw * |D - D'| +
        c * M * K / cw * ell * (∑ i, |B i - B' i|) := by
  have he : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have hdc (i) := Dcoef_bound hc (hz i) (hw.1 i) hcw hell (hh i) (hθ i)
  have hbc (i) := Bcoef_bound hc hb (hz i) (hw.1 i) hcw he
    (lt_of_lt_of_le zero_lt_one (hh i)) (hθ i) (hBM i) (hLK i)
  have hnn (i) : 0 ≤ Dcoef c (θ i) (z i) (w i) ∧
      0 ≤ Bcoef c b (θ i) (z i) (w i) :=
    coefficients_nonneg hc hb (by rw [hθ i]; exact div_pos (mul_pos hcw (lt_of_lt_of_le zero_lt_one (hh i))) he) (hz i) (hw.1 i)
  have hdiff (i) : primitive c b (θ i) (z i) (B i) D (w i) -
      primitive c b (θ i) (z i) (B' i) D' (w i) =
      Dcoef c (θ i) (z i) (w i) * (D - D') -
      Bcoef c b (θ i) (z i) (w i) * (B i - B' i) := by
    rw [primitive_coefficients, primitive_coefficients]
    ring
  have hpoint (i) : |primitive c b (θ i) (z i) (B i) D (w i) -
      primitive c b (θ i) (z i) (B' i) D' (w i)| ≤
      c * (1 / cw + 1) * ell * w i * |D - D'| +
        c * M * K / cw * ell * |B i - B' i| := by
    rw [hdiff]
    calc
      _ ≤ |Dcoef c (θ i) (z i) (w i) * (D - D')| +
          |Bcoef c b (θ i) (z i) (w i) * (B i - B' i)| := abs_sub _ _
      _ = Dcoef c (θ i) (z i) (w i) * |D - D'| +
          Bcoef c b (θ i) (z i) (w i) * |B i - B' i| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (hnn i).1, abs_of_nonneg (hnn i).2]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right (hdc i) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (hbc i) (abs_nonneg _))
  unfold potential
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |primitive c b (θ i) (z i) (B i) D (w i) -
        primitive c b (θ i) (z i) (B' i) D' (w i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (c * (1 / cw + 1) * ell * w i * |D - D'| +
        c * M * K / cw * ell * |B i - B' i|) := Finset.sum_le_sum fun i _ => hpoint i
    _ = c * (1 / cw + 1) * ell * (∑ i, w i) * |D - D'| +
        c * M * K / cw * ell * (∑ i, |B i - B' i|) := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hw.2 (by positivity)) (abs_nonneg _)) le_rfl

end KServer.SideTracker

namespace KServer.SideFamilies
open Finset SideTracker AdaptiveMinimization
variable {J R : Type*} [Fintype J] [DecidableEq J] [Fintype R]

omit [DecidableEq J] [Fintype R] in
lemma fromLog_input_bound {A : Finset J} (_flags : J → R → Bool)
    {W b cw ell c M D D' : ℝ} (h : J → ℝ)
    (hW : 0≤W) (hcw : 0 < cw) (hell : 1≤ell) (hh : ∀ i, 1≤h i)
    (hc : 0 ≤ c) (hb : 0≤b) (hM : ∀ i, b+cw*h i/ell≤M)
    {a B B' : J → ℝ} (ha : a∈ChangingDomains.sideDomain A W) :
    |potential c b (fun i => cw*h i/ell) (fun i => Real.exp (1-h i)/h i) B D a-
      potential c b (fun i => cw*h i/ell) (fun i => Real.exp (1-h i)/h i) B' D' a|≤
      c*(1/cw+1)*ell*W*|D-D'|+
        c*M*(Real.log (1+W)+2)/cw*ell*ChangingDomains.variation B B' := by
  have hp : 0<ell := lt_of_lt_of_le zero_lt_one hell
  apply potential_input_bound hc hb hcw hell
    (fun i => div_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one (hh i))) hh
    (fun _ => rfl)
  · intro i
    have ht : 0 ≤ cw*h i/ell := div_nonneg (mul_nonneg hcw.le (le_trans zero_le_one (hh i))) hp.le
    linarith [hM i]
  · intro i
    apply side_log_bound (hh i) hW
    exact ⟨ha.1 i,(single_le_sum (fun j _ => ha.1 j) (mem_univ i)).trans ha.2.1⟩
  · exact ⟨ha.1,ha.2.1⟩

omit [DecidableEq J] in
lemma parameter_jump {W b cw ell c M D : ℝ} {h h' B a : J → ℝ}
    (hW : 0≤W) (hcw : 0 < cw) (hell : 1≤ell)
    (hh : ∀ i, 1≤h i) (hh' : ∀ i, 1≤h' i)
    (hc : 0 ≤ c) (hb : 0≤b) (hD : 0≤D) (hB : ∀ i, 0≤B i)
    (hM : ∀ i, b+cw*h i/ell≤M) (hM' : ∀ i, b+cw*h' i/ell≤M)
    (ha : a∈domain W) (hcap : ∀ i, D*a i≤M*B i) :
    |potential c b (fun i => cw*h' i/ell) (fun i => Real.exp (1-h' i)/h' i) B D a-
      potential c b (fun i => cw*h i/ell) (fun i => Real.exp (1-h i)/h i) B D a|≤
      2*(c*(1/cw+1)*M+c*M*(Real.log (1+W)+2)/cw)*ell*
        (∑ i, if h i=h' i then 0 else B i) := by
  have hp : 0<ell := lt_of_lt_of_le zero_lt_one hell
  have hw (i : J) : a i∈Set.Icc 0 W :=
    ⟨ha.1 i,(single_le_sum (fun j _ => ha.1 j) (mem_univ i)).trans ha.2⟩
  have hbound (q : J → ℝ) (hq : ∀ i, 1≤q i) (hMq : ∀ i, b+cw*q i/ell≤M) (i : J) :
      |primitive c b (cw*q i/ell) (Real.exp (1-q i)/q i) (B i) D (a i)|≤
        (c*(1/cw+1)*M+c*M*(Real.log (1+W)+2)/cw)*ell*B i := by
    have ht : 0 ≤ cw*q i/ell := div_nonneg (mul_nonneg hcw.le (le_trans zero_le_one (hq i))) hp.le
    have he := primitive_component_bound hc hb
      (div_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one (hq i))) (ha.1 i)
      hcw hell (hq i) rfl (show b+(cw*q i/ell)/2≤M by linarith [hMq i])
      (side_log_bound (hq i) hW (hw i)) (hB i) hD
    have hcap' := mul_le_mul_of_nonneg_left (hcap i)
      (show 0 ≤ c*(1/cw+1)*ell by positivity)
    calc
      _ ≤ c*(1/cw+1)*ell*(D*a i)+
        c*M*(Real.log (1+W)+2)/cw*ell*B i := he
      _ ≤ c*(1/cw+1)*ell*(M*B i)+
        c*M*(Real.log (1+W)+2)/cw*ell*B i := add_le_add hcap' le_rfl
      _ = _ := by ring
  unfold potential
  rw [←sum_sub_distrib,mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro i _
  by_cases hi : h i=h' i
  · simp [hi]
  · rw [ite_eq_right hi]
    have ho := hbound h hh hM i
    have hn := hbound h' hh' hM' i
    exact (abs_sub _ _).trans (by linarith)

omit [Fintype J] in
lemma prepared_core_zero (old new : Data J R) (p : J × R → ℝ)
    {i : J} (hi : i∉old.active∩new.active) : core (prepareData old new) p i=0 := by
  simp [core,prepareData,ChangingDomains.syntheticFlags,hi]

lemma transport_payment (old new : Data J R) {M : ℝ}
    (hb : 1≤old.b) (hD : 0≤new.D)
    (hM : ∀ i∈old.active, old.b+old.θ i≤M) (hW : 2*M<old.W)
    (p : J × R → ℝ) (hp : ∀ ir, 0≤p ir)
    (a : J → ℝ) (ha : a∈ChangingDomains.sideDomain old.active old.W) :
    new.D*ChangingDomains.variation (transport (8*M) old new p a)
      (prepare (8*M) old new p a)=0 := by
  have hfeas := update_feasible (prepareData old new) hb hD hM hW p hp
    (fun i hi r => by
      change i∉old.active at hi
      simp [prepareData,ChangingDomains.syntheticFlags,hi]) a ha
  exact ChangingDomains.transposeSide_payment (prepare_mem (8*M) old new p a).1 hD
    hfeas.1 (fun i hi => prepared_core_zero old new p (by simp [hi]))

lemma transport_value (c : ℝ) (old new : Data J R) (p : J × R → ℝ) (a : J → ℝ)
    (hzero : new.D*ChangingDomains.variation (transport c old new p a)
      (prepare c old new p a)=0) :
    (family c).value (prepareData old new) p (transport c old new p a)=
      (family c).value (prepareData old new) p (prepare c old new p a) := by
  rw [value_eq,value_eq]
  unfold potential
  apply sum_congr rfl
  intro i _
  by_cases hi : i∈new.active
  · simp [transport,ChangingDomains.transposeSide,hi]
  · have hB : core (prepareData old new) p i=0 :=
      prepared_core_zero old new p (by simp [hi])
    by_cases hD : new.D=0
    · rw [hB]
      change primitive c old.b (old.θ i) (old.z i) 0 new.D _ =
        primitive c old.b (old.θ i) (old.z i) 0 new.D _
      simp [hD,primitive]
    · have hvar : ChangingDomains.variation (transport c old new p a)
          (prepare c old new p a)=0 := (mul_eq_zero.mp hzero).resolve_left hD
      have hd := single_le_sum (s := univ)
        (f := fun j => |transport c old new p a j-prepare c old new p a j|)
        (fun j _ => abs_nonneg _) (mem_univ i)
      change |transport c old new p a i-prepare c old new p a i|≤
        ChangingDomains.variation (transport c old new p a) (prepare c old new p a) at hd
      rw [hvar] at hd
      have he := sub_eq_zero.mp (abs_nonpos_iff.mp hd)
      rw [he]

/-- Local side edit payment for the actual two minimizers and deletion.  The
potential discrepancy terms will be bounded with the literal log parameters. -/
lemma step_payment (old new : Data J R) {M : ℝ}
    (hb : 1≤old.b) (hD : 0≤new.D)
    (hM : ∀ i∈old.active, old.b+old.θ i≤M) (hW : 2*M<old.W)
    (p : J × R → ℝ) (hp : ∀ ir, 0≤p ir)
    (a : J → ℝ) (ha : a∈ChangingDomains.sideDomain old.active old.W)
    (hWW : old.W=new.W) :
    new.D*ChangingDomains.variation (step (8*M) old new p a) a ≤
      (family (8*M)).value old p a-(family (8*M)).value new p (step (8*M) old new p a)+
      |(family (8*M)).value (prepareData old new) p a-(family (8*M)).value old p a|+
      |(family (8*M)).value new p (transport (8*M) old new p a)-
        (family (8*M)).value (prepareData old new) p (transport (8*M) old new p a)| := by
  have hz := transport_payment old new hb hD hM hW p hp a ha
  have he := transport_value (8*M) old new p a hz
  have h₁ := (family (8*M)).update_payment (prepareData old new) p new.D ha
  have h₂ := (family (8*M)).update_payment new p new.D (transport_mem (8*M) old new p a hWW)
  have hm₁ := ChangingDomains.variation_triangle (step (8*M) old new p a)
    (transport (8*M) old new p a) a
  have hm₂ := ChangingDomains.variation_triangle (transport (8*M) old new p a)
    (prepare (8*M) old new p a) a
  have hp₁ := mul_le_mul_of_nonneg_left hm₁ hD
  have hp₂ := mul_le_mul_of_nonneg_left hm₂ hD
  change new.D*ChangingDomains.variation (prepare (8*M) old new p a) a ≤
    (family (8*M)).value (prepareData old new) p a-
      (family (8*M)).value (prepareData old new) p (prepare (8*M) old new p a) at h₁
  change new.D*ChangingDomains.variation (step (8*M) old new p a)
    (transport (8*M) old new p a) ≤
    (family (8*M)).value new p (transport (8*M) old new p a)-
      (family (8*M)).value new p (step (8*M) old new p a) at h₂
  have hab₁ := le_abs_self ((family (8*M)).value (prepareData old new) p a-(family (8*M)).value old p a)
  have hab₂ := le_abs_self ((family (8*M)).value new p (transport (8*M) old new p a)-
    (family (8*M)).value (prepareData old new) p (transport (8*M) old new p a))
  nlinarith

end KServer.SideFamilies

end
end
end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_RankProportions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
namespace KServer.RankTracking
variable {Ω : Type*} [Fintype Ω]

lemma held_adapted (test : ℝ → ℝ → Prop) [DecidableRel test] {w : Ω → ℝ}
    (R : FilteredRanks w) : ∀ t, Adapted (R.history t) (held test R.p t) := by
  intro t
  induction t with
  | zero => exact R.adapted 0
  | succ t ih =>
    intro ω ω' hh
    have hprev := ih ω ω' (R.refines t ω ω' hh)
    have hnow := R.adapted (t+1) ω ω' hh
    simp only [held,hnow,hprev]

lemma potential_affine (p r : ℝ) : potential p r=(1-2*r)*p+r^2 := by unfold potential; ring
lemma potential_bounds {p r : ℝ} (hp : p ∈ Set.Icc 0 1) (hr : r ∈ Set.Icc 0 1) :
    potential p r ∈ Set.Icc 0 1 := by
  constructor
  · exact add_nonneg (mul_nonneg hp.1 (sub_nonneg.mpr hp.2)) (sq_nonneg _)
  · rw [potential_affine]
    have hpr := mul_nonneg hp.1 (mul_nonneg hr.1 (sub_nonneg.mpr hr.2))
    have hqr := mul_nonneg (sub_nonneg.mpr hp.2) (mul_nonneg hr.1 (sub_nonneg.mpr hr.2))
    have ha := mul_nonneg (sub_nonneg.mpr hp.2) (sub_nonneg.mpr hr.2)
    have hb := mul_nonneg hp.1 hr.1
    nlinarith
lemma slope_abs {r : ℝ} (hr : r ∈ Set.Icc 0 1) : |1-2*r| ≤1 := by
  rw [abs_le]; constructor <;> linarith [hr.1,hr.2]

omit [Fintype Ω] in
lemma credit_step (test : ℝ → ℝ → Prop) [DecidableRel test] (p : ℕ → Ω → ℝ)
    (before : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    credit test p t ω = potential (p t ω) (held test p t ω) -
      potential (p (t+1) ω) (held test p (t+1) ω) +
      (1-2*held test p t ω)*(before (t+1) ω-p t ω) +
      (1-2*held test p t ω)*(p (t+1) ω-before (t+1) ω) := by
  simp only [credit,held]
  split_ifs <;> simp only [potential] <;> ring

lemma expected_credit_step (test : ℝ → ℝ → Prop) [DecidableRel test]
    {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (R : FilteredRanks w) (t : ℕ) :
    avg w (credit test R.p t) ≤
      avg w (fun ω => potential (R.p t ω) (held test R.p t ω)) -
      avg w (fun ω => potential (R.p (t+1) ω) (held test R.p (t+1) ω)) +
      avg w (fun ω => |R.p (t+1) ω-R.before (t+1) ω|) := by
  have hf : Adapted (R.history t) (fun ω => 1-2*held test R.p t ω) := by
    intro ω ω' hh; dsimp only; rw [held_adapted test R t ω ω' hh]
  calc _ = avg w (fun ω => potential (R.p t ω) (held test R.p t ω) -
      potential (R.p (t+1) ω) (held test R.p (t+1) ω) +
      (1-2*held test R.p t ω)*(R.before (t+1) ω-R.p t ω) +
      (1-2*held test R.p t ω)*(R.p (t+1) ω-R.before (t+1) ω)) := by
        congr 1; funext ω; exact credit_step _ _ _ _ _
       _ = _ + avg w (fun ω => (1-2*held test R.p t ω)*(R.p (t+1) ω-R.before (t+1) ω)) := by
        rw [avg_add,avg_add,avg_sub,filtering_affine R t _ hf,add_zero]
       _ ≤ _ := by
        apply add_le_add_right
        apply avg_mono hw
        intro ω
        exact (le_abs_self _).trans (by
          rw [abs_mul]
          exact (mul_le_mul_of_nonneg_right (slope_abs (held_range test R.range t ω)) (abs_nonneg _)).trans_eq (one_mul _))

/-- Signed filtering is retained at every step, before the reset decision. -/
theorem reset_credit_bound (test : ℝ → ℝ → Prop) [DecidableRel test]
    {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω=1) (R : FilteredRanks w) (N : ℕ) :
    (∑ t ∈ Finset.range N, avg w (credit test R.p t)) ≤
      (∑ t ∈ Finset.range N, avg w (fun ω => |R.p (t+1) ω-R.before (t+1) ω|))+1 := by
  let V : ℕ → ℝ := fun t => avg w (fun ω => potential (R.p t ω) (held test R.p t ω))
  have hV t : 0 ≤ V t ∧ V t ≤1 := by
    constructor
    · have hh := avg_mono hw (fun ω => (potential_bounds (R.range t ω) (held_range test R.range t ω)).1)
      simpa only [avg_const w hw1 0] using hh
    · have hh := avg_mono hw (fun ω => (potential_bounds (R.range t ω) (held_range test R.range t ω)).2)
      simpa only [avg_const w hw1 1] using hh
  have hs : (∑ t ∈ Finset.range N, avg w (credit test R.p t)) ≤
      V 0-V N+(∑ t ∈ Finset.range N, avg w (fun ω => |R.p (t+1) ω-R.before (t+1) ω|)) := by
    calc _ ≤ ∑ t ∈ Finset.range N, (V t-V (t+1)+avg w (fun ω => |R.p (t+1) ω-R.before (t+1) ω|)) :=
          sum_le_sum fun t _ => expected_credit_step test hw R t
         _ = _ := by rw [sum_add_distrib,Finset.sum_range_sub']
  linarith [(hV 0).2,(hV N).1]


/-- Source's scalar factor-loss constant, including zero endpoints. -/
lemma sqrt_factor_gap_one {a b ξ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hξ : 0 < ξ) (hξh : ξ < 1/2) (hfail : (1+ξ)*b ≤ a) :
    (ξ/5)*(a-b) ≤ (Real.sqrt a-Real.sqrt b)^2 := by
  let A := Real.sqrt a
  let B := Real.sqrt b
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hAs : A^2=a := Real.sq_sqrt ha
  have hBs : B^2=b := Real.sq_sqrt hb
  have hba : b ≤ a := by nlinarith [mul_nonneg hξ.le hb]
  have hAB : B ≤ A := Real.sqrt_le_sqrt hba
  have hlin : ξ*(A+B) ≤ 5*(A-B) := by
    by_cases hz : A+B=0
    · rw [hz]; linarith
    have hsum : 0 < A+B := lt_of_le_of_ne (add_nonneg hA hB) (Ne.symm hz)
    by_contra hbad
    have hd : A-B < (ξ/5)*(A+B) := by linarith
    have hprod : ξ*(A+B) ≤ (1/2)*(A+B) := mul_le_mul_of_nonneg_right hξh.le hsum.le
    have hbS : (9/20)*(A+B) ≤ B := by linarith
    have hbSq : (81/400)*(A+B)^2 ≤ B^2 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ B-(9/20)*(A+B))
        (by positivity : 0 ≤ B+(9/20)*(A+B))]
    have hmul := mul_le_mul_of_nonneg_left hbSq hξ.le
    have hmul' := mul_lt_mul_of_pos_right hd hsum
    have hpos := mul_pos hξ (sq_pos_of_pos hsum)
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hlin (sub_nonneg.mpr hAB)
  change (ξ/5)*(a-b) ≤ (A-B)^2
  nlinarith

lemma sqrt_factor_gap {a b ξ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hξ : 0 < ξ) (hξh : ξ < 1/2)
    (hfail : (1+ξ)*a < b ∨ (1+ξ)*b < a) :
    (ξ/5)*|a-b| ≤ (Real.sqrt a-Real.sqrt b)^2 := by
  rcases hfail with hab | hba
  · have hle : a ≤ b := by nlinarith [mul_nonneg hξ.le ha]
    rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    have hh := sqrt_factor_gap_one hb ha hξ hξh hab.le
    nlinarith
  · have hle : b ≤ a := by nlinarith [mul_nonneg hξ.le hb]
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    exact sqrt_factor_gap_one ha hb hξ hξh hba.le

omit [Fintype Ω] in
lemma factor_movement_credit (f : ℝ → ℝ) {ξ K : ℝ} (hξ : 0 < ξ) (hξh : ξ < 1/2)
    (hK : 0 ≤ K) (hf : ∀ p ∈ Set.Icc (0:ℝ) 1, 0 ≤ f p)
    (hlip : ∀ p ∈ Set.Icc (0:ℝ) 1, ∀ r ∈ Set.Icc (0:ℝ) 1,
      |Real.sqrt (f p)-Real.sqrt (f r)| ≤ K*|p-r|)
    {p : ℕ → Ω → ℝ} (hp : ∀ t ω, p t ω ∈ Set.Icc 0 1) (t : ℕ) (ω : Ω) :
    |f (held (factorTest f ξ) p (t+1) ω)-f (held (factorTest f ξ) p t ω)| ≤
      (5*K^2/ξ)*credit (factorTest f ξ) p t ω := by
  have hr := held_range (factorTest f ξ) hp t ω
  by_cases ht : factorTest f ξ (p (t+1) ω) (held (factorTest f ξ) p t ω)
  · simp only [held,ite_eq_left ht,credit]
    have hg := sqrt_factor_gap (hf (p (t+1) ω) (hp (t+1) ω)) (hf _ hr) hξ hξh ht
    have hl := hlip (p (t+1) ω) (hp (t+1) ω) _ hr
    have hs : (Real.sqrt (f (p (t+1) ω))-Real.sqrt (f (held (factorTest f ξ) p t ω)))^2 ≤
        K^2*(p (t+1) ω-held (factorTest f ξ) p t ω)^2 := by
      have hh := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hK (abs_nonneg _))).mpr hl
      simpa only [sq_abs,mul_pow] using hh
    have hmove : ξ*|f (p (t+1) ω)-f (held (factorTest f ξ) p t ω)| ≤
        5*K^2*(p (t+1) ω-held (factorTest f ξ) p t ω)^2 := by nlinarith [hg.trans hs]
    calc _ = (ξ*|f (p (t+1) ω)-f (held (factorTest f ξ) p t ω)|)/ξ := by field_simp
         _ ≤ (5*K^2*(p (t+1) ω-held (factorTest f ξ) p t ω)^2)/ξ :=
          div_le_div_of_nonneg_right hmove hξ.le
         _ = _ := by ring
  · simp [held,ht,credit]

/-- The absolute tracker used for all core flags. Its cost is the actual
number of reference refreshes, not the variation of the raw posteriors. -/
theorem absolute_rank_tracking {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (hw1 : ∑ ω, w ω=1) (R : FilteredRanks w) {δ : ℝ} (hδ : 0 < δ) :
    (∀ t ω, |R.p t ω-held (absoluteTest δ) R.p t ω| ≤ δ) ∧
    ∀ N, (∑ t ∈ Finset.range N, avg w (resetIndicator (absoluteTest δ) R.p t)) ≤
      (δ^2)⁻¹*((∑ t ∈ Finset.range N, avg w (fun ω => |R.p (t+1) ω-R.before (t+1) ω|))+1) := by
  constructor
  · intro t ω
    cases t with
    | zero => simp [held,hδ.le]
    | succ t =>
      simp only [held]
      split_ifs with ht
      · simp [hδ.le]
      · exact le_of_not_gt ht
  · intro N
    have hstep (t : ℕ) (ω : Ω) : resetIndicator (absoluteTest δ) R.p t ω ≤
        (δ^2)⁻¹*credit (absoluteTest δ) R.p t ω := by
      simp only [resetIndicator,credit]
      split_ifs with ht
      · have hsq : δ^2 ≤ (R.p (t+1) ω-held (absoluteTest δ) R.p t ω)^2 := by
          have habs : δ ≤ |R.p (t+1) ω-held (absoluteTest δ) R.p t ω| := le_of_lt ht
          simpa only [sq_abs] using (sq_le_sq₀ hδ.le (abs_nonneg _)).mpr habs
        rw [le_inv_mul_iff₀ (sq_pos_of_pos hδ),mul_one]
        exact hsq
      · simp
    calc _ ≤ ∑ t ∈ Finset.range N, avg w (fun ω => (δ^2)⁻¹*credit (absoluteTest δ) R.p t ω) :=
          sum_le_sum fun t _ => avg_mono hw (hstep t)
         _ = (δ^2)⁻¹*(∑ t ∈ Finset.range N, avg w (credit (absoluteTest δ) R.p t)) := by
          simp_rw [avg_mul]; rw [mul_sum]
         _ ≤ _ := mul_le_mul_of_nonneg_left (reset_credit_bound (absoluteTest δ) hw hw1 R N) (by positivity)

omit [Fintype Ω] in
/-- Causal hold-or-reset rules never increase total scalar input variation.
The deviation from the held reference pays for any waiting interval. -/
lemma held_variation_step (test : ℝ → ℝ → Prop) [DecidableRel test]
    (p : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    |held test p (t+1) ω-held test p t ω|+|p (t+1) ω-held test p (t+1) ω| ≤
      |p (t+1) ω-p t ω|+|p t ω-held test p t ω| := by
  have hh := abs_sub_le (p (t+1) ω) (p t ω) (held test p t ω)
  simp only [held]
  split_ifs <;> simpa using hh

omit [Fintype Ω] in
theorem held_variation (test : ℝ → ℝ → Prop) [DecidableRel test]
    (p : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) :
    (∑ t ∈ Finset.range N, |held test p (t+1) ω-held test p t ω|) ≤
      ∑ t ∈ Finset.range N, |p (t+1) ω-p t ω| := by
  have hstrong : (∑ t ∈ Finset.range N, |held test p (t+1) ω-held test p t ω|)+
      |p N ω-held test p N ω| ≤ ∑ t ∈ Finset.range N, |p (t+1) ω-p t ω| := by
    induction N with
    | zero => simp [held]
    | succ N ih =>
      simp only [sum_range_succ]
      linarith [held_variation_step test p N ω]
  linarith [abs_nonneg (p N ω-held test p N ω)]

lemma factor_change_charge {a b δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hδ : 0 < δ)
    (ht : (1+δ)*a < b ∨ (1+δ)*b < a) : a+b ≤ (1+2/δ)*|a-b| := by
  rcases ht with hab | hba
  · have hab' : a ≤ b := by nlinarith [mul_nonneg hδ.le ha]
    rw [abs_of_nonpos (sub_nonpos.mpr hab')]
    calc a+b = (δ*(a+b))/δ := by field_simp
         _ ≤ ((δ+2)*(b-a))/δ := div_le_div_of_nonneg_right (by nlinarith) hδ.le
         _ = (1+2/δ)*-(a-b) := by field_simp; ring
  · have hba' : b ≤ a := by nlinarith [mul_nonneg hδ.le hb]
    rw [abs_of_nonneg (sub_nonneg.mpr hba')]
    calc a+b = (δ*(a+b))/δ := by field_simp
         _ ≤ ((δ+2)*(a-b))/δ := div_le_div_of_nonneg_right (by nlinarith) hδ.le
         _ = (1+2/δ)*(a-b) := by field_simp

end KServer.RankTracking
namespace KServer.CoreFlags
open KServer.RankTracking
variable {Ω : Type} [Fintype Ω] {w : Ω → ℝ}

lemma change_le_reset (R : FilteredRanks w) (t : ℕ) (ω : Ω) :
    change R t ω ≤ resetIndicator (absoluteTest tolerance) R.p t ω := by
  by_cases ht : absoluteTest tolerance (R.p (t+1) ω) (held (absoluteTest tolerance) R.p t ω)
  · simp only [resetIndicator,ite_eq_left ht,change]
    split_ifs <;> norm_num
  · have he : flag R (t+1) ω = flag R t ω := by simp [flag,held,ht]
    simp [change,he,resetIndicator,ht]

/-- The exact number of changed flags is charged to the fixed absolute trackers.
No raw posterior total variation is charged. -/
theorem core_change_budget {J : Type} [Fintype J]
    (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω=1) (R : J → FilteredRanks w) (N : ℕ) :
    (∑ t ∈ range N, avg w (fun ω => ∑ j, change (R j) t ω)) ≤
      (tolerance^2)⁻¹ * ((∑ t ∈ range N, avg w
        (fun ω => ∑ j, |(R j).p (t+1) ω-(R j).before (t+1) ω|)) + Fintype.card J) := by
  calc _ ≤ ∑ t ∈ range N, avg w (fun ω => ∑ j, resetIndicator (absoluteTest tolerance) (R j).p t ω) := by
        apply sum_le_sum
        intro t _
        apply avg_mono hw
        intro ω
        apply sum_le_sum
        intro j _
        exact change_le_reset (R j) t ω
    _ = ∑ j, ∑ t ∈ range N, avg w (resetIndicator (absoluteTest tolerance) (R j).p t) := by
      simp_rw [avg_sum]; rw [sum_comm]
    _ ≤ ∑ j, (tolerance^2)⁻¹ * ((∑ t ∈ range N, avg w
        (fun ω => |(R j).p (t+1) ω-(R j).before (t+1) ω|))+1) := by
      exact sum_le_sum fun j _ => (absolute_rank_tracking hw hw1 (R j) tolerance_pos).2 N
    _ = _ := by
      rw [← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul, mul_one]
      congr 2
      simp_rw [avg_sum]
      exact sum_comm

lemma flag_adapted (R : FilteredRanks w) (t : ℕ) {ω z : Ω}
    (he : R.history t ω = R.history t z) : flag R t ω=flag R t z := by
  unfold flag
  rw [held_adapted (absoluteTest tolerance) R t ω z he]

end KServer.CoreFlags
end


/- Rank functions for dominated allocation, as in §03, equation explicit-rank. -/


noncomputable section
open Set Filter
namespace KServer.RankFunctions

lemma sqrt_slope_bound {z p : ℝ} (hz : z ∈ Set.Icc 0 (1 / 100 : ℝ))
    (hp0 : 0 ≤ p) (hp : p < sstar) :
    ‖slope z p / (2 * Real.sqrt (rank z p))‖ ≤ 4 := by
  have hr := rank_pos hz hp
  have hs := Real.sqrt_pos.mpr hr
  have hsq := Real.sq_sqrt hr.le
  have hsign : slope z p ≤ 0 := by
    have hh := slope_monotone hz hp.le
    have hps : ¬ sstar ≤ pstar := by norm_num [sstar, pstar]
    simpa [slope, hps] using hh
  rw [Real.norm_eq_abs, abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg hsign (by positivity))]
  rw [← neg_div, div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt (rank z p))]
  by_cases h : p ≤ pstar
  · have hrsmall : 4 / 5 ≤ rank z p := by
      rw [rank, ite_eq_left h]
      have ht := mul_le_mul_of_nonneg_left h (by linarith [hz.1] : 0 ≤ 3 + z)
      norm_num [pstar] at ht
      nlinarith [hz.2]
    have hslo : 1 / 2 ≤ Real.sqrt (rank z p) := by nlinarith
    simp only [slope, ite_eq_left h]
    linarith [hz.2]
  · have hx : 0 < sstar - p := sub_pos.mpr hp
    have hx1 : sstar - p ≤ 1 := by norm_num [sstar]; linarith
    have hA : 2 ≤ A z := (coefficients hz).1
    have hA' : A z ≤ 3 := by dsimp [A]; linarith [hz.1]
    have hB : 0 ≤ B z := (coefficients hz).2
    have hB' : B z ≤ 1 / 10 := by dsimp [B]; linarith [hz.2]
    have hrank : rank z p = (sstar - p)^2 * (A z + B z * (sstar - p)) := by
      rw [rank, ite_eq_right h, ite_eq_left hp.le]
      dsimp [middle]
      ring
    have hBx := mul_le_mul_of_nonneg_left hx1 hB
    have hBx0 := mul_nonneg hB hx.le
    have hslo : sstar - p ≤ Real.sqrt (rank z p) := by
      have hh := mul_le_mul_of_nonneg_left (by linarith : 1 ≤ A z + B z * (sstar - p)) (sq_nonneg (sstar - p))
      rw [← hrank] at hh
      nlinarith
    simp only [slope, ite_eq_right h, ite_eq_left hp.le]
    have hh := mul_le_mul_of_nonneg_left (by linarith : 2 * A z + 3 * (B z * (sstar - p)) ≤ 8) hx.le
    nlinarith

lemma sqrt_right_derivative {z p : ℝ} (hz : z ∈ Set.Icc 0 (1 / 100 : ℝ)) :
    HasDerivWithinAt (fun p => Real.sqrt (rank z p))
      (if p < sstar then slope z p / (2 * Real.sqrt (rank z p)) else 0) (Ici p) p := by
  by_cases hp : p < sstar
  · rw [ite_eq_left hp]
    exact ((rank_derivative z p).sqrt (ne_of_gt (rank_pos hz hp))).hasDerivWithinAt
  · rw [ite_eq_right hp]
    apply (hasDerivWithinAt_const p (Ici p) (0 : ℝ)).congr
    · intro x hx
      rw [rank_cutoff z ((le_of_not_gt hp).trans hx), Real.sqrt_zero]
    · rw [rank_cutoff z (le_of_not_gt hp), Real.sqrt_zero]

lemma sqrt_rank_lipschitz {z : ℝ} (hz : z ∈ Set.Icc 0 (1 / 100 : ℝ)) :
    LipschitzOnWith 4 (fun p => Real.sqrt (rank z p)) (Ici 0) := by
  have hc : Continuous (fun p => Real.sqrt (rank z p)) :=
    Real.continuous_sqrt.comp (continuous_iff_continuousAt.mpr fun p => (rank_derivative z p).continuousAt)
  have hbound (p : ℝ) (hp : 0 ≤ p) :
      ‖if p < sstar then slope z p / (2 * Real.sqrt (rank z p)) else 0‖ ≤ 4 := by
    split_ifs with h
    · exact sqrt_slope_bound hz hp h
    · norm_num
  have hsegment (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
      ‖Real.sqrt (rank z b) - Real.sqrt (rank z a)‖ ≤ 4 * (b - a) := by
    exact norm_image_sub_le_of_norm_deriv_right_le_segment hc.continuousOn
      (fun p _ => sqrt_right_derivative hz) (fun p hp => hbound p (ha.trans hp.1)) b ⟨hab, le_rfl⟩
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro x hx y hy
  rcases le_total x y with h | h
  · simp only [Real.norm_eq_abs]
    rw [abs_of_nonpos (sub_nonpos.mpr h)]
    have hh := hsegment x y hx h
    rw [norm_sub_rev] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  · simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h), NNReal.coe_ofNat] using hsegment y x hy h


lemma sqrt_sizeRank (p : ℝ) : Real.sqrt (sizeRank p) = (4 / 3) * max (3 / 4 - p) 0 := by
  rw [sizeRank, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (le_max_right _ _)]
  norm_num
  ring

lemma sqrt_sizeRank_lipschitz : LipschitzWith (4 / 3) (fun p => Real.sqrt (sizeRank p)) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  simp only [sqrt_sizeRank, Real.norm_eq_abs]
  rw [← mul_sub, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 3)]
  have h := abs_max_sub_max_le_abs (3 / 4 - x) (3 / 4 - y) (0 : ℝ)
  have he : |(3 / 4 - x) - (3 / 4 - y)| = |x-y| := by
    rw [show (3 / 4 - x) - (3 / 4 - y) = -(x-y) by ring, abs_neg]
  rw [he] at h
  exact mul_le_mul_of_nonneg_left h (by norm_num)

end KServer.RankFunctions

noncomputable section
open scoped BigOperators
open Finset
namespace KServer.FineCaps
open KServer.RankTracking KServer.RankFunctions KServer.CoreFlags
variable {Ω : Type} [Fintype Ω] {w : Ω → ℝ}

/-- The concrete endpoint tracker, not a separately postulated estimate. -/
lemma estimate_variation_budget (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω=1)
    {ξ z : ℝ} (hξ : 0 < ξ) (hξh : ξ < 1/2) (hz : z ∈ Set.Icc 0 (1/100 : ℝ))
    (R : FilteredRanks w) (N : ℕ) :
    (∑ t ∈ range N, avg w (fun ω => |estimate ξ z R (t+1) ω-estimate ξ z R t ω|)) ≤
      (80/ξ)*((∑ t ∈ range N, avg w (fun ω => |R.p (t+1) ω-R.before (t+1) ω|))+1) := by
  have hlip : ∀ p ∈ Set.Icc (0:ℝ) 1, ∀ r ∈ Set.Icc (0:ℝ) 1,
      |Real.sqrt (rank z p)-Real.sqrt (rank z r)| ≤ (4:ℝ)*|p-r| := by
    intro p hp r hr
    have hh := (lipschitzOnWith_iff_norm_sub_le.mp (sqrt_rank_lipschitz hz)) hp.1 hr.1
    simpa only [Real.norm_eq_abs, NNReal.coe_ofNat] using hh
  have hs t ω := factor_movement_credit (rank z) hξ hξh (show (0:ℝ) ≤ 4 by norm_num)
    (fun p hp => (rank_range hz hp.1).1) hlip R.range t ω
  have hs' t ω : |estimate ξ z R (t+1) ω-estimate ξ z R t ω| ≤
      (80/ξ)*credit (factorTest (rank z) ξ) R.p t ω := by
    simpa only [estimate, show (5:ℝ)*4^2=80 by norm_num] using hs t ω
  calc _ ≤ ∑ t ∈ range N, avg w (fun ω => (80/ξ)*credit (factorTest (rank z) ξ) R.p t ω) :=
        sum_le_sum fun t _ => avg_mono hw (hs' t)
    _ = (80/ξ)*(∑ t ∈ range N, avg w (credit (factorTest (rank z) ξ) R.p t)) := by
        simp_rw [avg_mul]; rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (reset_credit_bound (factorTest (rank z) ξ) hw hw1 R N)
        (by positivity)

lemma interpolated_variation {ξ a : ℝ} (ha : a ∈ Set.Icc 0 1)
    (R : FilteredRanks w) (t : ℕ) (ω : Ω) :
    |interpolated ξ a R (t+1) ω-interpolated ξ a R t ω| ≤
      |estimate ξ 0 R (t+1) ω-estimate ξ 0 R t ω|+
      |estimate ξ (1/100) R (t+1) ω-estimate ξ (1/100) R t ω| := by
  have hA : 0 ≤ 1-a := by linarith [ha.2]
  calc _ = |(1-a)*(estimate ξ 0 R (t+1) ω-estimate ξ 0 R t ω) +
        a*(estimate ξ (1/100) R (t+1) ω-estimate ξ (1/100) R t ω)| := by
          unfold interpolated; congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (by
      rw [abs_mul,abs_mul,abs_of_nonneg hA,abs_of_nonneg ha.1]
      simpa only [one_mul] using add_le_add
        (mul_le_mul_of_nonneg_right (show 1-a ≤ 1 by linarith [ha.1])
          (abs_nonneg (estimate ξ 0 R (t+1) ω-estimate ξ 0 R t ω)))
        (mul_le_mul_of_nonneg_right ha.2
          (abs_nonneg (estimate ξ (1/100) R (t+1) ω-estimate ξ (1/100) R t ω))))

lemma capTerm_range {ξ a κ : ℝ} (ha : a ∈ Set.Icc 0 1) (hκ : κ ∈ Set.Icc 0 2)
    (R : FilteredRanks w) (t : ℕ) (ω : Ω) : capTerm ξ a κ R t ω ∈ Set.Icc 0 2 := by
  have hh := interpolated_range (ξ := ξ) ha R t ω
  dsimp [capTerm]
  split_ifs
  · constructor <;> norm_num
  · exact ⟨mul_nonneg hκ.1 hh.1, (mul_le_mul_of_nonneg_left hh.2 hκ.1).trans (by simpa using hκ.2)⟩

lemma capTerm_variation {ξ a κ : ℝ} (ha : a ∈ Set.Icc 0 1) (hκ : κ ∈ Set.Icc 0 2)
    (R : FilteredRanks w) (t : ℕ) (ω : Ω) :
    |capTerm ξ a κ R (t+1) ω-capTerm ξ a κ R t ω| ≤
      2*(|estimate ξ 0 R (t+1) ω-estimate ξ 0 R t ω|+
        |estimate ξ (1/100) R (t+1) ω-estimate ξ (1/100) R t ω|+change R t ω) := by
  have hv := interpolated_variation (ξ := ξ) ha R t ω
  have hn0 := abs_nonneg (estimate ξ 0 R (t+1) ω-estimate ξ 0 R t ω)
  have hn1 := abs_nonneg (estimate ξ (1/100) R (t+1) ω-estimate ξ (1/100) R t ω)
  by_cases he : flag R (t+1) ω=flag R t ω
  · have hc : change R t ω=0 := by simp [change,he]
    rw [hc,add_zero]
    unfold capTerm
    rw [he]
    split_ifs
    · simp only [sub_self,abs_zero]; positivity
    · rw [←mul_sub,abs_mul,abs_of_nonneg hκ.1]
      exact (mul_le_mul_of_nonneg_left hv hκ.1).trans
        (mul_le_mul_of_nonneg_right hκ.2 (add_nonneg hn0 hn1))
  · have hc : change R t ω=1 := by simp [change,he]
    have h0 := capTerm_range (ξ := ξ) ha hκ R t ω
    have h1 := capTerm_range (ξ := ξ) ha hκ R (t+1) ω
    have hb : |capTerm ξ a κ R (t+1) ω-capTerm ξ a κ R t ω| ≤ 2 := by
      exact abs_le.mpr ⟨by linarith [h0.1,h0.2,h1.1,h1.2],by linarith [h0.1,h0.2,h1.1,h1.2]⟩
    rw [hc]
    linarith

lemma fineVariation_step {ξ : ℝ} (a κ : ℕ → Ω → ℝ) (wholesale : ℕ → Ω → Bool)
    (ha : ∀ t ω, a t ω ∈ Set.Icc 0 1) (hκ : ∀ t ω, κ t ω ∈ Set.Icc 0 2)
    (hhold : ∀ t ω, wholesale t ω=false → a (t+1) ω=a t ω ∧ κ (t+1) ω=κ t ω)
    (R : FilteredRanks w) (t : ℕ) (ω : Ω) :
    fineVariation ξ a κ wholesale R t ω ≤
      2*(|estimate ξ 0 R (t+1) ω-estimate ξ 0 R t ω|+
        |estimate ξ (1/100) R (t+1) ω-estimate ξ (1/100) R t ω|+change R t ω) := by
  cases h : wholesale t ω with
  | true =>
    simp only [fineVariation,h,↓reduceIte]
    have : 0 ≤ change R t ω := by unfold change; split_ifs <;> norm_num
    positivity
  | false =>
    obtain ⟨hA,hK⟩ := hhold t ω h
    simpa only [fineVariation,h,Bool.false_eq_true,↓reduceIte,hA,hK] using
      capTerm_variation (ξ := ξ) (ha t ω) (hκ t ω) R t ω

lemma all_endpoint_budget {J : Type} [Fintype J]
    (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω=1)
    {ξ z : ℝ} (hξ : 0 < ξ) (hξh : ξ < 1/2) (hz : z ∈ Set.Icc 0 (1/100 : ℝ))
    (R : J → FilteredRanks w) (N : ℕ) :
    (∑ t ∈ range N, avg w (fun ω => ∑ j,
      |estimate ξ z (R j) (t+1) ω-estimate ξ z (R j) t ω|)) ≤
      (80/ξ)*((∑ t ∈ range N, avg w
        (fun ω => ∑ j, |(R j).p (t+1) ω-(R j).before (t+1) ω|))+Fintype.card J) := by
  calc _ = ∑ j, ∑ t ∈ range N, avg w
        (fun ω => |estimate ξ z (R j) (t+1) ω-estimate ξ z (R j) t ω|) := by
          simp_rw [avg_sum]; rw [sum_comm]
    _ ≤ ∑ j, (80/ξ)*((∑ t ∈ range N, avg w
        (fun ω => |(R j).p (t+1) ω-(R j).before (t+1) ω|))+1) :=
          sum_le_sum fun j _ => estimate_variation_budget hw hw1 hξ hξh hz (R j) N
    _ = _ := by
      rw [←mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul,mul_one]
      congr 2
      simp_rw [avg_sum]
      exact sum_comm

/-- §03 fine-cap budget. The right side has one uniform initialization term
per rank, not one per coarse epoch. Arbitrary pathwise nonwholesale selection
is valid only after the all-step filtering credits have been accounted for. -/
theorem fine_cap_budget {J : Type} [Fintype J]
    (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω=1)
    {ξ : ℝ} (hξ : 0 < ξ) (hξh : ξ < 1/2)
    (a κ : J → ℕ → Ω → ℝ) (wholesale : J → ℕ → Ω → Bool)
    (ha : ∀ j t ω, a j t ω ∈ Set.Icc 0 1) (hκ : ∀ j t ω, κ j t ω ∈ Set.Icc 0 2)
    (hhold : ∀ j t ω, wholesale j t ω=false →
      a j (t+1) ω=a j t ω ∧ κ j (t+1) ω=κ j t ω)
    (R : J → FilteredRanks w) (N : ℕ) :
    (∑ t ∈ range N, avg w (fun ω => ∑ j, fineVariation ξ (a j) (κ j) (wholesale j) (R j) t ω)) ≤
      2*(160/ξ+(tolerance^2)⁻¹)*((∑ t ∈ range N, avg w
        (fun ω => ∑ j, |(R j).p (t+1) ω-(R j).before (t+1) ω|))+Fintype.card J) := by
  have h0 := all_endpoint_budget hw hw1 hξ hξh
    (by norm_num : (0:ℝ) ∈ Set.Icc 0 (1/100)) R N
  have h1 := all_endpoint_budget hw hw1 hξ hξh
    (by norm_num : (1/100:ℝ) ∈ Set.Icc 0 (1/100)) R N
  have hc := core_change_budget hw hw1 R N
  calc _ ≤ ∑ t ∈ range N, avg w (fun ω => ∑ j,
        2*(|estimate ξ 0 (R j) (t+1) ω-estimate ξ 0 (R j) t ω|+
          |estimate ξ (1/100) (R j) (t+1) ω-estimate ξ (1/100) (R j) t ω|+change (R j) t ω)) := by
        apply sum_le_sum
        intro t _
        apply avg_mono hw
        intro ω
        exact sum_le_sum fun j _ => fineVariation_step (a j) (κ j) (wholesale j)
          (ha j) (hκ j) (hhold j) (R j) t ω
    _ = 2*((∑ t ∈ range N, avg w (fun ω => ∑ j,
          |estimate ξ 0 (R j) (t+1) ω-estimate ξ 0 (R j) t ω|))+
        (∑ t ∈ range N, avg w (fun ω => ∑ j,
          |estimate ξ (1/100) (R j) (t+1) ω-estimate ξ (1/100) (R j) t ω|))+
        (∑ t ∈ range N, avg w (fun ω => ∑ j, change (R j) t ω))) := by
          simp_rw [←mul_sum,sum_add_distrib,avg_mul,avg_add]
          rw [←mul_sum,sum_add_distrib,sum_add_distrib]
    _ ≤ _ := by
      have h := add_le_add (add_le_add h0 h1) hc
      have h' := mul_le_mul_of_nonneg_left h (show (0:ℝ) ≤ 2 by norm_num)
      convert h' using 1
      all_goals try with_reducible_and_instances rfl
      first | rfl | ring

end KServer.FineCaps
end

end

/- Finite-law rank superadditivity and summation by parts. -/


end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Coarse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Finset

namespace KServer.CoarseSchedule
open Finset

lemma factor_ge_seven (δ : ℝ) (hδ : 0 < δ) (hδu : δ ≤ 1/3) : 7 ≤ factor δ := by
  have hh : 6 ≤ 2/δ := (le_div_iff₀ hδ).mpr (by linarith)
  exact by dsimp [factor]; linarith

lemma charge_self (s : State) : charge s s = 0 := by simp [charge]
lemma charge_le {s t : State} (hs : 0 ≤ s.value) (ht : 0 ≤ t.value) :
    charge s t ≤ s.value+t.value := by
  unfold charge
  split_ifs <;> linarith

lemma update_credit {c δ x : ℝ} {s : State} (hc : 0 ≤ c)
    (hδ : 0 < δ) (hδu : δ ≤ 1/3) (hx : 0 ≤ x) (hs : Valid s) :
    charge s (update c δ x s) + potential c δ x (update c δ x s) ≤ potential c δ x s := by
  have hC := factor_ge_seven δ hδ hδu
  have hC0 : 0 ≤ factor δ := by linarith
  have hC1 : 1 ≤ factor δ := by linarith
  have hCs : |x-s.value| ≤ factor δ*|x-s.value| := by nlinarith [abs_nonneg (x-s.value)]
  unfold update
  split_ifs with hon hoff href hon'
  · have hsx : s.value ≤ |x-s.value|+x := by
      have hh := le_abs_self (s.value-x)
      rw [abs_sub_comm s.value x] at hh
      linarith
    have hch := charge_le (s := s) (t := ⟨false,0⟩) hs.1 (by norm_num)
    simp only [potential, Bool.false_eq_true, ite_false, sub_zero, abs_of_nonneg hx]
    simp only [hon, ite_true]
    have hbound : (factor δ+1)*x ≤ 2*(factor δ+1)*c := by
      nlinarith [mul_le_mul_of_nonneg_left hoff (show 0 ≤ factor δ+1 by linarith)]
    linarith
  · have hch := charge_le (s := s) (t := ⟨true,x⟩) hs.1 hx
    have hfac := RankTracking.factor_change_charge hs.1 hx hδ href
    rw [abs_sub_comm] at hfac
    change s.value+x ≤ factor δ*|x-s.value| at hfac
    simp only [potential, sub_self, abs_zero, mul_zero, zero_add, hon, ite_true]
    linarith
  · simp [charge_self]
  · have hfalse : s.active = false := by simpa using hon
    have hz := hs.2 hfalse
    have hch := charge_le (s := s) (t := ⟨true,x⟩) hs.1 hx
    simp only [potential, sub_self, abs_zero, mul_zero, zero_add, hfalse, Bool.false_eq_true, ite_false, ite_true,
      hz, sub_zero, abs_of_nonneg hx]
    have hc1 : 2*(factor δ+1)*c ≤ (factor δ-1)*(5*c) := by nlinarith
    have hc2 : (factor δ-1)*(5*c) ≤ (factor δ-1)*x :=
      mul_le_mul_of_nonneg_left hon' (by linarith)
    simp only [hz] at hch
    linarith
  · simp [charge_self]

lemma potential_nonneg {c δ x : ℝ} {s : State} (hc : 0 ≤ c) (hδ : 0 < δ) :
    0 ≤ potential c δ x s := by
  unfold potential factor
  split_ifs <;> positivity

lemma potential_input {c δ x y : ℝ} (s : State) (hδ : 0 < δ) :
    potential c δ y s ≤ potential c δ x s + factor δ*|y-x| := by
  have h0 : 0 ≤ factor δ := by unfold factor; positivity
  have hh := mul_le_mul_of_nonneg_left (abs_sub_le y x s.value) h0
  simpa only [potential, mul_add] using (show
    factor δ*|y-s.value|+(if s.active then 2*(factor δ+1)*c else 0) ≤
    factor δ*|x-s.value|+(if s.active then 2*(factor δ+1)*c else 0)+factor δ*|y-x| by
      linarith)

/-- Uniform-in-horizon amortization of the literal §03 active-size schedule.
This pays genuine old-plus-new charges, not merely total variation. -/
theorem active_size_budget {c δ : ℝ} {x : ℕ → ℝ} {initial : State}
    (hc : 0 ≤ c) (hδ : 0 < δ) (hδu : δ ≤ 1/3)
    (hx : ∀ t, 0 ≤ x t) (hi : Valid initial) (N : ℕ) :
    (∑ t ∈ range N, charge (run c δ x initial t) (run c δ x initial (t+1))) ≤
      factor δ*(∑ t ∈ range N, |x (t+1)-x t|) + potential c δ (x 0) initial := by
  have hstrong : (∑ t ∈ range N, charge (run c δ x initial t) (run c δ x initial (t+1))) +
      potential c δ (x N) (run c δ x initial N) ≤
      factor δ*(∑ t ∈ range N, |x (t+1)-x t|) + potential c δ (x 0) initial := by
    induction N with
    | zero => simp [run]
    | succ N ih =>
      have hcredit := update_credit hc hδ hδu (hx (N+1)) (run_valid (c := c) (δ := δ) hx hi N)
      have hinput := potential_input (c := c) (δ := δ) (x := x N) (y := x (N+1))
        (run c δ x initial N) hδ
      simp only [sum_range_succ, mul_add, run] at *
      linarith
  linarith [potential_nonneg (x := x N) (s := run c δ x initial N) hc hδ]

end KServer.CoarseSchedule


/-! The actual epoch/wholesale recurrence of §03. The old credit is discarded
on a parent refresh, never spent twice. Empty transitions are forced by the
same variation test. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.EpochSchedule
variable {J K : Type*} [Fintype J]

/-- Each volume-triggered wholesale consumes only its epoch's accumulated
variation. The constant 203 is the literal bound used in the source. -/
lemma update_budget {x y : J → ℝ} {a b : K} {s : State J}
    (hs : Valid x s) :
    wholesale x y a b s+203*(update x y a b s).credit ≤
      203*s.credit+203*variation y x+parentCharge x y a b := by
  classical
  by_cases hk : a≠b
  · have hr : reset x y a b s := Or.inl hk
    simp only [wholesale,update,ite_eq_left hr,parentCharge,ite_eq_left hk]
    linarith [hs.2.1,variation_nonneg y x]
  · by_cases hv : total s.reference/100 < s.credit+variation y x
    · have hr : reset x y a b s := Or.inr hv
      simp only [wholesale,update,ite_eq_left hr,parentCharge,ite_eq_right hk]
      have ht := (valid_total hs).2
      have hd := (abs_le.mp (total_change y x)).2
      have hd' := variation_nonneg y x
      linarith [hs.2.1]
    · have hr : ¬reset x y a b s := not_or.mpr ⟨hk,hv⟩
      simp only [wholesale,update,ite_eq_right hr,parentCharge,ite_eq_right hk]
      ring_nf
      exact le_rfl

/-- Deterministic finite-horizon wholesale budget, with no terminal charge and
no dependence on the horizon in its constants. -/
theorem wholesale_budget (x : ℕ → J → ℝ) (key : ℕ → K) (hx : ∀ t i, 0 ≤ x t i) (n : ℕ) :
    (∑ t ∈ range n, wholesale (x t) (x (t+1)) (key t) (key (t+1)) (run x key t)) ≤
      203*(∑ t ∈ range n, variation (x (t+1)) (x t))+
      ∑ t ∈ range n, parentCharge (x t) (x (t+1)) (key t) (key (t+1)) := by
  have hh : ∀ m, (∑ t ∈ range m, wholesale (x t) (x (t+1)) (key t) (key (t+1)) (run x key t))+
      203*(run x key m).credit ≤
      203*(∑ t ∈ range m, variation (x (t+1)) (x t))+
      ∑ t ∈ range m, parentCharge (x t) (x (t+1)) (key t) (key (t+1)) := by
    intro m
    induction m with
    | zero => simp [run]
    | succ m ih =>
      have hs := update_budget (a := key m) (b := key (m+1)) (y := x (m+1)) (run_valid x key hx m)
      change wholesale _ _ _ _ _+203*(run x key (m+1)).credit ≤ _ at hs
      simp only [sum_range_succ]
      linarith
  have hn := (run_valid x key hx n).2.1
  linarith [hh n]

end KServer.EpochSchedule

namespace KServer.CoarseProcess
open RankTracking RankFunctions CoarseSchedule
variable {Ω J R : Type} [Fintype Ω] [Fintype J] [Fintype R] {w : Ω → ℝ}
attribute [local instance] Classical.propDecidable Classical.decEq

lemma estimate_bound (δ : ℝ) (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) :
    estimate δ P t ω ≤ Fintype.card R := by
  calc _ ≤ ∑ _ : R, (1:ℝ) := by
        apply sum_le_sum
        intro a _
        have hr := held_range (factorTest sizeRank δ) (P a).range t ω
        exact (sizeRank_le_complement hr).trans (by linarith [hr.1])
       _ = _ := by simp

lemma term_variation {δ : ℝ} (hδ : 0 < δ) (hδu : δ < 1/2)
    (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω=1) (P : FilteredRanks w) (N : ℕ) :
    (∑ t ∈ range N, avg w (fun ω =>
        |sizeRank (held (factorTest sizeRank δ) P.p (t+1) ω)-
          sizeRank (held (factorTest sizeRank δ) P.p t ω)|)) ≤
      (5*(4/3:ℝ)^2/δ)*((∑ t ∈ range N, avg w (fun ω => |P.p (t+1) ω-P.before (t+1) ω|))+1) := by
  have hlip (p q : ℝ) : |Real.sqrt (sizeRank p)-Real.sqrt (sizeRank q)| ≤ (4/3:ℝ)*|p-q| := by
    simpa only [Real.dist_eq,NNReal.coe_div,NNReal.coe_ofNat] using
      sqrt_sizeRank_lipschitz.dist_le_mul p q
  calc _ ≤ ∑ t ∈ range N, avg w (fun ω => (5*(4/3:ℝ)^2/δ)*credit (factorTest sizeRank δ) P.p t ω) :=
        sum_le_sum fun t _ => avg_mono hw (factor_movement_credit sizeRank hδ hδu (by norm_num)
          (fun _ _ => sizeRank_nonneg _) (fun p _ q _ => hlip p q) P.range t)
       _ = (5*(4/3:ℝ)^2/δ)*(∑ t ∈ range N, avg w (credit (factorTest sizeRank δ) P.p t)) := by
        simp_rw [avg_mul]; rw [mul_sum]
       _ ≤ _ := mul_le_mul_of_nonneg_left (reset_credit_bound (factorTest sizeRank δ) hw hw1 P N)
        (by positivity)

lemma estimate_variation {δ : ℝ} (hδ : 0 < δ) (hδu : δ < 1/2)
    (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω=1) (P : R → FilteredRanks w) (N : ℕ) :
    (∑ t ∈ range N, avg w (fun ω => |estimate δ P (t+1) ω-estimate δ P t ω|)) ≤
      (5*(4/3:ℝ)^2/δ)*
        ((∑ a, ∑ t ∈ range N, avg w (fun ω => |(P a).p (t+1) ω-(P a).before (t+1) ω|))+
          Fintype.card R) := by
  calc _ ≤ ∑ t ∈ range N, ∑ a, avg w (fun ω =>
        |sizeRank (held (factorTest sizeRank δ) (P a).p (t+1) ω)-
          sizeRank (held (factorTest sizeRank δ) (P a).p t ω)|) := by
        apply sum_le_sum
        intro t _
        rw [←avg_sum]
        apply avg_mono hw
        intro ω
        simp only [estimate,←sum_sub_distrib]
        exact Finset.abs_sum_le_sum_abs _ _
       _ = ∑ a, ∑ t ∈ range N, avg w (fun ω =>
        |sizeRank (held (factorTest sizeRank δ) (P a).p (t+1) ω)-
          sizeRank (held (factorTest sizeRank δ) (P a).p t ω)|) := by rw [sum_comm]
       _ ≤ ∑ a, (5*(4/3:ℝ)^2/δ)*
          ((∑ t ∈ range N, avg w (fun ω => |(P a).p (t+1) ω-(P a).before (t+1) ω|))+1) := by
        apply sum_le_sum
        intro a _
        exact term_variation hδ hδu hw hw1 (P a) N
       _ = _ := by simp only [mul_add,sum_add_distrib,←mul_sum,sum_const,card_univ,nsmul_eq_mul]; ring


lemma charge_nonneg {s t : CoarseSchedule.State} (hs : CoarseSchedule.Valid s)
    (ht : CoarseSchedule.Valid t) : 0 ≤ CoarseSchedule.charge s t := by
  unfold CoarseSchedule.charge
  split_ifs
  · rfl
  · exact add_nonneg hs.1 ht.1

lemma initial_potential {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hδu : δ ≤ 1/3)
    (P : R → FilteredRanks w) (ω : Ω) :
    potential c δ (estimate δ P 0 ω) (active c δ P ω 0) ≤ factor δ*Fintype.card R := by
  have hi : CoarseSchedule.Valid ⟨false,0⟩ := by simp [CoarseSchedule.Valid]
  have hx := estimate_nonneg δ P 0 ω
  have hh := update_credit hc.le hδ hδu hx hi
  have hn := charge_nonneg hi (update_valid hi hx (c:=c) (δ:=δ))
  have hb := mul_le_mul_of_nonneg_left (estimate_bound δ P 0 ω)
    (show 0 ≤ factor δ by unfold factor; positivity)
  have hp0 : CoarseSchedule.potential c δ (estimate δ P 0 ω) ⟨false,0⟩ = factor δ*estimate δ P 0 ω := by
    simp [CoarseSchedule.potential,abs_of_nonneg hx]
  change 0 ≤ charge ⟨false,0⟩ (active c δ P ω 0) at hn
  rw [hp0] at hh
  change CoarseSchedule.charge ⟨false,0⟩ (active c δ P ω 0)+
    potential c δ (estimate δ P 0 ω) (active c δ P ω 0) ≤ factor δ*estimate δ P 0 ω at hh
  linarith

lemma avg_range (w : Ω → ℝ) (f : ℕ → Ω → ℝ) (N : ℕ) :
    (∑ t ∈ range N, avg w (f t))=avg w (fun ω => ∑ t ∈ range N,f t ω) := by
  simp only [avg,mul_sum]
  exact sum_comm

/-- Actual old-plus-new active refresh budget, with a fixed-star endpoint. -/
theorem active_budget {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hδu : δ ≤ 1/1000)
    (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω=1) (P : R → FilteredRanks w) (N : ℕ) :
    (∑ t ∈ range N, avg w (fun ω =>
        charge (active c δ P ω t) (active c δ P ω (t+1)))) ≤
      (factor δ*(5*(4/3:ℝ)^2/δ)) *
        (∑ a, ∑ t ∈ range N, avg w (fun ω => |(P a).p (t+1) ω-(P a).before (t+1) ω|))+
      (factor δ*(5*(4/3:ℝ)^2/δ+1))*Fintype.card R := by
  have hf : 0 ≤ factor δ := by unfold factor; positivity
  have hs (ω : Ω) := active_size_budget hc.le hδ (show δ ≤ 1/3 by linarith)
    (fun t => estimate_nonneg δ P t ω)
    (update_valid (show CoarseSchedule.Valid ⟨false,0⟩ by simp [CoarseSchedule.Valid])
      (estimate_nonneg δ P 0 ω) (c:=c) (δ:=δ)) N
  have hb (ω : Ω) := initial_potential hc hδ (show δ ≤ 1/3 by linarith) P ω
  have hs' (ω : Ω) : (∑ t ∈ range N, charge (active c δ P ω t) (active c δ P ω (t+1))) ≤
      factor δ*(∑ t ∈ range N, |estimate δ P (t+1) ω-estimate δ P t ω|)+
      potential c δ (estimate δ P 0 ω) (active c δ P ω 0) := hs ω
  have hh := avg_mono hw (fun ω => hs' ω |>.trans (add_le_add_right (hb ω) _))
  change avg w (fun ω => ∑ t ∈ range N, charge (active c δ P ω t) (active c δ P ω (t+1))) ≤
    avg w (fun ω => factor δ * (∑ t ∈ range N, |estimate δ P (t+1) ω-estimate δ P t ω|)+
      factor δ*Fintype.card R) at hh
  rw [avg_add,avg_mul,avg_const w hw1,←avg_range,←avg_range] at hh
  have hv := mul_le_mul_of_nonneg_left (estimate_variation hδ (by linarith) hw hw1 P N) hf
  exact hh.trans (by nlinarith)

lemma estimate_adapted (δ : ℝ) (P : R → FilteredRanks w) (H : ℕ → Ω → ℕ)
    (hH : ∀ a t ω, (P a).history t ω=H t ω) (t : ℕ) :
    Adapted (H t) (estimate δ P t) := by
  intro ω z he
  unfold estimate
  apply sum_congr rfl
  intro a _
  rw [held_adapted (factorTest sizeRank δ) (P a) t ω z (by simpa only [hH] using he)]

lemma active_adapted (c δ : ℝ) (P : R → FilteredRanks w) (H : ℕ → Ω → ℕ)
    (hH : ∀ a t ω, (P a).history t ω=H t ω)
    (href : ∀ t ω z, H (t+1) ω=H (t+1) z → H t ω=H t z) (t : ℕ) :
    ∀ ω z, H t ω=H t z → active c δ P ω t=active c δ P z t := by
  induction t with
  | zero =>
    intro ω z he
    simp only [active,run]
    rw [estimate_adapted δ P H hH 0 ω z he]
  | succ t ih =>
    intro ω z he
    change update c δ (estimate δ P (t+1) ω) (active c δ P ω t)=
      update c δ (estimate δ P (t+1) z) (active c δ P z t)
    rw [estimate_adapted δ P H hH (t+1) ω z he,ih ω z (href t ω z he)]

omit [Fintype Ω] in
lemma relative_charge_bound {δ : ℝ} (hδ : 0 < δ) (x : ℕ → Ω → ℝ)
    (hx : ∀ t ω, 0 ≤ x t ω) (t : ℕ) (ω : Ω) :
    relativeCharge δ x t ω ≤ factor δ*|relative δ x (t+1) ω-relative δ x t ω| := by
  by_cases ht : factorTest id δ (x (t+1) ω) (relative δ x t ω)
  · have he : relative δ x (t+1) ω=x (t+1) ω := by
      change (if factorTest id δ (x (t+1) ω) (relative δ x t ω) then x (t+1) ω else relative δ x t ω)=_
      exact ite_eq_left ht
    have hh := factor_change_charge (hx (t+1) ω) (relative_nonneg x hx t ω) hδ ht
    rw [relativeCharge,he]
    split_ifs
    · exact mul_nonneg (by unfold factor; positivity) (abs_nonneg _)
    · unfold factor; linarith
  · have he : relative δ x (t+1) ω=relative δ x t ω := by
      change (if factorTest id δ (x (t+1) ω) (relative δ x t ω) then x (t+1) ω else relative δ x t ω)=_
      exact ite_eq_right ht
    simp [relativeCharge,he]

omit [Fintype Ω] in
lemma relative_budget {δ : ℝ} (hδ : 0 < δ) (x : ℕ → Ω → ℝ)
    (hx : ∀ t ω, 0 ≤ x t ω) (N : ℕ) (ω : Ω) :
    (∑ t ∈ range N, relativeCharge δ x t ω) ≤
      factor δ*(∑ t ∈ range N, |x (t+1) ω-x t ω|) := by
  calc _ ≤ ∑ t ∈ range N, factor δ*|relative δ x (t+1) ω-relative δ x t ω| :=
        sum_le_sum fun t _ => relative_charge_bound hδ x hx t ω
       _ = factor δ*(∑ t ∈ range N, |relative δ x (t+1) ω-relative δ x t ω|) := (mul_sum _ _ _).symm
       _ ≤ _ := mul_le_mul_of_nonneg_left (held_variation (factorTest id δ) x N ω)
        (by unfold factor; positivity)

end KServer.CoarseProcess

end
end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.CoarseEpoch
open RankTracking CoarseSchedule CoarseProcess
variable {Ω R J : Type} [Fintype Ω] [Fintype R] [Fintype J]
variable {w : Ω → ℝ}

lemma clipped_variation (c δ : ℝ) (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) :
    |clipped c δ P (t+1) ω-clipped c δ P t ω| ≤ |estimate δ P (t+1) ω-estimate δ P t ω| := by
  unfold clipped
  simpa only [max_comm c] using abs_max_sub_max_le_abs (estimate δ P (t+1) ω) (estimate δ P t ω) c

lemma parent_budget {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ) (hδu : δ ≤ 1/3)
    (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω,w ω=1) (P : R → FilteredRanks w) (N : ℕ) :
    (∑ t ∈ range N, avg w (relativeCharge δ (clipped c δ P) t)) ≤
      (factor δ*(5*(4/3:ℝ)^2/δ))*
        ((∑ a, ∑ t ∈ range N, avg w (fun ω => |(P a).p (t+1) ω-(P a).before (t+1) ω|))+Fintype.card R) := by
  have hf : 0 ≤ factor δ := by unfold factor; positivity
  rw [avg_range]
  calc _ ≤ avg w (fun ω => factor δ*(∑ t ∈ range N, |estimate δ P (t+1) ω-estimate δ P t ω|)) := by
        apply avg_mono hw
        intro ω
        exact (relative_budget hδ _ (clipped_nonneg hc δ P) N ω).trans
          (mul_le_mul_of_nonneg_left (sum_le_sum fun t _ => clipped_variation c δ P t ω) hf)
       _ = factor δ*(∑ t ∈ range N, avg w (fun ω => |estimate δ P (t+1) ω-estimate δ P t ω|)) := by
        rw [avg_mul,←avg_range]
       _ ≤ _ := by
        calc _ ≤ factor δ*((5*(4/3:ℝ)^2/δ)*
            ((∑ a, ∑ t ∈ range N, avg w (fun ω => |(P a).p (t+1) ω-(P a).before (t+1) ω|))+Fintype.card R)) :=
            mul_le_mul_of_nonneg_left (CoarseProcess.estimate_variation hδ (by linarith) hw hw1 P N) hf
             _ = _ := by ring

lemma total_parent {c δ ε : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hδu : δ ≤ 1/1000)
    (hε : 0 < ε) (hεu : ε ≤ 1/1000) (P : J → R → FilteredRanks w) (V : R → FilteredRanks w)
    (htree : ∀ t ω, (∑ i,size (P i) t ω) ≤ size V t ω) (ω : Ω) (t : ℕ) :
    EpochSchedule.total (vector c δ P ω t) ≤ 2*parent c ε V t ω := by
  have h := parent_accuracy hc.le hε V t ω
  have hp := parent_nonneg hc.le ε V t ω
  have hsq : (11/10:ℝ)*(1+ε)^2 ≤ 2 := by nlinarith [sq_nonneg (ε-1/1000)]
  calc _ ≤ ∑ i, (11/10:ℝ)*size (P i) t ω := sum_le_sum fun i _ => value_bound hc hδ hδu (P i) ω t
       _ = (11/10:ℝ)*(∑ i,size (P i) t ω) := (mul_sum _ _ _).symm
       _ ≤ (11/10:ℝ)*size V t ω := mul_le_mul_of_nonneg_left (htree t ω) (by norm_num)
       _ ≤ (11/10:ℝ)*((1+ε)^2*parent c ε V t ω) :=
          mul_le_mul_of_nonneg_left ((le_max_right _ _).trans h.1) (by norm_num)
       _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hsq hp]

lemma value_variation {s t : CoarseSchedule.State} (hs : CoarseSchedule.Valid s) (ht : CoarseSchedule.Valid t) :
    |s.value-t.value| ≤ charge s t := by
  unfold charge
  split_ifs with he
  · simp [he]
  · exact abs_sub_le_iff.mpr ⟨by linarith [ht.1],by linarith [hs.1]⟩

lemma vector_variation (c δ : ℝ) (P : J → R → FilteredRanks w) (ω : Ω) (t : ℕ) :
    EpochSchedule.variation (vector c δ P ω (t+1)) (vector c δ P ω t) ≤
      ∑ i, charge (active c δ (P i) ω t) (active c δ (P i) ω (t+1)) := by
  apply sum_le_sum
  intro i _
  rw [abs_sub_comm]
  exact value_variation (active_valid c δ (P i) ω t) (active_valid c δ (P i) ω (t+1))

lemma wholesale_parent {c δ ε : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hδu : δ ≤ 1/1000)
    (hε : 0 < ε) (hεu : ε ≤ 1/1000) (P : J → R → FilteredRanks w) (V : R → FilteredRanks w)
    (htree : ∀ t ω, (∑ i,size (P i) t ω) ≤ size V t ω) (β : ℝ → ℝ) (ω : Ω) (t : ℕ) :
    EpochSchedule.parentCharge (vector c δ P ω t) (vector c δ P ω (t+1))
        (β (parent c ε V t ω)) (β (parent c ε V (t+1) ω)) ≤
      2*relativeCharge ε (clipped c ε V) t ω := by
  classical
  unfold EpochSchedule.parentCharge
  split_ifs with he
  · have hn : parent c ε V t ω≠parent c ε V (t+1) ω := fun hh => he (congrArg β hh)
    change _ ≤ 2*(if parent c ε V t ω=parent c ε V (t+1) ω then 0 else parent c ε V t ω+parent c ε V (t+1) ω)
    rw [ite_eq_right hn]
    linarith [total_parent hc hδ hδu hε hεu P V htree ω t,
      total_parent hc hδ hδu hε hεu P V htree ω (t+1)]
  · unfold relativeCharge
    split_ifs
    · norm_num
    · exact mul_nonneg (by norm_num) (add_nonneg (parent_nonneg hc.le ε V t ω) (parent_nonneg hc.le ε V (t+1) ω))

/-- The literal epoch recurrence is paid by actual active-size and parent
reference changes; the test does not assume its own amortized conclusion. -/
lemma wholesale_budget {c δ ε : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hδu : δ ≤ 1/1000)
    (hε : 0 < ε) (hεu : ε ≤ 1/1000) (P : J → R → FilteredRanks w) (V : R → FilteredRanks w)
    (htree : ∀ t ω, (∑ i,size (P i) t ω) ≤ size V t ω) (β : ℝ → ℝ) (ω : Ω) (N : ℕ) :
    (∑ t ∈ range N, EpochSchedule.wholesale (vector c δ P ω t) (vector c δ P ω (t+1))
        (β (parent c ε V t ω)) (β (parent c ε V (t+1) ω))
        (EpochSchedule.run (vector c δ P ω) (fun t => β (parent c ε V t ω)) t)) ≤
      203*(∑ t ∈ range N, ∑ i,charge (active c δ (P i) ω t) (active c δ (P i) ω (t+1)))+
      2*(∑ t ∈ range N, relativeCharge ε (clipped c ε V) t ω) := by
  have hb := EpochSchedule.wholesale_budget (vector c δ P ω) (fun t => β (parent c ε V t ω))
    (vector_nonneg c δ P ω) N
  exact hb.trans (add_le_add
    (mul_le_mul_of_nonneg_left (sum_le_sum fun t _ => vector_variation c δ P ω t) (by norm_num))
    (by rw [mul_sum]; exact sum_le_sum fun t _ => wholesale_parent hc hδ hδu hε hεu P V htree β ω t))

end KServer.CoarseEpoch

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.CoarseSide
open RankTracking CoarseSchedule EpochSchedule

lemma C_nonneg {δ : ℝ} (hδ : 0 < δ) : 0 ≤ C δ := by unfold C factor; positivity

attribute [local instance] OAI.instDecidable_solutions
lemma update_budget {δ : ℝ} (hδ : 0 < δ) (x : ℕ → ℝ) (reset : ℕ → Prop)
    (hx : ∀ t, 0 ≤ x t) (t : ℕ) :
    charge δ x reset t+C δ*|x (t+1)-held δ x reset (t+1)| ≤
      C δ*|x t-held δ x reset t|+C δ*stepVariation x reset t := by
  have hC := C_nonneg hδ
  have hU := held_nonneg δ x reset hx t
  have ha := held_accuracy hδ x reset hx t
  by_cases hr : reset t
  · simp only [held,charge,not_true_eq_false,hr,false_and,true_or,ite_false,sub_self,abs_zero,mul_zero,add_zero,stepVariation,ite_true]
    exact mul_nonneg hC (abs_nonneg _)
  · by_cases hf : factorTest id δ (x (t+1)) (held δ x reset t)
    · have hp := factor_change_charge (hx (t+1)) hU hδ hf
      have hp' : x t+x (t+1) ≤ C δ*|x (t+1)-held δ x reset t| := by
        have he := mul_le_mul_of_nonneg_left hp (show 0 ≤ 1+δ by linarith)
        have hh : x (t+1) ≤ (1+δ)*x (t+1) := by nlinarith [mul_nonneg hδ.le (hx (t+1))]
        unfold C factor
        change x (t+1)+held δ x reset t ≤ (1+2/δ)*|x (t+1)-held δ x reset t| at hp
        nlinarith
      simp only [held,charge,hr,not_false_eq_true,hf,and_self,or_true,ite_true,
        sub_self,abs_zero,mul_zero,add_zero,stepVariation,ite_false]
      exact hp'.trans (by nlinarith [mul_le_mul_of_nonneg_left (abs_sub_le (x (t+1)) (x t) (held δ x reset t)) hC])
    · simp only [held,charge,hr,not_false_eq_true,hf,and_false,false_or,ite_false,zero_add,stepVariation]
      nlinarith [mul_le_mul_of_nonneg_left (abs_sub_le (x (t+1)) (x t) (held δ x reset t)) hC]

lemma budget {δ : ℝ} (hδ : 0 < δ) (x : ℕ → ℝ) (reset : ℕ → Prop)
    (hx : ∀ t, 0 ≤ x t) (N : ℕ) :
    (∑ t ∈ range N, charge δ x reset t) ≤ C δ*(∑ t ∈ range N, stepVariation x reset t) := by
  have hh : (∑ t ∈ range N, charge δ x reset t)+C δ*|x N-held δ x reset N| ≤
      C δ*(∑ t ∈ range N, stepVariation x reset t) := by
    induction N with
    | zero => simp [held]
    | succ N ih =>
      have h := update_budget hδ x reset hx N
      rw [sum_range_succ,sum_range_succ,mul_add]
      linarith
  linarith [mul_nonneg (C_nonneg hδ) (abs_nonneg (x N-held δ x reset N))]

variable {J K : Type} [Fintype J]

lemma mark_unchanged {x y : J → ℝ} {a b : K} {s : EpochSchedule.State J}
    (hr : ¬EpochSchedule.reset x y a b s) :
    dominant (EpochSchedule.update x y a b s)=dominant s := by
  simp only [EpochSchedule.update,ite_eq_right hr,dominant]

lemma side_variation {x y : J → ℝ} {s t : EpochSchedule.State J}
    (he : dominant s=dominant t) : |side x s-side y t| ≤ variation x y := by
  unfold side
  rw [←sum_sub_distrib]
  calc _ ≤ ∑ i, |(if dominant s=some i then 0 else if (dominant s).isSome then x i else 0)-
        (if dominant t=some i then 0 else if (dominant t).isSome then y i else 0)| := abs_sum_le_sum_abs _ _
       _ ≤ _ := by
        apply sum_le_sum
        intro i _
        rw [he]
        split_ifs <;> simp [abs_nonneg]

lemma side_stepVariation (x : ℕ → J → ℝ) (key : ℕ → K) (t : ℕ) :
    stepVariation (sideInput x key) (epochReset x key) t ≤ variation (x (t+1)) (x t) := by
  unfold stepVariation
  split_ifs with hr
  · exact variation_nonneg _ _
  · apply side_variation
    exact mark_unchanged hr

/-- Side-reference refreshes are paid independently of the number of epochs. -/
lemma side_budget {δ : ℝ} (hδ : 0 < δ) (x : ℕ → J → ℝ)
    (key : ℕ → K) (hx : ∀ t i, 0 ≤ x t i) (N : ℕ) :
    (∑ t ∈ range N, charge δ (sideInput x key) (epochReset x key) t) ≤
      C δ*(∑ t ∈ range N, variation (x (t+1)) (x t)) := by
  exact (budget hδ _ _ (fun t => side_nonneg (hx t) _) N).trans
    (mul_le_mul_of_nonneg_left (sum_le_sum fun t _ => side_stepVariation x key t) (C_nonneg hδ))

end KServer.CoarseSide

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.CoarseScale
open RankTracking RankFunctions CoreFlags
variable {Ω J R : Type} [Fintype Ω] [Fintype J] [Fintype R] {w : Ω → ℝ}

lemma noncore_nonneg (δ : ℝ) (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) :
    0 ≤ noncore δ P t ω := by
  apply sum_nonneg
  intro a _
  split_ifs
  · rfl
  · exact (FineCaps.estimate_range (by norm_num) (P a) t ω).1

lemma noncore_bound {δ : ℝ} (hδ : 0 < δ) (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) :
    noncore δ P t ω ≤ 36*(1+δ)*CoarseProcess.size P t ω := by
  calc _ ≤ ∑ a, FineCaps.estimate δ 0 (P a) t ω := by
        apply sum_le_sum
        intro a _
        split_ifs
        · exact (FineCaps.estimate_range (by norm_num) (P a) t ω).1
        · rfl
       _ ≤ ∑ a, (1+δ)*(36*sizeRank ((P a).p t ω)) := by
        apply sum_le_sum
        intro a _
        exact (FineCaps.estimate_accuracy hδ (by norm_num) (P a) t ω).2.trans
          (mul_le_mul_of_nonneg_left (rank_size (by norm_num) ((P a).range t ω).1) (by linarith))
       _ = _ := by unfold CoarseProcess.size; rw [←mul_sum,←mul_sum]; ring

lemma term_variation {e e' : ℝ} (he : e ∈ Set.Icc 0 1) (he' : e' ∈ Set.Icc 0 1)
    (b b' : Bool) :
    |(if b' then 0 else e')-(if b then 0 else e)| ≤ |e'-e|+(if b'=b then (0:ℝ) else 1) := by
  cases b <;> cases b' <;> simp [abs_of_nonneg he.1,abs_of_nonneg he'.1] <;>
    linarith [he.2,he'.2,abs_nonneg (e'-e)]

lemma noncore_variation (δ : ℝ) (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) :
    |noncore δ P (t+1) ω-noncore δ P t ω| ≤
      (∑ a, |FineCaps.estimate δ 0 (P a) (t+1) ω-FineCaps.estimate δ 0 (P a) t ω|)+
      ∑ a,change (P a) t ω := by
  unfold noncore
  rw [←sum_sub_distrib,←sum_add_distrib]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun a _ =>
    term_variation (FineCaps.estimate_range (by norm_num) (P a) t ω)
      (FineCaps.estimate_range (by norm_num) (P a) (t+1) ω) _ _)

lemma mark_positive {x : J → ℝ} {s : EpochSchedule.State J} {o : J}
    (hs : EpochSchedule.Valid x s) (ho : EpochSchedule.dominant s=some o) : 0 < x o := by
  have hp : 0 < EpochSchedule.total s.reference := by
    unfold EpochSchedule.dominant at ho
    split_ifs at ho with h
    exact h.choose_spec.1
  have := EpochSchedule.dominant_large hs ho
  linarith

lemma scale_nonneg (δ : ℝ) (P : J → R → FilteredRanks w) (t : ℕ) (ω : Ω)
    (s : EpochSchedule.State J) : 0 ≤ scale δ P t ω s := by
  unfold scale
  cases EpochSchedule.dominant s with
  | none => rfl
  | some i => exact noncore_nonneg δ (P i) t ω

lemma scale_bound {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hδu : δ ≤ 1/1000)
    (P : J → R → FilteredRanks w) (t : ℕ) (ω : Ω) (s : EpochSchedule.State J)
    (hs : EpochSchedule.Valid (CoarseEpoch.vector c δ P ω t) s) :
    scale δ P t ω s ≤ 41*EpochSchedule.total (CoarseEpoch.vector c δ P ω t) := by
  classical
  unfold scale
  cases ho : EpochSchedule.dominant s with
  | none => exact mul_nonneg (by norm_num) (EpochSchedule.total_nonneg (CoarseEpoch.vector_nonneg c δ P ω t))
  | some i =>
    have hp := mark_positive hs ho
    have ha : (CoarseProcess.active c δ (P i) ω t).active=true := by
      cases he : (CoarseProcess.active c δ (P i) ω t).active with
      | true => rfl
      | false =>
        have hz := (CoarseProcess.active_valid c δ (P i) ω t).2 he
        change 0 < (CoarseProcess.active c δ (P i) ω t).value at hp
        linarith
    have hlo := ((CoarseProcess.active_accuracy hc hδ hδu (P i) ω t).1 ha).1
    have hv := single_le_sum (fun j _ => CoarseEpoch.vector_nonneg c δ P ω t j) (mem_univ i)
    change (CoarseProcess.active c δ (P i) ω t).value ≤ EpochSchedule.total (CoarseEpoch.vector c δ P ω t) at hv
    have hb := noncore_bound hδ (P i) t ω
    have hm := CoarseProcess.size_nonneg (P i) t ω
    have hd := mul_le_mul_of_nonneg_right hδu hm
    change noncore δ (P i) t ω ≤ _
    nlinarith

lemma scale_unchanged_variation (δ : ℝ) (P : J → R → FilteredRanks w)
    (t : ℕ) (ω : Ω) (s s' : EpochSchedule.State J)
    (he : EpochSchedule.dominant s'=EpochSchedule.dominant s) :
    |scale δ P (t+1) ω s'-scale δ P t ω s| ≤
      ∑ i, ((∑ a, |FineCaps.estimate δ 0 (P i a) (t+1) ω-FineCaps.estimate δ 0 (P i a) t ω|)+
        ∑ a,change (P i a) t ω) := by
  have hnonneg i : 0 ≤ (∑ a, |FineCaps.estimate δ 0 (P i a) (t+1) ω-FineCaps.estimate δ 0 (P i a) t ω|)+
      ∑ a,change (P i a) t ω := by
    apply add_nonneg (sum_nonneg fun _ _ => abs_nonneg _)
    apply sum_nonneg; intro a _; unfold change; split_ifs <;> norm_num
  unfold scale
  rw [he]
  cases ho : EpochSchedule.dominant s with
  | none => simpa using sum_nonneg (fun i _ => hnonneg i)
  | some i => exact (noncore_variation δ (P i) t ω).trans (single_le_sum (fun i _ => hnonneg i) (mem_univ i))

end KServer.CoarseScale

namespace KServer.CoarseScale
open RankTracking RankFunctions CoreFlags
variable {Ω J R K : Type} [Fintype Ω] [Fintype J] [Fintype R] {w : Ω → ℝ}

lemma scale_step {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hδu : δ ≤ 1/1000)
    (P : J → R → FilteredRanks w) (ω : Ω) (key : ℕ → K) (t : ℕ) :
    let x := CoarseEpoch.vector c δ P ω
    let s := EpochSchedule.run x key
    |scale δ P (t+1) ω (s (t+1))-scale δ P t ω (s t)| ≤
      (∑ i, ((∑ a, |FineCaps.estimate δ 0 (P i a) (t+1) ω-FineCaps.estimate δ 0 (P i a) t ω|)+
        ∑ a,change (P i a) t ω))+
      41*EpochSchedule.wholesale (x t) (x (t+1)) (key t) (key (t+1)) (s t) := by
  intro x s
  have hv n := EpochSchedule.run_valid x key (CoarseEpoch.vector_nonneg c δ P ω) n
  by_cases hr : EpochSchedule.reset (x t) (x (t+1)) (key t) (key (t+1)) (s t)
  · have hb₀ := scale_bound hc hδ hδu P t ω (s t) (hv t)
    have hb₁ := scale_bound hc hδ hδu P (t+1) ω (s (t+1)) (hv (t+1))
    have hn₀ := scale_nonneg δ P t ω (s t)
    have hn₁ := scale_nonneg δ P (t+1) ω (s (t+1))
    have hj : 0 ≤ ∑ i, ((∑ a, |FineCaps.estimate δ 0 (P i a) (t+1) ω-FineCaps.estimate δ 0 (P i a) t ω|)+
        ∑ a,change (P i a) t ω) := by
      apply sum_nonneg
      intro i _
      apply add_nonneg (sum_nonneg fun _ _ => abs_nonneg _)
      apply sum_nonneg; intro a _; unfold change; split_ifs <;> norm_num
    rw [EpochSchedule.wholesale,ite_eq_left hr]
    apply abs_le.mpr
    constructor <;> linarith
  · rw [EpochSchedule.wholesale,ite_eq_right hr,mul_zero,add_zero]
    apply scale_unchanged_variation
    exact CoarseSide.mark_unchanged hr

/-- The change of dominant flex scale is paid by actual elementary trackers,
core flips, and wholesale totals. This includes changes of dominant identity. -/
lemma scale_budget {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hδu : δ ≤ 1/1000)
    (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω,w ω=1)
    (P : J → R → FilteredRanks w) (key : Ω → ℕ → K) (N : ℕ) :
    (∑ t ∈ range N, avg w (fun ω =>
      |scale δ P (t+1) ω (EpochSchedule.run (CoarseEpoch.vector c δ P ω) (key ω) (t+1))-
       scale δ P t ω (EpochSchedule.run (CoarseEpoch.vector c δ P ω) (key ω) t)|)) ≤
      (80/δ+(CoreFlags.tolerance^2)⁻¹)*
        ((∑ i, ∑ a, ∑ t ∈ range N, avg w (fun ω => |(P i a).p (t+1) ω-(P i a).before (t+1) ω|))+
          Fintype.card J*Fintype.card R)+
      41*(∑ t ∈ range N, avg w (fun ω => EpochSchedule.wholesale
        (CoarseEpoch.vector c δ P ω t) (CoarseEpoch.vector c δ P ω (t+1))
        (key ω t) (key ω (t+1)) (EpochSchedule.run (CoarseEpoch.vector c δ P ω) (key ω) t))) := by
  let drift i a := ∑ t ∈ range N, avg w (fun ω => |(P i a).p (t+1) ω-(P i a).before (t+1) ω|)
  have he i a := FineCaps.estimate_variation_budget hw hw1 hδ (by linarith) (by norm_num : (0:ℝ) ∈ Set.Icc 0 (1/100)) (P i a) N
  have hf := CoreFlags.core_change_budget hw hw1 (fun ia : J × R => P ia.1 ia.2) N
  have hest : (∑ t ∈ range N, avg w (fun ω => ∑ i,∑ a,
      |FineCaps.estimate δ 0 (P i a) (t+1) ω-FineCaps.estimate δ 0 (P i a) t ω|)) ≤
      (80/δ)*((∑ i,∑ a,drift i a)+Fintype.card J*Fintype.card R) := by
    simp_rw [avg_sum]
    rw [sum_comm]
    calc _ = ∑ i, ∑ a, ∑ t ∈ range N, avg w (fun ω =>
        |FineCaps.estimate δ 0 (P i a) (t+1) ω-FineCaps.estimate δ 0 (P i a) t ω|) := by
          apply sum_congr rfl; intro i _; exact sum_comm
         _ ≤ ∑ i,∑ a,(80/δ)*(drift i a+1) := sum_le_sum fun i _ => sum_le_sum fun a _ => he i a
         _ = _ := by simp_rw [←mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul,mul_one,card_univ]
  have hflags : (∑ t ∈ range N, avg w (fun ω => ∑ i,∑ a,change (P i a) t ω)) ≤
      (CoreFlags.tolerance^2)⁻¹*((∑ i,∑ a,drift i a)+Fintype.card J*Fintype.card R) := by
    have hd : (∑ t ∈ range N, avg w (fun ω => ∑ i,∑ a,
        |(P i a).p (t+1) ω-(P i a).before (t+1) ω|)) = ∑ i,∑ a,drift i a := by
      simp_rw [avg_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      exact sum_comm
    simpa only [Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul,hd] using hf
  calc _ ≤ ∑ t ∈ range N, avg w (fun ω =>
        (∑ i, ((∑ a, |FineCaps.estimate δ 0 (P i a) (t+1) ω-FineCaps.estimate δ 0 (P i a) t ω|)+
        ∑ a,change (P i a) t ω))+
        41*EpochSchedule.wholesale (CoarseEpoch.vector c δ P ω t) (CoarseEpoch.vector c δ P ω (t+1))
          (key ω t) (key ω (t+1)) (EpochSchedule.run (CoarseEpoch.vector c δ P ω) (key ω) t)) := by
        exact sum_le_sum fun t _ => avg_mono hw (fun ω => scale_step hc hδ hδu P ω (key ω) t)
       _ = (∑ t ∈ range N, avg w (fun ω => ∑ i,∑ a,
          |FineCaps.estimate δ 0 (P i a) (t+1) ω-FineCaps.estimate δ 0 (P i a) t ω|))+
         (∑ t ∈ range N, avg w (fun ω => ∑ i,∑ a,change (P i a) t ω))+
         41*(∑ t ∈ range N, avg w (fun ω => EpochSchedule.wholesale
           (CoarseEpoch.vector c δ P ω t) (CoarseEpoch.vector c δ P ω (t+1))
           (key ω t) (key ω (t+1)) (EpochSchedule.run (CoarseEpoch.vector c δ P ω) (key ω) t))) := by
          simp_rw [sum_add_distrib,avg_add,avg_mul,sum_add_distrib,←mul_sum]
       _ ≤ _ := by dsimp only [drift] at hest hflags; nlinarith

end KServer.CoarseScale

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_OutputDynamics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/- The two output formulas, finite-star algebra and static cap-proportion feasibility. -/


noncomputable section
open Finset
open scoped BigOperators
namespace KServer.OutputDynamics
variable {I : Type*} [Fintype I]

lemma variation_nonneg (x y : I → ℝ) : 0 ≤ variation x y :=
  sum_nonneg fun _ _ => abs_nonneg _

lemma variation_sum (x y : I → ℝ) : |(∑ i, x i) - ∑ i, y i| ≤ variation x y := by
  rw [← sum_sub_distrib]
  exact abs_sum_le_sum_abs _ _

lemma positive_part_lipschitz (x y : ℝ) : |max x 0 - max y 0| ≤ |x - y| := by
  exact abs_max_sub_max_le_abs x y 0

lemma excess_lipschitz (d e : I → ℝ) (q p : ℝ) :
    |excess d q - excess e p| ≤ variation d e + |q - p| := by
  apply (positive_part_lipschitz _ _).trans
  calc |((∑ i, d i) - q) - ((∑ i, e i) - p)| =
      |((∑ i, d i) - ∑ i, e i) + (p - q)| := by congr 1; ring
    _ ≤ |(∑ i, d i) - ∑ i, e i| + |p - q| := abs_add_le _ _
    _ ≤ variation d e + |q - p| := by rw [abs_sub_comm p q]; exact add_le_add (variation_sum d e) (le_refl _)

/-! Rule II: the finite type I here indexes sides only, with the dominant
coordinate stored separately. Thus the formulation includes an empty side set. -/

lemma scaled_movement {D D' Cw : ℝ} {w w' : I → ℝ} (hD' : 0 ≤ D')
    (hw : ∀ i, 0 ≤ w i) (hws : (∑ i, w i) ≤ Cw) :
    variation (fun i => D' * w' i) (fun i => D * w i) ≤
      D' * variation w' w + Cw * |D' - D| := by
  calc variation (fun i => D' * w' i) (fun i => D * w i) ≤
      (∑ i, (D' * |w' i - w i| + |D' - D| * w i)) := by
        apply sum_le_sum
        intro i _
        calc |D' * w' i - D * w i| = |D' * (w' i - w i) + (D' - D) * w i| := by congr 1; ring
          _ ≤ |D' * (w' i - w i)| + |(D' - D) * w i| := abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg hD', abs_of_nonneg (hw i)]
    _ = D' * variation w' w + |D' - D| * (∑ i, w i) := by
      rw [sum_add_distrib, ← mul_sum, ← mul_sum]; rfl
    _ ≤ _ := by have := mul_le_mul_of_nonneg_left hws (abs_nonneg (D' - D)); nlinarith

lemma output_from_holes_movement (d d' ζ ζ' : I → ℝ) :
    variation (fun i => d' i - ζ' i) (fun i => d i - ζ i) ≤
      variation d' d + variation ζ' ζ := by
  rw [variation, variation, variation, ← sum_add_distrib]
  apply sum_le_sum
  intro i _
  calc |(d' i - ζ' i) - (d i - ζ i)| = |(d' i - d i) - (ζ' i - ζ i)| := by congr 1; ring
    _ ≤ _ := abs_sub _ _

lemma variation_le_mass {z z' : I → ℝ} (hz : ∀ i, 0 ≤ z i) (hz' : ∀ i, 0 ≤ z' i) :
    variation z' z ≤ (∑ i, z' i)+(∑ i, z i) := by
  rw [←sum_add_distrib]
  apply sum_le_sum
  intro i _
  apply abs_sub_le_iff.mpr
  constructor <;> linarith [hz i,hz' i]

end KServer.OutputDynamics
end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.CausalSimplex
open AdaptiveMinimization SimplexFamilies AdaptiveAllocation
variable {J R : Type} [Fintype J] [DecidableEq J] [Fintype R]

variable {Ω : Type} [Fintype Ω]

omit [Fintype Ω] in
lemma run_adapted (C ell : ℝ) (d : ℕ → Ω → Input J R) (H : ℕ → Ω → ℕ)
    (href : ∀ t ω z, H (t+1) ω=H (t+1) z → H t ω=H t z)
    (hd : ∀ t ω z, H t ω=H t z → d t ω=d t z) (t : ℕ) (ω z : Ω)
    (he : H t ω=H t z) : run C ell d t ω=run C ell d t z := by
  exact state_adapted _ _ _ _ _ H href hd
    (fun t ω z h => congrArg Input.ranks (hd t ω z h))
    (fun t ω z h => congrArg mass (hd t ω z h)) t ω z he

end KServer.CausalSimplex

namespace KServer.CausalSimplex
open AdaptiveMinimization SimplexFamilies AdaptiveAllocation
variable {J R : Type} [Fintype J] [DecidableEq J] [Fintype R]

lemma candidate_regular (A B : Finset J) (f g : J → R → Bool) (h h' : J → ℝ)
    (hh : ∀ i, 1≤h i) (hh' : ∀ i, 1≤h' i) (C ell ct : ℝ)
    (p : J × R → ℝ) (a : J → ℝ) :
    candidate C ell (regular A f h (fun i => ct*h i/ell) hh)
      (regular B g h' (fun i => ct*h' i/ell) hh') p a=
      regularTransport C ell ct A B g h hh p a := rfl

lemma move_regular {A B : Finset J} (hA : A.Nonempty) (hB : B.Nonempty)
    (f g : J → R → Bool) (h h' : J → ℝ)
    (hh : ∀ i, 1≤h i) (hh' : ∀ i, 1≤h' i)
    {C ell ct ηmax Cexp : ℝ} (hC : 0<C) (hl : 0<ell) (hc : 0 < ct)
    (hmax : ∀ i∈A, ct*h i/ell≤ηmax) (hCexp : 0≤Cexp)
    (htail : ∑ i∈A, Real.exp (-h i)≤Cexp)
    (hgap : 2*(25+32*Cexp)*(1+ηmax)<C*ct)
    (p : J × R → ℝ) (hp : ∀ ir, 0≤p ir) (a : J → ℝ)
    (ha : a∈ChangingDomains.simplex A) (r r' : J × R → ℝ) (e : ℕ) :
    move C ell ⟨regular A f h (fun i => ct*h i/ell) hh,r,e⟩
      ⟨regular B g h' (fun i => ct*h' i/ell) hh',r',e⟩ p a=
      regularTransport C ell ct A B g h hh p a := by
  classical
  have hm := regular_transport_mem hA hB g h hh hC hl hc hmax hCexp htail hgap p hp a ha
  unfold move
  dsimp only
  rw [ite_eq_left rfl, candidate_regular]
  exact ite_eq_left hm

/-- The fully specified causal successor is the source's prepared/deleted/
minimized successor on an ordinary unmarked epoch. No policy-existence or
expected drift statement is an assumption. -/
lemma regular_successor {Ω : Type} [Fintype Ω] (d : ℕ → Ω → Input J R)
    (t : ℕ) (ω : Ω) {A B : Finset J} (hA : A.Nonempty) (hB : B.Nonempty)
    (f g : J → R → Bool) (h h' : J → ℝ)
    (hh : ∀ i, 1≤h i) (hh' : ∀ i, 1≤h' i)
    {C ell ct ηmax Cexp : ℝ} (hC : 0<C) (hl : 0<ell) (hc : 0 < ct)
    (hmax : ∀ i∈A, ct*h i/ell≤ηmax) (hCexp : 0≤Cexp)
    (htail : ∑ i∈A, Real.exp (-h i)≤Cexp)
    (hgap : 2*(25+32*Cexp)*(1+ηmax)<C*ct)
    (hp : ∀ ir, 0≤(d (t+1) ω).ranks ir)
    (hold : (d t ω).data=regular A f h (fun i => ct*h i/ell) hh)
    (hnew : (d (t+1) ω).data=regular B g h' (fun i => ct*h' i/ell) hh')
    (he : (d t ω).epoch=(d (t+1) ω).epoch) :
    run C ell d (t+1) ω = regularStep C ell ct A B g h h' hh hh'
      (d (t+1) ω).ranks (run C ell d t ω) := by
  have ha := run_mem C ell d t ω
  rw [hold] at ha
  change run C ell d t ω∈ChangingDomains.simplex A at ha
  have hm := move_regular hA hB f g h h' hh hh' hC hl hc hmax hCexp htail hgap
    (d (t+1) ω).ranks hp (run C ell d t ω) ha (d t ω).ranks (d (t+1) ω).ranks (d t ω).epoch
  have eo : d t ω=⟨regular A f h (fun i => ct*h i/ell) hh,(d t ω).ranks,(d t ω).epoch⟩ :=
    congrArg (fun v => (⟨v,(d t ω).ranks,(d t ω).epoch⟩ : Input J R)) hold
  have en : d (t+1) ω=⟨regular B g h' (fun i => ct*h' i/ell) hh',(d (t+1) ω).ranks,(d t ω).epoch⟩ := by
    calc
      d (t+1) ω = ⟨regular B g h' (fun i => ct*h' i/ell) hh',
          (d (t+1) ω).ranks,(d (t+1) ω).epoch⟩ :=
        congrArg (fun v => (⟨v,(d (t+1) ω).ranks,(d (t+1) ω).epoch⟩ : Input J R)) hnew
      _ = _ := by rw [he]
  have hm' : move C ell (d t ω) (d (t+1) ω) (d (t+1) ω).ranks (run C ell d t ω)=
      regularTransport C ell ct A B g h hh (d (t+1) ω).ranks (run C ell d t ω) :=
    (congrArg₂ (fun old new : Input J R => move C ell old new
      (d (t+1) ω).ranks (run C ell d t ω)) eo en).trans hm
  rw [run_successor,hm']
  unfold mass
  rw [hnew]
  rfl

lemma candidate_marked (A B : Finset J) (f g : J → R → Bool) (o : J)
    (h h' : J → ℝ) (u u' : ℝ) (hu : 0<u) (hu1 : u≤1)
    (hu' : 0<u') (hu1' : u'≤1) (hh : ∀ i≠o, 1≤h i) (hh' : ∀ i≠o, 1≤h' i)
    (C ell ct : ℝ) (p : J × R → ℝ) (a : J → ℝ) :
    candidate C ell (marked A f o h (fun i => ct*h i/ell) u hu hu1 hh)
      (marked B g o h' (fun i => ct*h' i/ell) u' hu' hu1' hh') p a=
      markedTransport C ell ct A B g o h u hu hu1 hh p a := rfl

lemma move_marked {A B : Finset J} {o : J} (hoA : o∈A) (hB : B.Nonempty)
    (f g : J → R → Bool) (h h' : J → ℝ) {u u' : ℝ}
    (hu : 0<u) (hu1 : u≤1) (hu' : 0<u') (hu1' : u'≤1)
    (ho : h o=u) (hh : ∀ i≠o, 1≤h i) (hh' : ∀ i≠o, 1≤h' i)
    {C ell ct ηmax Cexp c : ℝ} (hC : 0<C) (hl : 0<ell) (hc : 0 < ct)
    (hmax : ∀ i∈A, ct*h i/ell≤ηmax) (hCexp : 0≤Cexp)
    (hsideC : 0 < c) (hsideC1 : c≤1)
    (hside : ∀ i∈A, i≠o → c*(1+Real.log (1/u))≤h i)
    (htail : ∑ i∈A.erase o, Real.exp (-h i)≤Cexp*u)
    (hgap : 2*((25*c+2+32*Cexp)/c)*(1+ηmax)<C*ct)
    (p : J × R → ℝ) (hp : ∀ ir, 0≤p ir) (a : J → ℝ)
    (ha : a∈ChangingDomains.simplex A) (r r' : J × R → ℝ) (e : ℕ) :
    move C ell ⟨marked A f o h (fun i => ct*h i/ell) u hu hu1 hh,r,e⟩
      ⟨marked B g o h' (fun i => ct*h' i/ell) u' hu' hu1' hh',r',e⟩ p a=
      markedTransport C ell ct A B g o h u hu hu1 hh p a := by
  classical
  have hm := marked_transport_mem hoA hB g h hu hu1 ho hh hC hl hc hmax hCexp
    hsideC hsideC1 hside htail hgap p hp a ha
  unfold move
  dsimp only
  rw [ite_eq_left rfl, candidate_marked]
  exact ite_eq_left hm

lemma marked_successor {Ω : Type} [Fintype Ω] (d : ℕ → Ω → Input J R)
    (t : ℕ) (ω : Ω) {A B : Finset J} {o : J} (hoA : o∈A) (hB : B.Nonempty)
    (f g : J → R → Bool) (h h' : J → ℝ) {u u' : ℝ}
    (hu : 0<u) (hu1 : u≤1) (hu' : 0<u') (hu1' : u'≤1)
    (ho : h o=u) (hh : ∀ i≠o, 1≤h i) (hh' : ∀ i≠o, 1≤h' i)
    {C ell ct ηmax Cexp c : ℝ} (hC : 0<C) (hl : 0<ell) (hc : 0 < ct)
    (hmax : ∀ i∈A, ct*h i/ell≤ηmax) (hCexp : 0≤Cexp)
    (hsideC : 0 < c) (hsideC1 : c≤1)
    (hside : ∀ i∈A, i≠o → c*(1+Real.log (1/u))≤h i)
    (htail : ∑ i∈A.erase o, Real.exp (-h i)≤Cexp*u)
    (hgap : 2*((25*c+2+32*Cexp)/c)*(1+ηmax)<C*ct)
    (hp : ∀ ir, 0≤(d (t+1) ω).ranks ir)
    (hold : (d t ω).data=marked A f o h (fun i => ct*h i/ell) u hu hu1 hh)
    (hnew : (d (t+1) ω).data=marked B g o h' (fun i => ct*h' i/ell) u' hu' hu1' hh')
    (he : (d t ω).epoch=(d (t+1) ω).epoch) :
    run C ell d (t+1) ω = markedStep C ell ct A B g o h h' u u' hu hu1 hu' hu1' hh hh'
      (d (t+1) ω).ranks (run C ell d t ω) := by
  have ha := run_mem C ell d t ω
  rw [hold] at ha
  change run C ell d t ω∈ChangingDomains.simplex A at ha
  have hm := move_marked hoA hB f g h h' hu hu1 hu' hu1' ho hh hh' hC hl hc hmax hCexp
    hsideC hsideC1 hside htail hgap (d (t+1) ω).ranks hp (run C ell d t ω) ha
    (d t ω).ranks (d (t+1) ω).ranks (d t ω).epoch
  have eo : d t ω=⟨marked A f o h (fun i => ct*h i/ell) u hu hu1 hh,
      (d t ω).ranks,(d t ω).epoch⟩ :=
    congrArg (fun v => (⟨v,(d t ω).ranks,(d t ω).epoch⟩ : Input J R)) hold
  have en : d (t+1) ω=⟨marked B g o h' (fun i => ct*h' i/ell) u' hu' hu1' hh',
      (d (t+1) ω).ranks,(d t ω).epoch⟩ := by
    calc
      d (t+1) ω = ⟨marked B g o h' (fun i => ct*h' i/ell) u' hu' hu1' hh',
          (d (t+1) ω).ranks,(d (t+1) ω).epoch⟩ :=
        congrArg (fun v => (⟨v,(d (t+1) ω).ranks,(d (t+1) ω).epoch⟩ : Input J R)) hnew
      _ = _ := by rw [he]
  have hm' : move C ell (d t ω) (d (t+1) ω) (d (t+1) ω).ranks (run C ell d t ω)=
      markedTransport C ell ct A B g o h u hu hu1 hh (d (t+1) ω).ranks (run C ell d t ω) :=
    (congrArg₂ (fun old new : Input J R => move C ell old new
      (d (t+1) ω).ranks (run C ell d t ω)) eo en).trans hm
  rw [run_successor,hm']
  unfold mass
  rw [hnew]
  rfl

end KServer.CausalSimplex

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_AllocationSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Finset

namespace KServer.AllocationSchedule
open EpochSchedule
variable {J K : Type} [Fintype J] [DecidableEq J]

attribute [local instance] OAI.KServer.AllocationSchedule.instDecidable_solutions_1
omit [DecidableEq J] in
lemma epoch_same_iff (x : ℕ → J → ℝ) (key : ℕ → K) (t : ℕ) :
    epoch x key t=epoch x key (t+1) ↔ ¬CoarseSide.epochReset x key t := by
  classical
  rw [epoch]
  split_ifs <;> simp_all

end KServer.AllocationSchedule

end

/-! Binding the literal filtered-rank size schedule to the live child domain.
In particular no core or positive lower-envelope rank is silently discarded
when the coarse active state turns off. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.StarProfile
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch AllocationSchedule
variable {Ω J R : Type} [Fintype Ω] [Fintype J] [Fintype R] {w : Ω → ℝ}

omit [Fintype J] in
lemma vector_adapted (δ : ℝ) (P : J → R → FilteredRanks w) (H : ℕ → Ω → ℕ)
    (hH : ∀ i r t ω,(P i r).history t ω=H t ω)
    (hr : ∀ t ω z,H (t+1) ω=H (t+1) z → H t ω=H t z)
    (t : ℕ) (ω z : Ω) (he : H t ω=H t z) :
    vector cutoff δ P ω t=vector cutoff δ P z t := by
  funext i
  exact congrArg CoarseSchedule.State.value (active_adapted cutoff δ (P i) H (hH i) hr t ω z he)

lemma parent_adapted (c δ : ℝ) (P : R → FilteredRanks w) (H : ℕ → Ω → ℕ)
    (hH : ∀ r t ω,(P r).history t ω=H t ω)
    (hr : ∀ t ω z,H (t+1) ω=H (t+1) z → H t ω=H t z)
    (t : ℕ) (ω z : Ω) (he : H t ω=H t z) : parent c δ P t ω=parent c δ P t z := by
  induction t with
  | zero => exact congrArg (max c) (estimate_adapted δ P H hH 0 ω z he)
  | succ t ih =>
    have hh:=estimate_adapted δ P H hH (t+1) ω z he
    have hp:=ih (hr t ω z he)
    change (if factorTest id δ (clipped c δ P (t+1) ω) (parent c δ P t ω)
      then clipped c δ P (t+1) ω else parent c δ P t ω)=_
    simp only [clipped,hh,hp]
    rfl

end KServer.StarProfile

end


/-! Feasibility of the literal held-size scheduler's minimizing simplex law,
including empty and side-free marked epochs. Constants are uniform in degree. -/


/-! Actual true and held beta parameters. Their gaps follow from the true
parent/child size relation and the literal coarse epoch, not an output oracle. -/


/-! Prefix causality of the literal epoch, mark, side-total, log-size and
simplex-data recurrences. These equalities use the real input prefix; there
is no reinitialization at a fictitious conditional prefix. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ScheduleCausality
attribute [local instance] Classical.propDecidable
open AllocationSchedule EpochSchedule
variable {J K R : Type} [Fintype J] [DecidableEq J] [Fintype R]

lemma PrefixEq.mono {A : Type*} {t s : ℕ} {a b : ℕ → A}
    (h : PrefixEq t a b) (hs : s≤t) : PrefixEq s a b := fun j hj=>h j (hj.trans hs)

omit [DecidableEq J] in
lemma run_prefix (x y : ℕ → J → ℝ) (key key' : ℕ → K) (t : ℕ)
    (hx : PrefixEq t x y) (hk : PrefixEq t key key') : run x key t=run y key' t := by
  induction t with
  | zero => simp only [run,hx 0 le_rfl]
  | succ t ih =>
    have ht : t≤t+1 := Nat.le_succ t
    simp only [run,hx t ht,hx (t+1) le_rfl,hk t ht,hk (t+1) le_rfl,
      ih (hx.mono ht) (hk.mono ht)]

omit [DecidableEq J] in
lemma mass_prefix (x y : ℕ → J → ℝ) (key key' : ℕ → K) (t : ℕ)
    (hx : PrefixEq t x y) (hk : PrefixEq t key key') : mass x key t=mass y key' t :=
  congrArg (fun s:State J=>total s.reference) (run_prefix x y key key' t hx hk)

omit [DecidableEq J] in
lemma side_prefix (x y : ℕ → J → ℝ) (key key' : ℕ → K) (t : ℕ)
    (hx : PrefixEq t x y) (hk : PrefixEq t key key') :
    CoarseSide.sideInput x key t=CoarseSide.sideInput y key' t := by
  simp only [CoarseSide.sideInput,hx t le_rfl,run_prefix x y key key' t hx hk]

omit [DecidableEq J] in
lemma reset_prefix (x y : ℕ → J → ℝ) (key key' : ℕ → K) (t : ℕ)
    (hx : PrefixEq (t+1) x y) (hk : PrefixEq (t+1) key key') :
    CoarseSide.epochReset x key t=CoarseSide.epochReset y key' t := by
  have ht : t≤t+1 := Nat.le_succ t
  simp only [CoarseSide.epochReset,hx t ht,hx (t+1) le_rfl,hk t ht,hk (t+1) le_rfl,
    run_prefix x y key key' t (hx.mono ht) (hk.mono ht)]

omit [DecidableEq J] in
lemma sideHeld_prefix (δ : ℝ) (x y : ℕ → J → ℝ) (key key' : ℕ → K) (t : ℕ)
    (hx : PrefixEq t x y) (hk : PrefixEq t key key') : sideHeld δ x key t=sideHeld δ y key' t := by
  induction t with
  | zero => exact side_prefix x y key key' 0 hx hk
  | succ t ih =>
    change (if CoarseSide.epochReset x key t ∨ RankTracking.factorTest id δ
      (CoarseSide.sideInput x key (t+1)) (sideHeld δ x key t)
      then CoarseSide.sideInput x key (t+1) else sideHeld δ x key t)=_
    rw [reset_prefix x y key key' t hx hk,side_prefix x y key key' (t+1) hx hk,
      ih (hx.mono (Nat.le_succ t)) (hk.mono (Nat.le_succ t))]
    rfl

omit [DecidableEq J] in
lemma ratio_prefix (δ : ℝ) (x y : ℕ → J → ℝ) (key key' : ℕ → K) (t : ℕ)
    (hx : PrefixEq t x y) (hk : PrefixEq t key key') : sideRatio δ x key t=sideRatio δ y key' t := by
  rw [sideRatio,sideRatio,sideHeld_prefix δ x y key key' t hx hk,mass_prefix x y key key' t hx hk]

lemma weight_prefix (δ : ℝ) (x y : ℕ → J → ℝ) (key key' : ℕ → K) (t : ℕ)
    (hx : PrefixEq t x y) (hk : PrefixEq t key key') : weight δ x key t=weight δ y key' t := by
  funext i
  simp only [weight,run_prefix x y key key' t hx hk,ratio_prefix δ x y key key' t hx hk,
    hx t le_rfl,mass_prefix x y key key' t hx hk]

omit [DecidableEq J] in
lemma epoch_prefix (x y : ℕ → J → ℝ) (key key' : ℕ → K) (t : ℕ)
    (hx : PrefixEq t x y) (hk : PrefixEq t key key') : epoch x key t=epoch y key' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [epoch,reset_prefix x y key key' t hx hk,
      ih (hx.mono (Nat.le_succ t)) (hk.mono (Nat.le_succ t))]

omit [Fintype R] in
lemma data_prefix {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000) (C ell ct : ℝ)
    (x y : ℕ → J → ℝ) (key key' : ℕ → K)
    (hxn : ∀ t i,0≤x t i) (hyn : ∀ t i,0≤y t i)
    (flags flags' : ℕ → J → R → Bool) (t : ℕ)
    (hx : PrefixEq t x y) (hk : PrefixEq t key key') (hf : flags t=flags' t) :
    data hδ hδu C ell ct x key hxn flags t=data hδ hδu C ell ct y key' hyn flags' t := by
  have he:=run_prefix x y key key' t hx hk
  have hw:=weight_prefix δ x y key key' t hx hk
  have hu:=ratio_prefix δ x y key key' t hx hk
  unfold data
  dsimp only
  congr 1
  · exact congrArg (fun v=> (activeSet v).Nonempty) (hx t le_rfl)
  · simp only [hx t le_rfl,hf,hw,hu]
    have hd := congrArg dominant he
    clear he
    split
    · rename_i hl
      have hh : dominant (run y key' t)=none := hd.symm.trans hl
      split
      · rfl
      · rename_i o hr
        have hf := hh.symm.trans hr
        cases hf
    · rename_i o hl
      have hh : dominant (run y key' t)=some o := hd.symm.trans hl
      split
      · rename_i hc
        split
        · rename_i hr
          have hf := hh.symm.trans hr
          cases hf
        · rename_i j hr
          have hj : o=j := Option.some.inj (hh.symm.trans hr)
          subst j
          rfl
      · rename_i hc
        split
        · rename_i hr
          have hf := hh.symm.trans hr
          cases hf
        · rfl
  · simp only [hx t le_rfl,hf]

end KServer.ScheduleCausality

end


/-! The actual held-profile simplex proportion process, tied to the filtered
child ranks. Inactive coordinates are proved harmless, and feasibility holds
for its actual state at every time, including initialization and wholesale
restarts. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.StarSimplex
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseProcess CoarseEpoch
open AllocationSchedule StarProfile
variable {Ω J R K : Type} [Fintype Ω] [Fintype J] [DecidableEq J] [Fintype R]
variable {w : Ω → ℝ}

lemma input_core {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000) (C ell ct : ℝ)
    (P : J → R → FilteredRanks w) (key : ℕ → Ω → K) (t : ℕ) (ω : Ω) :
    SimplexFamilies.core (input hδ hδu C ell ct P key t ω).data
      (input hδ hδu C ell ct P key t ω).ranks =
      fun i=>∑ r,if CoreFlags.flag (P i r) t ω then (P i r).p t ω else 0 := by
  funext i
  simp only [input,SimplexFamilies.core,data_flags,flags]

omit [Fintype Ω] in
lemma history_prefix (H : ℕ → Ω → ℕ)
    (hr : ∀ t ω z,H (t+1) ω=H (t+1) z → H t ω=H t z)
    {t s : ℕ} (hs : s≤t) {ω z : Ω} (he : H t ω=H t z) : H s ω=H s z := by
  induction t with
  | zero => exact (Nat.eq_zero_of_le_zero hs) ▸ he
  | succ t ih =>
    rcases Nat.eq_or_lt_of_le hs with h|h
    · exact h ▸ he
    · exact ih (Nat.le_of_lt_succ h) (hr t ω z he)

lemma input_adapted {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000) (C ell ct : ℝ)
    (P : J → R → FilteredRanks w) (key : ℕ → Ω → K) (H:ℕ→Ω→ℕ)
    (hH : ∀ i r t ω,(P i r).history t ω=H t ω)
    (hr : ∀ t ω z,H (t+1) ω=H (t+1) z → H t ω=H t z)
    (hkey:∀ t ω z,H t ω=H t z→key t ω=key t z) (t : ℕ) (ω z : Ω) (he:H t ω=H t z) :
    input hδ hδu C ell ct P key t ω=input hδ hδu C ell ct P key t z := by
  have hx:ScheduleCausality.PrefixEq t (vector cutoff δ P ω) (vector cutoff δ P z) :=
    fun s hs=>vector_adapted δ P H hH hr s ω z (history_prefix H hr hs he)
  have hk:ScheduleCausality.PrefixEq t (fun s=>key s ω) (fun s=>key s z) :=
    fun s hs=>hkey s ω z (history_prefix H hr hs he)
  have hh (i:J) (r:R):(P i r).history t ω=(P i r).history t z := by rw[hH,hH,he]
  have hf:flags P ω t=flags P z t := by
    funext i r
    exact CoreFlags.flag_adapted (P i r) t (hh i r)
  have hp:(fun ir:J×R=>(P ir.1 ir.2).p t ω)=(fun ir=>(P ir.1 ir.2).p t z) := by
    funext ir
    exact (P ir.1 ir.2).adapted t ω z (hh _ _)
  unfold input
  congr 1
  · exact ScheduleCausality.data_prefix hδ hδu C ell ct _ _ _ _ _ _ _ _ t hx hk hf
  · exact ScheduleCausality.epoch_prefix _ _ _ _ t hx hk

lemma proportion_adapted {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000) (C ell ct : ℝ)
    (P : J → R → FilteredRanks w) (key : ℕ → Ω → K) (H:ℕ→Ω→ℕ)
    (hH : ∀ i r t ω,(P i r).history t ω=H t ω)
    (hr : ∀ t ω z,H (t+1) ω=H (t+1) z → H t ω=H t z)
    (hkey:∀ t ω z,H t ω=H t z→key t ω=key t z) (t : ℕ) (ω z : Ω) (he:H t ω=H t z) :
    proportion hδ hδu C ell ct P key t ω=proportion hδ hδu C ell ct P key t z :=
  CausalSimplex.run_adapted C ell _ H hr (input_adapted hδ hδu C ell ct P key H hH hr hkey) t ω z he

end KServer.StarSimplex

end


/-! Literal causal side minimizers, including pre-minimization, zero deletion,
wholesale restart, and minimization on the new domain. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.CausalSide
open AdaptiveMinimization SideFamilies
attribute [local instance] Classical.propDecidable Classical.decEq
variable {J R Ω : Type} [Fintype J] [Fintype R]

lemma run_successor (c : ℝ) (d : ℕ → Ω → Input J R) (t : ℕ) (ω : Ω) :
    run c d (t+1) ω=(SideFamilies.family c).update (d (t+1) ω).data (d (t+1) ω).ranks
      (d (t+1) ω).data.D (move c (d t ω) (d (t+1) ω) (d (t+1) ω).ranks (run c d t ω)) := rfl

lemma run_adapted (c : ℝ) (d : ℕ → Ω → Input J R) (H : ℕ → Ω → ℕ)
    (href : ∀ t ω z,H (t+1) ω=H (t+1) z → H t ω=H t z)
    (hd : ∀ t ω z,H t ω=H t z → d t ω=d t z) (t : ℕ) (ω z : Ω)
    (he : H t ω=H t z) : run c d t ω=run c d t z :=
  state_adapted _ _ _ _ _ H href hd
    (fun t ω z h=>congrArg Input.ranks (hd t ω z h))
    (fun t ω z h=>congrArg (fun d:Input J R=>d.data.D) (hd t ω z h)) t ω z he

lemma ordinary_successor (c : ℝ) (d : ℕ → Ω → Input J R) (t : ℕ) (ω : Ω)
    (he : (d t ω).epoch=(d (t+1) ω).epoch)
    (hW : (d t ω).data.W=(d (t+1) ω).data.W) :
    run c d (t+1) ω=SideFamilies.step c (d t ω).data (d (t+1) ω).data
      (d (t+1) ω).ranks (run c d t ω) := by
  rw [run_successor,move,ite_eq_left ⟨he,hW⟩]
  rfl

lemma ordinary_payment (d : ℕ → Ω → Input J R) {M : ℝ} (t : ℕ) (ω : Ω)
    (he : (d t ω).epoch=(d (t+1) ω).epoch)
    (hWW : (d t ω).data.W=(d (t+1) ω).data.W)
    (hb : 1≤(d t ω).data.b) (hD : 0≤(d (t+1) ω).data.D)
    (hM : ∀ i∈(d t ω).data.active,(d t ω).data.b+(d t ω).data.θ i≤M)
    (hW : 2*M<(d t ω).data.W) (hp : ∀ ir,0≤(d (t+1) ω).ranks ir) :
    let old:=(d t ω).data
    let new:=(d (t+1) ω).data
    let p:=(d (t+1) ω).ranks
    let a:=run (8*M) d t ω
    new.D*ChangingDomains.variation (run (8*M) d (t+1) ω) a ≤
      (SideFamilies.family (8*M)).value old p a-
      (SideFamilies.family (8*M)).value new p (run (8*M) d (t+1) ω)+
      |(SideFamilies.family (8*M)).value (prepareData old new) p a-
        (SideFamilies.family (8*M)).value old p a|+
      |(SideFamilies.family (8*M)).value new p (SideFamilies.transport (8*M) old new p a)-
        (SideFamilies.family (8*M)).value (prepareData old new) p
          (SideFamilies.transport (8*M) old new p a)| := by
  dsimp only
  rw [ordinary_successor _ _ _ _ he hWW]
  exact step_payment _ _ hb hD hM hW _ hp _ (run_mem _ _ _ _) hWW

end KServer.CausalSide

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Caps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual rankwise caps used by the star construction: core flags and
both endpoint trackers run for the full history, not only at output times. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TrackedCaps
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoreFlags
variable {Ω R : Type} [Fintype Ω] [Fintype R] {w : Ω → ℝ}

lemma cap_eq (P : R → FilteredRanks w) (ξ a κ : ℝ) (t : ℕ) (ω : Ω) :
    cap P ξ a κ t ω=count P t ω+κ*estimate P ξ a t ω := by
  unfold cap count estimate
  rw [mul_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro r _
  unfold FineCaps.capTerm
  split_ifs <;> ring

omit [Fintype R] in
lemma endpoint_adapted (P : FilteredRanks w) (ξ z : ℝ) (t : ℕ) {ω ρ : Ω}
    (h : P.history t ω=P.history t ρ) :
    FineCaps.estimate ξ z P t ω=FineCaps.estimate ξ z P t ρ := by
  unfold FineCaps.estimate
  congr 1
  exact held_adapted _ P t ω ρ h

end KServer.TrackedCaps

end


/-! Literal side process at a filtered star. The scale is the independently
running coarse tracker of the marked child's noncore rank values, as in
( dominant-scale-definition ), not a retrospectively selected comparator. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.StarSide
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseProcess CoarseEpoch AllocationSchedule StarProfile
variable {Ω J R K : Type} [Fintype Ω] [Fintype J] [DecidableEq J] [Fintype R]
variable {w : Ω → ℝ}

lemma coarseFlex_adapted (δ : ℝ) (P : R → FilteredRanks w) (H : ℕ → Ω → ℕ)
    (hH : ∀ r t ω,(P r).history t ω=H t ω) (t : ℕ) (ω z : Ω) (he : H t ω=H t z) :
    coarseFlex δ P t ω=coarseFlex δ P t z := by
  apply sum_congr rfl
  intro r _
  have hh:(P r).history t ω=(P r).history t z := by rw[hH,hH,he]
  rw [CoreFlags.flag_adapted (P r) t hh,TrackedCaps.endpoint_adapted (P r) δ 0 t hh]

lemma input_adapted {cw ell : ℝ} (hcw : 0 < cw) (hel : 0<ell) (δ : ℝ)
    (P : J → R → FilteredRanks w) (key : ℕ → Ω → K) (b : ℕ → Ω → ℝ) (H:ℕ→Ω→ℕ)
    (hH : ∀ i r t ω,(P i r).history t ω=H t ω)
    (hr : ∀ t ω z,H (t+1) ω=H (t+1) z → H t ω=H t z)
    (hkey:∀ t ω z,H t ω=H t z→key t ω=key t z)
    (hb:∀ t ω z,H t ω=H t z→b t ω=b t z) (t : ℕ) (ω z : Ω) (he:H t ω=H t z) :
    input hcw hel δ P key b t ω=input hcw hel δ P key b t z := by
  have hx:ScheduleCausality.PrefixEq t (vector cutoff δ P ω) (vector cutoff δ P z) :=
    fun s hs=>vector_adapted δ P H hH hr s ω z (StarSimplex.history_prefix H hr hs he)
  have hk:ScheduleCausality.PrefixEq t (fun s=>key s ω) (fun s=>key s z) :=
    fun s hs=>hkey s ω z (StarSimplex.history_prefix H hr hs he)
  have hm:mark δ P key t ω=mark δ P key t z :=
    congrArg EpochSchedule.dominant (ScheduleCausality.run_prefix _ _ _ _ t hx hk)
  have hA:sides δ P key t ω=sides δ P key t z := by simp only [sides,hm,hx t le_rfl]
  have hD:scale δ P key t ω=scale δ P key t z := by
    simp only [scale,hm]
    split
    · rfl
    · exact coarseFlex_adapted δ _ H (hH _) t ω z he
  have hf:sideFlags δ P key t ω=sideFlags δ P key t z := by
    funext i r
    have hh:(P i r).history t ω=(P i r).history t z := by rw[hH,hH,he]
    simp only [sideFlags,hA,CoreFlags.flag_adapted (P i r) t hh]
  have hh:logs δ P key t ω=logs δ P key t z := by
    funext i
    exact congrArg (fun h:J→ℝ=>max 1 (h i)) (ScheduleCausality.weight_prefix δ _ _ _ _ t hx hk)
  have hp:(fun ir:J×R=>(P ir.1 ir.2).p t ω)=(fun ir=>(P ir.1 ir.2).p t z) := by
    funext ir
    exact (P ir.1 ir.2).adapted t ω z (by rw[hH,hH,he])
  unfold input SideFamilies.fromLog
  simp only [hA,hf,hD,hh,hp,hb t ω z he,ScheduleCausality.epoch_prefix _ _ _ _ t hx hk]

lemma proportion_adapted {cw ell : ℝ} (hcw : 0 < cw) (hel : 0<ell) (δ : ℝ)
    (P : J → R → FilteredRanks w) (key : ℕ → Ω → K) (b : ℕ → Ω → ℝ) (H:ℕ→Ω→ℕ)
    (hH : ∀ i r t ω,(P i r).history t ω=H t ω)
    (hr : ∀ t ω z,H (t+1) ω=H (t+1) z → H t ω=H t z)
    (hkey:∀ t ω z,H t ω=H t z→key t ω=key t z)
    (hb:∀ t ω z,H t ω=H t z→b t ω=b t z) (t : ℕ) (ω z : Ω) (he:H t ω=H t z) :
    proportion hcw hel δ P key b t ω=proportion hcw hel δ P key b t z :=
  CausalSide.run_adapted 40 _ H hr (input_adapted hcw hel δ P key b H hH hr hkey hb) t ω z he

end KServer.StarSide

end


/-! The literal held dominant noncore scale is uniformly comparable to the
current parameterized flex mass; zeros coincide without a positive-mass
assumption. This is (dominant-scale-definition) / (D-comparison) in §03. -/


/-! One fixed absolute choice in the order required by §05; neither the
separation ratio nor any finite input parameter enters these constants. -/


/-! Endpoint-only fine caps with the actual held parent parameter. These
estimates are run for every rank and time, not just during output epochs. -/


/-! Binding the local numerical choices to the literal star processes. The
only input relation is conservation/superadditivity of the parent's rank size. -/


/-! Scalar constant choices used when the genuine minimizer proportions are
converted to allocations. All constants are the fixed absolute choices, not
parameters fitted to the finite law. -/


/-! The actual cap vector, lower envelopes, and single dominant error used by
§05. No aggregate cap or parameter inequalities are assumed. -/

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_OutputRules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! Rule I applied to the actual scheduled proportions and caps. Its only
external numeric input is a parent allocation covering the sum of the child
lower envelopes at the parent's parameter (the rank superadditivity premise). -/


/-! Literal side minimizer bounds at the fixed absolute constants. -/


/-! Side slack for the actual held logarithms, including zero and empty side
mass. This is a proved inequality, not an assumed output feasibility interface. -/


/-! The residual Rule II formula and its feasibility for the actual side
minimizer and marked flex scale. Empty side sets require no separate assumption. -/


/-! Literal two-regime rule schedule of §05. The rule is decided without
using the parent allocation. Ordinary switches earn potential drops; the
filtering increment is retained on every history, before the tests. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.RuleSchedule
attribute [local instance] Classical.propDecidable

lemma value_nonneg {S D : ℝ} (hS : 0≤S) (hD : 0≤D) (marked rule : Bool) :
    0≤value marked rule S D := by
  cases marked <;> cases rule <;> simp [value,hS,hD]
lemma value_upper {S D : ℝ} (hS : 0≤S) (hD : 0≤D) (marked rule : Bool) :
    value marked rule S D≤S+D := by
  cases marked <;> cases rule <;> simp only [value,Bool.false_eq_true,ite_true,ite_false] <;> linarith
lemma charge_nonneg {S D : ℝ} (hS : 0≤S) (hD : 0≤D) (marked reset old : Bool) :
    0 ≤ charge marked reset old S D := by
  unfold charge
  split_ifs <;> first | assumption | rfl

lemma ordinary_credit (S D : ℝ) (marked old : Bool) :
    charge marked false old S D/2+value marked (step marked false S D old) S D≤
      value marked old S D := by
  cases marked with
  | false => simp [charge,value]
  | true =>
    cases old with
    | false =>
      by_cases h:S<D/2
      · simp [charge,value,step,update,choose,h]
        linarith
      · simp [charge,value,step,update,choose,h]
    | true =>
      by_cases h:S≤2*D
      · simp [charge,value,step,update,h]
      · simp [charge,value,step,update,h]
        linarith

variable {Ω R : Type*} [Fintype Ω] [Fintype R]
open RankTracking

omit [Fintype Ω] in
lemma input_difference (marked rule : Bool) (f : R → Bool) (p q : R → ℝ) (D : ℝ) :
    value marked rule (core f p) D-value marked rule (core f q) D=
      ∑ r,coefficient marked rule f r*(p r-q r) := by
  cases marked <;> cases rule <;> simp [value,core,coefficient,←sum_sub_distrib]
  apply sum_congr rfl
  intro r _
  split_ifs <;> simp

omit [Fintype Ω] in
lemma core_nonneg (f : R → Bool) {p : R → ℝ} (hp : ∀ r,0≤p r) : 0 ≤ core f p := by
  exact sum_nonneg fun r _=>by split_ifs; exact hp r; rfl

omit [Fintype Ω] in
lemma input_lipschitz (marked rule : Bool) (f : R → Bool) (p q : R → ℝ) (D : ℝ) :
    |value marked rule (core f p) D-value marked rule (core f q) D|≤∑ r,|p r-q r| := by
  rw [input_difference]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro r _
  unfold coefficient
  split_ifs <;> simp

omit [Fintype Ω] in
lemma data_change (marked rule : Bool) (f g : R → Bool) (p : R → ℝ) {D E : ℝ}
    (hp : ∀ r,p r∈Set.Icc 0 1) :
    value marked rule (core g p) E-value marked rule (core f p) D≤
      (∑ r,if f r=g r then (0:ℝ) else 1)+|E-D| := by
  have hn:0≤∑ r,if f r=g r then (0:ℝ) else 1:=sum_nonneg fun _ _=>by positivity
  have hc:core g p-core f p≤∑ r,if f r=g r then (0:ℝ) else 1 := by
    rw [core,core,←sum_sub_distrib]
    apply sum_le_sum
    intro r _
    cases hf:f r <;> cases hg:g r <;> simp <;> linarith [(hp r).1,(hp r).2]
  cases marked <;> cases rule <;> simp only [value,Bool.false_eq_true,ite_true,ite_false] <;>
    linarith [abs_nonneg (E-D),le_abs_self (E-D)]

omit [Fintype Ω] in
lemma run_congr (marked reset : ℕ → Ω → Bool) (S D : ℕ → Ω → ℝ) (t : ℕ) (ω z : Ω)
    (hm : ∀ s≤t,marked s ω=marked s z) (hr : ∀ s≤t,reset s ω=reset s z)
    (hS : ∀ s≤t,S s ω=S s z) (hD : ∀ s≤t,D s ω=D s z) :
    run marked reset S D t ω=run marked reset S D t z := by
  induction t with
  | zero => simp only [run,hm 0 le_rfl,hS 0 le_rfl,hD 0 le_rfl]
  | succ t ih =>
    simp only [run,hm _ le_rfl,hr _ le_rfl,hS _ le_rfl,hD _ le_rfl]
    rw [ih (fun s hs=>hm s (hs.trans (Nat.le_succ t)))
      (fun s hs=>hr s (hs.trans (Nat.le_succ t)))
      (fun s hs=>hS s (hs.trans (Nat.le_succ t)))
      (fun s hs=>hD s (hs.trans (Nat.le_succ t)))]

end KServer.RuleSchedule

end


/-! The literal causal-regime output of a star: true hysteresis, both formulas,
and feasibility, uniformly in empty and vanishing-core cases. -/

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_AllocationMovement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree-independent movement algebra, allowing a zero simplex on an empty
active set and using the original fixed universe of star coordinates. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.OutputDynamics
variable {J:Type*} [Fintype J]
attribute [local instance] Classical.propDecidable Classical.decEq

lemma holesI_movement_subprob {R R':ℝ} {a a':J→ℝ} (hR':0≤R')
    (ha:∀ i,0≤a i) (hsa:(∑ i,a i)≤1):
    variation (holesI R' a') (holesI R a)≤|R'-R|+R'*variation a' a:=by
  calc _≤∑ i,(R'*|a' i-a i|+|R'-R| *a i):=by
        apply sum_le_sum
        intro i _
        change |R'*a' i-R*a i|≤_
        calc _=|R'*(a' i-a i)+(R'-R)*a i|:=by congr 1;ring
          _≤|R'*(a' i-a i)|+|(R'-R)*a i|:=abs_add_le _ _
          _=_:=by rw [abs_mul,abs_mul,abs_of_nonneg hR',abs_of_nonneg (ha i)]
      _=R'*variation a' a+|R'-R| *(∑ i,a i):=by
        rw [sum_add_distrib,←mul_sum,←mul_sum];rfl
      _≤_:=by nlinarith [mul_le_mul_of_nonneg_left hsa (abs_nonneg (R'-R))]

lemma outputI_movement_subprob {d d' a a':J→ℝ} {q q':ℝ}
    (ha:∀ i,0≤a i) (hsa:(∑ i,a i)≤1):
    variation (outputI d' q' a') (outputI d q a)≤
      |q'-q|+2*variation d' d+excess d' q'*variation a' a:=by
  have ho:=output_from_holes_movement d d' (holesI (excess d q) a) (holesI (excess d' q') a')
  have hh:=holesI_movement_subprob (R:=excess d q) (a':=a') (excess_nonneg d' q') ha hsa
  have he:=excess_lipschitz d' d q' q
  change variation (outputI d' q' a') (outputI d q a)≤_ at ho
  linarith

lemma variation_divide (o:J) (x y:J→ℝ):
    variation x y=|x o-y o|+∑ i∈univ.erase o,|x i-y i|:=by
  rw [variation,←sum_erase_add _ _ (mem_univ o),add_comm]

lemma restricted_variation_le (o:J) (x y:J→ℝ):
    (∑ i∈univ.erase o,|x i-y i|)≤variation x y:=by
  rw [variation_divide o]
  linarith [abs_nonneg (x o-y o)]

lemma residual_movement (o:J) {d d' w w':J→ℝ} {q q' D D' Cw:ℝ}
    (hD':0≤D') (hw:∀ i,0≤w i) (hws:(∑ i,w i)≤Cw):
    variation (residual o d' q' D' w') (residual o d q D w)≤
      |q'-q|+2*variation d' d+2*D'*variation w' w+2*Cw*|D'-D|:=by
  let s:J→ℝ:=fun i=>d i-D*w i
  let s':J→ℝ:=fun i=>d' i-D'*w' i
  have hscaled:=scaled_movement (D:=D) hD' hw hws (w':=w')
  have hside:=output_from_holes_movement d d' (fun i=>D*w i) (fun i=>D'*w' i)
  change variation s' s≤_ at hside
  have hdom: |min (d' o) (q'-∑ j∈univ.erase o,s' j)-min (d o) (q-∑ j∈univ.erase o,s j)|≤
      |d' o-d o|+|q'-q|+∑ j∈univ.erase o,|s' j-s j|:=by
    have hh: |min (d' o) (q'-∑ j∈univ.erase o,s' j)-min (d o) (q-∑ j∈univ.erase o,s j)|≤
        |d' o-d o|+|(q'-∑ j∈univ.erase o,s' j)-(q-∑ j∈univ.erase o,s j)|:=by
      apply (abs_min_sub_min_le_max _ _ _ _).trans
      exact max_le (by linarith [abs_nonneg ((q'-∑ j∈univ.erase o,s' j)-(q-∑ j∈univ.erase o,s j))])
        (by linarith [abs_nonneg (d' o-d o)])
    have he:|(q'-∑ j∈univ.erase o,s' j)-(q-∑ j∈univ.erase o,s j)|≤
        |q'-q|+∑ j∈univ.erase o,|s' j-s j|:=by
      calc _=|(q'-q)-((∑ j∈univ.erase o,s' j)-∑ j∈univ.erase o,s j)|:=by congr 1;ring
        _≤|q'-q|+|((∑ j∈univ.erase o,s' j)-∑ j∈univ.erase o,s j)|:=abs_sub _ _
        _≤_:=by rw [←sum_sub_distrib]
                exact add_le_add le_rfl (abs_sum_le_sum_abs (fun j:J => s' j-s j) (univ.erase o))
    linarith
  have hs:∑ i∈univ.erase o,|residual o d' q' D' w' i-residual o d q D w i|=
      ∑ i∈univ.erase o,|s' i-s i|:=by
    apply sum_congr rfl
    intro i hi
    simp only [residual,ite_eq_right (mem_erase.mp hi).1,s,s']
  rw [variation_divide o,hs]
  simp only [residual,ite_true]
  change |min (d' o) (q'-∑ j∈univ.erase o,s' j)-min (d o) (q-∑ j∈univ.erase o,s j)|+_≤_
  have hsum: (∑ i∈univ.erase o,|s' i-s i|)≤
      (∑ i∈univ.erase o,|d' i-d i|)+D'*variation w' w+Cw*|D'-D|:=by
    have hp: (∑ i∈univ.erase o,|s' i-s i|)≤
        (∑ i∈univ.erase o,|d' i-d i|)+(∑ i∈univ.erase o,|D'*w' i-D*w i|):=by
      rw [←sum_add_distrib]
      apply sum_le_sum
      intro i _
      dsimp only [s,s']
      calc _=|(d' i-d i)-(D'*w' i-D*w i)|:=by congr 1;ring
        _≤_:=abs_sub _ _
    linarith [restricted_variation_le o (fun i=>D'*w' i) (fun i=>D*w i)]
  rw [variation_divide o d' d]
  linarith [abs_nonneg (d' o-d o)]
end KServer.OutputDynamics

end


/-! Literal residual-hole mass and switch estimates on the fixed star universe.
These bounds also cover empty side sets and zero active masses. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.OutputDynamics
attribute [local instance] Classical.propDecidable Classical.decEq
variable {J:Type*} [Fintype J]

lemma residualHoles_nonneg (o:J) (d:J→ℝ) (q:ℝ) {D:ℝ} {w:J→ℝ}
    (hD:0≤D) (hw:∀ i,0≤w i):∀ i,0 ≤ residualHoles o d q D w i:=by
  intro i
  by_cases hi:i=o
  · subst i
    simp only [residualHoles,residual,ite_true]
    exact sub_nonneg.mpr (min_le_left _ _)
  · simp only [residualHoles,residual,ite_eq_right hi,sub_sub_cancel]
    exact mul_nonneg hD (hw i)

lemma residualHoles_mass (o:J) (d:J→ℝ) (q:ℝ) {D Cw:ℝ} {w:J→ℝ}
    (hD:0≤D) (hw:∀ i,0≤w i) (hws:(∑ i,w i)≤Cw):
    (∑ i,residualHoles o d q D w i)≤excess d q+Cw*D:=by
  have he: (∑ i,d i)-q≤excess d q:=le_max_left _ _
  have hn:=excess_nonneg d q
  have hside:0≤D*(∑ i∈univ.erase o,w i):=mul_nonneg hD (sum_nonneg fun i _=>hw i)
  have hd:residualHoles o d q D w o≤excess d q:=by
    simp only [residualHoles,residual,ite_true]
    have hs:(∑ i,d i)=(∑ i∈univ.erase o,d i)+d o:=
      (sum_erase_add univ d (mem_univ o)).symm
    rw [hs] at he
    have hx:d o-excess d q≤ min (d o) (q-∑ j∈univ.erase o,(d j-D*w j)):=by
      apply le_min
      · linarith
      · rw [sum_sub_distrib,←mul_sum]
        linarith
    linarith
  have hs:(∑ i∈univ.erase o,residualHoles o d q D w i)=D*(∑ i∈univ.erase o,w i):=by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    simp only [residualHoles,residual,ite_eq_right (mem_erase.mp hi).1,sub_sub_cancel]
  have hsub:(∑ i∈univ.erase o,w i)≤Cw:=by
    apply le_trans _ hws
    exact sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun i _ _=>hw i)
  rw [←sum_erase_add _ _ (mem_univ o),hs]
  nlinarith [mul_le_mul_of_nonneg_left hsub hD]

lemma residual_eq_sub_holes (o:J) (d:J→ℝ) (q D:ℝ) (w:J→ℝ):
    residual o d q D w=(fun i=>d i-residualHoles o d q D w i):=by
  funext i
  dsimp only [residualHoles]
  ring

lemma holesI_mass_subprob {R:ℝ} {a:J→ℝ} (hR:0≤R) (hsa:(∑ i,a i)≤1):
    (∑ i,holesI R a i)≤R:=by
  simp only [holesI,←mul_sum]
  nlinarith [mul_le_mul_of_nonneg_left hsa hR]

lemma downcross_fixed (o:J) {d d' a w':J→ℝ} {q q' D':ℝ}
    (hD':0≤D') (ha:∀ i,0≤a i) (hsa:(∑ i,a i)≤1)
    (hw':∀ i,0≤w' i) (hws:(∑ i,w' i)≤16) (hr:excess d' q'≤10*D'):
    variation (residual o d' q' D' w') (outputI d q a)≤
      |q'-q|+2*variation d' d+36*D':=by
  have hv:=variation_le_mass (holesI_nonneg (excess_nonneg d q) ha)
    (residualHoles_nonneg o d' q' hD' hw')
  have hm:=holesI_mass_subprob (excess_nonneg d q) hsa
  have hm':=residualHoles_mass o d' q' hD' hw' hws
  have he:=excess_lipschitz d' d q' q
  have ho:=output_from_holes_movement d d' (holesI (excess d q) a) (residualHoles o d' q' D' w')
  rw [←residual_eq_sub_holes] at ho
  change variation (residual o d' q' D' w') (outputI d q a)≤_ at ho
  linarith [neg_le_abs (excess d' q'-excess d q)]

lemma upcross_fixed (o:J) {d d' a' w:J→ℝ} {q q' D D' S':ℝ}
    (hD:0≤D) (ha':∀ i,0≤a' i) (hsa:(∑ i,a' i)≤1)
    (hw:∀ i,0≤w i) (hws:(∑ i,w i)≤16)
    (hr:excess d' q'≤10*S') (hreg:D'≤S'/2):
    variation (outputI d' q' a') (residual o d q D w)≤
      |q'-q|+2*variation d' d+28*S'+16*|D'-D|:=by
  have hv:=variation_le_mass (residualHoles_nonneg o d q hD hw)
    (holesI_nonneg (excess_nonneg d' q') ha')
  have hm:=residualHoles_mass o d q hD hw hws
  have hm':=holesI_mass_subprob (excess_nonneg d' q') hsa
  have he:=excess_lipschitz d' d q' q
  have ho:=output_from_holes_movement d d' (residualHoles o d q D w) (holesI (excess d' q') a')
  rw [←residual_eq_sub_holes] at ho
  change variation (outputI d' q' a') (residual o d q D w)≤_ at ho
  linarith [neg_le_abs (excess d' q'-excess d q),neg_le_abs (D'-D)]
end KServer.OutputDynamics

end


/-! Same-rule and full crossing movement bounds for the actual output,
with one unit of parent variation. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualOutput
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar
open OutputDynamics
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

lemma alpha_subprob (k:ℝ) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (t:ℕ) (ω:Ω):
    (∑ i,α k P Q t ω i)≤1:=by
  have ha:=(α_mem k P Q t ω).2.1
  split_ifs at ha <;> linarith

lemma error_le_T {k:ℝ} (hk:1≤ k) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (t:ℕ) (ω:Ω) (hq:size Q t ω≤ k):e k P Q t ω≤ T k P Q t ω:=by
  have hel:1≤ ActualCaps.ell k:=by
    have hh:=Real.log_nonneg (show 1≤ k+1 by linarith)
    unfold ActualCaps.ell
    linarith
  have heb:eb≤ ActualCaps.ell k:=by
    have he:eb≤1:=by norm_num [eb,cb]
    exact he.trans hel
  have he:eb/ActualCaps.ell k≤1:=(div_le_one (ActualCaps.ell_pos hk)).mpr heb
  exact (e_bounds hk P Q t ω hq).2.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right he (T_nonneg hk P Q t ω hq))

lemma actual_excess {k:ℝ} (hk:1≤ k) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (t:ℕ) (ω:Ω) (hq:size Q t ω≤ k)
    {q:ℝ} (hp:(∑ i,(n P t ω i-β k Q t ω*B P t ω i+f k P Q t ω i))≤ q):
    excess (d k P Q t ω) q≤4*S P t ω+T k P Q t ω:=by
  have hb:=beta_range hk Q t ω hq
  have he:=e_bounds hk P Q t ω hq
  have hh:=hole_bound hp (error_sum hk P Q hs t ω hq) (by linarith : 0≤β k Q t ω) he.1
    (fun i=> TrackedCaps.core_nonneg (P i) t ω)
  change excess (d k P Q t ω) q≤β k Q t ω*S P t ω+e k P Q t ω at hh
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_right hb.2 (S_nonneg P t ω))
    (error_le_T hk P Q t ω hq))

lemma excess_ruleI {k:ℝ} (hk:1≤ k) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (t:ℕ) (ω:Ω) (hq:size Q t ω≤ k)
    {q:ℝ} (hp:(∑ i,(n P t ω i-β k Q t ω*B P t ω i+f k P Q t ω i))≤ q)
    (hr:∀ o,mark P Q t ω=some o→ D P Q t ω/2≤ S P t ω):
    excess (d k P Q t ω) q≤10*S P t ω:=by
  have hh:=actual_excess hk P Q hs t ω hq hp
  have ht:=ruleI_T hk P Q t ω hq hr
  linarith [S_nonneg P t ω]

lemma excess_down {k:ℝ} (hk:1≤ k) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (t:ℕ) (ω:Ω) (hq:size Q t ω≤ k)
    {q:ℝ} (hp:(∑ i,(n P t ω i-β k Q t ω*B P t ω i+f k P Q t ω i))≤ q)
    (hr:S P t ω≤ D P Q t ω/2):excess (d k P Q t ω) q≤10*D P Q t ω:=by
  linarith [actual_excess hk P Q hs t ω hq hp,(DT_compare hk P Q t ω hq).1,D_nonneg P Q t ω]

lemma outI_movement {k:ℝ} (hk:1≤ k) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (t:ℕ) (ω:Ω) (hq:size Q (t+1) ω≤ k)
    (q q':ℝ) (hp:(∑ i,(n P (t+1) ω i-β k Q (t+1) ω*B P (t+1) ω i+f k P Q (t+1) ω i))≤ q')
    (hr:∀ o,mark P Q (t+1) ω=some o→ D P Q (t+1) ω/2≤ S P (t+1) ω):
    variation (outI k P Q (t+1) ω q') (outI k P Q t ω q)≤
      |q'-q|+2*variation (d k P Q (t+1) ω) (d k P Q t ω)+
      10*S P (t+1) ω*variation (α k P Q (t+1) ω) (α k P Q t ω):=by
  exact (outputI_movement_subprob (α_mem k P Q t ω).1 (alpha_subprob k P Q t ω)).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right (excess_ruleI hk P Q hs (t+1) ω hq hp hr)
      (variation_nonneg _ _)))

lemma outII_movement {k:ℝ} (hk:1≤ k) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (t:ℕ) (ω:Ω) (q q':ℝ) (o:J):
    variation (outII hk P Q (t+1) ω o q') (outII hk P Q t ω o q)≤
      |q'-q|+2*variation (d k P Q (t+1) ω) (d k P Q t ω)+
      2*D P Q (t+1) ω*variation (side hk P Q (t+1) ω) (side hk P Q t ω)+
      32*|D P Q (t+1) ω-D P Q t ω|:=by
  have hh:=residual_movement o (q:=q) (q':=q') (d:=d k P Q t ω) (d':=d k P Q (t+1) ω)
    (w':=side hk P Q (t+1) ω) (D:=D P Q t ω) (D_nonneg P Q (t+1) ω) (side_mem hk P Q t ω).1 (side_mem hk P Q t ω).2.1
  change variation (outII hk P Q (t+1) ω o q') (outII hk P Q t ω o q)≤_ at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma out_downcross {k:ℝ} (hk:1≤ k) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (t:ℕ) (ω:Ω) (hq:size Q (t+1) ω≤ k)
    (q q':ℝ) (o:J)
    (hp:(∑ i,(n P (t+1) ω i-β k Q (t+1) ω*B P (t+1) ω i+f k P Q (t+1) ω i))≤ q')
    (hr:S P (t+1) ω≤ D P Q (t+1) ω/2):
    variation (outII hk P Q (t+1) ω o q') (outI k P Q t ω q)≤
      |q'-q|+2*variation (d k P Q (t+1) ω) (d k P Q t ω)+36*D P Q (t+1) ω:=by
  exact downcross_fixed o (D_nonneg P Q (t+1) ω) (α_mem k P Q t ω).1 (alpha_subprob k P Q t ω)
    (side_mem hk P Q (t+1) ω).1 (side_mem hk P Q (t+1) ω).2.1 (excess_down hk P Q hs (t+1) ω hq hp hr)

lemma out_upcross {k:ℝ} (hk:1≤ k) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (t:ℕ) (ω:Ω) (hq:size Q (t+1) ω≤ k)
    (q q':ℝ) (o:J)
    (hp:(∑ i,(n P (t+1) ω i-β k Q (t+1) ω*B P (t+1) ω i+f k P Q (t+1) ω i))≤ q')
    (hr:2*D P Q (t+1) ω≤ S P (t+1) ω):
    variation (outI k P Q (t+1) ω q') (outII hk P Q t ω o q)≤
      |q'-q|+2*variation (d k P Q (t+1) ω) (d k P Q t ω)+28*S P (t+1) ω+
      16*|D P Q (t+1) ω-D P Q t ω|:=by
  exact upcross_fixed o (D_nonneg P Q t ω) (α_mem k P Q (t+1) ω).1 (alpha_subprob k P Q (t+1) ω)
    (side_mem hk P Q t ω).1 (side_mem hk P Q t ω).2.1
    (excess_ruleI hk P Q hs (t+1) ω hq hp (fun _ _=> by linarith [D_nonneg P Q (t+1) ω]))
    (by linarith)

end KServer.ActualOutput

end


/-! Frozen-history affine payment with bounds on the actual held parameters.
No bound on fictitious off-schedule parameters is needed; the signed edit term
still has to be paid by the concrete coarse schedule. -/


/-! Dimension-free affine input slope on the actual held simplex parameters. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ScheduledSlope
attribute [local instance] Classical.propDecidable
open AllocationSchedule EpochSchedule SimplexFamilies
variable {J R K : Type} [Fintype J] [DecidableEq J] [Fintype R]

omit [Fintype R] in
lemma coefficient_bound {δ C ell ct : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (hC : 0≤C) (hel : 0<ell) (hct : 0 ≤ ct)
    (x : ℕ → J → ℝ) (key : ℕ → K) (hx : ∀ t i,0≤x t i)
    (flags : ℕ → J → R → Bool) (t : ℕ)
    (hmax : ∀ i,ct*weight δ x key t i/ell≤1)
    (a : J → ℝ) (ha : a∈ChangingDomains.simplex (activeSet (x t))) (ir : J×R) :
    |coefficient C ell (data hδ hδu C ell ct x key hx flags t) a ir|≤13*C*ell := by
  have heta : ∀ i,ct*weight δ x key t i/ell∈Set.Icc 0 1 := fun i=>
    ⟨div_nonneg (mul_nonneg hct (weight_nonneg δ x key hx t i)) hel.le,hmax i⟩
  have hnn : 0≤13*C*ell := by positivity
  unfold data
  dsimp only
  split
  · split
    · rename_i hn
      have h:=regular_coefficient_bound (activeSet (x t)) (flags t) (weight δ x key t)
        (fun i=>ct*weight δ x key t i/ell)
        (fun i=>weight_regular_one δ x key t i (by simp [hn])) heta hC hel.le ha ir
      exact h.trans (by nlinarith [mul_nonneg hC hel.le])
    · split
      · exact marked_coefficient_bound _ _ _ _ _ _ _ _ heta hC hel.le ha ir
      · simpa only [zeroData,coefficient,ite_true,abs_zero] using hnn
  · simpa only [zeroData,coefficient,ite_true,abs_zero] using hnn

open RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile
variable {Ω : Type} [Fintype Ω] {w : Ω → ℝ}

lemma actual_bound {δ C ct k : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (hC : 0≤C) (hct : 0 ≤ ct) (hctu : ct*20002≤1) (hk : 1≤k)
    (P : J → R → FilteredRanks w) (key : ℕ → Ω → K)
    (hs : ∀ t ω,(∑ i,size (P i) t ω)≤k) (t : ℕ) (ω : Ω)
    (a : J → ℝ) (ha : a∈ChangingDomains.simplex (activeSet (vector cutoff δ P ω t))) (ir : J×R) :
    |coefficient C (1+Real.log (k+1))
      (StarSimplex.input hδ hδu C (1+Real.log (k+1)) ct P key t ω).data a ir|≤
      13*C*(1+Real.log (k+1)) := by
  have hel : 0<1+Real.log (k+1) := by
    have h:=Real.log_nonneg (show 1≤k+1 by linarith)
    linarith
  apply coefficient_bound hδ hδu hC hel hct _ _ (vector_nonneg cutoff δ P ω) _ t _ a ha ir
  intro i
  apply (div_le_iff₀ hel).mpr
  have h:=weight_upper hδ hδu hk (vector cutoff δ P ω) (fun s=>key s ω)
    (vector_nonneg cutoff δ P ω) (fun s=>vector_total hδ hδu P s ω (hs s ω))
    (fun s i hi=>vector_floor hδ hδu P s ω i hi) t i
  have hmul:=mul_le_mul_of_nonneg_left h hct
  have hmul2:=mul_le_mul_of_nonneg_right hctu hel.le
  nlinarith

end KServer.ScheduledSlope

end


/-! Selective parameter charges on the actual size schedule.  In particular a
regular-component edit is charged only to its changed coordinate, and the
marked component is charged to side mass, never to the dominant child. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ScheduleEdits
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseProcess CoarseEpoch AllocationSchedule StarProfile
variable {Ω J R K : Type} [Fintype Ω] [Fintype J] [DecidableEq J] [Fintype R]
variable {w : Ω → ℝ}

omit [DecidableEq J] in
lemma ordinary_reference (x : ℕ→J→ℝ) (key : ℕ→K) (t : ℕ)
    (he : epoch x key t=epoch x key (t+1)) :
    (EpochSchedule.run x key (t+1)).reference=(EpochSchedule.run x key t).reference := by
  have hn:=(epoch_same_iff x key t).mp he
  change ¬EpochSchedule.reset _ _ _ _ _ at hn
  simp only [EpochSchedule.run,EpochSchedule.update,ite_eq_right hn]

omit [DecidableEq J] in
lemma ordinary_mass (x : ℕ→J→ℝ) (key : ℕ→K) (t : ℕ)
    (he : epoch x key t=epoch x key (t+1)) : mass x key (t+1)=mass x key t :=
  congrArg EpochSchedule.total (ordinary_reference x key t he)

omit [DecidableEq J] in
lemma ordinary_mark (x : ℕ→J→ℝ) (key : ℕ→K) (t : ℕ)
    (he : epoch x key t=epoch x key (t+1)) :
    EpochSchedule.dominant (EpochSchedule.run x key (t+1))=
      EpochSchedule.dominant (EpochSchedule.run x key t) :=
  CoarseSide.mark_unchanged ((epoch_same_iff x key t).mp he)

lemma ordinary_weight (δ : ℝ) (x : ℕ→J→ℝ) (key : ℕ→K) (t : ℕ)
    (he : epoch x key t=epoch x key (t+1)) (i : J)
    (hi : EpochSchedule.dominant (EpochSchedule.run x key t)≠some i)
    (hx : x t i=x (t+1) i) : weight δ x key t i=weight δ x key (t+1) i := by
  simp only [weight,ordinary_mark x key t he,ite_eq_right hi,ordinary_mass x key t he,hx]

lemma count_bound {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (P : R→FilteredRanks w) (t : ℕ) (ω : Ω) :
    TrackedCaps.count P t ω≤40*(active cutoff δ P ω t).value := by
  by_cases hp:0<(active cutoff δ P ω t).value
  · have hc:=(TrackedCaps.domination P (by norm_num : (0:ℝ)∈Set.Icc 0 (1/100:ℝ)) t ω)
    have hn:=TrackedCaps.flex_nonneg P (by norm_num : (0:ℝ)∈Set.Icc 0 (1/100:ℝ)) t ω
    have ha:=(active_accuracy (by norm_num [cutoff] : 0 < cutoff) hδ hδu P ω t).1
      ((live_iff hδ hδu P t ω).mp hp)
    linarith
  · have hf:=inactive_flag_false hδ hδu P hp
    have hz:TrackedCaps.count P t ω=0 := by simp [TrackedCaps.count,hf]
    rw [hz]
    exact mul_nonneg (by norm_num) (active_valid cutoff δ P ω t).1

lemma raw_core_bound {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (P : R→FilteredRanks w) (t : ℕ) (ω : Ω) (p : R→ℝ) (hp:∀ r,p r∈Set.Icc 0 1) :
    (∑ r,if CoreFlags.flag (P r) t ω then p r else 0)≤40*(active cutoff δ P ω t).value := by
  apply le_trans _ (count_bound hδ hδu P t ω)
  apply sum_le_sum
  intro r _
  split_ifs
  · exact (hp r).2
  · rfl

lemma prepared_input_bound {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (P : J→R→FilteredRanks w) (old : Finset J) (t : ℕ) (ω : Ω)
    (p : J×R→ℝ) (hp:∀ ir,p ir∈Set.Icc 0 1) (i:J) :
    AdaptiveAllocation.preparedInput old (activeSet (vector cutoff δ P ω t))
      (StarSimplex.flags P ω t) p i≤40*vector cutoff δ P ω t i := by
  have hb:=raw_core_bound hδ hδu (P i) t ω (fun r=>p (i,r)) (fun r=>hp (i,r))
  apply le_trans _ hb
  apply sum_le_sum
  intro r _
  simp only [AdaptiveAllocation.preparedFlags,ChangingDomains.syntheticFlags,StarSimplex.flags]
  by_cases hh : i∈old ∧ i∈activeSet (vector cutoff δ P ω t) <;>
    by_cases hf : CoreFlags.flag (P i r) t ω=true <;>
    simp [mem_inter,hh,hf,(hp (i,r)).1]

lemma regular_charge {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (P : J→R→FilteredRanks w) (key : ℕ→Ω→K) (t : ℕ) (ω : Ω)
    (he : epoch (vector cutoff δ P ω) (fun s=>key s ω) t=
      epoch (vector cutoff δ P ω) (fun s=>key s ω) (t+1))
    (p : J×R→ℝ) (hp:∀ ir,p ir∈Set.Icc 0 1) (S:Finset J)
    (hS:∀ i∈S,EpochSchedule.dominant (EpochSchedule.run (vector cutoff δ P ω)
      (fun s=>key s ω) t)≠some i) :
    (∑ i∈S,if weight δ (vector cutoff δ P ω) (fun s=>key s ω) t i=
        weight δ (vector cutoff δ P ω) (fun s=>key s ω) (t+1) i then 0 else
      AdaptiveAllocation.preparedInput (activeSet (vector cutoff δ P ω t))
        (activeSet (vector cutoff δ P ω (t+1))) (StarSimplex.flags P ω (t+1)) p i) ≤
    40*(∑ i∈S,CoarseSchedule.charge (active cutoff δ (P i) ω t)
      (active cutoff δ (P i) ω (t+1))) := by
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  split_ifs with hh
  · exact mul_nonneg (by norm_num) (charge_nonneg (active_valid _ _ _ _ _) (active_valid _ _ _ _ _))
  · have hn:(active cutoff δ (P i) ω t).value≠(active cutoff δ (P i) ω (t+1)).value := by
      intro hv
      exact hh (ordinary_weight δ _ _ t he i (hS i hi) hv)
    rw [CoarseSchedule.charge,ite_eq_right hn]
    have hb:=prepared_input_bound hδ hδu P (activeSet (vector cutoff δ P ω t)) (t+1) ω p hp i
    change _≤40*((active cutoff δ (P i) ω t).value+(active cutoff δ (P i) ω (t+1)).value)
    change _≤40*(active cutoff δ (P i) ω (t+1)).value at hb
    linarith [(active_valid cutoff δ (P i) ω t).1]

lemma side_ratio_charge {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (x:ℕ→J→ℝ) (key:ℕ→K) (hx:∀ t i,0≤x t i) (t:ℕ)
    (he:epoch x key t=epoch x key (t+1)) (o:J)
    (ho:EpochSchedule.dominant (EpochSchedule.run x key t)=some o)
    (B:J→ℝ) (hb:∀ i,B i≤40*x (t+1) i) :
    (if sideRatio δ x key t=sideRatio δ x key (t+1) then 0 else
      (∑ i∈univ.erase o,B i)+(sideRatio δ x key t+sideRatio δ x key (t+1))*(∑ i,B i)) ≤
    124*CoarseSide.charge δ (CoarseSide.sideInput x key) (CoarseSide.epochReset x key) t := by
  have hn:=(epoch_same_iff x key t).mp he
  have hm:=ordinary_mass x key t he
  have ho':EpochSchedule.dominant (EpochSchedule.run x key (t+1))=some o :=
    (ordinary_mark x key t he).trans ho
  have hA : 0 < mass x key t :=dominant_mass_pos ho
  have hs:0≤CoarseSide.sideInput x key t:=CoarseSide.side_nonneg (hx t) _
  have hs':0≤CoarseSide.sideInput x key (t+1):=CoarseSide.side_nonneg (hx (t+1)) _
  have hch:0≤CoarseSide.charge δ (CoarseSide.sideInput x key) (CoarseSide.epochReset x key) t := by
    unfold CoarseSide.charge
    split_ifs
    · exact add_nonneg hs hs'
    · rfl
  split_ifs with hu
  · exact mul_nonneg (by norm_num) hch
  · have hU:sideHeld δ x key t≠sideHeld δ x key (t+1) := by
      intro hh
      exact hu (by simp only [sideRatio,hm,hh])
    have ht:factorTest id δ (CoarseSide.sideInput x key (t+1)) (sideHeld δ x key t) := by
      by_contra hh
      apply hU
      symm
      change CoarseSide.held δ _ _ (t+1)=CoarseSide.held δ _ _ t
      change ¬factorTest id δ (CoarseSide.sideInput x key (t+1))
        (CoarseSide.held δ _ _ t) at hh
      rw [CoarseSide.held,ite_eq_right (not_or.mpr ⟨hn,hh⟩)]
    rw [CoarseSide.charge,ite_eq_left ⟨hn,ht⟩]
    have hsn: (∑ i∈univ.erase o,B i)≤40*CoarseSide.sideInput x key (t+1) := by
      change _≤40*CoarseSide.side (x (t+1)) (EpochSchedule.run x key (t+1))
      rw [side_eq_erase _ _ ho',mul_sum]
      exact sum_le_sum fun i _=>hb i
    have htot:(∑ i,B i)≤41*mass x key t := by
      have h:=sum_le_sum (s:=univ) (fun i _=>hb i)
      rw [←mul_sum] at h
      have ha:=(mass_accuracy x key hx (t+1)).2
      rw [hm] at ha
      change EpochSchedule.total (x (t+1))≤_ at ha
      change (∑ i,B i)≤40*EpochSchedule.total (x (t+1)) at h
      linarith
    have hrat : 0 ≤ sideRatio δ x key t+sideRatio δ x key (t+1) :=
      add_nonneg (side_ratio_nonneg δ x key hx t) (side_ratio_nonneg δ x key hx (t+1))
    have hprod:=mul_le_mul_of_nonneg_left htot hrat
    have heq:(sideRatio δ x key t+sideRatio δ x key (t+1))*(41*mass x key t)=
        41*(sideHeld δ x key t+sideHeld δ x key (t+1)) := by
      simp only [sideRatio,hm]
      field_simp [hA.ne']
    rw [heq] at hprod
    have hu0:=(side_held_accuracy hδ x key hx t).2
    have hu1:=(side_held_accuracy hδ x key hx (t+1)).2
    have hUbound:sideHeld δ x key t+sideHeld δ x key (t+1)≤
        2*(CoarseSide.sideInput x key t+CoarseSide.sideInput x key (t+1)) := by
      have hmul:=mul_le_mul_of_nonneg_right (show 1+δ≤2 by linarith) (add_nonneg hs hs')
      nlinarith
    linarith

end KServer.ScheduleEdits

end


/-! Literal all-case pointwise movement, preserving the coefficient one of
parent movement. No probabilistic movement endpoint is assumed here. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualOutput
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar OutputDynamics
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

lemma switchCharge_nonneg (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (t:ℕ) (ω:Ω):
    0≤ switchCharge P Q t ω:=
  RuleSchedule.charge_nonneg (S_nonneg P (t+1) ω) (D_nonneg P Q (t+1) ω) _ _ _

lemma reset_iff (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (t:ℕ) (ω:Ω):
    reset P Q (t+1) ω=false ↔
      epoch (vector cutoff ds P ω) (fun s=> key Q s ω) t=
      epoch (vector cutoff ds P ω) (fun s=> key Q s ω) (t+1):=by
  simp only [reset,Nat.add_sub_cancel,decide_eq_false_iff_not]
  exact (epoch_same_iff (vector cutoff ds P ω) (fun s=> key Q s ω) t).symm

lemma ordinary_mark (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (t:ℕ) (ω:Ω)
    (he:reset P Q (t+1) ω=false):mark P Q (t+1) ω=mark P Q t ω:=by
  exact ScheduleEdits.ordinary_mark _ _ t ((reset_iff P Q t ω).mp he)

lemma ordinary_movement {k:ℝ} (hk:1≤ k) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (t:ℕ) (ω:Ω)
    (hq:size Q (t+1) ω≤ k) (q q':ℝ)
    (hp:(∑ i,(n P (t+1) ω i-β k Q (t+1) ω*B P (t+1) ω i+f k P Q (t+1) ω i))≤ q')
    (he:reset P Q (t+1) ω=false):
    variation (out hk P Q (t+1) ω q') (out hk P Q t ω q)≤
      |q'-q|+2*variation (d k P Q (t+1) ω) (d k P Q t ω)+
      40*(S P (t+1) ω*variation (α k P Q (t+1) ω) (α k P Q t ω)+
        D P Q (t+1) ω*variation (side hk P Q (t+1) ω) (side hk P Q t ω)+
        |D P Q (t+1) ω-D P Q t ω|+switchCharge P Q t ω):=by
  have hm:=ordinary_mark P Q t ω he
  have hSa:0≤ S P (t+1) ω*variation (α k P Q (t+1) ω) (α k P Q t ω):=
    mul_nonneg (S_nonneg P (t+1) ω) (variation_nonneg _ _)
  have hDw:0≤ D P Q (t+1) ω*variation (side hk P Q (t+1) ω) (side hk P Q t ω):=
    mul_nonneg (D_nonneg P Q (t+1) ω) (variation_nonneg _ _)
  have hJ:=switchCharge_nonneg P Q t ω
  have hD:=abs_nonneg (D P Q (t+1) ω-D P Q t ω)
  cases ho:mark P Q t ω with
  | none=>
    have ho':mark P Q (t+1) ω=none:=hm.trans ho
    have hh:=outI_movement hk P Q hs t ω hq q q' hp (fun _ h=> by rw [ho'] at h; cases h)
    simp only [out,ho,ho']
    linarith
  | some o=>
    have ho':mark P Q (t+1) ω=some o:=hm.trans ho
    have hmarked:marked P Q (t+1) ω=true:=by simp [marked,ho']
    have hu:rule P Q (t+1) ω=RuleSchedule.update (S P (t+1) ω) (D P Q (t+1) ω) (rule P Q t ω):=by
      simp only [rule,RuleSchedule.run,RuleSchedule.step,hmarked,he,ite_true,Bool.false_eq_true,ite_false]
    have hj:switchCharge P Q t ω=
        (if rule P Q (t+1) ω=rule P Q t ω then 0 else
          if rule P Q (t+1) ω then D P Q (t+1) ω else S P (t+1) ω):=by
      simp only [switchCharge,RuleSchedule.charge,hmarked,he,Bool.false_eq_true,ite_false,ite_true,←hu]
    cases hold:rule P Q t ω <;> cases hnew:rule P Q (t+1) ω
    · have hr: D P Q (t+1) ω/2≤ S P (t+1) ω:=by
        have h:=(rule_allowed P Q (t+1) ω).2 hmarked
        simpa only [hnew,Bool.false_eq_true,ite_false] using h
      have hh:=outI_movement hk P Q hs t ω hq q q' hp (fun _ _=> hr)
      simp only [out,ho,ho',hold,hnew,Bool.false_eq_true,ite_false]
      linarith
    · have hr:S P (t+1) ω≤ D P Q (t+1) ω/2:=by
        rw [hold,RuleSchedule.update,RuleSchedule.choose] at hu
        simp only [hnew,Bool.false_eq_true,ite_false] at hu
        exact (of_decide_eq_true hu.symm).le
      have hh:=out_downcross hk P Q hs t ω hq q q' o hp hr
      have hj':switchCharge P Q t ω=D P Q (t+1) ω:=by simpa only [hold,hnew,Bool.true_eq_false,ite_false,ite_true] using hj
      simp only [out,ho,ho',hold,hnew,Bool.false_eq_true,ite_false,ite_true]
      rw [hj']
      linarith [D_nonneg P Q (t+1) ω]
    · have hr:2*D P Q (t+1) ω≤ S P (t+1) ω:=by
        rw [hold,RuleSchedule.update] at hu
        simp only [hnew,ite_true] at hu
        exact (lt_of_not_ge (of_decide_eq_false hu.symm)).le
      have hh:=out_upcross hk P Q hs t ω hq q q' o hp hr
      have hj':switchCharge P Q t ω=S P (t+1) ω:=by simpa only [hold,hnew,Bool.false_eq_true,ite_false] using hj
      simp only [out,ho,ho',hold,hnew,Bool.false_eq_true,ite_false,ite_true]
      rw [hj']
      linarith [S_nonneg P (t+1) ω]
    · have hh:=outII_movement hk P Q t ω q q' o
      simp only [out,ho,ho',hold,hnew,ite_true]
      linarith

end KServer.ActualOutput

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_AllocationCausality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hysteresis switch budget with signed filtering before every reset test.
The only costs are actual rank drifts, actual flag changes, held-scale
variation, and the new potential at literal wholesale resets. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.RuleSchedule
attribute [local instance] Classical.propDecidable
open RankTracking
variable {Ω R : Type} [Fintype Ω] [Fintype R] {w : Ω→ℝ}

lemma S_nonneg (P : R→FilteredRanks w) (flags : ℕ→Ω→R→Bool) (t : ℕ) (ω : Ω) :
    0≤S P flags t ω :=core_nonneg _ (fun r=>((P r).range t ω).1)

lemma editing (P : R→FilteredRanks w) (flags : ℕ→Ω→R→Bool)
    (marked reset : ℕ→Ω→Bool) (D : ℕ→Ω→ℝ) (hD : ∀ t ω,0≤D t ω)
    (hm : ∀ t ω,reset (t+1) ω=false→marked (t+1) ω=marked t ω) (t : ℕ) (ω : Ω) :
    J P flags marked reset D t ω/2+potential P flags marked reset D (t+1) ω≤
      value (marked t ω) (run marked reset (S P flags) D t ω)
        (core (flags t ω) (fun r=>(P r).p (t+1) ω)) (D t ω)+expense P flags reset D t ω := by
  let old:=run marked reset (S P flags) D t ω
  have hmid:=value_nonneg (core_nonneg (flags t ω) (fun r=>((P r).range (t+1) ω).1))
    (hD t ω) (marked t ω) old
  cases he:reset (t+1) ω with
  | true=>
    have hv:=value_upper (S_nonneg P flags (t+1) ω) (hD (t+1) ω) (marked (t+1) ω)
      (run marked reset (S P flags) D (t+1) ω)
    have hf:0≤∑ r,if flags t ω r=flags (t+1) ω r then (0:ℝ) else 1:=
      sum_nonneg fun _ _=>by positivity
    simp only [J,charge,he,ite_true,zero_div,zero_add,potential,expense] at ⊢
    dsimp only [old] at hmid
    linarith [abs_nonneg (D (t+1) ω-D t ω)]
  | false=>
    have hc:=ordinary_credit (S P flags (t+1) ω) (D (t+1) ω) (marked (t+1) ω) old
    have hd:=data_change (marked t ω) old (flags t ω) (flags (t+1) ω)
      (fun r=>(P r).p (t+1) ω) (D:=D t ω) (E:=D (t+1) ω) (fun r=>(P r).range (t+1) ω)
    rw [hm t ω he] at hc
    change value (marked t ω) old (S P flags (t+1) ω) (D (t+1) ω) -
      value (marked t ω) old (core (flags t ω) (fun r=>(P r).p (t+1) ω)) (D t ω)≤_ at hd
    simp only [J,potential,run,he,expense,Bool.false_eq_true,ite_false,add_zero,hm t ω he]
    change charge (marked t ω) false old _ _/2+value (marked t ω)
      (step (marked t ω) false _ _ old) _ _≤_
    linarith

lemma run_adapted (P : R→FilteredRanks w) (flags : ℕ→Ω→R→Bool)
    (marked reset : ℕ→Ω→Bool) (D : ℕ→Ω→ℝ) (H : ℕ→Ω→ℕ)
    (hH : ∀ r t ω,(P r).history t ω=H t ω)
    (href : ∀ t ω z,H (t+1) ω=H (t+1) z→H t ω=H t z)
    (hf : ∀ t ω z,H t ω=H t z→flags t ω=flags t z)
    (hm : ∀ t ω z,H t ω=H t z→marked t ω=marked t z)
    (hr : ∀ t ω z,H t ω=H t z→ reset t ω=reset t z)
    (hD : ∀ t ω z,H t ω=H t z→D t ω=D t z) (t : ℕ) (ω z : Ω) (he:H t ω=H t z) :
    run marked reset (S P flags) D t ω=run marked reset (S P flags) D t z := by
  have hh s (hs:s≤t):H s ω=H s z:=StarSimplex.history_prefix H href hs he
  apply run_congr marked reset (S P flags) D t ω z
  · exact fun s hs=>hm s ω z (hh s hs)
  · exact fun s hs=>hr s ω z (hh s hs)
  · intro s hs
    unfold S
    rw [hf s ω z (hh s hs)]
    congr 1
    funext r
    exact (P r).adapted s ω z (by simpa only [hH] using hh s hs)
  · exact fun s hs=>hD s ω z (hh s hs)

lemma filtering_zero (P : R→FilteredRanks w) (flags : ℕ→Ω→R→Bool)
    (marked reset : ℕ→Ω→Bool) (D : ℕ→Ω→ℝ) (H : ℕ→Ω→ℕ)
    (hH : ∀ r t ω,(P r).history t ω=H t ω)
    (href : ∀ t ω z,H (t+1) ω=H (t+1) z→H t ω=H t z)
    (hf : ∀ t ω z,H t ω=H t z→flags t ω=flags t z)
    (hm : ∀ t ω z,H t ω=H t z→marked t ω=marked t z)
    (hr : ∀ t ω z,H t ω=H t z→ reset t ω=reset t z)
    (hD : ∀ t ω z,H t ω=H t z→D t ω=D t z) (t : ℕ) :
    avg w (fun ω=>value (marked t ω) (run marked reset (S P flags) D t ω)
      (core (flags t ω) (fun r=>(P r).before (t+1) ω)) (D t ω)-
      potential P flags marked reset D t ω)=0 := by
  simp_rw [potential,S,input_difference,avg_sum]
  apply sum_eq_zero
  intro r _
  apply filtering_affine (P r) t
  intro ω z he
  have hh:H t ω=H t z:=by simpa only [hH] using he
  dsimp only
  rw [hm t ω z hh,run_adapted P flags marked reset D H hH href hf hm hr hD t ω z hh,hf t ω z hh]

lemma payment_step (P : R→FilteredRanks w) (flags : ℕ→Ω→R→Bool)
    (marked reset : ℕ→Ω→Bool) (D : ℕ→Ω→ℝ) (H : ℕ→Ω→ℕ)
    (hw : ∀ ω,0≤w ω) (hDn : ∀ t ω,0≤D t ω)
    (hreset : ∀ t ω,reset (t+1) ω=false→marked (t+1) ω=marked t ω)
    (hH : ∀ r t ω,(P r).history t ω=H t ω)
    (href : ∀ t ω z,H (t+1) ω=H (t+1) z→H t ω=H t z)
    (hf : ∀ t ω z,H t ω=H t z→flags t ω=flags t z)
    (hm : ∀ t ω z,H t ω=H t z→marked t ω=marked t z)
    (hr : ∀ t ω z,H t ω=H t z→ reset t ω=reset t z)
    (hD : ∀ t ω z,H t ω=H t z→D t ω=D t z) (t : ℕ) :
    avg w (J P flags marked reset D t)/2+avg w (potential P flags marked reset D (t+1))≤
      avg w (potential P flags marked reset D t)+
      (∑ r,avg w (fun ω=>|(P r).p (t+1) ω-(P r).before (t+1) ω|))+
      avg w (expense P flags reset D t) := by
  have hp (ω:Ω):J P flags marked reset D t ω/2+potential P flags marked reset D (t+1) ω≤
      value (marked t ω) (run marked reset (S P flags) D t ω)
        (core (flags t ω) (fun r=>(P r).before (t+1) ω)) (D t ω)+
      (∑ r,|(P r).p (t+1) ω-(P r).before (t+1) ω|)+expense P flags reset D t ω := by
    have he:=editing P flags marked reset D hDn hreset t ω
    have hd:=(le_abs_self _).trans (input_lipschitz (marked t ω)
      (run marked reset (S P flags) D t ω) (flags t ω)
      (fun r=>(P r).p (t+1) ω) (fun r=>(P r).before (t+1) ω) (D t ω))
    linarith
  have ha:=avg_mono hw hp
  simp only [avg_add,avg_sum] at ha
  have hdiv:avg w (fun ω=>J P flags marked reset D t ω/2)=avg w (J P flags marked reset D t)/2:=by
    simp only [avg,←mul_div_assoc,sum_div]
  rw [hdiv] at ha
  have hzero:=filtering_zero P flags marked reset D H hH href hf hm hr hD t
  rw [avg_sub] at hzero
  linarith

lemma payment (P : R→FilteredRanks w) (flags : ℕ→Ω→R→Bool)
    (marked reset : ℕ→Ω→Bool) (D : ℕ→Ω→ℝ) (H : ℕ→Ω→ℕ)
    (hw : ∀ ω,0≤w ω) (hDn : ∀ t ω,0≤D t ω)
    (hreset : ∀ t ω,reset (t+1) ω=false→ marked (t+1) ω=marked t ω)
    (hH : ∀ r t ω,(P r).history t ω=H t ω)
    (href : ∀ t ω z,H (t+1) ω=H (t+1) z→ H t ω=H t z)
    (hf : ∀ t ω z,H t ω=H t z→ flags t ω=flags t z)
    (hm : ∀ t ω z,H t ω=H t z→ marked t ω=marked t z)
    (hr : ∀ t ω z,H t ω=H t z→ reset t ω=reset t z)
    (hD : ∀ t ω z,H t ω=H t z→ D t ω=D t z) (n : ℕ) :
    (∑ t∈range n,avg w (J P flags marked reset D t))≤
      2*(avg w (potential P flags marked reset D 0)+
        (∑ t∈range n,∑ r,avg w (fun ω=>|(P r).p (t+1) ω-(P r).before (t+1) ω|))+
        ∑ t∈range n,avg w (expense P flags reset D t)) := by
  have hh:(∑ t∈range n,avg w (J P flags marked reset D t))/2+
      avg w (potential P flags marked reset D n)≤
      avg w (potential P flags marked reset D 0)+
        (∑ t∈range n,∑ r,avg w (fun ω=>|(P r).p (t+1) ω-(P r).before (t+1) ω|))+
        ∑ t∈range n,avg w (expense P flags reset D t) := by
    induction n with
    | zero=>simp
    | succ n ih=>
      simp only [sum_range_succ]
      have hp:=payment_step P flags marked reset D H hw hDn hreset hH href hf hm hr hD n
      linarith
  have hn:0≤avg w (potential P flags marked reset D n):=
    sum_nonneg fun ω _=>mul_nonneg (hw ω)
      (value_nonneg (S_nonneg P flags n ω) (hDn n ω) _ _)
  linarith

end KServer.RuleSchedule

end


/-! Predictability of the *actual* star schedule and regime, for the common
observation history. In particular none of the filtering coefficients uses
the new reset event. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualOutput
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

lemma key_adapted (Q:R→ FilteredRanks w) (H:ℕ→Ω→ℕ)
    (hQ:∀ r t ω,(Q r).history t ω=H t ω)
    (hr:∀ t ω z,H (t+1) ω=H (t+1) z→ H t ω=H t z)
    (t:ℕ) (ω z:Ω) (he:H t ω=H t z):key Q t ω=key Q t z:=
  parent_adapted cutoff dp Q H hQ hr t ω z he
lemma b_adapted (k:ℝ) (Q:R→ FilteredRanks w) (H:ℕ→Ω→ℕ)
    (hQ:∀ r t ω,(Q r).history t ω=H t ω)
    (hr:∀ t ω z,H (t+1) ω=H (t+1) z→ H t ω=H t z)
    (t:ℕ) (ω z:Ω) (he:H t ω=H t z):b k Q t ω=b k Q t z:=by
  unfold b
  rw [key_adapted Q H hQ hr t ω z he]

section
variable (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (H:ℕ→Ω→ℕ)
    (hP:∀ i r t ω,(P i r).history t ω=H t ω)
    (hQ:∀ r t ω,(Q r).history t ω=H t ω)
    (hr:∀ t ω z,H (t+1) ω=H (t+1) z→ H t ω=H t z)
include hP hQ hr
omit [Fintype J] in
lemma schedule_prefix (t:ℕ) (ω z:Ω) (he:H t ω=H t z):
    ScheduleCausality.PrefixEq t (vector cutoff ds P ω) (vector cutoff ds P z) ∧
    ScheduleCausality.PrefixEq t (fun s=> key Q s ω) (fun s=> key Q s z):=by
  constructor
  · exact fun s hs=> vector_adapted ds P H hP hr s ω z (StarSimplex.history_prefix H hr hs he)
  · exact fun s hs=> key_adapted Q H hQ hr s ω z (StarSimplex.history_prefix H hr hs he)
lemma mark_adapted (t:ℕ) (ω z:Ω) (he:H t ω=H t z):mark P Q t ω=mark P Q t z:=by
  have hd:=schedule_prefix P Q H hP hQ hr t ω z he
  exact congrArg EpochSchedule.dominant (ScheduleCausality.run_prefix _ _ _ _ t hd.1 hd.2)
lemma marked_adapted (t:ℕ) (ω z:Ω) (he:H t ω=H t z):marked P Q t ω=marked P Q t z:=
  congrArg Option.isSome (mark_adapted P Q H hP hQ hr t ω z he)
lemma reset_adapted (t:ℕ) (ω z:Ω) (he:H t ω=H t z):reset P Q t ω=reset P Q t z:=by
  have hd:=schedule_prefix P Q H hP hQ hr t ω z he
  have ht:t-1≤ t:=Nat.sub_le _ _
  simp only [reset,hd.1 t le_rfl,hd.1 (t-1) ht,hd.2 t le_rfl,hd.2 (t-1) ht,
    ScheduleCausality.run_prefix _ _ _ _ (t-1) (hd.1.mono ht) (hd.2.mono ht)]
lemma D_adapted (t:ℕ) (ω z:Ω) (he:H t ω=H t z):D P Q t ω=D P Q t z:=by
  have hm:=mark_adapted P Q H hP hQ hr t ω z he
  change (match mark P Q t ω with | none=>0 | some o=> StarSide.coarseFlex ds (P o) t ω)=
    (match mark P Q t z with | none=>0 | some o=> StarSide.coarseFlex ds (P o) t z)
  rw [hm]
  cases mark P Q t z with
  | none=> rfl
  | some o=> exact StarSide.coarseFlex_adapted ds (P o) H (hP o) t ω z he
end

lemma rule_S (P:J→ R→ FilteredRanks w) (t:ℕ) (ω:Ω):
    RuleSchedule.S (fun ir:J×R=> P ir.1 ir.2) (ruleFlags P) t ω=S P t ω:=by
  simp only [RuleSchedule.S,RuleSchedule.core,ruleFlags,S,B,TrackedCaps.core,Fintype.sum_prod_type]
  rfl
omit [Fintype J] [Fintype R] in
lemma flags_adapted (P:J→ R→ FilteredRanks w) (H:ℕ→Ω→ℕ)
    (hP:∀ i r t ω,(P i r).history t ω=H t ω)
    (t:ℕ) (ω z:Ω) (he:H t ω=H t z):ruleFlags P t ω=ruleFlags P t z:=by
  funext ir
  exact CoreFlags.flag_adapted (P ir.1 ir.2) t (by rw [hP,hP,he])
end KServer.ActualOutput

end


/-! Uniform affine slope and endpoint bounds for the literal marked-side
family; logarithmic cancellation removes dependence on the number of children. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.SideProfile
attribute [local instance] Classical.propDecidable
open SideTracker SideFamilies
variable {J R : Type} [Fintype J] [DecidableEq J] [Fintype R]

lemma B_bound {cw ell b h a:ℝ} (hcw:0 < cw) (hel:1≤ell) (hh:1≤h)
    (hb:0≤b) (hM:b+cw*h/ell≤5) (ha:a∈Set.Icc 0 16) :
    Bcoef 40 b (cw*h/ell) (Real.exp (1-h)/h) a≤3600/cw*ell := by
  have hp:0<ell:=lt_of_lt_of_le zero_lt_one hel
  have hz:0<Real.exp (1-h)/h:=div_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one hh)
  have ht:0 ≤ cw*h/ell:=by positivity
  have hl:=side_log_bound hh (by norm_num : (0:ℝ)≤16) ha
  have hlog:Real.log (1+(16:ℝ))+2≤18 := by
    have h:=Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<1+16)
    linarith
  have hm:=mul_le_mul_of_nonneg_right hlog (le_trans zero_le_one hh)
  have h:=Bcoef_bound (by norm_num : (0:ℝ)≤40) hb hz ha.1 hcw hp
    (lt_of_lt_of_le zero_lt_one hh) rfl (show b+(cw*h/ell)/2≤5 by linarith)
    (show Real.log (1+a/(Real.exp (1-h)/h))≤18*h from hl.trans hm)
  norm_num at h
  exact h

omit [DecidableEq J] in
lemma coefficient_bound {cw ell b D:ℝ} (hcw:0 < cw) (hel:1≤ell)
    (A:Finset J) (f:J→R→Bool) (h:J→ℝ) (hh:∀ i,1≤h i)
    (hb:0≤b) (hM:∀ i,b+cw*h i/ell≤5) (a:J→ℝ)
    (ha:a∈ChangingDomains.sideDomain A 16) (ir:J×R) :
    let d:=fromLog A f 16 b D cw ell h (by norm_num) hcw
      (lt_of_lt_of_le zero_lt_one hel) hh
    |(family 40).coefficient d a ir|≤3600/cw*ell := by
  intro d
  have hw:a ir.1∈Set.Icc 0 16:=⟨ha.1 _,(single_le_sum (fun i _=>ha.1 i) (mem_univ _)).trans ha.2.1⟩
  have hbnd:=B_bound hcw hel (hh ir.1) hb (hM ir.1) hw
  have hn:0≤Bcoef 40 b (cw*h ir.1/ell) (Real.exp (1-h ir.1)/h ir.1) (a ir.1):=
    (coefficients_nonneg (by norm_num) hb
      (by have he:=lt_of_lt_of_le zero_lt_one hel; have hi:=lt_of_lt_of_le zero_lt_one (hh ir.1); positivity)
      (div_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one (hh ir.1))) hw.1).2
  change |if f ir.1 ir.2 then -Bcoef 40 b (cw*h ir.1/ell) (Real.exp (1-h ir.1)/h ir.1) (a ir.1) else 0|≤_
  split_ifs
  · simpa only [abs_neg,abs_of_nonneg hn] using hbnd
  · simp only [abs_zero]
    positivity

omit [DecidableEq J] in
lemma endpoint {cw ell b D:ℝ} (hcw:0 < cw) (hel:1≤ell)
    (A:Finset J) (f:J→R→Bool) (h:J→ℝ) (hh:∀ i,1≤h i)
    (hb:0≤b) (hM:∀ i,b+cw*h i/ell≤5) (hD:0≤D)
    (p:J×R→ℝ) (hp:∀ ir,0≤p ir) (a:J→ℝ)
    (ha:a∈ChangingDomains.sideDomain A 16) :
    let d:=fromLog A f 16 b D cw ell h (by norm_num) hcw
      (lt_of_lt_of_le zero_lt_one hel) hh
    |(family 40).value d p a|≤640*(1/cw+1)*ell*D+
      (3600/cw*ell)*(∑ i,core d p i) := by
  intro d
  have hB (i:J):0 ≤ core d p i:=sum_nonneg fun r _=>by split_ifs; exact hp _; rfl
  have he (i:J):|primitive 40 b (cw*h i/ell) (Real.exp (1-h i)/h i) (core d p i) D (a i)|≤
      40*(1/cw+1)*ell*(D*a i)+(3600/cw*ell)*core d p i := by
    have hw:a i∈Set.Icc 0 16:=⟨ha.1 _,(single_le_sum (fun i _=>ha.1 i) (mem_univ _)).trans ha.2.1⟩
    have hz:0<Real.exp (1-h i)/h i:=div_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one (hh i))
    have hn:=coefficients_nonneg (by norm_num : (0:ℝ)≤40) hb
      (show 0 < cw*h i/ell by have he:=lt_of_lt_of_le zero_lt_one hel; have hi:=lt_of_lt_of_le zero_lt_one (hh i); positivity) hz hw.1
    rw [primitive_coefficients]
    calc _≤|Dcoef 40 (cw*h i/ell) (Real.exp (1-h i)/h i) (a i)*D|+
        |Bcoef 40 b (cw*h i/ell) (Real.exp (1-h i)/h i) (a i)*core d p i|:=abs_sub _ _
         _=Dcoef 40 (cw*h i/ell) (Real.exp (1-h i)/h i) (a i)*D+
          Bcoef 40 b (cw*h i/ell) (Real.exp (1-h i)/h i) (a i)*core d p i := by
            rw [abs_of_nonneg (mul_nonneg hn.1 hD),abs_of_nonneg (mul_nonneg hn.2 (hB i))]
         _≤(40*(1/cw+1)*ell*a i)*D+(3600/cw*ell)*core d p i:=
          add_le_add (mul_le_mul_of_nonneg_right (Dcoef_bound (by norm_num) hz hw.1 hcw hel (hh i) rfl) hD)
            (mul_le_mul_of_nonneg_right (B_bound hcw hel (hh i) hb (hM i) hw) (hB i))
         _= _:=by ring
  rw [value_eq]
  change |∑ i,primitive 40 b (cw*h i/ell) (Real.exp (1-h i)/h i) (core d p i) D (a i)|≤_
  calc _≤∑ i,|primitive 40 b (cw*h i/ell) (Real.exp (1-h i)/h i) (core d p i) D (a i)|:=abs_sum_le_sum_abs _ _
       _≤∑ i,(40*(1/cw+1)*ell*(D*a i)+(3600/cw*ell)*core d p i):=sum_le_sum fun i _=>he i
       _=40*(1/cw+1)*ell*D*(∑ i,a i)+(3600/cw*ell)*(∑ i,core d p i):=by
          simp only [sum_add_distrib,←mul_sum]; ring
       _≤640*(1/cw+1)*ell*D+(3600/cw*ell)*(∑ i,core d p i):=by
          have hc:0≤40*(1/cw+1)*ell*D:=by positivity
          have hm:=mul_le_mul_of_nonneg_left ha.2.1 hc
          nlinarith

end KServer.SideProfile

end


/-! Literal synthetic-flag preparation and selective held-log parameter edits
for the marked-side minimizers of the constructed star. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.SideEdits
attribute [local instance] Classical.propDecidable
open SideTracker SideFamilies
variable {J R : Type} [Fintype J] [DecidableEq J] [Fintype R]

lemma Q_nonneg {cw ell:ℝ} (hcw:0 < cw) (hel:0≤ell):0≤Q cw ell:=by
  have hl:=Real.log_nonneg (by norm_num : (1:ℝ)≤17)
  unfold Q; positivity

lemma pre_edit {cw ell b D E:ℝ} (hcw:0 < cw) (hel:1≤ell)
    (A B:Finset J) (f g:J→R→Bool) (h h':J→ℝ) (hh:∀ i,1≤h i) (hh':∀ i,1≤h' i)
    (hb:0≤b) (hM:∀ i,b+cw*h i/ell≤5)
    (p:J×R→ℝ) (hp:∀ ir,p ir∈Set.Icc 0 1)
    (hf:∀ i∉A,∀ r,f i r=false) (hg:∀ i∉B,∀ r,g i r=false)
    (a:J→ℝ) (ha:a∈ChangingDomains.sideDomain A 16) :
    let old:=fromLog A f 16 b D cw ell h (by norm_num) hcw (lt_of_lt_of_le zero_lt_one hel) hh
    let new:=fromLog B g 16 b E cw ell h' (by norm_num) hcw (lt_of_lt_of_le zero_lt_one hel) hh'
    |(family 40).value (prepareData old new) p a-(family 40).value old p a|≤
      L cw ell*|E-D|+Q cw ell*ChangingDomains.changedFlags f g := by
  intro old new
  have hi:=fromLog_input_bound (R:=R) f h (by norm_num : (0:ℝ)≤16) hcw hel hh
    (by norm_num : (0:ℝ)≤40) hb hM (D:=E) (D':=D)
    (B:=core (prepareData old new) p) (B':=core old p) ha
  have hs:ChangingDomains.variation (core (prepareData old new) p) (core old p)≤
      ChangingDomains.changedFlags f g:=by
    have he:=(ChangingDomains.synthetic_errors (fun i r=>hp (i,r)) hf hg).1
    change ChangingDomains.variation (ChangingDomains.core (ChangingDomains.syntheticFlags A B g) (fun i r=>p (i,r)))
      (ChangingDomains.core f (fun i r=>p (i,r)))≤_
    simpa only [ChangingDomains.variation,abs_sub_comm] using he
  have hm:=mul_le_mul_of_nonneg_left hs (Q_nonneg hcw (le_trans zero_le_one hel))
  rw [value_eq,value_eq]
  change |potential 40 b (fun i=>cw*h i/ell) (fun i=>Real.exp (1-h i)/h i)
    (core (prepareData old new) p) E a-potential 40 b (fun i=>cw*h i/ell) (fun i=>Real.exp (1-h i)/h i)
    (core old p) D a|≤_
  calc _≤40*(1/cw+1)*ell*16*|E-D|+
      40*5*(Real.log (1+16)+2)/cw*ell*ChangingDomains.variation (core (prepareData old new) p) (core old p):=hi
       _≤L cw ell*|E-D|+Q cw ell*ChangingDomains.changedFlags f g:=by
        norm_num only at *
        unfold L Q at *
        linarith

lemma post_edit {cw ell b D E:ℝ} (hcw:0 < cw) (hel:1≤ell)
    (A B:Finset J) (f g:J→R→Bool) (h h':J→ℝ) (hh:∀ i,1≤h i) (hh':∀ i,1≤h' i)
    (hb:1≤b) (hM:∀ i,b+cw*h i/ell≤5) (hM':∀ i,b+cw*h' i/ell≤5) (hE:0≤E)
    (p:J×R→ℝ) (hp:∀ ir,0≤p ir)
    (a:J→ℝ) (ha:a∈ChangingDomains.sideDomain A 16) :
    let old:=fromLog A f 16 b D cw ell h (by norm_num) hcw (lt_of_lt_of_le zero_lt_one hel) hh
    let new:=fromLog B g 16 b E cw ell h' (by norm_num) hcw (lt_of_lt_of_le zero_lt_one hel) hh'
    let z:=SideFamilies.transport 40 old new p a
    |(family 40).value new p z-(family 40).value (prepareData old new) p z|≤
      K cw ell*(∑ i,if h i=h' i then 0 else core (prepareData old new) p i) := by
  intro old new z
  have hz:z∈ChangingDomains.sideDomain B 16:=SideFamilies.transport_mem 40 old new p a rfl
  have hprep:=SideFamilies.update_feasible (prepareData old new) (M:=5) hb hE
    (fun i _=>hM i) (by norm_num : 2*(5:ℝ)<16) p hp
    (fun i hi r=>by
      change i∉A at hi
      change (if i∈A∩B then g i r else false)=false
      simp only [mem_inter,hi,false_and,ite_false]) a ha
  norm_num only at hprep
  have hcap:∀ i,E*z i≤5*core (prepareData old new) p i:=by
    intro i
    by_cases hi:i∈B
    · have hm:=mul_le_mul_of_nonneg_right (hM i)
        (show 0 ≤ core (prepareData old new) p i from sum_nonneg fun r _=>by split_ifs; exact hp _; rfl)
      have ht:=hprep.1 i
      change E*SideFamilies.prepare 40 old new p a i≤(b+cw*h i/ell)*core (prepareData old new) p i at ht
      change E*ChangingDomains.transposeSide B (SideFamilies.prepare 40 old new p a) i≤_
      simp only [ChangingDomains.transposeSide,ite_eq_left hi]
      exact ht.trans hm
    · have he:z i=0:=hz.2.2 i hi
      rw [he,mul_zero]
      exact mul_nonneg (by norm_num) (sum_nonneg fun r _=>by split_ifs; exact hp _; rfl)
  have hew:potential 40 b (fun i=>cw*h' i/ell) (fun i=>Real.exp (1-h' i)/h' i) (core new p) E z=
      potential 40 b (fun i=>cw*h' i/ell) (fun i=>Real.exp (1-h' i)/h' i) (core (prepareData old new) p) E z:=by
    apply sum_congr rfl
    intro i _
    by_cases hi:i∈A∩B
    · have hc:core new p i=core (prepareData old new) p i:=by
        unfold core
        simp only [new,old,fromLog,prepareData,ChangingDomains.syntheticFlags,ite_eq_left hi]
      rw [hc]
    · have hz0:z i=0:=by
        by_cases hiB:i∈B
        · have hiA:i∉A:=fun h=>hi (mem_inter.mpr ⟨h,hiB⟩)
          have hp0:(SideFamilies.prepare 40 old new p a) i=0:=
            (SideFamilies.prepare_mem 40 old new p a).2.2 i hiA
          change ChangingDomains.transposeSide B (SideFamilies.prepare 40 old new p a) i=0
          simp only [ChangingDomains.transposeSide,ite_eq_left hiB,hp0]
        · exact hz.2.2 i hiB
      simp only [hz0,primitive,zero_div,add_zero,Real.log_one,mul_zero,sub_zero ]
  have he:=SideFamilies.parameter_jump (by norm_num : (0:ℝ)≤16) hcw hel hh hh'
    (by norm_num : (0:ℝ)≤40) (show 0≤b by linarith) hE
    (fun i=>show 0 ≤ core (prepareData old new) p i from sum_nonneg fun r _=>by split_ifs; exact hp _; rfl)
    hM hM' ⟨hz.1,hz.2.1⟩ hcap
  rw [value_eq,value_eq]
  change |potential 40 b (fun i=>cw*h' i/ell) (fun i=>Real.exp (1-h' i)/h' i) (core new p) E z-
    potential 40 b (fun i=>cw*h i/ell) (fun i=>Real.exp (1-h i)/h i) (core (prepareData old new) p) E z|≤_
  rw [hew]
  norm_num only at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [K]
  ring

end KServer.SideEdits

end


/-! Every side edit is charged to the literal rank-flag and coarse-coordinate
schedule. No cardinality factor or charge to an unchanged dominant child. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.SideActualEdits
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseProcess CoarseEpoch AllocationSchedule StarProfile StarSide
variable {Ω J R K : Type} [Fintype Ω] [Fintype J] [DecidableEq J] [Fintype R]
variable {w:Ω→ℝ}

omit [DecidableEq J] in
lemma ordinary_key (x:ℕ→J→ℝ) (key:ℕ→K) (t:ℕ)
    (he:epoch x key t=epoch x key (t+1)) : key t=key (t+1):=by
  have hn:=(epoch_same_iff x key t).mp he
  exact Classical.not_not.mp ((not_or.mp hn).1)

lemma flags_supported (δ:ℝ) (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (t:ℕ) (ω:Ω) :
    ∀ i∉sides δ P key t ω,∀ r,sideFlags δ P key t ω i r=false:=by
  intro i hi r
  simp only [sideFlags,ite_eq_right hi]

lemma flags_marked {δ:ℝ} (hδ:0<δ) (hδu:δ≤1/1000)
    (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (t:ℕ) (ω:Ω) (o i:J) (r:R)
    (ho:mark δ P key t ω=some o) :
    sideFlags δ P key t ω i r=if i=o then false else CoreFlags.flag (P i r) t ω := by
  by_cases hi:i=o
  · subst i
    simp [sideFlags,sides,ho]
  · by_cases hA:i∈activeSet (vector cutoff δ P ω t)
    · simp [sideFlags,sides,ho,hi,hA]
    · have hf:=StarProfile.flags_supported hδ hδu P t ω i hA r
      change CoreFlags.flag (P i r) t ω=false at hf
      simp [sideFlags,sides,ho,hA,hi,hf]

lemma flags_change {δ:ℝ} (hδ:0<δ) (hδu:δ≤1/1000)
    (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (t:ℕ) (ω:Ω)
    (he:epoch (vector cutoff δ P ω) (fun s=>key s ω) t=
      epoch (vector cutoff δ P ω) (fun s=>key s ω) (t+1)) :
    ChangingDomains.changedFlags (sideFlags δ P key t ω) (sideFlags δ P key (t+1) ω)≤
      ChangingDomains.changedFlags (StarSimplex.flags P ω t) (StarSimplex.flags P ω (t+1)) := by
  have hm:mark δ P key (t+1) ω=mark δ P key t ω:=ScheduleEdits.ordinary_mark _ _ _ he
  cases ho:mark δ P key t ω with
  | none=>
    have hn:sideFlags δ P key t ω=fun _ _=>false:=by funext i r; simp [sideFlags,sides,ho]
    have hn':sideFlags δ P key (t+1) ω=fun _ _=>false:=by funext i r; simp [sideFlags,sides,hm,ho]
    rw [hn,hn']
    simp only [ChangingDomains.changedFlags,ite_true,sum_const_zero]
    exact sum_nonneg fun _ _=>sum_nonneg fun _ _=>by positivity
  | some o=>
    apply sum_le_sum
    intro i _
    apply sum_le_sum
    intro r _
    rw [flags_marked hδ hδu P key t ω o i r ho,
      flags_marked hδ hδu P key (t+1) ω o i r (hm.trans ho)]
    by_cases hi:i=o
    · simp only [ite_eq_left hi,ite_true]
      split_ifs <;> norm_num
    · simp only [ite_eq_right hi,StarSimplex.flags]
      exact le_rfl

lemma prepared_core_bound {δ cw ell:ℝ} (hδ:0<δ) (hδu:δ≤1/1000)
    (hcw:0 < cw) (hel:0<ell) (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (b:ℕ→Ω→ℝ)
    (t:ℕ) (ω:Ω) (p:J×R→ℝ) (hp:∀ ir,p ir∈Set.Icc 0 1) (i:J) :
    let d:=input hcw hel δ P key b
    SideFamilies.core (SideFamilies.prepareData (d t ω).data (d (t+1) ω).data) p i≤
      40*vector cutoff δ P ω (t+1) i := by
  intro d
  apply le_trans _ (ScheduleEdits.raw_core_bound hδ hδu (P i) (t+1) ω (fun r=>p (i,r)) (fun r=>hp (i,r)))
  apply sum_le_sum
  intro r _
  change (if ChangingDomains.syntheticFlags (sides δ P key t ω) (sides δ P key (t+1) ω)
      (sideFlags δ P key (t+1) ω) i r then p (i,r) else 0)≤
      (if CoreFlags.flag (P i r) (t+1) ω then p (i,r) else 0)
  by_cases hf:CoreFlags.flag (P i r) (t+1) ω=true
  · simp only [ChangingDomains.syntheticFlags,sideFlags,hf]
    split_ifs <;> first | exact (hp (i,r)).1 | exact le_rfl
  · simp [ChangingDomains.syntheticFlags,sideFlags,hf]

lemma logs_charge {δ cw ell:ℝ} (hδ:0<δ) (hδu:δ≤1/1000)
    (hcw:0 < cw) (hel:0<ell) (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (b:ℕ→Ω→ℝ)
    (t:ℕ) (ω:Ω) (p:J×R→ℝ) (hp:∀ ir,p ir∈Set.Icc 0 1)
    (he:epoch (vector cutoff δ P ω) (fun s=>key s ω) t=
      epoch (vector cutoff δ P ω) (fun s=>key s ω) (t+1)) :
    let d:=input hcw hel δ P key b
    (∑ i,if logs δ P key t ω i=logs δ P key (t+1) ω i then 0 else
      SideFamilies.core (SideFamilies.prepareData (d t ω).data (d (t+1) ω).data) p i)≤
      40*(∑ i,CoarseSchedule.charge (active cutoff δ (P i) ω t) (active cutoff δ (P i) ω (t+1))) := by
  intro d
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  have hn:0≤CoarseSchedule.charge (active cutoff δ (P i) ω t) (active cutoff δ (P i) ω (t+1)):=
    charge_nonneg (active_valid _ _ _ _ _) (active_valid _ _ _ _ _)
  split_ifs with hlog
  · linarith
  · by_cases hi:mark δ P key t ω=some i
    · have hc:SideFamilies.core (SideFamilies.prepareData (d t ω).data (d (t+1) ω).data) p i=0:=by
        apply SideFamilies.prepared_core_zero
        change i∉sides δ P key t ω∩sides δ P key (t+1) ω
        simp [sides,hi]
      rw [hc]
      linarith
    · have hx:(active cutoff δ (P i) ω t).value≠(active cutoff δ (P i) ω (t+1)).value:=by
        intro hv
        exact hlog (congrArg (max 1) (ScheduleEdits.ordinary_weight δ _ _ t he i hi hv))
      rw [CoarseSchedule.charge,ite_eq_right hx]
      have hbnd:=prepared_core_bound hδ hδu hcw hel P key b t ω p hp i
      change _≤40*(active cutoff δ (P i) ω (t+1)).value at hbnd
      linarith [(active_valid cutoff δ (P i) ω t).1]

lemma theta_bound {δ k cw:ℝ} (hδ:0<δ) (hδu:δ≤1/1000) (hk:1≤k)
    (hcw:0 < cw) (hcwu:cw*20002≤1) (P:J→R→FilteredRanks w) (key:ℕ→Ω→K)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤k) (t:ℕ) (ω:Ω) (i:J) :
    cw*logs δ P key t ω i/(1+Real.log (k+1))≤1 := by
  have hel:0<1+Real.log (k+1):=by have h:=Real.log_nonneg (show 1≤k+1 by linarith); linarith
  apply (div_le_iff₀ hel).mpr
  have hh:=mul_le_mul_of_nonneg_left (logs_upper hδ hδu hk P key hs t ω i) hcw.le
  have hg:=mul_le_mul_of_nonneg_right hcwu hel.le
  nlinarith

end KServer.SideActualEdits

end


/-! The non-wholesale cap variation of the literal output. All endpoint
trackers are charged over all times before selecting the ordinary steps. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualOutput
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar OutputDynamics
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

lemma capScale_range {k:ℝ} (hk:1≤ k) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (t:ℕ) (ω:Ω) (i:J):capScale k P Q t ω i∈Set.Icc 0 2:=by
  have h:=(ActualCaps.scalar_errors hk).2
  dsimp only [capScale]
  split_ifs <;> constructor <;> linarith [h.1,h.2.1]

lemma cap_sum (k:ℝ) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (t:ℕ) (ω:Ω) (i:J):
    d k P Q t ω i=∑ r,FineCaps.capTerm (rho/ActualCaps.ell k) (ActualCaps.a k Q t ω)
      (capScale k P Q t ω i) (P i r) t ω:=by
  rw [←TrackedCaps.cap,TrackedCaps.cap_eq]
  simp only [d,n,flexcap,ActualCaps.flexCap,decide_eq_true_eq,capScale]

lemma cap_parameters_held (k:ℝ) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (t:ℕ) (ω:Ω) (he:reset P Q (t+1) ω=false) (i:J):
    ActualCaps.a k Q (t+1) ω=ActualCaps.a k Q t ω ∧
      capScale k P Q (t+1) ω i=capScale k P Q t ω i:=by
  have hm:=ordinary_mark P Q t ω he
  have hkey:=SideActualEdits.ordinary_key (vector cutoff ds P ω) (fun s=> key Q s ω) t
    ((reset_iff P Q t ω).mp he)
  constructor
  · change 100*(CoarseParameters.upperBeta k cutoff cb (ActualCaps.ell k) dp (key Q (t+1) ω)-3)=_
    rw [←hkey]
    rfl
  · simp only [capScale,hm]

lemma fine_step (k:ℝ) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (t:ℕ) (ω:Ω):
    (if reset P Q (t+1) ω then 0 else variation (d k P Q (t+1) ω) (d k P Q t ω))≤
      ∑ ir:J×R,FineCaps.fineVariation (rho/ActualCaps.ell k) (ActualCaps.a k Q)
        (fun s z=> capScale k P Q s z ir.1) (fun s z=> reset P Q (s+1) z) (P ir.1 ir.2) t ω:=by
  cases he:reset P Q (t+1) ω with
  | true=> simp only [he,ite_true,FineCaps.fineVariation,sum_const_zero,le_refl]
  | false=>
    simp only [he,Bool.false_eq_true,ite_false,FineCaps.fineVariation,Fintype.sum_prod_type]
    apply sum_le_sum
    intro i _
    change |d k P Q (t+1) ω i-d k P Q t ω i|≤_
    rw [cap_sum,cap_sum,←sum_sub_distrib]
    exact abs_sum_le_sum_abs _ _

lemma fine_budget {k:ℝ} (hk:1≤ k) (hw:∀ ω,0≤ w ω) (hw1:∑ ω,w ω=1)
    (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (hq:∀ t ω,size Q t ω≤ k) (N:ℕ):
    (∑ t∈range N,avg w (fun ω=> if reset P Q (t+1) ω then 0 else
      variation (d k P Q (t+1) ω) (d k P Q t ω)))≤
      2*(160/(rho/ActualCaps.ell k)+(CoreFlags.tolerance^2)⁻¹)*
        ((∑ t∈range N,avg w (fun ω=>∑ ir:J×R,|(P ir.1 ir.2).p (t+1) ω-(P ir.1 ir.2).before (t+1) ω|))+
          Fintype.card (J×R)):=by
  have hξ:0< rho/ActualCaps.ell k:=(ActualCaps.scalar_errors hk).1
  have hξh:rho/ActualCaps.ell k<1/2:=by
    have h1:=ActualCaps.ell_ge_one hk
    have hr:rho<1/2:=by norm_num [rho,lb,cb]
    apply (div_lt_iff₀ (ActualCaps.ell_pos hk)).mpr
    linarith
  have hh:=FineCaps.fine_cap_budget (J:=J×R) hw hw1 hξ hξh
    (fun _=> ActualCaps.a k Q) (fun ir s z=> capScale k P Q s z ir.1)
    (fun _ s z=> reset P Q (s+1) z)
    (fun _ s z=>(ActualCaps.ranges hk Q s z (hq s z)).2.1)
    (fun ir s z=> capScale_range hk P Q s z ir.1)
    (fun ir s z he=> cap_parameters_held k P Q s z he ir.1)
    (fun ir=> P ir.1 ir.2) N
  exact (sum_le_sum fun t _=> avg_mono hw (fine_step k P Q t)).trans hh

end KServer.ActualOutput

end


/-! Every coordinate of the actual feasible star output depends only on
observed history and on the supplied parent quota. -/


/-! The literal recursive allocation is adapted to the request filtration.
No adaptedness of the hidden offline configurations is asserted or required. -/

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Experiments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Finset

namespace KServer.FiniteExperiment
attribute [local instance] Classical.propDecidable
open Finset Episode PosteriorRanks
universe u v
variable {Y : Type u} [MetricSpace Y] [Fintype Y] {k H : ℕ} [NeZero k]

variable {T : Type v} [Fintype T]

omit [MetricSpace Y] in
lemma weight_nonneg (law : FiniteDistribution (Fin H → Y)) (tape : FiniteDistribution T)
    (ω : (Fin H → Y) × T) : 0≤weight law tape ω :=
  mul_nonneg (law.property.1 _) (tape.property.1 _)

omit [MetricSpace Y] in
lemma weight_sum (law : FiniteDistribution (Fin H → Y)) (tape : FiniteDistribution T) :
    ∑ ω,weight law tape ω=1 := by
  simp only [weight,Fintype.sum_prod_type,←mul_sum,tape.property.2,mul_one,law.property.2]

end KServer.FiniteExperiment

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_JointExperiment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The posterior counting measure is built from labeled hidden positions.
Integrating adapted metric tests is exactly conditional expectation, and
prefix quota domination is relative to this measure, not an extra premise. -/


/-! Removing null atoms preserves the literal conditional experiment. This
allows quota feasibility to be used only on positive posterior fibers. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PositiveExperiment
open RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Ω:Type} [Fintype Ω]

lemma sum_support {w:Ω→ℝ} (hw:∀ ω,0≤w ω) (f:Ω→ℝ):
    (∑ ω:Support w,weight w ω*f ω.val)=∑ ω,w ω*f ω:=by
  have hh:=Fintype.sum_subtype_add_sum_subtype (fun ω=>0<w ω) (fun ω=>w ω*f ω)
  have hz:(∑ ω:{ω:Ω // ¬0<w ω},w ω.val*f ω.val)=0:=by
    apply sum_eq_zero
    intro ω _
    have he:w ω.val=0:=le_antisymm (le_of_not_gt ω.property) (hw ω.val)
    rw [he,zero_mul]
  simpa only [hz,add_zero,weight] using hh

lemma weight_sum {w:Ω→ℝ} (hw:∀ ω,0≤w ω) (hw1:∑ ω,w ω=1):
    (∑ ω:Support w,weight w ω)=1:=by
  simpa only [mul_one] using (sum_support hw (fun _=>1)).trans (by simpa only [mul_one] using hw1)

end KServer.PositiveExperiment

end


/-! The single positive finite joint request/tape experiment for every scale.
All maps use precisely the request history and the independent finite tapes. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointExperiment
open FiniteExperiment PartitionProbabilities RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ}

variable (law:FiniteDistribution (Fin H→Y)) {r:Fin L→ℝ} (hr:∀ d,0 < r d)

lemma raw_nonneg (ω:Raw Y k H L r):0 ≤ rawWeight law hr ω:=
  FiniteExperiment.weight_nonneg law (tapeLaw (Y:=Y) (k:=k) (H:=H) hr) ω
lemma weight_sum:(∑ ω:Atom (k:=k) law hr,weight law hr ω)=1:=
  PositiveExperiment.weight_sum (raw_nonneg law hr) (FiniteExperiment.weight_sum law (tapeLaw (Y:=Y) (k:=k) (H:=H) hr))

end KServer.JointExperiment

end


/-! The dependent permanent key alphabet is genuinely finite. -/


/-! Endpoint costs on the actual schedule are charged to active size, rather
than to all inactive fixed labels. This is needed for wholesale edits. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ScheduledEndpoint
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile AllocationSchedule
open SimplexFamilies
variable {Ω J R K : Type} [Fintype Ω] [Fintype J] [DecidableEq J] [Fintype R]
variable {w : Ω → ℝ}

lemma masked_value_bound (C ell : ℝ) (d : Data J R) (p : J×R→ℝ) (a : J→ℝ) {L:ℝ}
    (hc : ∀ ir,|coefficient C ell d a ir|≤L)
    (hp : ∀ ir,p ir∈Set.Icc 0 1) :
    |(family C ell).value d p a|≤L*(∑ i,∑ r,if d.flags i r then (1:ℝ) else 0) := by
  change |0+∑ ir,coefficient C ell d a ir*p ir|≤_
  rw [zero_add]
  calc _≤∑ ir,|coefficient C ell d a ir*p ir|:= abs_sum_le_sum_abs _ _
       _≤∑ ir:J×R,L*(if d.flags ir.1 ir.2 then (1:ℝ) else 0) := by
        apply sum_le_sum
        intro ir _
        by_cases hf:d.flags ir.1 ir.2=true
        · simp only [hf,ite_true,mul_one,abs_mul,abs_of_nonneg (hp ir).1]
          exact (mul_le_mul_of_nonneg_left (hp ir).2 (abs_nonneg _)).trans (by simpa using hc ir)
        · have hz:coefficient C ell d a ir=0 := by simp [coefficient,hf]
          simp [hz,hf]
       _= _ := by rw [←mul_sum,Fintype.sum_prod_type]

lemma actual_bound {δ C ct k : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (hC : 0≤C) (hct : 0 ≤ ct) (hctu : ct*20002≤1) (hk : 1≤k)
    (P : J→R→FilteredRanks w) (key : ℕ→Ω→K)
    (hs : ∀ t ω,(∑ i,size (P i) t ω)≤k) (t:ℕ) (ω:Ω)
    (p:J×R→ℝ) (hp:∀ ir,p ir∈Set.Icc 0 1)
    (a:J→ℝ) (ha:a∈ChangingDomains.simplex (activeSet (vector cutoff δ P ω t))) :
    |(family C (1+Real.log (k+1))).value
      (StarSimplex.input hδ hδu C (1+Real.log (k+1)) ct P key t ω).data p a|≤
      520*C*(1+Real.log (k+1))*EpochSchedule.total (vector cutoff δ P ω t) := by
  have hel : 0≤1+Real.log (k+1) := by have h:=Real.log_nonneg (show 1≤k+1 by linarith); linarith
  have hL : 0≤13*C*(1+Real.log (k+1)) := by positivity
  have hh:=masked_value_bound C (1+Real.log (k+1))
    (StarSimplex.input hδ hδu C (1+Real.log (k+1)) ct P key t ω).data p a
    (ScheduledSlope.actual_bound hδ hδu hC hct hctu hk P key hs t ω a ha) hp
  have hn:(∑ i,∑ r,if (StarSimplex.input hδ hδu C (1+Real.log (k+1)) ct P key t ω).data.flags i r
      then (1:ℝ) else 0)≤40*EpochSchedule.total (vector cutoff δ P ω t) := by
    simp only [StarSimplex.input,data_flags,StarSimplex.flags]
    change (∑ i,TrackedCaps.count (P i) t ω)≤40*(∑ i,vector cutoff δ P ω t i)
    rw [mul_sum]
    exact sum_le_sum fun i _=>ScheduleEdits.count_bound hδ hδu (P i) t ω
  calc _≤13*C*(1+Real.log (k+1))*(40*EpochSchedule.total (vector cutoff δ P ω t)) :=
        hh.trans (mul_le_mul_of_nonneg_left hn hL)
       _= _ := by ring

end KServer.ScheduledEndpoint

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_ScheduleBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact structural identifications of the scheduled integral family and
bounds on the actual slack coefficients. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ScheduleShape
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile AllocationSchedule
open SimplexFamilies
variable {Ω J R K : Type} [Fintype Ω] [Fintype J] [DecidableEq J] [Fintype R]
variable {w : Ω → ℝ}

lemma eta_bound {δ ct k : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (hct : 0 ≤ ct) (hctu : ct*20002≤1) (hk : 1≤k)
    (P : J→R→FilteredRanks w) (key : ℕ→Ω→K)
    (hs : ∀ t ω,(∑ i,size (P i) t ω)≤k) (t:ℕ) (ω:Ω) (i:J) :
    ct*weight δ (vector cutoff δ P ω) (fun s=>key s ω) t i/(1+Real.log (k+1))∈Set.Icc 0 1 := by
  have hel : 0<1+Real.log (k+1) := by have h:=Real.log_nonneg (show 1≤k+1 by linarith); linarith
  constructor
  · exact div_nonneg (mul_nonneg hct (weight_nonneg δ _ _ (vector_nonneg cutoff δ P ω) t i)) hel.le
  · apply (div_le_iff₀ hel).mpr
    have h:=weight_upper hδ hδu hk (vector cutoff δ P ω) (fun s=>key s ω)
      (vector_nonneg cutoff δ P ω) (fun s=>vector_total hδ hδu P s ω (hs s ω))
      (fun s i hi=>vector_floor hδ hδu P s ω i hi) t i
    have hmul:=mul_le_mul_of_nonneg_left h hct
    have hmul2:=mul_le_mul_of_nonneg_right hctu hel.le
    nlinarith

omit [Fintype R] in
lemma regular_data {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000) (C ell ct:ℝ)
    (x:ℕ→J→ℝ) (key:ℕ→K) (hx:∀ t i,0≤x t i) (flags:ℕ→J→R→Bool) (t:ℕ)
    (hA:(activeSet (x t)).Nonempty)
    (hn:EpochSchedule.dominant (EpochSchedule.run x key t)=none)
    (hh:∀ i,1≤weight δ x key t i) :
    data hδ hδu C ell ct x key hx flags t=
      regular (activeSet (x t)) (flags t) (weight δ x key t) (fun i=>ct*weight δ x key t i/ell) hh := by
  unfold data
  dsimp only
  rw [ite_eq_left hA]
  split <;> simp_all

omit [Fintype R] in
lemma marked_data {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000) (C ell ct:ℝ)
    (x:ℕ→J→ℝ) (key:ℕ→K) (hx:∀ t i,0≤x t i) (flags:ℕ→J→R→Bool) (t:ℕ) (o:J)
    (ho:EpochSchedule.dominant (EpochSchedule.run x key t)=some o)
    (hu:0 < sideRatio δ x key t) (hu1:sideRatio δ x key t≤1)
    (hh:∀ i≠o,1≤weight δ x key t i) :
    data hδ hδu C ell ct x key hx flags t=
      marked (activeSet (x t)) (flags t) o (weight δ x key t) (fun i=>ct*weight δ x key t i/ell)
        (sideRatio δ x key t) hu hu1 hh := by
  have hA:(activeSet (x t)).Nonempty:=⟨o,marked_active x key hx t ho⟩
  unfold data
  dsimp only
  rw [ite_eq_left hA]
  split <;> simp_all

end KServer.ScheduleShape

end


/- Deterministic scheduled-simplex payments use raw ranks before parameter edits. -/


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ScheduledPayment
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile AllocationSchedule
open SimplexFamilies AdaptiveAllocation ScheduleShape
variable {Ω J R K : Type} [Fintype Ω] [Fintype J] [DecidableEq J] [Fintype R]
variable {w : Ω → ℝ}

lemma ordinary_regular {δ C ct k : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (hC : 0<C) (hct : 0 < ct) (hctu : ct*20002≤1) (hgap:700<C*ct) (hk : 1≤k)
    (P : J→R→FilteredRanks w) (key : ℕ→Ω→K)
    (hs : ∀ t ω,(∑ i,size (P i) t ω)≤k) (t:ℕ) (ω:Ω)
    (he:epoch (vector cutoff δ P ω) (fun s=>key s ω) t=
      epoch (vector cutoff δ P ω) (fun s=>key s ω) (t+1))
    (hA:(activeSet (vector cutoff δ P ω t)).Nonempty)
    (hB:(activeSet (vector cutoff δ P ω (t+1))).Nonempty)
    (hn:EpochSchedule.dominant (EpochSchedule.run (vector cutoff δ P ω) (fun s=>key s ω) t)=none) :
    let ell:=1+Real.log (k+1)
    let d:=StarSimplex.input hδ hδu C ell ct P key
    let a:=StarSimplex.proportion hδ hδu C ell ct P key
    CausalSimplex.mass (d (t+1) ω)*ChangingDomains.variation (a (t+1) ω) (a t ω)≤
      (family C ell).value (d t ω).data (d (t+1) ω).ranks (a t ω)-
      (family C ell).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)+
      (6*C*ell+4)*ChangingDomains.changedFlags (StarSimplex.flags P ω t) (StarSimplex.flags P ω (t+1))+
      320*C*ell*(∑ i,CoarseSchedule.charge (active cutoff δ (P i) ω t) (active cutoff δ (P i) ω (t+1))) := by
  intro ell d a
  let x:=vector cutoff δ P ω
  let ky:=fun s=>key s ω
  let h:=weight δ x ky t
  let h':=weight δ x ky (t+1)
  let f:=StarSimplex.flags P ω t
  let g:=StarSimplex.flags P ω (t+1)
  let A:=activeSet (x t)
  let B:=activeSet (x (t+1))
  have hel:0<ell := by have hlog:=Real.log_nonneg (show 1≤k+1 by linarith); dsimp [ell]; linarith
  change EpochSchedule.dominant (EpochSchedule.run x ky t)=none at hn
  have hn':EpochSchedule.dominant (EpochSchedule.run x ky (t+1))=none :=
    (ScheduleEdits.ordinary_mark x ky t he).trans hn
  have hh:∀ i,1≤h i := fun i=>weight_regular_one δ x ky t i (by simp [hn])
  have hh':∀ i,1≤h' i := fun i=>weight_regular_one δ x ky (t+1) i (by simp [hn'])
  have heta:∀ i,ct*h i/ell∈Set.Icc 0 1 := eta_bound hδ hδu hct.le hctu hk P key hs t ω
  have heta':∀ i,ct*h' i/ell∈Set.Icc 0 1 := eta_bound hδ hδu hct.le hctu hk P key hs (t+1) ω
  have ht:=regular_exp_sum δ x ky (vector_nonneg cutoff δ P ω) t
    (ScheduledSimplex.nonempty_mass x ky (vector_nonneg cutoff δ P ω) t hA) hn
  have hgp:2*(25+32*(2:ℝ))*(1+1)<C*ct := by linarith
  have hold:(d t ω).data=regular A f h (fun i=>ct*h i/ell) hh :=
    regular_data hδ hδu C ell ct x ky (vector_nonneg cutoff δ P ω) (StarSimplex.flags P ω) t hA hn hh
  have hnew:(d (t+1) ω).data=regular B g h' (fun i=>ct*h' i/ell) hh' :=
    regular_data hδ hδu C ell ct x ky (vector_nonneg cutoff δ P ω) (StarSimplex.flags P ω) (t+1) hB hn' hh'
  have hp:∀ ir,(d (t+1) ω).ranks ir∈Set.Icc 0 1 := fun ir=>(P ir.1 ir.2).range (t+1) ω
  have hf:∀ i∉A,∀ r,f i r=false := fun i hi r=>flags_supported hδ hδu P t ω i hi r
  have hg:∀ i∉B,∀ r,g i r=false := fun i hi r=>flags_supported hδ hδu P (t+1) ω i hi r
  have ha:a t ω∈ChangingDomains.simplex A := StarSimplex.proportion_mem hδ hδu C ell ct P key t ω
  have ha':a (t+1) ω∈ChangingDomains.simplex B := StarSimplex.proportion_mem hδ hδu C ell ct P key (t+1) ω
  have hstep:a (t+1) ω=regularStep C ell ct A B g h h' hh hh' (d (t+1) ω).ranks (a t ω) :=
    CausalSimplex.regular_successor d t ω hA hB f g h h' hh hh' hC hel hct
      (fun i _=>(heta i).2) (by norm_num : (0:ℝ)≤2) ht hgp (fun ir=>(hp ir).1) hold hnew he
  have hpay:=regular_step_payment hA hB f g h h' hh hh' hC hel hct heta heta'
    (fun i _=>(heta i).2) (by norm_num : (0:ℝ)≤2) ht hgp (d (t+1) ω).ranks hp hf hg (a t ω) ha
  dsimp only at hpay
  rw [←hstep] at hpay
  have hv0: (family C ell).value (d t ω).data (d (t+1) ω).ranks (a t ω)=
      potential C ell (regular A f h (fun i=>ct*h i/ell) hh)
        (core (regular A f h (fun i=>ct*h i/ell) hh) (d (t+1) ω).ranks) (a t ω) := by
    rw [hold]
    exact value_eq C ell _ _ _ ha
  have hv1: (family C ell).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)=
      potential C ell (regular B g h' (fun i=>ct*h' i/ell) hh')
        (core (regular B g h' (fun i=>ct*h' i/ell) hh') (d (t+1) ω).ranks) (a (t+1) ω) := by
    rw [hnew]
    exact value_eq C ell _ _ _ ha'
  have hc:=ScheduleEdits.regular_charge hδ hδu P key t ω he (d (t+1) ω).ranks hp univ
    (fun i _=>by rw [hn]; simp)
  change (∑ i,if h i=h' i then 0 else preparedInput A B g (d (t+1) ω).ranks i)≤
    40*(∑ i,CoarseSchedule.charge (active cutoff δ (P i) ω t) (active cutoff δ (P i) ω (t+1))) at hc
  have hcn:0≤8*C*ell := by positivity
  have hc':=mul_le_mul_of_nonneg_left hc hcn
  rw [hv0,hv1]
  change (∑ i,core (d (t+1) ω).data (d (t+1) ω).ranks i)*_≤_
  rw [hnew]
  nlinarith


lemma ordinary_marked {δ C ct k : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (hC : 0<C) (hct : 0 < ct) (hctu : ct*20002≤1) (hgap:700<C*ct) (hk : 1≤k)
    (P : J→R→FilteredRanks w) (key : ℕ→Ω→K)
    (hs : ∀ t ω,(∑ i,size (P i) t ω)≤k) (t:ℕ) (ω:Ω)
    (he:epoch (vector cutoff δ P ω) (fun s=>key s ω) t=
      epoch (vector cutoff δ P ω) (fun s=>key s ω) (t+1)) (o:J)
    (ho:EpochSchedule.dominant (EpochSchedule.run (vector cutoff δ P ω) (fun s=>key s ω) t)=some o)
    (hu:0 < sideRatio δ (vector cutoff δ P ω) (fun s=>key s ω) t)
    (hu':0 < sideRatio δ (vector cutoff δ P ω) (fun s=>key s ω) (t+1)) :
    let ell:=1+Real.log (k+1)
    let x:=vector cutoff δ P ω
    let ky:=fun s=>key s ω
    let d:=StarSimplex.input hδ hδu C ell ct P key
    let a:=StarSimplex.proportion hδ hδu C ell ct P key
    CausalSimplex.mass (d (t+1) ω)*ChangingDomains.variation (a (t+1) ω) (a t ω)≤
      (family C ell).value (d t ω).data (d (t+1) ω).ranks (a t ω)-
      (family C ell).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)+
      (26*C*ell+4)*ChangingDomains.changedFlags (StarSimplex.flags P ω t) (StarSimplex.flags P ω (t+1))+
      320*C*ell*(∑ i∈univ.erase o,CoarseSchedule.charge (active cutoff δ (P i) ω t) (active cutoff δ (P i) ω (t+1)))+
      2976*C*ell*CoarseSide.charge δ (CoarseSide.sideInput x ky) (CoarseSide.epochReset x ky) t := by
  intro ell x ky d a
  let h:=weight δ x ky t
  let h':=weight δ x ky (t+1)
  let u:=sideRatio δ x ky t
  let u':=sideRatio δ x ky (t+1)
  let f:=StarSimplex.flags P ω t
  let g:=StarSimplex.flags P ω (t+1)
  let A:=activeSet (x t)
  let B:=activeSet (x (t+1))
  have hxn:=vector_nonneg cutoff δ P ω
  have hel:0<ell := by have hlog:=Real.log_nonneg (show 1≤k+1 by linarith); dsimp [ell]; linarith
  change EpochSchedule.dominant (EpochSchedule.run x ky t)=some o at ho
  have ho':EpochSchedule.dominant (EpochSchedule.run x ky (t+1))=some o :=
    (ScheduleEdits.ordinary_mark x ky t he).trans ho
  have hA:o∈A:=marked_active x ky hxn t ho
  have hB:B.Nonempty:=⟨o,marked_active x ky hxn (t+1) ho'⟩
  have hh:∀ i≠o,1≤h i := fun i hi=>weight_regular_one δ x ky t i (by rw [ho]; simpa [eq_comm] using hi)
  have hh':∀ i≠o,1≤h' i := fun i hi=>weight_regular_one δ x ky (t+1) i (by rw [ho']; simpa [eq_comm] using hi)
  have heta:∀ i,ct*h i/ell∈Set.Icc 0 1 := eta_bound hδ hδu hct.le hctu hk P key hs t ω
  have heta':∀ i,ct*h' i/ell∈Set.Icc 0 1 := eta_bound hδ hδu hct.le hctu hk P key hs (t+1) ω
  have hu1:u≤1:= (side_ratio_upper hδ hδu x ky hxn t ho).trans (by norm_num)
  have hu1':u'≤1:= (side_ratio_upper hδ hδu x ky hxn (t+1) ho').trans (by norm_num)
  have how:h o=u:=marked_weight δ x ky t o ho
  have how':h' o=u':=marked_weight δ x ky (t+1) o ho'
  have hside:∀ i∈A,i≠o→(1/2:ℝ)*(1+Real.log (1/u))≤h i :=
    fun i hi hio=>weight_side_lower hδ hδu x ky hxn t ho hi hio hu
  have ht:=side_exp_sum hδ hδu x ky hxn t ho
  have hgp:2*((25*(1/2:ℝ)+2+32*2)/(1/2))*(1+1)<C*ct := by linarith
  have hold:(d t ω).data=marked A f o h (fun i=>ct*h i/ell) u hu hu1 hh :=
    marked_data hδ hδu C ell ct x ky hxn (StarSimplex.flags P ω) t o ho hu hu1 hh
  have hnew:(d (t+1) ω).data=marked B g o h' (fun i=>ct*h' i/ell) u' hu' hu1' hh' :=
    marked_data hδ hδu C ell ct x ky hxn (StarSimplex.flags P ω) (t+1) o ho' hu' hu1' hh'
  have hp:∀ ir,(d (t+1) ω).ranks ir∈Set.Icc 0 1 := fun ir=>(P ir.1 ir.2).range (t+1) ω
  have hf:∀ i∉A,∀ r,f i r=false := fun i hi r=>flags_supported hδ hδu P t ω i hi r
  have hg:∀ i∉B,∀ r,g i r=false := fun i hi r=>flags_supported hδ hδu P (t+1) ω i hi r
  have ha:a t ω∈ChangingDomains.simplex A := StarSimplex.proportion_mem hδ hδu C ell ct P key t ω
  have ha':a (t+1) ω∈ChangingDomains.simplex B := StarSimplex.proportion_mem hδ hδu C ell ct P key (t+1) ω
  have hstep:a (t+1) ω=markedStep C ell ct A B g o h h' u u' hu hu1 hu' hu1' hh hh' (d (t+1) ω).ranks (a t ω) :=
    CausalSimplex.marked_successor d t ω hA hB f g h h' hu hu1 hu' hu1' how hh hh' hC hel hct
      (fun i _=>(heta i).2) (by norm_num : (0:ℝ)≤2) (by norm_num : (0:ℝ)<1/2)
      (by norm_num) hside ht hgp (fun ir=>(hp ir).1) hold hnew he
  have hcte:ct≤ell:=by have hlog:=Real.log_nonneg (show 1≤k+1 by linarith); dsimp [ell]; linarith
  have hote:ct*u/ell≤u:= (div_le_iff₀ hel).mpr (by nlinarith)
  have hote':ct*u'/ell≤u':= (div_le_iff₀ hel).mpr (by nlinarith)
  have hpay:=marked_step_payment hA hB f g h h' hu hu1 hu' hu1' how how' hh hh' hC hel hct heta heta'
    hote hote' (fun i _=>(heta i).2) (by norm_num : (0:ℝ)≤2) (by norm_num : (0:ℝ)<1/2)
    (by norm_num) hside ht hgp (d (t+1) ω).ranks hp hf hg (a t ω) ha
  dsimp only at hpay
  rw [←hstep] at hpay
  have hv0: (family C ell).value (d t ω).data (d (t+1) ω).ranks (a t ω)=
      potential C ell (marked A f o h (fun i=>ct*h i/ell) u hu hu1 hh)
        (core (marked A f o h (fun i=>ct*h i/ell) u hu hu1 hh) (d (t+1) ω).ranks) (a t ω) := by
    rw [hold]
    exact value_eq C ell _ _ _ ha
  have hv1: (family C ell).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)=
      potential C ell (marked B g o h' (fun i=>ct*h' i/ell) u' hu' hu1' hh')
        (core (marked B g o h' (fun i=>ct*h' i/ell) u' hu' hu1' hh') (d (t+1) ω).ranks) (a (t+1) ω) := by
    rw [hnew]
    exact value_eq C ell _ _ _ ha'
  have hc:=ScheduleEdits.regular_charge hδ hδu P key t ω he (d (t+1) ω).ranks hp (univ.erase o)
    (fun i hi=>by rw [ho]; simpa [eq_comm] using (mem_erase.mp hi).1)
  have huq:=ScheduleEdits.side_ratio_charge hδ hδu x ky hxn t he o ho
    (preparedInput A B g (d (t+1) ω).ranks)
    (ScheduleEdits.prepared_input_bound hδ hδu P A (t+1) ω (d (t+1) ω).ranks hp)
  have hc':=mul_le_mul_of_nonneg_left hc (by positivity : 0≤8*C*ell)
  have huq':=mul_le_mul_of_nonneg_left huq (by positivity : 0≤24*C*ell)
  rw [hv0,hv1]
  change (∑ i,core (d (t+1) ω).data (d (t+1) ω).ranks i)*_≤_
  rw [hnew]
  nlinarith

end KServer.ScheduledPayment

end


/-! Actual singleton/side-free transitions: their cost is paid by changed
flags, not by a fresh charge to the persistent dominant mass. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.SingletonPayment
attribute [local instance] Classical.propDecidable
open SimplexFamilies AdaptiveAllocation
variable {J R : Type} [Fintype J] [DecidableEq J] [Fintype R]

lemma point_mem (o:J) {A:Finset J} (ho:o∈A) : point o∈ChangingDomains.simplex A := by
  refine ⟨fun i=>by unfold point; split_ifs <;> norm_num,?_,?_⟩
  · simp [point,ite_eq_left (show A.Nonempty from ⟨o,ho⟩)]
  · intro i hi
    have hn:i≠o:=fun he=>hi (he ▸ ho)
    simp [point,hn]

lemma singleton_eq {o:J} {a:J→ℝ} (ha:a∈ChangingDomains.simplex {o}) : a=point o := by
  have hz:∀ i,i≠o→a i=0:=fun i hi=>ha.2.2 i (by simpa using hi)
  have hs:(∑ i,a i)=a o := sum_eq_single o (fun i _ hi=>hz i hi) (by simp)
  have ho:a o=1:=by simpa only [hs,singleton_nonempty,ite_true] using ha.2.1
  funext i
  by_cases hi:i=o
  · subst i; simp [point,ho]
  · simp [point,hi,hz i hi]

lemma zero_value (C ell:ℝ) (d:Data J R) (p:J×R→ℝ) (a:J→ℝ)
    (hz:d.zeroPotential=true) : (family C ell).value d p a=0 := by
  simp [AdaptiveMinimization.Family.value,family,coefficient,hz]

lemma base_value (C ell:ℝ) (d:Data J R) (p:J×R→ℝ) :
    (family C ell).value d p d.base=0 := by
  simp [AdaptiveMinimization.Family.value,family,coefficient,K,Z]

lemma core_value_bound (C ell:ℝ) (d:Data J R) (p:J×R→ℝ) (a:J→ℝ) {L:ℝ}
    (hc:∀ ir,|coefficient C ell d a ir|≤L) (hp:∀ ir,0≤p ir) :
    |(family C ell).value d p a|≤L*(∑ i,core d p i) := by
  change |0+∑ ir,coefficient C ell d a ir*p ir|≤_
  rw [zero_add]
  calc _≤∑ ir,|coefficient C ell d a ir*p ir|:=abs_sum_le_sum_abs _ _
       _≤∑ ir:J×R,L*(if d.flags ir.1 ir.2 then p ir else 0) := by
        apply sum_le_sum
        intro ir _
        by_cases hf:d.flags ir.1 ir.2=true
        · simp only [hf,ite_true,abs_mul,abs_of_nonneg (hp ir)]
          exact mul_le_mul_of_nonneg_right (hc ir) (hp ir)
        · have hz:coefficient C ell d a ir=0:=by simp [coefficient,hf]
          simp [hz,hf]
       _= _ := by rw [←mul_sum,Fintype.sum_prod_type]; rfl

lemma candidate_singleton (C ell:ℝ) (old new:Data J R) (o:J)
    (hA:old.active={o}) (p:J×R→ℝ) (a:J→ℝ) :
    CausalSimplex.candidate C ell old new p a=
      ChangingDomains.transposeSimplex new.active (∑ i,core (CausalSimplex.prepared old new) p i) (point o) := by
  have hm := (family C ell).update_mem (CausalSimplex.prepared old new) p
    (∑ i,core (CausalSimplex.prepared old new) p i) a
  change CausalSimplex.prepare C ell old new p a∈ChangingDomains.simplex old.active at hm
  rw [hA] at hm
  exact congrArg (ChangingDomains.transposeSimplex new.active _) (singleton_eq hm)

lemma old_singleton {C ell L:ℝ} (hL:0≤L) (old new:CausalSimplex.Input J R)
    (o:J) (hA:old.data.active={o}) (ho:o∈new.data.active)
    (he:old.epoch=new.epoch) (hz:old.data.zeroPotential=true)
    (p:J×R→ℝ) (hp:∀ ir,p ir∈Set.Icc 0 1)
    (hf:∀ i∉old.data.active,∀ r,old.data.flags i r=false)
    (hg:∀ i∉new.data.active,∀ r,new.data.flags i r=false)
    (hbase:(family C ell).value new.data p (point o)=0)
    (hcoeff:∀ a,a∈ChangingDomains.simplex new.data.active→∀ ir,|coefficient C ell new.data a ir|≤L)
    (a:J→ℝ) (ha:a∈ChangingDomains.simplex old.data.active) :
    let S:=∑ i,core new.data p i
    let b:=CausalSimplex.move C ell old new p a
    let c:=(family C ell).update new.data p S b
    S*ChangingDomains.variation c a≤
      (family C ell).value old.data p a-(family C ell).value new.data p c+
      (L+2)*ChangingDomains.changedFlags old.data.flags new.data.flags := by
  intro S b c
  have hae:a=point o:=singleton_eq (hA ▸ ha)
  have hB:new.data.active.Nonempty:=⟨o,ho⟩
  let T:=∑ i,core (CausalSimplex.prepared old.data new.data) p i
  have hcand:=candidate_singleton C ell old.data new.data o hA p a
  have hcm:CausalSimplex.candidate C ell old.data new.data p a∈ChangingDomains.simplex new.data.active := by
    rw [hcand]
    unfold ChangingDomains.transposeSimplex
    split_ifs
    · exact ChangingDomains.canonical_mem _
    · exact point_mem o ho
  have hb:b=ChangingDomains.transposeSimplex new.data.active T (point o) := by
    change CausalSimplex.move C ell old new p a=_
    rw [CausalSimplex.move,ite_eq_left he,ite_eq_left hcm,hcand]
  have hbm:b∈ChangingDomains.simplex new.data.active:=CausalSimplex.move_mem C ell old new p a
  have hSn:0≤S:=sum_nonneg fun i _=>ChangingDomains.core_nonneg (fun i r=>(hp (i,r)).1) i
  have hpay: S*ChangingDomains.variation c b≤
      (family C ell).value new.data p b-(family C ell).value new.data p c :=
    (family C ell).update_payment new.data p S hbm
  have hvold:=zero_value C ell old.data p a hz
  rw [hvold]
  by_cases ht:T=0
  · have herr:= (ChangingDomains.synthetic_errors (fun i r=>hp (i,r)) hf hg).2
    have hdiff:=le_of_abs_le ((total_variation_bound (core new.data p)
      (core (CausalSimplex.prepared old.data new.data) p)).trans herr)
    change S-T≤ChangingDomains.changedFlags old.data.flags new.data.flags at hdiff
    rw [ht,sub_zero] at hdiff
    have hv: (family C ell).value new.data p b≤L*S :=
      (le_abs_self _).trans (core_value_bound C ell new.data p b (hcoeff b hbm) (fun ir=>(hp ir).1))
    have htri:=mul_le_mul_of_nonneg_left (ChangingDomains.variation_triangle c b a) hSn
    have hvar:=mul_le_mul_of_nonneg_left (ChangingDomains.simplex_variation hbm ha) hSn
    have hmul:=mul_le_mul_of_nonneg_left hdiff (show 0≤L+2 by linarith)
    nlinarith
  · have hba:b=a:=by rw [hb,ChangingDomains.transposeSimplex,ite_eq_right ht,hae]
    rw [hba] at hpay
    rw [hae,hbase] at hpay
    rw [hae]
    have hfn:0≤ChangingDomains.changedFlags old.data.flags new.data.flags := by
      apply sum_nonneg
      intro i _
      apply sum_nonneg
      intro r _
      split_ifs <;> norm_num
    nlinarith [mul_nonneg (show 0≤L+2 by linarith) hfn]

end KServer.SingletonPayment

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.SingletonPayment
attribute [local instance] Classical.propDecidable
open SimplexFamilies AdaptiveAllocation
variable {J R : Type} [Fintype J] [DecidableEq J] [Fintype R]

omit [Fintype R] in
lemma marked_point_potential (A : Finset J) (f : J→R→Bool) (o:J) (h eta:J→ℝ)
    {u:ℝ} (hu:0<u) (hu1:u≤1) (hh:∀ i≠o,1≤h i) (C ell:ℝ) (v:J→ℝ) :
    potential C ell (marked A f o h eta u hu hu1 hh) v (point o)=0 := by
  simp [potential,marked,SimplexAnalytic.primitive,point]

lemma new_singleton {A:Finset J} {o:J} (hoA:o∈A)
    (f g:J→R→Bool) (h:J→ℝ) {u:ℝ} (hu:0<u) (hu1:u≤1)
    (ho:h o=u) (hh:∀ i≠o,1≤h i)
    {C ell ct ηmax Cexp c:ℝ} (hC:0<C) (hl:0<ell) (hc:0 < ct)
    (he:∀ i,ct*h i/ell∈Set.Icc 0 1)
    (hmax:∀ i∈A,ct*h i/ell≤ηmax) (hCexp:0≤Cexp)
    (hsideC:0 < c) (hsideC1:c≤1)
    (hside:∀ i∈A,i≠o→c*(1+Real.log (1/u))≤h i)
    (htail:∑ i∈A.erase o,Real.exp (-h i)≤Cexp*u)
    (hgap:2*((25*c+2+32*Cexp)/c)*(1+ηmax)<C*ct)
    (p:J×R→ℝ) (hp:∀ ir,p ir∈Set.Icc 0 1)
    (hf:∀ i∉A,∀ r,f i r=false) (hg:∀ i∉({o}:Finset J),∀ r,g i r=false)
    (a:J→ℝ) (ha:a∈ChangingDomains.simplex A) :
    let d0:=marked A f o h (fun i=>ct*h i/ell) u hu hu1 hh
    (∑ i,ChangingDomains.core g (fun i r=>p (i,r)) i)*ChangingDomains.variation (point o) a≤
      potential C ell d0 (core d0 p) a+(13*C*ell+4)*ChangingDomains.changedFlags f g := by
  intro d0
  let B:=({o}:Finset J)
  let v:=preparedInput A B g p
  let d1:=marked A (preparedFlags A B g) o h (fun i=>ct*h i/ell) u hu hu1 hh
  let a1:=markedPrepare C ell ct A B g o h u hu hu1 hh p a
  let a2:=markedTransport C ell ct A B g o h u hu hu1 hh p a
  let S:=∑ i,v i
  let T:=∑ i,ChangingDomains.core g (fun i r=>p (i,r)) i
  have hv:∀ i,0≤v i:=fun i=>ChangingDomains.core_nonneg (fun i r=>(hp (i,r)).1) i
  have hSn:0≤S:=sum_nonneg fun i _=>hv i
  have hB:B.Nonempty:=singleton_nonempty o
  have ha1:a1∈ChangingDomains.simplex A := (family C ell).update_mem d1 p S a
  have ha2:a2∈ChangingDomains.simplex B:=marked_transport_mem hoA hB g h hu hu1 ho hh
    hC hl hc hmax hCexp hsideC hsideC1 hside htail hgap p (fun ir=>(hp ir).1) a ha
  have hae:a2=point o:=singleton_eq ha2
  have ht:potential C ell d0 v a2=potential C ell d0 v a1 :=
    marked_transpose_value A B f o h (fun i=>ct*h i/ell) hu hu1 hh C ell v a1 hv
  have hz:potential C ell d0 v a2=0 := by
    rw [hae]
    exact marked_point_potential A f o h (fun i=>ct*h i/ell) hu hu1 hh C ell v
  have hpay:S*ChangingDomains.variation a1 a≤potential C ell d0 v a := by
    have hp1:=literal_update_payment C ell d1 p S ha
    change S*ChangingDomains.variation a1 a≤potential C ell d0 v a-potential C ell d0 v a1 at hp1
    rw [←ht,hz,sub_zero] at hp1
    exact hp1
  have herr:=ChangingDomains.synthetic_errors (fun i r=>hp (i,r)) hf hg
  have hi:=marked_input_bound A ⟨o,hoA⟩ f o h (fun i=>ct*h i/ell) hu hu1 hh he hC.le hl.le
    (B:=core d0 p) (B':=v) ha
  have hdelta:=mul_le_mul_of_nonneg_left herr.1 (by positivity : 0≤13*C*ell)
  have hzero:S*ChangingDomains.variation a2 a1=0:=ChangingDomains.transposeSimplex_payment B S a1
  have hST:S≤T:=sub_nonneg.mp (ChangingDomains.synthetic_total (A:=A) (B:=B) (g:=g) (fun i r=>(hp (i,r)).1))
  have hdiff:T-S≤ChangingDomains.changedFlags f g :=
    (le_abs_self _).trans ((total_variation_bound (ChangingDomains.core g (fun i r=>p (i,r))) v).trans herr.2)
  have hm:=ChangingDomains.prepared_weight_comparison ha ha1 ha2 hSn hST hzero (a₃:=a2)
  rw [ChangingDomains.variation_self,mul_zero,add_zero,hae] at hm
  have hlow:=neg_le_of_abs_le hi
  change -(13*C*ell*ChangingDomains.variation (core d0 p) v)≤
    potential C ell d0 (core d0 p) a-potential C ell d0 v a at hlow
  change 13*C*ell*ChangingDomains.variation (core d0 p) v≤
    13*C*ell*ChangingDomains.changedFlags f g at hdelta
  change T*ChangingDomains.variation (point o) a≤_
  nlinarith

end KServer.SingletonPayment

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ScheduledPayment
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile AllocationSchedule
open SimplexFamilies AdaptiveAllocation ScheduleShape SingletonPayment
variable {Ω J R K : Type} [Fintype Ω] [Fintype J] [DecidableEq J] [Fintype R]
variable {w : Ω→ℝ}

omit [Fintype Ω] [Fintype R] in
lemma marked_zero_flag {δ:ℝ} (hδ:0<δ) (hδu:δ≤1/1000) (C ell ct:ℝ)
    (x:ℕ→J→ℝ) (key:ℕ→K) (hx:∀ t i,0≤x t i) (flags:ℕ→J→R→Bool)
    (t:ℕ) (o:J) (ho:EpochSchedule.dominant (EpochSchedule.run x key t)=some o)
    (hu:sideRatio δ x key t=0) :
    (data hδ hδu C ell ct x key hx flags t).zeroPotential=true := by
  have hA:(activeSet (x t)).Nonempty:=⟨o,marked_active x key hx t ho⟩
  unfold data
  dsimp only
  rw [ite_eq_left hA]
  split <;> simp_all [zeroData]

omit [Fintype Ω] in
lemma marked_point_value {δ:ℝ} (hδ:0<δ) (hδu:δ≤1/1000) (C ell ct:ℝ)
    (x:ℕ→J→ℝ) (key:ℕ→K) (hx:∀ t i,0≤x t i) (flags:ℕ→J→R→Bool)
    (t:ℕ) (o:J) (ho:EpochSchedule.dominant (EpochSchedule.run x key t)=some o)
    (p:J×R→ℝ) :
    (family C ell).value (data hδ hδu C ell ct x key hx flags t) p (point o)=0 := by
  by_cases hu:0 < sideRatio δ x key t
  · have hu1:sideRatio δ x key t≤1:=(side_ratio_upper hδ hδu x key hx t ho).trans (by norm_num)
    have hh:∀ i≠o,1≤weight δ x key t i:=fun i hi=>weight_regular_one δ x key t i (by rw [ho]; simpa [eq_comm] using hi)
    rw [marked_data hδ hδu C ell ct x key hx flags t o ho hu hu1 hh]
    exact base_value C ell _ p
  · have hz:sideRatio δ x key t=0:=le_antisymm (le_of_not_gt hu) (side_ratio_nonneg δ x key hx t)
    exact zero_value C ell _ p _ (marked_zero_flag hδ hδu C ell ct x key hx flags t o ho hz)

lemma ordinary_old_zero {δ C ct k:ℝ} (hδ:0<δ) (hδu:δ≤1/1000)
    (hC:0≤C) (hct:0 ≤ ct) (hctu:ct*20002≤1) (hk:1≤k)
    (P:J→R→FilteredRanks w) (key:ℕ→Ω→K)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤k) (t:ℕ) (ω:Ω)
    (he:epoch (vector cutoff δ P ω) (fun s=>key s ω) t=
      epoch (vector cutoff δ P ω) (fun s=>key s ω) (t+1)) (o:J)
    (ho:EpochSchedule.dominant (EpochSchedule.run (vector cutoff δ P ω) (fun s=>key s ω) t)=some o)
    (hu:sideRatio δ (vector cutoff δ P ω) (fun s=>key s ω) t=0) :
    let ell:=1+Real.log (k+1)
    let d:=StarSimplex.input hδ hδu C ell ct P key
    let a:=StarSimplex.proportion hδ hδu C ell ct P key
    CausalSimplex.mass (d (t+1) ω)*ChangingDomains.variation (a (t+1) ω) (a t ω)≤
      (family C ell).value (d t ω).data (d (t+1) ω).ranks (a t ω)-
      (family C ell).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)+
      (13*C*ell+2)*ChangingDomains.changedFlags (StarSimplex.flags P ω t) (StarSimplex.flags P ω (t+1)) := by
  intro ell d a
  let x:=vector cutoff δ P ω
  let ky:=fun s=>key s ω
  have hxn:=vector_nonneg cutoff δ P ω
  have hel:0≤ell:=by have hlog:=Real.log_nonneg (show 1≤k+1 by linarith); dsimp [ell]; linarith
  have ho':EpochSchedule.dominant (EpochSchedule.run x ky (t+1))=some o:=
    (ScheduleEdits.ordinary_mark x ky t he).trans ho
  have hA:(d t ω).data.active={o}:=(data_active hδ hδu C ell ct x ky hxn (StarSimplex.flags P ω) t).trans
    (marked_zero_singleton hδ x ky hxn t ho hu)
  have hoB:o∈(d (t+1) ω).data.active:=by
    change o∈(data hδ hδu C ell ct x ky hxn (StarSimplex.flags P ω) (t+1)).active
    rw [data_active]
    exact marked_active x ky hxn (t+1) ho'
  have hz:(d t ω).data.zeroPotential=true:=marked_zero_flag hδ hδu C ell ct x ky hxn (StarSimplex.flags P ω) t o ho hu
  have hp:∀ ir,(d (t+1) ω).ranks ir∈Set.Icc 0 1:=fun ir=>(P ir.1 ir.2).range (t+1) ω
  have hf:∀ i∉(d t ω).data.active,∀ r,(d t ω).data.flags i r=false:=by
    change ∀ i∉(data hδ hδu C ell ct x ky hxn (StarSimplex.flags P ω) t).active,∀ r,_=false
    simp only [data_active]
    intro i hi r
    change (data hδ hδu C ell ct x ky hxn (StarSimplex.flags P ω) _).flags i r=false
    rw [data_flags]
    exact flags_supported hδ hδu P t ω i hi r
  have hg:∀ i∉(d (t+1) ω).data.active,∀ r,(d (t+1) ω).data.flags i r=false:=by
    change ∀ i∉(data hδ hδu C ell ct x ky hxn (StarSimplex.flags P ω) (t+1)).active,∀ r,_=false
    simp only [data_active]
    intro i hi r
    change (data hδ hδu C ell ct x ky hxn (StarSimplex.flags P ω) _).flags i r=false
    rw [data_flags]
    exact flags_supported hδ hδu P (t+1) ω i hi r
  have hcoeff:∀ b,b∈ChangingDomains.simplex (d (t+1) ω).data.active→∀ ir,|coefficient C ell (d (t+1) ω).data b ir|≤13*C*ell := by
    intro b hb
    have hm:(d (t+1) ω).data.active=activeSet (x (t+1)):=data_active hδ hδu C ell ct x ky hxn (StarSimplex.flags P ω) (t+1)
    exact ScheduledSlope.actual_bound hδ hδu hC hct hctu hk P key hs (t+1) ω b (hm ▸ hb)
  have hb: (family C ell).value (d (t+1) ω).data (d (t+1) ω).ranks (point o)=0 :=
    marked_point_value hδ hδu C ell ct x ky hxn (StarSimplex.flags P ω) (t+1) o ho' _
  have ha:a t ω∈ChangingDomains.simplex (d t ω).data.active:=CausalSimplex.run_mem C ell d t ω
  have hpay:=old_singleton (by positivity : 0≤13*C*ell) (d t ω) (d (t+1) ω) o hA hoB he hz _ hp hf hg hb hcoeff _ ha
  have hsuc:a (t+1) ω=(family C ell).update (d (t+1) ω).data (d (t+1) ω).ranks
      (CausalSimplex.mass (d (t+1) ω))
      (CausalSimplex.move C ell (d t ω) (d (t+1) ω) (d (t+1) ω).ranks (a t ω)) :=
    CausalSimplex.run_successor C ell d t ω
  rw [hsuc]
  have hf0:(d t ω).data.flags=StarSimplex.flags P ω t:=data_flags hδ hδu C ell ct x ky hxn (StarSimplex.flags P ω) t
  have hf1:(d (t+1) ω).data.flags=StarSimplex.flags P ω (t+1):=data_flags hδ hδu C ell ct x ky hxn (StarSimplex.flags P ω) (t+1)
  simpa only [CausalSimplex.mass,hf0,hf1] using hpay


lemma ordinary_new_zero {δ C ct k:ℝ} (hδ:0<δ) (hδu:δ≤1/1000)
    (hC:0<C) (hct:0 < ct) (hctu:ct*20002≤1) (hgap:700<C*ct) (hk:1≤k)
    (P:J→R→FilteredRanks w) (key:ℕ→Ω→K)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤k) (t:ℕ) (ω:Ω)
    (he:epoch (vector cutoff δ P ω) (fun s=>key s ω) t=
      epoch (vector cutoff δ P ω) (fun s=>key s ω) (t+1)) (o:J)
    (ho:EpochSchedule.dominant (EpochSchedule.run (vector cutoff δ P ω) (fun s=>key s ω) t)=some o)
    (hu:0 < sideRatio δ (vector cutoff δ P ω) (fun s=>key s ω) t)
    (hu':sideRatio δ (vector cutoff δ P ω) (fun s=>key s ω) (t+1)=0) :
    let ell:=1+Real.log (k+1)
    let d:=StarSimplex.input hδ hδu C ell ct P key
    let a:=StarSimplex.proportion hδ hδu C ell ct P key
    CausalSimplex.mass (d (t+1) ω)*ChangingDomains.variation (a (t+1) ω) (a t ω)≤
      (family C ell).value (d t ω).data (d (t+1) ω).ranks (a t ω)-
      (family C ell).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)+
      (13*C*ell+4)*ChangingDomains.changedFlags (StarSimplex.flags P ω t) (StarSimplex.flags P ω (t+1)) := by
  intro ell d a
  let x:=vector cutoff δ P ω
  let ky:=fun s=>key s ω
  let h:=weight δ x ky t
  let u:=sideRatio δ x ky t
  let f:=StarSimplex.flags P ω t
  let g:=StarSimplex.flags P ω (t+1)
  let A:=activeSet (x t)
  have hxn:=vector_nonneg cutoff δ P ω
  have hel:0<ell:=by have hlog:=Real.log_nonneg (show 1≤k+1 by linarith); dsimp [ell]; linarith
  change EpochSchedule.dominant (EpochSchedule.run x ky t)=some o at ho
  have ho':EpochSchedule.dominant (EpochSchedule.run x ky (t+1))=some o:=
    (ScheduleEdits.ordinary_mark x ky t he).trans ho
  have hA:o∈A:=marked_active x ky hxn t ho
  have hB:activeSet (x (t+1))={o}:=marked_zero_singleton hδ x ky hxn (t+1) ho' hu'
  have hh:∀ i≠o,1≤h i:=fun i hi=>weight_regular_one δ x ky t i (by rw [ho]; simpa [eq_comm] using hi)
  have heta:∀ i,ct*h i/ell∈Set.Icc 0 1:=eta_bound hδ hδu hct.le hctu hk P key hs t ω
  have hu1:u≤1:=(side_ratio_upper hδ hδu x ky hxn t ho).trans (by norm_num)
  have how:h o=u:=marked_weight δ x ky t o ho
  have hside:∀ i∈A,i≠o→(1/2:ℝ)*(1+Real.log (1/u))≤h i:=
    fun i hi hio=>weight_side_lower hδ hδu x ky hxn t ho hi hio hu
  have ht:=side_exp_sum hδ hδu x ky hxn t ho
  have hgp:2*((25*(1/2:ℝ)+2+32*2)/(1/2))*(1+1)<C*ct:=by linarith
  have hold:(d t ω).data=marked A f o h (fun i=>ct*h i/ell) u hu hu1 hh :=
    marked_data hδ hδu C ell ct x ky hxn (StarSimplex.flags P ω) t o ho hu hu1 hh
  have hp:∀ ir,(d (t+1) ω).ranks ir∈Set.Icc 0 1:=fun ir=>(P ir.1 ir.2).range (t+1) ω
  have hf:∀ i∉A,∀ r,f i r=false:=fun i hi r=>flags_supported hδ hδu P t ω i hi r
  have hg:∀ i∉({o}:Finset J),∀ r,g i r=false:=by
    rw [←hB]
    exact fun i hi r=>flags_supported hδ hδu P (t+1) ω i hi r
  have ha:a t ω∈ChangingDomains.simplex A:=StarSimplex.proportion_mem hδ hδu C ell ct P key t ω
  have ha':a (t+1) ω∈ChangingDomains.simplex {o}:=by
    rw [←hB]
    exact StarSimplex.proportion_mem hδ hδu C ell ct P key (t+1) ω
  have hae:a (t+1) ω=point o:=singleton_eq ha'
  have hpay:=new_singleton hA f g h hu hu1 how hh hC hel hct heta
    (fun i _=>(heta i).2) (by norm_num : (0:ℝ)≤2) (by norm_num : (0:ℝ)<1/2)
    (by norm_num) hside ht hgp (d (t+1) ω).ranks hp hf hg (a t ω) ha
  dsimp only at hpay
  have hv0:(family C ell).value (d t ω).data (d (t+1) ω).ranks (a t ω)=
      potential C ell (marked A f o h (fun i=>ct*h i/ell) u hu hu1 hh)
        (core (marked A f o h (fun i=>ct*h i/ell) u hu hu1 hh) (d (t+1) ω).ranks) (a t ω) := by
    rw [hold]
    exact value_eq C ell _ _ _ ha
  have hv1:(family C ell).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)=0:=
    zero_value C ell _ _ _ (marked_zero_flag hδ hδu C ell ct x ky hxn (StarSimplex.flags P ω) (t+1) o ho' hu')
  have hm:CausalSimplex.mass (d (t+1) ω)=∑ i,ChangingDomains.core g (fun i r=>(d (t+1) ω).ranks (i,r)) i := by
    have hgf:(d (t+1) ω).data.flags=g:=data_flags hδ hδu C ell ct x ky hxn (StarSimplex.flags P ω) (t+1)
    simp only [CausalSimplex.mass,core,hgf,ChangingDomains.core]
  rw [hv0,hv1,sub_zero,hae,hm]
  exact hpay

end KServer.ScheduledPayment

end


/-! The complete ordinary/wholesale simplex payment for the literal schedule.
All charges below are computed by the actual switches, never supplied by a
finite-law hypothesis. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ScheduledPayment
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile AllocationSchedule
open SimplexFamilies AdaptiveAllocation ScheduleShape SingletonPayment
variable {Ω J R K : Type} [Fintype Ω] [Fintype J] [DecidableEq J] [Fintype R]
variable {w : Ω→ℝ}

omit [Fintype Ω] [DecidableEq J] [Fintype R] in
lemma empty_total (x:J→ℝ) (hx:∀ i,0≤x i) (hA:¬(activeSet x).Nonempty) : EpochSchedule.total x=0 := by
  apply sum_eq_zero
  intro i _
  apply le_antisymm _ (hx i)
  by_contra hn
  exact hA ⟨i,(mem_activeSet x i).mpr (lt_of_not_ge hn)⟩

omit [Fintype Ω] [DecidableEq J] [Fintype R] in
lemma positive_active (x:J→ℝ) (hx:∀ i,0≤x i) (hp:0<EpochSchedule.total x) : (activeSet x).Nonempty := by
  by_contra hn
  rw [empty_total x hx hn] at hp
  exact (lt_irrefl _ hp)

omit [Fintype Ω] [DecidableEq J] [Fintype R] in
lemma ordinary_nonempty (x:ℕ→J→ℝ) (key:ℕ→K) (hx:∀ t i,0≤x t i) (t:ℕ)
    (he:epoch x key t=epoch x key (t+1)) :
    (activeSet (x t)).Nonempty ↔ (activeSet (x (t+1))).Nonempty := by
  have hm:=ScheduleEdits.ordinary_mass x key t he
  constructor
  · intro ha
    have h:=ScheduledSimplex.nonempty_mass x key hx t ha
    have hb:=(mass_accuracy x key hx (t+1)).1
    rw [hm] at hb
    exact positive_active _ (hx (t+1)) (by linarith)
  · intro hb
    have h:=ScheduledSimplex.nonempty_mass x key hx (t+1) hb
    rw [hm] at h
    have ha:=(mass_accuracy x key hx t).1
    exact positive_active _ (hx t) (by linarith)

omit [Fintype Ω] [DecidableEq J] in
lemma flags_nonneg (f g:J→R→Bool) : 0≤ChangingDomains.changedFlags f g := by
  apply sum_nonneg
  intro i _
  apply sum_nonneg
  intro r _
  split_ifs <;> norm_num

omit [Fintype Ω] [Fintype R] [DecidableEq J] in
lemma side_charge_nonneg (δ:ℝ) (x:ℕ→J→ℝ) (key:ℕ→K) (hx:∀ t i,0≤x t i) (t:ℕ) :
    0≤CoarseSide.charge δ (CoarseSide.sideInput x key) (CoarseSide.epochReset x key) t := by
  unfold CoarseSide.charge
  split_ifs
  · exact add_nonneg (CoarseSide.side_nonneg (hx t) _) (CoarseSide.side_nonneg (hx (t+1)) _)
  · rfl

omit [DecidableEq J] in
lemma expense_nonneg {C ell:ℝ} (hC:0≤C) (hel:0≤ell) (δ:ℝ) (P:J→R→FilteredRanks w)
    (key:ℕ→Ω→K) (t:ℕ) (ω:Ω) : 0≤expense C ell δ P key t ω := by
  have hf:=flags_nonneg (StarSimplex.flags P ω t) (StarSimplex.flags P ω (t+1))
  have hc:0≤∑ i,CoarseSchedule.charge (active cutoff δ (P i) ω t) (active cutoff δ (P i) ω (t+1)):=
    sum_nonneg fun i _=>charge_nonneg (active_valid cutoff δ (P i) ω t) (active_valid cutoff δ (P i) ω (t+1))
  have hu:=side_charge_nonneg δ (vector cutoff δ P ω) (fun s=>key s ω) (vector_nonneg cutoff δ P ω) t
  have hw:0≤EpochSchedule.wholesale (vector cutoff δ P ω t) (vector cutoff δ P ω (t+1)) (key t ω) (key (t+1) ω)
      (EpochSchedule.run (vector cutoff δ P ω) (fun s=>key s ω) t) := by
    unfold EpochSchedule.wholesale
    split_ifs
    · exact add_nonneg (EpochSchedule.total_nonneg (vector_nonneg cutoff δ P ω t))
        (EpochSchedule.total_nonneg (vector_nonneg cutoff δ P ω (t+1)))
    · rfl
  unfold expense
  positivity

lemma mass_bound {δ:ℝ} (hδ:0<δ) (hδu:δ≤1/1000) (C ell ct:ℝ) (P:J→R→FilteredRanks w)
    (key:ℕ→Ω→K) (t:ℕ) (ω:Ω) :
    CausalSimplex.mass (StarSimplex.input hδ hδu C ell ct P key t ω)≤40*EpochSchedule.total (vector cutoff δ P ω t) := by
  simp only [CausalSimplex.mass,core,StarSimplex.input,data_flags,StarSimplex.flags]
  change (∑ i,∑ r,if CoreFlags.flag (P i r) t ω then (P i r).p t ω else 0)≤40*(∑ i,vector cutoff δ P ω t i)
  rw [mul_sum]
  exact sum_le_sum fun i _=>ScheduleEdits.raw_core_bound hδ hδu (P i) t ω
    (fun r=>(P i r).p t ω) (fun r=>(P i r).range t ω)

lemma wholesale_payment {δ C ct k:ℝ} (hδ:0<δ) (hδu:δ≤1/1000)
    (hC:0≤C) (hct:0 ≤ ct) (hctu:ct*20002≤1) (hk:1≤k)
    (P:J→R→FilteredRanks w) (key:ℕ→Ω→K)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤k) (t:ℕ) (ω:Ω)
    (he:epoch (vector cutoff δ P ω) (fun s=>key s ω) t≠
      epoch (vector cutoff δ P ω) (fun s=>key s ω) (t+1)) :
    let ell:=1+Real.log (k+1)
    let d:=StarSimplex.input hδ hδu C ell ct P key
    let a:=StarSimplex.proportion hδ hδu C ell ct P key
    CausalSimplex.mass (d (t+1) ω)*ChangingDomains.variation (a (t+1) ω) (a t ω)≤
      (family C ell).value (d t ω).data (d (t+1) ω).ranks (a t ω)-
      (family C ell).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)+expense C ell δ P key t ω := by
  intro ell d a
  let x:=vector cutoff δ P ω
  let ky:=fun s=>key s ω
  have hel:0≤ell:=by have h:=Real.log_nonneg (show 1≤k+1 by linarith); dsimp [ell]; linarith
  have ha:=StarSimplex.proportion_mem hδ hδu C ell ct P key t ω
  have ha':=StarSimplex.proportion_mem hδ hδu C ell ct P key (t+1) ω
  have hm:=mass_bound hδ hδu C ell ct P key (t+1) ω
  have hmove: CausalSimplex.mass (d (t+1) ω)*ChangingDomains.variation (a (t+1) ω) (a t ω)≤80*EpochSchedule.total (x (t+1)) := by
    have hn:0≤CausalSimplex.mass (d (t+1) ω):=by
      apply sum_nonneg
      intro i _
      apply sum_nonneg
      intro r _
      split_ifs
      · exact ((P i r).range (t+1) ω).1
      · rfl
    have hh:=mul_le_mul_of_nonneg_left (ChangingDomains.simplex_variation ha' ha) hn
    nlinarith
  have hp:∀ ir,(d (t+1) ω).ranks ir∈Set.Icc 0 1:=fun ir=>(P ir.1 ir.2).range (t+1) ω
  have h₀:=neg_le_of_abs_le (ScheduledEndpoint.actual_bound hδ hδu hC hct hctu hk P key hs t ω _ hp _ ha)
  have h₁:=le_of_abs_le (ScheduledEndpoint.actual_bound hδ hδu hC hct hctu hk P key hs (t+1) ω _ hp _ ha')
  have hn:CoarseSide.epochReset x ky t:=Classical.not_not.mp (fun hh=>he ((epoch_same_iff x ky t).mpr hh))
  have wh:EpochSchedule.wholesale (x t) (x (t+1)) (ky t) (ky (t+1)) (EpochSchedule.run x ky t)=
      EpochSchedule.total (x t)+EpochSchedule.total (x (t+1)):=ite_eq_left hn
  have hcharges:0≤(26*C*ell+4)*ChangingDomains.changedFlags (StarSimplex.flags P ω t) (StarSimplex.flags P ω (t+1))+
      320*C*ell*(∑ i,CoarseSchedule.charge (active cutoff δ (P i) ω t) (active cutoff δ (P i) ω (t+1)))+
      2976*C*ell*CoarseSide.charge δ (CoarseSide.sideInput x ky) (CoarseSide.epochReset x ky) t := by
    have hf:=flags_nonneg (StarSimplex.flags P ω t) (StarSimplex.flags P ω (t+1))
    have hc:0≤∑ i,CoarseSchedule.charge (active cutoff δ (P i) ω t) (active cutoff δ (P i) ω (t+1)):=
      sum_nonneg fun i _=>charge_nonneg (active_valid cutoff δ (P i) ω t) (active_valid cutoff δ (P i) ω (t+1))
    have hu:=side_charge_nonneg δ x ky (vector_nonneg cutoff δ P ω) t
    positivity
  unfold expense
  change _≤_+(_+(_)*EpochSchedule.wholesale (x t) (x (t+1)) (ky t) (ky (t+1)) (EpochSchedule.run x ky t))
  rw [wh]
  have hx0:0≤EpochSchedule.total (x t):=EpochSchedule.total_nonneg (vector_nonneg cutoff δ P ω t)
  nlinarith

omit [DecidableEq J] in
lemma expense_lower {C ell:ℝ} (hC:0≤C) (hel:0≤ell) (δ:ℝ) (P:J→R→FilteredRanks w)
    (key:ℕ→Ω→K) (t:ℕ) (ω:Ω) :
    (26*C*ell+4)*ChangingDomains.changedFlags (StarSimplex.flags P ω t) (StarSimplex.flags P ω (t+1))+
      320*C*ell*(∑ i,CoarseSchedule.charge (active cutoff δ (P i) ω t) (active cutoff δ (P i) ω (t+1)))+
      2976*C*ell*CoarseSide.charge δ (CoarseSide.sideInput (vector cutoff δ P ω) (fun s=>key s ω))
        (CoarseSide.epochReset (vector cutoff δ P ω) (fun s=>key s ω)) t ≤ expense C ell δ P key t ω := by
  have hw:0≤EpochSchedule.wholesale (vector cutoff δ P ω t) (vector cutoff δ P ω (t+1)) (key t ω) (key (t+1) ω)
      (EpochSchedule.run (vector cutoff δ P ω) (fun s=>key s ω) t) := by
    unfold EpochSchedule.wholesale
    split_ifs
    · exact add_nonneg (EpochSchedule.total_nonneg (vector_nonneg cutoff δ P ω t))
        (EpochSchedule.total_nonneg (vector_nonneg cutoff δ P ω (t+1)))
    · rfl
  exact le_add_of_nonneg_right (mul_nonneg (by positivity) hw)

lemma payment {δ C ct k:ℝ} (hδ:0<δ) (hδu:δ≤1/1000)
    (hC:0<C) (hct:0 < ct) (hctu:ct*20002≤1) (hgap:700<C*ct) (hk:1≤k)
    (P:J→R→FilteredRanks w) (key:ℕ→Ω→K)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤k) (t:ℕ) (ω:Ω) :
    let ell:=1+Real.log (k+1)
    let d:=StarSimplex.input hδ hδu C ell ct P key
    let a:=StarSimplex.proportion hδ hδu C ell ct P key
    CausalSimplex.mass (d (t+1) ω)*ChangingDomains.variation (a (t+1) ω) (a t ω)≤
      (family C ell).value (d t ω).data (d (t+1) ω).ranks (a t ω)-
      (family C ell).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)+expense C ell δ P key t ω := by
  intro ell d a
  let x:=vector cutoff δ P ω
  let ky:=fun s=>key s ω
  have hx:=vector_nonneg cutoff δ P ω
  have hel:0≤ell:=by have h:=Real.log_nonneg (show 1≤k+1 by linarith); dsimp [ell]; linarith
  by_cases he:epoch x ky t=epoch x ky (t+1)
  · have hf:=flags_nonneg (StarSimplex.flags P ω t) (StarSimplex.flags P ω (t+1))
    have hc:0≤∑ i,CoarseSchedule.charge (active cutoff δ (P i) ω t) (active cutoff δ (P i) ω (t+1)):=
      sum_nonneg fun i _=>charge_nonneg (active_valid cutoff δ (P i) ω t) (active_valid cutoff δ (P i) ω (t+1))
    have hu:=side_charge_nonneg δ x ky hx t
    have hl:=expense_lower hC.le hel δ P key t ω
    have hcn:0≤C*ell:=mul_nonneg hC.le hel
    by_cases hA:(activeSet (x t)).Nonempty
    · have hB:=(ordinary_nonempty x ky hx t he).mp hA
      cases ho:EpochSchedule.dominant (EpochSchedule.run x ky t) with
      | none =>
        have hp:=ordinary_regular hδ hδu hC hct hctu hgap hk P key hs t ω he hA hB ho
        change _≤(family C ell).value (d t ω).data (d (t+1) ω).ranks (a t ω)-
          (family C ell).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)+_+_ at hp
        change _+_+2976*C*ell*CoarseSide.charge δ (CoarseSide.sideInput x ky) (CoarseSide.epochReset x ky) t≤_ at hl
        nlinarith [mul_nonneg hcn hf,mul_nonneg hcn hu]
      | some o =>
        by_cases hu0:sideRatio δ x ky t=0
        · have hp:=ordinary_old_zero hδ hδu hC.le hct.le hctu hk P key hs t ω he o ho hu0
          change _≤(family C ell).value (d t ω).data (d (t+1) ω).ranks (a t ω)-
            (family C ell).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)+_ at hp
          change _+_+2976*C*ell*CoarseSide.charge δ (CoarseSide.sideInput x ky) (CoarseSide.epochReset x ky) t≤_ at hl
          nlinarith [mul_nonneg hcn hf,mul_nonneg hcn hc,mul_nonneg hcn hu]
        · have hup:0 < sideRatio δ x ky t:=lt_of_le_of_ne (side_ratio_nonneg δ x ky hx t) (Ne.symm hu0)
          by_cases hu1:sideRatio δ x ky (t+1)=0
          · have hp:=ordinary_new_zero hδ hδu hC hct hctu hgap hk P key hs t ω he o ho hup hu1
            change _≤(family C ell).value (d t ω).data (d (t+1) ω).ranks (a t ω)-
              (family C ell).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)+_ at hp
            change _+_+2976*C*ell*CoarseSide.charge δ (CoarseSide.sideInput x ky) (CoarseSide.epochReset x ky) t≤_ at hl
            nlinarith [mul_nonneg hcn hf,mul_nonneg hcn hc,mul_nonneg hcn hu]
          · have hup':0 < sideRatio δ x ky (t+1):=lt_of_le_of_ne (side_ratio_nonneg δ x ky hx (t+1)) (Ne.symm hu1)
            have hp:=ordinary_marked hδ hδu hC hct hctu hgap hk P key hs t ω he o ho hup hup'
            have hs' : (∑ i∈univ.erase o,CoarseSchedule.charge (active cutoff δ (P i) ω t) (active cutoff δ (P i) ω (t+1)))≤
                ∑ i,CoarseSchedule.charge (active cutoff δ (P i) ω t) (active cutoff δ (P i) ω (t+1)):=
              sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun i _ _=>charge_nonneg (active_valid cutoff δ (P i) ω t) (active_valid cutoff δ (P i) ω (t+1)))
            have hmul:=mul_le_mul_of_nonneg_left hs' (show 0≤320*C*ell by positivity)
            change _≤(family C ell).value (d t ω).data (d (t+1) ω).ranks (a t ω)-
              (family C ell).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)+_+_+_ at hp
            linarith
    · have hB:¬(activeSet (x (t+1))).Nonempty:=fun hh=>hA ((ordinary_nonempty x ky hx t he).mpr hh)
      have hz (s:ℕ) (hn:¬(activeSet (x s)).Nonempty) : (d s ω).data.zeroPotential=true := by
        change (data hδ hδu C ell ct x ky hx (StarSimplex.flags P ω) s).zeroPotential=true
        unfold data
        dsimp only
        rw [ite_eq_right hn]
        rfl
      have hm:CausalSimplex.mass (d (t+1) ω)=0 := by
        have hm:=mass_bound hδ hδu C ell ct P key (t+1) ω
        rw [empty_total _ (hx (t+1)) hB,mul_zero] at hm
        apply le_antisymm hm
        apply sum_nonneg
        intro i _
        exact ChangingDomains.core_nonneg (fun i r=>((P i r).range (t+1) ω).1) _
      rw [hm,zero_mul,zero_value C ell _ _ _ (hz t hA),zero_value C ell _ _ _ (hz (t+1) hB),sub_self,zero_add]
      exact expense_nonneg hC.le hel δ P key t ω
  · exact wholesale_payment hδ hδu hC.le hct.le hctu hk P key hs t ω he

end KServer.ScheduledPayment

end


/-! Literal coarse schedule bills and their finite-experiment budgets. The
right sides use drift after conditioning, never raw posterior variation. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualCharges
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

lemma constants_nonneg:0≤ activeConstant ∧ 0≤ parentConstant ∧ 0≤ flagConstant:=by
  norm_num [activeConstant,parentConstant,flagConstant,CoarseSchedule.factor,ds,dp,lb,cb,CoreFlags.tolerance]
lemma inventory_nonneg (hw:∀ ω,0≤ w ω) (P:R→ FilteredRanks w) (N:ℕ):0≤ inventory P N:=by
  apply add_nonneg _ (Nat.cast_nonneg _)
  unfold drift
  exact sum_nonneg fun t _=>sum_nonneg fun ω _=>mul_nonneg (hw ω)
    (sum_nonneg fun r _=>abs_nonneg _)
lemma flags_nonneg (P:J→ R→ FilteredRanks w) (t:ℕ) (ω:Ω):0≤ flags P t ω:=
  ScheduledPayment.flags_nonneg _ _
lemma active_nonneg (P:J→ R→ FilteredRanks w) (t:ℕ) (ω:Ω):0≤ active P t ω:=by
  apply sum_nonneg
  intro i _
  exact CoarseProcess.charge_nonneg (active_valid cutoff ds (P i) ω t) (active_valid cutoff ds (P i) ω (t+1))
lemma wholesale_nonneg (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (t:ℕ) (ω:Ω):0≤ wholesale P Q t ω:=by
  unfold wholesale EpochSchedule.wholesale
  split_ifs
  · exact add_nonneg (EpochSchedule.total_nonneg (vector_nonneg cutoff ds P ω t))
      (EpochSchedule.total_nonneg (vector_nonneg cutoff ds P ω (t+1)))
  · rfl

lemma flags_eq (P:J→ R→ FilteredRanks w) (t:ℕ) (ω:Ω):
    flags P t ω=∑ ir:J×R,CoreFlags.change (P ir.1 ir.2) t ω:=by
  unfold flags ChangingDomains.changedFlags
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro r _
  unfold StarSimplex.flags CoreFlags.change
  by_cases he:CoreFlags.flag (P i r) t ω=CoreFlags.flag (P i r) (t+1) ω
  · simp only [he,ite_true]
  · simp only [he,Ne.symm he,ite_false]

lemma flags_budget (hw:∀ ω,0≤ w ω) (hw1:∑ ω,w ω=1) (P:J→ R→ FilteredRanks w) (N:ℕ):
    (∑ t∈range N,avg w (flags P t))≤ flagConstant*inventory (flat P) N:=by
  have h:=CoreFlags.core_change_budget hw hw1 (flat P) N
  change (∑ t∈range N,avg w (fun ω=>∑ ir:J×R,CoreFlags.change (P ir.1 ir.2) t ω))≤_ at h
  simpa only [←flags_eq,flagConstant,inventory,drift] using h

lemma inventory_flat (P:J→ R→ FilteredRanks w) (N:ℕ):
    inventory (flat P) N=∑ i,inventory (P i) N:=by
  simp only [inventory,drift,flat,Fintype.sum_prod_type,avg_sum,sum_add_distrib,sum_const,nsmul_eq_mul,
    Fintype.card_prod,Nat.cast_mul,card_univ]
  rw [sum_comm]

lemma active_budget (hw:∀ ω,0≤ w ω) (hw1:∑ ω,w ω=1) (P:J→ R→ FilteredRanks w) (N:ℕ):
    (∑ t∈range N,avg w (active P t))≤ activeConstant*inventory (flat P) N:=by
  have hb (i:J): (∑ t∈range N,avg w (fun ω=> CoarseSchedule.charge
      (CoarseProcess.active cutoff ds (P i) ω t) (CoarseProcess.active cutoff ds (P i) ω (t+1))))≤
      activeConstant*inventory (P i) N:=by
    have h:=CoarseProcess.active_budget (by norm_num [cutoff] : 0< cutoff)
      (by norm_num [ds] : 0< ds) (by norm_num [ds] : ds≤1/1000) hw hw1 (P i) N
    have hd:0≤ drift (P i) N:=by
      unfold drift avg
      exact sum_nonneg fun t _=>sum_nonneg fun ω _=>mul_nonneg (hw ω)
        (sum_nonneg fun r _=>abs_nonneg _)
    have hf:0≤ CoarseSchedule.factor ds:=by norm_num [CoarseSchedule.factor,ds]
    rw [sum_comm] at h
    simp only [←avg_sum] at h
    change _≤ CoarseSchedule.factor ds*(5*(4/3:ℝ)^2/ds)*drift (P i) N+
      activeConstant*Fintype.card R at h
    dsimp only [activeConstant,inventory] at ⊢
    dsimp only [activeConstant] at h
    nlinarith [mul_nonneg hf hd]
  change (∑ t∈range N,avg w (fun ω=>∑ i,CoarseSchedule.charge
    (CoarseProcess.active cutoff ds (P i) ω t) (CoarseProcess.active cutoff ds (P i) ω (t+1))))≤_
  simp only [avg_sum]
  rw [sum_comm,inventory_flat,mul_sum]
  exact sum_le_sum fun i _=> hb i

lemma parent_budget (hw:∀ ω,0≤ w ω) (hw1:∑ ω,w ω=1) (Q:R→ FilteredRanks w) (N:ℕ):
    (∑ t∈range N,avg w (parentCharge Q t))≤ parentConstant*inventory Q N:=by
  have h:=CoarseEpoch.parent_budget (by norm_num [cutoff] : 0≤ cutoff)
    (by norm_num [dp,lb,cb] : 0< dp) (by norm_num [dp,lb,cb] : dp≤1/3) hw hw1 Q N
  rw [sum_comm] at h
  change (∑ t∈range N,avg w (CoarseProcess.relativeCharge dp (clipped cutoff dp Q) t))≤_
  simpa only [←avg_sum,parentConstant,inventory,drift] using h

lemma wholesale_budget (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (N:ℕ) (ω:Ω):
    (∑ t∈range N,wholesale P Q t ω)≤203*(∑ t∈range N,active P t ω)+
      2*(∑ t∈range N,parentCharge Q t ω):=by
  exact CoarseEpoch.wholesale_budget (by norm_num [cutoff]) (by norm_num [ds]) (by norm_num [ds])
    (by norm_num [dp,lb,cb]) (by norm_num [dp,lb,cb]) P Q hs id ω N

lemma sideRefresh_budget (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (N:ℕ) (ω:Ω):
    (∑ t∈range N,sideRefresh P Q t ω)≤ CoarseSide.C ds*(∑ t∈range N,active P t ω):=by
  exact (CoarseSide.side_budget (by norm_num [ds] : 0< ds) (vector cutoff ds P ω)
    (fun s=> key Q s ω) (vector_nonneg cutoff ds P ω) N).trans
    (mul_le_mul_of_nonneg_left (sum_le_sum fun t _=> vector_variation cutoff ds P ω t)
      (CoarseSide.C_nonneg (by norm_num [ds])))
end KServer.ActualCharges

end


/-! Uniform coarse accounting for the actual local star. The only variable
right-hand side is the sum of true drift and one fixed rank inventory. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualCharges
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

lemma total_mono (hw:∀ ω,0≤ w ω) {N:ℕ} {f g:ℕ→Ω→ℝ} (h:∀ t ω,f t ω≤ g t ω):
    total w N f≤ total w N g:=sum_le_sum fun t _=> avg_mono hw (h t)
lemma total_nonneg (hw:∀ ω,0≤ w ω) {N:ℕ} {f:ℕ→Ω→ℝ} (h:∀ t ω,0≤ f t ω):
    0≤ total w N f:=sum_nonneg fun t _=> sum_nonneg fun ω _=> mul_nonneg (hw ω) (h t ω)
lemma total_add (N:ℕ) (f g:ℕ→Ω→ℝ):
    total w N (fun t ω=> f t ω+g t ω)=total w N f+total w N g:=by
  simp only [total,avg_add,sum_add_distrib]
lemma total_mul (N:ℕ) (c:ℝ) (f:ℕ→Ω→ℝ):
    total w N (fun t ω=> c*f t ω)=c*total w N f:=by
  simp only [total,avg_mul,←mul_sum]
lemma stock_nonneg (hw:∀ ω,0≤ w ω) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (N:ℕ):
    0≤ stock P Q N:=add_nonneg (inventory_nonneg hw _ _) (inventory_nonneg hw _ _)
lemma inventory_child_le (hw:∀ ω,0≤ w ω) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (N:ℕ):
    inventory (flat P) N≤ stock P Q N:=le_add_of_nonneg_right (inventory_nonneg hw _ _)
lemma inventory_parent_le (hw:∀ ω,0≤ w ω) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (N:ℕ):
    inventory Q N≤ stock P Q N:=le_add_of_nonneg_left (inventory_nonneg hw _ _)
lemma more_constants_nonneg:0≤ wholesaleConstant ∧ 0≤ scaleConstant ∧ 0≤ sideRefreshConstant:=by
  rcases constants_nonneg with ⟨ha,hp,hf⟩
  have hc:=CoarseSide.C_nonneg (by norm_num [ds]:0< ds)
  have hd:0≤80/ds:=by norm_num [ds]
  dsimp only [wholesaleConstant,scaleConstant,sideRefreshConstant]
  constructor
  · positivity
  constructor <;> positivity

lemma flags_bound (hw:∀ ω,0≤ w ω) (hw1:∑ ω,w ω=1) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (N:ℕ):
    total w N (flags P)≤ flagConstant*stock P Q N:=
  (flags_budget hw hw1 P N).trans (mul_le_mul_of_nonneg_left (inventory_child_le hw P Q N) constants_nonneg.2.2)
lemma active_bound (hw:∀ ω,0≤ w ω) (hw1:∑ ω,w ω=1) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (N:ℕ):
    total w N (ActualCharges.active P)≤ activeConstant*stock P Q N:=
  (active_budget hw hw1 P N).trans (mul_le_mul_of_nonneg_left (inventory_child_le hw P Q N) constants_nonneg.1)
lemma parent_bound (hw:∀ ω,0≤ w ω) (hw1:∑ ω,w ω=1) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (N:ℕ):
    total w N (parentCharge Q)≤ parentConstant*stock P Q N:=
  (parent_budget hw hw1 Q N).trans (mul_le_mul_of_nonneg_left (inventory_parent_le hw P Q N) constants_nonneg.2.1)
lemma wholesale_bound (hw:∀ ω,0≤ w ω) (hw1:∑ ω,w ω=1) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (N:ℕ):
    total w N (wholesale P Q)≤ wholesaleConstant*stock P Q N:=by
  have h:=avg_mono hw (wholesale_budget P Q hs N)
  simp only [avg_add,avg_mul,←CoarseProcess.avg_range] at h
  change total w N (wholesale P Q)≤203*total w N (ActualCharges.active P)+2*total w N (parentCharge Q) at h
  have ha:=active_bound hw hw1 P Q N
  have hp:=parent_bound hw hw1 P Q N
  dsimp only [wholesaleConstant]
  nlinarith
lemma sideRefresh_bound (hw:∀ ω,0≤ w ω) (hw1:∑ ω,w ω=1) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (N:ℕ):
    total w N (sideRefresh P Q)≤ sideRefreshConstant*stock P Q N:=by
  have h:=avg_mono hw (sideRefresh_budget P Q N)
  simp only [avg_mul,←CoarseProcess.avg_range] at h
  change total w N (sideRefresh P Q)≤ CoarseSide.C ds*total w N (ActualCharges.active P) at h
  exact h.trans (by simpa only [sideRefreshConstant,mul_assoc] using
    mul_le_mul_of_nonneg_left (active_bound hw hw1 P Q N) (CoarseSide.C_nonneg (by norm_num [ds])))

lemma scale_eq (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (t:ℕ) (ω:Ω):
    ActualOutput.D P Q t ω=CoarseScale.scale ds P t ω
      (EpochSchedule.run (vector cutoff ds P ω) (fun s=> key Q s ω) t):=by
  unfold ActualOutput.D StarSide.scale StarSide.mark CoarseScale.scale
  cases EpochSchedule.dominant (EpochSchedule.run (vector cutoff ds P ω) (fun s=> key Q s ω) t) <;> rfl

lemma scale_bound (hw:∀ ω,0≤ w ω) (hw1:∑ ω,w ω=1) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (N:ℕ):
    total w N (fun t ω=>|ActualOutput.D P Q (t+1) ω-ActualOutput.D P Q t ω|)≤ scaleConstant*stock P Q N:=by
  have hc:=CoarseScale.scale_budget (by norm_num [cutoff]:0< cutoff) (by norm_num [ds]:0< ds)
    (by norm_num [ds]:ds≤1/1000) hw hw1 P (fun ω t=> key Q t ω) N
  have hd:(∑ i,∑ r,∑ t∈range N,avg w (fun ω=>|(P i r).p (t+1) ω-(P i r).before (t+1) ω|))=drift (flat P) N:=by
    simp only [drift,flat,Fintype.sum_prod_type,avg_sum]
    symm
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    exact sum_comm
  simp only [hd,←scale_eq] at hc
  have hi:drift (flat P) N+(Fintype.card J:ℝ)*(Fintype.card R:ℝ)=inventory (flat P) N:=by
    simp only [inventory,Fintype.card_prod,Nat.cast_mul]
  rw [hi] at hc
  change total w N (fun t ω=>|ActualOutput.D P Q (t+1) ω-ActualOutput.D P Q t ω|)≤
    (80/ds+flagConstant)*inventory (flat P) N+41*total w N (wholesale P Q) at hc
  have hwc:=wholesale_bound hw hw1 P Q hs N
  have hci:=inventory_child_le hw P Q N
  have hcc:0≤80/ds+flagConstant:=by have h:=constants_nonneg.2.2; norm_num [ds]; positivity
  have hb:=mul_le_mul_of_nonneg_left hci hcc
  dsimp only [scaleConstant]
  nlinarith
end KServer.ActualCharges

end


/-! Deterministic payment for the literal side state, with only actual edits
on the right hand side. Parent parameters are held through an ordinary epoch. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.SidePayment
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile AllocationSchedule StarSide
open SideFamilies
variable {Ω J R K : Type} [Fintype Ω] [Fintype J] [DecidableEq J] [Fintype R]
variable {w:Ω→ℝ}

lemma pre_actual {δ cw ell:ℝ} (hδ:0<δ) (hδu:δ≤1/1000)
    (hcw:0 < cw) (hel:1≤ell) (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (b:ℕ→Ω→ℝ)
    (t:ℕ) (ω:Ω) (hb:0≤b t ω)
    (hM:∀ i,b t ω+cw*logs δ P key t ω i/ell≤5) (hbe:b t ω=b (t+1) ω)
    (he:epoch (vector cutoff δ P ω) (fun s=>key s ω) t=
      epoch (vector cutoff δ P ω) (fun s=>key s ω) (t+1)) :
    let hp:0<ell:=lt_of_lt_of_le zero_lt_one hel
    let d:=input hcw hp δ P key b
    let a:=proportion hcw hp δ P key b t ω
    |(family 40).value (prepareData (d t ω).data (d (t+1) ω).data) (d (t+1) ω).ranks a-
      (family 40).value (d t ω).data (d (t+1) ω).ranks a|≤
      SideEdits.L cw ell*|scale δ P key (t+1) ω-scale δ P key t ω|+
      SideEdits.Q cw ell*ChangingDomains.changedFlags (StarSimplex.flags P ω t) (StarSimplex.flags P ω (t+1)) := by
  intro hp d a
  have hh:=SideEdits.pre_edit hcw hel (sides δ P key t ω) (sides δ P key (t+1) ω)
    (sideFlags δ P key t ω) (sideFlags δ P key (t+1) ω)
    (logs δ P key t ω) (logs δ P key (t+1) ω) (fun i=>le_max_left _ _) (fun i=>le_max_left _ _)
    hb hM (d (t+1) ω).ranks (fun ir=>(P ir.1 ir.2).range (t+1) ω)
    (SideActualEdits.flags_supported δ P key t ω) (SideActualEdits.flags_supported δ P key (t+1) ω)
    a (proportion_mem hcw hp δ P key b t ω) (D:=scale δ P key t ω) (E:=scale δ P key (t+1) ω)
  have hd1:(d (t+1) ω).data=fromLog (sides δ P key (t+1) ω) (sideFlags δ P key (t+1) ω)
      16 (b t ω) (scale δ P key (t+1) ω) cw ell (logs δ P key (t+1) ω)
      (by norm_num) hcw hp (fun i=>le_max_left _ _):=by dsimp [d,input]; rw [hbe]
  rw [hd1]
  exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (SideActualEdits.flags_change hδ hδu P key t ω he) (SideEdits.Q_nonneg hcw hp.le)))

lemma post_actual {δ cw ell:ℝ} (hδ:0<δ) (hδu:δ≤1/1000)
    (hcw:0 < cw) (hel:1≤ell) (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (b:ℕ→Ω→ℝ)
    (t:ℕ) (ω:Ω) (hb:1≤b t ω)
    (hM:∀ s i,b t ω+cw*logs δ P key s ω i/ell≤5) (hbe:b t ω=b (t+1) ω)
    (he:epoch (vector cutoff δ P ω) (fun s=>key s ω) t=
      epoch (vector cutoff δ P ω) (fun s=>key s ω) (t+1)) :
    let hp:0<ell:=lt_of_lt_of_le zero_lt_one hel
    let d:=input hcw hp δ P key b
    let a:=proportion hcw hp δ P key b t ω
    let z:=SideFamilies.transport 40 (d t ω).data (d (t+1) ω).data (d (t+1) ω).ranks a
    |(family 40).value (d (t+1) ω).data (d (t+1) ω).ranks z-
      (family 40).value (prepareData (d t ω).data (d (t+1) ω).data) (d (t+1) ω).ranks z|≤
      SideEdits.K cw ell*(40*(∑ i,CoarseSchedule.charge (active cutoff δ (P i) ω t) (active cutoff δ (P i) ω (t+1)))) := by
  intro hp d a z
  have hh:=SideEdits.post_edit hcw hel (sides δ P key t ω) (sides δ P key (t+1) ω)
    (sideFlags δ P key t ω) (sideFlags δ P key (t+1) ω)
    (logs δ P key t ω) (logs δ P key (t+1) ω) (fun i=>le_max_left _ _) (fun i=>le_max_left _ _)
    hb (hM t) (hM (t+1)) (scale_nonneg δ P key (t+1) ω) (d (t+1) ω).ranks
    (fun ir=>((P ir.1 ir.2).range (t+1) ω).1) a (proportion_mem hcw hp δ P key b t ω)
    (D:=scale δ P key t ω)
  have hd1:(d (t+1) ω).data=fromLog (sides δ P key (t+1) ω) (sideFlags δ P key (t+1) ω)
      16 (b t ω) (scale δ P key (t+1) ω) cw ell (logs δ P key (t+1) ω)
      (by norm_num) hcw hp (fun i=>le_max_left _ _):=by dsimp [d,input]; rw [hbe]
  dsimp only at hh
  rw [←hd1] at hh
  have hK:0≤SideEdits.K cw ell:=by
    unfold SideEdits.K
    have hl:=Real.log_nonneg (show (1:ℝ)≤17 by norm_num)
    positivity
  exact hh.trans (mul_le_mul_of_nonneg_left (SideActualEdits.logs_charge hδ hδu hcw hp P key b t ω
    (d (t+1) ω).ranks (fun ir=>(P ir.1 ir.2).range (t+1) ω) he) hK)

end KServer.SidePayment

end


noncomputable section
open scoped BigOperators
namespace KServer.SideFixed
open SideFamilies
attribute [local instance] Classical.decEq
variable {Ω J R:Type} [Fintype J] [Fintype R]
lemma payment (d:ℕ→Ω→CausalSide.Input J R) (t:ℕ) (ω:Ω)
    (he:(d t ω).epoch=(d (t+1) ω).epoch)
    (hWW:(d t ω).data.W=(d (t+1) ω).data.W)
    (hb:1≤(d t ω).data.b) (hD:0≤(d (t+1) ω).data.D)
    (hM:∀ i∈(d t ω).data.active,(d t ω).data.b+(d t ω).data.θ i≤5)
    (hW:10<(d t ω).data.W) (hp:∀ ir,0≤(d (t+1) ω).ranks ir) :
    let old:=(d t ω).data
    let new:=(d (t+1) ω).data
    let p:=(d (t+1) ω).ranks
    let a:=CausalSide.run 40 d t ω
    new.D*ChangingDomains.variation (CausalSide.run 40 d (t+1) ω) a≤
      (family 40).value old p a-(family 40).value new p (CausalSide.run 40 d (t+1) ω)+
      |(family 40).value (prepareData old new) p a-(family 40).value old p a|+
      |(family 40).value new p (SideFamilies.transport 40 old new p a)-
        (family 40).value (prepareData old new) p (SideFamilies.transport 40 old new p a)| := by
  have hh:=CausalSide.ordinary_payment d (M:=5) t ω he hWW hb hD hM (by norm_num; exact hW) hp
  simpa only [show (8:ℝ)*5=40 by norm_num] using hh
lemma payment_of_edits (d:ℕ→Ω→CausalSide.Input J R) (t:ℕ) (ω:Ω)
    (he:(d t ω).epoch=(d (t+1) ω).epoch)
    (hWW:(d t ω).data.W=(d (t+1) ω).data.W)
    (hb:1≤(d t ω).data.b) (hD:0≤(d (t+1) ω).data.D)
    (hM:∀ i∈(d t ω).data.active,(d t ω).data.b+(d t ω).data.θ i≤5)
    (hW:10<(d t ω).data.W) (hp:∀ ir,0≤(d (t+1) ω).ranks ir) (u v:ℝ)
    (hpre: |(family 40).value (prepareData (d t ω).data (d (t+1) ω).data)
      (d (t+1) ω).ranks (CausalSide.run 40 d t ω)-
      (family 40).value (d t ω).data (d (t+1) ω).ranks (CausalSide.run 40 d t ω)|≤u)
    (hpost: |(family 40).value (d (t+1) ω).data (d (t+1) ω).ranks
      (SideFamilies.transport 40 (d t ω).data (d (t+1) ω).data (d (t+1) ω).ranks (CausalSide.run 40 d t ω))-
      (family 40).value (prepareData (d t ω).data (d (t+1) ω).data) (d (t+1) ω).ranks
      (SideFamilies.transport 40 (d t ω).data (d (t+1) ω).data (d (t+1) ω).ranks (CausalSide.run 40 d t ω))|≤v) :
    (d (t+1) ω).data.D*ChangingDomains.variation (CausalSide.run 40 d (t+1) ω) (CausalSide.run 40 d t ω)≤
      (family 40).value (d t ω).data (d (t+1) ω).ranks (CausalSide.run 40 d t ω)-
      (family 40).value (d (t+1) ω).data (d (t+1) ω).ranks (CausalSide.run 40 d (t+1) ω)+u+v := by
  exact (payment d t ω he hWW hb hD hM hW hp).trans (add_le_add (add_le_add le_rfl hpre) hpost)

end KServer.SideFixed

end


/-! Deterministic payment for the literal side state, with only actual edits
on the right hand side. Parent parameters are held through an ordinary epoch. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.SidePayment
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile AllocationSchedule StarSide
open SideFamilies
variable {Ω J R K : Type} [Fintype Ω] [Fintype J]  [Fintype R]
variable {w:Ω→ℝ}

lemma ordinary {δ k cw:ℝ} (hδ:0<δ) (hδu:δ≤1/1000) (hk:1≤k)
    (hcw:0 < cw) (hcwu:cw*20002≤1) (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (b:ℕ→Ω→ℝ)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤k) (t:ℕ) (ω:Ω)
    (hb:1≤b t ω) (hbu:b t ω≤4) (hbe:b t ω=b (t+1) ω)
    (he:epoch (vector cutoff δ P ω) (fun s=>key s ω) t=
      epoch (vector cutoff δ P ω) (fun s=>key s ω) (t+1)) :
    let ell:=1+Real.log (k+1)
    let hel:0<ell:=by have h:=Real.log_nonneg (show 1≤k+1 by linarith); dsimp [ell]; linarith
    let d:=input hcw hel δ P key b
    let a:=proportion hcw hel δ P key b
    scale δ P key (t+1) ω*ChangingDomains.variation (a (t+1) ω) (a t ω)≤
      (family 40).value (d t ω).data (d (t+1) ω).ranks (a t ω)-
      (family 40).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)+
      SideEdits.L cw ell*|scale δ P key (t+1) ω-scale δ P key t ω|+
      SideEdits.Q cw ell*ChangingDomains.changedFlags (StarSimplex.flags P ω t) (StarSimplex.flags P ω (t+1))+
      40*SideEdits.K cw ell*(∑ i,CoarseSchedule.charge (active cutoff δ (P i) ω t) (active cutoff δ (P i) ω (t+1))) := by
  intro ell hel d a
  have hell:1≤ell:=by dsimp [ell]; linarith [Real.log_nonneg (show 1≤k+1 by linarith)]
  have hM (s:ℕ) (i:J):b t ω+cw*logs δ P key s ω i/ell≤5:=by
    have h:=SideActualEdits.theta_bound hδ hδu hk hcw hcwu P key hs s ω i
    change cw*logs δ P key s ω i/ell≤1 at h
    linarith
  have hp:∀ ir,(d (t+1) ω).ranks ir∈Set.Icc 0 1:=fun ir=>(P ir.1 ir.2).range (t+1) ω
  have hpre:=pre_actual hδ hδu hcw hell P key b t ω (by linarith) (hM t) hbe he
  have hpost:=post_actual hδ hδu hcw hell P key b t ω hb hM hbe he
  have hpst : |(family 40).value (d (t+1) ω).data (d (t+1) ω).ranks
      (SideFamilies.transport 40 (d t ω).data (d (t+1) ω).data (d (t+1) ω).ranks (a t ω))-
      (family 40).value (prepareData (d t ω).data (d (t+1) ω).data) (d (t+1) ω).ranks
      (SideFamilies.transport 40 (d t ω).data (d (t+1) ω).data (d (t+1) ω).ranks (a t ω))|≤
    40*SideEdits.K cw ell*(∑ i,CoarseSchedule.charge (active cutoff δ (P i) ω t) (active cutoff δ (P i) ω (t+1))) := by
    simpa only [mul_left_comm,mul_assoc] using hpost
  have hpay:=SideFixed.payment_of_edits d t ω he rfl hb (scale_nonneg δ P key (t+1) ω)
    (fun i _=>hM t i) (by norm_num : (10:ℝ)<16) (fun ir=>(hp ir).1) _ _ hpre hpst
  dsimp only [a,proportion,d] at *
  simpa only [input,fromLog,add_assoc] using hpay

end KServer.SidePayment

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.SideActualBounds
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile AllocationSchedule StarSide
open SideFamilies
variable {Ω J R K : Type} [Fintype Ω] [Fintype J] [DecidableEq J] [Fintype R]
variable {w:Ω→ℝ}

omit [DecidableEq J] in
lemma scale_bound {δ:ℝ} (hδ:0<δ) (hδu:δ≤1/1000)
    (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (t:ℕ) (ω:Ω) :
    StarSide.scale δ P key t ω≤41*EpochSchedule.total (vector cutoff δ P ω t) := by
  have h:=CoarseScale.scale_bound (by norm_num [cutoff] : 0 < cutoff) hδ hδu P t ω
    (EpochSchedule.run (vector cutoff δ P ω) (fun s=>key s ω) t)
    (EpochSchedule.run_valid (vector cutoff δ P ω) (fun s=>key s ω) (vector_nonneg cutoff δ P ω) t)
  change CoarseScale.scale δ P t ω _≤_ at h
  unfold CoarseScale.scale at h
  unfold StarSide.scale mark
  cases hm : EpochSchedule.dominant (EpochSchedule.run (vector cutoff δ P ω) (fun s => key s ω) t) <;>
    simpa only [hm, Option.elim,CoarseScale.noncore,coarseFlex] using h

lemma core_bound {δ cw ell:ℝ} (hδ:0<δ) (hδu:δ≤1/1000) (hcw:0 < cw) (hel:0<ell)
    (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (b:ℕ→Ω→ℝ) (t:ℕ) (ω:Ω)
    (p:J×R→ℝ) (hp:∀ ir,p ir∈Set.Icc 0 1) :
    (∑ i,core (input hcw hel δ P key b t ω).data p i)≤40*EpochSchedule.total (vector cutoff δ P ω t) := by
  unfold EpochSchedule.total
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  apply le_trans _ (ScheduleEdits.count_bound hδ hδu (P i) t ω)
  apply sum_le_sum
  intro r _
  change (if sideFlags δ P key t ω i r then p (i,r) else 0)≤
    (if CoreFlags.flag (P i r) t ω then 1 else 0)
  by_cases hf:CoreFlags.flag (P i r) t ω=true
  · simp only [sideFlags,hf,ite_true]
    split_ifs <;> first | exact (hp (i,r)).2 | norm_num
  · simp [sideFlags,hf]

lemma endpoint {δ k cw:ℝ} (hδ:0<δ) (hδu:δ≤1/1000) (hk:1≤k)
    (hcw:0 < cw) (hcwu:cw*20002≤1) (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (b:ℕ→Ω→ℝ)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤k) (t:ℕ) (ω:Ω) (hb:0≤b t ω) (hbu:b t ω≤4)
    (p:J×R→ℝ) (hp:∀ ir,p ir∈Set.Icc 0 1) :
    let ell:=1+Real.log (k+1)
    let hel:0<ell:=by have h:=Real.log_nonneg (show 1≤k+1 by linarith); dsimp [ell]; linarith
    let d:=input hcw hel δ P key b
    let a:=proportion hcw hel δ P key b
    |(family 40).value (d t ω).data p (a t ω)|≤
      200000*(1/cw+1)*ell*EpochSchedule.total (vector cutoff δ P ω t) := by
  intro ell hel d a
  have hell:1≤ell:=by dsimp [ell]; linarith [Real.log_nonneg (show 1≤k+1 by linarith)]
  have hM (i:J):b t ω+cw*logs δ P key t ω i/ell≤5:=by
    have h:=SideActualEdits.theta_bound hδ hδu hk hcw hcwu P key hs t ω i
    change cw*logs δ P key t ω i/ell≤1 at h
    linarith
  have h:=SideProfile.endpoint hcw hell (sides δ P key t ω) (sideFlags δ P key t ω)
    (logs δ P key t ω) (fun i=>le_max_left _ _) hb hM (scale_nonneg δ P key t ω)
    p (fun ir=>(hp ir).1) (a t ω) (proportion_mem hcw hel δ P key b t ω)
  change |(family 40).value (d t ω).data p (a t ω)|≤
    640*(1/cw+1)*ell*scale δ P key t ω+(3600/cw*ell)*(∑ i,core (d t ω).data p i) at h
  have hD:=mul_le_mul_of_nonneg_left (scale_bound hδ hδu P key t ω)
    (show 0≤640*(1/cw+1)*ell by positivity)
  have hB:=mul_le_mul_of_nonneg_left (core_bound hδ hδu hcw hel P key b t ω p hp)
    (show 0≤3600/cw*ell by positivity)
  have hn:=EpochSchedule.total_nonneg (vector_nonneg cutoff δ P ω t)
  have he:0≤ell*EpochSchedule.total (vector cutoff δ P ω t):=mul_nonneg hel.le hn
  have hc:0≤1/cw*(ell*EpochSchedule.total (vector cutoff δ P ω t)):=by positivity
  change (3600/cw*ell)*(∑ i,core (d t ω).data p i)≤_ at hB
  simp only [div_eq_mul_inv,one_mul] at h hD hB he hc ⊢
  nlinarith only [h,hD,hB,he,hc]

lemma variation_bound {cw ell:ℝ} (hcw:0 < cw) (hel:0<ell) (δ:ℝ)
    (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (b:ℕ→Ω→ℝ) (t:ℕ) (ω:Ω) :
    ChangingDomains.variation (proportion hcw hel δ P key b (t+1) ω) (proportion hcw hel δ P key b t ω)≤32 := by
  have ha:=proportion_mem hcw hel δ P key b t ω
  have ha':=proportion_mem hcw hel δ P key b (t+1) ω
  calc _≤∑ i,(proportion hcw hel δ P key b (t+1) ω i+proportion hcw hel δ P key b t ω i) := by
        exact sum_le_sum fun i _=>(abs_sub _ _).trans_eq (by rw [abs_of_nonneg (ha'.1 i),abs_of_nonneg (ha.1 i)])
       _≤32 := by rw [sum_add_distrib]; linarith [ha.2.1,ha'.2.1]

end KServer.SideActualBounds

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.SidePayment
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile AllocationSchedule StarSide SideFamilies
variable {Ω J R K : Type} [Fintype Ω] [Fintype J]  [Fintype R]
variable {w:Ω→ℝ}

lemma payment {δ k cw:ℝ} (hδ:0<δ) (hδu:δ≤1/1000) (hk:1≤k)
    (hcw:0 < cw) (hcwu:cw*20002≤1) (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (b:ℕ→Ω→ℝ)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤k) (t:ℕ) (ω:Ω)
    (hb:∀ s,1≤b s ω) (hbu:∀ s,b s ω≤4)
    (hbe: key t ω=key (t+1) ω→b t ω=b (t+1) ω) :
    let ell:=1+Real.log (k+1)
    let hel:0<ell:=by have h:=Real.log_nonneg (show 1≤k+1 by linarith); dsimp [ell]; linarith
    let d:=input hcw hel δ P key b
    let a:=proportion hcw hel δ P key b
    scale δ P key (t+1) ω*ChangingDomains.variation (a (t+1) ω) (a t ω)≤
      (family 40).value (d t ω).data (d (t+1) ω).ranks (a t ω)-
      (family 40).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)+expense cw ell δ P key t ω := by
  intro ell hel d a
  by_cases he:epoch (vector cutoff δ P ω) (fun s=>key s ω) t=
      epoch (vector cutoff δ P ω) (fun s=>key s ω) (t+1)
  · have hp:=ordinary hδ hδu hk hcw hcwu P key b hs t ω (hb t) (hbu t)
      (hbe (SideActualEdits.ordinary_key (vector cutoff δ P ω) (fun s=>key s ω) t he)) he
    change _≤(family 40).value (d t ω).data (d (t+1) ω).ranks (a t ω)-
      (family 40).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)+_+_+_ at hp
    simpa only [expense,ite_eq_left he,add_assoc] using hp
  · have h0:=SideActualBounds.endpoint hδ hδu hk hcw hcwu P key b hs t ω
      (by linarith [hb t] : 0≤b t ω) (hbu t) (d (t+1) ω).ranks (fun ir=>(P ir.1 ir.2).range (t+1) ω)
    have h1:=SideActualBounds.endpoint hδ hδu hk hcw hcwu P key b hs (t+1) ω
      (by linarith [hb (t+1)] : 0≤b (t+1) ω) (hbu (t+1)) (d (t+1) ω).ranks (fun ir=>(P ir.1 ir.2).range (t+1) ω)
    change |(family 40).value (d t ω).data (d (t+1) ω).ranks (a t ω)|≤_ at h0
    change |(family 40).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)|≤_ at h1
    have hv:=SideActualBounds.variation_bound hcw hel δ P key b t ω
    change ChangingDomains.variation (a (t+1) ω) (a t ω)≤32 at hv
    have hmv:=mul_le_mul_of_nonneg_left hv (scale_nonneg δ P key (t+1) ω)
    have hD:=SideActualBounds.scale_bound hδ hδu P key (t+1) ω
    have hel1:1≤ell:=by dsimp [ell]; linarith [Real.log_nonneg (show 1≤k+1 by linarith)]
    have hold:=EpochSchedule.total_nonneg (vector_nonneg cutoff δ P ω t)
    have hnew:=EpochSchedule.total_nonneg (vector_nonneg cutoff δ P ω (t+1))
    have hc:1≤(1/cw+1)*ell:=by
      have hc:0≤1/cw:=by positivity
      nlinarith only [hel1,hc]
    have hcost:=mul_le_mul_of_nonneg_right hc hnew
    have hor:0≤(1/cw+1)*ell*EpochSchedule.total (vector cutoff δ P ω t):=by positivity
    rw [expense,ite_eq_right he]
    have hlo:=neg_abs_le ((family 40).value (d t ω).data (d (t+1) ω).ranks (a t ω))
    have hhi:=le_abs_self ((family 40).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω))
    dsimp only [ell] at *
    nlinarith only [h0,h1,hmv,hD,hcost,hor,hlo,hhi,hnew]

end KServer.SidePayment

end


/-! Fixed absolute coefficients for actual simplex/side edits. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualCharges
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

lemma edit_constants_nonneg:0≤ simplexConstant ∧ 0≤ sideConstant:=by
  rcases constants_nonneg with ⟨ha,hp,hf⟩
  rcases more_constants_nonneg with ⟨hh,hs,hr⟩
  have hC:0< C:=positive.2.2.2.2.1
  have hc:0< cw:=positive.2.2.2.1
  have hl:0≤ Real.log 17:=Real.log_nonneg (by norm_num)
  dsimp only [simplexConstant,sideConstant,SideEdits.L,SideEdits.Q,SideEdits.K]
  constructor <;> positivity

lemma simplex_expense (hw:∀ ω,0≤ w ω) (hw1:∑ ω,w ω=1) {ell:ℝ} (hell:1≤ ell)
    (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (N:ℕ):
    total w N (ScheduledPayment.expense C ell ds P (key Q))≤ simplexConstant*ell*stock P Q N:=by
  have he:total w N (ScheduledPayment.expense C ell ds P (key Q))=
      (26*C*ell+4)*total w N (flags P)+320*C*ell*total w N (ActualCharges.active P)+
      2976*C*ell*total w N (sideRefresh P Q)+(520*C*ell+80)*total w N (wholesale P Q):=by
    change total w N (fun t ω=>(26*C*ell+4)*flags P t ω+320*C*ell*ActualCharges.active P t ω+
      2976*C*ell*sideRefresh P Q t ω+(520*C*ell+80)*wholesale P Q t ω)=_
    rw [total_add,total_add,total_add,total_mul,total_mul,total_mul,total_mul]
  have hf:=flags_bound hw hw1 P Q N
  have ha:=active_bound hw hw1 P Q N
  have hr:=sideRefresh_bound hw hw1 P Q N
  have hh:=wholesale_bound hw hw1 P Q hs N
  have hC:=positive.2.2.2.2.1
  have hstock:=stock_nonneg hw P Q N
  have hflag:=mul_nonneg constants_nonneg.2.2 hstock
  have hwhole:=mul_nonneg more_constants_nonneg.1 hstock
  have hb:total w N (ScheduledPayment.expense C ell ds P (key Q))≤
      (26*C*ell+4)*(flagConstant*stock P Q N)+320*C*ell*(activeConstant*stock P Q N)+
      2976*C*ell*(sideRefreshConstant*stock P Q N)+(520*C*ell+80)*(wholesaleConstant*stock P Q N):=by
    rw [he]
    gcongr
  dsimp only [simplexConstant]
  nlinarith [mul_nonneg (sub_nonneg.mpr hell) hflag,mul_nonneg (sub_nonneg.mpr hell) hwhole]

lemma side_expense_step {ell:ℝ} (hell:0≤ ell) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (t:ℕ) (ω:Ω):
    SidePayment.expense cw ell ds P (key Q) t ω≤
      SideEdits.L cw ell*|ActualOutput.D P Q (t+1) ω-ActualOutput.D P Q t ω|+
      SideEdits.Q cw ell*flags P t ω+40*SideEdits.K cw ell*ActualCharges.active P t ω+
      300000*(1/cw+1)*ell*wholesale P Q t ω:=by
  have hc:0< cw:=positive.2.2.2.1
  have hl:0≤ Real.log 17:=Real.log_nonneg (by norm_num)
  have hf:=flags_nonneg P t ω
  have ha:=active_nonneg P t ω
  have hd:=abs_nonneg (ActualOutput.D P Q (t+1) ω-ActualOutput.D P Q t ω)
  have hw:=wholesale_nonneg P Q t ω
  unfold SidePayment.expense
  split_ifs
  · change _≤ SideEdits.L cw ell*|StarSide.scale ds P (key Q) (t+1) ω-StarSide.scale ds P (key Q) t ω|+
      SideEdits.Q cw ell*flags P t ω+40*SideEdits.K cw ell*ActualCharges.active P t ω+_
    exact le_add_of_nonneg_right (by positivity)
  · have he:EpochSchedule.reset (vector cutoff ds P ω t) (vector cutoff ds P ω (t+1))
      (key Q t ω) (key Q (t+1) ω) (EpochSchedule.run (vector cutoff ds P ω) (fun s=> key Q s ω) t):=by
      exact not_not.mp (fun hn=> by rename_i hh; exact hh ((epoch_same_iff _ _ t).mpr hn))
    rw [wholesale,EpochSchedule.wholesale,ite_eq_left he]
    dsimp only [SideEdits.L,SideEdits.Q,SideEdits.K]
    have h1:0≤ SideEdits.L cw ell*|ActualOutput.D P Q (t+1) ω-ActualOutput.D P Q t ω|:=by
      dsimp only [SideEdits.L]; positivity
    have h2:0≤ SideEdits.Q cw ell*flags P t ω:=by dsimp only [SideEdits.Q]; positivity
    have h3:0≤40*SideEdits.K cw ell*ActualCharges.active P t ω:=by dsimp only [SideEdits.K]; positivity
    dsimp only [SideEdits.L,SideEdits.Q,SideEdits.K] at h1 h2 h3
    linarith

lemma side_expense (hw:∀ ω,0≤ w ω) (hw1:∑ ω,w ω=1) {ell:ℝ} (hell:0≤ ell)
    (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (N:ℕ):
    total w N (SidePayment.expense cw ell ds P (key Q))≤ sideConstant*ell*stock P Q N:=by
  have h:=total_mono hw (N:=N) (side_expense_step hell P Q)
  rw [total_add,total_add,total_add,total_mul,total_mul,total_mul,total_mul] at h
  have hD:=scale_bound hw hw1 P Q hs N
  have hf:=flags_bound hw hw1 P Q N
  have ha:=active_bound hw hw1 P Q N
  have hh:=wholesale_bound hw hw1 P Q hs N
  have hc:0< cw:=positive.2.2.2.1
  have hl:0≤ Real.log 17:=Real.log_nonneg (by norm_num)
  calc _≤ _:=h
       _≤ SideEdits.L cw ell*(scaleConstant*stock P Q N)+SideEdits.Q cw ell*(flagConstant*stock P Q N)+
      40*SideEdits.K cw ell*(activeConstant*stock P Q N)+300000*(1/cw+1)*ell*(wholesaleConstant*stock P Q N):=by
        dsimp only [SideEdits.L,SideEdits.Q,SideEdits.K]
        gcongr
       _= _:=by dsimp only [sideConstant,SideEdits.L,SideEdits.Q,SideEdits.K]; ring
end KServer.ActualCharges

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_AllocationBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! True-prefix filtering followed by paid literal profile edits.  In particular
no event chosen at the new history is allowed to select a filtering term. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ScheduledFiltering
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile AllocationSchedule
open SimplexFamilies AdaptiveAllocation AdaptiveMinimization
variable {Ω J R K : Type} [Fintype Ω] [Fintype J] [DecidableEq J] [Fintype R]
variable {w : Ω→ℝ}

lemma filtering_zero {δ:ℝ} (hδ:0<δ) (hδu:δ≤1/1000) (C ell ct:ℝ)
    (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (H:ℕ→Ω→ℕ)
    (hH:∀ i r t ω,(P i r).history t ω=H t ω)
    (hr:∀ t ω z,H (t+1) ω=H (t+1) z→H t ω=H t z)
    (hkey:∀ t ω z,H t ω=H t z→key t ω=key t z) (t:ℕ) :
    let d:=StarSimplex.input hδ hδu C ell ct P key
    let a:=StarSimplex.proportion hδ hδu C ell ct P key
    avg w (fun ω=>(family C ell).value (d t ω).data (fun ir=>(P ir.1 ir.2).before (t+1) ω) (a t ω)-
      (family C ell).value (d t ω).data (d t ω).ranks (a t ω))=0 := by
  intro d a
  simp_rw [(family C ell).input_difference]
  rw [avg_sum_any]
  apply sum_eq_zero
  intro ir _
  apply filtering_affine (P ir.1 ir.2)
  intro ω z he
  rw [hH,hH] at he
  have hd:=congrArg CausalSimplex.Input.data (StarSimplex.input_adapted hδ hδu C ell ct P key H hH hr hkey t ω z he)
  have ha:=StarSimplex.proportion_adapted hδ hδu C ell ct P key H hH hr hkey t ω z he
  change (family C ell).coefficient (d t ω).data (a t ω) ir=(family C ell).coefficient (d t z).data (a t z) ir
  change (d t ω).data=(d t z).data at hd
  change a t ω=a t z at ha
  rw [hd,ha]

lemma payment_step {δ C ct k:ℝ} (hδ:0<δ) (hδu:δ≤1/1000)
    (hC:0<C) (hct:0 < ct) (hctu:ct*20002≤1) (hgap:700<C*ct) (hk:1≤k)
    (hw:∀ ω,0≤w ω) (P:J→R→FilteredRanks w) (key:ℕ→Ω→K)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤k) (H:ℕ→Ω→ℕ)
    (hH:∀ i r t ω,(P i r).history t ω=H t ω)
    (hr:∀ t ω z,H (t+1) ω=H (t+1) z→H t ω=H t z)
    (hkey:∀ t ω z,H t ω=H t z→key t ω=key t z) (t:ℕ) :
    let ell:=1+Real.log (k+1)
    let d:=StarSimplex.input hδ hδu C ell ct P key
    let a:=StarSimplex.proportion hδ hδu C ell ct P key
    avg w (fun ω=>CausalSimplex.mass (d (t+1) ω)*ChangingDomains.variation (a (t+1) ω) (a t ω))≤
      avg w (fun ω=>(family C ell).value (d t ω).data (d t ω).ranks (a t ω))-
      avg w (fun ω=>(family C ell).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω))+
      13*C*ell*(∑ ir:J×R,avg w (fun ω=>|(P ir.1 ir.2).p (t+1) ω-(P ir.1 ir.2).before (t+1) ω|))+
      avg w (ScheduledPayment.expense C ell δ P key t) := by
  intro ell d a
  have hpoint (ω:Ω) : CausalSimplex.mass (d (t+1) ω)*ChangingDomains.variation (a (t+1) ω) (a t ω)≤
      ((family C ell).value (d t ω).data (d t ω).ranks (a t ω)-
      (family C ell).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω))+
      ((family C ell).value (d t ω).data (fun ir=>(P ir.1 ir.2).before (t+1) ω) (a t ω)-
      (family C ell).value (d t ω).data (d t ω).ranks (a t ω))+
      13*C*ell*(∑ ir:J×R,|(P ir.1 ir.2).p (t+1) ω-(P ir.1 ir.2).before (t+1) ω|)+
      ScheduledPayment.expense C ell δ P key t ω := by
    have hp:=ScheduledPayment.payment hδ hδu hC hct hctu hgap hk P key hs t ω
    have ha:=StarSimplex.proportion_mem hδ hδu C ell ct P key t ω
    have hl:=ScheduledSlope.actual_bound hδ hδu hC.le hct.le hctu hk P key hs t ω _ ha
    have hd: (family C ell).value (d t ω).data (d (t+1) ω).ranks (a t ω)-
        (family C ell).value (d t ω).data (fun ir=>(P ir.1 ir.2).before (t+1) ω) (a t ω)≤
        13*C*ell*(∑ ir:J×R,|(P ir.1 ir.2).p (t+1) ω-(P ir.1 ir.2).before (t+1) ω|) :=
      (le_abs_self _).trans ((family C ell).input_lipschitz (d t ω).data _ _ (a t ω) hl)
    change _≤(family C ell).value (d t ω).data (d (t+1) ω).ranks (a t ω)-
      (family C ell).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)+_ at hp
    linarith
  have he:=avg_mono hw hpoint
  simp only [avg_add,avg_sub,avg_mul,avg_sum_any] at he
  have hf:=filtering_zero hδ hδu C ell ct P key H hH hr hkey t
  dsimp only at hf
  rw [avg_sub] at hf
  change avg w (fun ω=>(family C ell).value (d t ω).data (fun ir=>(P ir.1 ir.2).before (t+1) ω) (a t ω))-
    avg w (fun ω=>(family C ell).value (d t ω).data (d t ω).ranks (a t ω))=0 at hf
  rw [hf,add_zero] at he
  exact he

lemma payment {δ C ct k:ℝ} (hδ:0<δ) (hδu:δ≤1/1000)
    (hC:0<C) (hct:0 < ct) (hctu:ct*20002≤1) (hgap:700<C*ct) (hk:1≤k)
    (hw:∀ ω,0≤w ω) (P:J→R→FilteredRanks w) (key:ℕ→Ω→K)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤k) (H:ℕ→Ω→ℕ)
    (hH:∀ i r t ω,(P i r).history t ω=H t ω)
    (hr:∀ t ω z,H (t+1) ω=H (t+1) z→H t ω=H t z)
    (hkey:∀ t ω z,H t ω=H t z→key t ω=key t z) (n:ℕ) :
    let ell:=1+Real.log (k+1)
    let d:=StarSimplex.input hδ hδu C ell ct P key
    let a:=StarSimplex.proportion hδ hδu C ell ct P key
    (∑ t∈range n,avg w (fun ω=>CausalSimplex.mass (d (t+1) ω)*ChangingDomains.variation (a (t+1) ω) (a t ω)))≤
      avg w (fun ω=>(family C ell).value (d 0 ω).data (d 0 ω).ranks (a 0 ω))-
      avg w (fun ω=>(family C ell).value (d n ω).data (d n ω).ranks (a n ω))+
      13*C*ell*(∑ t∈range n,∑ ir:J×R,avg w (fun ω=>|(P ir.1 ir.2).p (t+1) ω-(P ir.1 ir.2).before (t+1) ω|))+
      ∑ t∈range n,avg w (ScheduledPayment.expense C ell δ P key t) := by
  intro ell d a
  induction n with
  | zero=>simp
  | succ n ih=>
    simp only [sum_range_succ]
    have hp:=payment_step hδ hδu hC hct hctu hgap hk hw P key hs H hH hr hkey n
    change avg w (fun ω=>CausalSimplex.mass (d (n+1) ω)*ChangingDomains.variation (a (n+1) ω) (a n ω))≤
      avg w (fun ω=>(family C ell).value (d n ω).data (d n ω).ranks (a n ω))-
      avg w (fun ω=>(family C ell).value (d (n+1) ω).data (d (n+1) ω).ranks (a (n+1) ω))+_+_ at hp
    linarith

lemma bounded_endpoint {δ C ct k:ℝ} (hδ:0<δ) (hδu:δ≤1/1000)
    (hC:0≤C) (hct:0 ≤ ct) (hctu:ct*20002≤1) (hk:1≤k)
    (hw:∀ ω,0≤w ω) (hw1:∑ ω,w ω=1) (P:J→R→FilteredRanks w) (key:ℕ→Ω→K)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤k) (t:ℕ) :
    let ell:=1+Real.log (k+1)
    let d:=StarSimplex.input hδ hδu C ell ct P key
    let a:=StarSimplex.proportion hδ hδu C ell ct P key
    |avg w (fun ω=>(family C ell).value (d t ω).data (d t ω).ranks (a t ω))|≤572*C*ell*k := by
  intro ell d a
  have hel:0≤ell:=by dsimp [ell]; have h:=Real.log_nonneg (show 1≤k+1 by linarith); linarith
  calc _≤avg w (fun ω=>|(family C ell).value (d t ω).data (d t ω).ranks (a t ω)|) := by
        unfold avg
        exact (abs_sum_le_sum_abs _ _).trans_eq (by
          congr 1; funext ω; rw [abs_mul,abs_of_nonneg (hw ω)])
       _≤avg w (fun _=>572*C*ell*k) := by
        apply avg_mono hw
        intro ω
        have h:=ScheduledEndpoint.actual_bound hδ hδu hC hct hctu hk P key hs t ω
          (d t ω).ranks (fun ir=>(P ir.1 ir.2).range t ω) (a t ω)
          (StarSimplex.proportion_mem hδ hδu C ell ct P key t ω)
        have ht:=StarProfile.vector_total hδ hδu P t ω (hs t ω)
        have hm:=mul_le_mul_of_nonneg_left ht (show 0≤520*C*ell by positivity)
        change |(family C ell).value (d t ω).data (d t ω).ranks (a t ω)|≤520*C*ell*EpochSchedule.total (vector cutoff δ P ω t) at h
        change (∑ i,vector cutoff δ P ω t i)≤_ at ht
        unfold EpochSchedule.total at h hm
        nlinarith
       _= _ :=avg_const w hw1 _

end KServer.ScheduledFiltering

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.SideFiltering
attribute [local instance] Classical.propDecidable Classical.decEq
open AdaptiveMinimization RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile AllocationSchedule StarSide SideFamilies
variable {Ω J R K : Type} [Fintype Ω] [Fintype J]  [Fintype R]
variable {w:Ω→ℝ}

lemma filtering_zero {cw ell:ℝ} (hcw:0 < cw) (hel:0<ell) (δ:ℝ)
    (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (b:ℕ→Ω→ℝ) (H:ℕ→Ω→ℕ)
    (hH:∀ i r t ω,(P i r).history t ω=H t ω)
    (hr:∀ t ω z,H (t+1) ω=H (t+1) z→H t ω=H t z)
    (hkey:∀ t ω z,H t ω=H t z→key t ω=key t z)
    (hb:∀ t ω z,H t ω=H t z→b t ω=b t z) (t:ℕ) :
    let d:=input hcw hel δ P key b
    let a:=proportion hcw hel δ P key b
    avg w (fun ω=>(family 40).value (d t ω).data (fun ir=>(P ir.1 ir.2).before (t+1) ω) (a t ω)-
      (family 40).value (d t ω).data (d t ω).ranks (a t ω))=0 := by
  intro d a
  simp_rw [(family 40).input_difference]
  rw [avg_sum_any]
  apply sum_eq_zero
  intro ir _
  apply filtering_affine (P ir.1 ir.2)
  intro ω z he
  rw [hH,hH] at he
  have hd:=congrArg CausalSide.Input.data (input_adapted hcw hel δ P key b H hH hr hkey hb t ω z he)
  have ha:=proportion_adapted hcw hel δ P key b H hH hr hkey hb t ω z he
  change (family 40).coefficient (d t ω).data (a t ω) ir=(family 40).coefficient (d t z).data (a t z) ir
  change (d t ω).data=(d t z).data at hd
  change a t ω=a t z at ha
  rw [hd,ha]

lemma slope {δ k cw:ℝ} (hδ:0<δ) (hδu:δ≤1/1000) (hk:1≤k)
    (hcw:0 < cw) (hcwu:cw*20002≤1) (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (b:ℕ→Ω→ℝ)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤k) (t:ℕ) (ω:Ω) (hb:0≤b t ω) (hbu:b t ω≤4) :
    let ell:=1+Real.log (k+1)
    let hel:0<ell:=by have h:=Real.log_nonneg (show 1≤k+1 by linarith); dsimp [ell]; linarith
    let d:=input hcw hel δ P key b
    let a:=proportion hcw hel δ P key b
    ∀ ir,|(family 40).coefficient (d t ω).data (a t ω) ir|≤3600/cw*ell := by
  intro ell hel d a ir
  have hell:1≤ell:=by dsimp [ell]; linarith [Real.log_nonneg (show 1≤k+1 by linarith)]
  have hM (i:J):b t ω+cw*logs δ P key t ω i/ell≤5:=by
    have h:=SideActualEdits.theta_bound hδ hδu hk hcw hcwu P key hs t ω i
    change cw*logs δ P key t ω i/ell≤1 at h
    linarith
  exact SideProfile.coefficient_bound hcw hell (sides δ P key t ω) (sideFlags δ P key t ω)
    (logs δ P key t ω) (fun i=>le_max_left _ _) hb hM (a t ω) (proportion_mem hcw hel δ P key b t ω) ir

lemma payment_step {δ k cw:ℝ} (hδ:0<δ) (hδu:δ≤1/1000) (hk:1≤k)
    (hcw:0 < cw) (hcwu:cw*20002≤1) (hw:∀ ω,0≤w ω)
    (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (b:ℕ→Ω→ℝ)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤k)
    (hb:∀ t ω,1≤b t ω) (hbu:∀ t ω,b t ω≤4)
    (hbe:∀ t ω,key t ω=key (t+1) ω→b t ω=b (t+1) ω)
    (H:ℕ→Ω→ℕ) (hH:∀ i r t ω,(P i r).history t ω=H t ω)
    (hr:∀ t ω z,H (t+1) ω=H (t+1) z→H t ω=H t z)
    (hkey:∀ t ω z,H t ω=H t z→key t ω=key t z)
    (hbad:∀ t ω z,H t ω=H t z→b t ω=b t z) (t:ℕ) :
    let ell:=1+Real.log (k+1)
    let hel:0<ell:=by have h:=Real.log_nonneg (show 1≤k+1 by linarith); dsimp [ell]; linarith
    let d:=input hcw hel δ P key b
    let a:=proportion hcw hel δ P key b
    avg w (fun ω=>scale δ P key (t+1) ω*ChangingDomains.variation (a (t+1) ω) (a t ω))≤
      avg w (fun ω=>(family 40).value (d t ω).data (d t ω).ranks (a t ω))-
      avg w (fun ω=>(family 40).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω))+
      3600/cw*ell*(∑ ir:J×R,avg w (fun ω=>|(P ir.1 ir.2).p (t+1) ω-(P ir.1 ir.2).before (t+1) ω|))+
      avg w (SidePayment.expense cw ell δ P key t) := by
  intro ell hel d a
  have hpoint (ω:Ω) : scale δ P key (t+1) ω*ChangingDomains.variation (a (t+1) ω) (a t ω)≤
      ((family 40).value (d t ω).data (d t ω).ranks (a t ω)-
      (family 40).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω))+
      ((family 40).value (d t ω).data (fun ir=>(P ir.1 ir.2).before (t+1) ω) (a t ω)-
      (family 40).value (d t ω).data (d t ω).ranks (a t ω))+
      3600/cw*ell*(∑ ir:J×R,|(P ir.1 ir.2).p (t+1) ω-(P ir.1 ir.2).before (t+1) ω|)+
      SidePayment.expense cw ell δ P key t ω := by
    have hp:=SidePayment.payment hδ hδu hk hcw hcwu P key b hs t ω (fun s=>hb s ω) (fun s=>hbu s ω) (hbe t ω)
    have hl:=slope hδ hδu hk hcw hcwu P key b hs t ω (by linarith [hb t ω]) (hbu t ω)
    have hd: (family 40).value (d t ω).data (d (t+1) ω).ranks (a t ω)-
        (family 40).value (d t ω).data (fun ir=>(P ir.1 ir.2).before (t+1) ω) (a t ω)≤
        3600/cw*ell*(∑ ir:J×R,|(P ir.1 ir.2).p (t+1) ω-(P ir.1 ir.2).before (t+1) ω|) :=
      (le_abs_self _).trans ((family 40).input_lipschitz (d t ω).data _ _ (a t ω) hl)
    change _≤(family 40).value (d t ω).data (d (t+1) ω).ranks (a t ω)-
      (family 40).value (d (t+1) ω).data (d (t+1) ω).ranks (a (t+1) ω)+_ at hp
    linarith
  have he:=avg_mono hw hpoint
  simp only [avg_add,avg_sub,avg_mul,avg_sum_any] at he
  have hf:=filtering_zero hcw hel δ P key b H hH hr hkey hbad t
  dsimp only at hf
  rw [avg_sub] at hf
  change avg w (fun ω=>(family 40).value (d t ω).data (fun ir=>(P ir.1 ir.2).before (t+1) ω) (a t ω))-
    avg w (fun ω=>(family 40).value (d t ω).data (d t ω).ranks (a t ω))=0 at hf
  rw [hf,add_zero] at he
  exact he

lemma payment {δ k cw:ℝ} (hδ:0<δ) (hδu:δ≤1/1000) (hk:1≤k)
    (hcw:0 < cw) (hcwu:cw*20002≤1) (hw:∀ ω,0≤w ω)
    (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (b:ℕ→Ω→ℝ)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤k)
    (hb:∀ t ω,1≤b t ω) (hbu:∀ t ω,b t ω≤4)
    (hbe:∀ t ω,key t ω=key (t+1) ω→b t ω=b (t+1) ω)
    (H:ℕ→Ω→ℕ) (hH:∀ i r t ω,(P i r).history t ω=H t ω)
    (hr:∀ t ω z,H (t+1) ω=H (t+1) z→H t ω=H t z)
    (hkey:∀ t ω z,H t ω=H t z→key t ω=key t z)
    (hbad:∀ t ω z,H t ω=H t z→b t ω=b t z) (n:ℕ) :
    let ell:=1+Real.log (k+1)
    let hel:0<ell:=by have h:=Real.log_nonneg (show 1≤k+1 by linarith); dsimp [ell]; linarith
    let d:=input hcw hel δ P key b
    let a:=proportion hcw hel δ P key b
    (∑ t∈range n,avg w (fun ω=>scale δ P key (t+1) ω*ChangingDomains.variation (a (t+1) ω) (a t ω)))≤
      avg w (fun ω=>(family 40).value (d 0 ω).data (d 0 ω).ranks (a 0 ω))-
      avg w (fun ω=>(family 40).value (d n ω).data (d n ω).ranks (a n ω))+
      3600/cw*ell*(∑ t∈range n,∑ ir:J×R,avg w (fun ω=>|(P ir.1 ir.2).p (t+1) ω-(P ir.1 ir.2).before (t+1) ω|))+
      ∑ t∈range n,avg w (SidePayment.expense cw ell δ P key t) := by
  intro ell hel d a
  induction n with
  | zero=>simp
  | succ n ih=>
    simp only [sum_range_succ]
    have hp:=payment_step hδ hδu hk hcw hcwu hw P key b hs hb hbu hbe H hH hr hkey hbad n
    change avg w (fun ω=>scale δ P key (n+1) ω*ChangingDomains.variation (a (n+1) ω) (a n ω))≤
      avg w (fun ω=>(family 40).value (d n ω).data (d n ω).ranks (a n ω))-
      avg w (fun ω=>(family 40).value (d (n+1) ω).data (d (n+1) ω).ranks (a (n+1) ω))+_+_ at hp
    linarith

end KServer.SideFiltering

end


/-! Expected movement of the literal minimizers, with uniform endpoint bills. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualCharges
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar ActualOutput
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

lemma drift_le_stock (hw:∀ ω,0≤w ω) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (N:ℕ):
    drift (flat P) N≤ stock P Q N:=
  (le_add_of_nonneg_right (Nat.cast_nonneg (Fintype.card (J×R)))).trans (inventory_child_le hw P Q N)
lemma raw_drift_eq (P:J→R→FilteredRanks w) (N:ℕ):
    (∑ t∈range N,∑ ir:J×R,avg w (fun ω=>|(P ir.1 ir.2).p (t+1) ω-(P ir.1 ir.2).before (t+1) ω|))=
      drift (flat P) N:=by simp only [drift,flat,avg_sum]

lemma simplex_mass (k:ℝ) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):
    CausalSimplex.mass (StarSimplex.input (δ:=ds) (by norm_num [ds]) (by norm_num [ds])
      C (ActualCaps.ell k) ct P (key Q) t ω)=S P t ω:=by
  simp only [CausalSimplex.mass,StarSimplex.input_core]
  rfl

lemma simplex_movement {k:ℝ} (hk:1≤k) (hw:∀ ω,0≤w ω) (hw1:∑ ω,w ω=1)
    (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤k)
    (H:ℕ→Ω→ℕ) (hP:∀ i r t ω,(P i r).history t ω=H t ω)
    (hQ:∀ r t ω,(Q r).history t ω=H t ω)
    (hr:∀ t ω z,H (t+1) ω=H (t+1) z→H t ω=H t z) (N:ℕ):
    total w N (fun t ω=>S P (t+1) ω*ChangingDomains.variation (α k P Q (t+1) ω) (α k P Q t ω))≤
      1144*C*ActualCaps.ell k*k+(13*C+simplexConstant)*ActualCaps.ell k*stock P Q N:=by
  have hs' t ω: (∑ i,size (P i) t ω)≤k:=(hs t ω).trans (hq t ω)
  have hp:=ScheduledFiltering.payment (δ:=ds) (by norm_num [ds]) (by norm_num [ds])
    positive.2.2.2.2.1 positive.2.2.1 small.1 small.2.2.1 hk hw P (key Q) hs' H hP hr
    (key_adapted Q H hQ hr) N
  have he t:=ScheduledFiltering.bounded_endpoint (δ:=ds) (by norm_num [ds]) (by norm_num [ds])
    positive.2.2.2.2.1.le positive.2.2.1.le small.1 hk hw hw1 P (key Q) hs' t
  dsimp only at hp he
  have hl:(1+Real.log (k+1))=ActualCaps.ell k:=rfl
  simp only [hl,simplex_mass,raw_drift_eq] at hp he
  change total w N (fun t ω=>S P (t+1) ω*ChangingDomains.variation (α k P Q (t+1) ω) (α k P Q t ω))≤_ at hp
  have he0:=(abs_le.mp (he 0)).2
  have heN:=(abs_le.mp (he N)).1
  have hx:=simplex_expense hw hw1 (ActualCaps.ell_ge_one hk) P Q hs N
  have hd:=mul_le_mul_of_nonneg_left (drift_le_stock hw P Q N)
    (show 0≤13*C*ActualCaps.ell k by have hc:=positive.2.2.2.2.1; have he:=ActualCaps.ell_pos hk; positivity)
  dsimp only [total] at hx
  linarith only [hp,he0,heN,hx,hd]

lemma side_endpoint {k:ℝ} (hk:1≤k) (hw:∀ ω,0≤w ω) (hw1:∑ ω,w ω=1)
    (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤k) (t:ℕ):
    |avg w (fun ω=>(SideFamilies.family 40).value (sideData hk P Q t ω).data
      (sideData hk P Q t ω).ranks (side hk P Q t ω))|≤220000*(1/cw+1)*ActualCaps.ell k*k:=by
  have hc:0 < cw:=positive.2.2.2.1
  have hel:0<ActualCaps.ell k:=ActualCaps.ell_pos hk
  calc _≤avg w (fun ω=>|(SideFamilies.family 40).value (sideData hk P Q t ω).data
        (sideData hk P Q t ω).ranks (side hk P Q t ω)|):=by
          unfold avg
          exact (abs_sum_le_sum_abs _ _).trans_eq (by
            congr 1; funext ω; rw [abs_mul,abs_of_nonneg (hw ω)])
       _≤avg w (fun _=>220000*(1/cw+1)*ActualCaps.ell k*k):=by
          apply avg_mono hw
          intro ω
          have hp:=SideActualBounds.endpoint (δ:=ds) (by norm_num [ds]) (by norm_num [ds]) hk hc small.2.1
            P (key Q) (b k Q) (fun s z=>(hs s z).trans (hq s z)) t ω
            (by linarith [(b_range hk Q t ω (hq t ω)).1]) (b_range hk Q t ω (hq t ω)).2
            (sideData hk P Q t ω).ranks (fun ir=>(P ir.1 ir.2).range t ω)
          change |(SideFamilies.family 40).value (sideData hk P Q t ω).data
            (sideData hk P Q t ω).ranks (side hk P Q t ω)|≤_ at hp
          have ht:=StarProfile.vector_total (δ:=ds) (by norm_num [ds]) (by norm_num [ds]) P t ω ((hs t ω).trans (hq t ω))
          have hm:=mul_le_mul_of_nonneg_left ht (show 0≤200000*(1/cw+1)*ActualCaps.ell k by positivity)
          dsimp only [EpochSchedule.total,ActualCaps.ell] at hp hm ⊢
          nlinarith only [hp,hm]
       _= _:=avg_const w hw1 _

lemma side_movement {k:ℝ} (hk:1≤k) (hw:∀ ω,0≤w ω) (hw1:∑ ω,w ω=1)
    (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤k)
    (H:ℕ→Ω→ℕ) (hP:∀ i r t ω,(P i r).history t ω=H t ω)
    (hQ:∀ r t ω,(Q r).history t ω=H t ω)
    (hr:∀ t ω z,H (t+1) ω=H (t+1) z→H t ω=H t z) (N:ℕ):
    total w N (fun t ω=>D P Q (t+1) ω*ChangingDomains.variation (side hk P Q (t+1) ω) (side hk P Q t ω))≤
      440000*(1/cw+1)*ActualCaps.ell k*k+(3600/cw+sideConstant)*ActualCaps.ell k*stock P Q N:=by
  have hc:0 < cw:=positive.2.2.2.1
  have hel:0<ActualCaps.ell k:=ActualCaps.ell_pos hk
  have hp:=SideFiltering.payment (δ:=ds) (by norm_num [ds]) (by norm_num [ds]) hk hc small.2.1 hw
    P (key Q) (b k Q) (fun s z=>(hs s z).trans (hq s z))
    (fun t ω=>by linarith [(b_range hk Q t ω (hq t ω)).1])
    (fun t ω=>(b_range hk Q t ω (hq t ω)).2)
    (fun t ω he=>by unfold b; rw [he]) H hP hr
    (key_adapted Q H hQ hr) (b_adapted k Q H hQ hr) N
  dsimp only at hp
  have hl:(1+Real.log (k+1))=ActualCaps.ell k:=rfl
  simp only [hl,raw_drift_eq] at hp
  change total w N (fun t ω=>D P Q (t+1) ω*ChangingDomains.variation (side hk P Q (t+1) ω) (side hk P Q t ω))≤
    avg w (fun ω=>(SideFamilies.family 40).value (sideData hk P Q 0 ω).data (sideData hk P Q 0 ω).ranks (side hk P Q 0 ω))-
    avg w (fun ω=>(SideFamilies.family 40).value (sideData hk P Q N ω).data (sideData hk P Q N ω).ranks (side hk P Q N ω))+
    3600/cw*ActualCaps.ell k*drift (flat P) N+total w N (SidePayment.expense cw (ActualCaps.ell k) ds P (key Q)) at hp
  have he0:=(abs_le.mp (side_endpoint hk hw hw1 P Q hs hq 0)).2
  have heN:=(abs_le.mp (side_endpoint hk hw hw1 P Q hs hq N)).1
  have hx:=side_expense hw hw1 hel.le P Q hs N
  have hd:=mul_le_mul_of_nonneg_left (drift_le_stock hw P Q N) (show 0≤3600/cw*ActualCaps.ell k by positivity)
  linarith
end KServer.ActualCharges

end


/-! Switch charges from the actual regime recursion, including uniform
initialization and literal wholesale bills. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualCharges
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar ActualOutput
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

lemma ruleConstant_nonneg:0≤ ruleConstant:=by
  have hf:=constants_nonneg.2.2
  have hh:=more_constants_nonneg.1
  have hs:=more_constants_nonneg.2.1
  dsimp [ruleConstant]; positivity

lemma core_coarse (P:J→R→FilteredRanks w) (t:ℕ) (ω:Ω):
    S P t ω≤40*EpochSchedule.total (vector cutoff ds P ω t):=by
  unfold S EpochSchedule.total
  rw [mul_sum]
  exact sum_le_sum fun i _=>ScheduleEdits.raw_core_bound (δ:=ds) (by norm_num [ds])
    (by norm_num [ds]) (P i) t ω (fun r=>(P i r).p t ω) (fun r=>(P i r).range t ω)
lemma joint_coarse (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):
    S P t ω+D P Q t ω≤81*EpochSchedule.total (vector cutoff ds P ω t):=by
  have h:=SideActualBounds.scale_bound (δ:=ds) (by norm_num [ds]) (by norm_num [ds]) P (key Q) t ω
  change D P Q t ω≤_ at h
  linarith [core_coarse P t ω]
lemma ruleS_eq (P:J→R→FilteredRanks w):RuleSchedule.S (flat P) (ruleFlags P)=S P:=by
  funext t ω; exact rule_S P t ω
lemma ruleJ_eq (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w):
    RuleSchedule.J (flat P) (ruleFlags P) (marked P Q) (reset P Q) (D P Q)=switchCharge P Q:=by
  funext t ω
  simp only [RuleSchedule.J,ruleS_eq,switchCharge,rule]
lemma rule_expense_step (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):
    RuleSchedule.expense (flat P) (ruleFlags P) (reset P Q) (D P Q) t ω≤
      flags P t ω+|D P Q (t+1) ω-D P Q t ω|+81*wholesale P Q t ω:=by
  have hf:(∑ ir:J×R,if ruleFlags P t ω ir=ruleFlags P (t+1) ω ir then (0:ℝ) else 1)=flags P t ω:=by
    rw [flags_eq]
    apply sum_congr rfl
    intro ir _
    unfold ruleFlags CoreFlags.change
    by_cases h : CoreFlags.flag (P ir.1 ir.2) t ω=CoreFlags.flag (P ir.1 ir.2) (t+1) ω
    · simp only [ite_eq_left h,ite_eq_left h.symm]
    · simp only [ite_eq_right h,ite_eq_right (Ne.symm h)]
  simp only [RuleSchedule.expense,ruleS_eq,hf]
  apply add_le_add le_rfl
  cases he:reset P Q (t+1) ω with
  | false=>simp only [Bool.false_eq_true,ite_false]; exact mul_nonneg (by norm_num) (wholesale_nonneg P Q t ω)
  | true=>
    simp only [ite_true]
    have hr:EpochSchedule.reset (vector cutoff ds P ω t) (vector cutoff ds P ω (t+1))
      (key Q t ω) (key Q (t+1) ω) (EpochSchedule.run (vector cutoff ds P ω) (fun s=>key Q s ω) t):=by
        simpa only [reset,Nat.add_sub_cancel,decide_eq_true_eq] using he
    rw [wholesale,EpochSchedule.wholesale,ite_eq_left hr]
    have h:=joint_coarse P Q (t+1) ω
    linarith [EpochSchedule.total_nonneg (vector_nonneg cutoff ds P ω t)]
lemma rule_expense (hw:∀ ω,0≤w ω) (hw1:∑ ω,w ω=1)
    (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (N:ℕ):
    total w N (RuleSchedule.expense (flat P) (ruleFlags P) (reset P Q) (D P Q))≤ ruleConstant*stock P Q N:=by
  have h:=total_mono hw (N:=N) (rule_expense_step P Q)
  rw [total_add,total_add,total_mul] at h
  have hf:=flags_bound hw hw1 P Q N
  have hd:=scale_bound hw hw1 P Q hs N
  have hh:=wholesale_bound hw hw1 P Q hs N
  dsimp only [ruleConstant]
  linarith
lemma rule_initial {k:ℝ} (hk:1≤k) (hw:∀ ω,0≤w ω) (hw1:∑ ω,w ω=1)
    (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤k):
    avg w (RuleSchedule.potential (flat P) (ruleFlags P) (marked P Q) (reset P Q) (D P Q) 0)≤90*k:=by
  calc _≤avg w (fun _=>90*k):=by
        apply avg_mono hw
        intro ω
        have hv:=RuleSchedule.value_upper (S_nonneg P 0 ω) (D_nonneg P Q 0 ω) (marked P Q 0 ω) (rule P Q 0 ω)
        have hj:=joint_coarse P Q 0 ω
        have ht:=StarProfile.vector_total (δ:=ds) (by norm_num [ds]) (by norm_num [ds]) P 0 ω ((hs 0 ω).trans (hq 0 ω))
        simp only [RuleSchedule.potential,ruleS_eq]
        change RuleSchedule.value (marked P Q 0 ω) (rule P Q 0 ω) (S P 0 ω) (D P Q 0 ω)≤_
        unfold EpochSchedule.total at hj ht
        linarith
       _= _:=avg_const w hw1 _
lemma switch_movement {k:ℝ} (hk:1≤k) (hw:∀ ω,0≤w ω) (hw1:∑ ω,w ω=1)
    (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤k)
    (H:ℕ→Ω→ℕ) (hP:∀ i r t ω,(P i r).history t ω=H t ω)
    (hQ:∀ r t ω,(Q r).history t ω=H t ω)
    (hr:∀ t ω z,H (t+1) ω=H (t+1) z→H t ω=H t z) (N:ℕ):
    total w N (switchCharge P Q)≤180*k+2*(1+ruleConstant)*stock P Q N:=by
  have hp:=RuleSchedule.payment (flat P) (ruleFlags P) (marked P Q) (reset P Q) (D P Q) H hw
    (D_nonneg P Q) (fun t ω he=>congrArg Option.isSome (ordinary_mark P Q t ω he))
    (fun ir=> hP ir.1 ir.2) hr (flags_adapted P H hP) (marked_adapted P Q H hP hQ hr)
    (reset_adapted P Q H hP hQ hr) (D_adapted P Q H hP hQ hr) N
  simp only [ruleJ_eq,flat,raw_drift_eq] at hp
  have hi:=rule_initial hk hw hw1 P Q hs hq
  have he:=rule_expense hw hw1 P Q hs N
  have hd:=drift_le_stock hw P Q N
  change total w N (switchCharge P Q)≤2*(_+drift (flat P) N+_) at hp
  dsimp only [total] at he
  linarith only [hp,hi,he,hd]

end KServer.ActualCharges
end


/-! All-step output charging, including wholesale jumps without a charge per
child or per epoch. The parent variation retains coefficient exactly one. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualOutput
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar OutputDynamics
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

lemma coarse_output {k:ℝ} (hk:1≤ k) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤ k)
    (t:ℕ) (ω:Ω) (q:ℝ)
    (hp:(∑ i,(n P t ω i-β k Q t ω*B P t ω i+f k P Q t ω i))≤ q) (i:J):
    out hk P Q t ω q i≤80*vector cutoff ds P ω t i:=by
  have hd:=output_domination hk P Q hs hq t ω q hp i
  by_cases hi:i∈ActualStar.active P t ω
  · have hl:0<(CoarseProcess.active cutoff ds (P i) ω t).value:=by
      exact (AllocationSchedule.mem_activeSet (vector cutoff ds P ω t) i).mp hi
    have ha:=(active_accuracy (by norm_num [cutoff]:0 < cutoff) (by norm_num [ds]:0<ds)
      (by norm_num [ds]:ds≤1/1000) (P i) ω t).1
      ((live_iff (by norm_num [ds]) (by norm_num [ds]) (P i) t ω).mp hl)
    change _≤80*(CoarseProcess.active cutoff ds (P i) ω t).value
    linarith [ha.1]
  · have hf:=(out_feasible hk P Q hs hq t ω q hp).1 i
    rw [inactive_d hk P Q t ω (hq t ω) hi] at hf
    exact hf.2.trans (mul_nonneg (by norm_num) (vector_nonneg cutoff ds P ω t i))

lemma wholesale_output {k:ℝ} (hk:1≤ k) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤ k)
    (t:ℕ) (ω:Ω) (q q':ℝ)
    (hp:(∑ i,(n P t ω i-β k Q t ω*B P t ω i+f k P Q t ω i))≤ q)
    (hp':(∑ i,(n P (t+1) ω i-β k Q (t+1) ω*B P (t+1) ω i+f k P Q (t+1) ω i))≤ q')
    (he:reset P Q (t+1) ω=true):
    variation (out hk P Q (t+1) ω q') (out hk P Q t ω q)≤80*ActualCharges.wholesale P Q t ω:=by
  have hr:EpochSchedule.reset (vector cutoff ds P ω t) (vector cutoff ds P ω (t+1))
      (key Q t ω) (key Q (t+1) ω) (EpochSchedule.run (vector cutoff ds P ω) (fun s=>key Q s ω) t):=by
    simpa only [reset,Nat.add_sub_cancel,decide_eq_true_eq] using he
  rw [ActualCharges.wholesale,EpochSchedule.wholesale,ite_eq_left hr]
  calc _≤∑ i,(out hk P Q (t+1) ω q' i+out hk P Q t ω q i):=by
        apply sum_le_sum
        intro i _
        exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (output_domination hk P Q hs hq (t+1) ω q' hp' i).1,
          abs_of_nonneg (output_domination hk P Q hs hq t ω q hp i).1])
       _≤∑ i,(80*vector cutoff ds P ω (t+1) i+80*vector cutoff ds P ω t i):=
        sum_le_sum fun i _=>add_le_add (coarse_output hk P Q hs hq (t+1) ω q' hp' i)
          (coarse_output hk P Q hs hq t ω q hp i)
       _= _:=by simp only [sum_add_distrib,←mul_sum,EpochSchedule.total]; ring

lemma all_movement {k:ℝ} (hk:1≤ k) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤ k)
    (t:ℕ) (ω:Ω) (q q':ℝ)
    (hp:(∑ i,(n P t ω i-β k Q t ω*B P t ω i+f k P Q t ω i))≤ q)
    (hp':(∑ i,(n P (t+1) ω i-β k Q (t+1) ω*B P (t+1) ω i+f k P Q (t+1) ω i))≤ q'):
    variation (out hk P Q (t+1) ω q') (out hk P Q t ω q)≤
      |q'-q|+2*(if reset P Q (t+1) ω then 0 else variation (d k P Q (t+1) ω) (d k P Q t ω))+
      40*(S P (t+1) ω*variation (α k P Q (t+1) ω) (α k P Q t ω)+
        D P Q (t+1) ω*variation (side hk P Q (t+1) ω) (side hk P Q t ω)+
        |D P Q (t+1) ω-D P Q t ω|+switchCharge P Q t ω)+80*ActualCharges.wholesale P Q t ω:=by
  cases he:reset P Q (t+1) ω with
  | false=>
    simp only [Bool.false_eq_true,ite_false]
    exact (ordinary_movement hk P Q hs t ω (hq (t+1) ω) q q' hp' he).trans
      (le_add_of_nonneg_right (mul_nonneg (by norm_num) (ActualCharges.wholesale_nonneg P Q t ω)))
  | true=>
    have hh:=wholesale_output hk P Q hs hq t ω q q' hp hp' he
    simp only [ite_true,mul_zero,add_zero]
    have hS:=mul_nonneg (S_nonneg P (t+1) ω) (variation_nonneg (α k P Q (t+1) ω) (α k P Q t ω))
    have hD:=mul_nonneg (D_nonneg P Q (t+1) ω) (variation_nonneg (side hk P Q (t+1) ω) (side hk P Q t ω))
    linarith [abs_nonneg (q'-q),abs_nonneg (D P Q (t+1) ω-D P Q t ω),switchCharge_nonneg P Q t ω]
end KServer.ActualOutput

end


/-! The unconditional local allocation movement theorem for the
literal output already constructed. Its parent coefficient is exactly one;
all other costs are true drift and a fixed, law/horizon-independent inventory. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualCharges
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar ActualOutput
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

lemma output_constants_nonneg:0≤ fineConstant ∧ 0≤ movementConstant ∧ 0≤ endpointConstant ∧ 0<localConstant:=by
  have hc:=positive.2.2.2.2.1
  have hw:=positive.2.2.2.1
  have hr:=positive.2.2.2.2.2.2.2.1
  have hf:=constants_nonneg.2.2
  have hh:=more_constants_nonneg.1
  have hs:=more_constants_nonneg.2.1
  have he:=edit_constants_nonneg.1
  have he2:=edit_constants_nonneg.2
  have hb:=ruleConstant_nonneg
  have hfi:0≤ fineConstant:=by dsimp [fineConstant]; positivity
  have hm:0≤ movementConstant:=by dsimp only [movementConstant]; positivity
  have hep:0≤ endpointConstant:=by dsimp only [endpointConstant]; positivity
  refine ⟨hfi,hm,hep,?_⟩
  dsimp only [localConstant]; linarith

lemma fine_movement {k:ℝ} (hk:1≤ k) (hw:∀ ω,0≤ w ω) (hw1:∑ ω,w ω=1)
    (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (hq:∀ t ω,size Q t ω≤ k) (N:ℕ):
    total w N (fun t ω=>if reset P Q (t+1) ω then 0 else
      ChangingDomains.variation (d k P Q (t+1) ω) (d k P Q t ω))≤ fineConstant*ActualCaps.ell k*stock P Q N:=by
  have hp:=fine_budget hk hw hw1 P Q hq N
  change total w N (fun t ω=>if reset P Q (t+1) ω then 0 else
    ChangingDomains.variation (d k P Q (t+1) ω) (d k P Q t ω))≤
      2*(160/(rho/ActualCaps.ell k)+flagConstant)*inventory (flat P) N at hp
  have hc:0≤ 2*(160/(rho/ActualCaps.ell k)+flagConstant):=by
    have hr:=positive.2.2.2.2.2.2.2.1; have he:=ActualCaps.ell_pos hk; have hf:=constants_nonneg.2.2
    positivity
  have hu:=mul_le_mul_of_nonneg_left (inventory_child_le hw P Q N) hc
  have hell:=ActualCaps.ell_ge_one hk
  have hf:=mul_nonneg constants_nonneg.2.2 (stock_nonneg hw P Q N)
  have herr:=mul_nonneg (sub_nonneg.mpr hell) hf
  rw [div_div_eq_mul_div] at hp hu
  simp only [fineConstant,div_eq_mul_inv] at hp hu ⊢
  nlinarith only [hp,hu,herr]

lemma output_movement {k:ℝ} (hk:1≤ k) (hw:∀ ω,0≤ w ω) (hw1:∑ ω,w ω=1)
    (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤ k)
    (H:ℕ→Ω→ℕ) (hP:∀ i r t ω,(P i r).history t ω=H t ω)
    (hQ:∀ r t ω,(Q r).history t ω=H t ω)
    (hr:∀ t ω z,H (t+1) ω=H (t+1) z→H t ω=H t z)
    (q:ℕ→Ω→ℝ)
    (hp:∀ t ω,(∑ i,(n P t ω i-β k Q t ω*B P t ω i+f k P Q t ω i))≤ q t ω) (N:ℕ):
    total w N (fun t ω=>ChangingDomains.variation (out hk P Q (t+1) ω (q (t+1) ω)) (out hk P Q t ω (q t ω)))≤
      total w N (fun t ω=>|q (t+1) ω-q t ω|)+
        movementConstant*ActualCaps.ell k*stock P Q N+endpointConstant*ActualCaps.ell k*k:=by
  have h:=total_mono hw (N:=N) (fun t ω=>all_movement hk P Q hs hq t ω (q t ω) (q (t+1) ω) (hp t ω) (hp (t+1) ω))
  simp only [total_add,total_mul] at h
  simp only [OutputDynamics.variation,ChangingDomains.variation] at h ⊢
  have hf:=fine_movement hk hw hw1 P Q hq N
  have ha:=simplex_movement hk hw hw1 P Q hs hq H hP hQ hr N
  have hb:=side_movement hk hw hw1 P Q hs hq H hP hQ hr N
  have hd:=scale_bound hw hw1 P Q hs N
  have hc:=switch_movement hk hw hw1 P Q hs hq H hP hQ hr N
  have hh:=wholesale_bound hw hw1 P Q hs N
  simp only [ChangingDomains.variation] at hf ha hb
  have hel:=ActualCaps.ell_ge_one hk
  have hst:=stock_nonneg hw P Q N
  have h1:=mul_nonneg (sub_nonneg.mpr hel) (mul_nonneg more_constants_nonneg.2.1 hst)
  have h2:=mul_nonneg (sub_nonneg.mpr hel) (mul_nonneg more_constants_nonneg.1 hst)
  have h3:=mul_nonneg (sub_nonneg.mpr hel) (mul_nonneg (add_nonneg zero_le_one ruleConstant_nonneg) hst)
  have h4:=mul_nonneg (sub_nonneg.mpr hel) (show 0≤ k by linarith)
  dsimp only [movementConstant,endpointConstant]
  nlinarith only [h,hf,ha,hb,hd,hc,hh,h1,h2,h3,h4]

lemma local_movement {k:ℝ} (hk:1≤ k) (hw:∀ ω,0≤ w ω) (hw1:∑ ω,w ω=1)
    (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤ k)
    (H:ℕ→Ω→ℕ) (hP:∀ i r t ω,(P i r).history t ω=H t ω)
    (hQ:∀ r t ω,(Q r).history t ω=H t ω)
    (hr:∀ t ω z,H (t+1) ω=H (t+1) z→H t ω=H t z)
    (q:ℕ→Ω→ℝ)
    (hp:∀ t ω,(∑ i,(n P t ω i-β k Q t ω*B P t ω i+f k P Q t ω i))≤ q t ω) (N:ℕ):
    total w N (fun t ω=>ChangingDomains.variation (out hk P Q (t+1) ω (q (t+1) ω)) (out hk P Q t ω (q t ω)))≤
      total w N (fun t ω=>|q (t+1) ω-q t ω|)+
        localConstant*ActualCaps.ell k*(drift (flat P) N+drift Q N+(Fintype.card (J×R):ℝ)+Fintype.card R+k):=by
  have h:=output_movement hk hw hw1 P Q hs hq H hP hQ hr q hp N
  have hs0:=stock_nonneg hw P Q N
  have hek:=mul_nonneg (ActualCaps.ell_pos hk).le (show 0≤ k by linarith)
  have hes:=mul_nonneg (ActualCaps.ell_pos hk).le hs0
  have hm:=output_constants_nonneg.2.1
  have he:=output_constants_nonneg.2.2.1
  have hstock : drift (flat P) N+drift Q N+(Fintype.card (J×R):ℝ)+Fintype.card R+k=stock P Q N+k:=by
    dsimp only [stock,inventory]; ring
  rw [hstock]
  dsimp only [localConstant]
  nlinarith only [h,hes,hek,mul_nonneg hm hek,mul_nonneg he hes]
end KServer.ActualCharges

end


/-! The actual top-down allocation, summed over the fixed complete-prefix
hierarchy. All initialization costs depend only on the fixed label inventory. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HierarchicalQuota
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking ActualCharges
variable {Ω A Y:Type} [Fintype Ω] [Fintype A] {k:ℕ} {w:Ω→ℝ}

lemma sum_snoc {d:ℕ} (f:(Fin (d+1)→A)→ℝ):
    (∑ word,f word)=∑ word:Fin d→A,∑ a:A,f (Fin.snoc word a):=by
  calc _ = ∑ p:A×(Fin d→A),f (Fin.snoc p.2 p.1):=
          (Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (d+1)=>A)) _ _ (fun _=>rfl)).symm
       _ = _:=by rw [Fintype.sum_prod_type,sum_comm]

lemma total_sum {I:Type} [Fintype I] (w:Ω→ℝ) (N:ℕ) (f:I→ℕ→Ω→ℝ):
    total w N (fun t ω=>∑ i,f i t ω)=∑ i,total w N (f i):=by
  unfold total
  simp_rw [avg_sum]
  exact sum_comm

lemma drift_flat {R:Type} [Fintype R] (P:A→R→FilteredRanks w) (N:ℕ):
    drift (flat P) N=∑ a,drift (P a) N:=by
  unfold drift flat
  simp_rw [Fintype.sum_prod_type,avg_sum]
  rw [sum_comm]

variable (hw:∀ ω,0 ≤ w ω) (H:ℕ→Ω→ℕ)
variable (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
variable (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y)

lemma levelMove_nonneg (hk:1 ≤ (k:ℝ)) (d N:ℕ):0 ≤ levelMove hw H hr maps q hk d N:=by
  unfold levelMove nodeMove total
  exact sum_nonneg fun _ _=>sum_nonneg fun _ _=>sum_nonneg fun ω _=>mul_nonneg (hw ω) (abs_nonneg _)
lemma levelDrift_nonneg (d N:ℕ):0 ≤ levelDrift hw H hr maps q d N:=by
  unfold levelDrift drift
  exact sum_nonneg fun _ _=>sum_nonneg fun _ _=>sum_nonneg fun ω _=>mul_nonneg (hw ω) (sum_nonneg fun _ _=>abs_nonneg _)
lemma levelMove_zero (hk:1 ≤ (k:ℝ)) (N:ℕ):levelMove hw H hr maps q hk 0 N=0:=by
  simp [levelMove,nodeMove,quota,total,avg]
lemma levelDrift_zero (N:ℕ):levelDrift hw H hr maps q 0 N=0:=by
  unfold levelDrift drift
  apply sum_eq_zero
  intro word _
  apply sum_eq_zero
  intro t _
  unfold avg
  apply sum_eq_zero
  intro ω _
  have he:∀ a:Fin k,(parent hw H hr maps q word a).p (t+1) ω=0:=fun a=>
    HierarchicalRanks.family_root hw H hr maps q word a (t+1) ω
  have hb:∀ a:Fin k,(parent hw H hr maps q word a).before (t+1) ω=0:=by
    intro a
    change PosteriorRanks.posterior w (H (t+1)) (PosteriorRanks.rank
      (fun ρ=>HierarchyCounts.count (maps t ρ) word (q t ρ)) a.val) ω=0
    have hz:PosteriorRanks.rank (fun ρ=>HierarchyCounts.count (maps t ρ) word (q t ρ)) a.val=fun _=>0:=by
      funext ρ
      simp only [PosteriorRanks.rank,HierarchyCounts.count_zero]
      exact ite_eq_right (by omega)
    rw [hz]
    simp [PosteriorRanks.posterior,PosteriorRanks.numerator]
  simp only [he,hb,sub_self,abs_zero,sum_const_zero,mul_zero]

lemma level_movement (hk:1 ≤ (k:ℝ)) (hw1:∑ ω,w ω=1) (hwpos:∀ ω,0<w ω) (d N:ℕ):
    levelMove hw H hr maps q hk (d+1) N ≤ levelMove hw H hr maps q hk d N+
      localConstant*ActualCaps.ell k*(levelDrift hw H hr maps q d N+
        levelDrift hw H hr maps q (d+1) N+levelInventory A k d):=by
  have h word:=local_movement hk hw hw1 (children hw H hr maps q word) (parent hw H hr maps q word)
    (sizes hw H hr maps q word hwpos) (size_bound hw H hr maps q word) H
    (fun _ _ _ _=>rfl) (fun _ _ _=>rfl) hr (quota hw H hr maps q hk d word)
    (fun t ω=>parent_budget hw H hr maps q hk word hwpos t ω _
      (quota_bounds hw H hr maps q hk hwpos d word t ω).1) N
  have hs:=sum_le_sum (s:=univ) (fun word _=>h word)
  simp only [ChangingDomains.variation,total_sum,←quota_snoc,drift_flat] at hs
  change (∑ word:Fin d→A,∑ a:A,nodeMove hw H hr maps q hk (Fin.snoc word a) N) ≤ _ at hs
  rw [←sum_snoc (fun word=>nodeMove hw H hr maps q hk word N)] at hs
  simp only [sum_add_distrib,←mul_sum] at hs
  change levelMove hw H hr maps q hk (d+1) N ≤ levelMove hw H hr maps q hk d N+_ at hs
  have he:(∑ word:Fin d→A,∑ a:A,drift (children hw H hr maps q word a) N)=levelDrift hw H hr maps q (d+1) N:=by
    rw [levelDrift,sum_snoc (fun word=>drift (parent hw H hr maps q word) N)]
    rfl
  rw [he] at hs
  simp only [sum_const,nsmul_eq_mul,card_univ] at hs
  convert hs using 1; simp only [levelDrift,levelInventory]; ring
end KServer.HierarchicalQuota

end


/-! Geometric absorption with the literal parent coefficient one. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HierarchicalQuota

lemma weighted_shift (r m:ℕ→ℝ) (hr:∀ d,0 ≤ r d) (hm:∀ d,0 ≤ m d)
    (hroot:m 0=0) (hhalf:∀ d,r (d+1) ≤ r d/2) (L:ℕ):
    (∑ d∈range L,r d*m d) ≤ (1/2:ℝ)*∑ d∈range L,r d*m (d+1):=by
  cases L with
  | zero=>simp
  | succ L=>
    rw [sum_range_succ',hroot,mul_zero,add_zero]
    calc _ ≤ ∑ d∈range L,(1/2:ℝ)*(r d*m (d+1)):=by
            apply sum_le_sum
            intro d _
            have h:=mul_le_mul_of_nonneg_right (hhalf d) (hm (d+1))
            linarith
         _ = (1/2:ℝ)*∑ d∈range L,r d*m (d+1):=by rw [mul_sum]
         _ ≤ (1/2:ℝ)*∑ d∈range (L+1),r d*m (d+1):=by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            rw [sum_range_succ]
            exact le_add_of_nonneg_right (mul_nonneg (hr L) (hm (L+1)))

variable {Ω A Y:Type} [Fintype Ω] [Fintype A] {k:ℕ} {w:Ω→ℝ}
variable (hw:∀ ω,0 ≤ w ω) (H:ℕ→Ω→ℕ)
variable (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
variable (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y)

open ActualCharges

theorem allocation_absorption (hk:1 ≤ (k:ℝ)) (hw1:∑ ω,w ω=1) (hwpos:∀ ω,0<w ω)
    (r:ℕ→ℝ) (hrad:∀ d,0 ≤ r d) (hhalf:∀ d,r (d+1) ≤ r d/2) (L N:ℕ):
    treeMove hw H hr maps q hk r L N ≤
      2*localConstant*ActualCaps.ell k*(treeDrift hw H hr maps q r L N+treeInventory A k r L):=by
  have hp:=weighted_shift r (fun d=>levelMove hw H hr maps q hk d N) hrad
    (fun d=>levelMove_nonneg hw H hr maps q hk d N) (levelMove_zero hw H hr maps q hk N) hhalf L
  have he:(∑ d∈range L,r d*(localConstant*ActualCaps.ell k*
      (levelDrift hw H hr maps q d N+levelDrift hw H hr maps q (d+1) N+levelInventory A k d)))=
      localConstant*ActualCaps.ell k*(treeDrift hw H hr maps q r L N+treeInventory A k r L):=by
    unfold treeDrift treeInventory
    rw [←sum_add_distrib,mul_sum]
    apply sum_congr rfl
    intro d _
    ring
  have hs':treeMove hw H hr maps q hk r L N ≤
      (∑ d∈range L,r d*levelMove hw H hr maps q hk d N)+
      localConstant*ActualCaps.ell k*(treeDrift hw H hr maps q r L N+treeInventory A k r L):=by
    have hh:=sum_le_sum (s:=range L) (fun d _=>
      mul_le_mul_of_nonneg_left (level_movement hw H hr maps q hk hw1 hwpos d N) (hrad d))
    simp only [mul_add,sum_add_distrib] at hh
    rw [←he]
    simpa only [mul_add,sum_add_distrib,treeMove] using hh
  change _ ≤ (1/2:ℝ)*treeMove hw H hr maps q hk r L N at hp
  linarith
end KServer.HierarchicalQuota

end


/-! Conditional-drift coupling for literal fixed-prefix occupancies. The
right side is movement of the hidden labeled configurations, not observation
noise or a hypothesized allocation cost. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HierarchicalQuota
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking ActualCharges HierarchyCounts

lemma histogram_distance {I B:Type} [Fintype I] [Fintype B] [DecidableEq B] (f g:I→B):
    (∑ b:B,|(∑ i:I,if f i=b then (1:ℝ) else 0)-(∑ i:I,if g i=b then (1:ℝ) else 0)|) ≤
      2*∑ i:I,if f i=g i then (0:ℝ) else 1:=by
  calc _ ≤ ∑ b:B,∑ i:I,|((if f i=b then (1:ℝ) else 0)-(if g i=b then (1:ℝ) else 0))|:=by
            apply sum_le_sum
            intro b _
            rw [←sum_sub_distrib]
            exact abs_sum_le_sum_abs _ _
       _ = ∑ i:I,∑ b:B,|((if f i=b then (1:ℝ) else 0)-(if g i=b then (1:ℝ) else 0))|:=sum_comm
       _ = _:=by
            rw [mul_sum]
            apply sum_congr rfl
            intro i _
            by_cases h:f i=g i
            · simp [h]
            · have hp:∀ b:B,|((if f i=b then (1:ℝ) else 0)-(if g i=b then (1:ℝ) else 0))|=
                (if b=f i then 1 else 0)+(if b=g i then 1 else 0):=by
                intro b
                by_cases hf:b=f i <;> by_cases hg:b=g i
                · exact False.elim (h (hf.symm.trans hg))
                · simp [hf,Ne.symm h,h]
                · simp [hg,Ne.symm h,h]
                · simp [Ne.symm hf,Ne.symm hg,hf,hg]
              simp only [hp,sum_add_distrib]
              norm_num [h]

variable {Ω A Y:Type} [Fintype Ω] [Fintype A] {k:ℕ} {w:Ω→ℝ}
variable (hw:∀ ω,0 ≤ w ω) (H:ℕ→Ω→ℕ)
variable (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
variable (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y)

omit [Fintype Ω] [Fintype A] in
lemma count_histogram {d:ℕ} (word:Fin d→A) (t:ℕ) (ω:Ω):
    (count (maps t ω) word (q t ω):ℝ)=∑ l:Fin k,if address maps q d t ω l=word then (1:ℝ) else 0:=by
  simp only [count,card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  apply sum_congr rfl
  intro l _
  have he:hit (maps t ω) word (q t ω l)↔address maps q d t ω l=word:=by
    exact ⟨fun h=>funext h,fun h i=>congrFun h i⟩
  simp only [he]

lemma level_drift_count (d N:ℕ):levelDrift hw H hr maps q d N ≤ levelHidden (w:=w) maps q d N:=by
  unfold levelDrift drift levelHidden total
  rw [sum_comm]
  apply sum_le_sum
  intro t _
  rw [avg_sum]
  apply sum_le_sum
  intro word _
  rw [avg_sum]
  exact PosteriorRanks.rankProcess_drift hw H hr
    (fun t ω=>count (maps t ω) word (q t ω)) (fun t ω=>count_le _ _ _) t

include hw in
lemma level_count_cross (d N:ℕ):levelHidden (w:=w) maps q d N ≤ 2*total w N (prefixCross maps q d):=by
  unfold levelHidden
  rw [←total_mul]
  apply total_mono hw
  intro t ω
  simp only [count_histogram maps q]
  unfold prefixCross
  exact (histogram_distance (I:=Fin k) (B:=Fin d→A) (address maps q d (t+1) ω) (address maps q d t ω))

omit [Fintype Ω] [Fintype A] in
lemma prefixCross_nonneg (d t:ℕ) (ω:Ω):0 ≤ prefixCross maps q d t ω:=by
  unfold prefixCross
  exact sum_nonneg fun _ _=>by split_ifs <;> norm_num

end KServer.HierarchicalQuota

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_PrefixAllocation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/- Persistent heavy-slot size tracking filters tangents before adaptive refresh. -/


/-! Persistent heavy-slot size tracking on the actual finite observation
experiment. Raw counts can change with both the hidden trajectory and the
adapted partition. No martingale identity is postulated. -/


/-! Literal children and geometric edge weights of the retained complete
prefix tree. These identify the numbered rounding tree without deleting empty
words or changing its allocated coordinates. -/


/-! Quotas and parks on the actual numbered complete-prefix tree, with their
posterior support witnesses. Rounding.Tree and TreeRounding.Tree have the same
parent data; the conversion below changes no vertex or quantity. -/


/-! Actual truncation ancestors of complete-prefix words, with the retained
numbering used by the finite rounding tree. -/


/-! Cumulative parked mass in the actual prefix cut is bounded by posterior
mass of the 67-radius ball. Selection can depend on the completed state. -/


/-! Literal variation of all parks, including the root park, with the exact
parent-edge factor. No metric or rounding movement estimate is assumed. -/
noncomputable section
open scoped BigOperators
open Finset

namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable (A:Type) [Fintype A] (L:ℕ)

lemma sum_vertices (f:(d:ℕ)→(Fin d→A)→ℝ):
    (∑ v:Fin (Fintype.card (Vertex A L)),f (numbering A L v).1.val (numbering A L v).2)=
      ∑ d∈range (L+1),∑ word:Fin d→A,f d word:=by
  calc _ = ∑ u:Vertex A L,f u.1.val u.2:=
          Fintype.sum_equiv (numbering A L).toEquiv _ _ (fun _=>rfl)
       _ = (∑ d:Fin (L+1),∑ word:Fin d.val→A,f d.val word):=by rw [Fintype.sum_sigma]
       _ = _:=Fin.sum_univ_eq_sum_range (fun d=>∑ word:Fin d→A,f d word) (L+1)

end KServer.PrefixTree

end


/-! Fixed last-key bands in the complete prefix tree. -/


/-! Literal all-key persistent size references on the adapted complete map. -/


/-! All finer selected last-key bands form a literal prefix cut. -/


/-! The actual prefix parks satisfy the logarithmic coefficient estimate.
The denominator is the held persistent slot size; empty selected levels vanish. -/


/-! Literal allocation and persistent bands on the single positive experiment. -/


/-! From the exact conditional allocation construction to levelwise hidden-key
changes. This counts both true hidden movement and changing online maps. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HierarchicalQuota
attribute [local instance] Classical.propDecidable Classical.decEq
open ActualCharges
variable {Ω A Y:Type} [Fintype Ω] [Fintype A] {k:ℕ} {w:Ω→ℝ}
variable (hw:∀ ω,0 ≤ w ω) (H:ℕ→Ω→ℕ)
variable (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
variable (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y)

omit [Fintype Ω] [Fintype A] in
lemma prefixCross_zero (t:ℕ) (ω:Ω):prefixCross maps q 0 t ω=0:=by
  have he:∀ l:Fin k,address maps q 0 (t+1) ω l=address maps q 0 t ω l:=by
    intro l
    funext i
    exact i.elim0
  simp [prefixCross,he]

omit [Fintype Ω] [Fintype A] in
lemma prefixCross_step (d t:ℕ) (ω:Ω):prefixCross maps q (d+1) t ω ≤
    prefixCross maps q d t ω+keyCross maps q d t ω:=by
  unfold prefixCross keyCross
  rw [←sum_add_distrib]
  apply sum_le_sum
  intro l _
  by_cases ha:address maps q d (t+1) ω l=address maps q d t ω l
  · by_cases hb:maps (t+1) ω d (q (t+1) ω l)=maps t ω d (q t ω l)
    · have he:address maps q (d+1) (t+1) ω l=address maps q (d+1) t ω l:=by
        funext i
        exact Fin.lastCases (motive:=fun i:Fin (d+1)=>
          address maps q (d+1) (t+1) ω l i=address maps q (d+1) t ω l i)
          hb (fun j=>congrFun ha j) i
      simp [he,ha,hb]
    · simp only [ite_eq_left ha,ite_eq_right hb,zero_add]
      split_ifs <;> norm_num
  · simp only [ite_eq_right ha]
    split_ifs <;> norm_num

omit [Fintype A] in
include hw in
lemma prefix_transport_bound (r:ℕ→ℝ) (hrad:∀ d,0 ≤ r d)
    (hhalf:∀ d,r (d+1) ≤ r d/2) (L N:ℕ):
    prefixTransport (w:=w) maps q r L N ≤ 2*keyTransport (w:=w) maps q r L N:=by
  have hs:=sum_le_sum (s:=range L) (fun d _=>mul_le_mul_of_nonneg_left
    (total_mono hw (N:=N) (fun t ω=>prefixCross_step maps q d t ω)) (hrad d))
  simp only [total_add,mul_add,sum_add_distrib] at hs
  have hp:=weighted_shift r (fun d=>total w N (prefixCross maps q d)) hrad
    (fun d=>total_nonneg hw (fun t ω=>prefixCross_nonneg maps q d t ω))
    (by simp [total,prefixCross_zero,RankTracking.avg]) hhalf L
  change _ ≤ (1/2:ℝ)*prefixTransport maps q r L N at hp
  change prefixTransport maps q r L N ≤ _+keyTransport maps q r L N at hs
  linarith

include hw in
lemma tree_drift_bound (r:ℕ→ℝ) (hrad:∀ d,0 ≤ r d)
    (hhalf:∀ d,r (d+1) ≤ r d/2) (L N:ℕ):
    treeDrift hw H hr maps q r L N ≤ 6*keyTransport (w:=w) maps q r L N:=by
  have hc d:= (level_drift_count hw H hr maps q d N).trans (level_count_cross hw maps q d N)
  have hs:=sum_le_sum (s:=range L) (fun d _=>mul_le_mul_of_nonneg_left (hc (d+1)) (hrad d))
  have hp:=weighted_shift r (fun d=>levelDrift hw H hr maps q d N) hrad
    (fun d=>levelDrift_nonneg hw H hr maps q d N) (levelDrift_zero hw H hr maps q N) hhalf L
  have hx:=prefix_transport_bound hw maps q r hrad hhalf L N
  have hs':(∑ d∈range L,r d*levelDrift hw H hr maps q (d+1) N) ≤
      2*prefixTransport (w:=w) maps q r L N:=by
    simpa only [prefixTransport,mul_sum,mul_assoc,mul_comm,mul_left_comm] using hs
  unfold treeDrift
  simp only [mul_add,sum_add_distrib]
  -- The precise coefficient is six with these per-level estimates.
  linarith
end KServer.HierarchicalQuota

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualCharges
open RankTracking
variable {Ω I:Type} [Fintype Ω] [Fintype I] {w:Ω→ℝ}
lemma total_sum (N:ℕ) (f:I→ℕ→Ω→ℝ):
    total w N (fun t ω=>∑ i,f i t ω)=∑ i,total w N (f i):=by
  simp only [total,avg_sum]
  exact sum_comm
end KServer.ActualCharges

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_JointBudget
attribute [-instance] _root_.OAI.KServer.TreeRounding.inventoryFintype _root_.OAI.KServer.TreeRounding.inventoryNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometric absorption on the same numbered tree used for metric rounding. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointBudget
open JointExperiment JointAllocation HierarchicalQuota ActualCharges RankTracking
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0 < r d) (hk:1≤(k:ℝ))

lemma quota_tree {R τ:ℝ} (hτ:τ≠0) (N:ℕ):
    total (weight law hr) N (stepQuota s law hr hk R τ)=
      treeMove (weight_nonneg law hr) (history law hr) (history_refines law hr)
        (maps law hr s) (hidden law hr s) hk (fun d=>R/τ^d) L N:=by
  unfold stepQuota
  rw [ActualCharges.total_sum]
  simp only [total_mul]
  have he:∀ v:Node (Y:=Y) (k:=k) (L:=L),
      PrefixTree.weight (LevelKeys.Key Y k) L R τ ((PrefixTree.tree _ L).parent v)*
        total (weight law hr) N (fun t ω=>|quota s law hr hk (t+1) ω v-quota s law hr hk t ω v|)=
      (τ*(R/τ^(PrefixTree.numbering (LevelKeys.Key Y k) L v).1.val))*
        nodeMove (weight_nonneg law hr) (history law hr) (history_refines law hr)
          (maps law hr s) (hidden law hr s) hk (PrefixTree.numbering (LevelKeys.Key Y k) L v).2 N:=by
    intro v
    by_cases hv:v=0
    · subst v
      have hroot t ω:quota s law hr hk t ω 0=(k:ℝ):=PrefixTree.Q_root _ L _ _ _ _ _ hk t ω
      have hn:=congrArg (fun z:PrefixTree.Vertex (LevelKeys.Key Y k) L=>
        (τ*(R/τ^z.1.val))*nodeMove (weight_nonneg law hr) (history law hr)
          (history_refines law hr) (maps law hr s) (hidden law hr s) hk z.2 N)
        (PrefixTree.numbering_zero (LevelKeys.Key Y k) L)
      rw [hn]
      simp only [hroot,sub_self,abs_zero,nodeMove,PrefixTree.root,Fin.val_zero,HierarchicalQuota.quota,
        total,avg,mul_zero,sum_const_zero]
    · rw [PrefixTree.parent_weight _ L hτ v hv]
      rfl
  simp_rw [he]
  rw [PrefixTree.sum_vertices (LevelKeys.Key Y k) L (fun d word=>
    (τ*(R/τ^d))*nodeMove (weight_nonneg law hr) (history law hr) (history_refines law hr)
      (maps law hr s) (hidden law hr s) hk word N)]
  rw [sum_range_succ']
  have hz:(∑ word:Fin 0→LevelKeys.Key Y k,(τ*(R/τ^0))*
      nodeMove (weight_nonneg law hr) (history law hr) (history_refines law hr)
        (maps law hr s) (hidden law hr s) hk word N)=0:=by
    simp only [nodeMove,HierarchicalQuota.quota,sub_self,abs_zero,total,avg,mul_zero,sum_const_zero]
  rw [hz,add_zero]
  unfold treeMove levelMove
  apply sum_congr rfl
  intro d _
  rw [mul_sum]
  apply sum_congr rfl
  intro word _
  congr 1
  rw [pow_succ]
  field_simp

lemma geo_half {R τ:ℝ} (hR:0≤R) (hτ:2≤τ) (d:ℕ):
    R/τ^(d+1)≤(R/τ^d)/2:=by
  rw [pow_succ,div_mul_eq_div_div]
  exact div_le_div_of_nonneg_left (div_nonneg hR (pow_nonneg (by linarith) _)) (by norm_num) hτ

lemma key_tree {R τ:ℝ} (hτ:τ≠0) (hrad:∀ d,r d=R/τ^(d.val+1)) (N:ℕ):
    keyTransport (w:=weight law hr) (maps law hr s) (hidden law hr s) (fun d=>R/τ^d) L N=
      τ*total (weight law hr) N (stepKey s law hr):=by
  unfold keyTransport stepKey
  simp only [ActualCharges.total_sum,total_mul,mul_sum]
  rw [←Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro d _
  rw [hrad,←mul_assoc]
  congr 1
  rw [pow_succ]
  field_simp

lemma quota_bound_oai {R τ:ℝ} (hR:0≤R) (hτ:2≤τ) (hrad:∀ d,r d=R/τ^(d.val+1)) (N:ℕ):
    total (weight law hr) N (stepQuota s law hr hk R τ)≤
      (12*τ*localConstant)*ActualCaps.ell k*total (weight law hr) N (stepKey s law hr)+
      2*localConstant*ActualCaps.ell k*treeInventory (LevelKeys.Key Y k) k (fun d=>R/τ^d) L:=by
  have hn:τ≠0:=by linarith
  have hnp:∀ d,0≤R/τ^d:=fun d=>div_nonneg hR (pow_nonneg (by linarith) d)
  rw [quota_tree s law hr hk hn]
  have ha:=allocation_absorption (weight_nonneg law hr) (history law hr) (history_refines law hr)
    (maps law hr s) (hidden law hr s) hk (weight_sum law hr) (weight_pos law hr)
    (fun d=>R/τ^d) hnp (geo_half hR hτ) L N
  have hd:=tree_drift_bound (weight_nonneg law hr) (history law hr) (history_refines law hr)
    (maps law hr s) (hidden law hr s) (fun d=>R/τ^d) hnp (geo_half hR hτ) L N
  rw [key_tree s law hr hn hrad] at hd
  have hc:0≤2*localConstant*ActualCaps.ell k:=by
    have he:=ActualCaps.ell_ge_one hk
    have hl:0≤localConstant:=ActualCharges.output_constants_nonneg.2.2.2.le
    positivity
  exact ha.trans (by nlinarith [mul_le_mul_of_nonneg_left hd hc])

end KServer.JointBudget

end


/-! All-scale, law/horizon-independent roster endpoint, aggregating the actual
chronological edit charges rather than assuming metric distortion. -/


/-! The chronological triangle inequality for the literal priority stages. -/


/-! The all-step embedded motion of the selected hidden labeled optimum. -/


/-! The finite all-scale offline embedding endpoint. -/


/-! The finite all-scale embedding is used with the reversed geometric list
of radii in the top-down prefix construction, not with a moved quantifier. -/

end OAI
end

theorem solution : type_of% @OAI.KServer.JointBudget.quota_bound_oai := @OAI.KServer.JointBudget.quota_bound_oai
