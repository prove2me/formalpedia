-- Prove2me | solution 1 for OAI.KServer.main_theorem
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T15:02:59.797545+00:00
-- url     : https://prove2.me/submissions/ad717368-78f3-4eab-8c5b-0ca73fdeffb1

import Mathlib
import Definitions.Def_KServer
import Definitions.Def_OAIQ17Ks000
import Theorems.Thm_OAI_KServer_JointBudget_quota_bound
import Theorems.Thm_OAI_KServer_JointEmbedding_key_bound

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

end KServer.PosteriorRanks


/-! ## The actual finite hidden experiment of §02

The input is drawn once. Its selected optimum is hidden, whereas a finite
independent partition tape and the true request prefix are observed. No
conditioning on rounding outcomes enters this experiment. -/
namespace KServer.PosteriorRanks
variable {Ω : Type*} [Fintype Ω]

lemma mass_pos_of_weight {w : Ω → ℝ} (hw : ∀ ω, 0≤w ω) (H : Ω → ℕ)
    (ω : Ω) (hω : 0<w ω) : 0 < mass w H (H ω) := by
  apply hω.trans_le
  exact single_le_sum (fun z _ => hw z) (by simp [fiber])

lemma posterior_sum {I : Type*} [Fintype I] (w : Ω → ℝ) (H : Ω → ℕ)
    (f : I → Ω → ℝ) (ω : Ω) :
    posterior w H (fun z => ∑ i,f i z) ω=∑ i,posterior w H (f i) ω := by
  simp only [posterior,numerator,mul_sum,sum_div]
  rw [sum_comm]

lemma posterior_mul (w : Ω → ℝ) (H : Ω → ℕ) (f : Ω → ℝ) (c : ℝ) (ω : Ω) :
    posterior w H (fun z => f z*c) ω=posterior w H f ω*c := by
  simp only [posterior,numerator,←mul_assoc,←sum_mul]
  ring

end KServer.PosteriorRanks

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

end KServer.RankTracking
namespace KServer.CoreFlags
open KServer.RankTracking
variable {Ω : Type} [Fintype Ω] {w : Ω → ℝ}

lemma flag_adapted (R : FilteredRanks w) (t : ℕ) {ω z : Ω}
    (he : R.history t ω = R.history t z) : flag R t ω=flag R t z := by
  unfold flag
  rw [held_adapted (absoluteTest tolerance) R t ω z he]

end KServer.CoreFlags
end


/- Rank functions for dominated allocation, as in §03, equation explicit-rank. -/


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


/-! The actual epoch/wholesale recurrence of §03. The old credit is discarded
on a parent refresh, never spent twice. Empty transitions are forced by the
same variation test. -/
noncomputable section
open scoped BigOperators
open Finset

namespace KServer.CoarseProcess
open RankTracking RankFunctions CoarseSchedule
variable {Ω J R : Type} [Fintype Ω] [Fintype J] [Fintype R] {w : Ω → ℝ}
attribute [local instance] Classical.propDecidable Classical.decEq

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

end KServer.CoarseProcess

end
end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.CoarseSide
open RankTracking CoarseSchedule EpochSchedule

lemma C_nonneg {δ : ℝ} (hδ : 0 < δ) : 0 ≤ C δ := by unfold C factor; positivity

end KServer.CoarseSide

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

lemma run_adapted (c : ℝ) (d : ℕ → Ω → Input J R) (H : ℕ → Ω → ℕ)
    (href : ∀ t ω z,H (t+1) ω=H (t+1) z → H t ω=H t z)
    (hd : ∀ t ω z,H t ω=H t z → d t ω=d t z) (t : ℕ) (ω z : Ω)
    (he : H t ω=H t z) : run c d t ω=run c d t z :=
  state_adapted _ _ _ _ _ H href hd
    (fun t ω z h=>congrArg Input.ranks (hd t ω z h))
    (fun t ω z h=>congrArg (fun d:Input J R=>d.data.D) (hd t ω z h)) t ω z he

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

lemma cap_adapted (P : R → FilteredRanks w) (ξ a κ : ℝ) (t : ℕ) {ω ρ : Ω}
    (h : ∀ r,(P r).history t ω=(P r).history t ρ) :
    cap P ξ a κ t ω=cap P ξ a κ t ρ := by
  apply sum_congr rfl
  intro r _
  unfold FineCaps.capTerm FineCaps.interpolated
  rw [flag_adapted (P r) t (h r),endpoint_adapted _ _ _ _ (h r),endpoint_adapted _ _ _ _ (h r)]

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

variable {Ω R : Type*} [Fintype Ω] [Fintype R]
open RankTracking

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
-- module Solutions.OAIQ17_KS.KServer_Rounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/- Prescribed correlated-total rounding and minimization over finite joint laws, without an independence requirement. -/


noncomputable section
open Finset
open scoped BigOperators

/-! Continuation of Section09: finite top-down tree coupling.  The sampled
ancestors are retained as part of the joint state; no conditional means given
those ancestors are assumed. -/
namespace KServer.TreeRounding
open KServer.Rounding

attribute [instance] Law.finite

lemma Law.avg_add {α : Type} (L : Law α) (f g : α → ℝ) :
    L.avg (fun x => f x+g x)=L.avg f+L.avg g := by
  simp [Law.avg, mul_add, sum_add_distrib]

variable {n : ℕ} [NeZero n]

lemma Law.avg_le_of_support {α : Type} (L : Law α) {f g : α → ℝ}
    (h : ∀ ω, f (L.point ω) ≤ g (L.point ω)) : L.avg f ≤ L.avg g :=
  sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (L.nonneg ω)

end KServer.TreeRounding

end

/- Finite-tree park conservation and geometric subcapacity. -/


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.Rounding

variable {n : ℕ} [NeZero n]

lemma Tree.indicator_nonneg (T : Tree n) (v w : Fin n) : 0 ≤ T.indicator v w := by
  unfold Tree.indicator
  split <;> norm_num

/-- Several descendant collections may be charged simultaneously to a fixed
cut. The hypotheses are explicit incidence data, not an assumed mass bound. -/
theorem Tree.cut_park_capacity (T : Tree n) (q : Fin n → ℝ)
    (hp : ∀ w, 0 ≤ T.park q w) (S F : Finset (Fin n))
    (hcover : ∀ w ∈ S, ∃ v ∈ F, T.under v w=true) :
    (∑ w ∈ S, T.park q w) ≤ ∑ v ∈ F, q v := by
  classical
  have hpoint : ∀ w ∈ S, T.park q w ≤ ∑ v ∈ F, T.indicator v w*T.park q w := by
    intro w hw
    obtain ⟨v,hv,hu⟩ := hcover w hw
    calc _ = T.indicator v w*T.park q w := by simp [Tree.indicator,hu]
         _ ≤ _ := single_le_sum (fun z _ => mul_nonneg (T.indicator_nonneg z w) (hp w)) hv
  calc _ ≤ ∑ w ∈ S, ∑ v ∈ F, T.indicator v w*T.park q w := sum_le_sum hpoint
       _ = ∑ v ∈ F, ∑ w ∈ S, T.indicator v w*T.park q w := sum_comm
       _ ≤ ∑ v ∈ F, ∑ w, T.indicator v w*T.park q w := by
        apply sum_le_sum
        intro v _
        exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun w _ _ =>
          mul_nonneg (T.indicator_nonneg v w) (hp w))
       _ = _ := by simp_rw [T.park_subtree_total]

section Geometry
variable {Y : Type*} [MetricSpace Y] [Fintype Y] [DecidableEq Y]

omit [DecidableEq Y] in
/-- A cell with a nearby validity witness lies in the source's 67r ball. -/
lemma witness_ball_inclusion {R : Finset Y} {y z : Y} {r : ℝ}
    (hz : z ∈ R) (hnear : dist y z ≤ 27*r)
    (hdiam : ∀ a ∈ R, ∀ b ∈ R, dist a b ≤ 40*r) :
    R ⊆ univ.filter (fun a => dist y a ≤ 67*r) := by
  intro a ha
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  have ht := dist_triangle y z a
  have hd := hdiam z hz a ha
  linarith

omit [NeZero n] [MetricSpace Y] [Fintype Y] in
lemma disjoint_counting_mass {μ : Y → ℝ} (hμ : ∀ y, 0 ≤ μ y)
    {R : Fin n → Finset Y} {F : Finset (Fin n)} {B : Finset Y}
    (hdisj : Set.PairwiseDisjoint (↑F) R) (hsub : ∀ v ∈ F, R v ⊆ B) :
    (∑ v ∈ F, countingMass μ (R v)) ≤ countingMass μ B := by
  unfold countingMass
  rw [←sum_biUnion hdisj]
  apply sum_le_sum_of_subset_of_nonneg
  · intro y hy
    obtain ⟨v,hv,hy⟩ := mem_biUnion.mp hy
    exact hsub v hv hy
  · intro y _ _
    exact hμ y

/-- Cumulative park capacity with the exact geometric radius 67. Grouping is by
actual tree ancestors; posterior regions are those fixed-prefix cells. The cut
F may contain unoccupied roots too, and can be the full depth-j cut. -/
theorem Tree.geometric_park_capacity (T : Tree n) (q : Fin n → ℝ)
    (hp : ∀ w, 0 ≤ T.park q w) (S F : Finset (Fin n))
    (hcover : ∀ w ∈ S, ∃ v ∈ F, T.under v w=true)
    (R : Fin n → Finset Y) (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y)
    {C r : ℝ} (hC : 0 ≤ C) (y : Y)
    (hq : ∀ v ∈ F, q v ≤ C*countingMass μ (R v))
    (hdisj : Set.PairwiseDisjoint (↑F) R)
    (hwitness : ∀ v ∈ F, ∃ z ∈ R v, dist y z ≤ 27*r)
    (hdiam : ∀ v ∈ F, ∀ a ∈ R v, ∀ b ∈ R v, dist a b ≤ 40*r) :
    (∑ w ∈ S, T.park q w) ≤
      C*countingMass μ (univ.filter (fun z => dist y z ≤ 67*r)) := by
  have hsub : ∀ v ∈ F, R v ⊆ univ.filter (fun z => dist y z ≤ 67*r) := by
    intro v hv
    obtain ⟨z,hz,hn⟩ := hwitness v hv
    exact witness_ball_inclusion hz hn (hdiam v hv)
  calc _ ≤ ∑ v ∈ F, q v := T.cut_park_capacity q hp S F hcover
       _ ≤ ∑ v ∈ F, C*countingMass μ (R v) := sum_le_sum hq
       _ = C*(∑ v ∈ F, countingMass μ (R v)) := (mul_sum _ _ _).symm
       _ ≤ _ := mul_le_mul_of_nonneg_left (disjoint_counting_mass hμ hdisj hsub) hC

end Geometry

end KServer.Rounding

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Hierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conditional ranks of literal complete-prefix cells, connected to the
allocation's filtered process and compatible lower envelopes. No local
allocation or competitiveness assertion is an input. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HierarchicalRanks
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking PosteriorRanks HierarchyCounts
variable {Ω A Y : Type} [Fintype Ω] [Fintype A] {k d : ℕ}
variable {w : Ω → ℝ} (hw : ∀ ω,0≤w ω)
variable (H : ℕ → Ω → ℕ)
variable (hr : ∀ t ω ρ,H (t+1) ω=H (t+1) ρ → H t ω=H t ρ)
variable (maps : ℕ → Ω → ℕ → Y → A) (q : ℕ → Ω → Fin k → Y)

omit [Fintype A] in
/-- The first reward rank is exactly zero if each possible hidden placement
has a member in the current observed cell. This is a fiber, not an independence
assertion and does not condition on any rounding outcomes. -/
lemma first_rank_zero {k : ℕ} (hk : 0<k) (q : ℕ → Ω → Fin k → Y)
    (word : Fin d → A) (t : ℕ) (ω : Ω)
    (hs : ∀ ρ,H t ρ=H t ω → ∃ l,hit (maps t ρ) word (q t ρ l)) :
    (family hw H hr maps q word ⟨0,hk⟩).p t ω=0 := by
  change posterior w (H t) (PosteriorRanks.rank _ 0) ω=0
  unfold posterior numerator
  have hn : (∑ ρ∈fiber (H t) (H t ω),w ρ*PosteriorRanks.rank
      (fun z=>count (maps t z) word (q t z)) 0 ρ)=0 := by
    apply sum_eq_zero
    intro ρ hρ
    obtain ⟨l,hl⟩:=hs ρ (mem_filter.mp hρ).2
    have hc : 0 < count (maps t ρ) word (q t ρ) := card_pos.mpr ⟨l,by simp [hl]⟩
    simp [PosteriorRanks.rank,not_le.mpr hc]
  rw [hn,zero_div]

omit [Fintype A] in
lemma served_lower {k : ℕ} (hk : 0<k) (q : ℕ → Ω → Fin k → Y)
    (word : Fin d → A) {z : ℝ} (hz : z∈Set.Icc 0 (1/100:ℝ)) (t : ℕ) (ω : Ω)
    (hs : ∀ ρ,H t ρ=H t ω → ∃ l,hit (maps t ρ) word (q t ρ l)) :
    1≤lower hw H hr maps q word z t ω := by
  have h:=single_le_sum (s:=univ)
    (fun a _=>RankFunctions.rank_nonneg hz ((family hw H hr maps q word a).p t ω))
    (mem_univ (⟨0,hk⟩:Fin k))
  rw [first_rank_zero hw H hr maps hk q word t ω hs,RankFunctions.rank_zero] at h
  exact h

end KServer.HierarchicalRanks

end


/-! Actual top-down fractional quotas on all complete-prefix labels. The
parent budget is obtained from conditional count superadditivity, not posited
as an allocation oracle. Fixed unused labels remain present. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HierarchicalQuota
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking ActualStar
variable {Ω A Y:Type} [Fintype Ω] [Fintype A] {k:ℕ} {w:Ω→ℝ}
variable (hw:∀ ω,0≤w ω) (H:ℕ→Ω→ℕ)
variable (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
variable (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y)

lemma served (hk:1≤(k:ℝ)) (hwpos:∀ ω,0<w ω) {d:ℕ} (word:Fin d→A) (t:ℕ) (ω:Ω)
    (hs:∀ ρ,H t ρ=H t ω→∃ l,HierarchyCounts.hit (maps t ρ) word (q t ρ l)):
    1≤quota hw H hr maps q hk d word t ω:=by
  have hkp:0<k:=by exact_mod_cast (show (0:ℝ)<k by linarith)
  exact (HierarchicalRanks.served_lower hw H hr maps hkp q word
    (ActualCaps.ranges hk _ t ω (size_bound hw H hr maps q word t ω)).1 t ω hs).trans
    (quota_bounds hw H hr maps q hk hwpos d word t ω).1
end KServer.HierarchicalQuota

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
lemma rule_adapted (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (H:ℕ→Ω→ℕ)
    (hP:∀ i r t ω,(P i r).history t ω=H t ω)
    (hQ:∀ r t ω,(Q r).history t ω=H t ω)
    (hr:∀ t ω z,H (t+1) ω=H (t+1) z→ H t ω=H t z)
    (t:ℕ) (ω z:Ω) (he:H t ω=H t z):rule P Q t ω=rule P Q t z:=by
  have hh:=RuleSchedule.run_adapted (fun ir:J×R=> P ir.1 ir.2) (ruleFlags P)
    (marked P Q) (reset P Q) (D P Q) H (fun ir=> hP ir.1 ir.2) hr
    (flags_adapted P H hP) (marked_adapted P Q H hP hQ hr)
    (reset_adapted P Q H hP hQ hr) (D_adapted P Q H hP hQ hr) t ω z he
  have hs : RuleSchedule.S (fun ir:J×R=> P ir.1 ir.2) (ruleFlags P)=S P:=by
    funext s u
    exact rule_S P s u
  simpa only [hs,rule] using hh
end KServer.ActualOutput

end


/-! Uniform affine slope and endpoint bounds for the literal marked-side
family; logarithmic cancellation removes dependence on the number of children. -/


/-! Literal synthetic-flag preparation and selective held-log parameter edits
for the marked-side minimizers of the constructed star. -/


/-! Every side edit is charged to the literal rank-flag and coarse-coordinate
schedule. No cardinality factor or charge to an unchanged dominant child. -/


/-! The non-wholesale cap variation of the literal output. All endpoint
trackers are charged over all times before selecting the ordinary steps. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualOutput
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar OutputDynamics
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

lemma cap_sum (k:ℝ) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (t:ℕ) (ω:Ω) (i:J):
    d k P Q t ω i=∑ r,FineCaps.capTerm (rho/ActualCaps.ell k) (ActualCaps.a k Q t ω)
      (capScale k P Q t ω i) (P i r) t ω:=by
  rw [←TrackedCaps.cap,TrackedCaps.cap_eq]
  simp only [d,n,flexcap,ActualCaps.flexCap,decide_eq_true_eq,capScale]

end KServer.ActualOutput

end


/-! Every coordinate of the actual feasible star output depends only on
observed history and on the supplied parent quota. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualOutput
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}
variable (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (H:ℕ→Ω→ℕ)
    (hP:∀ i r t ω,(P i r).history t ω=H t ω)
    (hQ:∀ r t ω,(Q r).history t ω=H t ω)
    (hr:∀ t ω z,H (t+1) ω=H (t+1) z→H t ω=H t z)
include hP hQ hr
lemma d_adapted (k:ℝ) (t:ℕ) (ω z:Ω) (he:H t ω=H t z):d k P Q t ω=d k P Q t z:=by
  have hk:=key_adapted Q H hQ hr t ω z he
  have ha:ActualCaps.a k Q t ω=ActualCaps.a k Q t z:=by
    change 100*(CoarseParameters.upperBeta k cutoff cb (ActualCaps.ell k) dp (key Q t ω)-3)=_
    rw [hk]; rfl
  have hm:=mark_adapted P Q H hP hQ hr t ω z he
  have hs i:capScale k P Q t ω i=capScale k P Q t z i:=by unfold capScale; rw [hm]
  funext i
  rw [cap_sum,cap_sum,ha,hs]
  exact TrackedCaps.cap_adapted (P i) _ _ _ t (fun r=>by rw [hP,hP,he])
lemma α_adapted (k:ℝ) (t:ℕ) (ω z:Ω) (he:H t ω=H t z):α k P Q t ω=α k P Q t z:=
  StarSimplex.proportion_adapted (δ:=ds) (by norm_num [ds]) (by norm_num [ds]) C (ActualCaps.ell k) ct
    P (key Q) H hP hr (key_adapted Q H hQ hr) t ω z he
lemma side_adapted {k:ℝ} (hk:1≤k) (t:ℕ) (ω z:Ω) (he:H t ω=H t z):side hk P Q t ω=side hk P Q t z:=
  StarSide.proportion_adapted positive.2.2.2.1 (ActualCaps.ell_pos hk) ds P (key Q) (b k Q)
    H hP hr (key_adapted Q H hQ hr) (b_adapted k Q H hQ hr) t ω z he
lemma out_adapted {k:ℝ} (hk:1≤k) (t:ℕ) (ω z:Ω) (he:H t ω=H t z) (q:ℝ):
    out hk P Q t ω q=out hk P Q t z q:=by
  have hd:=d_adapted P Q H hP hQ hr k t ω z he
  have ha:=α_adapted P Q H hP hQ hr k t ω z he
  have hside:=side_adapted P Q H hP hQ hr hk t ω z he
  have hD:=D_adapted P Q H hP hQ hr t ω z he
  have hm:=mark_adapted P Q H hP hQ hr t ω z he
  have hreg:=rule_adapted P Q H hP hQ hr t ω z he
  simp only [out,hm,hreg]
  cases hmz:mark P Q t z with
  | none=>simp only [outI,hd,ha]
  | some o=>
    cases hrz:rule P Q t z with
    | false=>simp only [Bool.false_eq_true,ite_false,outI,hd,ha]
    | true=>
      simp only [ite_true]
      funext i
      simp only [outII,sideOut,hd,hside,hD]
end KServer.ActualOutput

end


/-! The literal recursive allocation is adapted to the request filtration.
No adaptedness of the hidden offline configurations is asserted or required. -/
noncomputable section
namespace KServer.HierarchicalQuota
variable {Ω A Y:Type} [Fintype Ω] [Fintype A] {k:ℕ} {w:Ω→ℝ}
variable (hw:∀ ω,0≤w ω) (H:ℕ→Ω→ℕ)
variable (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
variable (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y)
lemma quota_adapted (hk:1≤(k:ℝ)) (d:ℕ) (word:Fin d→A) (t:ℕ) (ω ρ:Ω)
    (he:H t ω=H t ρ):quota hw H hr maps q hk d word t ω=quota hw H hr maps q hk d word t ρ:=by
  induction d with
  | zero=>rfl
  | succ d ih=>
    simp only [quota,ih]
    exact congrFun (ActualOutput.out_adapted (children hw H hr maps q (Fin.init word))
      (parent hw H hr maps q (Fin.init word)) H (fun _ _ _ _=>rfl) (fun _ _ _=>rfl)
      hr hk t ω ρ he _) _
end KServer.HierarchicalQuota

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace KServer

universe u

lemma pathProbability_nonneg {k : ℕ} {X : Type u} (A : Policy k X)
    (h : List (X × Fin k)) (σ : List X) (j : Fin σ.length → Fin k) :
    0  ≤  pathProbability A h σ j := by
  induction σ generalizing h with
  | nil => simp [pathProbability]
  | cons r rs ih => exact mul_nonneg ((A h r).property.1 _) (ih _ _)

/-- Decompose a complete label string into its first decision and its tail. -/
lemma sum_labelStrings {k n : ℕ} (f : (Fin (n + 1) → Fin k) → ℝ) :
    ∑ j, f j = ∑ i : Fin k, ∑ js : Fin n → Fin k, f (Fin.cons i js) := by
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Fin k))
    (fun p => f (Fin.cons p.1 p.2)) f (fun _ => rfl), Fintype.sum_prod_type]

lemma pathProbability_sum {k : ℕ} {X : Type u} (A : Policy k X)
    (h : List (X × Fin k)) (σ : List X) :
    ∑ j : Fin σ.length → Fin k, pathProbability A h σ j = 1 := by
  induction σ generalizing h with
  | nil => simp [pathProbability]
  | cons r rs ih =>
    change (∑ j : Fin (rs.length + 1) → Fin k, pathProbability A h (r :: rs) j) = 1
    rw [sum_labelStrings]
    simp only [pathProbability, Fin.cons_zero, Fin.cons_succ]
    simp_rw [← Finset.mul_sum, ih, mul_one]
    exact (A h r).property.2

lemma continuous_pathProbability {k : ℕ} {X : Type u}
    (h : List (X × Fin k)) (σ : List X) (j : Fin σ.length → Fin k) :
    Continuous fun A : Policy k X => pathProbability A h σ j := by
  induction σ generalizing h with
  | nil => exact continuous_const
  | cons r rs ih =>
    change Continuous fun A : Policy k X =>
      (A h r).val (j 0) * pathProbability A (h ++ [(r, j 0)]) rs (fun i => j i.succ)
    apply Continuous.mul _ (ih _ _)
    exact (continuous_apply (j 0)).comp
      (continuous_subtype_val.comp ((continuous_apply r).comp (continuous_apply h)))

/-- Equation (cost-polynomial): a fixed finite input has continuous expected
cost on the full, possibly infinite, product of decision simplexes. -/
lemma continuous_expectedCost {k : ℕ} {X : Type u} [MetricSpace X]
    (s : Configuration k X) (σ : List X) :
    Continuous fun A : Policy k X => expectedCost A s σ := by
  exact continuous_finsetSum _ fun j _ =>
    (continuous_pathProbability [] σ j).mul continuous_const

/-- The topological step of Lemma `compact-policy`.  The finite feasibility
premise is the *remaining quantitative obligation*, not asserted here. This
lemma does not use finite/bounded/discrete assumptions on the request space. -/
theorem compact_policy_of_finite_feasibility {k : ℕ} {X : Type u} [MetricSpace X]
    (s : Configuration k X) (bound : List X → ℝ)
    (hfinite : ∀ F : Finset (List X), ∃ A : Policy k X,
      ∀ σ ∈ F, expectedCost A s σ  ≤  bound σ) :
    ∃ A : Policy k X, ∀ σ : List X, expectedCost A s σ  ≤  bound σ := by
  let constraints (σ : List X) : Set (Policy k X) :=
    {A | expectedCost A s σ  ≤  bound σ}
  have hclosed (σ : List X) : IsClosed (constraints σ) :=
    isClosed_le (continuous_expectedCost s σ) continuous_const
  have hfip (F : Finset (List X)) : (⋂ σ ∈ F, constraints σ).Nonempty := by
    obtain ⟨A, hA⟩ := hfinite F
    exact ⟨A, by simpa only [Set.mem_iInter, constraints, Set.mem_ofPred_eq] using hA⟩
  obtain ⟨A, hA⟩ := CompactSpace.iInter_nonempty hclosed hfip
  exact ⟨A, by simpa only [Set.mem_iInter, constraints, Set.mem_ofPred_eq] using hA⟩

/-! Section02's matching and strongly lazy simulation, including repeated
positions and arbitrary metric spaces. -/

end KServer
end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Behavior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace KServer
universe u

section Matching
variable {k : ℕ} {X : Type u} [MetricSpace X]

lemma matching_le (A C : Configuration k X) (π : Equiv.Perm (Fin k)) :
    matching A C  ≤  matchSum A C π :=
  (exists_minimum_matching A C).choose_spec π

lemma matching_nonneg (A C : Configuration k X) : 0  ≤  matching A C := by
  unfold matching matchSum
  exact Finset.sum_nonneg fun _ _ => dist_nonneg

lemma matching_self (A : Configuration k X) : matching A A = 0 := by
  apply le_antisymm _ (matching_nonneg _ _)
  simpa [matchSum] using matching_le A A (Equiv.refl _)

lemma matching_triangle (A C D : Configuration k X) :
    matching A D  ≤  matching A C + matching C D := by
  let π := matchingPerm A C
  let τ := matchingPerm C D
  calc
    matching A D  ≤  matchSum A D (π.trans τ) := matching_le _ _ _
    _  ≤  ∑ i, (dist (A i) (C (π i)) + dist (C (π i)) (D (τ (π i)))) := by
      apply Finset.sum_le_sum
      intro i _
      exact dist_triangle _ _ _
    _ = matching A C + matching C D := by
      rw [Finset.sum_add_distrib, Equiv.sum_comp π (fun i => dist (C i) (D (τ i)))]
      rfl

lemma matching_symmetric (A C : Configuration k X) : matching A C = matching C A := by
  have h (A C : Configuration k X) : matching A C  ≤  matching C A := by
    let π := matchingPerm C A
    calc
      matching A C  ≤  matchSum A C π.symm := matching_le _ _ _
      _ = matching C A := by
        unfold matchSum matching
        rw [← Equiv.sum_comp π (fun i => dist (A i) (C (π.symm i)))]
        simp only [Equiv.symm_apply_apply, dist_comm]
        rfl
  exact le_antisymm (h _ _) (h _ _)

lemma matchSum_serve (A C : Configuration k X) (π : Equiv.Perm (Fin k))
    (i : Fin k) (r : X) (hr : C (π i) = r) :
    dist (A i) r + matchSum (serve A i r) C π = matchSum A C π := by
  classical
  unfold matchSum
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    ← Finset.sum_erase_add _ (fun j => dist (A j) (C (π j))) (Finset.mem_univ i)]
  have he : (∑ j ∈ Finset.univ.erase i, dist ((serve A i r) j) (C (π j))) =
      ∑ j ∈ Finset.univ.erase i, dist (A j) (C (π j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [serve, Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [he]
  simp [serve, hr, add_comm]

lemma lazyChoice_covered (A C : Configuration k X) (r : X) (hc : ∃ i, C i = r)
    (ha : ∃ i, A i = r) : A (lazyChoice A C r hc) = r := by
  simp only [lazyChoice, dite_eq_left ha]
  exact ha.choose_spec

lemma lazyChoice_cost (A C : Configuration k X) (r : X) (hc : ∃ i, C i = r) :
    dist (A (lazyChoice A C r hc)) r +
      matching (serve A (lazyChoice A C r hc) r) C  ≤  matching A C := by
  classical
  by_cases ha : ∃ i, A i = r
  · have he := lazyChoice_covered A C r hc ha
    have hserve : serve A (lazyChoice A C r hc) r = A := by
      ext j
      by_cases hj : j = lazyChoice A C r hc
      · subst j; simp [serve, he]
      · simp only [serve, Function.update_of_ne hj]
    simp [he, hserve]
  · let i := (matchingPerm A C).symm hc.choose
    have hi : C (matchingPerm A C i) = r := by
      simpa only [i, Equiv.apply_symm_apply] using hc.choose_spec
    simp only [lazyChoice, dite_eq_right ha]
    calc
      dist (A i) r + matching (serve A i r) C
           ≤  dist (A i) r + matchSum (serve A i r) C (matchingPerm A C) :=
        add_le_add_right (matching_le _ _ _) _
      _ = matching A C := matchSum_serve A C _ i r hi

end Matching


lemma continuationCost_nil {k : ℕ} {X : Type u} [MetricSpace X]
    (A : Policy k X) (s : Configuration k X) (h : List (X × Fin k)) :
    continuationCost A s h [] = 0 := by simp [continuationCost, serviceCost]

lemma continuationCost_cons {k : ℕ} {X : Type u} [MetricSpace X]
    (A : Policy k X) (s : Configuration k X) (h : List (X × Fin k))
    (r : X) (σ : List X) :
    continuationCost A s h (r :: σ) =
      ∑ i : Fin k, (A h r).val i *
        (dist (s i) r + continuationCost A (serve s i r) (h ++ [(r,i)]) σ) := by
  change (∑ j : Fin (σ.length + 1) → Fin k,
    pathProbability A h (r :: σ) j * serviceCost s (r :: σ) j) = _
  rw [sum_labelStrings]
  simp only [pathProbability, serviceCost, Fin.cons_zero, Fin.cons_succ]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
  change (∑ j : Fin σ.length → Fin k, pathProbability A (h ++ [(r,i)]) σ j) *
    dist (s i) r + continuationCost A (serve s i r) (h ++ [(r,i)]) σ = _
  rw [pathProbability_sum, one_mul]

section OfflineComparison
variable {k : ℕ} [NeZero k] {X : Type u} [MetricSpace X]

lemma optimalCost_nonneg (s : Configuration k X) (σ : List X) : 0  ≤  optimalCost s σ := by
  exact le_csInf (Set.range_nonempty _) (by rintro _ ⟨w,rfl⟩; exact serviceCost_nonneg _ _ _)

omit [NeZero k] in
lemma matching_serve_le (C : Configuration k X) (i : Fin k) (r : X) :
    matching C (serve C i r)  ≤  dist (C i) r := by
  classical
  calc
    matching C (serve C i r)  ≤  matchSum C (serve C i r) (Equiv.refl _) := matching_le _ _ _
    _ = dist (C i) r := by
      simp [matchSum, serve, Function.update_apply, apply_ite]

omit [NeZero k] in
/-- Source lazy simulation applied purely pathwise, without a causality premise;
this is the comparison needed for repeated initial tuples. -/
theorem offline_lazy_comparison (A C : Configuration k X) (σ : List X)
    (j : Fin σ.length → Fin k) :
    ∃ w : Fin σ.length → Fin k,
      serviceCost A σ w  ≤  matching A C + serviceCost C σ j := by
  induction σ generalizing A C with
  | nil =>
    refine ⟨fun i => Fin.elim0 i, ?_⟩
    simpa [serviceCost] using matching_nonneg A C
  | cons r σ ih =>
    let C' := serve C (j 0) r
    have hc : ∃ i, C' i = r := ⟨j 0, by simp [C',serve]⟩
    let i := lazyChoice A C' r hc
    obtain ⟨w,hw⟩ := ih (serve A i r) C' (fun t => j t.succ)
    refine ⟨Fin.cons i w, ?_⟩
    simp only [serviceCost, Fin.cons_zero, Fin.cons_succ]
    have hstep := lazyChoice_cost A C' r hc
    have htri := matching_triangle A C C'
    have hmove := matching_serve_le C (j 0) r
    change dist (A i) r + matching (serve A i r) C'  ≤  _ at hstep
    change matching C C'  ≤  _ at hmove
    change dist (A i) r + serviceCost (serve A i r) σ w  ≤ 
      matching A C + (dist (C (j 0)) r + serviceCost C' σ (fun t => j t.succ))
    linarith

/-- Exact source bound `OPT_t  ≤  OPT_s + M(s,t)`; no distinctness is used. -/
theorem optimalCost_change_start (s t : Configuration k X) (σ : List X) :
    optimalCost t σ  ≤  optimalCost s σ + matching s t := by
  obtain ⟨j,hj⟩ := optimalCost_attained s σ
  obtain ⟨w,hw⟩ := offline_lazy_comparison t s σ j
  have ho := optimalCost_le_service t σ w
  rw [hj, matching_symmetric t s] at hw
  linarith

end OfflineComparison

lemma historyProbability_append {k : ℕ} {X : Type u} (A : Policy k X)
    (pre h h' : List (X × Fin k)) :
    historyProbability A pre (h ++ h') =
      historyProbability A pre h * historyProbability A (pre ++ h) h' := by
  induction h generalizing pre with
  | nil => simp [historyProbability]
  | cons ri h ih =>
    simp only [List.cons_append, historyProbability, ih, List.append_assoc, List.nil_append, Prod.mk.eta]
    ring

lemma historyProbability_singleton {k : ℕ} {X : Type u} (A : Policy k X)
    (pre : List (X × Fin k)) (r : X) (i : Fin k) :
    historyProbability A pre [(r,i)] = (A pre r).val i := by
  simp [historyProbability]


/-! ## Explicit causal realization of finite hidden-state algorithms.
This discharges a policy-existence interface needed both by correlated rounding
and by the fictitious-prefix episode extraction. It is not a competitiveness
premise: the machine below is arbitrary and its behavioral policy is constructed. -/
namespace HiddenMachine
open Finset
variable {k : ℕ} {X : Type u} {S : Type*} [Fintype S]

variable (M : Data k X S)

lemma mass_nonneg (h : List (X × Fin k)) : 0  ≤  mass M h :=
  sum_nonneg fun s _ => weights_nonneg M h s

lemma evolve_append (w : S → ℝ) (pre h g : List (X × Fin k)) :
    evolve M w pre (h++g) = evolve M (evolve M w pre h) (pre++h) g := by
  induction h generalizing w pre with
  | nil => simp [evolve]
  | cons ri h ih =>
    rcases ri with ⟨r,i⟩
    simpa only [List.cons_append,evolve,List.append_assoc,List.singleton_append,List.nil_append] using
      ih (step M pre r i w) (pre++[(r,i)])

lemma weights_append (h : List (X × Fin k)) (r : X) (i : Fin k) :
    weights M (h++[(r,i)]) = step M h r i (weights M h) := by
  rw [weights,evolve_append]
  rfl

lemma mass_append (h : List (X × Fin k)) (r : X) (i : Fin k) :
    mass M (h++[(r,i)]) = outMass M h r i := by
  simp only [mass,weights_append,outMass]

lemma outMass_le_mass (h : List (X × Fin k)) (r : X) (i : Fin k) :
    outMass M h r i  ≤  mass M h := by
  rw [←outMass_sum M h r]
  exact single_le_sum (fun j _ => outMass_nonneg M h r j) (mem_univ i)

lemma mass_mul_policy (h : List (X × Fin k)) (r : X) (i : Fin k) :
    mass M h * (policy M h r).val i=outMass M h r i := by
  by_cases hp : 0 < mass M h
  · simp only [policy,hp,↓reduceDIte]
    exact mul_div_cancel₀ _ (ne_of_gt hp)
  · have hz : mass M h=0 := le_antisymm (le_of_not_gt hp) (mass_nonneg M h)
    have ho : outMass M h r i=0 := le_antisymm (by simpa [hz] using outMass_le_mass M h r i)
      (outMass_nonneg M h r i)
    simp only [hz,ho,zero_mul]

variable [MetricSpace X]

omit [MetricSpace X] in
/-- Weighted branch disintegration; a finite algebraic identity, including
zero-likelihood branches, rather than an assumed conditional kernel. -/
lemma branch_sum (h : List (X × Fin k)) (r : X) (w : S → ℝ)
    (f : Fin k → S → ℝ) :
    (∑ i : Fin k, ∑ s', step M h r i w s' * f i s') =
      ∑ s, w s * ∑ s', M.transition h r s s' * f (M.output h r s s') s' := by
  simp only [step,sum_mul,mul_sum]
  rw [sum_comm]
  conv_lhs => arg 2; ext s'; rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro s _
  apply sum_congr rfl
  intro s' _
  simp only [ite_mul,zero_mul,sum_ite_eq,mem_univ,ite_true]
  ring

/-- Forgetting a finite private state preserves *exactly* all finite expected
costs. No finite-horizon policy family is identified without constructing its
single behavioral continuation. -/
theorem realization_cost (start : Configuration k X) (h : List (X × Fin k))
    (σ : List X) :
    mass M h * continuationCost (policy M) (configurationAfter start h) h σ =
      ∑ s, weights M h s * machineCost M start h s σ := by
  induction σ generalizing h with
  | nil => simp [continuationCost_nil,machineCost]
  | cons r σ ih =>
    rw [continuationCost_cons,mul_sum]
    have hh (i : Fin k) :
        mass M h * ((policy M h r).val i *
          (dist (configurationAfter start h i) r +
            continuationCost (policy M) (serve (configurationAfter start h) i r)
              (h++[(r,i)]) σ)) =
        ∑ s', step M h r i (weights M h) s' *
          (dist (configurationAfter start h i) r +
            machineCost M start (h++[(r,i)]) s' σ) := by
      rw [←mul_assoc,mass_mul_policy,mul_add]
      have hf := ih (h++[(r,i)])
      rw [mass_append,weights_append,configurationAfter_append] at hf
      rw [hf]
      simp only [mul_add,sum_add_distrib,←sum_mul,outMass]
    simp_rw [hh]
    rw [branch_sum]
    rfl


omit [MetricSpace X] in
lemma policy_strong (start : Configuration k X)
    (hout : ∀ h r s s', (∃ i, configurationAfter start h i=r) →
      configurationAfter start h (M.output h r s s')=r)
    (hnull : ∀ h r, (∃ i, configurationAfter start h i=r) →
      configurationAfter start h (M.nullOutput h r)=r) : StronglyLazy start (policy M) := by
  intro h r hc j hj
  have hn : j ≠ M.nullOutput h r := by intro he; exact hj (he ▸ hnull h r hc)
  have ho : outMass M h r j=0 := by
    apply sum_eq_zero
    intro s' _
    apply sum_eq_zero
    intro s _
    have hne : M.output h r s s' ≠ j := by
      intro he; exact hj (he ▸ hout h r s s' hc)
    simp only [hne,ite_false]
  by_cases hp : 0 < mass M h
  · simp only [policy,hp,↓reduceDIte,ho,zero_div]
  · simp only [policy,hp,↓reduceDIte,pureDistribution,hn,ite_false]

variable [NeZero k]

omit [MetricSpace X] in
lemma lazyFallback_covered (start : Configuration k X) (h : List (X × Fin k)) (r : X)
    (hc : ∃ i, configurationAfter start h i=r) :
    configurationAfter start h (lazyFallback start h r)=r := by
  simp only [lazyFallback,hc,↓reduceDIte]
  exact Classical.choose_spec hc

variable (start : Configuration k X) (V : List X → S → Configuration k X)
variable (hcover : ∀ h r s, ∃ i, V (h++[r]) s i=r)

lemma lazyMachine_strong : StronglyLazy start (policy (lazyMachine M start V hcover)) := by
  apply policy_strong
  · intro h r s s' hc
    exact lazyChoice_covered _ _ _ _ hc
  · exact lazyFallback_covered start

lemma lazyMachine_bound (h : List (X × Fin k)) (s : S) (σ : List X) :
    machineCost (lazyMachine M start V hcover) start h s σ  ≤ 
      matching (configurationAfter start h) (V (h.map Prod.fst) s)+
        virtualCost M start V hcover h s σ := by
  induction σ generalizing h s with
  | nil => simpa only [machineCost,virtualCost,add_zero] using matching_nonneg _ _
  | cons r σ ih =>
    let L := lazyMachine M start V hcover
    have hh (s' : S) := ih (h++[(r,L.output h r s s')]) s'
    have hone (s' : S) :
        dist (configurationAfter start h (L.output h r s s')) r +
          machineCost L start (h++[(r,L.output h r s s')]) s' σ  ≤ 
        matching (configurationAfter start h) (V (h.map Prod.fst) s)+
          (matching (V (h.map Prod.fst) s) (V (h.map Prod.fst++[r]) s')+
            virtualCost M start V hcover (h++[(r,L.output h r s s')]) s' σ) := by
      have hi := hh s'
      simp only [configurationAfter_append,List.map_append,List.map_singleton] at hi
      have hc := lazyChoice_cost (configurationAfter start h) (V (h.map Prod.fst++[r]) s') r
        (hcover _ r s')
      have ht := matching_triangle (configurationAfter start h) (V (h.map Prod.fst) s)
        (V (h.map Prod.fst++[r]) s')
      change dist (configurationAfter start h (L.output h r s s')) r +
        matching (serve (configurationAfter start h) (L.output h r s s') r)
          (V (h.map Prod.fst++[r]) s')  ≤  _ at hc
      linarith
    calc
      _  ≤  ∑ s', M.transition h r s s' *
          (matching (configurationAfter start h) (V (h.map Prod.fst) s)+
          (matching (V (h.map Prod.fst) s) (V (h.map Prod.fst++[r]) s')+
            virtualCost M start V hcover (h++[(r,L.output h r s s')]) s' σ)) := by
        exact sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left (hone s')
          (M.transition_nonneg _ _ _ _)
      _ = _ := by
        simp only [virtualCost,mul_add,sum_add_distrib,←sum_mul,M.transition_sum,one_mul]
        rfl

/-- Fully constructed randomized causal strong-lazy simulation with arbitrary
finite correlated private states and an arbitrary initial virtual mismatch.
It is uniform over all fixed finite request sequences, including all horizons. -/
theorem causal_random_lazy_simulation :
    ∃ A : Policy k X, StronglyLazy start A ∧ ∀ σ : List X,
      expectedCost A start σ  ≤ 
        (∑ s, M.initial s*matching start (V [] s))+
          ∑ s, M.initial s*virtualCost M start V hcover [] s σ := by
  let L := lazyMachine M start V hcover
  refine ⟨policy L,lazyMachine_strong M start V hcover,?_⟩
  intro σ
  have he := realization_cost L start [] σ
  have hb : (∑ s, M.initial s*machineCost L start [] s σ)  ≤ 
      (∑ s, M.initial s*matching start (V [] s))+
        ∑ s, M.initial s*virtualCost M start V hcover [] s σ := by
    rw [←sum_add_distrib]
    apply sum_le_sum
    intro s _
    have h := mul_le_mul_of_nonneg_left (lazyMachine_bound M start V hcover [] s σ)
      (M.initial_nonneg s)
    simpa only [configurationAfter,List.foldl_nil,List.map_nil,mul_add] using h
  have hinit : mass L []=1 := L.initial_sum
  rw [hinit,one_mul] at he
  exact he.trans_le hb

end HiddenMachine
end KServer

namespace KServer
namespace BoundedSimulation
noncomputable section
open Finset
universe u
variable {k : ℕ} [NeZero k] {X : Type u}

lemma labelAt_update {H : ℕ} (s : Memory H k) (n : ℕ) (i : Fin k) (hn : n<H) :
    labelAt (update s n i) n=i := by
  classical
  simp [labelAt,update,hn]

lemma history_update {H : ℕ} (h : List X) (s : Memory H k) (i : Fin k) :
    history h (update s h.length i)=history h s := by
  classical
  apply List.ext_getElem (by simp [history])
  intro n hn hn'
  simp only [history,List.getElem_mapIdx]
  have hn0 : n<h.length := by simpa [history] using hn
  by_cases hH : h.length<H
  · have hnH := hn0.trans hH
    have hne : (⟨n,hnH⟩ : Fin H) ≠ ⟨h.length,hH⟩ := by
      intro he; have heq : n=h.length := congrArg Fin.val he; omega
    simp [labelAt,update,hH,hnH,Function.update_of_ne hne]
  · simp [update,hH]

lemma history_step {H : ℕ} (h : List X) (r : X) (s : Memory H k)
    (i : Fin k) (hh : h.length<H) :
    history (h++[r]) (update s h.length i)=history h s++[(r,i)] := by
  rw [history_append,history_update,labelAt_update s _ i hh]

variable (H : ℕ) (A : Policy k X) (pre : List (X × Fin k))

lemma transition_integrate (h : List (X × Fin k)) (r : X) (s : Memory H k)
    (f : Memory H k → ℝ) :
    ∑ s', transition H A pre h r s s'*f s'=
      ∑ i : Fin k, (A (pre++history (h.map Prod.fst) s) r).val i * f (update s h.length i) := by
  classical
  simp only [transition,Finset.sum_mul,ite_mul,zero_mul]
  rw [Finset.sum_comm]
  simp

variable (start virtualStart : Configuration k X)

lemma virtual_step (h : List X) (r : X) (s : Memory H k)
    (i : Fin k) (hh : h.length<H) :
    virtual H virtualStart (h++[r]) (update s h.length i)=
      serve (virtual H virtualStart h s) i r := by
  simp only [virtual,history_step h r s i hh,configurationAfter_append]

variable [MetricSpace X]

/-- Exact virtual continuation bound, honoring the entire private label history.
In particular the virtual policy is not falsely conditioned only on the real
server positions or on the current request. -/
lemma virtual_cost_bound (h : List (X × Fin k)) (s : Memory H k) (σ : List X)
    (hb : h.length+σ.length ≤ H) :
    HiddenMachine.virtualCost (machine H A pre) start (virtual H virtualStart)
      (virtual_covers H virtualStart) h s σ  ≤ 
    continuationCost A (virtual H virtualStart (h.map Prod.fst) s)
      (pre++history (h.map Prod.fst) s) σ := by
  induction σ generalizing h s with
  | nil => simp [HiddenMachine.virtualCost,continuationCost_nil]
  | cons r σ ih =>
    have hh : h.length<H := by simpa using (show h.length< H by simp only [List.length_cons] at hb; omega)
    rw [HiddenMachine.virtualCost]
    change (∑ s', transition H A pre h r s s' * _)  ≤  _
    rw [transition_integrate,continuationCost_cons]
    apply sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ ((A (pre++history (h.map Prod.fst) s) r).property.1 i)
    let L := HiddenMachine.lazyMachine (machine H A pre) start (virtual H virtualStart)
      (virtual_covers H virtualStart)
    let s' := update s h.length i
    let j := L.output h r s s'
    have hv : virtual H virtualStart (h.map Prod.fst++[r]) s'=
        serve (virtual H virtualStart (h.map Prod.fst) s) i r := by
      simpa [s'] using virtual_step H virtualStart (h.map Prod.fst) r s i (by simpa using hh)
    have hvh : history (h.map Prod.fst++[r]) s'=history (h.map Prod.fst) s++[(r,i)] := by
      simpa [s'] using history_step (h.map Prod.fst) r s i (by simpa using hh)
    have hi := ih (h++[(r,j)]) s' (by
      simp only [List.length_append,List.length_cons,List.length_nil] at *
      omega)
    simp only [List.map_append,List.map_singleton] at hi
    rw [hv,hvh,←List.append_assoc] at hi
    have hm := matching_serve_le (virtual H virtualStart (h.map Prod.fst) s) i r
    change matching (virtual H virtualStart (h.map Prod.fst) s)
      (virtual H virtualStart (h.map Prod.fst++[r]) s') +
      HiddenMachine.virtualCost (machine H A pre) start (virtual H virtualStart)
        (virtual_covers H virtualStart) (h++[(r,j)]) s' σ  ≤  _
    rw [hv]
    exact add_le_add hm hi

/-- Realizes a supplied behavioral policy from a different actual start, up to
any prescribed finite horizon; its construction is causal on all histories.
The bound is uniform in the horizon, permitting the global compactness step. -/
theorem finite_horizon_simulation :
    ∃ B : Policy k X, StronglyLazy start B ∧ ∀ σ : List X, σ.length ≤ H →
      expectedCost B start σ  ≤  matching start virtualStart+
        continuationCost A virtualStart pre σ := by
  obtain ⟨B,hB,hcost⟩ := HiddenMachine.causal_random_lazy_simulation
    (machine H A pre) start (virtual H virtualStart) (virtual_covers H virtualStart)
  refine ⟨B,hB,?_⟩
  intro σ hσ
  have hc := hcost σ
  have hz (s : Memory H k) : virtual H virtualStart [] s=virtualStart := rfl
  have hinit (s : Memory H k) : (machine H A pre).initial s=(if s=(fun _=>0) then 1 else 0) := rfl
  simp only [hinit,ite_mul,one_mul,zero_mul,sum_ite_eq',mem_univ,↓reduceIte,hz] at hc
  refine hc.trans (add_le_add le_rfl ?_)
  simpa only [List.length_nil,zero_add,List.map_nil,history,List.mapIdx_nil,List.append_nil,
    virtual,configurationAfter,List.foldl_nil] using
      virtual_cost_bound H A pre start virtualStart [] (fun _=>0) σ (by simpa using hσ)

/-- One global causal simulator on an arbitrary metric. The finite-memory
constructions above incur the same initial matching, so compactness selects a
single policy valid for every finite horizon. No finiteness of X is required. -/
theorem global_simulation :
    ∃ B : Policy k X, ∀ σ : List X,
      expectedCost B start σ  ≤  matching start virtualStart+
        continuationCost A virtualStart pre σ := by
  apply compact_policy_of_finite_feasibility
  intro F
  let H := F.sup List.length
  obtain ⟨B,_,hB⟩ := finite_horizon_simulation H A pre start virtualStart
  exact ⟨B,fun σ hσ => hB σ (Finset.le_sup hσ)⟩

end
end BoundedSimulation
end KServer

namespace KServer
universe u
section Mixture
variable {k : ℕ} {X : Type u} {Ω : Type*} [Fintype Ω]
variable (w : Ω → ℝ) (hw : ∀ ω, 0  ≤  w ω) (hs : ∑ ω, w ω = 1)
variable (A : Ω → Policy k X)

include hw in
lemma mixtureLikelihood_nonneg (h : List (X × Fin k)) :
    0  ≤  mixtureLikelihood w A h :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (hw ω) (historyProbability_nonneg _ _ _)

include hw in
lemma weightedLikelihood_le (h : List (X × Fin k)) (ω : Ω) :
    w ω * historyProbability (A ω) [] h  ≤  mixtureLikelihood w A h := by
  exact Finset.single_le_sum (fun i _ =>
    mul_nonneg (hw i) (historyProbability_nonneg _ _ _)) (Finset.mem_univ ω)

lemma mixtureLikelihood_append (h : List (X × Fin k)) (r : X) (i : Fin k) :
    mixtureLikelihood w A (h ++ [(r,i)]) =
      ∑ ω, w ω * historyProbability (A ω) [] h * (A ω h r).val i := by
  simp only [mixtureLikelihood, historyProbability_append, List.nil_append,
    historyProbability_singleton]
  congr 1
  funext ω
  ring

variable [NeZero k]

lemma mixturePolicy_recurrence (h : List (X × Fin k)) (r : X) (i : Fin k) :
    mixtureLikelihood w A h * (mixturePolicy w hw A h r).val i =
      mixtureLikelihood w A (h ++ [(r,i)]) := by
  rw [mixtureLikelihood_append]
  by_cases hp : 0 < mixtureLikelihood w A h
  · simp only [mixturePolicy, hp, ↓reduceDIte]
    field_simp
  · have hz : mixtureLikelihood w A h = 0 :=
      le_antisymm (le_of_not_gt hp) (mixtureLikelihood_nonneg w hw A h)
    rw [hz, zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro ω _
    have hω : w ω * historyProbability (A ω) [] h = 0 :=
      le_antisymm (by simpa only [hz] using weightedLikelihood_le w hw A h ω)
        (mul_nonneg (hw ω) (historyProbability_nonneg _ _ _))
    rw [hω, zero_mul]

include hs in
lemma historyProbability_mixture (h : List (X × Fin k)) :
    historyProbability (mixturePolicy w hw A) [] h = mixtureLikelihood w A h := by
  induction h using List.reverseRecOn with
  | nil => simpa [historyProbability, mixtureLikelihood] using hs.symm
  | append_singleton h ri ih =>
    rw [historyProbability_append, List.nil_append, historyProbability_singleton, ih]
    exact mixturePolicy_recurrence w hw A h ri.1 ri.2

lemma historyProbability_ofFn {k : ℕ} {X : Type u} (A : Policy k X)
    (pre : List (X × Fin k)) (σ : List X) (j : Fin σ.length → Fin k) :
    historyProbability A pre (List.ofFn fun i => (σ.get i, j i)) =
      pathProbability A pre σ j := by
  induction σ generalizing pre with
  | nil => simp [historyProbability, pathProbability]
  | cons r rs ih =>
    rw [List.ofFn_succ]
    simp only [List.get_eq_getElem, historyProbability, pathProbability]
    exact congrArg ((A pre r).val (j 0) * ·) (ih _ _)

/- Every complete path has exactly the prescribed finite mixture law. -/
include hs in
theorem pathProbability_mixture (σ : List X) (j : Fin σ.length → Fin k) :
    pathProbability (mixturePolicy w hw A) [] σ j =
      ∑ ω, w ω * pathProbability (A ω) [] σ j := by
  rw [← historyProbability_ofFn, historyProbability_mixture w hw hs A]
  simp only [mixtureLikelihood, historyProbability_ofFn]

/- Consequently the full finite cost vector, not just a single input cost,
is the same convex combination under this one horizon-independent policy. -/
include hs in
theorem expectedCost_mixture [MetricSpace X] (s : Configuration k X) (σ : List X) :
    expectedCost (mixturePolicy w hw A) s σ = ∑ ω, w ω * expectedCost (A ω) s σ := by
  simp only [expectedCost, pathProbability_mixture w hw hs A, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end Mixture

section Binary
variable {k : ℕ} [NeZero k] {X : Type u} [MetricSpace X]

/-- One private coin implements a convex combination simultaneously for all inputs. -/
lemma exists_binary_mixture (s : Configuration k X) (A B : Policy k X)
    (a b : ℝ) (ha : 0  ≤  a) (hb : 0  ≤  b) (hab : a + b = 1) :
    ∃ D : Policy k X, ∀ σ, expectedCost D s σ =
      a * expectedCost A s σ + b * expectedCost B s σ := by
  let w : Bool → ℝ := fun i => if i then a else b
  let P : Bool → Policy k X := fun i => if i then A else B
  have hw : ∀ i, 0  ≤  w i := by intro i; cases i <;> simp [w, ha, hb]
  have hs : ∑ i, w i = 1 := by simpa [w, add_comm] using hab
  refine ⟨mixturePolicy w hw P, fun σ => ?_⟩
  simpa [w, P, add_comm] using expectedCost_mixture w hw hs P s σ

end Binary

/-- The finite convex-separation implication used in source Lemma finite-set.
Its premise is an explicit distributional estimate, not an assumed online policy
existence theorem. The lemma itself is an unconditional convex-geometric fact. -/
theorem nonpositive_vector_of_distributional {ι : Type*} [Fintype ι]
    (S : Set (ι → ℝ)) (hne : S.Nonempty) (hcmp : IsCompact S) (hconv : Convex ℝ S)
    (hdist : ∀ w : ι → ℝ, (∀ i, 0  ≤  w i) → (∑ i, w i = 1) →
      ∃ v ∈ S, ∑ i, w i * v i  ≤  0) :
    ∃ v ∈ S, ∀ i, v i  ≤  0 := by
  classical
  by_contra hnot
  let N : Set (ι → ℝ) := {x | ∀ i, x i  ≤  0}
  have hnconv : Convex ℝ N := by
    intro x hx y hy a b ha hb hab i
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha (hx i))
      (mul_nonpos_of_nonneg_of_nonpos hb (hy i))
  have hnclosed : IsClosed N := by
    have he : N = ⋂ i, {x : ι → ℝ | x i  ≤  0} := by ext; simp [N]
    rw [he]
    exact isClosed_iInter fun i => isClosed_le (continuous_apply i) continuous_const
  have hdisj : Disjoint N S := by
    rw [Set.disjoint_left]
    intro x hx hxs
    exact hnot ⟨x,hxs,hx⟩
  obtain ⟨f,u,v,hN,huv,hS⟩ :=
    geometric_hahn_banach_closed_compact hnconv hnclosed hconv hcmp hdisj
  have hupos : 0 < u := by simpa using hN 0 (by intro i; exact le_rfl)
  let c : ι → ℝ := fun i => f (Pi.single i 1)
  have hrepr (x : ι → ℝ) : f x = ∑ i, c i * x i := by
    have he : x = ∑ i, x i • (Pi.single i 1 : ι → ℝ) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [he]
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  have hc : ∀ i, 0  ≤  c i := by
    intro i
    by_contra hci
    have hcneg : c i < 0 := lt_of_not_ge hci
    let t := (u + 1) / c i
    have ht : t < 0 := div_neg_of_pos_of_neg (by linarith) hcneg
    have hmem : t • (Pi.single i 1 : ι → ℝ) ∈ N := by
      intro j
      by_cases hj : j = i
      · subst j; simpa using ht.le
      · simp [hj]
    have hh := hN (t • (Pi.single i 1 : ι → ℝ)) hmem
    have hval : f (t • (Pi.single i 1 : ι → ℝ)) = u + 1 := by
      rw [map_smul]
      change t * c i = u + 1
      exact div_mul_cancel₀ _ hcneg.ne
    rw [hval] at hh
    linarith
  have htot : 0 < ∑ i, c i := by
    by_contra hpos
    have hz : ∑ i, c i = 0 := le_antisymm (le_of_not_gt hpos)
      (Finset.sum_nonneg fun i _ => hc i)
    have hc0 : ∀ i, c i = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hc i)).mp hz i (Finset.mem_univ i)
    obtain ⟨x,hx⟩ := hne
    have hh := hS x hx
    rw [hrepr] at hh
    simp only [hc0, zero_mul, Finset.sum_const_zero] at hh
    linarith
  let w : ι → ℝ := fun i => c i / ∑ i, c i
  have hw : ∀ i, 0  ≤  w i := fun i => div_nonneg (hc i) htot.le
  have hws : ∑ i, w i = 1 := by
    dsimp only [w]
    rw [← Finset.sum_div, div_self htot.ne']
  obtain ⟨x,hx,hwx⟩ := hdist w hw hws
  have hfx : f x  ≤  0 := by
    rw [hrepr]
    have he : (∑ i, w i * x i) = (∑ i, c i * x i) / (∑ i, c i) := by
      simp only [w, div_mul_eq_mul_div, Finset.sum_div]
    rw [he] at hwx
    simpa only [zero_mul] using (div_le_iff₀ htot).mp hwx
  have hh := hS x hx
  linarith

section FiniteFeasibility
variable {k : ℕ} [NeZero k] {X : Type u} [MetricSpace X]

/-- Source finite-set separation, directly on the compact behavioral policy
space. Finite random-seed conversion proved above supplies its convexity. -/
theorem finite_policy_of_distributional {ι : Type*} [Fintype ι]
    (s : Configuration k X) (σ : ι → List X) (bound : ι → ℝ)
    (hdist : ∀ w : ι → ℝ, (∀ i, 0  ≤  w i) → (∑ i, w i = 1) →
      ∃ A : Policy k X, ∑ i, w i * expectedCost A s (σ i)  ≤  ∑ i, w i * bound i) :
    ∃ A : Policy k X, ∀ i, expectedCost A s (σ i)  ≤  bound i := by
  classical
  let cost : Policy k X → (ι → ℝ) := fun A i => expectedCost A s (σ i) - bound i
  have hcont : Continuous cost := continuous_pi fun i =>
    (continuous_expectedCost s (σ i)).sub continuous_const
  have hne : (Set.range cost).Nonempty := Set.range_nonempty cost
  have hconv : Convex ℝ (Set.range cost) := by
    rintro _ ⟨A,rfl⟩ _ ⟨B,rfl⟩ a b ha hb hab
    obtain ⟨D,hD⟩ := exists_binary_mixture s A B a b ha hb hab
    refine ⟨D, funext fun i => ?_⟩
    change expectedCost D s (σ i) - bound i =
      a * (expectedCost A s (σ i) - bound i) + b * (expectedCost B s (σ i) - bound i)
    rw [hD]
    linear_combination (bound i) * hab
  have hg : ∀ w : ι → ℝ, (∀ i, 0  ≤  w i) → (∑ i, w i = 1) →
      ∃ v ∈ Set.range cost, ∑ i, w i * v i  ≤  0 := by
    intro w hw hs
    obtain ⟨A,hA⟩ := hdist w hw hs
    refine ⟨cost A, ⟨A,rfl⟩, ?_⟩
    simpa only [cost, mul_sub, Finset.sum_sub_distrib, sub_nonpos] using hA
  obtain ⟨_, ⟨A,rfl⟩,hA⟩ := nonpositive_vector_of_distributional
    (Set.range cost) hne (isCompact_range hcont) hconv hg
  exact ⟨A, fun i => sub_nonpos.mp (hA i)⟩

end FiniteFeasibility

/-- Quantifier-exact combination of finite separation and product compactness.
No law-dependent or horizon-dependent policy is silently asserted: the entire
quantitative distributional premise is displayed, and remains to be obtained
from the new finite-law construction and amplification. -/
theorem global_policy_of_finite_laws {k : ℕ} [NeZero k] {X : Type u} [MetricSpace X]
    (s : Configuration k X) (bound : List X → ℝ)
    (hdist : ∀ F : Finset (List X), ∀ w : F → ℝ,
      (∀ i, 0  ≤  w i) → (∑ i, w i = 1) →
      ∃ A : Policy k X, ∑ i : F, w i * expectedCost A s i.val  ≤ 
        ∑ i : F, w i * bound i.val) :
    ∃ A : Policy k X, ∀ σ, expectedCost A s σ  ≤  bound σ := by
  apply compact_policy_of_finite_feasibility
  intro F
  obtain ⟨A,hA⟩ := finite_policy_of_distributional s (fun i : F => i.val)
    (fun i : F => bound i.val) (hdist F)
  exact ⟨A, fun σ hσ => hA ⟨σ,hσ⟩⟩

end KServer


namespace KServer
noncomputable section
open scoped BigOperators
universe u v

lemma mapHistory_comp {k : ℕ} {X : Type u} {Y : Type v} {Z : Type*}
    (f : X → Y) (g : Y → Z) (h : List (X × Fin k)) :
    mapHistory g (mapHistory f h) = mapHistory (g ∘ f) h := by
  simp [mapHistory,List.map_map,Function.comp_def]

lemma mapHistory_id {k : ℕ} {X : Type u} (h : List (X × Fin k)) :
    mapHistory id h = h := by simp [mapHistory]

lemma map_serve {k : ℕ} {X : Type u} {Y : Type v} (f : X → Y)
    (s : Configuration k X) (i : Fin k) (r : X) :
    f ∘ serve s i r = serve (f ∘ s) i (f r) := by
  classical
  funext j
  by_cases h : j=i <;> simp [serve,Function.comp_def,h]

/-- Executing an identical label string through an isometry preserves every
individual path cost, without any assumption on the ambient metric. -/
lemma serviceCost_map {k : ℕ} {X : Type u} {Y : Type v}
    [MetricSpace X] [MetricSpace Y] (f : X → Y) (hf : Isometry f)
    (s : Configuration k X) (σ : List X) (j : Fin σ.length → Fin k) :
    serviceCost (f ∘ s) (σ.map f) (fun i => j ⟨i.val,by simpa using i.isLt⟩) =
      serviceCost s σ j := by
  induction σ generalizing s with
  | nil => rfl
  | cons r σ ih =>
    change dist (f (s (j 0))) (f r) +
      serviceCost (serve (f ∘ s) (j 0) (f r)) (σ.map f)
        (fun i => j ⟨i.val+1,by simpa using i.isLt⟩) = _
    rw [hf.dist_eq,←map_serve]
    exact congrArg (fun z => dist (s (j 0)) r+z) (ih (serve s (j 0) r) (fun i => j i.succ))

lemma pathProbability_retract {k : ℕ} {X : Type u} {Y : Type v}
    (f : X → Y) (g : Y → X) (hfg : Function.LeftInverse f g)
    (A : Policy k Y) (h : List (Y × Fin k)) (σ : List Y)
    (j : Fin σ.length → Fin k) :
    pathProbability (retractPolicy f A) (mapHistory g h) (σ.map g)
      (fun i => j ⟨i.val,by simpa using i.isLt⟩) = pathProbability A h σ j := by
  induction σ generalizing h with
  | nil => rfl
  | cons r σ ih =>
    have hg : mapHistory f (mapHistory g h)=h := by
      rw [mapHistory_comp]
      have : f ∘ g = id := funext hfg
      rw [this,mapHistory_id]
    change (A (mapHistory f (mapHistory g h)) (f (g r))).val (j 0) *
      pathProbability (retractPolicy f A) (mapHistory g h++[(g r,j 0)]) (σ.map g)
        (fun i => j ⟨i.val+1,by simpa using i.isLt⟩) = _
    rw [hg,hfg]
    have hh : mapHistory g h++[(g r,j 0)]=mapHistory g (h++[(r,j 0)]) := by
      simp [mapHistory]
    rw [hh]
    exact congrArg (fun z => (A h r).val (j 0)*z) (ih (h++[(r,j 0)]) (fun i => j i.succ))

lemma expectedCost_retract {k : ℕ} {X : Type u} {Y : Type v}
    [MetricSpace X] [MetricSpace Y] (f : X → Y) (g : Y → X)
    (hfg : Function.LeftInverse f g) (hg : Isometry g)
    (A : Policy k Y) (s : Configuration k Y) (σ : List Y) :
    expectedCost (retractPolicy f A) (g ∘ s) (σ.map g)=expectedCost A s σ := by
  classical
  unfold expectedCost
  let e : (Fin (σ.map g).length → Fin k) ≃ (Fin σ.length → Fin k) :=
    Equiv.arrowCongr (finCongr (List.length_map ..)) (Equiv.refl _)
  apply Fintype.sum_equiv e
  intro j
  have hj : j=(fun i => e j ⟨i.val,by simpa using i.isLt⟩) := by rfl
  have hc := congrArg₂ (fun a b : ℝ => a*b) (pathProbability_retract f g hfg A [] σ (e j))
      (serviceCost_map g hg s σ (e j))
  rw [←hj] at hc
  simpa only [mapHistory,List.map_nil] using hc

lemma optimalCost_map {k : ℕ} {X : Type u} {Y : Type v}
    [MetricSpace X] [MetricSpace Y] (g : X → Y) (hg : Isometry g)
    (s : Configuration k X) (σ : List X) :
    optimalCost (g ∘ s) (σ.map g)=optimalCost s σ := by
  unfold optimalCost
  congr 1
  ext z
  constructor
  · rintro ⟨j,rfl⟩
    refine ⟨fun i => j (Fin.cast (List.length_map ..).symm i),?_⟩
    symm
    simpa only [Fin.cast, Fin.eta] using serviceCost_map g hg s σ
      (fun i => j (Fin.cast (List.length_map ..).symm i))
  · rintro ⟨j,rfl⟩
    exact ⟨fun i => j (Fin.cast (List.length_map ..) i),serviceCost_map g hg s σ j⟩

/-- Every finite family of requests lies in an actual finite submetric. Metric restriction preserves the finite laws, movement costs and offline minima needed for product compactness. -/


theorem distinct_policy_from_finite_submetrics {k : ℕ} [NeZero k]
    (α : ℝ) (hfinite : FiniteDistinctLawBound.{u} k α)
    {X : Type u} [MetricSpace X] (s : Configuration k X) (hs : Function.Injective s) :
    ∃ A : Policy k X, ∀ σ, expectedCost A s σ  ≤  α*optimalCost s σ := by
  classical
  apply global_policy_of_finite_laws s (fun σ => α*optimalCost s σ)
  intro F w hw hsum
  let points : Finset X := Finset.univ.image s ∪ F.biUnion List.toFinset
  have hstart (i : Fin k) : s i ∈ points := by
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  have hreq (σ : F) (x : X) (hx : x ∈ σ.val) : x ∈ points := by
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨σ.val,σ.property,by simpa using hx⟩
  let Y := {x : X // x ∈ points}
  let sy : Configuration k Y := fun i => ⟨s i,hstart i⟩
  let ret : X → Y := fun x => if hx : x ∈ points then ⟨x,hx⟩ else sy 0
  have hret : Function.LeftInverse ret (Subtype.val : Y → X) := by
    intro y
    simp only [ret,dite_eq_left y.property]
    exact Subtype.eta _ _
  have hiso : Isometry (Subtype.val : Y → X) := by exact isometry_subtype_coe
  let words : F → List Y := fun σ => σ.val.attach.map fun x => ⟨x.val,hreq σ x.val x.property⟩
  have hwords (σ : F) : (words σ).map (Subtype.val : Y → X)=σ.val := by
    simp [words,List.map_map,Function.comp_def]
  have hsy : (Subtype.val : Y → X) ∘ sy=s := rfl
  have hinj : Function.Injective sy := by
    intro i j hij
    exact hs (congrArg Subtype.val hij)
  -- `F` lives in universe u, so index the finitely many words by Fin card.
  let e : Fin (Fintype.card F) ≃ F := (Fintype.equivFin F).symm
  obtain ⟨A,hA⟩ := hfinite Y inferInstance inferInstance sy hinj _ inferInstance
    (fun i => words (e i)) (fun i => w (e i)) (fun i => hw (e i))
    (by simpa only [e.sum_comp] using hsum)
  refine ⟨retractPolicy ret A,?_⟩
  have he (i : F) : expectedCost (retractPolicy ret A) s i.val=
      expectedCost A sy (words i) := by
    rw [←hwords i,←hsy]
    exact expectedCost_retract ret Subtype.val hret hiso A sy (words i)
  have ho (i : F) : optimalCost s i.val=optimalCost sy (words i) := by
    rw [←hwords i,←hsy]
    exact optimalCost_map Subtype.val hiso sy (words i)
  simp only [he,ho]
  rw [e.sum_comp (fun i => w i*expectedCost A sy (words i)),
    e.sum_comp (fun i => w i*(α*optimalCost sy (words i)))] at hA
  exact hA

end
end KServer

namespace KServer
noncomputable section
universe u

/-- Source §10, repeated initial positions. This is a proved transformation of
policies, not a competitiveness assumption: the sole input is the virtual
policy's actual bound, and the real policy is constructed by finite filtering
and compactness above. Its additive constant is independent of every input. -/
theorem repeat_start_transfer {k : ℕ} [NeZero k] {X : Type u} [MetricSpace X]
    (s u : Configuration k X) (α : ℝ) (hα : 0 ≤ α)
    (A : Policy k X) (hA : ∀ σ, expectedCost A u σ ≤ α*optimalCost u σ) :
    ∃ B : Policy k X, ∀ σ,
      expectedCost B s σ  ≤  α*optimalCost s σ+(α+1)*matching s u := by
  obtain ⟨B,hB⟩ := BoundedSimulation.global_simulation A [] s u
  refine ⟨B,fun σ => ?_⟩
  have hb : expectedCost B s σ  ≤  matching s u+expectedCost A u σ := hB σ
  have ho := mul_le_mul_of_nonneg_left (optimalCost_change_start s u σ) hα
  have ha := hA σ
  nlinarith

lemma source_log_comparison {k : ℕ} (hk : 2 ≤ k) :
    (1+Real.log (k+1))^2 ≤ 4*(Real.log (k+1))^2 := by
  have hk3 : (3:ℝ) ≤ k+1 := by exact_mod_cast (show 3 ≤ k+1 by omega)
  have h3 : Real.exp 1< (k:ℝ)+1 := Real.exp_one_lt_three.trans_le hk3
  have hlog : 1<Real.log ((k:ℝ)+1) := (Real.lt_log_iff_exp_lt (by positivity)).mpr h3
  nlinarith [sq_nonneg (Real.log ((k:ℝ)+1)-1)]

/-- Arbitrary-metric transfer and repeated starting positions reduce the competitive estimate to a finite amplified-law bound, with constants uniform over all request horizons. -/


theorem main_reduction :
    (∃ d : ℝ, 0 ≤ d ∧ ∀ k : ℕ, 2 ≤ k →
      FiniteDistinctLawBound.{u} k (d*(1+Real.log (k+1))^2)) → ReductionStatement.{u} := by
  rintro ⟨d,hd,hfinite⟩
  refine ⟨4*d,?_⟩
  intro k hk X _ hcard s
  let : NeZero k := ⟨by omega⟩
  let α : ℝ := d*(1+Real.log (k+1))^2
  have hα : 0 ≤ α := mul_nonneg hd (sq_nonneg _)
  have halpha : α  ≤  (4*d)*(Real.log (k+1))^2 := by
    have h := mul_le_mul_of_nonneg_left (source_log_comparison hk) hd
    dsimp [α]
    nlinarith
  have hdist (u : Configuration k X) (hu : Function.Injective u) :
      ∃ A : Policy k X, ∀ σ, expectedCost A u σ ≤ α*optimalCost u σ :=
    distinct_policy_from_finite_submetrics α (hfinite k hk) u hu
  by_cases hs : Function.Injective s
  · obtain ⟨A,hA⟩ := hdist s hs
    refine ⟨A,0,le_rfl,fun _=>rfl,fun σ=> ?_⟩
    have h := mul_le_mul_of_nonneg_right halpha (optimalCost_nonneg s σ)
    simpa only [add_zero] using (hA σ).trans h
  · obtain ⟨e,he⟩ := hcard
    let u : Configuration k X := fun i=>e i.castSucc
    have hu : Function.Injective u := by
      intro i j hij
      exact Fin.castSucc_injective k (he hij)
    obtain ⟨A,hA⟩ := hdist u hu
    obtain ⟨B,hB⟩ := repeat_start_transfer s u α hα A hA
    refine ⟨B,(α+1)*matching s u,mul_nonneg (by linarith) (matching_nonneg _ _),
      fun h=>False.elim (hs h),fun σ=>?_⟩
    exact (hB σ).trans (add_le_add
      (mul_le_mul_of_nonneg_right halpha (optimalCost_nonneg s σ)) le_rfl)

end
end KServer

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Amplification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace KServer
universe u
namespace Episode
open Finset
variable {k : ℕ} {X : Type u} [MetricSpace X]

lemma traceCost_nonneg (s : Configuration k X) (h : List (X × Fin k)) :
    0  ≤  traceCost s h := by
  induction h generalizing s with
  | nil => simp [traceCost]
  | cons ri h ih => exact add_nonneg dist_nonneg (ih _)

omit [MetricSpace X] in
lemma configurationAfter_nil (s : Configuration k X) : configurationAfter s [] = s := rfl
omit [MetricSpace X] in
lemma configurationAfter_cons (s : Configuration k X) (r : X) (i : Fin k)
    (h : List (X × Fin k)) :
    configurationAfter s ((r,i)::h) = configurationAfter (serve s i r) h := rfl

lemma traceCost_append (s : Configuration k X) (h g : List (X × Fin k)) :
    traceCost s (h++g) = traceCost s h + traceCost (configurationAfter s h) g := by
  induction h generalizing s with
  | nil => simp [traceCost,configurationAfter]
  | cons ri h ih =>
    rcases ri with ⟨r,i⟩
    simp only [List.cons_append,traceCost,configurationAfter_cons,ih]
    ring

omit [MetricSpace X] in
lemma configurationAfter_append' (s : Configuration k X) (h g : List (X × Fin k)) :
    configurationAfter s (h++g) = configurationAfter (configurationAfter s h) g := by
  simp [configurationAfter,List.foldl_append]

omit [MetricSpace X] in
lemma serve_undo (s : Configuration k X) (i : Fin k) (r : X) :
    serve (serve s i r) i (s i) = s := by
  funext j
  by_cases h : j=i <;> simp [serve,h]

omit [MetricSpace X] in
/-- The literal reverse word returns the labeled tuple, not just its multiset. -/
lemma reverse_restores (s : Configuration k X) (h : List (X × Fin k)) :
    configurationAfter (configurationAfter s h) (reverseTrace s h) = s := by
  induction h generalizing s with
  | nil => rfl
  | cons ri h ih =>
    rcases ri with ⟨r,i⟩
    rw [reverseTrace,configurationAfter_cons,configurationAfter_append',ih]
    exact serve_undo s i r

lemma reverse_cost (s : Configuration k X) (h : List (X × Fin k)) :
    traceCost (configurationAfter s h) (reverseTrace s h) = traceCost s h := by
  induction h generalizing s with
  | nil => rfl
  | cons ri h ih =>
    rcases ri with ⟨r,i⟩
    rw [reverseTrace,configurationAfter_cons,traceCost_append,reverse_restores,ih]
    simp only [traceCost,add_zero,serve,Function.update_self]
    rw [dist_comm]
    ring

omit [MetricSpace X] in
lemma reverse_length (s : Configuration k X) (h : List (X × Fin k)) :
    (reverseTrace s h).length = h.length := by
  induction h generalizing s with
  | nil => rfl
  | cons ri h ih => rcases ri with ⟨r,i⟩; simp [reverseTrace,ih]

lemma serviceTrace_cost (s : Configuration k X) (σ : List X)
    (j : Fin σ.length → Fin k) : traceCost s (serviceTrace σ j) = serviceCost s σ j := by
  induction σ generalizing s with
  | nil => rfl
  | cons r σ ih => exact congrArg (fun x => dist (s (j 0)) r+x) (ih _ _)

omit [MetricSpace X] in
/-- Every legal designated trace gives a label string in the source lazy model. -/
lemma exists_labelString (h : List (X × Fin k)) :
    ∃ j : Fin (h.map Prod.fst).length → Fin k,
      serviceTrace (h.map Prod.fst) j = h := by
  induction h with
  | nil => exact ⟨Fin.elim0,rfl⟩
  | cons ri h ih =>
    rcases ri with ⟨r,i⟩
    obtain ⟨j,hj⟩ := ih
    refine ⟨Fin.cons i j,?_⟩
    change (r,i) :: serviceTrace (h.map Prod.fst) j = (r,i) :: h
    exact congrArg (List.cons (r,i)) hj

lemma optimalCost_le_trace [NeZero k] (s : Configuration k X) (h : List (X × Fin k)) :
    optimalCost s (h.map Prod.fst)  ≤  traceCost s h := by
  obtain ⟨j,hj⟩ := exists_labelString h
  have hc := serviceTrace_cost s (h.map Prod.fst) j
  rw [hj] at hc
  rw [hc]
  exact optimalCost_le_service s _ j

lemma cheap_closed_episode [NeZero k] (s : Configuration k X) (σ : List X) :
    ∃ h : List (X × Fin k), h.map Prod.fst = σ ∧
      traceCost s (h++reverseTrace s h) = 2*optimalCost s σ ∧
      configurationAfter s (h++reverseTrace s h) = s ∧
      (h++reverseTrace s h).length = 2*σ.length := by
  obtain ⟨j,hj⟩ := optimalCost_attained s σ
  let h := serviceTrace σ j
  have hc : traceCost s h = optimalCost s σ := by
    rw [serviceTrace_cost]; exact hj
  have hl : h.length = σ.length := by
    have hr := serviceTrace_requests σ j
    have he := congrArg List.length hr
    simpa only [List.length_map] using he
  refine ⟨h,serviceTrace_requests σ j,?_,?_,?_⟩
  · rw [traceCost_append,reverse_cost,hc]; ring
  · rw [configurationAfter_append',reverse_restores]
  · rw [List.length_append,reverse_length,hl]; omega

omit [MetricSpace X] in
lemma serve_same (s : Configuration k X) {i : Fin k} {r : X} (he : s i=r) :
    serve s i r = s := by
  funext j
  by_cases h : j=i <;> simp [serve,h,←he]

lemma zero_trace_unchanged (s : Configuration k X) (h : List (X × Fin k))
    (hz : traceCost s h=0) : configurationAfter s h=s ∧
      ∀ r ∈ h.map Prod.fst, ∃ i, s i=r := by
  induction h generalizing s with
  | nil => exact ⟨rfl,by simp⟩
  | cons ri h ih =>
    rcases ri with ⟨r,i⟩
    have hd : dist (s i) r=0 := by
      have hn := traceCost_nonneg (serve s i r) h
      have hn' : 0  ≤  dist (s i) r := dist_nonneg
      change dist (s i) r + traceCost (serve s i r) h=0 at hz
      linarith
    have he := dist_eq_zero.mp hd
    have hs := serve_same s he
    have ht : traceCost s h=0 := by simpa only [traceCost,hd,zero_add,hs] using hz
    obtain ⟨heq,hcov⟩ := ih s ht
    refine ⟨by simpa only [configurationAfter_cons,hs] using heq,?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with hx|hx
    · exact ⟨i,he.trans hx.symm⟩
    · exact hcov x hx

lemma lazy_covered_trace (s : Configuration k X) (h : List (X × Fin k))
    (hl : LazyTrace s h) (hc : ∀ r ∈ h.map Prod.fst, ∃ i, s i=r) :
    configurationAfter s h=s ∧ traceCost s h=0 := by
  induction h generalizing s with
  | nil => exact ⟨rfl,rfl⟩
  | cons ri h ih =>
    rcases ri with ⟨r,i⟩
    have he : s i=r := hl.1 (hc r (by simp))
    have hs := serve_same s he
    obtain ⟨heq,hcost⟩ := ih s (by simpa only [hs] using hl.2)
      (fun x hx => hc x (List.mem_cons_of_mem _ hx))
    exact ⟨by simpa only [configurationAfter_cons,hs] using heq,
      by simp only [traceCost,he,dist_self,zero_add,hs,hcost]⟩

lemma matching_zero_of_covers (s A : Configuration k X) (hs : Function.Injective s)
    (hc : ∀ i, ∃ j, A j=s i) : matching A s=0 := by
  classical
  choose f hf using hc
  have hi : Function.Injective f := by
    intro i j hij
    apply hs
    rw [←hf i,←hf j,hij]
  let e : Equiv.Perm (Fin k) := Equiv.ofBijective f
    ⟨hi,Finite.surjective_of_injective hi⟩
  have hms : matchSum s A e=0 := by
    apply Finset.sum_eq_zero
    intro i _
    change dist (s i) (A (f i))=0
    rw [hf,dist_self]
  have hm := matching_le s A e
  rw [hms,matching_symmetric] at hm
  exact le_antisymm hm (matching_nonneg _ _)

/-- A zero-cost reset cycle covers all k distinct starting points; strong
laziness then keeps that multiset fixed through all following reset requests. -/
lemma zero_cycle_finishes_reset (s A : Configuration k X) (hs : Function.Injective s)
    (h g : List (X × Fin k))
    (hcycle : h.map Prod.fst = List.ofFn s) (hz : traceCost A h=0)
    (hg : LazyTrace (configurationAfter A h) g)
    (hrequests : ∀ r ∈ g.map Prod.fst, r ∈ Set.range s) :
    matching (configurationAfter A (h++g)) s=0 := by
  obtain ⟨heq,hcov⟩ := zero_trace_unchanged A h hz
  have hc : ∀ i, ∃ j, A j=s i := by
    intro i
    apply hcov
    rw [hcycle]
    exact List.mem_ofFn.mpr ⟨i,rfl⟩
  have hga : LazyTrace A g := by simpa only [heq] using hg
  have hcover : ∀ r ∈ g.map Prod.fst, ∃ j, A j=r := by
    intro r hr
    obtain ⟨i,hi⟩ := hrequests r hr
    exact hi ▸ hc i
  rw [configurationAfter_append',heq,(lazy_covered_trace A g hga hcover).1]
  exact matching_zero_of_covers s A hs hc


omit [MetricSpace X] in
lemma lazyTrace_append (s : Configuration k X) (h g : List (X × Fin k)) :
    LazyTrace s (h++g) ↔ LazyTrace s h ∧ LazyTrace (configurationAfter s h) g := by
  induction h generalizing s with
  | nil => simp [LazyTrace,configurationAfter]
  | cons ri h ih =>
    rcases ri with ⟨r,i⟩
    simp only [List.cons_append,LazyTrace,configurationAfter_cons,ih,and_assoc]

lemma discrete_trace_cost (δ : ℝ) (_hδ : 0  ≤  δ)
    (hg : ∀ x y : X, x ≠ y → δ  ≤  dist x y)
    (A : Configuration k X) (h : List (X × Fin k)) :
    traceCost A h=0 ∨ δ  ≤  traceCost A h := by
  induction h generalizing A with
  | nil => exact Or.inl rfl
  | cons ri h ih =>
    rcases ri with ⟨r,i⟩
    by_cases he : A i=r
    · have hu := serve_same A he
      simpa only [traceCost,he,dist_self,zero_add,hu] using ih A
    · exact Or.inr (by
        have hd := hg (A i) r he
        have hn := traceCost_nonneg (serve A i r) h
        change δ  ≤  dist (A i) r + traceCost (serve A i r) h
        linarith)

omit [MetricSpace X] in
lemma cycleTrace_requests (s : Configuration k X) (j : Fin k → Fin k) :
    (cycleTrace s j).map Prod.fst = List.ofFn s := by
  simp only [cycleTrace,List.map_ofFn]
  rfl

omit [MetricSpace X] in
lemma resetTrace_requests (s : Configuration k X) (ls : List (Fin k → Fin k)) :
    ∀ r ∈ (resetTrace s ls).map Prod.fst, r ∈ Set.range s := by
  intro r hr
  obtain ⟨ri,hri,hr⟩ := List.mem_map.mp hr
  obtain ⟨j,hj,hri⟩ := List.mem_flatMap.mp hri
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hri
  exact ⟨i, by rw [←hr,←hi]⟩

lemma reset_dichotomy (s A : Configuration k X) (hs : Function.Injective s)
    (δ : ℝ) (hδ : 0  ≤  δ) (hg : ∀ x y : X, x ≠ y → δ  ≤  dist x y)
    (ls : List (Fin k → Fin k)) (hl : LazyTrace A (resetTrace s ls)) :
    matching (configurationAfter A (resetTrace s ls)) s=0 ∨
      (ls.length : ℝ)*δ  ≤  traceCost A (resetTrace s ls) := by
  induction ls generalizing A with
  | nil => exact Or.inr (by simp [resetTrace,traceCost])
  | cons j ls ih =>
    have he : resetTrace s (j::ls) = cycleTrace s j ++ resetTrace s ls := rfl
    rw [he] at hl ⊢
    obtain ⟨hlc,hlt⟩ := (lazyTrace_append _ _ _).mp hl
    rcases discrete_trace_cost δ hδ hg A (cycleTrace s j) with hz|hpos
    · exact Or.inl (zero_cycle_finishes_reset s A hs _ _ (cycleTrace_requests s j)
        hz hlt (resetTrace_requests s ls))
    · rcases ih (configurationAfter A (cycleTrace s j)) hlt with hm|hb
      · exact Or.inl (by rwa [configurationAfter_append'])
      · right
        rw [traceCost_append,List.length_cons,Nat.cast_add,Nat.cast_one]
        linarith

lemma matching_le_diameter (A s : Configuration k X) (Δ : ℝ)
    (hdiam : ∀ x y : X, dist x y  ≤  Δ) : matching A s  ≤  (k : ℝ)*Δ := by
  apply (matching_le A s (Equiv.refl _)).trans
  change (∑ i : Fin k, dist (A i) (s i))  ≤  _
  calc
    _  ≤  ∑ _i : Fin k, Δ := Finset.sum_le_sum fun _ _ => hdiam _ _
    _ = _ := by simp

/-- Equation reset-mismatch with its actual finite-reset cost. The metric gap
is used only to choose the number of cycles; no bound depends on the horizon. -/
theorem reset_mismatch (s A : Configuration k X) (hs : Function.Injective s)
    (δ Δ : ℝ) (hδ : 0  ≤  δ) (hg : ∀ x y : X, x ≠ y → δ  ≤  dist x y)
    (hdiam : ∀ x y : X, dist x y  ≤  Δ)
    (ls : List (Fin k → Fin k)) (hR : (k : ℝ)*Δ  ≤  (ls.length : ℝ)*δ)
    (hl : LazyTrace A (resetTrace s ls)) :
    matching (configurationAfter A (resetTrace s ls)) s  ≤ 
      traceCost A (resetTrace s ls) := by
  rcases reset_dichotomy s A hs δ hδ hg ls hl with hm|hc
  · rw [hm]; exact traceCost_nonneg _ _
  · exact (matching_le_diameter _ _ Δ hdiam).trans (hR.trans hc)


/-- Source's finite-space gap and diameter, with no assumption of discreteness
on the eventual arbitrary metric space. Only the local finite experiment uses
these constants. -/
lemma finite_gap_diameter [Fintype X] (hne : ∃ x y : X, x ≠ y) :
    ∃ δ Δ : ℝ, 0 < δ ∧ 0  ≤  Δ ∧
      (∀ x y : X, x ≠ y → δ  ≤  dist x y) ∧ (∀ x y : X, dist x y  ≤  Δ) := by
  classical
  let pairs : Finset (X × X) := Finset.univ.filter fun p => p.1 ≠ p.2
  have hp : pairs.Nonempty := by
    obtain ⟨x,y,hxy⟩ := hne
    exact ⟨(x,y),by simp [pairs,hxy]⟩
  obtain ⟨p,hp,hm⟩ := Finset.exists_min_image pairs (fun p => dist p.1 p.2) hp
  have hup : (Finset.univ : Finset (X × X)).Nonempty := ⟨p,Finset.mem_univ _⟩
  obtain ⟨q,hq,hM⟩ := Finset.exists_max_image Finset.univ
    (fun p : X × X => dist p.1 p.2) hup
  refine ⟨dist p.1 p.2,dist q.1 q.2,?_,dist_nonneg,?_,?_⟩
  · apply dist_pos.mpr
    exact (Finset.mem_filter.mp hp).2
  · intro x y hxy; exact hm (x,y) (by simp [pairs,hxy])
  · intro x y; exact hM (x,y) (Finset.mem_univ _)

lemma resetCount_bound (Δ δ : ℝ) (hδ : 0 < δ) :
    (k : ℝ)*Δ < (resetCount k Δ δ : ℝ)*δ := by
  have h := Nat.lt_floor_add_one ((k : ℝ)*Δ/δ)
  have h' := (div_lt_iff₀ hδ).mp h
  simpa only [resetCount,Nat.cast_add,Nat.cast_one] using h'

/-- The finite reset length is chosen once for the metric and starting stock,
not for the law or horizon. It applies to every strongly lazy trace of that
reset word, including choices of labels occupying equal positions. -/
theorem exists_uniform_reset [Fintype X] (s : Configuration k X)
    (hs : Function.Injective s) (hne : ∃ x y : X, x ≠ y) :
    ∃ R : ℕ, 0 < R ∧ ∀ A : Configuration k X,
      ∀ ls : List (Fin k → Fin k), ls.length=R →
        LazyTrace A (resetTrace s ls) →
        matching (configurationAfter A (resetTrace s ls)) s  ≤  traceCost A (resetTrace s ls) := by
  obtain ⟨δ,Δ,hδ,hΔ,hg,hdiam⟩ := finite_gap_diameter hne
  refine ⟨resetCount k Δ δ,Nat.zero_lt_succ _,?_⟩
  intro A ls hlen hl
  apply reset_mismatch s A hs δ Δ hδ.le hg hdiam ls _ hl
  rw [hlen]
  exact (resetCount_bound Δ δ hδ).le

end Episode
end KServer

namespace KServer
namespace Amplification
noncomputable section
open Finset
universe u
variable {k : ℕ} [NeZero k] {X : Type u} [MetricSpace X]

omit [NeZero k] in
lemma cost_nil (A : Policy k X) (s : Configuration k X) (h : List (X × Fin k)) :
    cost A s h []=0 := continuationCost_nil _ _ _

omit [NeZero k] in
lemma cost_cons (A : Policy k X) (s : Configuration k X)
    (h : List (X × Fin k)) (r : X) (σ : List X) :
    cost A s h (r::σ)=∑ i, (A h r).val i *
      (dist (configurationAfter s h i) r+cost A s (h++[(r,i)]) σ) := by
  simp only [cost,continuationCost_cons,configurationAfter_append]

omit [NeZero k] [MetricSpace X] in
lemma after_const (A : Policy k X) (h : List (X × Fin k)) (σ : List X) (c : ℝ) :
    after A h σ (fun _=>c)=c := by
  induction σ generalizing h with
  | nil => rfl
  | cons r σ ih => simp only [after,ih,←sum_mul,(A h r).property.2,one_mul]

omit [NeZero k] [MetricSpace X] in
lemma after_mono (A : Policy k X) (h : List (X × Fin k)) (σ : List X)
    {f g : List (X × Fin k) → ℝ} (hfg : ∀ h, f h ≤ g h) :
    after A h σ f ≤ after A h σ g := by
  induction σ generalizing h with
  | nil => exact hfg h
  | cons r σ ih =>
    exact sum_le_sum fun i _=>mul_le_mul_of_nonneg_left (ih _) ((A h r).property.1 i)

omit [NeZero k] [MetricSpace X] in
lemma after_nonneg (A : Policy k X) (h : List (X × Fin k)) (σ : List X)
    {f : List (X × Fin k) → ℝ} (hf : ∀ h, 0 ≤ f h) : 0 ≤ after A h σ f := by
  simpa only [after_const] using after_mono A h σ hf

omit [NeZero k] [MetricSpace X] in
lemma after_add (A : Policy k X) (h : List (X × Fin k)) (σ : List X)
    (f g : List (X × Fin k) → ℝ) :
    after A h σ (fun h=>f h+g h)=after A h σ f+after A h σ g := by
  induction σ generalizing h with
  | nil => rfl
  | cons r σ ih => simp only [after,ih,mul_add,sum_add_distrib]

omit [NeZero k] [MetricSpace X] in
lemma after_mul (A : Policy k X) (h : List (X × Fin k)) (σ : List X)
    (c : ℝ) (f : List (X × Fin k) → ℝ) :
    after A h σ (fun h=>c*f h)=c*after A h σ f := by
  induction σ generalizing h with
  | nil => rfl
  | cons r σ ih => simp only [after,ih,Finset.mul_sum]; congr 1; funext i; ring

omit [NeZero k] [MetricSpace X] in
lemma after_append (A : Policy k X) (h : List (X × Fin k)) (ρ σ : List X)
    (f : List (X × Fin k) → ℝ) :
    after A h (ρ++σ) f=after A h ρ (fun h=>after A h σ f) := by
  induction ρ generalizing h with
  | nil => rfl
  | cons r ρ ih => simp only [List.cons_append,after,ih]

omit [NeZero k] in
lemma cost_append (A : Policy k X) (s : Configuration k X)
    (h : List (X × Fin k)) (ρ σ : List X) :
    cost A s h (ρ++σ)=cost A s h ρ+after A h ρ (fun h=>cost A s h σ) := by
  induction ρ generalizing h with
  | nil => simp [cost_nil,after]
  | cons r ρ ih =>
    simp only [List.cons_append,cost_cons,ih,after,mul_add,sum_add_distrib]
    ring

omit [NeZero k] in
lemma cost_nonneg (A : Policy k X) (s : Configuration k X)
    (h : List (X × Fin k)) (σ : List X) : 0 ≤ cost A s h σ := by
  unfold cost continuationCost
  exact sum_nonneg fun j _=>mul_nonneg (pathProbability_nonneg _ _ _ _) (serviceCost_nonneg _ _ _)

omit [NeZero k] [MetricSpace X] in
lemma after_paths (A : Policy k X) (h : List (X × Fin k)) (σ : List X)
    (f : List (X × Fin k) → ℝ) :
    after A h σ f=∑ j : Fin σ.length → Fin k,
      pathProbability A h σ j * f (h++Episode.serviceTrace σ j) := by
  induction σ generalizing h with
  | nil => simp [after,pathProbability,Episode.serviceTrace]
  | cons r σ ih =>
    change after A h (r::σ) f = ∑ j : Fin (σ.length+1) → Fin k,
      pathProbability A h (r::σ) j * f (h++Episode.serviceTrace (r::σ) j)
    rw [sum_labelStrings]
    simp only [after,ih,pathProbability,Episode.serviceTrace,Fin.cons_zero,Fin.cons_succ,List.append_assoc,
      List.singleton_append,mul_assoc,Finset.mul_sum]

omit [NeZero k] in
lemma cost_paths (A : Policy k X) (s : Configuration k X) (h : List (X × Fin k))
    (σ : List X) : cost A s h σ = ∑ j : Fin σ.length → Fin k,
      pathProbability A h σ j * Episode.traceCost (configurationAfter s h) (Episode.serviceTrace σ j) := by
  simp only [cost,continuationCost,Episode.serviceTrace_cost]

omit [NeZero k] [MetricSpace X] in
lemma supported_trace_lazy (A : Policy k X) (s : Configuration k X)
    (hl : StronglyLazy s A) (h : List (X × Fin k)) (σ : List X)
    (j : Fin σ.length → Fin k) (hp : pathProbability A h σ j ≠0) :
    Episode.LazyTrace (configurationAfter s h) (Episode.serviceTrace σ j) := by
  induction σ generalizing h with
  | nil => trivial
  | cons r σ ih =>
    have hn := mul_ne_zero_iff.mp hp
    refine ⟨?_,?_⟩
    · intro hc
      by_contra hh
      exact hn.1 (hl h r hc (j 0) hh)
    · have ht := ih (h++[(r,j 0)]) (fun i=>j i.succ) hn.2
      simpa only [configurationAfter_append] using ht

omit [NeZero k] [MetricSpace X] in
/-- Extract one cycle's label list from any trace whose requests are the fixed
starting tuple. This prevents an unjustified switch from label multisets to
labeled equality in the reset argument. -/
lemma trace_of_cycle_requests (s : Configuration k X) (h : List (X × Fin k))
    (hr : h.map Prod.fst=List.ofFn s) :
    ∃ j : Fin k → Fin k, h=Episode.cycleTrace s j := by
  have hlen : h.length=k := by
    have := congrArg List.length hr
    simpa only [List.length_map,List.length_ofFn] using this
  let j : Fin k → Fin k := fun i=>(h.get ⟨i.val,by simp [hlen]⟩).2
  refine ⟨j,?_⟩
  apply List.ext_getElem (by simp [Episode.cycleTrace,hlen])
  intro n hn hn'
  simp only [Episode.cycleTrace,List.getElem_ofFn]
  have hnk : n<k := by simpa [hlen] using hn
  have hrn := congrArg (fun l : List X=>l[n]?) hr
  have hx : h[n].1=s ⟨n,hnk⟩ := by
    simpa [List.getElem?_eq_getElem,hn,hnk] using hrn
  exact Prod.ext hx rfl

omit [NeZero k] [MetricSpace X] in
lemma trace_of_reset_requests (s : Configuration k X) (R : ℕ)
    (h : List (X × Fin k)) (hr : h.map Prod.fst=(List.replicate R (List.ofFn s)).flatten) :
    ∃ ls : List (Fin k → Fin k), ls.length=R ∧ h=Episode.resetTrace s ls := by
  induction R generalizing h with
  | zero =>
    have he : h=[] := by
      have hh := congrArg List.length hr
      simpa using hh
    exact ⟨[],rfl,he⟩
  | succ R ih =>
    have hr' : h.map Prod.fst=List.ofFn s++(List.replicate R (List.ofFn s)).flatten := by
      simpa only [List.replicate_succ,List.flatten_cons] using hr
    have ht : (h.take k).map Prod.fst=List.ofFn s := by
      rw [List.map_take,hr']
      simp
    have hd : (h.drop k).map Prod.fst=(List.replicate R (List.ofFn s)).flatten := by
      rw [List.map_drop,hr']
      simp
    obtain ⟨j,hj⟩ := trace_of_cycle_requests s (h.take k) ht
    obtain ⟨ls,hlen,hls⟩ := ih (h.drop k) hd
    refine ⟨j::ls,by simp [hlen],?_⟩
    change h=Episode.cycleTrace s j++Episode.resetTrace s ls
    rw [←hj,←hls,List.take_append_drop]

omit [NeZero k] in
/-- The reset bound for literal Bellman expectation under an actual strongly
lazy policy, not an assumed distribution of reset costs. -/
theorem expected_reset [Fintype X] (s : Configuration k X) (hs : Function.Injective s)
    (hne : ∃ x y : X, x ≠ y) :
    ∃ R : ℕ, 0<R ∧ ∀ A : Policy k X, StronglyLazy s A → ∀ h,
      after A h ((List.replicate R (List.ofFn s)).flatten)
        (fun g=>matching (configurationAfter s g) s)  ≤ 
      cost A s h ((List.replicate R (List.ofFn s)).flatten) := by
  obtain ⟨R,hR,hreset⟩ := Episode.exists_uniform_reset s hs hne
  refine ⟨R,hR,?_⟩
  intro A hA h
  rw [after_paths,cost_paths]
  apply sum_le_sum
  intro j _
  by_cases hzero : pathProbability A h ((List.replicate R (List.ofFn s)).flatten) j=0
  · simp [hzero]
  · obtain ⟨ls,hlen,htrace⟩ := trace_of_reset_requests s R
      (Episode.serviceTrace ((List.replicate R (List.ofFn s)).flatten) j)
      (Episode.serviceTrace_requests _ _)
    have htl := supported_trace_lazy A s hA h _ j hzero
    rw [htrace] at htl
    have hb := hreset (configurationAfter s h) ls hlen htl
    rw [←htrace] at hb
    rw [Episode.configurationAfter_append']
    exact mul_le_mul_of_nonneg_left hb (pathProbability_nonneg _ _ _ _)

variable {Ω : Type} [Fintype Ω]

/-- The minimum is attained in the full product of causal decision simplexes,
not in a horizon-dependent surrogate space. -/
lemma law_minimum (s : Configuration k X) (σ : Ω → List X) (w : Ω → ℝ) :
    ∃ P : Policy k X, ∀ A : Policy k X,
      (∑ ω, w ω*expectedCost P s (σ ω))  ≤  ∑ ω, w ω*expectedCost A s (σ ω) := by
  have hc : Continuous fun A : Policy k X => ∑ ω, w ω*expectedCost A s (σ ω) :=
    continuous_finsetSum _ fun ω _ => continuous_const.mul (continuous_expectedCost s (σ ω))
  obtain ⟨P,_,hP⟩ := isCompact_univ.exists_isMinOn
    (Set.univ_nonempty : (Set.univ : Set (Policy k X)).Nonempty) hc.continuousOn
  exact ⟨P,fun A=>hP (Set.mem_univ A)⟩

/-- Minimum-law continuation and compactness give a causal policy without sampling fictitious prefixes. -/


lemma minimum_continuation (s : Configuration k X) (σ : Ω → List X) (w : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω=1) (m : ℝ)
    (hmin : ∀ B : Policy k X, m  ≤  ∑ ω, w ω*expectedCost B s (σ ω))
    (A : Policy k X) (h : List (X × Fin k)) :
    m  ≤  matching (configurationAfter s h) s+∑ ω, w ω*cost A s h (σ ω) := by
  obtain ⟨B,hB⟩ := BoundedSimulation.global_simulation A h s (configurationAfter s h)
  have hb := (hmin B).trans (sum_le_sum fun ω _=>
    mul_le_mul_of_nonneg_left (hB (σ ω)) (hw ω))
  simpa only [mul_add,sum_add_distrib,←sum_mul,hsum,one_mul,
    matching_symmetric s (configurationAfter s h),cost] using hb

omit [NeZero k] [MetricSpace X] in
lemma lawAfter_mono (A : Policy k X) (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (σ : Ω → List X) (h : List (X × Fin k))
    {f g : List (X × Fin k) → ℝ} (hfg : ∀ h, f h ≤ g h) :
    lawAfter A w σ h f ≤ lawAfter A w σ h g :=
  sum_le_sum fun ω _=>mul_le_mul_of_nonneg_left (after_mono A h _ hfg) (hw ω)

omit [NeZero k] [MetricSpace X] in
lemma lawAfter_const (A : Policy k X) (w : Ω → ℝ) (hsum : ∑ ω, w ω=1)
    (σ : Ω → List X) (h : List (X × Fin k)) (c : ℝ) :
    lawAfter A w σ h (fun _=>c)=c := by
  simp only [lawAfter,after_const,←sum_mul,hsum,one_mul]

omit [NeZero k] [MetricSpace X] in
lemma lawAfter_add (A : Policy k X) (w : Ω → ℝ) (σ : Ω → List X)
    (h : List (X × Fin k)) (f g : List (X × Fin k) → ℝ) :
    lawAfter A w σ h (fun h=>f h+g h)=lawAfter A w σ h f+lawAfter A w σ h g := by
  simp only [lawAfter,after_add,mul_add,sum_add_distrib]

omit [NeZero k] in
/-- Exact telescoping lower bound for repeated independent closed episodes.
The second premise here is derived from `expected_reset` below; it is not an
assumed policy-existence claim. -/
lemma episode_telescope (A : Policy k X) (s : Configuration k X)
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω=1)
    (ep : Ω → List X) (m : ℝ)
    (hstep : ∀ h, m+lawAfter A w ep h (fun g=>matching (configurationAfter s g) s)  ≤ 
      matching (configurationAfter s h) s+lawCost A s w ep h) :
    ∀ (N : ℕ) h, (N : ℝ)*m  ≤  matching (configurationAfter s h) s+runCost A s w ep N h := by
  intro N
  induction N with
  | zero => intro h; simpa [runCost] using matching_nonneg (configurationAfter s h) s
  | succ N ih =>
    intro h
    have he := lawAfter_mono A w hw ep h ih
    rw [lawAfter_const A w hsum,lawAfter_add] at he
    have hs := hstep h
    simp only [runCost,Nat.cast_add,Nat.cast_one]
    linarith

/-- The reset charge and the minimum-continuation inequality together give the
one-episode drift needed for the preceding telescope. -/
lemma episode_step (A : Policy k X) (s : Configuration k X)
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω=1)
    (σ ρ : Ω → List X) (z : List X) (m : ℝ)
    (hmin : ∀ B : Policy k X, m  ≤  ∑ ω, w ω*expectedCost B s (σ ω))
    (hz : ∀ h, after A h z (fun g=>matching (configurationAfter s g) s) ≤ cost A s h z) :
    ∀ h, m+lawAfter A w (fun ω=>σ ω++ρ ω++z) h
      (fun g=>matching (configurationAfter s g) s)  ≤ 
      matching (configurationAfter s h) s+lawCost A s w (fun ω=>σ ω++ρ ω++z) h := by
  intro h
  have hm := minimum_continuation s σ w hw hsum m hmin A h
  have hb : lawCost A s w σ h + lawAfter A w (fun ω=>σ ω++ρ ω++z) h
      (fun g=>matching (configurationAfter s g) s)  ≤ 
      lawCost A s w (fun ω=>σ ω++ρ ω++z) h := by
    unfold lawCost lawAfter
    rw [←sum_add_distrib]
    apply sum_le_sum
    intro ω _
    rw [←mul_add]
    apply mul_le_mul_of_nonneg_left _ (hw ω)
    rw [after_append,after_append,cost_append,cost_append]
    have hr : after A h (σ ω) (fun g=>after A g (ρ ω) (fun g=>cost A s g z))  ≤ 
        after A h (σ ω) (fun g=>cost A s g (ρ ω))+
          after A h (σ ω) (fun g=>after A g (ρ ω) (fun g=>cost A s g z)) :=
      le_add_of_nonneg_left (after_nonneg A h _ (fun g=>cost_nonneg A s g _))
    have he := after_mono A h (σ ω) (fun g=>after_mono A g (ρ ω) hz)
    rw [after_append]
    linarith
  change m  ≤  matching (configurationAfter s h) s+lawCost A s w σ h at hm
  linarith

lemma sum_strings {N : ℕ} (f : (Fin (N+1) → Ω) → ℝ) :
    ∑ v, f v=∑ ω, ∑ v : Fin N → Ω, f (Fin.cons ω v) := by
  rw [←Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (N+1)=>Ω))
    (fun p=>f (Fin.cons p.1 p.2)) f (fun _=>rfl),Fintype.sum_prod_type]

omit [Fintype Ω] in
lemma iidWeight_nonneg (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) :
    ∀ N v, 0 ≤ iidWeight w N v := by
  intro N
  induction N with
  | zero => intro v; exact zero_le_one
  | succ N ih => intro v; exact mul_nonneg (hw _) (ih _)

lemma iidWeight_sum (w : Ω → ℝ) (hsum : ∑ ω, w ω=1) :
    ∀ N, ∑ v, iidWeight w N v=1 := by
  intro N
  induction N with
  | zero => simp [iidWeight]
  | succ N ih =>
    rw [sum_strings]
    simp only [iidWeight,Fin.cons_zero,Fin.cons_succ,←Finset.mul_sum,ih,mul_one,hsum]

omit [NeZero k] [MetricSpace X] in
lemma after_sum (A : Policy k X) (h : List (X × Fin k)) (σ : List X)
    {ι : Type} [Fintype ι] (f : ι → List (X × Fin k) → ℝ) :
    after A h σ (fun h=>∑ i, f i h)=∑ i, after A h σ (f i) := by
  induction σ generalizing h with
  | nil => rfl
  | cons r σ ih => simp only [after,ih,Finset.mul_sum]; exact sum_comm

omit [NeZero k] in
/-- The Bellman recursion is exactly the expectation under the concrete finite
product law on iid forward words, including the algorithm's labels. -/
lemma runCost_iid (A : Policy k X) (s : Configuration k X) (w : Ω → ℝ)
    (hsum : ∑ ω, w ω=1) (ep : Ω → List X) :
    ∀ N h, runCost A s w ep N h=
      ∑ v, iidWeight w N v*cost A s h (iidWord ep N v) := by
  intro N
  induction N with
  | zero => intro h; simp [runCost,iidWord,cost_nil]
  | succ N ih =>
    intro h
    rw [sum_strings]
    simp only [runCost,iidWord,iidWeight,Fin.cons_zero,Fin.cons_succ,cost_append,
      mul_add,sum_add_distrib]
    simp_rw [mul_assoc,←Finset.mul_sum,←sum_mul,iidWeight_sum w hsum,one_mul]
    rw [←sum_add_distrib]
    unfold lawCost lawAfter
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro ω _
    rw [←mul_add,←mul_add]
    congr 2
    rw [show runCost A s w ep N = (fun h=>∑ v, iidWeight w N v*cost A s h (iidWord ep N v)) from funext ih,after_sum]
    simp only [after_mul]

omit [MetricSpace X] [Fintype Ω] in
lemma iidWord_length (ep : Ω → List X) (L : ℕ) (hL : ∀ ω, (ep ω).length=L) :
    ∀ N v, (iidWord ep N v).length=N*L := by
  intro N
  induction N with
  | zero => simp [iidWord]
  | succ N ih => intro v; simp [iidWord,List.length_append,hL,ih,Nat.succ_mul,Nat.add_comm]

omit [NeZero k] in
lemma stationary_trace (s : Configuration k X) (t : List (X × Fin k))
    (ht : ∀ ri ∈ t, s ri.2=ri.1) :
    configurationAfter s t=s ∧ Episode.traceCost s t=0 := by
  induction t with
  | nil => exact ⟨rfl,rfl⟩
  | cons ri t ih =>
    rcases ri with ⟨r,i⟩
    obtain ⟨he,hc⟩ := ih (fun x hx=>ht x (List.mem_cons_of_mem _ hx))
    have hs := Episode.serve_same s (ht (r,i) (List.mem_cons_self))
    simp only [Episode.configurationAfter_cons,hs,he,Episode.traceCost,
      ht (r,i) (List.mem_cons_self),dist_self,zero_add,hc,and_self]

omit [NeZero k] in
lemma stationary_reset (s : Configuration k X) (R : ℕ) :
    configurationAfter s (Episode.resetTrace s (List.replicate R id))=s ∧
      Episode.traceCost s (Episode.resetTrace s (List.replicate R id))=0 := by
  apply stationary_trace
  intro ri hri
  obtain ⟨j,hj,hri⟩ := List.mem_flatMap.mp hri
  obtain ⟨_,rfl⟩ := List.mem_replicate.mp hj
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hri
  simp only [←hi,Function.id_def]

omit [NeZero k] [MetricSpace X] in
lemma reset_length (s : Configuration k X) (ls : List (Fin k → Fin k)) :
    (Episode.resetTrace s ls).length=ls.length*k := by
  induction ls with
  | nil => simp [Episode.resetTrace]
  | cons j ls ih =>
    change (Episode.cycleTrace s j++Episode.resetTrace s ls).length=(ls.length+1)*k
    simp only [List.length_append,Episode.cycleTrace,List.length_ofFn,ih]
    ring

omit [NeZero k] [MetricSpace X] in
lemma reset_requests_eq (s : Configuration k X) (R : ℕ) :
    (Episode.resetTrace s (List.replicate R id)).map Prod.fst=
      (List.replicate R (List.ofFn s)).flatten := by
  induction R with
  | zero => rfl
  | succ R ih =>
    change (Episode.cycleTrace s id++Episode.resetTrace s (List.replicate R id)).map Prod.fst=_
    rw [List.map_append,Episode.cycleTrace_requests,ih]
    rfl

/-- Padded *closed* episodes, valid even when forward lengths differ. Padding
is inserted after the reverse path and before the reset, so it costs the closed
offline trace zero and does not compromise the online reset-mismatch bound. -/
lemma closed_padded_episodes (s : Configuration k X) (σ : Ω → List X) (R : ℕ) :
    ∃ L : ℕ, ∃ ρ : Ω → List X, ∃ t : Ω → List (X × Fin k),
      ∀ ω, (t ω).map Prod.fst=σ ω++ρ ω++(List.replicate R (List.ofFn s)).flatten ∧
        configurationAfter s (t ω)=s ∧ Episode.traceCost s (t ω)=2*optimalCost s (σ ω) ∧
        (t ω).length=L := by
  classical
  choose h hreq hcost hend hlen using fun ω=>Episode.cheap_closed_episode s (σ ω)
  let M := Finset.univ.sup (fun ω=>(σ ω).length)
  let pad (ω : Ω) := List.replicate (2*(M-(σ ω).length)) (s 0,(0 : Fin k))
  let z := Episode.resetTrace s (List.replicate R id)
  have hz := stationary_reset s R
  have hp (ω : Ω) : configurationAfter s (pad ω)=s ∧ Episode.traceCost s (pad ω)=0 := by
    apply stationary_trace
    intro ri hri
    have he := (List.mem_replicate.mp hri).2
    subst ri
    rfl
  refine ⟨2*M+R*k,fun ω=>(Episode.reverseTrace s (h ω)++pad ω).map Prod.fst,
    fun ω=>((h ω++Episode.reverseTrace s (h ω))++pad ω)++z,?_⟩
  intro ω
  have hM : (σ ω).length ≤ M := by
    dsimp [M]
    exact Finset.le_sup (f := fun ω : Ω => (σ ω).length) (Finset.mem_univ ω)
  refine ⟨?_,?_,?_,?_⟩
  · simp only [List.map_append,hreq]
    simp only [z,reset_requests_eq,List.append_assoc]
  · rw [Episode.configurationAfter_append',Episode.configurationAfter_append',hend,(hp ω).1]
    exact hz.1
  · have hf : configurationAfter s ((h ω++Episode.reverseTrace s (h ω))++pad ω)=s := by
      rw [Episode.configurationAfter_append',hend,(hp ω).1]
    rw [Episode.traceCost_append,hf,Episode.traceCost_append,hcost,hend,(hp ω).2,hz.2]
    ring
  · simp only [List.length_append,hlen,pad,List.length_replicate,z,reset_length]
    omega

omit [NeZero k] [MetricSpace X] [Fintype Ω] in
lemma iidTrace_requests (t : Ω → List (X × Fin k)) :
    ∀ N v, (iidTrace t N v).map Prod.fst=iidWord (fun ω=>(t ω).map Prod.fst) N v := by
  intro N
  induction N with
  | zero => intro v; rfl
  | succ N ih => intro v; simp only [iidTrace,List.map_append,iidWord,ih]

omit [NeZero k] [Fintype Ω] in
lemma iidTrace_cost (s : Configuration k X) (t : Ω → List (X × Fin k))
    (ht : ∀ ω, configurationAfter s (t ω)=s) :
    ∀ N v, Episode.traceCost s (iidTrace t N v)=iidSum (fun ω=>Episode.traceCost s (t ω)) N v := by
  intro N
  induction N with
  | zero => intro v; rfl
  | succ N ih => intro v; simp only [iidTrace,Episode.traceCost_append,ht,ih,iidSum]

lemma iidSum_expectation (w q : Ω → ℝ) (hsum : ∑ ω,w ω=1) :
    ∀ N, (∑ v, iidWeight w N v*iidSum q N v)=(N : ℝ)*∑ ω,w ω*q ω := by
  intro N
  induction N with
  | zero => simp [iidSum]
  | succ N ih =>
    rw [sum_strings]
    simp only [iidWeight,iidSum,Fin.cons_zero,Fin.cons_succ,mul_add,sum_add_distrib]
    simp_rw [mul_assoc,←Finset.mul_sum,←sum_mul,iidWeight_sum w hsum,one_mul,ih]
    rw [hsum,one_mul]
    push_cast
    ring

lemma iid_offline (s : Configuration k X) (σ : Ω → List X)
    (t : Ω → List (X × Fin k)) (ht : ∀ ω, configurationAfter s (t ω)=s)
    (hc : ∀ ω, Episode.traceCost s (t ω)=2*optimalCost s (σ ω))
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω,w ω=1) (N : ℕ) :
    (∑ v, iidWeight w N v*optimalCost s (iidWord (fun ω=>(t ω).map Prod.fst) N v)) ≤
      2*(N : ℝ)*(∑ ω,w ω*optimalCost s (σ ω)) := by
  have hb := sum_le_sum (s:=Finset.univ) (fun v _=>mul_le_mul_of_nonneg_left
    (Episode.optimalCost_le_trace s (iidTrace t N v)) (iidWeight_nonneg w hw N v))
  simp only [iidTrace_requests,iidTrace_cost s t ht] at hb
  refine hb.trans_eq ?_
  rw [iidSum_expectation w _ hsum]
  simp_rw [hc]
  rw [show (∑ ω,w ω*(2*optimalCost s (σ ω)))=2*∑ ω,w ω*optimalCost s (σ ω) by
    rw [Finset.mul_sum]; apply sum_congr rfl; intro ω _; ring]
  ring

universe v
variable {Λ : Type v} [Fintype Λ]

omit [Fintype Λ] in
lemma pushWeights_nonneg (f : Ω → Λ) (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) :
    ∀ y, 0 ≤ pushWeights f w y := by
  classical
  intro y
  unfold pushWeights
  exact sum_nonneg fun ω _=>by split_ifs; exact hw ω; exact le_rfl

lemma pushWeights_expectation (f : Ω → Λ) (w : Ω → ℝ) (g : Λ → ℝ) :
    (∑ y, pushWeights f w y*g y)=∑ ω,w ω*g (f ω) := by
  classical
  simp only [pushWeights,Finset.sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro ω _
  simp only [ite_mul,zero_mul]
  simp

lemma pushWeights_sum (f : Ω → Λ) (w : Ω → ℝ) (hsum : ∑ ω,w ω=1) :
    ∑ y,pushWeights f w y=1 := by
  simpa only [mul_one,hsum] using pushWeights_expectation f w (fun _=>1)

omit [NeZero k] in
/-- Exact transport of a horizon law to a finite indexed family; identically
valued words are grouped rather than incorrectly treated as different inputs. -/
lemma fixed_law_indexed [Fintype X] (s : Configuration k X) (c D : ℝ)
    (hfinite : ∀ H : ℕ, ∀ q : (Fin H → X) → ℝ,
      (∀ v,0 ≤ q v) → (∑ v,q v=1) → ∃ A : Policy k X, StronglyLazy s A ∧
        (∑ v,q v*expectedCost A s (List.ofFn v))  ≤ 
          c*(∑ v,q v*optimalCost s (List.ofFn v))+D)
    (σ : Ω → List X) (w : Ω → ℝ) (hw : ∀ ω,0 ≤ w ω) (hsum : ∑ ω,w ω=1)
    (H : ℕ) (hH : ∀ ω,(σ ω).length=H) :
    ∃ A : Policy k X, StronglyLazy s A ∧
      (∑ ω,w ω*expectedCost A s (σ ω))  ≤  c*(∑ ω,w ω*optimalCost s (σ ω))+D := by
  let f : Ω → (Fin H → X) := fun ω i=>(σ ω).get (Fin.cast (hH ω).symm i)
  have hf (ω : Ω) : List.ofFn (f ω)=σ ω := by
    apply List.ext_getElem (by simpa using (hH ω).symm)
    intro n hn hn'
    simp [f]
  obtain ⟨A,hA,hb⟩ := hfinite H (pushWeights f w)
    (pushWeights_nonneg f w hw) (pushWeights_sum f w hsum)
  rw [pushWeights_expectation,pushWeights_expectation] at hb
  simp only [hf] at hb
  exact ⟨A,hA,hb⟩

/-- Removing a fixed additive term by arbitrarily many repetitions. This
argument includes the zero-optimum case without assuming a positive Q. -/
lemma remove_additive (m q D : ℝ) (h : ∀ N : ℕ, (N : ℝ)*m ≤ (N : ℝ)*q+D) : m ≤ q := by
  by_contra hmq
  have hp : 0 < m-q := sub_pos.mpr (lt_of_not_ge hmq)
  obtain ⟨N,hN⟩ := exists_nat_gt (D/(m-q))
  have hmul : D<(N : ℝ)*(m-q) := (div_lt_iff₀ hp).mp hN
  have hb := h N
  nlinarith

/-- Episode amplification transfers the finite-law estimate to a horizon-uniform competitive bound. -/


theorem amplification_of_uniform_finite_law [Fintype X]
    (s : Configuration k X) (hs : Function.Injective s) (hne : ∃ x y : X,x≠y)
    (c D : ℝ) (hc : 0 ≤ c)
    (hfinite : ∀ H : ℕ, ∀ q : (Fin H → X) → ℝ,
      (∀ v,0 ≤ q v) → (∑ v,q v=1) → ∃ A : Policy k X, StronglyLazy s A ∧
        (∑ v,q v*expectedCost A s (List.ofFn v))  ≤ 
          c*(∑ v,q v*optimalCost s (List.ofFn v))+D)
    (σ : Ω → List X) (w : Ω → ℝ) (hw : ∀ ω,0 ≤ w ω) (hsum : ∑ ω,w ω=1) :
    ∃ P : Policy k X, (∑ ω,w ω*expectedCost P s (σ ω))  ≤ 
      2*c*(∑ ω,w ω*optimalCost s (σ ω)) := by
  obtain ⟨P,hP⟩ := law_minimum s σ w
  let m := ∑ ω,w ω*expectedCost P s (σ ω)
  let Q := ∑ ω,w ω*optimalCost s (σ ω)
  obtain ⟨R,hR,hreset⟩ := expected_reset s hs hne
  obtain ⟨L,ρ,t,ht⟩ := closed_padded_episodes s σ R
  let ep : Ω → List X := fun ω=>(t ω).map Prod.fst
  have hep : ep=(fun ω=>σ ω++ρ ω++(List.replicate R (List.ofFn s)).flatten) :=
    funext fun ω=>(ht ω).1
  have hlen (ω : Ω) : (ep ω).length=L := by
    simp only [ep,List.length_map,(ht ω).2.2.2]
  have hcN : ∀ N : ℕ, (N : ℝ)*m  ≤  (N : ℝ)*(2*c*Q)+D := by
    intro N
    obtain ⟨A,hA,hcost⟩ := fixed_law_indexed s c D hfinite (iidWord ep N)
      (iidWeight w N) (iidWeight_nonneg w hw N) (iidWeight_sum w hsum N)
      (N*L) (iidWord_length ep L hlen N)
    have hupper := iid_offline s σ t (fun ω=>(ht ω).2.1) (fun ω=>(ht ω).2.2.1) w hw hsum N
    have hc' := hcost.trans (add_le_add (mul_le_mul_of_nonneg_left hupper hc) le_rfl)
    have hstep := episode_step A s w hw hsum σ ρ
      ((List.replicate R (List.ofFn s)).flatten) m hP (hreset A hA)
    rw [←hep] at hstep
    have hlower := episode_telescope A s w hw hsum ep m hstep N []
    rw [Episode.configurationAfter_nil,matching_self,zero_add,runCost_iid A s w hsum] at hlower
    have hid (v : Fin N → Ω) : cost A s [] (iidWord ep N v)=expectedCost A s (iidWord ep N v) := rfl
    simp only [hid] at hlower
    change (N : ℝ)*m  ≤  _ at hlower
    dsimp [Q]
    nlinarith
  exact ⟨P,remove_additive m (2*c*Q) D hcN⟩

end
end Amplification
end KServer

namespace KServer
noncomputable section
open Finset
universe u


/-- The finite-law estimate implies the arbitrary-metric competitive bound
through closed-episode amplification and product compactness. -/
theorem finite_law_suffices_for_main : FiniteLawStatement.{u} → ReductionStatement.{u} := by
  intro h
  obtain ⟨a,ha⟩ := h
  apply main_reduction
  refine ⟨2*max a 0,mul_nonneg (by norm_num) (le_max_right _ _),?_⟩
  intro k hk Y _ _ s hs Ω _ σ w hw hsum
  let : NeZero k := ⟨by omega⟩
  have hne : ∃ x y : Y, x≠y := by
    refine ⟨s ⟨0,by omega⟩,s ⟨1,by omega⟩,?_⟩
    intro he
    have hi := congrArg Fin.val (hs he)
    exact Nat.zero_ne_one hi
  obtain ⟨D,hD,hF⟩ := ha Y inferInstance inferInstance hne k hk s
  let c := max a 0*(1+Real.log (k+1))^2
  have hc : 0 ≤ c := mul_nonneg (le_max_right _ _) (sq_nonneg _)
  have hfinite : ∀ H : ℕ, ∀ q : (Fin H → Y) → ℝ,
      (∀ v,0 ≤ q v) → (∑ v,q v=1) → ∃ A : Policy k Y, StronglyLazy s A ∧
        (∑ v,q v*expectedCost A s (List.ofFn v)) ≤
          c*(∑ v,q v*optimalCost s (List.ofFn v))+D := by
    intro H q hq hqsum
    obtain ⟨A,hA,hb⟩ := hF H ⟨q,hq,hqsum⟩
    refine ⟨A,hA,hb.trans ?_⟩
    refine add_le_add ?_ le_rfl
    apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    · exact sum_nonneg fun v _=>mul_nonneg (hq v) (optimalCost_nonneg s _)
  obtain ⟨P,hP⟩ := Amplification.amplification_of_uniform_finite_law
    s hs hne c D hc hfinite σ w hw hsum
  refine ⟨P,hP.trans_eq ?_⟩
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro ω _
  dsimp [c]
  ring

end
end KServer

end

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

omit [Fintype Y] in
lemma optimalTrace_cost (s : Configuration k Y) (σ : Fin H → Y) :
    traceCost s (optimalTrace s σ)=optimalCost s (List.ofFn σ) := by
  rw [optimalTrace,serviceTrace_cost]
  exact (optimalCost_attained s (List.ofFn σ)).choose_spec

omit [Fintype Y] in
lemma optimalTrace_get_request (s : Configuration k Y) (σ : Fin H → Y) (t : Fin H) :
    ((optimalTrace s σ)[t.val]'(by rw [optimalTrace_length]; exact t.isLt)).1=σ t := by
  have he := congrArg (fun l : List Y => l[t.val]?) (optimalTrace_requests s σ)
  apply Option.some.inj
  simpa only [List.getElem?_map,List.getElem?_eq_getElem
    (show t.val<(optimalTrace s σ).length by rw [optimalTrace_length]; exact t.isLt),
    Option.map_some,List.getElem?_ofFn,Fin.isLt,dite_eq_left] using he

omit [Fintype Y] in
lemma hidden_step (s : Configuration k Y) (σ : Fin H → Y) (t : Fin H) :
    hidden s σ (t.val+1)=serve (hidden s σ t.val) (mover s σ t) (σ t) := by
  have ht : t.val<(optimalTrace s σ).length := by rw [optimalTrace_length]; exact t.isLt
  rw [hidden,List.take_succ_eq_append_getElem ht,configurationAfter_append]
  simp only [configurationAfter]
  rw [optimalTrace_get_request]
  rfl

omit [Fintype Y] in
lemma hidden_covers (s : Configuration k Y) (σ : Fin H → Y) (t : Fin H) :
    hidden s σ (t.val+1) (mover s σ t)=σ t := by
  rw [hidden_step]
  simp [serve]

omit [MetricSpace Y] [Fintype Y] in
lemma prefix_request {σ ρ : Fin H → Y} (t : Fin H)
    (h : requestPrefix σ (t.val+1)=requestPrefix ρ (t.val+1)) : σ t=ρ t := by
  have he := congrFun h t
  simpa [requestPrefix] using he

variable {T : Type v} [Fintype T]

omit [MetricSpace Y] in
lemma weight_nonneg (law : FiniteDistribution (Fin H → Y)) (tape : FiniteDistribution T)
    (ω : (Fin H → Y) × T) : 0≤weight law tape ω :=
  mul_nonneg (law.property.1 _) (tape.property.1 _)

omit [MetricSpace Y] in
lemma weight_sum (law : FiniteDistribution (Fin H → Y)) (tape : FiniteDistribution T) :
    ∑ ω,weight law tape ω=1 := by
  simp only [weight,Fintype.sum_prod_type,←mul_sum,tape.property.2,mul_one,law.property.2]


omit [Fintype Y] in
lemma hidden_movement (s : Configuration k Y) (σ : Fin H → Y) (t : Fin H) :
    (∑ i,dist (hidden s σ t.val i) (hidden s σ (t.val+1) i))=
      dist (hidden s σ t.val (mover s σ t)) (σ t) := by
  classical
  rw [hidden_step]
  simp [serve,Function.update_apply,apply_ite]

omit [Fintype Y] in
lemma hidden_total_cost (s : Configuration k Y) (σ : Fin H → Y) :
    (∑ t : Fin H,∑ i,dist (hidden s σ t.val i) (hidden s σ (t.val+1) i))=
      optimalCost s (List.ofFn σ) := by
  have he (n : ℕ) (hn : n≤H) :
      traceCost s ((optimalTrace s σ).take n)=
        ∑ t ∈ range n,∑ i,dist (hidden s σ t i) (hidden s σ (t+1) i) := by
    induction n with
    | zero => simp [traceCost]
    | succ n ih =>
      have hlt : n<(optimalTrace s σ).length := by rw [optimalTrace_length]; omega
      rw [List.take_succ_eq_append_getElem hlt,traceCost_append,ih (by omega),sum_range_succ]
      congr 1
      rw [hidden_movement s σ ⟨n,by omega⟩]
      simp only [traceCost,add_zero]
      rw [optimalTrace_get_request s σ ⟨n,by omega⟩]
      rfl
  have htake : (optimalTrace s σ).take H=optimalTrace s σ := by
    apply List.take_of_length_le
    exact (optimalTrace_length s σ).le
  rw [←optimalTrace_cost,←htake,he H le_rfl]
  exact (Finset.sum_range (fun t : ℕ => ∑ i,
    dist (hidden s σ t i) (hidden s σ (t+1) i))).symm

lemma expected_hidden_cost (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (tape : FiniteDistribution T) :
    (∑ ω,weight law tape ω*(∑ t : Fin H,∑ i,
      dist (hidden s ω.1 t.val i) (hidden s ω.1 (t.val+1) i)))=
        ∑ σ,law.val σ*optimalCost s (List.ofFn σ) := by
  simp only [hidden_total_cost,weight,Fintype.sum_prod_type]
  simp_rw [mul_right_comm (law.val _) (tape.val _),←mul_sum,tape.property.2,mul_one]

omit [MetricSpace Y] in
lemma requestHistory_eq_iff (t : ℕ) (σ ρ : Fin H → Y) :
    requestHistory t σ=requestHistory t ρ ↔ requestPrefix σ t=requestPrefix ρ t := by
  unfold requestHistory
  rw [Fin.val_inj,(Fintype.equivFin _).injective.eq_iff]

omit [MetricSpace Y] in
lemma mass_product (law : FiniteDistribution (Fin H → Y)) (tape : FiniteDistribution T)
    (t : ℕ) (ω : (Fin H → Y) × T) :
    mass (weight law tape) (history t) (history t ω)=
      mass law.val (requestHistory t) (requestHistory t ω.1)*tape.val ω.2 := by
  classical
  simp only [mass,fiber,sum_filter,history_eq_iff,requestHistory_eq_iff,
    Fintype.sum_prod_type,weight]
  rw [sum_mul]
  apply sum_congr rfl
  intro σ _
  by_cases hp : requestPrefix σ t=requestPrefix ω.1 t
  · simp [hp]
  · simp [hp]

omit [MetricSpace Y] in
lemma numerator_product (law : FiniteDistribution (Fin H → Y)) (tape : FiniteDistribution T)
    (t : ℕ) (ω : (Fin H → Y) × T) (f : (Fin H → Y) → ℝ) :
    numerator (weight law tape) (history t) (fun z => f z.1) (history t ω)=
      numerator law.val (requestHistory t) f (requestHistory t ω.1)*tape.val ω.2 := by
  classical
  simp only [numerator,fiber,sum_filter,history_eq_iff,requestHistory_eq_iff,
    Fintype.sum_prod_type,weight]
  rw [sum_mul]
  apply sum_congr rfl
  intro σ _
  by_cases hp : requestPrefix σ t=requestPrefix ω.1 t
  · simp [hp]; ring
  · simp [hp]

omit [MetricSpace Y] in
/-- The precise independence statement legitimately used by the manuscript.
It does not assert independence of partition events after conditioning on the
tape, nor does it select reset events in a martingale estimate. -/
lemma posterior_tape_irrelevant (law : FiniteDistribution (Fin H → Y))
    (tape : FiniteDistribution T) (t : ℕ) (ω : (Fin H → Y) × T)
    (ht : tape.val ω.2≠0) (f : (Fin H → Y) → ℝ) :
    posterior (weight law tape) (history t) (fun z => f z.1) ω=
      posterior law.val (requestHistory t) f ω.1 := by
  simp only [posterior,numerator_product,mass_product]
  exact mul_div_mul_right _ _ ht

omit [MetricSpace Y] [Fintype Y] [NeZero k] in
lemma metricCount_nonneg (c : Configuration k Y) (y : Y) : 0 ≤ metricCount c y := by
  classical
  exact sum_nonneg fun i _ => by split_ifs <;> norm_num

omit [MetricSpace Y] [Fintype Y] [NeZero k] in
lemma metricCount_at (c : Configuration k Y) (y : Y) (h : ∃ i,c i=y) :
    1 ≤ metricCount c y := by
  classical
  obtain ⟨i,hi⟩ := h
  have hs := single_le_sum (s := (univ : Finset (Fin k))) (f := fun j =>
    if c j=y then (1:ℝ) else 0) (fun j _ => by split_ifs <;> norm_num) (mem_univ i)
  simpa [hi,metricCount] using hs

lemma mu_nonneg (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (t : ℕ) (σ : Fin H → Y) (y : Y) : 0 ≤ mu s law t σ y :=
  posterior_nonneg law.property.1 _ (fun _ => metricCount_nonneg _ _) _

omit [MetricSpace Y] in
lemma request_of_history (t : Fin H) (σ ρ : Fin H → Y)
    (h : requestHistory (t.val+1) σ=requestHistory (t.val+1) ρ) : σ t=ρ t := by
  have he := congrFun ((requestHistory_eq_iff _ _ _).mp h) t
  simpa [requestPrefix,t.isLt] using he

lemma mu_served (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (t : Fin H) (σ : Fin H → Y) (hσ : 0<law.val σ) : 1 ≤ mu s law (t.val+1) σ (σ t) := by
  have hc : posterior law.val (requestHistory (t.val+1)) (fun _ => (1:ℝ)) σ=1 :=
    posterior_fiber_const σ (fun _ _ => rfl) (mass_pos_of_weight law.property.1 _ σ hσ).ne'
  rw [←hc]
  apply posterior_mono_fiber law.property.1
  intro ρ hρ
  apply metricCount_at
  rw [←request_of_history t ρ σ hρ]
  exact ⟨mover s ρ t,hidden_covers s ρ t⟩

lemma mu_adapted (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (t : ℕ) (y : Y) : RankTracking.Adapted (requestHistory t) (fun σ => mu s law t σ y) :=
  posterior_adapted _ _ _

end KServer.FiniteExperiment

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Potential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Deterministic heavy-center schedule and its clipped distance profile.
Random heavy radii do not affect this schedule. -/

noncomputable section
open scoped BigOperators Classical
open Finset Set


/-! Exact scale summations for pilot drift and the partition budget.
No policy or drift estimate is assumed. -/
noncomputable section
open scoped BigOperators Classical
open Finset

namespace KServer.Pilot
open Finset
variable {Y : Type*} [Fintype Y] [MetricSpace Y]

lemma ball_mono {x : Y} {r s : ℝ} (h : r ≤ s) : ball x r ⊆ ball x s := by
  intro y hy
  exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hy).2.trans h⟩

omit [Fintype Y] [MetricSpace Y] in
lemma mass_mono {μ : Y → ℝ} (hμ : ∀ y, 0 ≤ μ y) {A B : Finset Y} (h : A ⊆ B) :
    mass μ A ≤ mass μ B := sum_le_sum_of_subset_of_nonneg h (fun i _ _ => hμ i)

end KServer.Pilot

end
end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Partitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Finset Set

namespace KServer.FiniteExperiment
open RankTracking PosteriorRanks Pilot
attribute [local instance] Classical.propDecidable
variable {Y : Type*} [MetricSpace Y] [Fintype Y]
variable {k H : ℕ} [NeZero k]

omit [MetricSpace Y] in
lemma requestHistory_refines (t : ℕ) (σ ρ : Fin H → Y)
    (h : requestHistory (t+1) σ = requestHistory (t+1) ρ) :
    requestHistory t σ = requestHistory t ρ := by
  apply (requestHistory_eq_iff t σ ρ).mpr
  funext i
  have hh := congrFun ((requestHistory_eq_iff (t+1) σ ρ).mp h) i
  unfold requestPrefix at *
  by_cases hi : i.val < t
  · simpa [hi, show i.val < t+1 by omega] using hh
  · simp [hi]

end KServer.FiniteExperiment

end


/-! The actual true-prefix heavy-center recursion of §07. All physical and
filtering steps are included in its potential budget, not only edit steps. -/
noncomputable section
open scoped BigOperators
open Finset Set
namespace KServer.HeavyCenters
open Pilot FiniteExperiment RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable
variable {Y : Type*} [MetricSpace Y] [Fintype Y]
variable {k H : ℕ} [NeZero k]

lemma step_separated (r γ δ : ℝ) (C : Finset Y) (μ : Y → ℝ) (x : Y)
    (hC : (C : Set Y).Pairwise (fun a b => 100*r<dist a b)) :
    ((step r γ δ C μ x : Finset Y) : Set Y).Pairwise (fun a b => 100*r<dist a b) := by
  unfold step
  split_ifs
  · intro a ha b hb hab
    rcases mem_insert.mp ha with rfl | ha
    · rcases mem_insert.mp hb with rfl | hb
      · exact (hab rfl).elim
      · have hd := (mem_filter.mp hb).2
        simpa only [dist_comm] using hd
    · rcases mem_insert.mp hb with rfl | hb
      · exact (mem_filter.mp ha).2
      · exact hC (mem_filter.mp ha).1 (mem_filter.mp hb).1 hab
  · exact hC

lemma centers_succ (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (r γ δ : ℝ) (σ : Fin H → Y) (t : Fin H) :
    centers s law r γ δ σ (t.val+1)=
      step r γ δ (centers s law r γ δ σ t.val) (mu s law (t.val+1) σ) (σ t) := by
  simp only [centers,t.isLt,↓reduceDIte]

lemma centers_separated (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (r γ δ : ℝ) (σ : Fin H → Y) (t : ℕ) :
    ((centers s law r γ δ σ t : Finset Y) : Set Y).Pairwise (fun a b => 100*r<dist a b) := by
  induction t with
  | zero => simp [centers]
  | succ t ih =>
    rw [centers]
    split_ifs
    · exact step_separated r γ δ _ _ _ ih
    · exact ih

lemma centers_adapted (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (r γ δ : ℝ) (t : ℕ) :
    ∀ σ ρ,requestHistory t σ=requestHistory t ρ →
      centers s law r γ δ σ t=centers s law r γ δ ρ t := by
  induction t with
  | zero => intros; rfl
  | succ t ih =>
    intro σ ρ h
    have hc := ih σ ρ (requestHistory_refines t σ ρ h)
    have hμ : mu s law (t+1) σ=mu s law (t+1) ρ :=
      funext (fun y => mu_adapted s law (t+1) y σ ρ h)
    simp only [centers]
    split_ifs with ht
    · rw [hc,hμ,request_of_history ⟨t,ht⟩ σ ρ h]
    · exact hc

end KServer.HeavyCenters

end


/-! Fixed labels with a cooldown are constructed by finite online coloring.
A conflict set is a deterministic collection of previously reserved records;
labels are never used as random-tape indices. This is the finite pool mechanism
of §07, not a growing historical alphabet. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.OnlineLabels

variable {M : ℕ}

lemma stage_step_old (hM : 0<M) (conflict : ℕ → Finset ℕ)
    (hcard : ∀ t, (conflict t).card<M) {i t : ℕ} (hi : i≠t) :
    stage hM conflict hcard (t+1) i=stage hM conflict hcard t i := by
  simp [stage,hi]

lemma stage_stable (hM : 0<M) (conflict : ℕ → Finset ℕ)
    (hcard : ∀ t, (conflict t).card<M) {i t : ℕ} (hi : i<t) :
    stage hM conflict hcard t i=stage hM conflict hcard (i+1) i := by
  induction t with
  | zero => omega
  | succ t ih =>
      by_cases hit : i=t
      · subst i; rfl
      · rw [stage_step_old hM conflict hcard hit,ih (by omega)]

lemma color_avoids (hM : 0<M) (conflict : ℕ → Finset ℕ)
    (hcard : ∀ t, (conflict t).card<M)
    (hbefore : ∀ t, ∀ j ∈ conflict t, j<t) (t : ℕ) {j : ℕ}
    (hj : j ∈ conflict t) : color hM conflict hcard t≠color hM conflict hcard j := by
  have hi := (unused_exists (conflict t) (stage hM conflict hcard t) (hcard t)).choose_spec j hj
  rw [stage_stable hM conflict hcard (hbefore t j hj)] at hi
  simpa [color,stage] using Ne.symm hi

/-- If each simultaneous or cooldown pair was included when the later record
was inserted, the fixed pool colors it injectively. This local premise is on
record geometry, not an assumed random algorithm or cost estimate. -/
theorem color_injective_on (hM : 0<M) (conflict : ℕ → Finset ℕ)
    (hcard : ∀ t, (conflict t).card<M)
    (hbefore : ∀ t, ∀ j ∈ conflict t, j<t) (S : Set ℕ)
    (hpairs : ∀ i ∈ S, ∀ j ∈ S, j < i → j ∈ conflict i) :
    Set.InjOn (color hM conflict hcard) S := by
  intro i hi j hj he
  rcases lt_trichotomy i j with hij | hij | hij
  · exact False.elim (color_avoids hM conflict hcard hbefore j (hpairs j hj i hi hij) he.symm)
  · exact hij
  · exact False.elim (color_avoids hM conflict hcard hbefore i (hpairs i hi j hj hij) he)

end KServer.OnlineLabels

end


/-! Actual finite heavy-ball label update. Intersections in the finite metric
force reuse; otherwise the new label avoids both current and previous labels.
No region, anchor or label lifetime is assumed. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HeavyLabels
open HeavyCenters
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y : Type*} [MetricSpace Y] [Fintype Y]

lemma overlap_distance {C : Finset Y} {rad : Y → ℝ} {x a : Y} {r R : ℝ}
    (hrad : ∀ a∈C,rad a≤20*r) (hR : R≤20*r) (ha : a∈overlap C rad x R) :
    dist a x≤40*r := by
  obtain ⟨ha,p,hp,hx⟩ := mem_filter.mp ha
  have ht:=dist_triangle a p x
  rw [dist_comm p x] at ht
  linarith [hrad a ha]

omit [MetricSpace Y] in
lemma fresh_avoids (C D : Finset Y) (label prev : Y → Pool Y) :
    fresh C D label prev∉C.image label ∧ fresh C D label prev∉D.image prev :=
  (unused C D label prev).choose_spec

lemma existing_match {C D : Finset Y} {rad : Y → ℝ} {label prev : Y → Pool Y} {x a : Y} {R : ℝ}
    (hl : Set.InjOn label (C:Set Y)) (ha : a∈C)
    (he : insertedLabel C D rad label prev x R=label a) : a∈overlap C rad x R := by
  unfold insertedLabel at he
  split_ifs at he with h
  · have heq:=hl (mem_filter.mp h.choose_spec).1 ha he
    exact heq ▸ h.choose_spec
  · exact False.elim ((fresh_avoids C D label prev).1 (mem_image.mpr ⟨a,ha,he.symm⟩))

lemma inserted_diff_kept {C D : Finset Y} {rad : Y → ℝ} {label prev : Y → Pool Y} {x a : Y} {r R : ℝ}
    (hr : 0 < r) (hrad : ∀ a∈C,rad a≤20*r) (hR : R≤20*r)
    (hl : Set.InjOn label (C:Set Y)) (ha : a∈C) (hd : 100*r<dist a x) :
    insertedLabel C D rad label prev x R≠label a := by
  intro he
  have hh:=overlap_distance hrad hR (existing_match hl ha he)
  linarith

/-- An actual update preserves injective active heavy labels. -/
lemma update_injective {C D : Finset Y} {rad : Y → ℝ} {label prev : Y → Pool Y} {x : Y} {r R : ℝ}
    (hr : 0 < r) (hrad : ∀ a∈C,rad a≤20*r) (hR : R≤20*r)
    (hl : Set.InjOn label (C:Set Y)) :
    Set.InjOn (updatedLabel C D rad label prev x R) (replace r C x:Set Y) := by
  intro a ha b hb he
  rcases mem_insert.mp ha with hax|ha
  · subst a
    rcases mem_insert.mp hb with hbx|hb
    · exact hbx.symm
    · have hbx : b≠x := by
        intro hh; have hd:=(mem_filter.mp hb).2; simp only [hh,dist_self] at hd; linarith
      simp only [updatedLabel,Function.update_self,Function.update_of_ne hbx] at he
      exact False.elim (inserted_diff_kept hr hrad hR hl (mem_filter.mp hb).1 (mem_filter.mp hb).2 he)
  · rcases mem_insert.mp hb with hbx|hb
    · subst b
      have hax : a≠x := by
        intro hh; have hd:=(mem_filter.mp ha).2; simp only [hh,dist_self] at hd; linarith
      simp only [updatedLabel,Function.update_self,Function.update_of_ne hax] at he
      exact False.elim (inserted_diff_kept hr hrad hR hl (mem_filter.mp ha).1 (mem_filter.mp ha).2 he.symm)
    · have hax : a≠x := by
        intro hh; have hd:=(mem_filter.mp ha).2; simp only [hh,dist_self] at hd; linarith
      have hbx : b≠x := by
        intro hh; have hd:=(mem_filter.mp hb).2; simp only [hh,dist_self] at hd; linarith
      simp only [updatedLabel,Function.update_of_ne hax,Function.update_of_ne hbx] at he
      exact hl (mem_filter.mp ha).1 (mem_filter.mp hb).1 he

end KServer.HeavyLabels

end


/-! Exact truncated exponential tails and first-hit cancellation used by the
chronological finite-law partition construction, manuscript §07.  The radius
law is not replaced by a uniform/padded law: `tail` is its exact tail. -/


/-! Finite inverse-tail sampling for the chronological tape. It applies both
to retirement ages and to the finitely many observable radius thresholds. -/


/-! Finite discretization of the manuscript's truncated exponential radius.
All pairwise-distance decisions are included in a finite ordered grid; its
literal tail law yields a finite tape, without invoking assumed independence. -/


/-! Finite realization of the uniform heavy-ball radii. The finite grid
preserves every relevant metric threshold, hence its law is exact for balls. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.FiniteUniform
open FiniteRadius FiniteSurvival
attribute [local instance] Classical.propDecidable Classical.decEq

variable {Y : Type*} [Fintype Y] [PseudoMetricSpace Y]
lemma radius_range {r : ℝ} (hr : 0 < r) (i : Outcome Y r) : radius r i∈Set.Icc (16*r) (20*r) := by
  have hh:=point_range (thresholds (Y:=Y) r) hr i
  dsimp [radius]; constructor <;> linarith [hh.1,hh.2]
end KServer.FiniteUniform

end


/-! The literal causal heavy-ball radii/labels recursion on the constructed
finite tape. The center schedule is the actual true-prefix pilot schedule. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HeavySchedule
open HeavyCenters HeavyLabels FiniteExperiment
attribute [local instance] Classical.propDecidable
variable {Y : Type*} [MetricSpace Y] [Fintype Y]
variable {k H : ℕ} [NeZero k]

lemma run_valid (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    {r : ℝ} (hr : 0 < r) (γ δ : ℝ) (σ : Fin H → Y) (tape : Fin H → FiniteUniform.Outcome Y r)
    (t : ℕ) :
    (∀ a∈centers s law r γ δ σ t,(run s law r γ δ σ tape t).rad a∈Set.Icc (16*r) (20*r)) ∧
    Set.InjOn (run s law r γ δ σ tape t).label (centers s law r γ δ σ t:Set Y) := by
  induction t with
  | zero => simp [centers,Set.InjOn]
  | succ t ih =>
    rw [run,centers]
    dsimp only
    simp only [HeavyCenters.step]
    split_ifs with ht ha
    · constructor
      · intro a haC
        rcases mem_insert.mp haC with hax|haC
        · subst a
          simpa only [Function.update_self] using FiniteUniform.radius_range hr (tape ⟨t,ht⟩)
        · have hax : a≠σ ⟨t,ht⟩ := by
            intro he
            have hd:=(mem_filter.mp haC).2
            rw [he,dist_self] at hd
            linarith
          simp only [Function.update_of_ne hax]
          exact ih.1 a (mem_filter.mp haC).1
      · have hv := update_injective (D := centers s law r γ δ σ (t-1))
          (prev := (run s law r γ δ σ tape t).previous) (x := σ ⟨t,ht⟩)
          hr (fun a ha=>(ih.1 a ha).2) (FiniteUniform.radius_range hr (tape ⟨t,ht⟩)).2 ih.2
        exact hv
    · exact ih
    · exact ih

end KServer.HeavySchedule

end


/-! Exact finite ball laws for the metric thresholds used in §07.  Their
chronological first-hit estimate uses the constructed product law, not an
independence premise about a posterior filtration. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.FiniteBallLaw
open PartitionProbabilities FiniteRadius
attribute [local instance] Classical.propDecidable Classical.decEq

variable {Y : Type*} [Fintype Y] [PseudoMetricSpace Y]

lemma radius_range {r : ℝ} (hr : 0 < r) (i : Outcome Y r) : radius r i ∈ Set.Icc r (2*r) :=
  point_range _ hr i

end KServer.FiniteBallLaw

end


/- Chronological rosters retain insertion times rather than surviving random balls. The tests are independent of the partition tape, and young records reserve slots. -/


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.Chronological

variable {Y : Type*} [MetricSpace Y]

lemma schedule_before (request : ℕ → Y) (r : ℝ) (K : ℕ) (qualifies : ℕ → Prop)
    (t : ℕ) : ∀ i ∈ schedule request r K qualifies t, i < t := by
  classical
  induction t with
  | zero => simp [schedule]
  | succ t ih =>
      intro i hi
      simp only [schedule] at hi
      split_ifs at hi with h
      · rcases mem_insert.mp hi with rfl | hi
        · omega
        · exact (ih i hi).trans (Nat.lt_succ_self t)
      · exact (ih i hi).trans (Nat.lt_succ_self t)

end KServer.Chronological

end


/-! The distinct actual and auxiliary lifetimes of §07.  These estimates are
uniform in the horizon and in every fixed chronological insertion schedule.
Compulsory-retirement tails are unconditional, as required by the source. -/


/-! Literal actual roster lifetime tape, separate from the auxiliary short
roster.  Every construction below is finite at the prescribed horizon. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualRoster
open RosterLifetimes FiniteSurvival Chronological FiniteBallLaw PartitionProbabilities
attribute [local instance] Classical.propDecidable Classical.decEq

lemma alive_young {K a : ℕ} {d : Lifetime K} (h : alive K a d) : a<K^2 := by
  rcases h with h|h
  · have hk : K ≤ K^2 := by nlinarith [Nat.zero_le K]
    exact h.trans_le hk
  · exact h.trans_lt d.isLt

variable {Y : Type*} [MetricSpace Y] {H K : ℕ}

lemma present_young (center : ℕ → Y) (I : Finset ℕ) (r : ℝ) (tape : Fin H → Lifetime K) (i : Fin H)
    (hp : present center I r tape i) : (i:ℕ)∈I ∧ age center I (20*r) i<K^2 :=
  ⟨hp.1,alive_young hp.2⟩

section Radius
variable [Fintype Y]

lemma first_some_iff (center : ℕ → Y) (I : Finset ℕ) (r : ℝ) (life : Fin H → Lifetime K)
    (radii : Fin H → Outcome Y r) (x : Y) (i : Fin H) :
    first center I r life radii x=some i ↔
      covered center I r life radii x i ∧ ∀ j < i,¬covered center I r life radii x j := by
  dsimp only [first]
  split_ifs with h
  · constructor
    · intro he
      have hi : (univ.filter (covered center I r life radii x)).min' h=i := Option.some.inj he
      constructor
      · rw [←hi]
        exact (mem_filter.mp (min'_mem _ _)).2
      · intro j hj hc
        have hmin := min'_le (univ.filter (covered center I r life radii x)) j (mem_filter.mpr ⟨mem_univ _,hc⟩)
        rw [hi] at hmin
        exact (not_le_of_gt hj) hmin
    · rintro ⟨hi,hbefore⟩
      congr 1
      apply le_antisymm
      · exact min'_le _ _ (mem_filter.mpr ⟨mem_univ _,hi⟩)
      · by_contra hh
        exact hbefore _ (lt_of_not_ge hh) (mem_filter.mp (min'_mem _ _)).2
  · constructor
    · simp
    · intro hi
      exact False.elim (h ⟨i,mem_filter.mpr ⟨mem_univ _,hi.1⟩⟩)

end Radius
end KServer.ActualRoster

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Rosters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! Heavy keys of the constructed finite schedule and their exact full-input
spatial estimate; label reuse does not impose or assume a probability law. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HeavyKeys
open HeavyCenters HeavySchedule HeavyLabels FiniteExperiment PartitionProbabilities
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y : Type*} [MetricSpace Y]

lemma hit_unique {r : ℝ} (hr : 0 < r) {C : Finset Y} {rad : Y → ℝ} {x a b : Y}
    (hC : (C:Set Y).Pairwise (fun a b=>100*r<dist a b))
    (hrad : ∀ a∈C,rad a≤20*r) (ha : a∈hits C rad x) (hb : b∈hits C rad x) : a=b := by
  by_contra hn
  obtain ⟨ha,hax⟩:=mem_filter.mp ha
  obtain ⟨hb,hbx⟩:=mem_filter.mp hb
  have hd:=hC ha hb hn
  have ht:=dist_triangle a x b
  rw [dist_comm x b] at ht
  linarith [hrad a ha,hrad b hb]

lemma centerKey_some {r : ℝ} (hr : 0 < r) {C : Finset Y} {rad : Y → ℝ} {x a : Y}
    (hC : (C:Set Y).Pairwise (fun a b=>100*r<dist a b))
    (hrad : ∀ a∈C,rad a≤20*r) :
    centerKey C rad x=some a ↔ a∈C ∧ dist a x ≤ rad a := by
  unfold centerKey
  split_ifs with h
  · constructor
    · intro he
      have he':=Option.some.inj he
      rw [←he']
      exact mem_filter.mp h.choose_spec
    · intro ha
      rw [hit_unique hr hC hrad h.choose_spec (mem_filter.mpr ha)]
  · simp only [false_iff,not_and]
    intro ha hx
    exact h ⟨a,mem_filter.mpr ⟨ha,hx⟩⟩

end KServer.HeavyKeys

end


/-! Finite independent short-lifetime expectations used only for the pilot
profile in §07. No adaptive independence is postulated: all equalities below
are identities of finite product sums. -/


/-! The genuine deterministic expected short-roster profile in §07, on the
finite preallocated set of insertion ordinals. The auxiliary lifetimes are
not the actual partition lifetimes. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ShortRoster
open Chronological RosterLifetimes
attribute [local instance] Classical.propDecidable Classical.decEq

variable {Y : Type*} [MetricSpace Y] {H : ℕ}


lemma age_congr {request request' : ℕ → Y} {S : Finset ℕ} {r : ℝ} {i : ℕ}
    (hi : request i=request' i) (h : ∀ j∈S,request j=request' j) :
    age request S r i=age request' S r i := by
  unfold age
  congr 1
  apply filter_congr
  intro j hj
  rw [hi,h j hj]

end KServer.ShortRoster

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Tiers
attribute [-instance] _root_.OAI.KServer.JointExperiment.levelTapeFintype _root_.OAI.KServer.LevelKeys.alphabetFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/- Analytic insertion gain for the second compact pilot under the profile hypotheses. -/


/-! The actual adapted chronological tier process and its all-step compact
pilot payment. No conditional drift or unconstructed roster is postulated. -/
noncomputable section
open scoped BigOperators
open Finset Set
namespace KServer.TierProcess
open FiniteExperiment RankTracking PosteriorRanks Pilot Chronological
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y : Type*} [MetricSpace Y] [Fintype Y] [DecidableEq Y]
variable {k H : ℕ} [NeZero k]

omit [MetricSpace Y] [DecidableEq Y] in
lemma request_adapted (s : Configuration k Y) {t i : ℕ} (hi : i<t)
    (σ ρ : Fin H → Y) (hh : requestHistory t σ=requestHistory t ρ) :
    request s σ i=request s ρ i := by
  unfold request
  split_ifs with hH
  · have he:=congrFun ((requestHistory_eq_iff _ _ _).mp hh) ⟨i,hH⟩
    simpa [requestPrefix,hi] using he
  · rfl

omit [DecidableEq Y] in
lemma roster_succ (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (T : Template) (r γ h : ℝ) (K : ℕ) (σ : Fin H → Y) (t : ℕ) :
    roster s law T r γ h K σ (t+1)=
      if insertTest (request s σ) (roster s law T r γ h K σ t) r K t (qualifies s law T r γ h σ t)
      then insert t (roster s law T r γ h K σ t) else roster s law T r γ h K σ t := rfl

omit [DecidableEq Y] in
lemma roster_before (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (T : Template) (r γ h : ℝ) (K : ℕ) (σ : Fin H → Y) (t : ℕ) :
    ∀ i∈roster s law T r γ h K σ t,i<t :=
  schedule_before _ _ _ _ _

omit [DecidableEq Y] in
lemma roster_adapted (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (T : Template) (r γ h : ℝ) (K : ℕ) (t : ℕ) :
    ∀ σ ρ,requestHistory t σ=requestHistory t ρ →
      roster s law T r γ h K σ t=roster s law T r γ h K ρ t := by
  induction t with
  | zero => intros; rfl
  | succ t ih =>
    intro σ ρ hh
    have hc:=ih σ ρ (requestHistory_refines t σ ρ hh)
    have hreq : ∀ i,i<t+1 → request s σ i=request s ρ i := fun i hi=>request_adapted s hi σ ρ hh
    have hq : qualifies s law T r γ h σ t ↔ qualifies s law T r γ h ρ t := by
      have hμ : mu s law (t+1) σ=mu s law (t+1) ρ := funext (fun y=>mu_adapted s law (t+1) y σ ρ hh)
      simp only [qualifies,hμ,hreq t (by omega)]
    have ha (i : ℕ) (hi : i∈roster s law T r γ h K σ t) :
        age (request s σ) (roster s law T r γ h K σ t) (20*r) i=
        age (request s ρ) (roster s law T r γ h K σ t) (20*r) i :=
      ShortRoster.age_congr (hreq i (by have hh:=roster_before s law T r γ h K σ t i hi; omega))
        (fun j hj=>hreq j (by have hh:=roster_before s law T r γ h K σ t j hj; omega))
    have ht : insertTest (request s σ) (roster s law T r γ h K σ t) r K t (qualifies s law T r γ h σ t) ↔
        insertTest (request s ρ) (roster s law T r γ h K ρ t) r K t (qualifies s law T r γ h ρ t) := by
      unfold insertTest
      rw [←hc,hq]
      refine and_congr Iff.rfl (not_congr ?_)
      apply exists_congr
      intro i
      apply and_congr_right
      intro hi
      rw [ha i hi,hreq i (by have hh:=roster_before s law T r γ h K σ t i hi; omega),hreq t (by omega)]
    rw [roster_succ,roster_succ,ht,hc]

end KServer.TierProcess

end


/-! Fixed absolute tier parameters and the weighted insertion estimate.
The roster remains the chronological finite-law
roster, not a family satisfying a hypothetical insertion bound. -/


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.Chronological
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y : Type*} [MetricSpace Y]

lemma schedule_mem (center : ℕ → Y) (r : ℝ) (K : ℕ) (qualifies : ℕ → Prop)
    (n i : ℕ) : i∈schedule center r K qualifies n ↔
      i<n ∧ insertTest center (schedule center r K qualifies i) r K i (qualifies i) := by
  induction n with
  | zero => simp [schedule]
  | succ n ih =>
    by_cases hin : i=n
    · subst i
      have hn : n∉schedule center r K qualifies n := fun hh=>Nat.lt_irrefl _ (schedule_before _ _ _ _ _ _ hh)
      simp only [schedule]
      split_ifs with he
      · simp [he]
      · simp [he,hn]
    · simp only [schedule]
      split_ifs with h
      · rw [mem_insert,or_iff_right hin,ih]
        constructor
        · intro hh; exact ⟨by omega,hh.2⟩
        · intro hh; exact ⟨by omega,hh.2⟩
      · rw [ih]
        constructor
        · intro hh; exact ⟨by omega,hh.2⟩
        · intro hh; exact ⟨by omega,hh.2⟩

lemma schedule_mono (center : ℕ → Y) (r : ℝ) (K : ℕ) (qualifies : ℕ → Prop) :
    Monotone (schedule center r K qualifies) := by
  intro m n hmn i hi
  rw [schedule_mem] at hi ⊢
  exact ⟨hi.1.trans_le hmn,hi.2⟩

lemma age_mono_history (center : ℕ → Y) {I J : Finset ℕ} (hIJ : I⊆J) (R : ℝ) (i : ℕ) :
    age center I R i≤age center J R i := by
  apply card_le_card
  exact filter_subset_filter _ hIJ

variable [Fintype Y]

omit [Fintype Y] in
lemma reserved_before (center : ℕ → Y) (r : ℝ) (K : ℕ) (qualifies : ℕ → Prop) (t i : ℕ)
    (hi : i∈reserved center r K qualifies t) : i<t :=
  schedule_before _ _ _ _ _ _ ((mem_young _ _ _ _ _).mp hi).1

omit [Fintype Y] in
lemma reserved_backward (center : ℕ → Y) (r : ℝ) (K : ℕ) (qualifies : ℕ → Prop)
    {i t T : ℕ} (htT : t≤T) (hit : i<t) (hi : i∈reserved center r K qualifies T) :
    i∈reserved center r K qualifies t := by
  obtain ⟨hI,ha⟩ := (mem_young _ _ _ _ _).mp hi
  apply (mem_young _ _ _ _ _).mpr
  refine ⟨?_,(age_mono_history center (schedule_mono center r K qualifies htT) _ _).trans_lt ha⟩
  rw [schedule_mem] at hI ⊢
  exact ⟨hit,hI.2⟩

omit [Fintype Y] in
lemma conflicts_before (center : ℕ → Y) (r : ℝ) (K : ℕ) (qualifies : ℕ → Prop)
    (t i : ℕ) (hi : i∈conflicts center r K qualifies t) : i<t := by
  rcases mem_union.mp hi with hi|hi
  · exact reserved_before center r K qualifies t i hi
  · exact (reserved_before center r K qualifies (t-1) i hi).trans_le (Nat.sub_le _ _)

/-- Common labels on consecutive maps identify the same chronological record.
In particular ordinary roster anchors do not move when a label persists. -/
theorem label_injective_consecutive (center : ℕ → Y) {r : ℝ} (hr : 0 ≤ r) (K : ℕ)
    (qualifies : ℕ → Prop) (t : ℕ) :
    Set.InjOn (label center hr K qualifies)
      (↑(reserved center r K qualifies t ∪ reserved center r K qualifies (t+1)) : Set ℕ) := by
  apply OnlineLabels.color_injective_on (pool_pos K) _ (conflicts_card center hr K qualifies)
    (conflicts_before center r K qualifies)
  intro i hi j hj hji
  have hiT : i<t+1 := by
    rcases mem_union.mp hi with hi|hi
    · exact (reserved_before center r K qualifies t i hi).trans (Nat.lt_succ_self _)
    · exact reserved_before center r K qualifies (t+1) i hi
  apply mem_union_left
  rcases mem_union.mp hj with hj|hj
  · exact reserved_backward center r K qualifies (by omega) hji hj
  · exact reserved_backward center r K qualifies (by omega) hji hj

end KServer.Chronological

end


/-! Present chronological balls, permanent finite-pool labels and actual
anchors. These are literal constructed keys, not assumed partitions. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TierKeys
open Chronological ActualRoster FiniteBallLaw PartitionProbabilities
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y : Type*} [MetricSpace Y] [Fintype Y] {H K : ℕ}

lemma key_some (center : ℕ → Y) {r : ℝ} (hr : 0 ≤ r) (q : ℕ → Prop)
    (life : Fin H → Lifetime K) (rad : Fin H → Outcome Y r) (t : ℕ) (x : Y) (a : Fin (pool Y K)) :
    key center hr K q life rad t x=some a →
      ∃ i : Fin H,first center (schedule center r K q t) r life rad x=some i ∧
        Chronological.label center hr K q i=a := by
  unfold key
  cases he : first center (schedule center r K q t) r life rad x with
  | none => simp
  | some i => intro hh; exact ⟨i,rfl,Option.some.inj hh⟩

lemma first_reserved (center : ℕ → Y) (r : ℝ) (q : ℕ → Prop)
    (life : Fin H → Lifetime K) (rad : Fin H → Outcome Y r) (t : ℕ) (x : Y) {i : Fin H}
    (hi : first center (schedule center r K q t) r life rad x=some i) :
    (i:ℕ)∈reserved center r K q t := by
  have hp:=((first_some_iff _ _ _ _ _ _ _).mp hi).1.1
  exact (mem_young _ _ _ _ _).mpr (present_young center _ r life i hp)

lemma common_same_record (center : ℕ → Y) {r : ℝ} (hr : 0 ≤ r) (q : ℕ → Prop)
    (life : Fin H → Lifetime K) (rad : Fin H → Outcome Y r) (t : ℕ) (x y : Y)
    {i j : Fin H}
    (hi : first center (schedule center r K q t) r life rad x=some i)
    (hj : first center (schedule center r K q (t+1)) r life rad y=some j)
    (he : Chronological.label center hr K q i=Chronological.label center hr K q j) : i=j := by
  apply Fin.ext
  exact label_injective_consecutive center hr K q t
    (mem_union_left _ (first_reserved center r q life rad t x hi))
    (mem_union_right _ (first_reserved center r q life rad (t+1) y hj)) he

variable [Nonempty Y]

lemma anchor_record (center : ℕ → Y) {r : ℝ} (hr : 0 ≤ r) (q : ℕ → Prop)
    (t : ℕ) {i : ℕ} (hi : i∈reserved center r K q t) :
    anchor center hr K q t (Chronological.label center hr K q i)=center i := by
  have he : ∃ j∈reserved center r K q t,
      Chronological.label center hr K q j=Chronological.label center hr K q i := ⟨i,hi,rfl⟩
  rw [anchor,dite_eq_left he]
  congr 1
  exact label_injective_consecutive center hr K q t
    (mem_union_left _ he.choose_spec.1) (mem_union_left _ hi) he.choose_spec.2

lemma anchor_distance (center : ℕ → Y) {r : ℝ} (hr : 0 < r) (q : ℕ → Prop)
    (life : Fin H → Lifetime K) (rad : Fin H → Outcome Y r) (t : ℕ) (x : Y)
    {a : Fin (pool Y K)} (ha : key center hr.le K q life rad t x=some a) :
    dist (anchor center hr.le K q t a) x≤2*r := by
  obtain ⟨i,hi,hl⟩:=key_some center hr.le q life rad t x a ha
  rw [←hl,anchor_record center hr.le q t (first_reserved center r q life rad t x hi)]
  exact ((first_some_iff _ _ _ _ _ _ _).mp hi).1.2 |>.trans (radius_range hr _).2

lemma anchors_persist (center : ℕ → Y) {r : ℝ} (hr : 0 ≤ r) (q : ℕ → Prop)
    (life : Fin H → Lifetime K) (rad : Fin H → Outcome Y r) (t : ℕ) (x y : Y)
    {a : Fin (pool Y K)} (hx : key center hr K q life rad t x=some a)
    (hy : key center hr K q life rad (t+1) y=some a) :
    anchor center hr K q t a=anchor center hr K q (t+1) a := by
  obtain ⟨i,hi,hli⟩:=key_some center hr q life rad t x a hx
  obtain ⟨j,hj,hlj⟩:=key_some center hr q life rad (t+1) y a hy
  have he:=common_same_record center hr q life rad t x y hi hj (hli.trans hlj.symm)
  subst j
  rw [←hli,anchor_record center hr q t (first_reserved center r q life rad t x hi),
    anchor_record center hr q (t+1) (first_reserved center r q life rad (t+1) y hj)]

end KServer.TierKeys

end


/-! Fixed finite precedence alphabets: literal selection of the first covering
structure, with singleton fallback. This is the coordinate map in §07. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PriorityKeys
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I Y : Type*} [Fintype I] [LinearOrder I] {A : I → Type*}

lemma selected_some_of_mem (key : (i:I) → Y → Option (A i)) (x : Y)
    (h:(covered key x).Nonempty) :
    ∃ a : A ((covered key x).min' h),
      key ((covered key x).min' h) x=some a ∧
      selected key x=some ⟨(covered key x).min' h,a⟩ := by
  have hn:=(mem_filter.mp (min'_mem (covered key x) h)).2
  cases he:key ((covered key x).min' h) x with
  | none => exact False.elim (hn he)
  | some a => exact ⟨a,rfl,by simp only [selected,dite_eq_left h,he,Option.map_some]⟩

lemma selected_some (key : (i:I) → Y → Option (A i)) (x : Y)
    {z : Sigma A} (hz:selected key x=some z) :
    key z.1 x=some z.2 ∧ ∀ i<z.1,key i x=none := by
  have h:(covered key x).Nonempty:=by
    by_contra hn
    simp only [selected,dite_eq_right hn] at hz
    cases hz
  obtain ⟨a,ha,hs⟩:=selected_some_of_mem key x h
  have he: (⟨(covered key x).min' h,a⟩:Sigma A)=z:=Option.some.inj (hs.symm.trans hz)
  subst z
  refine ⟨ha,?_⟩
  intro i hi
  by_contra hn
  have hm:=min'_le (covered key x) i (mem_filter.mpr ⟨mem_univ _,hn⟩)
  exact (not_lt_of_ge hm) hi

variable [MetricSpace Y]

lemma anchor_distance (keys : (i:I) → Y → Option (A i))
    (anchors : (i:I) → A i → Y) {r:ℝ} (hr:0 ≤ r)
    (ha:∀ i x a,keys i x=some a → dist (anchors i a) x≤20*r) (x:Y) :
    dist (anchor anchors (key keys x)) x≤20*r := by
  cases he:selected keys x with
  | none => simpa only [key,he,anchor,dist_self] using mul_nonneg (by norm_num : (0:ℝ)≤20) hr
  | some z =>
    simpa only [key,he,anchor] using ha z.1 x z.2 (selected_some keys x he).1

lemma cell_diameter (keys : (i:I) → Y → Option (A i))
    (anchors : (i:I) → A i → Y) {r:ℝ} (hr:0 ≤ r)
    (ha:∀ i x a,keys i x=some a → dist (anchors i a) x≤20*r)
    {x y:Y} (he:key keys x=key keys y) : dist x y≤40*r := by
  have hx:=anchor_distance keys anchors hr ha x
  have hy:=anchor_distance keys anchors hr ha y
  rw [←he] at hy
  have ht:=dist_triangle x (anchor anchors (key keys x)) y
  rw [dist_comm x (anchor anchors (key keys x))] at ht
  linarith
end KServer.PriorityKeys

end


/-! Literal dyadic tier parameters and their logarithmic expense, §07. -/


/-! Coverage and exact tier selection for the actual posterior-driven map.
The logarithmic ratio is computed from the new true-prefix metric posterior. -/


/-! The actual finite complete level alphabet and map of §07: chronological
heavy balls precede the dyadic tiers, and singleton keys are the fallback. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.LevelKeys
open FiniteExperiment Pilot TierProcess LevelCoverage
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y : Type*} [MetricSpace Y] [Fintype Y] {k H : ℕ} [NeZero k]

lemma heavy_anchor_distance (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (tape:Fin H→FiniteUniform.Outcome Y r) (t:ℕ) (x:Y)
    (a:HeavyLabels.Pool Y) (ha:HeavyKeys.key s law r heavyGamma heavyDelta σ tape t x=some a) :
    dist (heavyAnchor s law r σ tape t a) x ≤ 20*r := by
  have hv:=HeavySchedule.run_valid s law hr heavyGamma heavyDelta σ tape t
  unfold HeavyKeys.key at ha
  cases hc:HeavyKeys.centerKey (HeavyCenters.centers s law r heavyGamma heavyDelta σ t)
    (HeavySchedule.run s law r heavyGamma heavyDelta σ tape t).rad x with
  | none => simp only [hc,Option.map_none] at ha; cases ha
  | some c =>
    simp only [hc,Option.map_some,Option.some.injEq] at ha
    have hC:=HeavyCenters.centers_separated s law r heavyGamma heavyDelta σ t
    obtain ⟨hcm,hd⟩:=(HeavyKeys.centerKey_some hr hC (fun b hb=>(hv.1 b hb).2)).mp hc
    have he:∃ b∈HeavyCenters.centers s law r heavyGamma heavyDelta σ t,
      (HeavySchedule.run s law r heavyGamma heavyDelta σ tape t).label b=a:=⟨c,hcm,ha⟩
    rw [heavyAnchor,dite_eq_left he]
    have hh:=hv.2 he.choose_spec.1 hcm (he.choose_spec.2.trans ha.symm)
    rw [hh]
    exact hd.trans (hv.1 c hcm).2

lemma structure_anchor_distance (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (tape:Tape Y k H r) (t:ℕ)
    (i:Structure k) (x:Y) (a:Alphabet Y k i)
    (ha:keys s law hr.le σ tape t i x=some a) :
    dist (anchors s law hr.le σ tape t i a) x ≤ 20*r := by
  cases i with
  | none => exact heavy_anchor_distance s law hr σ tape.1 t x a ha
  | some i =>
    have : Nonempty Y :=nonemptyY s
    have hd:=TierKeys.anchor_distance (request s σ) hr (tierQualifies s law r σ i)
      (tape.2 i).1 (tape.2 i).2 t x ha
    exact hd.trans (by linarith)

lemma anchor_distance (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (tape:Tape Y k H r) (t:ℕ) (x:Y) :
    dist (anchor s law hr.le σ tape t (map s law hr.le σ tape t x)) x ≤ 20*r :=
  PriorityKeys.anchor_distance _ _ hr.le (structure_anchor_distance s law hr σ tape t) x

lemma cell_diameter (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (tape:Tape Y k H r) (t:ℕ) (x y:Y)
    (he:map s law hr.le σ tape t x=map s law hr.le σ tape t y) : dist x y ≤ 40*r :=
  PriorityKeys.cell_diameter _ _ hr.le (structure_anchor_distance s law hr σ tape t) he
end KServer.LevelKeys

end


/-! Explicit finite independent tapes and their exact marginal laws. -/


/-! A single genuine finite independent tape for the complete level map. -/

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_PartitionBudget
attribute [-instance] _root_.OAI.KServer.JointExperiment.levelTapeFintype _root_.OAI.KServer.LevelKeys.alphabetFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal conditional averaging for the hidden optimum's stationary members.
Only conditioning on the true request prefix is used; tape averages may be
performed first without conditioning on a surviving random roster. -/


/-! Literal tier edit potentials along the selected hidden optimum.
Retirement averages are over the complete independent tape, before request
prefix conditioning.  All quantities below refer to constructed keys. -/


/-! True-prefix payment of literal tier retirement errors by the posterior
insertion mass.  No conditioning on the realized random tape is used. -/


/-! Literal one-step tier cost + potential accounting at the true observation
filtration. The insertion term is the existing geometric pilot charge. -/


/-! Horizon-independent endpoint bound for the actual dyadic-tier edits. -/


/-! Literal deterministic heavy-center schedule and its clipped distance profile,
§07 of the current manuscript. Random heavy radii do not affect this schedule. -/


/-! The actual heavy-priority stage, including its deterministic clipped-ramp
potential and the true hidden trajectory. -/


/-! True-prefix causality of the literal fixed-label complete level map.
The finite permanent colors and cooldown reservations do not read the future. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.KeysAdapted
open FiniteExperiment TierProcess Chronological ActualRoster LevelKeys LevelLaw
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

omit [MetricSpace Y] [NeZero k] in
lemma history_mono {t T:ℕ} (ht:t≤T) (σ ρ:Fin H→Y)
    (hh:requestHistory T σ=requestHistory T ρ) : requestHistory t σ=requestHistory t ρ := by
  rw [requestHistory_eq_iff] at hh ⊢
  funext i
  by_cases hi:i.val<t
  · have hiT:i.val<T:=lt_of_lt_of_le hi ht
    have he:=congrFun hh i
    simpa only [requestPrefix,ite_eq_left hi,ite_eq_left hiT] using he
  · simp only [requestPrefix,ite_eq_right hi]

lemma run_adapted (s:Configuration k Y) (law:RequestLaw Y H)
    (r γ δ:ℝ) (tape:Fin H→FiniteUniform.Outcome Y r) (t:ℕ)
    (σ ρ:Fin H→Y) (hh:requestHistory t σ=requestHistory t ρ) :
    HeavySchedule.run s law r γ δ σ tape t=HeavySchedule.run s law r γ δ ρ tape t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have h0:requestHistory t σ=requestHistory t ρ:=requestHistory_refines t σ ρ hh
    have hd:=ih h0
    have hc:=HeavyCenters.centers_adapted s law r γ δ t σ ρ h0
    have hp:=HeavyCenters.centers_adapted s law r γ δ (t-1) σ ρ (history_mono (Nat.sub_le _ _) σ ρ h0)
    have hm:mu s law (t+1) σ=mu s law (t+1) ρ:=funext (fun p=>mu_adapted s law (t+1) p σ ρ hh)
    simp only [HeavySchedule.run,hd,hc,hp,hm]
    by_cases ht:t<H
    · simp only [dite_eq_left ht]
      rw [request_of_history ⟨t,ht⟩ σ ρ hh]
    · simp only [dite_eq_right ht]

lemma heavy_key_adapted (s:Configuration k Y) (law:RequestLaw Y H)
    (r γ δ:ℝ) (tape:Fin H→FiniteUniform.Outcome Y r) (t:ℕ) (p:Y)
    (σ ρ:Fin H→Y) (hh:requestHistory t σ=requestHistory t ρ) :
    HeavyKeys.key s law r γ δ σ tape t p=HeavyKeys.key s law r γ δ ρ tape t p := by
  unfold HeavyKeys.key
  rw [run_adapted s law r γ δ tape t σ ρ hh,HeavyCenters.centers_adapted s law r γ δ t σ ρ hh]

lemma reserved_adapted (s:Configuration k Y) (law:RequestLaw Y H)
    (T:Pilot.Template) (r γ h:ℝ) (K t:ℕ) (σ ρ:Fin H→Y)
    (hh:requestHistory t σ=requestHistory t ρ) :
    reserved (request s σ) r K (qualifies s law T r γ h σ) t=
      reserved (request s ρ) r K (qualifies s law T r γ h ρ) t := by
  change young (request s σ) (roster s law T r γ h K σ t) (20*r) (K^2)=_
  have he:=roster_adapted s law T r γ h K t σ ρ hh
  change _=young (request s ρ) (roster s law T r γ h K ρ t) (20*r) (K^2)
  rw [←he]
  unfold young
  apply filter_congr
  intro i hi
  rw [ShortRoster.age_congr (request_adapted s (roster_before s law T r γ h K σ t i hi) σ ρ hh)
    (fun j hj=>request_adapted s (roster_before s law T r γ h K σ t j hj) σ ρ hh)]

lemma conflicts_adapted (s:Configuration k Y) (law:RequestLaw Y H)
    (T:Pilot.Template) (r γ h:ℝ) (K t:ℕ) (σ ρ:Fin H→Y)
    (hh:requestHistory t σ=requestHistory t ρ) :
    conflicts (request s σ) r K (qualifies s law T r γ h σ) t=
      conflicts (request s ρ) r K (qualifies s law T r γ h ρ) t := by
  unfold conflicts
  rw [reserved_adapted s law T r γ h K t σ ρ hh,
    reserved_adapted s law T r γ h K (t-1) σ ρ (history_mono (Nat.sub_le _ _) σ ρ hh)]

omit [MetricSpace Y] [Fintype Y] [NeZero k] in
lemma stage_congr {M t:ℕ} (hM:0<M) {c d:ℕ→Finset ℕ}
    (hc:∀ j,(c j).card<M) (hd:∀ j,(d j).card<M) (he:∀ j,j<t→c j=d j) :
    OnlineLabels.stage hM c hc t=OnlineLabels.stage hM d hd t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hp:=ih (fun j hj=>he j (by omega))
    simp only [OnlineLabels.stage,hp,he t (by omega)]

lemma label_adapted (s:Configuration k Y) (law:RequestLaw Y H)
    (T:Pilot.Template) {r:ℝ} (hr:0 ≤ r) (γ h:ℝ) (K t i:ℕ) (hi:i<t)
    (σ ρ:Fin H→Y) (hh:requestHistory t σ=requestHistory t ρ) :
    Chronological.label (request s σ) hr K (qualifies s law T r γ h σ) i=
      Chronological.label (request s ρ) hr K (qualifies s law T r γ h ρ) i := by
  unfold Chronological.label OnlineLabels.color
  have he:=stage_congr (t:=i+1) (pool_pos (Y:=Y) K)
    (conflicts_card (request s σ) hr K (qualifies s law T r γ h σ))
    (conflicts_card (request s ρ) hr K (qualifies s law T r γ h ρ))
    (fun j hj=>conflicts_adapted s law T r γ h K j σ ρ (history_mono (by omega) σ ρ hh))
  exact congrFun he i

lemma first_congr {c d:ℕ→Y} {I:Finset ℕ} {r:ℝ} {K:ℕ}
    (hc:∀ j∈I,c j=d j) (life:Fin H→Lifetime K) (rad:Fin H→FiniteBallLaw.Outcome Y r) (p:Y) :
    first c I r life rad p=first d I r life rad p := by
  have he:covered c I r life rad p=covered d I r life rad p:=by
    funext i
    apply propext
    unfold covered present
    by_cases hi:(i:ℕ)∈I
    · rw [ShortRoster.age_congr (hc i hi) hc,hc i hi]
    · simp only [hi,false_and]
  unfold first
  rw [he]

lemma tier_key_adapted (s:Configuration k Y) (law:RequestLaw Y H)
    (T:Pilot.Template) {r:ℝ} (hr:0 ≤ r) (γ h:ℝ) (K:ℕ)
    (life:Fin H→Lifetime K) (rad:Fin H→FiniteBallLaw.Outcome Y r) (t:ℕ) (p:Y)
    (σ ρ:Fin H→Y) (hh:requestHistory t σ=requestHistory t ρ) :
    TierKeys.key (request s σ) hr K (qualifies s law T r γ h σ) life rad t p=
      TierKeys.key (request s ρ) hr K (qualifies s law T r γ h ρ) life rad t p := by
  have hR:=roster_adapted s law T r γ h K t σ ρ hh
  have hf:first (request s σ) (roster s law T r γ h K σ t) r life rad p=
      first (request s ρ) (roster s law T r γ h K ρ t) r life rad p:=by
    exact (first_congr (fun j hj=>request_adapted s (roster_before s law T r γ h K σ t j hj) σ ρ hh) life rad p).trans
      (congrArg (fun I=>first (request s ρ) I r life rad p) hR)
  change (first (request s σ) (roster s law T r γ h K σ t) r life rad p).map
    (fun j:Fin H=>Chronological.label (request s σ) hr K (qualifies s law T r γ h σ) j)=
    (first (request s ρ) (roster s law T r γ h K ρ t) r life rad p).map
    (fun j:Fin H=>Chronological.label (request s ρ) hr K (qualifies s law T r γ h ρ) j)
  refine (Option.map_congr ?_).trans (congrArg (fun z=>z.map
    (fun j:Fin H=>Chronological.label (request s ρ) hr K (qualifies s law T r γ h ρ) j)) hf)
  intro i he
  have hi:=(first_some_iff (request s σ) (roster s law T r γ h K σ t) r life rad p i).mp he
  exact label_adapted s law T hr γ h K t i
    (roster_before s law T r γ h K σ t i hi.1.1.1) σ ρ hh

lemma keys_adapted (s:Configuration k Y) (law:RequestLaw Y H)
    {r:ℝ} (hr:0 ≤ r) (a:Tape Y k H r) (t:ℕ) (σ ρ:Fin H→Y)
    (hh:requestHistory t σ=requestHistory t ρ) :
    keys s law hr σ a t=keys s law hr ρ a t := by
  funext i p
  cases i with
  | none => exact heavy_key_adapted s law _ _ _ a.1 t p σ ρ hh
  | some i =>
    exact tier_key_adapted s law tierTemplate hr tierGamma (height i) (tierK (height i))
      (a.2 i).1 (a.2 i).2 t p σ ρ hh

lemma map_adapted (s:Configuration k Y) (law:RequestLaw Y H)
    {r:ℝ} (hr:0 ≤ r) (a:Tape Y k H r) (t:ℕ) (p:Y) (σ ρ:Fin H→Y)
    (hh:requestHistory t σ=requestHistory t ρ) :
    LevelKeys.map s law hr σ a t p=LevelKeys.map s law hr ρ a t p := by
  unfold LevelKeys.map
  rw [keys_adapted s law hr a t σ ρ hh]

end KServer.KeysAdapted

end


/-! True-prefix heavy edit accounting. The deterministic profile is telescoped
on the hidden labeled optimum; no surviving-radius conditioning is used. -/

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
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PosteriorCounting
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking PosteriorRanks HierarchyCounts
variable {Ω Y A:Type} [Fintype Ω] [Fintype Y] [Fintype A]
variable {w:Ω→ℝ} (hw:∀ ω,0≤w ω) {k:ℕ}

omit [Fintype Y] in
lemma atoms_nonneg (q:Fin k→Y) (y:Y):0≤atoms q y:=by
  exact sum_nonneg fun _ _=>by split_ifs <;> norm_num

lemma atoms_total (q:Fin k→Y):(∑ y,atoms q y)=(k:ℝ):=by
  unfold atoms
  rw [sum_comm]
  simp

include hw in
omit [Fintype Y] in
lemma measure_nonneg (H:Ω→ℕ) (q:Ω→Fin k→Y) (ω:Ω) (y:Y):
    0 ≤ measure (w:=w) H q ω y:=posterior_nonneg hw H (fun _=>atoms_nonneg _ _) ω

include hw in
lemma measure_total (H:Ω→ℕ) (q:Ω→Fin k→Y) (ω:Ω) (hω:0<w ω):
    (∑ y,measure (w:=w) H q ω y)=(k:ℝ):=by
  unfold measure
  rw [←posterior_sum]
  exact posterior_fiber_const ω (fun _ _=>atoms_total _) (positive_mass hw H ω hω).ne'

lemma atoms_integral (q:Fin k→Y) (f:Y→ℝ):
    (∑ y,atoms q y*f y)=∑ l:Fin k,f (q l):=by
  unfold atoms
  simp only [sum_mul,ite_mul,one_mul,zero_mul]
  rw [sum_comm]
  simp

lemma conditional_integral (H:Ω→ℕ) (q:Ω→Fin k→Y) (ω:Ω)
    (F:Ω→Y→ℝ) (hF:∀ ρ,H ρ=H ω→F ρ=F ω):
    (∑ y,measure (w:=w) H q ω y*F ω y)=
      posterior w H (fun ρ=>∑ l:Fin k,F ρ (q ρ l)) ω:=by
  unfold measure
  simp_rw [←posterior_mul]
  rw [←posterior_sum]
  unfold posterior numerator
  congr 1
  apply sum_congr rfl
  intro ρ hρ
  dsimp only
  rw [atoms_integral,hF ρ (mem_filter.mp hρ).2]

lemma conditional_mean (H:Ω→ℕ) (f:Ω→ℝ) (ω:Ω):
    (∑ ρ,conditional w H ω ρ*f ρ)=posterior w H f ω:=by
  unfold conditional posterior numerator
  simp only [ite_mul,zero_mul,div_mul_eq_mul_div]
  rw [←sum_filter,←sum_div]
  rfl

omit [Fintype A] in
lemma prefix_mass (H:Ω→ℕ) (maps:Ω→ℕ→Y→A) (q:Ω→Fin k→Y)
    {d:ℕ} (word:Fin d→A) (ω:Ω) (hm:∀ ρ,H ρ=H ω→maps ρ=maps ω):
    (∑ y∈univ.filter (hit (maps ω) word),measure (w:=w) H q ω y)=
      posterior w H (fun ρ=>(count (maps ρ) word (q ρ):ℝ)) ω:=by
  unfold measure posterior numerator
  rw [←sum_div]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro ρ hρ
  rw [←mul_sum]
  congr 1
  have he:=hm ρ (mem_filter.mp hρ).2
  dsimp only
  rw [he]
  unfold atoms count
  rw [sum_comm]
  simp only [card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  apply sum_congr rfl
  intro l _
  simp [eq_comm]

lemma size_prefix_bound (H:ℕ→Ω→ℕ)
    (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
    (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y)
    {d:ℕ} (word:Fin d→A) (t:ℕ) (ω:Ω) (hω:0<w ω)
    (hm:∀ ρ,H t ρ=H t ω→maps t ρ=maps t ω):
    HierarchicalRanks.size hw H hr maps q word t ω≤
      ∑ y∈univ.filter (hit (maps t ω) word),measure (w:=w) (H t) (q t) ω y:=by
  rw [prefix_mass (H t) (maps t) (q t) word ω hm,HierarchicalRanks.size_eq]
  rw [←conditional_mean]
  exact (HierarchyCounts.compatible w hw (H t) ω hω (maps t) word (q t)
    (z:=0) (by norm_num)).2.2

end KServer.PosteriorCounting

end


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

lemma mass_support {w:Ω→ℝ} (hw:∀ ω,0≤w ω) (H:Ω→ℕ) (h:ℕ):
    PosteriorRanks.mass (weight w) (fun ω=>H ω.val) h=PosteriorRanks.mass w H h:=by
  simpa only [PosteriorRanks.mass,PosteriorRanks.fiber,sum_filter,mul_ite,mul_one,mul_zero]
    using sum_support hw (fun ω=>if H ω=h then 1 else 0)

lemma numerator_support {w:Ω→ℝ} (hw:∀ ω,0≤w ω) (H:Ω→ℕ) (f:Ω→ℝ) (h:ℕ):
    PosteriorRanks.numerator (weight w) (fun ω=>H ω.val) (fun ω=>f ω.val) h=
      PosteriorRanks.numerator w H f h:=by
  simpa only [PosteriorRanks.numerator,PosteriorRanks.fiber,sum_filter,mul_ite,mul_zero]
    using sum_support hw (fun ω=>if H ω=h then f ω else 0)

lemma posterior_support {w:Ω→ℝ} (hw:∀ ω,0≤w ω) (H:Ω→ℕ) (f:Ω→ℝ) (ω:Support w):
    posterior (weight w) (fun ρ=>H ρ.val) (fun ρ=>f ρ.val) ω=posterior w H f ω.val:=by
  simp only [posterior,mass_support hw,numerator_support hw]

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

lemma avg_raw (f:Raw Y k H L r→ℝ):
    avg (weight (k:=k) law hr) (fun ω=>f ω.val)=avg (rawWeight law hr) f:=
  PositiveExperiment.sum_support (raw_nonneg law hr) f

lemma request_pos (ω:Atom (k:=k) law hr):0<law.val ω.val.1:=by
  have hp:=weight_pos law hr ω
  change 0<law.val ω.val.1*(tapeLaw (Y:=Y) (k:=k) (H:=H) hr).val ω.val.2 at hp
  exact pos_of_mul_pos_left hp ((tapeLaw (Y:=Y) (k:=k) (H:=H) hr).property.1 ω.val.2)

lemma tape_pos (ω:Atom (k:=k) law hr):0<(tapeLaw (Y:=Y) (k:=k) (H:=H) hr).val ω.val.2:=by
  have hp:=weight_pos law hr ω
  change 0<law.val ω.val.1*(tapeLaw (Y:=Y) (k:=k) (H:=H) hr).val ω.val.2 at hp
  exact pos_of_mul_pos_right hp (law.property.1 _)

lemma history_eq (t:ℕ) (ω ρ:Atom (k:=k) law hr)
    (h:history law hr t ω=history law hr t ρ):
    ω.val.2=ρ.val.2 ∧ requestPrefix ω.val.1 t=requestPrefix ρ.val.1 t:=
  (FiniteExperiment.history_eq_iff t ω.val ρ.val).mp h

variable [NeZero k] (s:Configuration k Y)

lemma maps_adapted (t:ℕ) (ω ρ:Atom (k:=k) law hr)
    (h:history law hr t ω=history law hr t ρ):maps law hr s t ω=maps law hr s t ρ:=by
  obtain ⟨ht,hp⟩:=history_eq law hr t ω ρ h
  have hh:requestHistory t ω.val.1=requestHistory t ρ.val.1:=
    (requestHistory_eq_iff _ _ _).mpr hp
  funext d y
  unfold maps
  split_ifs with hd
  · rw [ht]
    exact KeysAdapted.map_adapted s law (hr ⟨d,hd⟩).le (ρ.val.2 ⟨d,hd⟩) t y _ _ hh
  · rfl

lemma measure_eq (t:ℕ) (ω:Atom (k:=k) law hr) (y:Y):
    PosteriorCounting.measure (w:=weight law hr) (history law hr t) (hidden law hr s t) ω y=
      mu s law t ω.val.1 y:=by
  change posterior (PositiveExperiment.weight (rawWeight law hr))
    (fun z=>FiniteExperiment.history t z.val)
    (fun z=>PosteriorCounting.atoms (FiniteExperiment.hidden s z.val.1 t) y) ω=_
  rw [PositiveExperiment.posterior_support (raw_nonneg law hr) (FiniteExperiment.history t)
    (fun z:Raw Y k H L r=>PosteriorCounting.atoms (FiniteExperiment.hidden s z.1 t) y) ω]
  unfold rawWeight FiniteExperiment.mu
  convert posterior_tape_irrelevant law (tapeLaw (Y:=Y) (k:=k) (H:=H) hr) t ω.val (tape_pos law hr ω).ne' (fun σ=>PosteriorCounting.atoms (FiniteExperiment.hidden s σ t) y) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [FiniteExperiment.metricCount,PosteriorCounting.atoms]

omit [NeZero k] in
lemma request_history (t:Fin H) (ω ρ:Atom (k:=k) law hr)
    (h:history law hr (t.val+1) ω=history law hr (t.val+1) ρ):ω.val.1 t=ρ.val.1 t:=
  prefix_request t (history_eq law hr _ ω ρ h).2

lemma hidden_covers (t:Fin H) (ω:Atom (k:=k) law hr):
    ∃ i,hidden law hr s (t.val+1) ω i=ω.val.1 t:=
  ⟨mover s ω.val.1 t,FiniteExperiment.hidden_covers s ω.val.1 t⟩

end KServer.JointExperiment

end


/-! The dependent permanent key alphabet is genuinely finite. -/


/-! Endpoint costs on the actual schedule are charged to active size, rather
than to all inactive fixed labels. This is needed for wholesale edits. -/

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


/-! Actual singleton/side-free transitions: their cost is paid by changed
flags, not by a fresh charge to the persistent dominant mass. -/


/-! The complete ordinary/wholesale simplex payment for the literal schedule.
All charges below are computed by the actual switches, never supplied by a
finite-law hypothesis. -/


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
lemma more_constants_nonneg:0≤ wholesaleConstant ∧ 0≤ scaleConstant ∧ 0≤ sideRefreshConstant:=by
  rcases constants_nonneg with ⟨ha,hp,hf⟩
  have hc:=CoarseSide.C_nonneg (by norm_num [ds]:0< ds)
  have hd:0≤80/ds:=by norm_num [ds]
  dsimp only [wholesaleConstant,scaleConstant,sideRefreshConstant]
  constructor
  · positivity
  constructor <;> positivity

end KServer.ActualCharges

end


/-! Deterministic payment for the literal side state, with only actual edits
on the right hand side. Parent parameters are held through an ordinary epoch. -/


/-! Deterministic payment for the literal side state, with only actual edits
on the right hand side. Parent parameters are held through an ordinary epoch. -/


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


/-! Expected movement of the literal minimizers, with uniform endpoint bills. -/


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

end KServer.ActualCharges
end


/-! All-step output charging, including wholesale jumps without a charge per
child or per epoch. The parent variation retains coefficient exactly one. -/


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

end KServer.ActualCharges

end


/-! The actual top-down allocation, summed over the fixed complete-prefix
hierarchy. All initialization costs depend only on the fixed label inventory. -/


/-! Geometric absorption with the literal parent coefficient one. -/


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


noncomputable section
open scoped BigOperators
open Set Finset
namespace KServer.KeySizeTracking

lemma tangent_credit {u s : ℝ} (hu : 0 < u) (hs : 0 < s) :
    tangent u s - tangent s s = entropy u s := by
  rw [entropy, Real.log_div hs.ne' hu.ne']
  unfold tangent
  ring

lemma lower_ratio {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    (x - 1)^2 / 2 ≤ x * Real.log x - x + 1 := by
  let f : ℝ → ℝ := fun y => (y-1)^2/2 - (y*Real.log y-y+1)
  have hd (y : ℝ) (hy : 0 < y) : HasDerivAt f (y-1-Real.log y) y := by
    have h := (((hasDerivAt_id y).sub_const 1).pow 2).div_const 2
    have h' := (((hasDerivAt_id y).mul (Real.hasDerivAt_log hy.ne')).sub
      (hasDerivAt_id y)).add_const 1
    convert h.sub h' using 1 <;> first | rfl | (norm_num [id_eq]; field_simp [hy.ne']; ring)
  have hm : MonotoneOn f (Icc x 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc x 1)
    · intro y hy
      exact (hd y (hx.trans_le hy.1)).continuousAt.continuousWithinAt
    · intro y hy
      exact (hd y (hx.trans_le (interior_subset hy).1)).hasDerivWithinAt
    · intro y hy
      have h := Real.log_le_sub_one_of_pos (hx.trans_le (interior_subset hy).1)
      linarith
  have h := hm ⟨le_rfl,hx1⟩ ⟨hx1,le_rfl⟩ hx1
  dsimp [f] at h
  norm_num at h
  linarith

lemma upper_ratio {x : ℝ} (hx : 1 ≤ x) :
    (x - 1)^2 / (2*x) ≤ x * Real.log x - x + 1 := by
  let f : ℝ → ℝ := fun y => y*Real.log y-y+1 - (y-1)^2/(2*y)
  have hd (y : ℝ) (hy : 0 < y) :
      HasDerivAt f (Real.log y - (1-y⁻¹^2)/2) y := by
    have h := (((hasDerivAt_id y).mul (Real.hasDerivAt_log hy.ne')).sub
      (hasDerivAt_id y)).add_const 1
    have h' := (((hasDerivAt_id y).sub_const 1).pow 2).div
      ((hasDerivAt_id y).const_mul 2) (by positivity : 2*y ≠ 0)
    convert h.sub h' using 1 <;> first | rfl | (norm_num [id_eq]; field_simp [hy.ne']; ring)
  have hm : MonotoneOn f (Icc 1 x) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 1 x)
    · intro y hy
      exact (hd y (by linarith [hy.1])).continuousAt.continuousWithinAt
    · intro y hy
      exact (hd y (by linarith [(interior_subset hy).1])).hasDerivWithinAt
    · intro y hy
      have hp : 0 < y := by linarith [(interior_subset hy).1]
      have h := Real.one_sub_inv_le_log_of_pos hp
      nlinarith [sq_nonneg (1-y⁻¹)]
  have h := hm ⟨le_rfl,hx⟩ ⟨hx,le_rfl⟩ hx
  dsimp [f] at h
  norm_num at h
  linarith

lemma entropy_quadratic {u s : ℝ} (hu : 0 < u) (hs : 0 < s) :
    (s-u)^2 / (2*max s u) ≤ entropy u s := by
  have hx : 0 < s/u := div_pos hs hu
  have he : entropy u s = u*((s/u)*Real.log (s/u)-s/u+1) := by
    unfold entropy
    field_simp
  rw [he]
  rcases le_total s u with hsu | hus
  · rw [max_eq_right hsu]
    have h := mul_le_mul_of_nonneg_left
      (lower_ratio hx ((div_le_one hu).mpr hsu)) hu.le
    convert h using 1 <;> first | rfl | field_simp
  · rw [max_eq_left hus]
    have h := mul_le_mul_of_nonneg_left
      (upper_ratio ((one_le_div hu).mpr hus)) hu.le
    convert h using 1 <;> first | rfl | field_simp

lemma relative_credit {u s : ℝ} (hu : 0 < u) (hs : 0 < s)
    (hfail : s < (5/6:ℝ)*u ∨ (6/5:ℝ)*u < s) :
    (s+u)/144 ≤ tangent u s-tangent s s := by
  rw [tangent_credit hu hs]
  have hq := entropy_quadratic hu hs
  have hm : 0 < max s u := lt_of_lt_of_le hs (le_max_left _ _)
  have hgap : (max s u / 6)^2 ≤ (s-u)^2 := by
    rcases hfail with h | h
    · have hsu : s ≤ u := by linarith
      rw [max_eq_right hsu]
      nlinarith
    · have hus : u ≤ s := by linarith
      rw [max_eq_left hus]
      nlinarith
  have hsum : s+u ≤ 2*max s u := by linarith [le_max_left s u,le_max_right s u]
  have hh : (s+u)/144 ≤ (s-u)^2/(2*max s u) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hsum hm.le]
  exact hh.trans hq


variable {Ω : Type} [Fintype Ω]

lemma avg_add (w f g : Ω → ℝ) : avg w (fun ω => f ω+g ω)=avg w f+avg w g := by
  simp [avg,mul_add,sum_add_distrib]
lemma avg_sub (w f g : Ω → ℝ) : avg w (fun ω => f ω-g ω)=avg w f-avg w g := by
  simp [avg,mul_sub,sum_sub_distrib]
lemma avg_mul (w f : Ω → ℝ) (c : ℝ) : avg w (fun ω => c*f ω)=c*avg w f := by
  simp only [avg,mul_sum,mul_left_comm (w _) c]
lemma avg_mono {w f g : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (h : ∀ ω, f ω ≤ g ω) :
    avg w f ≤ avg w g := sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (hw ω)
lemma avg_const (w : Ω → ℝ) (hw : ∑ ω, w ω=1) (c : ℝ) : avg w (fun _ => c)=c := by
  simp [avg,←sum_mul,hw]

lemma fiber_weighted_zero (H : Ω → ℕ) (f g : Ω → ℝ)
    (hf : Adapted H f) (hg : ∀ h, ∑ ω ∈ Finset.univ.filter (fun ω => H ω=h), g ω=0) :
    ∑ ω, f ω*g ω=0 := by
  classical
  let c : ℕ → ℝ := fun h => if hh : ∃ ω, H ω=h then f hh.choose else 0
  have hc : ∀ ω, f ω=c (H ω) := by
    intro ω
    dsimp [c]
    rw [dite_eq_left ⟨ω,rfl⟩]
    exact hf ω _ (Exists.choose_spec (show ∃ ω', H ω'=H ω from ⟨ω,rfl⟩)).symm
  have hs : (∑ ω, f ω*g ω) =
      ∑ h ∈ Finset.univ.image H, ∑ ω ∈ Finset.univ.filter (fun ω => H ω=h), f ω*g ω := by
    symm
    exact Finset.sum_fiberwise_of_maps_to (by intro ω _; exact Finset.mem_image.mpr ⟨ω,Finset.mem_univ _,rfl⟩) _
  rw [hs]
  apply sum_eq_zero
  intro h _
  calc _ = c h*(∑ ω ∈ Finset.univ.filter (fun ω => H ω=h), g ω) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro ω hω
        rw [hc ω,(Finset.mem_filter.mp hω).2]
       _ = 0 := by rw [hg,mul_zero]

omit [Fintype Ω] in
lemma held_range {s : ℕ → Ω → ℝ} {K : ℝ} (hs : ∀ t ω, s t ω ∈ Icc 1 K) :
    ∀ t ω, held s t ω ∈ Icc 1 K := by
  intro t
  induction t with
  | zero => exact hs 0
  | succ t ih => intro ω; dsimp [held]; split_ifs <;> [exact hs _ _; exact ih ω]

lemma held_adapted {w : Ω → ℝ} {K : ℝ} (R : FilteredSizes w K) :
    ∀ t, Adapted (R.history t) (held R.s t) := by
  intro t
  induction t with
  | zero => exact R.adapted 0
  | succ t ih =>
    intro ω ω' hh
    have hprev := ih ω ω' (R.refines t ω ω' hh)
    have hnow := R.adapted (t+1) ω ω' hh
    simp only [held,hnow,hprev]

omit [Fintype Ω] in
lemma held_accurate {s : ℕ → Ω → ℝ} (hs : ∀ t ω, 0 ≤ s t ω) (t : ℕ) (ω : Ω) :
    (5/6:ℝ)*held s t ω ≤ s t ω ∧ s t ω ≤ (6/5:ℝ)*held s t ω := by
  cases t with
  | zero => dsimp [held]; constructor <;> nlinarith [hs 0 ω]
  | succ t =>
    dsimp [held]
    split_ifs with h
    · constructor <;> nlinarith [hs (t+1) ω]
    · simp only [refresh,not_or,not_lt] at h
      exact h

lemma slope_bound {K u : ℝ} (hu : u ∈ Icc 1 K) :
    |-(1+Real.log u)| ≤ 1+Real.log K := by
  have hp : 0 < u := by linarith [hu.1]
  have hl := Real.log_nonneg hu.1
  rw [abs_neg,abs_of_nonneg (by linarith : 0 ≤ 1+Real.log u)]
  linarith [Real.log_le_log hp hu.2]

lemma tangent_bound {K u s : ℝ} (hu : u ∈ Icc 1 K) (hs : s ∈ Icc 1 K) :
    |tangent u s| ≤ K*(1+(1+Real.log K)) := by
  have hK : 1 ≤ K := hu.1.trans hu.2
  have hu0 : 0 ≤ u := by linarith [hu.1]
  have hs0 : 0 ≤ s := by linarith [hs.1]
  have hL : 0 ≤ 1+Real.log K := by linarith [Real.log_nonneg hK]
  have h := slope_bound hu
  rw [abs_neg] at h
  calc |tangent u s| ≤ |u|+|(1+Real.log u)*s| := by simpa [tangent] using abs_sub_le u 0 ((1+Real.log u)*s)
       _ = u+|1+Real.log u| * s := by rw [abs_of_nonneg hu0,abs_mul,abs_of_nonneg hs0]
       _ ≤ K+(1+Real.log K)*K := add_le_add hu.2 (mul_le_mul h hs.2 hs0 hL)
       _ = _ := by ring

omit [Fintype Ω] in
lemma refresh_cost_step {s : ℕ → Ω → ℝ} {K : ℝ}
    (hs : ∀ t ω, s t ω ∈ Icc 1 K) (t : ℕ) (ω : Ω) :
    refreshCost s t ω /144 ≤
      tangent (held s t ω) (s t ω)-tangent (held s (t+1) ω) (s (t+1) ω) +
      (-(1+Real.log (held s t ω)))*(s (t+1) ω-s t ω) := by
  have hp : 0 < held s t ω := by linarith [(held_range hs t ω).1]
  have hp' : 0 < s (t+1) ω := by linarith [(hs (t+1) ω).1]
  have he : tangent (held s t ω) (s t ω)-tangent (held s (t+1) ω) (s (t+1) ω) +
      (-(1+Real.log (held s t ω)))*(s (t+1) ω-s t ω) =
      tangent (held s t ω) (s (t+1) ω)-tangent (held s (t+1) ω) (s (t+1) ω) := by
    unfold tangent; ring
  rw [he]
  dsimp [refreshCost,held]
  split_ifs with h
  · simpa only [add_comm] using relative_credit hp hp' h
  · simp

lemma filtering_zero {w : Ω → ℝ} {K : ℝ} (R : FilteredSizes w K) (t : ℕ) :
    avg w (fun ω => (-(1+Real.log (held R.s t ω)))*(R.before (t+1) ω-R.s t ω))=0 := by
  unfold avg
  simp_rw [mul_left_comm (w _) (-(1+Real.log (held R.s t _)))]
  apply fiber_weighted_zero (R.history t) _ _ _ (R.filtering t)
  intro ω ω' hh
  dsimp only
  rw [held_adapted R t ω ω' hh]

lemma expected_refresh_step {w : Ω → ℝ} {K : ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (R : FilteredSizes w K) (t : ℕ) :
    avg w (refreshCost R.s t)/144 ≤
      avg w (fun ω => tangent (held R.s t ω) (R.s t ω))-
      avg w (fun ω => tangent (held R.s (t+1) ω) (R.s (t+1) ω))+
      (1+Real.log K)*avg w (fun ω => |R.s (t+1) ω-R.before (t+1) ω|) := by
  have hs := avg_mono hw (refresh_cost_step R.range t)
  have he : avg w (fun ω => refreshCost R.s t ω/144)=avg w (refreshCost R.s t)/144 := by
    simp only [avg,←mul_div_assoc,Finset.sum_div]
  rw [he] at hs
  have hsplit : ∀ ω,
      (-(1+Real.log (held R.s t ω)))*(R.s (t+1) ω-R.s t ω) =
      (-(1+Real.log (held R.s t ω)))*(R.before (t+1) ω-R.s t ω)+
      (-(1+Real.log (held R.s t ω)))*(R.s (t+1) ω-R.before (t+1) ω) := by intro ω; ring
  simp_rw [hsplit] at hs
  rw [avg_add,avg_sub,avg_add,filtering_zero,zero_add] at hs
  apply hs.trans
  apply add_le_add le_rfl
  rw [←avg_mul]
  apply avg_mono hw
  intro ω
  calc _ ≤ |(-(1+Real.log (held R.s t ω)))*(R.s (t+1) ω-R.before (t+1) ω)| := le_abs_self _
       _ ≤ _ := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (slope_bound (held_range R.range t ω)) (abs_nonneg _)

/-- Size-refresh budget, before substituting the mapped-member
transport bound. Crucially the constant is independent of the horizon. -/
theorem size_refresh_budget {w : Ω → ℝ} {K : ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (hw1 : ∑ ω, w ω=1) (R : FilteredSizes w K) (N : ℕ) :
    ∑ t ∈ range N, avg w (refreshCost R.s t) ≤
      144*(1+Real.log K)*(∑ t ∈ range N, avg w (fun ω => |R.s (t+1) ω-R.before (t+1) ω|))+
      288*K*(1+(1+Real.log K)) := by
  let V : ℕ → ℝ := fun t => avg w (fun ω => tangent (held R.s t ω) (R.s t ω))
  let B : ℝ := K*(1+(1+Real.log K))
  have hV t : -B ≤ V t ∧ V t ≤ B := by
    have hb ω := abs_le.mp (tangent_bound (held_range R.range t ω) (R.range t ω))
    constructor
    · have h := avg_mono hw (fun ω => (hb ω).1)
      simpa only [avg_const w hw1 (-(K*(1+(1+Real.log K))))] using h
    · have h := avg_mono hw (fun ω => (hb ω).2)
      simpa only [avg_const w hw1 (K*(1+(1+Real.log K)))] using h
  have hsum := sum_le_sum (s := range N) (fun t _ => expected_refresh_step hw R t)
  change (∑ t ∈ range N, avg w (refreshCost R.s t)/144) ≤
    ∑ t ∈ range N, (V t-V (t+1)+(1+Real.log K)*avg w (fun ω => |R.s (t+1) ω-R.before (t+1) ω|)) at hsum
  rw [←sum_div,sum_add_distrib,Finset.sum_range_sub',←mul_sum] at hsum
  dsimp [B] at hV
  nlinarith [(hV 0).2,(hV N).1]

end KServer.KeySizeTracking

end


/-! Persistent heavy-slot size tracking on the actual finite observation
experiment. Raw counts can change with both the hidden trajectory and the
adapted partition. No martingale identity is postulated. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PosteriorSizes
open RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Ω:Type} [Fintype Ω] {w:Ω→ℝ}

lemma process_drift (hw:∀ ω,0≤w ω) (hwpos:∀ ω,0<w ω) {K:ℝ}
    (H:ℕ→Ω→ℕ) (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
    (N:ℕ→Ω→ℝ) (hN:∀ t ω,N t ω∈Set.Icc 0 K) (t:ℕ):
    avg w (fun ω=>|(process hw hwpos H hr N hN).s (t+1) ω-
      (process hw hwpos H hr N hN).before (t+1) ω|)≤
        avg w (fun ω=>|N (t+1) ω-N t ω|):=by
  simp only [process,Nat.add_sub_cancel,add_sub_add_left_eq_sub]
  exact posterior_drift hw (H (t+1)) (N (t+1)) (N t)

lemma refresh_budget (hw:∀ ω,0≤w ω) (hwpos:∀ ω,0<w ω) (hw1:∑ ω,w ω=1)
    {K:ℝ} (hK:0≤K) (H:ℕ→Ω→ℕ)
    (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
    (N:ℕ→Ω→ℝ) (hN:∀ t ω,N t ω∈Set.Icc 0 K) (T:ℕ):
    (∑ t∈range T,avg w (KeySizeTracking.refreshCost (process hw hwpos H hr N hN).s t)) ≤
      144*(1+Real.log (K+1))*(∑ t∈range T,avg w (fun ω=>|N (t+1) ω-N t ω|))+
        288*(K+1)*(1+(1+Real.log (K+1))):=by
  have h:=KeySizeTracking.size_refresh_budget hw hw1
    (process hw hwpos H hr N hN) T
  have hm:=sum_le_sum (s:=range T) (fun t _=>process_drift hw hwpos H hr N hN t)
  have hp:0≤144*(1+Real.log (K+1)):=by have :=Real.log_nonneg (by linarith : 1≤K+1); positivity
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_left hm hp) (le_refl _))

end KServer.PosteriorSizes

end


/-! Literal children and geometric edge weights of the retained complete
prefix tree. These identify the numbered rounding tree without deleting empty
words or changing its allocated coordinates. -/


/-! Quotas and parks on the actual numbered complete-prefix tree, with their
posterior support witnesses. Rounding.Tree and TreeRounding.Tree have the same
parent data; the conversion below changes no vertex or quantity. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable (A:Type) [Fintype A] (L:ℕ)

variable {Ω Y:Type} [Fintype Ω] [Fintype Y] {k:ℕ} {w:Ω→ℝ}
variable (hw:∀ ω,0≤w ω) (H:ℕ→Ω→ℕ)
variable (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
variable (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y) (hk:1≤(k:ℝ))

omit [Fintype Y] in
lemma Q_adapted (t:ℕ) (v:Fin (Fintype.card (Vertex A L))):
    RankTracking.Adapted (H t) (fun ω=>Q A L hw H hr maps q hk t ω v):=by
  intro ω ρ he
  exact HierarchicalQuota.quota_adapted hw H hr maps q hk _ _ t ω ρ he

lemma Q_mass (hwpos:∀ ω,0<w ω) (t:ℕ) (ω:Ω)
    (hm:∀ ρ,H t ρ=H t ω→maps t ρ=maps t ω) (v:Fin (Fintype.card (Vertex A L))):
    Q A L hw H hr maps q hk t ω v≤
      72*∑ y∈region A L maps t ω v,PosteriorCounting.measure (w:=w) (H t) (q t) ω y:=by
  exact (HierarchicalQuota.quota_bounds hw H hr maps q hk hwpos _ _ t ω).2.trans
    (mul_le_mul_of_nonneg_left (PosteriorCounting.size_prefix_bound hw H hr maps q _ t ω (hwpos ω) hm)
      (by norm_num))

lemma Q_witness (hwpos:∀ ω,0<w ω) (t:ℕ) (ω:Ω)
    (hm:∀ ρ,H t ρ=H t ω→maps t ρ=maps t ω) (v:Fin (Fintype.card (Vertex A L)))
    (hq:0<Q A L hw H hr maps q hk t ω v):∃ y,y∈region A L maps t ω v:=by
  have hh:=Q_mass A L hw H hr maps q hk hwpos t ω hm v
  by_contra hn
  have he:region A L maps t ω v=∅:=by
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    exact hn ⟨y,hy⟩
  rw [he,sum_empty,mul_zero] at hh
  linarith

omit [Fintype Y] in
lemma park_le_Q (hwpos:∀ ω,0<w ω) (t:ℕ) (ω:Ω) (v:Fin (Fintype.card (Vertex A L))):
    (travelTree A L).park (Q A L hw H hr maps q hk t ω) v≤Q A L hw H hr maps q hk t ω v:=by
  apply sub_le_self
  exact sum_nonneg fun u _=>Q_nonneg A L hw H hr maps q hk hwpos t ω u.val

end KServer.PrefixTree

end


/-! Actual truncation ancestors of complete-prefix words, with the retained
numbering used by the finite rounding tree. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable (A:Type) [Fintype A] (L:ℕ)

omit [Fintype A] in
lemma take_self (v:Vertex A L):take A L v v.1.val le_rfl=v:=by
  rcases v with ⟨j,f⟩
  rfl

omit [Fintype A] in
lemma take_parent (v:Vertex A L) {d:ℕ} (hd:d<v.1.val):
    take A L (parent A L v) d (by rw [parent_depth A L v (by omega)]; omega)=
      take A L v d hd.le:=by
  rcases v with ⟨⟨e,he⟩,f⟩
  cases e with
  | zero=>exact False.elim (Nat.not_lt_zero _ hd)
  | succ e=>rfl

omit [Fintype A] in
lemma hit_take {Y:Type} (maps:ℕ→Y→A) (v:Vertex A L) (d:ℕ) (hd:d≤v.1.val)
    (y:Y) (hy:HierarchyCounts.hit maps v.2 y):
    HierarchyCounts.hit maps (take A L v d hd).2 y:=by
  intro i
  exact hy ⟨i.val,lt_of_lt_of_le i.isLt hd⟩

lemma numbering_parent (v:Fin (Fintype.card (Vertex A L))):
    numbering A L ((travelTree A L).parent v)=parent A L (numbering A L v):=by
  exact (numbering A L).apply_symm_apply _

lemma numbering_eq_root (v:Fin (Fintype.card (Vertex A L))):
    numbering A L v=root A L ↔ v=0:=by
  rw [←numbering_zero A L]
  exact (numbering A L).injective.eq_iff

lemma take_under (v:Fin (Fintype.card (Vertex A L))) (d:ℕ) (hd:d≤(numbering A L v).1.val):
    (travelTree A L).under ((numbering A L).symm (take A L (numbering A L v) d hd)) v=true:=by
  by_cases he:d=(numbering A L v).1.val
  · subst d
    rw [take_self,OrderIso.symm_apply_apply]
    exact (travelTree A L).under_self v
  · have hlt:d<(numbering A L v).1.val:=by omega
    have hv:v≠0:=by
      intro he
      subst v
      rw [numbering_zero] at hlt
      exact Nat.not_lt_zero _ hlt
    have hne:v≠(numbering A L).symm (take A L (numbering A L v) d hd):=by
      intro hh
      have hhh:=congrArg (fun u=>(numbering A L u).1.val) hh
      rw [OrderIso.apply_symm_apply] at hhh
      exact he hhh.symm
    rw [Rounding.Tree.under,ite_eq_right hne,dite_eq_right hv]
    have hp:d≤(numbering A L ((travelTree A L).parent v)).1.val:=by
      rw [numbering_parent,parent_depth A L _ (by omega)]
      omega
    have ht:take A L (numbering A L ((travelTree A L).parent v)) d hp=
        take A L (numbering A L v) d hd:=by
      simpa only [numbering_parent] using take_parent A L (numbering A L v) hlt
    rw [←ht]
    exact take_under ((travelTree A L).parent v) d hp
termination_by v.val
decreasing_by exact (travelTree A L).lower v hv

end KServer.PrefixTree

end


/-! Cumulative parked mass in the actual prefix cut is bounded by posterior
mass of the 67-radius ball. Selection can depend on the completed state. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable (A:Type) [Fintype A] (L:ℕ)

omit [Fintype A] in
lemma eq_of_common_hit {Y:Type} (maps:ℕ→Y→A) (u v:Vertex A L)
    (hd:u.1.val=v.1.val) (y:Y) (hu:HierarchyCounts.hit maps u.2 y)
    (hv:HierarchyCounts.hit maps v.2 y):u=v:=by
  rcases u with ⟨j,f⟩
  rcases v with ⟨j',g⟩
  have hj:j=j':=Fin.ext hd
  subst j'
  congr
  funext i
  exact (hu i).symm.trans (hv i)

variable {Ω Y:Type} [Fintype Ω] [Fintype Y] [MetricSpace Y] {k:ℕ} {w:Ω→ℝ}
variable (hw:∀ ω,0≤w ω) (H:ℕ→Ω→ℕ)
variable (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
variable (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y) (hk:1≤(k:ℝ))

theorem park_ball_capacity (hwpos:∀ ω,0<w ω) (t:ℕ) (ω:Ω)
    (hm:∀ ρ,H t ρ=H t ω→maps t ρ=maps t ω)
    (S:Finset (Fin (Fintype.card (Vertex A L)))) (d:ℕ) (y:Y) (r:ℝ)
    (hd:∀ u∈S,d≤(numbering A L u).1.val)
    (hwit:∀ u∈S,∃ z∈region A L maps t ω u,dist y z≤27*r)
    (hdiam:∀ v:Fin (Fintype.card (Vertex A L)),(numbering A L v).1.val=d→
      ∀ a∈region A L maps t ω v,∀ b∈region A L maps t ω v,dist a b≤40*r):
    (∑ u∈S,(travelTree A L).park (Q A L hw H hr maps q hk t ω) u)≤
      72*Rounding.countingMass (PosteriorCounting.measure (w:=w) (H t) (q t) ω)
        (univ.filter (fun z=>dist y z≤67*r)):=by
  let anc:S→Fin (Fintype.card (Vertex A L)):=fun u=>
    (numbering A L).symm (take A L (numbering A L u.val) d (hd u.val u.property))
  let F:Finset (Fin (Fintype.card (Vertex A L))):=univ.image anc
  have hdepth:∀ v∈F,(numbering A L v).1.val=d:=by
    intro v hv
    obtain ⟨u,_,rfl⟩:=mem_image.mp hv
    simp only [anc,OrderIso.apply_symm_apply,take]
  have hcover:∀ u∈S,∃ v∈F,(travelTree A L).under v u=true:=by
    intro u hu
    refine ⟨anc ⟨u,hu⟩,mem_image.mpr ⟨⟨u,hu⟩,mem_univ _,rfl⟩,?_⟩
    exact take_under A L u d (hd u hu)
  have hdisj:Set.PairwiseDisjoint (↑F) (region A L maps t ω):=by
    intro u hu v hv hne
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    apply hne
    apply (numbering A L).injective
    exact eq_of_common_hit A L (maps t ω) _ _ ((hdepth u hu).trans (hdepth v hv).symm) z
      (mem_filter.mp hz).2 (mem_filter.mp hz').2
  have hwitness:∀ v∈F,∃ z∈region A L maps t ω v,dist y z≤27*r:=by
    intro v hv
    obtain ⟨u,_,rfl⟩:=mem_image.mp hv
    obtain ⟨z,hz,hclose⟩:=hwit u.val u.property
    refine ⟨z,?_,hclose⟩
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    rw [show numbering A L (anc u)=take A L (numbering A L u.val) d (hd u.val u.property) from
      OrderIso.apply_symm_apply _ _]
    exact hit_take A L (maps t ω) _ d _ z (mem_filter.mp hz).2
  exact (travelTree A L).geometric_park_capacity _
    (park_nonneg A L hw H hr maps q hk hwpos t ω) S F hcover (region A L maps t ω)
    _ (PosteriorCounting.measure_nonneg hw (H t) (q t) ω) (by norm_num) y
    (fun v _=>Q_mass A L hw H hr maps q hk hwpos t ω hm v) hdisj hwitness
    (fun v hv=>hdiam v (hdepth v hv))

end KServer.PrefixTree

end


/-! Literal variation of all parks, including the root park, with the exact
parent-edge factor. No metric or rounding movement estimate is assumed. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.Rounding
attribute [local instance] Classical.propDecidable Classical.decEq
variable {n:ℕ} [NeZero n]

lemma Tree.park_difference (T:Tree n) (q q':Fin n→ℝ) (v:Fin n):
    |T.park q' v-T.park q v|≤|q' v-q v|+∑ u:T.Child v,|q' u.val-q u.val|:=by
  have hh: T.park q' v-T.park q v=(q' v-q v)-∑ u:T.Child v,(q' u.val-q u.val):=by
    rw [sum_sub_distrib]
    unfold Tree.park
    ring
  rw [hh]
  exact (abs_sub _ _).trans (add_le_add (le_refl _) (abs_sum_le_sum_abs _ _))

lemma Tree.weighted_park_variation (T:Tree n) (q q' R:Fin n→ℝ)
    (hR:∀ v,0≤R v) (hroot:q' 0=q 0) {τ:ℝ} (hτ:0<τ)
    (hgeom:∀ v,v≠0→R (T.parent v)=τ*R v):
    (∑ v,R v*|T.park q' v-T.park q v|)≤
      (1+1/τ)*(∑ v,R (T.parent v)*|q' v-q v|):=by
  let f:=fun v=>|q' v-q v|
  have hf:f 0=0:=by simp [f,hroot]
  have he:(∑ v,R v*f v)=(1/τ)*(∑ v,R (T.parent v)*f v):=by
    rw [mul_sum]
    apply sum_congr rfl
    intro v _
    by_cases hv:v=0
    · simp [hv,hf]
    · rw [hgeom v hv]
      field_simp
  have hb:=sum_le_sum (s:=univ) (fun v (_:v∈univ)=>
    mul_le_mul_of_nonneg_left (T.park_difference q q' v) (hR v))
  simp only [mul_add,sum_add_distrib] at hb
  change _≤(∑ v,R v*f v)+(∑ v,R v*∑ u:T.Child v,f u.val) at hb
  rw [T.weighted_children R f hf,he] at hb
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  ring
end KServer.Rounding

end


/-! Fixed last-key bands in the complete prefix tree. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable (A:Type) [Fintype A] (L:ℕ)

lemma band_nonneg {p:Node A L→ℝ} (hp:∀ v,0≤p v) (d:ℕ) (a:A):
    0≤bandMass A L p d a:=sum_nonneg (fun v _=>hp v)

lemma band_key {Y:Type} (maps:ℕ→Y→A) (d:ℕ) (a:A) {v:Node A L}
    (hv:v∈band A L d a) (y:Y) (hy:HierarchyCounts.hit maps (numbering A L v).2 y):
    maps d y=a:=by
  obtain ⟨hd,ha⟩:=(mem_filter.mp hv).2
  have hp:0<depth A L v:=by omega
  simp only [lastKey,dite_eq_left hp,Option.some.injEq] at ha
  have hi:=hy ⟨depth A L v-1,by change depth A L v-1<depth A L v; omega⟩
  dsimp only at hi
  have he:depth A L v-1=d:=by omega
  rw [←ha,←hi,he]

lemma band_depth (d:ℕ) (a:A) {v:Node A L} (hv:v∈band A L d a):
    (numbering A L v).1.val=d+1:=(mem_filter.mp hv).2.1

lemma band_disjoint {Y:Type} [Fintype Y] (maps:ℕ→Y→A) (d:ℕ) (a:A):
    Set.PairwiseDisjoint (↑(band A L d a))
      (fun v=>univ.filter (HierarchyCounts.hit maps (numbering A L v).2)):=by
  intro u hu v hv hne
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  apply hne
  apply (numbering A L).injective
  exact eq_of_common_hit A L maps _ _ ((band_depth A L d a hu).trans (band_depth A L d a hv).symm) z
    (mem_filter.mp hz).2 (mem_filter.mp hz').2

variable {Ω Y:Type} [Fintype Ω] [Fintype Y] [MetricSpace Y] {k:ℕ} {w:Ω→ℝ}
variable (hw:∀ ω,0≤w ω) (H:ℕ→Ω→ℕ)
variable (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
variable (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y) (hk:1≤(k:ℝ))

omit [MetricSpace Y] in
lemma band_capacity (hwpos:∀ ω,0<w ω) (t:ℕ) (ω:Ω)
    (hm:∀ ρ,H t ρ=H t ω→maps t ρ=maps t ω) (d:ℕ) (a:A):
    bandMass A L ((travelTree A L).park (Q A L hw H hr maps q hk t ω)) d a≤
      72*Rounding.countingMass (PosteriorCounting.measure (w:=w) (H t) (q t) ω)
        (univ.filter (fun y=>maps t ω d y=a)):=by
  have h:=sum_le_sum (s:=band A L d a) (fun v (_:v∈band A L d a)=>
    (park_le_Q A L hw H hr maps q hk hwpos t ω v).trans
      (Q_mass A L hw H hr maps q hk hwpos t ω hm v))
  change bandMass A L _ d a≤∑ v∈band A L d a,72*Rounding.countingMass
    (PosteriorCounting.measure (w:=w) (H t) (q t) ω) (region A L maps t ω v) at h
  rw [←mul_sum] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Rounding.disjoint_counting_mass (PosteriorCounting.measure_nonneg hw (H t) (q t) ω)
    (band_disjoint A L (maps t ω) d a)
  intro v hv y hy
  exact mem_filter.mpr ⟨mem_univ _,band_key A L (maps t ω) d a hv y (mem_filter.mp hy).2⟩

end KServer.PrefixTree

end


/-! Literal all-key persistent size references on the adapted complete map. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.KeyReferences
open RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Ω A Y:Type} [Fintype Ω] [Fintype A] [Fintype Y] {k:ℕ} {w:Ω→ℝ}
variable (H:ℕ→Ω→ℕ) (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y)

omit [Fintype A] in
lemma mass_eq (d:ℕ) (a:A) (t:ℕ) (ω:Ω)
    (hm:∀ ρ,H t ρ=H t ω→maps t ρ=maps t ω):
    (∑ y∈univ.filter (fun y=>maps t ω d y=a),PosteriorCounting.measure (w:=w) (H t) (q t) ω y)=
      posterior w (H t) (count maps q d a t) ω:=by
  have he:=PosteriorCounting.conditional_integral (w:=w) (H t) (q t) ω
    (fun ρ y=>if maps t ρ d y=a then (1:ℝ) else 0) (fun ρ h=>by funext y; rw [hm ρ h])
  unfold KeyReferences.count
  simpa only [sum_filter,mul_ite,mul_one,mul_zero] using he

variable (hw:∀ ω,0≤w ω) (hwpos:∀ ω,0<w ω)
variable (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)

include hw hwpos hr
omit [Fintype A] [Fintype Y] in
lemma size_range (d:ℕ) (a:A) (t:ℕ) (ω:Ω):size (w:=w) H maps q d a t ω∈Set.Icc 1 ((k:ℝ)+1):=
  (process H maps q hw hwpos hr d a).range t ω

omit [Fintype A] [Fintype Y] in
lemma reference_range (d:ℕ) (a:A) (t:ℕ) (ω:Ω):
    reference (w:=w) H maps q d a t ω∈Set.Icc 1 ((k:ℝ)+1):=
  KeySizeTracking.held_range (size_range H maps q hw hwpos hr d a) t ω

omit [Fintype A] [Fintype Y] in
lemma reference_comparison (d:ℕ) (a:A) (t:ℕ) (ω:Ω):
    (5/6:ℝ)*reference (w:=w) H maps q d a t ω≤ size (w:=w) H maps q d a t ω ∧
      size (w:=w) H maps q d a t ω≤ (6/5:ℝ)*reference (w:=w) H maps q d a t ω:=
  KeySizeTracking.held_accurate (fun t ω=>(by linarith [(size_range H maps q hw hwpos hr d a t ω).1])) t ω

omit [Fintype A] [Fintype Y] in
lemma reference_adapted (d:ℕ) (a:A) (t:ℕ):Adapted (H t) (reference (w:=w) H maps q d a t):=
  KeySizeTracking.held_adapted (process H maps q hw hwpos hr d a) t

omit [Fintype A] [Fintype Y] in
lemma refresh_budget (hw1:∑ ω,w ω=1) (d:ℕ) (a:A) (T:ℕ):
    (∑ t∈range T,avg w (KeySizeTracking.refreshCost (size (w:=w) H maps q d a) t))≤
      144*(1+Real.log ((k:ℝ)+1))*(∑ t∈range T,avg w (fun ω=>|count maps q d a (t+1) ω-count maps q d a t ω|))+
        288*((k:ℝ)+1)*(1+(1+Real.log ((k:ℝ)+1))):=
  PosteriorSizes.refresh_budget hw hwpos hw1 (Nat.cast_nonneg k) H hr
    (count maps q d a) (count_range maps q d a) T

end KServer.KeyReferences

end


/- Height-independent scale-capacity estimates use summation by parts rather than dyadic grouping. -/


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ParkedCoefficients

lemma tail_zero (b : ℕ → ℝ) (n : ℕ) : tail b n n=0 := by simp [tail]
lemma tail_step (b : ℕ → ℝ) {n i : ℕ} (hi : i < n) :
    tail b n i=b i+tail b n (i+1) := by
  unfold tail
  exact Finset.sum_eq_sum_Ico_succ_bot hi b

lemma logarithmic_increment {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b-a)/b ≤ Real.log b-Real.log a := by
  have hb := ha.trans_le hab
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne'] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

lemma summation_by_parts (b A : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ range n, b i/A i) = tail b n 0/A 0 +
      ∑ i ∈ range n, tail b n (i+1)*(1/A (i+1)-1/A i) := by
  have hstep : ∀ i ∈ range n, b i/A i =
      tail b n i/A i-tail b n (i+1)/A (i+1)+
      tail b n (i+1)*(1/A (i+1)-1/A i) := by
    intro i hi
    rw [tail_step b (mem_range.mp hi)]
    ring
  simp_rw [Finset.sum_congr rfl hstep, sum_add_distrib,
    Finset.sum_range_sub',tail_zero,zero_div,sub_zero]

/-- Positive tail capacities control reciprocal-weighted mass logarithmically.
The extra endpoint A n may be chosen as A (n-1), or any smaller positive value. -/
theorem capacity_log_sum {b A : ℕ → ℝ} {n : ℕ} {C K : ℝ}
    (hC : 0 ≤ C) (hA : ∀ i ≤ n, A i ∈ Set.Icc 1 K)
    (hdec : ∀ i < n, A (i+1) ≤ A i)
    (hcap : ∀ i ≤ n, tail b n i ≤ C*A i) :
    ∑ i ∈ range n, b i/A i ≤ C*(1+Real.log K) := by
  have hp i (hi : i ≤ n) : 0 < A i := by linarith [(hA i hi).1]
  have ht : ∀ i ∈ range n, tail b n (i+1)*(1/A (i+1)-1/A i) ≤
      C*(Real.log (A i)-Real.log (A (i+1))) := by
    intro i hi
    have hin := mem_range.mp hi
    have h1 : 0 ≤ 1/A (i+1)-1/A i := sub_nonneg.mpr
      (one_div_le_one_div_of_le (hp (i+1) (by omega)) (hdec i hin))
    calc _ ≤ C*A (i+1)*(1/A (i+1)-1/A i) :=
          mul_le_mul_of_nonneg_right (hcap (i+1) (by omega)) h1
         _ = C*((A i-A (i+1))/A i) := by
          field_simp [(hp i (by omega)).ne',(hp (i+1) (by omega)).ne']
         _ ≤ _ := mul_le_mul_of_nonneg_left
          (logarithmic_increment (hp (i+1) (by omega)) (hdec i hin)) hC
  have h0 : tail b n 0/A 0 ≤ C := (div_le_iff₀ (hp 0 (by omega))).mpr (hcap 0 (by omega))
  rw [summation_by_parts]
  have hs := sum_le_sum ht
  rw [←mul_sum,Finset.sum_range_sub'] at hs
  have hlog0 := Real.log_le_log (hp 0 (by omega)) (hA 0 (by omega)).2
  have hlogn := Real.log_nonneg (hA n le_rfl).1
  have hh := mul_le_mul_of_nonneg_left (show Real.log (A 0)-Real.log (A n) ≤ Real.log K by linarith) hC
  linarith

lemma tail_mono {b c : ℕ → ℝ} {n i : ℕ} (h : ∀ j < n, b j ≤ c j) :
    tail b n i ≤ tail c n i := by
  apply sum_le_sum
  intro j hj
  exact h j (mem_Ico.mp hj).2

/-- Exact abstract form of §08's geometric estimate. b is selected parked mass,
d its held key size, B=1+mass(B(y,r)), A=1+mass(B(y,67r)). The assumptions here
are pointwise capacity data, not stochastic or policy-existence interfaces. -/
theorem park_coefficients {b d A B : ℕ → ℝ} {n : ℕ} {C K ρ R L : ℝ}
    (hC : 0 ≤ C) (hρ : 0 < ρ) (hR : 0 ≤ R)
    (hb : ∀ i < n, 0 ≤ b i) (hd : ∀ i < n, 0 < d i)
    (hA : ∀ i ≤ n, A i ∈ Set.Icc 1 K)
    (hB : ∀ i < n, B i ∈ Set.Icc 1 (A i))
    (hdec : ∀ i < n, A (i+1) ≤ A i)
    (hcap : ∀ i ≤ n, tail b n i ≤ C*A i)
    (hnorm : ∀ i < n, B i ≤ ρ*d i)
    (hbound : ∀ i < n, b i/d i ≤ R)
    (hlog : ∑ i ∈ range n, Real.log (A i/B i) ≤ L) :
    ∑ i ∈ range n, b i/d i ≤ R*L/Real.log 2+2*ρ*C*(1+Real.log K) := by
  let good : ℕ → ℝ := fun i => if A i ≤ 2*B i then b i else 0
  have hpA i (hi : i ≤ n) : 0 < A i := by linarith [(hA i hi).1]
  have hpB i (hi : i < n) : 0 < B i := by linarith [(hB i hi).1]
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hg : ∀ i < n, good i ≤ b i := by
    intro i hi; dsimp [good]; split_ifs <;> [rfl; exact hb i hi]
  have hgc := capacity_log_sum hC hA hdec (fun i hi =>
    (tail_mono hg).trans (hcap i hi))
  have hstep : ∀ i ∈ range n, b i/d i ≤
      R/Real.log 2*Real.log (A i/B i)+2*ρ*(good i/A i) := by
    intro i hi
    have hin := mem_range.mp hi
    have hln : 0 ≤ Real.log (A i/B i) := Real.log_nonneg
      ((one_le_div (hpB i hin)).mpr (hB i hin).2)
    by_cases hh : A i ≤ 2*B i
    · have hrad : A i ≤ 2*ρ*d i := hh.trans (by nlinarith [hnorm i hin])
      have hw : b i/d i ≤ 2*ρ*(b i/A i) := by
        apply (div_le_iff₀ (hd i hin)).mpr
        have hm := mul_le_mul_of_nonneg_left hrad (hb i hin)
        have he : 2*ρ*(b i/A i)*d i = (b i*(2*ρ*d i))/A i := by ring
        rw [he]
        apply (le_div_iff₀ (hpA i (by omega))).mpr
        simpa [mul_assoc] using hm
      dsimp only [good]
      rw [ite_eq_left hh]
      exact hw.trans (le_add_of_nonneg_left (mul_nonneg (div_nonneg hR h2.le) hln))
    · have hratio : 2 ≤ A i/B i := (le_div_iff₀ (hpB i hin)).mpr (le_of_not_ge hh)
      have hln2 := Real.log_le_log (by norm_num : (0:ℝ) < 2) hratio
      have ht : R ≤ R/Real.log 2*Real.log (A i/B i) := by
        have h := mul_le_mul_of_nonneg_left hln2 (div_nonneg hR h2.le)
        simpa [div_mul_cancel₀ R h2.ne'] using h
      dsimp only [good]
      rw [ite_eq_right hh,zero_div,mul_zero,add_zero]
      exact (hbound i hin).trans ht
  have hs := sum_le_sum hstep
  rw [sum_add_distrib,←mul_sum,←mul_sum] at hs
  have hlu := mul_le_mul_of_nonneg_left hlog (div_nonneg hR h2.le)
  have hgu := mul_le_mul_of_nonneg_left hgc (by positivity : 0 ≤ 2*ρ)
  calc _ ≤ R/Real.log 2*L+2*ρ*(C*(1+Real.log K)) := hs.trans (add_le_add hlu hgu)
       _ = _ := by ring

/-- The exact fixed-offset telescope; scales shorter than the offset are included. -/
lemma scale_log_telescope {A B : ℕ → ℝ} {n p : ℕ} {K : ℝ}
    (hK : 1 ≤ K) (hA : ∀ i < n, A i ∈ Set.Icc 1 K)
    (hB : ∀ i < n, B i ∈ Set.Icc 1 K)
    (hshift : ∀ i < n, p ≤ i → A i ≤ B (i-p)) :
    ∑ i ∈ range n, Real.log (A i/B i) ≤ (p:ℝ)*Real.log K := by
  have hlogK := Real.log_nonneg hK
  have hlogB : ∀ i < n, 0 ≤ Real.log (B i) := fun i hi => Real.log_nonneg (hB i hi).1
  have hrewrite : (∑ i ∈ range n, Real.log (A i/B i)) =
      (∑ i ∈ range n, Real.log (A i))-(∑ i ∈ range n, Real.log (B i)) := by
    rw [←sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    have ha : 0 < A i := by linarith [(hA i (mem_range.mp hi)).1]
    have hb : 0 < B i := by linarith [(hB i (mem_range.mp hi)).1]
    exact Real.log_div ha.ne' hb.ne'
  rw [hrewrite]
  by_cases hpn : p ≤ n
  · have hfirst : ∑ i ∈ range p, Real.log (A i) ≤ (p:ℝ)*Real.log K := by
      calc _ ≤ ∑ _i ∈ range p, Real.log K := by
            apply sum_le_sum
            intro i hi
            have hin : i < n := (mem_range.mp hi).trans_le hpn
            exact Real.log_le_log (by linarith [(hA i hin).1]) (hA i hin).2
           _ = _ := by simp
    have hlast : ∑ i ∈ range (n-p), Real.log (A (p+i)) ≤
        ∑ i ∈ range (n-p), Real.log (B i) := by
      apply sum_le_sum
      intro i hi
      have hin : p+i < n := by have := mem_range.mp hi; omega
      have hh := hshift (p+i) hin (by omega)
      simp only [Nat.add_sub_cancel_left] at hh
      exact Real.log_le_log (by linarith [(hA (p+i) hin).1]) hh
    have htail : ∑ i ∈ range (n-p), Real.log (B i) ≤ ∑ i ∈ range n, Real.log (B i) := by
      apply sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
      intro i hi _
      exact hlogB i (mem_range.mp hi)
    have he := Finset.sum_range_add (fun i => Real.log (A i)) p (n-p)
    rw [Nat.add_sub_of_le hpn] at he
    linarith
  · have hupper : ∑ i ∈ range n, Real.log (A i) ≤ (n:ℝ)*Real.log K := by
      calc _ ≤ ∑ _i ∈ range n, Real.log K := by
            apply sum_le_sum
            intro i hi
            exact Real.log_le_log (by linarith [(hA i (mem_range.mp hi)).1]) (hA i (mem_range.mp hi)).2
           _ = _ := by simp
    have hnon := sum_nonneg (fun i hi => hlogB i (mem_range.mp hi))
    have hnp : (n:ℝ) ≤ p := by exact_mod_cast (le_of_not_ge hpn)
    nlinarith

/-- Source offset p=7 gives an absolute height-independent bound. The capacity
estimate is slightly relaxed from C*(A-1) to C*A, but the conclusion is the exact
O(1+log K) needed and the stronger source capacity implies this premise. -/
theorem seven_scale_park_coefficients {b d A B : ℕ → ℝ} {n : ℕ} {C K ρ R : ℝ}
    (hC : 0 ≤ C) (hρ : 0 < ρ) (hR : 0 ≤ R) (hK : 1 ≤ K)
    (hb : ∀ i < n, 0 ≤ b i) (hd : ∀ i < n, 0 < d i)
    (hA : ∀ i ≤ n, A i ∈ Set.Icc 1 K)
    (hB : ∀ i < n, B i ∈ Set.Icc 1 (A i))
    (hdec : ∀ i < n, A (i+1) ≤ A i)
    (hcap : ∀ i ≤ n, tail b n i ≤ C*(A i-1))
    (hnorm : ∀ i < n, B i ≤ ρ*d i)
    (hbound : ∀ i < n, b i/d i ≤ R)
    (hshift : ∀ i < n, 7 ≤ i → A i ≤ B (i-7)) :
    ∑ i ∈ range n, b i/d i ≤ (7*R/Real.log 2+2*ρ*C)*(1+Real.log K) := by
  have hlog := scale_log_telescope hK (fun i hi => hA i hi.le)
    (fun i hi => ⟨(hB i hi).1,(hB i hi).2.trans (hA i hi.le).2⟩) hshift
  have h := park_coefficients hC hρ hR hb hd hA hB hdec
    (fun i hi => (hcap i hi).trans (by nlinarith)) hnorm hbound hlog
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr := div_nonneg hR h2.le
  have hdiff : R*((7:ℕ):ℝ)*Real.log K/Real.log 2 + 2*ρ*C*(1+Real.log K) ≤
      (7*R/Real.log 2+2*ρ*C)*(1+Real.log K) := by
    calc _ = (7*R/Real.log 2+2*ρ*C)*(1+Real.log K)-7*(R/Real.log 2) := by norm_num; ring
         _ ≤ _ := sub_le_self _ (by positivity)
  calc _ ≤ R*((7:ℕ)*Real.log K)/Real.log 2+2*ρ*C*(1+Real.log K) := h
       _ = R*((7:ℕ):ℝ)*Real.log K/Real.log 2+2*ρ*C*(1+Real.log K) := by ring
       _ ≤ _ := hdiff

end KServer.ParkedCoefficients

namespace KServer.ParkedCoefficients
section MetricScales
variable {Y : Type*} [MetricSpace Y] [Fintype Y]

lemma ballMass_nonneg {μ : Y → ℝ} (hμ : ∀ z, 0 ≤ μ z) (y : Y) (r : ℝ) :
    0 ≤ ballMass μ y r := by
  apply sum_nonneg
  intro z _
  split_ifs <;> [exact hμ z; rfl]

lemma ballMass_total {μ : Y → ℝ} (hμ : ∀ z, 0 ≤ μ z) (y : Y) (r : ℝ) :
    ballMass μ y r ≤ ∑ z, μ z := by
  apply sum_le_sum
  intro z _
  split_ifs <;> [rfl; exact hμ z]

lemma ballMass_mono {μ : Y → ℝ} (hμ : ∀ z, 0 ≤ μ z) (y : Y)
    {r s : ℝ} (hrs : r ≤ s) : ballMass μ y r ≤ ballMass μ y s := by
  apply sum_le_sum
  intro z _
  split_ifs with h h' h' <;> first | rfl | exact hμ z | (exfalso; exact h' (h.trans hrs))

lemma radius_antitone {r₀ τ : ℝ} (hr : 0 ≤ r₀) (hτ : 1 ≤ τ) :
    Antitone (radius r₀ τ) := by
  intro i j hij
  have hp : 0 < τ := by linarith
  exact div_le_div_of_nonneg_left hr (pow_pos hp i) (pow_le_pow_right₀ hτ hij)

lemma radius_seven {r₀ τ : ℝ} (hr : 0 ≤ r₀) (hτ : 2 ≤ τ) {i : ℕ} (hi : 7 ≤ i) :
    67*radius r₀ τ i ≤ radius r₀ τ (i-7) := by
  have hp : 0 < τ := by linarith
  have hpow : (67:ℝ) ≤ τ^7 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hτ 7
    norm_num at hh
    linarith
  unfold radius
  rw [←mul_div_assoc]
  apply (div_le_div_iff₀ (pow_pos hp i) (pow_pos hp (i-7))).mpr
  have he : τ^i=τ^(i-7)*τ^7 := by rw [←pow_add,Nat.sub_add_cancel hi]
  rw [he]
  have hm := mul_le_mul_of_nonneg_left hpow (mul_nonneg hr (pow_nonneg hp.le (i-7)))
  nlinarith

/-- The pointwise coefficient bound now for the actual metric ball masses and
geometric scales of §07-08, not an assumed logarithmic telescope. b is zero on
unselected levels. Cumulative subcapacity is supplied by Tree.geometric_park_capacity;
held normalization and individual domination are the exact local invariants. -/
theorem metric_park_coefficients {μ : Y → ℝ} (hμ : ∀ z, 0 ≤ μ z)
    (y : Y) {k C ρ R r₀ τ : ℝ} {n : ℕ} {b d : ℕ → ℝ}
    (hmass : ∑ z, μ z=k) (hC : 0 ≤ C) (hρ : 0 < ρ) (hR : 0 ≤ R)
    (hr : 0 ≤ r₀) (hτ : 2 ≤ τ)
    (hb : ∀ i < n, 0 ≤ b i) (hd : ∀ i < n, 0 < d i)
    (hcap : ∀ i ≤ n, tail b n i ≤ C*ballMass μ y (67*radius r₀ τ i))
    (hnorm : ∀ i < n, 1+ballMass μ y (radius r₀ τ i) ≤ ρ*d i)
    (hbound : ∀ i < n, b i/d i ≤ R) :
    ∑ i ∈ range n, b i/d i ≤ (7*R/Real.log 2+2*ρ*C)*(1+Real.log (k+1)) := by
  let A := fun i => 1+ballMass μ y (67*radius r₀ τ i)
  let B := fun i => 1+ballMass μ y (radius r₀ τ i)
  have hk : 0 ≤ k := by rw [←hmass]; exact sum_nonneg (fun z _ => hμ z)
  have hrad : ∀ i, 0 ≤ radius r₀ τ i := fun i => div_nonneg hr (pow_nonneg (by linarith) i)
  have hAB : ∀ i, B i ≤ A i := by
    intro i
    dsimp [A,B]
    have h := ballMass_mono hμ y (show radius r₀ τ i ≤ 67*radius r₀ τ i by nlinarith [hrad i])
    linarith
  have hA : ∀ i ≤ n, A i ∈ Set.Icc 1 (k+1) := by
    intro i _
    have hn := ballMass_nonneg hμ y (67*radius r₀ τ i)
    have ht := ballMass_total hμ y (67*radius r₀ τ i)
    rw [hmass] at ht
    dsimp [A]
    constructor <;> linarith
  have hB : ∀ i < n, B i ∈ Set.Icc 1 (A i) := by
    intro i _
    exact ⟨by dsimp [B]; linarith [ballMass_nonneg hμ y (radius r₀ τ i)],hAB i⟩
  have hdec : ∀ i < n, A (i+1) ≤ A i := by
    intro i _
    have hh := radius_antitone hr (show 1 ≤ τ by linarith) (show i ≤ i+1 by omega)
    have hm := ballMass_mono hμ y (show 67*radius r₀ τ (i+1) ≤ 67*radius r₀ τ i by linarith)
    dsimp [A]; linarith
  have hshift : ∀ i < n, 7 ≤ i → A i ≤ B (i-7) := by
    intro i _ hi
    have hm := ballMass_mono hμ y (radius_seven hr hτ hi)
    dsimp [A,B]; linarith
  apply seven_scale_park_coefficients hC hρ hR (by linarith) hb hd hA hB hdec _ hnorm hbound hshift
  intro i hi
  simpa [A] using hcap i hi

end MetricScales
end KServer.ParkedCoefficients

end


/-! All finer selected last-key bands form a literal prefix cut. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable (A:Type) [Fintype A] (L:ℕ)

lemma selected_depth (sel:ℕ→Option A) {d:ℕ} {v:Node A L}
    (hv:v∈selectedBand A L sel d):depth A L v=d+1:=by
  unfold selectedBand at hv
  cases he:sel d with
  | none=>rw [he] at hv; exact (notMem_empty _ hv).elim
  | some a=>rw [he] at hv; exact band_depth A L d a hv

lemma selected_disjoint (sel:ℕ→Option A) (F:Finset ℕ):
    Set.PairwiseDisjoint (↑F) (selectedBand A L sel):=by
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro v hi hj
  have hd:=selected_depth A L sel hi
  have hd':=selected_depth A L sel hj
  omega

lemma selected_tail (p:Node A L→ℝ) (sel:ℕ→Option A) (j:ℕ):
    ParkedCoefficients.tail (selectedMass A L p sel) L j=
      ∑ v∈(Ico j L).biUnion (selectedBand A L sel),p v:=by
  rw [sum_biUnion (selected_disjoint A L sel (Ico j L))]
  rfl

variable {Ω Y:Type} [Fintype Ω] [Fintype Y] [MetricSpace Y] {k:ℕ} {w:Ω→ℝ}
variable (hw:∀ ω,0≤w ω) (H:ℕ→Ω→ℕ)
variable (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
variable (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y) (hk:1≤(k:ℝ))

theorem selected_capacity (hwpos:∀ ω,0<w ω) (t:ℕ) (ω:Ω)
    (hm:∀ ρ,H t ρ=H t ω→maps t ρ=maps t ω)
    (sel:ℕ→Option A) (y:Y) {R τ:ℝ} (hR:0≤R) (hτ:2≤τ)
    (hclose:∀ i a,sel i=some a→∀ z,maps t ω i z=a→
      dist y z≤27*ParkedCoefficients.radius R τ i)
    (hcells:∀ i a b,maps t ω i a=maps t ω i b→
      dist a b≤40*ParkedCoefficients.radius R τ i) (j:ℕ):
    ParkedCoefficients.tail
      (selectedMass A L ((travelTree A L).park (Q A L hw H hr maps q hk t ω)) sel) L j≤
      72*ParkedCoefficients.ballMass (PosteriorCounting.measure (w:=w) (H t) (q t) ω) y
        (67*ParkedCoefficients.radius R τ j):=by
  let p:Node A L→ℝ:=(travelTree A L).park (Q A L hw H hr maps q hk t ω)
  let F:Finset (Node A L):=(Ico j L).biUnion (selectedBand A L sel)
  let S:=F.filter (fun v=>0<p v)
  have hn:∀ v,0≤p v:=park_nonneg A L hw H hr maps q hk hwpos t ω
  have he:(∑ v∈F,p v)=(∑ v∈S,p v):=by
    symm
    apply sum_subset (filter_subset _ _)
    intro v hv hvs
    have hh:¬0<p v:=by simpa only [S,mem_filter,hv,true_and] using hvs
    exact le_antisymm (le_of_not_gt hh) (hn v)
  rw [selected_tail]
  change (∑ v∈F,p v)≤_
  rw [he]
  have hd:∀ v∈S,j+1≤(numbering A L v).1.val:=by
    intro v hv
    obtain ⟨i,hi,hvi⟩:=mem_biUnion.mp (mem_filter.mp hv).1
    have hvd:=selected_depth A L sel hvi
    have hij:=(mem_Ico.mp hi).1
    change j+1≤depth A L v
    omega
  have hwi:∀ v∈S,∃ z∈region A L maps t ω v,
      dist y z≤27*ParkedCoefficients.radius R τ j:=by
    intro v hv
    obtain ⟨i,hi,hvi⟩:=mem_biUnion.mp (mem_filter.mp hv).1
    have hp:0<Q A L hw H hr maps q hk t ω v:=
      lt_of_lt_of_le (mem_filter.mp hv).2 (park_le_Q A L hw H hr maps q hk hwpos t ω v)
    obtain ⟨z,hz⟩:=Q_witness A L hw H hr maps q hk hwpos t ω hm v hp
    refine ⟨z,hz,?_⟩
    unfold selectedBand at hvi
    cases hs:sel i with
    | none=>rw [hs] at hvi; exact (notMem_empty _ hvi).elim
    | some a=>
      rw [hs] at hvi
      exact (hclose i a hs z (band_key A L (maps t ω) i a hvi z (mem_filter.mp hz).2)).trans
        (mul_le_mul_of_nonneg_left (ParkedCoefficients.radius_antitone hR (by linarith)
          (mem_Ico.mp hi).1) (by norm_num))
  have hdia:∀ v:Node A L,(numbering A L v).1.val=j+1→
      ∀ a∈region A L maps t ω v,∀ b∈region A L maps t ω v,
        dist a b≤40*ParkedCoefficients.radius R τ j:=by
    intro v hv a ha b hb
    have hj:j<(numbering A L v).1.val:=by omega
    apply hcells
    exact ((mem_filter.mp ha).2 ⟨j,hj⟩).trans ((mem_filter.mp hb).2 ⟨j,hj⟩).symm
  have hh:=park_ball_capacity A L hw H hr maps q hk hwpos t ω hm S (j+1) y
    (ParkedCoefficients.radius R τ j) hd hwi hdia
  simpa only [Rounding.countingMass,ParkedCoefficients.ballMass,sum_filter] using hh

end KServer.PrefixTree

end


/-! The actual prefix parks satisfy the logarithmic coefficient estimate.
The denominator is the held persistent slot size; empty selected levels vanish. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable (A:Type) [Fintype A] (L:ℕ)
variable {Ω Y:Type} [Fintype Ω] [Fintype Y] [MetricSpace Y] {k:ℕ} {w:Ω→ℝ}
variable (hw:∀ ω,0≤w ω) (H:ℕ→Ω→ℕ)
variable (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
variable (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y) (hk:1≤(k:ℝ))

lemma selected_mass_nonneg {p:Node A L→ℝ} (hp:∀ v,0≤p v) (sel:ℕ→Option A) (j:ℕ):
    0 ≤ selectedMass A L p sel j:=sum_nonneg (fun v _=>hp v)

lemma ballMass_eq (μ:Y→ℝ) (y:Y) (r:ℝ):
    ParkedCoefficients.ballMass μ y r=Rounding.countingMass μ (univ.filter (fun z=>dist y z ≤ r)):=by
  simp only [ParkedCoefficients.ballMass,Rounding.countingMass,sum_filter]

theorem selected_coefficients (hwpos:∀ ω,0<w ω) (t:ℕ) (ω:Ω)
    (hm:∀ ρ,H t ρ=H t ω→maps t ρ=maps t ω)
    (sel:ℕ→Option A) (y:Y) (u:ℕ→A→ℝ) {R τ:ℝ} (hR:0≤R) (hτ:2≤τ)
    (hu:∀ i a,0<u i a)
    (hnorm:∀ i a,1+Rounding.countingMass (PosteriorCounting.measure (w:=w) (H t) (q t) ω)
      (univ.filter (fun z=>maps t ω i z=a))≤(6/5:ℝ)*u i a)
    (hclose:∀ i a,sel i=some a→∀ z,maps t ω i z=a→
      dist y z≤27*ParkedCoefficients.radius R τ i)
    (hcontains:∀ i a,sel i=some a→∀ z,dist y z≤ParkedCoefficients.radius R τ i→maps t ω i z=a)
    (hcells:∀ i a b,maps t ω i a=maps t ω i b→
      dist a b≤40*ParkedCoefficients.radius R τ i):
    let p:Node A L→ℝ:=(travelTree A L).park (Q A L hw H hr maps q hk t ω)
    let μ:=PosteriorCounting.measure (w:=w) (H t) (q t) ω
    ∑ i∈range L,selectedMass A L p sel i/
      selectedDenominator A μ y (ParkedCoefficients.radius R τ) sel u i≤
        (7*((6/5:ℝ)*72)/Real.log 2+2*(6/5:ℝ)*72)*(1+Real.log ((k:ℝ)+1)):=by
  dsimp only
  let μ:=PosteriorCounting.measure (w:=w) (H t) (q t) ω
  let p:Node A L→ℝ:=(travelTree A L).park (Q A L hw H hr maps q hk t ω)
  have hμ:∀ z,0≤μ z:=PosteriorCounting.measure_nonneg hw (H t) (q t) ω
  let den:=selectedDenominator A μ y (ParkedCoefficients.radius R τ) sel u
  have hd:∀ i,0<den i:=by
    intro i
    dsimp [den,selectedDenominator]
    cases hs:sel i with
    | none=>simp only; linarith [ParkedCoefficients.ballMass_nonneg hμ y (ParkedCoefficients.radius R τ i)]
    | some a=>exact hu i a
  have hn:∀ i,1+ParkedCoefficients.ballMass μ y (ParkedCoefficients.radius R τ i)≤(6/5:ℝ)*den i:=by
    intro i
    dsimp [den,selectedDenominator]
    cases hs:sel i with
    | none=>simp only; nlinarith [ParkedCoefficients.ballMass_nonneg hμ y (ParkedCoefficients.radius R τ i)]
    | some a=>
      have hb:ParkedCoefficients.ballMass μ y (ParkedCoefficients.radius R τ i)≤
          Rounding.countingMass μ (univ.filter (fun z=>maps t ω i z=a)):=by
        rw [ballMass_eq]
        apply sum_le_sum_of_subset_of_nonneg
        · intro z hz
          exact mem_filter.mpr ⟨mem_univ _,hcontains i a hs z (mem_filter.mp hz).2⟩
        · intro z _ _; exact hμ z
      exact (add_le_add_right hb 1).trans (hnorm i a)
  have hb:∀ i,selectedMass A L p sel i/den i≤(6/5:ℝ)*72:=by
    intro i
    dsimp [selectedMass,selectedBand,den,selectedDenominator]
    cases hs:sel i with
    | none=>simp only [sum_empty,zero_div]; norm_num
    | some a=>
      change bandMass A L p i a/u i a≤(6/5:ℝ)*72
      apply (div_le_iff₀ (hu i a)).mpr
      have hh:=band_capacity A L hw H hr maps q hk hwpos t ω hm i a
      have hn:=hnorm i a
      dsimp only [p] at *
      nlinarith
  exact ParkedCoefficients.metric_park_coefficients hμ y
    (PosteriorCounting.measure_total hw (H t) (q t) ω (hwpos ω))
    (by norm_num : (0:ℝ)≤72) (by norm_num : (0:ℝ)<6/5) (by norm_num : (0:ℝ)≤(6/5:ℝ)*72)
    hR hτ (fun i _=>selected_mass_nonneg A L (park_nonneg A L hw H hr maps q hk hwpos t ω) sel i)
    (fun i _=>hd i) (fun i _=>selected_capacity A L hw H hr maps q hk hwpos t ω hm sel y hR hτ hclose hcells i)
    (fun i _=>hn i) (fun i _=>hb i)
end KServer.PrefixTree

end


/-! Literal allocation and persistent bands on the single positive experiment. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointAllocation
open JointExperiment RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0 < r d) (hk:1≤(k:ℝ))

lemma band_nonneg (t:ℕ) (ω:Ω (k:=k) law hr) (d:ℕ) (a:A (Y:=Y) (k:=k)):
    0≤band s law hr hk t ω d a:=PrefixTree.band_nonneg _ L (park_nonneg s law hr hk t ω) d a

lemma band_capacity (t:ℕ) (ω:Ω (k:=k) law hr) (d:ℕ) (a:A (Y:=Y) (k:=k)):
    band s law hr hk t ω d a≤72*(size s law hr d a t ω-1):=by
  have hm:∀ ρ,history law hr t ρ=history law hr t ω→maps law hr s t ρ=maps law hr s t ω:=
    fun ρ h=>maps_adapted law hr s t ρ ω h
  have hh:=PrefixTree.band_capacity _ L (weight_nonneg law hr) (history law hr) (history_refines law hr)
    (maps law hr s) (hidden law hr s) hk (weight_pos law hr) t ω hm d a
  unfold Rounding.countingMass at hh
  rw [KeyReferences.mass_eq] at hh
  · simpa only [band,park,quota,size,KeyReferences.size,add_sub_cancel_left] using hh
  · exact hm

lemma size_range (d:ℕ) (a:A (Y:=Y) (k:=k)) (t:ℕ) (ω:Ω (k:=k) law hr):
    size s law hr d a t ω∈Set.Icc 1 ((k:ℝ)+1):=
  KeyReferences.size_range (history law hr) (maps law hr s) (hidden law hr s)
    (weight_nonneg law hr) (weight_pos law hr) (history_refines law hr) d a t ω

lemma reference_range (d:ℕ) (a:A (Y:=Y) (k:=k)) (t:ℕ) (ω:Ω (k:=k) law hr):
    reference s law hr d a t ω∈Set.Icc 1 ((k:ℝ)+1):=
  KeySizeTracking.held_range (size_range s law hr d a) t ω

lemma reference_pos (d:ℕ) (a:A (Y:=Y) (k:=k)) (t:ℕ) (ω:Ω (k:=k) law hr):
    0 < reference s law hr d a t ω:=by linarith [(reference_range s law hr d a t ω).1]

lemma reference_comparison (d:ℕ) (a:A (Y:=Y) (k:=k)) (t:ℕ) (ω:Ω (k:=k) law hr):
    (5/6:ℝ)*reference s law hr d a t ω≤ size s law hr d a t ω ∧
      size s law hr d a t ω≤ (6/5:ℝ)*reference s law hr d a t ω:=
  KeyReferences.reference_comparison (history law hr) (maps law hr s) (hidden law hr s)
    (weight_nonneg law hr) (weight_pos law hr) (history_refines law hr) d a t ω

lemma coefficient_bounds (t:ℕ) (ω:Ω (k:=k) law hr) (d:ℕ) (a:A (Y:=Y) (k:=k)):
    band s law hr hk t ω d a/reference s law hr d a t ω∈Set.Icc 0 ((6/5:ℝ)*72):=by
  constructor
  · exact div_nonneg (band_nonneg s law hr hk t ω d a) (reference_pos s law hr d a t ω).le
  · apply (div_le_iff₀ (reference_pos s law hr d a t ω)).mpr
    have hh:=band_capacity s law hr hk t ω d a
    have hn:=(reference_comparison s law hr d a t ω).2
    nlinarith

lemma quota_adapted (t:ℕ) (ω ρ:Ω (k:=k) law hr) (h:history law hr t ω=history law hr t ρ):
    quota s law hr hk t ω=quota s law hr hk t ρ:=by
  funext v
  exact PrefixTree.Q_adapted _ L (weight_nonneg law hr) (history law hr) (history_refines law hr)
    (maps law hr s) (hidden law hr s) hk t v ω ρ h

lemma band_adapted (t:ℕ) (ω ρ:Ω (k:=k) law hr) (h:history law hr t ω=history law hr t ρ):
    band s law hr hk t ω=band s law hr hk t ρ:=by
  unfold band park
  rw [quota_adapted s law hr hk t ω ρ h]

lemma reference_adapted (d:ℕ) (a:A (Y:=Y) (k:=k)) (t:ℕ):
    Adapted (history law hr t) (reference s law hr d a t):=
  KeyReferences.reference_adapted (history law hr) (maps law hr s) (hidden law hr s)
    (weight_nonneg law hr) (weight_pos law hr) (history_refines law hr) d a t

attribute [local instance] OAI.KServer.JointAllocation.keyDecEq
lemma size_mass_joint (d:ℕ) (a:A (Y:=Y) (k:=k)) (t:ℕ) (ω:Ω (k:=k) law hr):
    size s law hr d a t ω=1+∑ y∈univ.filter (fun y=>maps law hr s t ω d y=a),
      PosteriorCounting.measure (w:=weight law hr) (history law hr t) (hidden law hr s t) ω y:=by
  change 1+_=1+_
  exact congrArg (fun z:ℝ=>1+z) (KeyReferences.mass_eq (w:=weight law hr) (history law hr) (maps law hr s)
    (hidden law hr s) d a t ω (fun ρ h=>maps_adapted law hr s t ρ ω h)).symm

lemma size_mass (d:Fin L) (a:A (Y:=Y) (k:=k)) (t:ℕ) (ω:Ω (k:=k) law hr):
    size s law hr d.val a t ω=1+∑ y∈univ.filter (fun y=>LevelKeys.map s law (hr d).le
      ω.val.1 (ω.val.2 d) t y=a),FiniteExperiment.mu s law t ω.val.1 y:=by
  rw [size_mass_joint]
  have hm:maps law hr s t ω d.val=LevelKeys.map s law (hr d).le ω.val.1 (ω.val.2 d) t:=by
    funext y
    simp only [JointExperiment.maps,dite_eq_left d.isLt]
  rw [hm]
  apply congrArg (fun z:ℝ=>1+z)
  apply sum_congr rfl
  intro y _
  exact JointExperiment.measure_eq law hr s t ω y

end KServer.JointAllocation

end


/-! From the exact conditional allocation construction to levelwise hidden-key
changes. This counts both true hidden movement and changing online maps. -/


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
-- module Solutions.OAIQ17_KS.KServer_AnchorTravel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual retained heavy label, not an assumed anchor motion rule. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HeavyAnchorDynamics
open FiniteExperiment Pilot HeavyCenters HeavyLabels HeavySchedule LevelKeys TierProcess
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

lemma key_iff (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (tape:Fin H→FiniteUniform.Outcome Y r)
    (t:ℕ) (x:Y) (a:Pool Y):
    HeavyKeys.key s law r heavyGamma heavyDelta σ tape t x=some a ↔
      ∃ c∈centers s law r heavyGamma heavyDelta σ t,
        (run s law r heavyGamma heavyDelta σ tape t).label c=a ∧
        dist c x≤(run s law r heavyGamma heavyDelta σ tape t).rad c:=by
  have hv:=run_valid s law hr heavyGamma heavyDelta σ tape t
  have hC:=centers_separated s law r heavyGamma heavyDelta σ t
  unfold HeavyKeys.key
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨c,hc,ha⟩
    obtain ⟨hm,hd⟩:=(HeavyKeys.centerKey_some hr hC (fun c hc=>(hv.1 c hc).2)).mp hc
    exact ⟨c,hm,ha,hd⟩
  · rintro ⟨c,hm,ha,hd⟩
    exact ⟨c,(HeavyKeys.centerKey_some hr hC (fun c hc=>(hv.1 c hc).2)).mpr ⟨hm,hd⟩,ha⟩

lemma anchor_eq (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (tape:Fin H→FiniteUniform.Outcome Y r)
    (t:ℕ) {c:Y} {a:Pool Y} (hc:c∈centers s law r heavyGamma heavyDelta σ t)
    (ha:(run s law r heavyGamma heavyDelta σ tape t).label c=a):
    heavyAnchor s law r σ tape t a=c:=by
  have he:∃ b∈centers s law r heavyGamma heavyDelta σ t,
      (run s law r heavyGamma heavyDelta σ tape t).label b=a:=⟨c,hc,ha⟩
  rw [heavyAnchor,dite_eq_left he]
  exact (run_valid s law hr heavyGamma heavyDelta σ tape t).2
    he.choose_spec.1 hc (he.choose_spec.2.trans ha.symm)

lemma common_centers (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (tape:Fin H→FiniteUniform.Outcome Y r)
    (t:Fin H) {a b:Y}
    (ha:a∈centers s law r heavyGamma heavyDelta σ t.val)
    (hb:b∈centers s law r heavyGamma heavyDelta σ (t.val+1))
    (he:(run s law r heavyGamma heavyDelta σ tape t.val).label a=
      (run s law r heavyGamma heavyDelta σ tape (t.val+1)).label b):
    a=b ∨ (b=σ t ∧ 8*r<dist a b ∧ dist a b≤40*r ∧
      Active r heavyGamma heavyDelta (centers s law r heavyGamma heavyDelta σ t.val)
        (mu s law (t.val+1) σ) (σ t)):=by
  have hv:=run_valid s law hr heavyGamma heavyDelta σ tape t.val
  rw [centers_succ,step] at hb
  simp only [run,t.isLt,↓reduceDIte] at he
  split_ifs at hb he with hA
  · by_cases hbx:b=σ t
    · subst b
      simp only [updatedLabel,Function.update_self] at he
      have hov:=existing_match hv.2 ha he.symm
      have hd:=overlap_distance (fun c hc=>(hv.1 c hc).2)
        (FiniteUniform.radius_range hr (tape t)).2 hov
      exact Or.inr ⟨rfl,hA.2 a ha,hd,hA⟩
    · have hbC: b∈centers s law r heavyGamma heavyDelta σ t.val:=
        (mem_filter.mp ((mem_insert.mp hb).resolve_left hbx)).1
      simp only [updatedLabel,Function.update_of_ne hbx] at he
      exact Or.inl (hv.2 ha hbC he)
  · exact Or.inl (hv.2 ha hb he)

end KServer.HeavyAnchorDynamics

end


/-! The first-priority heavy region is its full ball, including boundaries. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HeavyAnchorDynamics
open FiniteExperiment Pilot HeavyCenters HeavyLabels HeavySchedule LevelKeys TierProcess
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

lemma level_heavy (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0 ≤ r) (σ:Fin H→Y) (tape:Tape Y k H r) (t:ℕ) (x:Y) (a:Pool Y):
    map s law hr σ tape t x=slot (k:=k) a ↔
      HeavyKeys.key s law r heavyGamma heavyDelta σ tape.1 t x=some a:=by
  let ks:=keys s law hr σ tape t
  change PriorityKeys.key ks x=Sum.inl ⟨none,a⟩ ↔ ks none x=some a
  constructor
  · intro he
    unfold PriorityKeys.key at he
    cases hs:PriorityKeys.selected ks x with
    | none=>rw [hs] at he; cases he
    | some z=>
      rw [hs] at he
      have hz:z=⟨none,a⟩:=Sum.inl.inj he
      subst z
      exact (PriorityKeys.selected_some ks x hs).1
  · intro ha
    have h:(PriorityKeys.covered ks x).Nonempty:=
      ⟨none,mem_filter.mpr ⟨mem_univ _,by rw [ha]; exact Option.some_ne_none _⟩⟩
    have hm:(PriorityKeys.covered ks x).min' h=none:=by
      apply le_antisymm
      · exact min'_le _ _ (mem_filter.mpr ⟨mem_univ _,by rw [ha]; exact Option.some_ne_none _⟩)
      · exact bot_le
    obtain ⟨b,hb,hs⟩:=PriorityKeys.selected_some_of_mem ks x h
    have he:(⟨(PriorityKeys.covered ks x).min' h,b⟩:Sigma (Alphabet Y k))=⟨none,a⟩:=by
      generalize hi : (PriorityKeys.covered ks x).min' h = i at b hb hm ⊢
      clear hi
      have hi0 : i=none:=hm
      subst i
      have hab:b=a:=Option.some.inj (hb.symm.trans ha)
      subst b
      rfl
    rw [he] at hs
    simp only [PriorityKeys.key,hs]

lemma region_ball (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (tape:Tape Y k H r) (t:ℕ) {c:Y} {a:Pool Y}
    (hc:c∈centers s law r heavyGamma heavyDelta σ t)
    (ha:(run s law r heavyGamma heavyDelta σ tape.1 t).label c=a):
    (univ.filter (fun x=>map s law hr.le σ tape t x=slot (k:=k) a))=
      ball c ((run s law r heavyGamma heavyDelta σ tape.1 t).rad c):=by
  ext x
  simp only [mem_filter,mem_univ,true_and,ball,level_heavy]
  rw [key_iff s law hr σ tape.1 t x a]
  constructor
  · rintro ⟨b,hb,hl,hd⟩
    have he: b=c:=(run_valid s law hr heavyGamma heavyDelta σ tape.1 t).2 hb hc (hl.trans ha.symm)
    simpa only [he] using hd
  · intro hd
    exact ⟨c,hc,ha,hd⟩

lemma heavy_mass_comparison (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (hσ:0<law.val σ) (tape:Tape Y k H r) (t:Fin H)
    (hA:Active r heavyGamma heavyDelta (centers s law r heavyGamma heavyDelta σ t.val)
      (mu s law (t.val+1) σ) (σ t)):
    let R:=(run s law r heavyGamma heavyDelta σ tape.1 (t.val+1)).rad (σ t)
    ball (σ t) (heavyGamma*r) ⊆ ball (σ t) R ∧
      mass (mu s law (t.val+1) σ) (ball (σ t) R)≤
        (1+heavyDelta)*mass (mu s law (t.val+1) σ) (ball (σ t) (heavyGamma*r)) ∧
      1≤ mass (mu s law (t.val+1) σ) (ball (σ t) (heavyGamma*r)):=by
  dsimp only
  have hR:(run s law r heavyGamma heavyDelta σ tape.1 (t.val+1)).rad (σ t)∈Set.Icc (16*r) (20*r):=by
    exact (run_valid s law hr heavyGamma heavyDelta σ tape.1 (t.val+1)).1 _
      (by rw [centers_succ,step,ite_eq_left hA]; exact mem_insert_self _ _)
  have hγ:0≤heavyGamma ∧ heavyGamma≤16:=by norm_num [heavyGamma]
  refine ⟨ball_mono (by nlinarith [hR.1]),?_,?_⟩
  · exact (mass_mono (fun z=>mu_nonneg s law (t.val+1) σ z)
      (ball_mono (by nlinarith [hR.2]))).trans hA.1
  · have hx:σ t∈ball (σ t) (heavyGamma*r):=by
      simp only [ball,mem_filter,mem_univ,true_and,dist_self]
      exact mul_nonneg hγ.1 hr.le
    exact (mu_served s law t σ hσ).trans
      (single_le_sum (fun z _=>mu_nonneg s law (t.val+1) σ z) hx)
end KServer.HeavyAnchorDynamics

end


/-! The metric and heavy-ball payment portions of §08's anchor travel proof.
These are required by the open finite-law construction, not a new main result.
The clipped ramp and rho=6/5 are the exact source choices. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.AnchorTravel

lemma ramp_nonneg (u : ℝ) : 0 ≤ ramp u := le_min (by norm_num) (le_max_left _ _)
lemma ramp_le_one (u : ℝ) : ramp u ≤ 1 := min_le_left _ _
lemma ramp_zero {u : ℝ} (h : u ≤ 4) : ramp u=0 := by
  unfold ramp
  rw [max_eq_left (by linarith),min_eq_right (by norm_num)]
lemma ramp_one {u : ℝ} (h : 7 ≤ u) : ramp u=1 := by
  unfold ramp
  rw [max_eq_right (by linarith),min_eq_left (by linarith)]

lemma ramp_lipschitz (a b : ℝ) : |ramp b-ramp a| ≤ |b-a|/3 := by
  rw [abs_le]
  constructor <;> unfold ramp <;>
    simp only [min_def,max_def] <;> split_ifs <;>
    have h1 := le_abs_self (b-a) <;> have h2 := neg_le_abs (b-a) <;> linarith

variable {Y : Type*} [MetricSpace Y]

/-- Actual pointwise metric motion inequality, including the saturation cutoff.
No independence between the old point and an updated history is required. -/
theorem ramp_motion {a y z : Y} {r c : ℝ} (hr : 0 < r) (hc : 0 ≤ c) :
    r*c*max 0 (ramp (dist a z/r)-ramp (dist a y/r)) ≤
      if dist a y < 7*r then dist y z/3*c else 0 := by
  by_cases hh : dist a y < 7*r
  · rw [ite_eq_left hh]
    have h := ramp_lipschitz (dist a y/r) (dist a z/r)
    have hmetric : |dist a z-dist a y| ≤ dist y z := by
      rw [abs_le]
      constructor
      · linarith [dist_triangle a z y,dist_comm z y]
      · linarith [dist_triangle a y z]
    have habs : |dist a z/r-dist a y/r| = |dist a z-dist a y|/r := by
      rw [←sub_div,abs_div,abs_of_pos hr]
    rw [habs] at h
    have hbound : ramp (dist a z/r)-ramp (dist a y/r) ≤ dist y z/r/3 :=
      (le_abs_self _).trans (h.trans (div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right hmetric hr.le) (by norm_num)))
    have hmax := max_le (by positivity : (0:ℝ) ≤ dist y z/r/3) hbound
    have hm := mul_le_mul_of_nonneg_left hmax (mul_nonneg hr.le hc)
    convert hm using 1 <;> first | rfl | field_simp
  · rw [ite_eq_right hh]
    have hsat : 7 ≤ dist a y/r := (le_div_iff₀ hr).mpr (le_of_not_gt hh)
    rw [ramp_one hsat,max_eq_left (by linarith [ramp_le_one (dist a z/r)]),mul_zero]

/-- On the heavy inner ball the new ramp vanishes and the old ramp is one. -/
lemma inner_ramp {a x z : Y} {r γ : ℝ} (hr : 0 < r) (hγ : γ < 1/100)
    (hax : 8*r < dist a x) (hxz : dist x z ≤ γ*r) :
    ramp (dist x z/r)=0 ∧ ramp (dist a z/r)=1 := by
  have htri := dist_triangle a z x
  rw [dist_comm z x] at htri
  constructor
  · apply ramp_zero
    apply (div_le_iff₀ hr).mpr
    nlinarith
  · apply ramp_one
    apply (le_div_iff₀ hr).mpr
    nlinarith

variable [DecidableEq Y]

/-- The heavy condition gives the actual unnormalized potential drop on a
retained reuse, with C the new heavy key's entire ball and S its inner ball. -/
theorem heavy_integral_drop {w : Y → ℝ} {C S : Finset Y} {a x : Y} {r γ δ : ℝ}
    (hw : ∀ z ∈ C, 0 ≤ w z) (hSC : S ⊆ C)
    (hr : 0 < r) (hγ : γ < 1/100) (hax : 8*r < dist a x)
    (hS : ∀ z ∈ S, dist x z ≤ γ*r)
    (hheavy : mass w C ≤ (1+δ)*mass w S) :
    integral w C x r-integral w C a r ≤ -(1-δ)*mass w S := by
  have hpoint : ∀ z ∈ C, w z*ramp (dist x z/r)-w z*ramp (dist a z/r) ≤
      w z-2*(if z ∈ S then w z else 0) := by
    intro z hz
    by_cases hs : z ∈ S
    · have hh := inner_ramp hr hγ hax (hS z hs)
      rw [hh.1,hh.2,ite_eq_left hs]
      ring_nf
      exact le_rfl
    · rw [ite_eq_right hs,mul_zero,sub_zero]
      nlinarith [mul_nonneg (hw z hz) (ramp_nonneg (dist a z/r)),
        mul_le_of_le_one_right (hw z hz) (ramp_le_one (dist x z/r))]
  have hsum := sum_le_sum hpoint
  have hrestrict : (∑ z ∈ C, if z ∈ S then w z else 0) = mass w S := by
    unfold mass
    rw [←sum_filter]
    rw [filter_mem_eq_inter,inter_eq_right.mpr hSC]
  rw [sum_sub_distrib,sum_sub_distrib,←mul_sum,hrestrict] at hsum
  change integral w C x r-integral w C a r ≤ mass w C-2*mass w S at hsum
  linarith

/-- Exact rho=6/5 normalization. H≥1 is used in the held-size comparison. -/
theorem retained_anchor_payment {w : Y → ℝ} {C S : Finset Y} {a x : Y}
    {r γ δ u b : ℝ} (hw : ∀ z ∈ C, 0 ≤ w z) (hSC : S ⊆ C)
    (hr : 0 < r) (hγ : γ < 1/100) (hδ : δ ≤ 1/100)
    (hax : 8*r < dist a x) (hS : ∀ z ∈ S, dist x z ≤ γ*r)
    (hheavy : mass w C ≤ (1+δ)*mass w S) (hH : 1 ≤ mass w S)
    (hu : 0 < u) (href : u ≤ (6/5)*(1+mass w C)) (hb : 0 ≤ b) :
    r*b/u*(integral w C x r-integral w C a r) ≤ -r*b/4 := by
  have hdrop := heavy_integral_drop hw hSC hr hγ hax hS hheavy
  have hM : u ≤ (6/5)*(2+δ)*mass w S := by nlinarith
  have hcoef : u ≤ 4*(1-δ)*mass w S := by
    have hp : 0 ≤ mass w S := by linarith
    have hh : (6/5)*(2+δ) ≤ 4*(1-δ) := by linarith
    exact hM.trans (mul_le_mul_of_nonneg_right hh hp)
  have hratio : (1:ℝ)/4 ≤ (1-δ)*mass w S/u := by
    apply (le_div_iff₀ hu).mpr
    linarith
  have hm := mul_le_mul_of_nonneg_left hdrop (div_nonneg (mul_nonneg hr.le hb) hu.le)
  have hp := mul_le_mul_of_nonneg_left hratio (mul_nonneg hr.le hb)
  calc _ ≤ r*b/u*(-(1-δ)*mass w S) := hm
       _ = -(r*b*((1-δ)*mass w S/u)) := by ring
       _ ≤ -(r*b*(1/4)) := neg_le_neg hp
       _ = -r*b/4 := by ring

/-- Positive normalization-refresh jumps are paid by the old-plus-new size
charge; no invalid comparison of the new integral to the old reference is used. -/
theorem normalization_refresh {r b I s u C : ℝ}
    (hr : 0 ≤ r) (hb : 0 ≤ b) (hI : 0 ≤ I) (hs : 0 < s) (hu : 0 < u)
    (hIs : I ≤ s) (hbu : b ≤ (6/5)*C*u) :
    r*b*I*(1/s-1/u) ≤ (6/5)*C*r*u := by
  by_cases h : u ≤ s
  · have h1 : 1/s-1/u ≤ 0 := sub_nonpos.mpr (one_div_le_one_div_of_le hu h)
    have hleft := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (mul_nonneg hr hb) hI) h1
    have hright : 0 ≤ (6/5)*C*r*u := by nlinarith [mul_nonneg hr hb, mul_le_mul_of_nonneg_left hbu hr]
    exact hleft.trans hright
  · have hdrop : r*b*I*(1/s-1/u) ≤ r*b := by
      have hdiv : I/s ≤ 1 := (div_le_one hs).mpr hIs
      have hp := mul_le_mul_of_nonneg_left hdiv (mul_nonneg hr hb)
      have hn := div_nonneg (mul_nonneg (mul_nonneg hr hb) hI) hu.le
      calc _ = r*b*(I/s)-r*b*I/u := by ring
           _ ≤ _ := by linarith
    exact hdrop.trans (by nlinarith [mul_le_mul_of_nonneg_left hbu hr])

end KServer.AnchorTravel

end


/-! The actual retained label releases the ramp credit. All geometry and the
one-unit inner mass are obtained from the actual embedding and served hidden
trajectory, not postulated as an anchor-payment interface. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HeavyAnchorDynamics
open FiniteExperiment Pilot HeavyCenters HeavyLabels HeavySchedule LevelKeys TierProcess
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

lemma absent_cell (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (tape:Tape Y k H r) (t:ℕ) (a:Pool Y)
    (ha:¬present s law r σ tape.1 t a):cell s law hr.le σ tape t a=∅:=by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have he:HeavyKeys.key s law r heavyGamma heavyDelta σ tape.1 t x=some a:=
    (level_heavy s law hr.le σ tape t x a).mp (mem_filter.mp hx).2
  obtain ⟨c,hc,hl,_⟩:=(key_iff s law hr σ tape.1 t x a).mp he
  exact ha ⟨c,hc,hl⟩

lemma moving_drop (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (hσ:0<law.val σ) (tape:Tape Y k H r) (t:Fin H)
    (a:Pool Y) (hold:present s law r σ tape.1 t.val a)
    (hnew:present s law r σ tape.1 (t.val+1) a)
    (hmove:heavyAnchor s law r σ tape.1 t.val a≠heavyAnchor s law r σ tape.1 (t.val+1) a)
    {u b:ℝ} (hu:0<u) (hb:0≤b)
    (href:u≤(6/5:ℝ)*(1+AnchorTravel.mass (mu s law (t.val+1) σ)
      (cell s law hr.le σ tape (t.val+1) a))):
    r*b/u*(AnchorTravel.integral (mu s law (t.val+1) σ) (cell s law hr.le σ tape (t.val+1) a)
      (heavyAnchor s law r σ tape.1 (t.val+1) a) r-
      AnchorTravel.integral (mu s law (t.val+1) σ) (cell s law hr.le σ tape (t.val+1) a)
      (heavyAnchor s law r σ tape.1 t.val a) r)≤-r*b/4:=by
  obtain ⟨c,hc,hl⟩:=hold
  obtain ⟨d,hd,hl'⟩:=hnew
  have ha:=anchor_eq s law hr σ tape.1 t.val hc hl
  have ha':=anchor_eq s law hr σ tape.1 (t.val+1) hd hl'
  have hcd:c≠d:=by intro he; exact hmove (ha.trans (he.trans ha'.symm))
  obtain ⟨hdx,hfar,_,hA⟩:=(common_centers s law hr σ tape.1 t hc hd (hl.trans hl'.symm)).resolve_left hcd
  have hanew:=ha'.trans hdx
  rw [hdx] at hd hl' hfar
  have hcell:=region_ball s law hr σ tape (t.val+1) hd hl'
  have hmass:=heavy_mass_comparison s law hr σ hσ tape t hA
  change _ ∧ _ ∧ _ at hmass
  change cell s law hr.le σ tape (t.val+1) a=_ at hcell
  rw [hcell] at href
  rw [ha,hanew,hcell]
  exact AnchorTravel.retained_anchor_payment
    (fun z _=>mu_nonneg s law (t.val+1) σ z) hmass.1 hr
    (by norm_num [heavyGamma]) (by norm_num [heavyDelta]) hfar
    (fun z hz=>(mem_filter.mp hz).2) hmass.2.1 hmass.2.2 hu href hb

end KServer.HeavyAnchorDynamics

end


/-! The old ramp cutoff selects a heavy ball containing the unit-radius ball
about the old point and lying inside its twenty-seven-radius neighborhood. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HeavyAnchorDynamics
open FiniteExperiment Pilot HeavyCenters HeavyLabels HeavySchedule LevelKeys TierProcess
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

lemma selected_data (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (tape:Tape Y k H r) (t:ℕ) (y:Y) (a:Key Y k)
    (ha:selected s law r σ tape.1 t y=some a):
    ∃ c∈centers s law r heavyGamma heavyDelta σ t,
      a=slot (k:=k) ((run s law r heavyGamma heavyDelta σ tape.1 t).label c) ∧
      dist c y<7*r:=by
  unfold selected at ha
  cases he:HeavyKeys.key s law r heavyGamma heavyDelta σ tape.1 t y with
  | none=>rw [he] at ha; cases ha
  | some b=>
    rw [he] at ha
    dsimp only at ha
    split_ifs at ha with hd
    · obtain ⟨c,hc,hl,_⟩:=(key_iff s law hr σ tape.1 t y b).mp he
      rw [anchor_eq s law hr σ tape.1 t hc hl] at hd
      exact ⟨c,hc,(Option.some.inj ha).symm.trans (congrArg (slot (k:=k)) hl.symm),hd⟩

lemma selected_close (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (tape:Tape Y k H r) (t:ℕ) (y:Y) (a:Key Y k)
    (ha:selected s law r σ tape.1 t y=some a) (z:Y)
    (hz:map s law hr.le σ tape t z=a):dist y z≤27*r:=by
  obtain ⟨c,hc,rfl,hd⟩:=selected_data s law hr σ tape t y a ha
  have hb:=region_ball s law hr σ tape t hc rfl
  have hz':z∈ball c ((run s law r heavyGamma heavyDelta σ tape.1 t).rad c):=by
    rw [←hb]; exact mem_filter.mpr ⟨mem_univ _,hz⟩
  have hr':=(run_valid s law hr heavyGamma heavyDelta σ tape.1 t).1 c hc
  have hh:=dist_triangle y c z
  rw [dist_comm y c] at hh
  have hd':=(mem_filter.mp hz').2
  change dist c z≤_ at hd'
  linarith [hr'.2]

lemma selected_contains (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (tape:Tape Y k H r) (t:ℕ) (y:Y) (a:Key Y k)
    (ha:selected s law r σ tape.1 t y=some a) (z:Y) (hz:dist y z ≤ r):
    map s law hr.le σ tape t z=a:=by
  obtain ⟨c,hc,rfl,hd⟩:=selected_data s law hr σ tape t y a ha
  apply (level_heavy s law hr.le σ tape t z _).mpr
  apply (key_iff s law hr σ tape.1 t z _).mpr
  refine ⟨c,hc,rfl,?_⟩
  have hr':=(run_valid s law hr heavyGamma heavyDelta σ tape.1 t).1 c hc
  have hh:=dist_triangle c y z
  linarith [hr'.1]

end KServer.HeavyAnchorDynamics

end


/-! The pointwise drift comparison for the old heavy-slot ramp coefficients.
It applies to an arbitrary coupled old/new member, without independence. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.AnchorTravel
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y J D:Type*} [MetricSpace Y]

lemma cutoff_nonneg {r:ℝ} {c:J→ℝ} {a:J→Y} (hc:∀ j,0 ≤ c j) (key:Option J) (y:Y):
    0 ≤ cutoff r c a key y:=by
  cases key with
  | none=>rfl
  | some j=>dsimp [cutoff]; split_ifs <;> [exact hc j; rfl]

lemma term_bounds {r M:ℝ} {c:J→ℝ} {a:J→Y}
    (hr:0 ≤ r) (hM:0≤M) (hc:∀ j,c j∈Set.Icc 0 M) (key:Option J) (y:Y):
    term r c a key y∈Set.Icc 0 (r*M):=by
  cases key with
  | none=>exact ⟨le_rfl,mul_nonneg hr hM⟩
  | some j=>
    dsimp [term]
    exact ⟨mul_nonneg (mul_nonneg hr (hc j).1) (ramp_nonneg _),
      (mul_le_of_le_one_right (mul_nonneg hr (hc j).1) (ramp_le_one _)).trans
        (mul_le_mul_of_nonneg_left (hc j).2 hr)⟩

lemma term_motion {r M:ℝ} {c:J→ℝ} {a:J→Y}
    (hr:0 < r) (hM:0≤M) (hc:∀ j,c j∈Set.Icc 0 M) (old new:Option J) (y z:Y):
    term r c a new z-term r c a old y≤
      M*r*(if new=old then 0 else 1)+dist y z/3*cutoff r c a old y:=by
  by_cases he:new=old
  · subst new
    rw [ite_eq_left rfl,mul_zero,zero_add]
    cases old with
    | none=>simp only [term,cutoff,sub_self,mul_zero,le_refl]
    | some j=>
      have hh:=ramp_motion (a:=a j) (y:=y) (z:=z) hr (hc j).1
      simp only [term,cutoff]
      calc _ = r*c j*(ramp (dist (a j) z/r)-ramp (dist (a j) y/r)):=by ring
           _ ≤ r*c j*max 0 (ramp (dist (a j) z/r)-ramp (dist (a j) y/r)):=
              mul_le_mul_of_nonneg_left (le_max_right _ _) (mul_nonneg hr.le (hc j).1)
           _ ≤ _:=by simpa only [mul_ite,mul_zero] using hh
  · rw [ite_eq_right he,mul_one]
    have hnew:term r c a new z ≤ r*M:=(term_bounds hr.le hM hc new z).2
    have hold:0≤term r c a old y:=(term_bounds hr.le hM hc old y).1
    have hcut:0≤dist y z/3*cutoff r c a old y:=
      mul_nonneg (div_nonneg dist_nonneg (by norm_num)) (cutoff_nonneg (fun j=>(hc j).1) old y)
    nlinarith

variable [Fintype D]

theorem member_drift {r:D→ℝ} {M C:ℝ} {c:D→J→ℝ} {a:D→J→Y}
    (hr:∀ d,0 < r d) (hM:0≤M) (hc:∀ d j,c d j∈Set.Icc 0 M)
    (old new:D→Y→Option J) (y z:Y)
    (hcut:(∑ d,cutoff (r d) (c d) (a d) (old d y) y)≤C):
    (∑ d,term (r d) (c d) (a d) (new d z) z)-
      (∑ d,term (r d) (c d) (a d) (old d y) y)≤
      M*(∑ d,r d*(if new d z=old d y then 0 else 1))+C/3*dist y z:=by
  rw [←sum_sub_distrib]
  have hh:=sum_le_sum (s:=(univ:Finset D)) (fun d _=>term_motion (a:=a d) (hr d) hM (hc d) (old d y) (new d z) y z)
  simp only [sum_add_distrib,mul_assoc,←mul_sum] at hh
  have hm:=mul_le_mul_of_nonneg_left hcut (div_nonneg (dist_nonneg (x:=y) (y:=z)) (by norm_num : (0:ℝ)≤3))
  nlinarith

end KServer.AnchorTravel

end


/-! Exact finite conditional integration for the chronological ramp. These
identities do not discard a filtering term after an adaptive choice. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.AnchorTravel
open RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Ω Y D J:Type} [Fintype Ω] [Fintype Y] [Fintype D] [Fintype J]
variable [MetricSpace Y] {w:Ω→ℝ} {k:ℕ}

omit [MetricSpace Y] in
lemma conditional_average (hw:∀ ω,0≤w ω) (H:Ω→ℕ) (q:Ω→Fin k→Y)
    (F:Ω→Y→ℝ) (hF:∀ ω ρ,H ω=H ρ→F ω=F ρ):
    avg w (fun ω=>∑ y,PosteriorCounting.measure (w:=w) H q ω y*F ω y)=
      avg w (fun ω=>∑ i:Fin k,F ω (q ω i)):=by
  have he:(fun ω=>∑ y,PosteriorCounting.measure (w:=w) H q ω y*F ω y)=
      posterior w H (fun ω=>∑ i:Fin k,F ω (q ω i)):=by
    funext ω
    exact PosteriorCounting.conditional_integral H q ω F (fun ρ h=>hF ρ ω h)
  rw [he]
  exact posterior_avg hw H _

lemma integral_term (μ:Y→ℝ) (key:Y→Option J) (a:J→Y) (r:ℝ) (c:J→ℝ):
    (∑ j,r*c j*slotIntegral μ key (a j) r j)=∑ y,μ y*term r c a (key y) y:=by
  simp only [slotIntegral,sum_filter,mul_sum,mul_ite,mul_zero]
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  cases he:key y with
  | none=>simp [term]
  | some j=>simp [term,mul_left_comm]

omit [Fintype J] in
lemma slotIntegral_nonneg {μ:Y→ℝ} (hμ:∀ y,0≤μ y) (key:Y→Option J) (a:Y) (r:ℝ) (j:J):
    0 ≤ slotIntegral μ key a r j:=
  sum_nonneg (fun y _=>mul_nonneg (hμ y) (ramp_nonneg _))

omit [Fintype J] in
lemma slotIntegral_bound {μ:Y→ℝ} (hμ:∀ y,0≤μ y) (key:Y→Option J) (a:Y) (r:ℝ) (j:J):
    slotIntegral μ key a r j≤∑ y∈univ.filter (fun y=>key y=some j),μ y:=by
  apply sum_le_sum
  intro y _
  exact mul_le_of_le_one_right (hμ y) (ramp_le_one _)

omit [Fintype Y] [Fintype J] in
lemma expected_membership (hw:∀ ω,0≤w ω)
    {r:D→ℝ} {M C:ℝ} {c:Ω→D→J→ℝ} {a:Ω→D→J→Y}
    (hr:∀ d,0 < r d) (hM:0≤M) (hc:∀ ω d j,c ω d j∈Set.Icc 0 M)
    (old new:Ω→D→Y→Option J) (q q':Ω→Fin k→Y)
    (hcut:∀ ω i,(∑ d,cutoff (r d) (c ω d) (a ω d) (old ω d (q ω i)) (q ω i))≤C):
    avg w (fun ω=>(∑ i:Fin k,∑ d,term (r d) (c ω d) (a ω d) (new ω d (q' ω i)) (q' ω i))-
      (∑ i:Fin k,∑ d,term (r d) (c ω d) (a ω d) (old ω d (q ω i)) (q ω i)))≤
      M*avg w (fun ω=>∑ i:Fin k,∑ d,r d*(if new ω d (q' ω i)=old ω d (q ω i) then 0 else 1))+
        C/3*avg w (fun ω=>∑ i:Fin k,dist (q ω i) (q' ω i)):=by
  have hh:=avg_mono hw (fun ω=>sum_le_sum (s:=(univ:Finset (Fin k)))
    (fun i _=>member_drift hr hM (hc ω) (old ω) (new ω) (q ω i) (q' ω i) (hcut ω i)))
  simp only [sum_sub_distrib,sum_add_distrib,←mul_sum,avg_add,avg_mul] at hh
  exact hh

omit [Fintype Y] [Fintype J] in
lemma raw_bounds {r:D→ℝ} {M:ℝ} (hr:∀ d,0 ≤ r d) (hM:0≤M)
    (c:D→J→ℝ) (a:D→J→Y) (key:D→Y→Option J) (q:Fin k→Y)
    (hc:∀ d j,c d j∈Set.Icc 0 M):
    (∑ i:Fin k,∑ d,term (r d) (c d) (a d) (key d (q i)) (q i))∈
      Set.Icc 0 (M*k*(∑ d,r d)):=by
  constructor
  · exact sum_nonneg (fun i _=>sum_nonneg (fun d _=>(term_bounds (hr d) hM (hc d) _ _).1))
  · calc _≤∑ i:Fin k,∑ d,r d*M:=sum_le_sum (fun i _=>sum_le_sum
            (fun d _=>(term_bounds (hr d) hM (hc d) _ _).2))
         _ = _:=by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,←sum_mul]; ring

end KServer.AnchorTravel

end


/-! Scalar chronological accounting in the source order: membership, reference,
park, anchor. The normalization comparison is used only after its refresh. -/
noncomputable section
namespace KServer.AnchorTravel

lemma reference_step {r b M I u C:ℝ}
    (hr:0 ≤ r) (hb:0≤b) (hI:I∈Set.Icc 0 M) (hM:0≤M) (hu:0<u)
    (hC:0≤C) (hbu:b≤(6/5:ℝ)*C*u):
    let un:=if KeySizeTracking.refresh (1+M) u then 1+M else u
    r*b/un*I-r*b/u*I≤(6/5:ℝ)*C*r*
      (if KeySizeTracking.refresh (1+M) u then u+un else 0):=by
  dsimp only
  split_ifs with h
  · have hh:=normalization_refresh hr hb hI.1 (by linarith : 0<1+M) hu
      (by linarith [hI.2] : I≤1+M) hbu
    have he:r*b/(1+M)*I-r*b/u*I=r*b*I*(1/(1+M)-1/u):=by ring
    rw [he]
    exact hh.trans (mul_le_mul_of_nonneg_left (by linarith : u≤u+(1+M))
      (by positivity))
  · simp only [sub_self,mul_zero,le_refl]

lemma park_step {r b c u I:ℝ} (hr:0 ≤ r) (hu:0<u)
    (hI:0≤I) (hIu:I≤(6/5:ℝ)*u):
    r*c/u*I-r*b/u*I≤(6/5:ℝ)*r*|c - b|:=by
  have hcoef:I/u≤(6/5:ℝ):=(div_le_iff₀ hu).mpr hIu
  have hcoef0:0≤I/u:=div_nonneg hI hu.le
  calc _ = r*(c-b)*(I/u):=by ring
       _ ≤ r*|c - b| * (I/u):=mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_abs_self _) hr) hcoef0
       _ ≤ r*|c - b| * (6/5:ℝ):=mul_le_mul_of_nonneg_left hcoef (mul_nonneg hr (abs_nonneg _))
       _ = _:=by ring

lemma anchor_step {r b c u I J:ℝ} (hr:0 ≤ r) (hc:0 ≤ c) (hu:0<u)
    (hI:0≤I) (hJ:J≤(6/5:ℝ)*u)
    (oldPresent newPresent moving:Prop) [Decidable oldPresent] [Decidable newPresent] [Decidable moving]
    (habs:¬newPresent→c=0) (hbirth:¬oldPresent→b=0)
    (hsame:oldPresent→newPresent→¬moving→J=I)
    (hdrop:oldPresent→newPresent→moving→ r*c/u*(J-I)≤ -r*c/4):
    r*c/u*J-r*c/u*I+
      (if oldPresent ∧ newPresent ∧ moving then r*c/4 else 0)≤
        (6/5:ℝ)*r*|c - b|:=by
  have hpos:0≤(6/5:ℝ)*r*|c - b|:=by positivity
  by_cases hn:newPresent
  · by_cases ho:oldPresent
    · by_cases hm:moving
      · rw [ite_eq_left ⟨ho,hn,hm⟩]
        have hh:=hdrop ho hn hm
        nlinarith
      · rw [ite_eq_right (by simp only [hm,and_false,not_false_eq_true]),hsame ho hn hm]
        simpa only [sub_self,add_zero] using hpos
    · rw [ite_eq_right (by simp only [ho,false_and,not_false_eq_true]),add_zero,hbirth ho,sub_zero,abs_of_nonneg hc]
      have hh:=mul_le_mul_of_nonneg_left hJ (div_nonneg (mul_nonneg hr hc) hu.le)
      have hz:0 ≤ r*c/u*I:=mul_nonneg (div_nonneg (mul_nonneg hr hc) hu.le) hI
      have he:r*c/u*((6/5:ℝ)*u)=(6/5:ℝ)*r*c:=by field_simp
      rw [he] at hh
      linarith
  · rw [ite_eq_right (by simp only [hn,and_false,false_and,not_false_eq_true]),habs hn]
    simp only [mul_zero,zero_div,zero_mul,sub_self,add_zero]
    positivity

end KServer.AnchorTravel

end


/-! Signed chronological potential, with old coefficients throughout the
membership comparison. The final telescope keeps a single finite endpoint. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.AnchorTravel
open RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Ω Y D J:Type} [Fintype Ω] [Fintype Y] [Fintype D] [Fintype J]
variable [MetricSpace Y] {w:Ω→ℝ} {k:ℕ}

lemma familyIntegral_eq (μ:Y→ℝ) (r:D→ℝ) (c:D→J→ℝ) (a:D→J→Y) (key:D→Y→Option J):
    familyIntegral μ r c a key=∑ y,μ y*familyTest r c a key y:=by
  simp only [familyIntegral,integral_term,familyTest,mul_sum]
  rw [sum_comm]

lemma expected_step (hw:∀ ω,0≤w ω) (H:Ω→ℕ) (q q':Ω→Fin k→Y)
    {r:D→ℝ} {M C:ℝ} (hr:∀ d,0 < r d) (hM:0≤M)
    (c c':Ω→D→J→ℝ) (a a':Ω→D→J→Y) (old new:Ω→D→Y→Option J)
    (hc:∀ ω d j,c ω d j∈Set.Icc 0 M)
    (hcut:∀ ω i,(∑ d,cutoff (r d) (c ω d) (a ω d) (old ω d (q ω i)) (q ω i))≤C)
    (had:∀ ω ρ,H ω=H ρ→familyTest r (c ω) (a ω) (new ω)=familyTest r (c ρ) (a ρ) (new ρ))
    (had':∀ ω ρ,H ω=H ρ→familyTest r (c' ω) (a' ω) (new ω)=familyTest r (c' ρ) (a' ρ) (new ρ))
    (travel charge:Ω→ℝ)
    (hstage:∀ ω,familyIntegral (PosteriorCounting.measure (w:=w) H q' ω) r (c' ω) (a' ω) (new ω)-
      familyIntegral (PosteriorCounting.measure (w:=w) H q' ω) r (c ω) (a ω) (new ω)+travel ω/4 ≤ charge ω):
    avg w (fun ω=>∑ i:Fin k,familyTest r (c' ω) (a' ω) (new ω) (q' ω i))-
      avg w (fun ω=>∑ i:Fin k,familyTest r (c ω) (a ω) (old ω) (q ω i))+
      avg w travel/4≤
        M*avg w (fun ω=>∑ i:Fin k,∑ d,r d*(if new ω d (q' ω i)=old ω d (q ω i) then 0 else 1))+
        C/3*avg w (fun ω=>∑ i:Fin k,dist (q ω i) (q' ω i))+avg w charge:=by
  have hh:=avg_mono hw hstage
  simp only [familyIntegral_eq,avg_add,avg_sub] at hh
  have hd:avg w (fun ω=>travel ω/4)=avg w travel/4:=by
    unfold RankTracking.avg
    rw [sum_div]
    apply sum_congr rfl
    intro ω _
    ring
  rw [hd,conditional_average hw H q' _ had,conditional_average hw H q' _ had'] at hh
  have hm:=expected_membership hw hr hM hc old new q q' hcut
  simp only [avg_sub] at hm
  change _≤_ at hm
  dsimp only [familyTest] at hh ⊢
  linarith

omit [Fintype Ω] [Fintype Y] [Fintype D] [Fintype J] [MetricSpace Y] in
lemma chronological_telescope (P T E:ℕ→ℝ) (N:ℕ) {B:ℝ}
    (hP:0≤P N) (hB:P 0≤B)
    (hstep:∀ t,t<N→P (t+1)-P t+T t/4≤E t):
    (∑ t∈range N,T t)≤4*(∑ t∈range N,E t)+4*B:=by
  have he:(∑ t∈range N,(P (t+1)-P t))=P N-P 0:=by
    clear hP hstep
    induction N with
    | zero=>simp
    | succ N ih=>rw [sum_range_succ,ih]; ring
  have hh:=sum_le_sum (s:=range N) (fun t ht=>hstep t (mem_range.mp ht))
  simp only [sum_add_distrib,←sum_div,he] at hh
  linarith

end KServer.AnchorTravel

end


/-! A literal single-slot ordered update: held reference, park, retained anchor. -/
noncomputable section
namespace KServer.AnchorTravel

lemma slot_stage {r b c u v M I J C:ℝ} (hr:0 ≤ r) (hb:0≤b) (hc:0 ≤ c)
    (hu:0<u) (hv:0<v) (hC:0≤C) (hM:0≤M)
    (hI:I∈Set.Icc 0 M) (hJ:J≤M)
    (hbu:b≤(6/5:ℝ)*C*u) (hn:1+M≤(6/5:ℝ)*v)
    (he:v=if KeySizeTracking.refresh (1+M) u then 1+M else u)
    (oldPresent newPresent moving:Prop) [Decidable oldPresent] [Decidable newPresent] [Decidable moving]
    (habs:¬newPresent→c=0) (hbirth:¬oldPresent→b=0)
    (hsame:oldPresent→newPresent→¬moving→J=I)
    (hdrop:oldPresent→newPresent→moving→ r*c/v*(J-I)≤ -r*c/4):
    r*(c/v)*J-r*(b/u)*I+
      (if oldPresent ∧ newPresent ∧ moving then r*c else 0)/4≤
        (6/5:ℝ)*C*r*(if KeySizeTracking.refresh (1+M) u then u+v else 0)+
          2*(6/5:ℝ)*r*|c-b|:=by
  have href:=reference_step hr hb hI hM hu hC hbu
  change _≤_ at href
  rw [←he] at href
  have hMv : M ≤ (6/5:ℝ)*v := (le_add_of_nonneg_left (show (0:ℝ)≤1 by norm_num)).trans hn
  have hp:=park_step (b:=b) (c:=c) hr hv hI.1 (hI.2.trans hMv)
  have ha:=anchor_step (b:=b) (I:=I) hr hc hv hI.1 (hJ.trans hMv)
    oldPresent newPresent moving habs hbirth hsame hdrop
  have ht:(if oldPresent ∧ newPresent ∧ moving then r*c else 0)/4=
      if oldPresent ∧ newPresent ∧ moving then r*c/4 else 0:=by split_ifs <;> simp
  rw [ht]
  simp only [mul_div_assoc] at href hp ha ⊢
  linarith

end KServer.AnchorTravel

end


/-! True prefix measurability of the literal permanent anchors, including
unused labels. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.KeysAdapted
open FiniteExperiment TierProcess Chronological ActualRoster LevelKeys LevelLaw
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

lemma heavy_anchor_adapted (s:Configuration k Y) (law:RequestLaw Y H)
    (r:ℝ) (tape:Fin H→FiniteUniform.Outcome Y r) (t:ℕ)
    (σ ρ:Fin H→Y) (hh:requestHistory t σ=requestHistory t ρ):
    heavyAnchor s law r σ tape t=heavyAnchor s law r ρ tape t:=by
  funext a
  unfold heavyAnchor
  rw [run_adapted s law r heavyGamma heavyDelta tape t σ ρ hh,
    HeavyCenters.centers_adapted s law r heavyGamma heavyDelta t σ ρ hh]

lemma tier_anchor_adapted [Nonempty Y] (s:Configuration k Y) (law:RequestLaw Y H)
    (T:Pilot.Template) {r:ℝ} (hr:0 ≤ r) (γ h:ℝ) (K t:ℕ)
    (σ ρ:Fin H→Y) (hh:requestHistory t σ=requestHistory t ρ):
    TierKeys.anchor (request s σ) hr K (qualifies s law T r γ h σ) t=
      TierKeys.anchor (request s ρ) hr K (qualifies s law T r γ h ρ) t:=by
  funext a
  have hR:=reserved_adapted s law T r γ h K t σ ρ hh
  have hlabel:∀ i,i∈reserved (request s σ) r K (qualifies s law T r γ h σ) t→
      Chronological.label (request s σ) hr K (qualifies s law T r γ h σ) i=
        Chronological.label (request s ρ) hr K (qualifies s law T r γ h ρ) i:=by
    intro i hi
    exact label_adapted s law T hr γ h K t i (reserved_before _ _ _ _ _ _ hi) σ ρ hh
  by_cases he:∃ i∈reserved (request s σ) r K (qualifies s law T r γ h σ) t,
      Chronological.label (request s σ) hr K (qualifies s law T r γ h σ) i=a
  · obtain ⟨i,hi,ha⟩:=he
    have hi':i∈reserved (request s ρ) r K (qualifies s law T r γ h ρ) t:=hR ▸ hi
    have ha':Chronological.label (request s ρ) hr K (qualifies s law T r γ h ρ) i=a:=
      (hlabel i hi).symm.trans ha
    rw [←ha,TierKeys.anchor_record _ _ _ _ hi,ha,←ha',TierKeys.anchor_record _ _ _ _ hi']
    exact request_adapted s (reserved_before _ _ _ _ _ _ hi) σ ρ hh
  · have he':¬∃ i∈reserved (request s ρ) r K (qualifies s law T r γ h ρ) t,
        Chronological.label (request s ρ) hr K (qualifies s law T r γ h ρ) i=a:=by
      rintro ⟨i,hi,ha⟩
      have hi':i∈reserved (request s σ) r K (qualifies s law T r γ h σ) t:=hR.symm ▸ hi
      exact he ⟨i,hi',(hlabel i hi').trans ha⟩
    simp only [TierKeys.anchor,dite_eq_right he,dite_eq_right he']

lemma anchor_adapted (s:Configuration k Y) (law:RequestLaw Y H)
    {r:ℝ} (hr:0 ≤ r) (a:Tape Y k H r) (t:ℕ) (σ ρ:Fin H→Y)
    (hh:requestHistory t σ=requestHistory t ρ):
    LevelKeys.anchor s law hr σ a t=LevelKeys.anchor s law hr ρ a t:=by
  let : Nonempty Y := ⟨s 0⟩
  have he:LevelKeys.anchors s law hr σ a t=LevelKeys.anchors s law hr ρ a t:=by
    funext i
    cases i with
    | none=>exact heavy_anchor_adapted s law r a.1 t σ ρ hh
    | some i=>exact tier_anchor_adapted s law tierTemplate hr tierGamma (height i) (tierK (height i)) t σ ρ hh
  unfold LevelKeys.anchor
  rw [he]

end KServer.KeysAdapted

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

lemma stepQuota_nonneg {R τ:ℝ} (hR:0≤R) (hτ:0≤τ) (t:ℕ) (ω:Atom (k:=k) law hr):
    0 ≤ stepQuota s law hr hk R τ t ω:=by
  unfold stepQuota
  exact sum_nonneg (fun v _=>mul_nonneg (PrefixTree.weight_nonneg _ L hR hτ _) (abs_nonneg _))
lemma stepKey_nonneg (t:ℕ) (ω:Atom (k:=k) law hr):0 ≤ stepKey s law hr t ω:=by
  unfold stepKey keyCross
  exact sum_nonneg fun d _=>mul_nonneg (hr d).le (sum_nonneg fun _ _=>by split_ifs <;> norm_num)

lemma park_bound {R τ:ℝ} (hR:0≤R) (hτ:0<τ) (t:ℕ) (ω:Atom (k:=k) law hr):
    (∑ v:Node (Y:=Y) (k:=k) (L:=L),PrefixTree.weight (LevelKeys.Key Y k) L R τ v*
      |park s law hr hk (t+1) ω v-park s law hr hk t ω v|)≤
      (1+1/τ)*stepQuota s law hr hk R τ t ω:=by
  exact (PrefixTree.travelTree (LevelKeys.Key Y k) L).weighted_park_variation _ _ _
    (PrefixTree.weight_nonneg _ L hR hτ.le)
    ((PrefixTree.Q_root _ L _ _ _ _ _ hk _ _).trans (PrefixTree.Q_root _ L _ _ _ _ _ hk _ _).symm)
    hτ (PrefixTree.parent_weight _ L hτ.ne')
end KServer.JointBudget

end


/-! All-scale, law/horizon-independent roster endpoint, aggregating the actual
chronological edit charges rather than assuming metric distortion. -/


/-! The chronological triangle inequality for the literal priority stages. -/


/-! The all-step embedded motion of the selected hidden labeled optimum. -/


/-! The finite all-scale offline embedding endpoint. -/


/-! The finite all-scale embedding is used with the reversed geometric list
of radii in the top-down prefix construction, not with a moved quantifier. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointEmbedding
open JointExperiment RankTracking ActualCharges
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0 < r d)

lemma hidden_cost:
    total (weight law hr) H (fun t ω=>∑ i:Fin k,dist (hidden law hr s t ω i) (hidden law hr s (t+1) ω i))=
      EmbeddedCost.opt s law:=by
  unfold total
  rw [←Fin.sum_univ_eq_sum_range,←avg_sum]
  unfold JointExperiment.hidden
  rw [avg_raw law hr (fun z:Raw Y k H L r =>∑ t:Fin H,∑ i:Fin k,
    dist (FiniteExperiment.hidden s z.1 t.val i) (FiniteExperiment.hidden s z.1 (t.val+1) i))]
  exact FiniteExperiment.expected_hidden_cost s law (tapeLaw hr)

end KServer.JointEmbedding

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_JointTravel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal retained-heavy anchor data and chronological payment on the one
joint request/tape experiment. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointHeavy
open JointExperiment JointAllocation LevelKeys TierProcess AnchorTravel HeavyAnchorDynamics
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0 < r d) (hk:1≤(k:ℝ))

attribute [local instance] OAI.KServer.JointHeavy.poolDecEq
lemma cell_eq (t:ℕ) (ω:Atom (k:=k) law hr) (d:Fin L) (a:J (Y:=Y)):
    univ.filter (fun y=>key s law hr t ω d y=some a)=
      HeavyAnchorDynamics.cell s law (hr d).le ω.val.1 (ω.val.2 d) t a:=by
  apply Finset.ext
  intro y
  simp only [HeavyAnchorDynamics.cell,mem_filter,mem_univ,true_and]
  exact (HeavyAnchorDynamics.level_heavy s law (hr d).le ω.val.1 (ω.val.2 d) t y a).symm

lemma mass_eq (t:ℕ) (ω:Atom (k:=k) law hr) (d:Fin L) (a:J (Y:=Y)):
    (∑ y∈univ.filter (fun y=>key s law hr t ω d y=some a),FiniteExperiment.mu s law t ω.val.1 y)=
      size s law hr d.val (slot (k:=k) a) t ω-1:=by
  rw [JointAllocation.size_mass,add_sub_cancel_left]
  apply sum_congr
  · ext y
    simp only [mem_filter,mem_univ,true_and]
    exact (HeavyAnchorDynamics.level_heavy s law (hr d).le ω.val.1 (ω.val.2 d) t y a).symm
  · intro y _; rfl

lemma b_nonneg (t:ℕ) (ω:Atom (k:=k) law hr) (d:Fin L) (a:J (Y:=Y)):
    0≤b s law hr hk t ω d a:=band_nonneg s law hr hk t ω d.val _
lemma u_pos (t:ℕ) (ω:Atom (k:=k) law hr) (d:Fin L) (a:J (Y:=Y)):
    0<u s law hr t ω d a:=reference_pos s law hr d.val _ t ω
lemma c_bounds (t:ℕ) (ω:Atom (k:=k) law hr) (d:Fin L) (a:J (Y:=Y)):
    c s law hr hk t ω d a∈Set.Icc 0 ((6/5:ℝ)*72):=
  coefficient_bounds s law hr hk t ω d.val _

lemma absent_band (t:ℕ) (ω:Atom (k:=k) law hr) (d:Fin L) (a:J (Y:=Y))
    (ha:¬present s law hr t ω d a):b s law hr hk t ω d a=0:=by
  have he:=HeavyAnchorDynamics.absent_cell s law (hr d) ω.val.1 (ω.val.2 d) t a ha
  have hh:=JointAllocation.band_capacity s law hr hk t ω d.val (slot (k:=k) a)
  rw [←mass_eq s law hr t ω d a,cell_eq,he,sum_empty,mul_zero] at hh
  exact le_antisymm hh (b_nonneg s law hr hk t ω d a)

lemma integral_eq (μ:Y→ℝ) (t:ℕ) (ω:Atom (k:=k) law hr) (d:Fin L) (a:J (Y:=Y)) (z:Y):
    slotIntegral μ (key s law hr t ω d) z (r d) a=
      integral μ (HeavyAnchorDynamics.cell s law (hr d).le ω.val.1 (ω.val.2 d) t a) z (r d):=by
  unfold slotIntegral integral
  rw [cell_eq]

lemma slot_payment (t:Fin H) (ω:Atom (k:=k) law hr) (d:Fin L) (a:J (Y:=Y)):
    let μ:=FiniteExperiment.mu s law (t.val+1) ω.val.1
    let bn:=b s law hr hk (t.val+1) ω d a
    let bo:=b s law hr hk t.val ω d a
    let un:=u s law hr (t.val+1) ω d a
    let uo:=u s law hr t.val ω d a
    let an:=anchor s law hr (t.val+1) ω d a
    let ao:=anchor s law hr t.val ω d a
    r d*(bn/un)*slotIntegral μ (key s law hr (t.val+1) ω d) an (r d) a-
      r d*(bo/uo)*slotIntegral μ (key s law hr (t.val+1) ω d) ao (r d) a+
      (if present s law hr t.val ω d a ∧ present s law hr (t.val+1) ω d a ∧ ao≠an then r d*bn else 0)/4≤
        (6/5:ℝ)*72*r d*KeySizeTracking.refreshCost (size s law hr d.val (slot (k:=k) a)) t.val ω+
          2*(6/5:ℝ)*r d*|bn-bo|:=by
  dsimp only
  let M:=size s law hr d.val (slot (k:=k) a) (t.val+1) ω-1
  have hMs:1+M=size s law hr d.val (slot (k:=k) a) (t.val+1) ω:=by dsimp only [M]; ring
  have hM:0≤M:=sub_nonneg.mpr (size_range s law hr d.val _ (t.val+1) ω).1
  have hμ:=FiniteExperiment.mu_nonneg s law (t.val+1) ω.val.1
  have hI:=slotIntegral_bound hμ (key s law hr (t.val+1) ω d) (anchor s law hr t.val ω d a) (r d) a
  have hJ:=slotIntegral_bound hμ (key s law hr (t.val+1) ω d) (anchor s law hr (t.val+1) ω d a) (r d) a
  rw [mass_eq] at hI hJ
  have hbu : b s law hr hk t.val ω d a≤(6/5:ℝ)*72*u s law hr t.val ω d a:=
    (div_le_iff₀ (u_pos s law hr t.val ω d a)).mp (c_bounds s law hr hk t.val ω d a).2
  have hn:1+M≤(6/5:ℝ)*u s law hr (t.val+1) ω d a:=by
    rw [hMs]
    exact (reference_comparison s law hr d.val (slot (k:=k) a) (t.val+1) ω).2
  have he:u s law hr (t.val+1) ω d a=if KeySizeTracking.refresh (1+M) (u s law hr t.val ω d a) then 1+M else u s law hr t.val ω d a:=by
    rw [hMs]
    rfl
  have hh:=slot_stage (hr d).le (b_nonneg s law hr hk t.val ω d a)
    (b_nonneg s law hr hk (t.val+1) ω d a) (u_pos s law hr t.val ω d a)
    (u_pos s law hr (t.val+1) ω d a) (by norm_num : (0:ℝ)≤72) hM
    ⟨slotIntegral_nonneg hμ _ _ _ _,hI⟩ hJ hbu hn he
    (present s law hr t.val ω d a) (present s law hr (t.val+1) ω d a)
    (anchor s law hr t.val ω d a≠anchor s law hr (t.val+1) ω d a)
    (absent_band s law hr hk (t.val+1) ω d a) (absent_band s law hr hk t.val ω d a)
    (by intro _ _ h; rw [not_not.mp h]) ?_
  · convert hh using 1
    all_goals try with_reducible_and_instances rfl
    rw [hMs]
    rfl
  · intro ho hn' hm
    rw [integral_eq,integral_eq]
    exact moving_drop s law (hr d) ω.val.1 (request_pos law hr ω) (ω.val.2 d) t a ho hn' hm
      (u_pos s law hr (t.val+1) ω d a) (b_nonneg s law hr hk (t.val+1) ω d a) (by
        have href:=(reference_comparison s law hr d.val (slot (k:=k) a) (t.val+1) ω).1
        have hmass:AnchorTravel.mass (FiniteExperiment.mu s law (t.val+1) ω.val.1)
            (HeavyAnchorDynamics.cell s law (hr d).le ω.val.1 (ω.val.2 d) (t.val+1) a)=
              size s law hr d.val (slot (k:=k) a) (t.val+1) ω-1:=by
          unfold AnchorTravel.mass
          rw [←cell_eq]
          exact mass_eq s law hr (t.val+1) ω d a
        rw [hmass]
        change reference s law hr d.val (slot (k:=k) a) (t.val+1) ω≤_
        linarith)

end KServer.JointHeavy

end


/-! Adapted chronological stage aggregation, retaining signed filtering. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointHeavy
open JointExperiment JointAllocation LevelKeys TierProcess AnchorTravel HeavyAnchorDynamics
open RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0 < r d) (hk:1≤(k:ℝ))
attribute [local instance] keyDecEq poolDecEq

lemma key_adapted (t:ℕ) (ω ρ:Atom (k:=k) law hr) (hh:history law hr t ω=history law hr t ρ):
    key s law hr t ω=key s law hr t ρ:=by
  obtain ⟨ht,hp⟩:=history_eq law hr t ω ρ hh
  funext d y
  unfold key
  rw [ht]
  exact KeysAdapted.heavy_key_adapted s law _ _ _ _ t y _ _ ((FiniteExperiment.requestHistory_eq_iff _ _ _).mpr hp)

lemma anchor_adapted (t:ℕ) (ω ρ:Atom (k:=k) law hr) (hh:history law hr t ω=history law hr t ρ):
    anchor s law hr t ω=anchor s law hr t ρ:=by
  obtain ⟨ht,hp⟩:=history_eq law hr t ω ρ hh
  funext d
  unfold anchor
  rw [ht]
  exact KeysAdapted.heavy_anchor_adapted s law _ _ t _ _ ((FiniteExperiment.requestHistory_eq_iff _ _ _).mpr hp)

lemma c_adapted (t:ℕ) (ω ρ:Atom (k:=k) law hr) (hh:history law hr t ω=history law hr t ρ):
    c s law hr hk t ω=c s law hr hk t ρ:=by
  funext d a
  unfold c b u
  rw [band_adapted s law hr hk t ω ρ hh,reference_adapted s law hr d.val (slot (k:=k) a) t ω ρ hh]

lemma prepared_adapted (t:ℕ) (ω ρ:Atom (k:=k) law hr) (hh:history law hr (t+1) ω=history law hr (t+1) ρ):
    familyTest r (c s law hr hk t ω) (anchor s law hr t ω) (key s law hr (t+1) ω)=
      familyTest r (c s law hr hk t ρ) (anchor s law hr t ρ) (key s law hr (t+1) ρ):=by
  rw [c_adapted s law hr hk t ω ρ (history_refines law hr t ω ρ hh),
    anchor_adapted s law hr t ω ρ (history_refines law hr t ω ρ hh),key_adapted s law hr (t+1) ω ρ hh]

lemma current_adapted (t:ℕ) (ω ρ:Atom (k:=k) law hr) (hh:history law hr t ω=history law hr t ρ):
    familyTest r (c s law hr hk t ω) (anchor s law hr t ω) (key s law hr t ω)=
      familyTest r (c s law hr hk t ρ) (anchor s law hr t ρ) (key s law hr t ρ):=by
  rw [c_adapted s law hr hk t ω ρ hh,anchor_adapted s law hr t ω ρ hh,key_adapted s law hr t ω ρ hh]

lemma stage_payment (t:Fin H) (ω:Atom (k:=k) law hr):
    familyIntegral (PosteriorCounting.measure (w:=weight law hr) (history law hr (t.val+1)) (hidden law hr s (t.val+1)) ω)
      r (c s law hr hk (t.val+1) ω) (anchor s law hr (t.val+1) ω) (key s law hr (t.val+1) ω)-
    familyIntegral (PosteriorCounting.measure (w:=weight law hr) (history law hr (t.val+1)) (hidden law hr s (t.val+1)) ω)
      r (c s law hr hk t.val ω) (anchor s law hr t.val ω) (key s law hr (t.val+1) ω)+
      travel s law hr hk t.val ω/4 ≤ charge s law hr hk t.val ω:=by
  have hm:PosteriorCounting.measure (w:=weight law hr) (history law hr (t.val+1)) (hidden law hr s (t.val+1)) ω=
      FiniteExperiment.mu s law (t.val+1) ω.val.1:=by funext y; exact measure_eq law hr s (t.val+1) ω y
  rw [hm]
  have hh:=sum_le_sum (s:=(univ:Finset (Fin L))) (fun d _=>sum_le_sum (s:=(univ:Finset (J (Y:=Y))))
    (fun a _=>slot_payment s law hr hk t ω d a))
  simp only [sum_add_distrib,sum_sub_distrib,←sum_div] at hh
  simpa only [familyIntegral,c,travel,charge,sum_add_distrib] using hh

lemma expected_payment (t:Fin H) {C:ℝ}
    (hcut:∀ ω i,(∑ d,cutoff (r d) (c s law hr hk t.val ω d) (anchor s law hr t.val ω d)
      (key s law hr t.val ω d (hidden law hr s t.val ω i)) (hidden law hr s t.val ω i))≤C):
    avg (weight law hr) (potential s law hr hk (t.val+1))-
      avg (weight law hr) (potential s law hr hk t.val)+avg (weight law hr) (travel s law hr hk t.val)/4≤
        ((6/5:ℝ)*72)*avg (weight law hr) (fun ω=>∑ i:Fin k,∑ d:Fin L,r d*(if
          key s law hr (t.val+1) ω d (hidden law hr s (t.val+1) ω i)=key s law hr t.val ω d (hidden law hr s t.val ω i)
          then 0 else 1))+
        C/3*avg (weight law hr) (fun ω=>∑ i:Fin k,dist (hidden law hr s t.val ω i) (hidden law hr s (t.val+1) ω i))+
        avg (weight law hr) (charge s law hr hk t.val):=
  expected_step (weight_nonneg law hr) (history law hr (t.val+1)) (hidden law hr s t.val) (hidden law hr s (t.val+1))
    hr (by norm_num) (c s law hr hk t.val) (c s law hr hk (t.val+1)) (anchor s law hr t.val) (anchor s law hr (t.val+1))
    (key s law hr t.val) (key s law hr (t.val+1)) (c_bounds s law hr hk t.val) hcut
    (prepared_adapted s law hr hk t.val) (current_adapted s law hr hk (t.val+1))
    (travel s law hr hk t.val) (charge s law hr hk t.val) (stage_payment s law hr hk t)

end KServer.JointHeavy

end


/-! The actual old heavy-slot coefficients have logarithmic all-scale sum. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointHeavy
open JointExperiment JointAllocation LevelKeys TierProcess AnchorTravel HeavyAnchorDynamics
attribute [local instance] Classical.propDecidable Classical.decEq keyDecEq poolDecEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0 < r d) (hk:1≤(k:ℝ))

lemma selected_term (t:ℕ) (ω:Atom (k:=k) law hr) (y:Y) (d:Fin L)
    (R τ:ℝ):
    PrefixTree.selectedMass (LevelKeys.Key Y k) L (park s law hr hk t ω) (selected s law hr t ω y) d.val/
      PrefixTree.selectedDenominator (LevelKeys.Key Y k)
        (PosteriorCounting.measure (w:=weight law hr) (history law hr t) (hidden law hr s t) ω)
        y (ParkedCoefficients.radius R τ) (selected s law hr t ω y)
        (fun j a=>reference s law hr j a t ω) d.val=
      cutoff (r d) (c s law hr hk t ω d) (anchor s law hr t ω d) (key s law hr t ω d y) y:=by
  have hs:selected s law hr t ω y d.val=(match key s law hr t ω d y with
    | none=>none
    | some a=>if dist (anchor s law hr t ω d a) y<7*r d then some (slot (k:=k) a) else none):=by
      simp only [selected,dite_eq_left d.isLt,HeavyAnchorDynamics.selected,key,anchor]
      rfl
  rw [PrefixTree.selectedMass,PrefixTree.selectedBand,PrefixTree.selectedDenominator,hs]
  cases he:key s law hr t ω d y with
  | none=>simp only [cutoff,sum_empty,zero_div]
  | some a=>
    simp only [cutoff]
    split_ifs with hd
    · rfl
    · simp only [sum_empty,zero_div]

lemma cutoff_sum (t:ℕ) (ω:Atom (k:=k) law hr) (y:Y)
    {R τ:ℝ} (hR:0≤R) (hτ:2≤τ) (hrad:∀ d,r d=ParkedCoefficients.radius R τ d.val):
    (∑ d:Fin L,cutoff (r d) (c s law hr hk t ω d) (anchor s law hr t ω d)
      (key s law hr t ω d y) y)≤
        (7*((6/5:ℝ)*72)/Real.log 2+2*(6/5:ℝ)*72)*(1+Real.log ((k:ℝ)+1)):=by
  have hh:=PrefixTree.selected_coefficients (LevelKeys.Key Y k) L (weight_nonneg law hr)
    (history law hr) (history_refines law hr) (maps law hr s) (hidden law hr s) hk
    (weight_pos law hr) t ω (fun ρ h=>maps_adapted law hr s t ρ ω h)
    (selected s law hr t ω y) y (fun j a=>reference s law hr j a t ω) hR hτ
    (fun j a=>reference_pos s law hr j a t ω) ?_ ?_ ?_ ?_
  · dsimp only at hh
    rw [←Fin.sum_univ_eq_sum_range] at hh
    change (∑ d:Fin L,PrefixTree.selectedMass (LevelKeys.Key Y k) L (park s law hr hk t ω)
      (selected s law hr t ω y) d.val/_)≤_ at hh
    simpa only [selected_term s law hr hk t ω y _ R τ] using hh
  · intro j a
    unfold Rounding.countingMass
    rw [←size_mass_joint s law hr j a t ω]
    exact (reference_comparison s law hr j a t ω).2
  · intro j a ha z hz
    unfold selected at ha
    split_ifs at ha with hj
    · have he:=HeavyAnchorDynamics.selected_close s law (hr ⟨j,hj⟩) ω.val.1 (ω.val.2 ⟨j,hj⟩) t y a ha z (by
        simpa only [maps,dite_eq_left hj] using hz)
      simpa only [hrad] using he
  · intro j a ha z hz
    unfold selected at ha
    split_ifs at ha with hj
    · have he:=HeavyAnchorDynamics.selected_contains s law (hr ⟨j,hj⟩) ω.val.1 (ω.val.2 ⟨j,hj⟩) t y a ha z (by
        simpa only [hrad] using hz)
      simpa only [maps,dite_eq_left hj] using he
  · intro j a b hab
    by_cases hj:j<L
    · have he:=LevelKeys.cell_diameter s law (hr ⟨j,hj⟩) ω.val.1 (ω.val.2 ⟨j,hj⟩) t a b (by
        simpa only [maps,dite_eq_left hj] using hab)
      simpa only [hrad] using he
    · have he:a=b:=Sum.inr.inj (by simpa only [maps,dite_eq_right hj] using hab)
      rw [he,dist_self]
      exact mul_nonneg (by norm_num) (div_nonneg hR (pow_nonneg (by linarith) _))

end KServer.JointHeavy

end


/-! Literal size-reference refresh budget summed over the fixed key inventory. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.KeyReferences
open RankTracking PosteriorRanks ActualCharges
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Ω A Y:Type} [Fintype Ω] [Fintype A] [Fintype Y] {k:ℕ} {w:Ω→ℝ}
variable (hw:∀ ω,0≤w ω) (hwpos:∀ ω,0<w ω) (hw1:∑ ω,w ω=1)
variable (H:ℕ→Ω→ℕ) (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
variable (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y)

include hw hwpos hr in
omit [Fintype A] [Fintype Y] in
lemma refresh_nonneg (d:ℕ) (a:A) (t:ℕ) (ω:Ω):
    0≤KeySizeTracking.refreshCost (size (w:=w) H maps q d a) t ω:=by
  unfold KeySizeTracking.refreshCost
  split_ifs
  · exact add_nonneg (le_trans (by norm_num) (reference_range H maps q hw hwpos hr d a t ω).1)
      (le_trans (by norm_num) (reference_range H maps q hw hwpos hr d a (t+1) ω).1)
  · rfl

omit [Fintype Ω] [Fintype Y] in
lemma count_variation (d t:ℕ) (ω:Ω):
    (∑ a:A,|count maps q d a (t+1) ω-count maps q d a t ω|)≤
      2*HierarchicalQuota.keyCross maps q d t ω:=
  HierarchicalQuota.histogram_distance (fun i=>maps (t+1) ω d (q (t+1) ω i))
    (fun i=>maps t ω d (q t ω i))

include hw hwpos hw1 hr in
omit [Fintype Y] in
lemma refresh_all (d N:ℕ):
    (∑ a:A,total w N (KeySizeTracking.refreshCost (size (w:=w) H maps q d a)))≤
      288*(1+Real.log ((k:ℝ)+1))*total w N (HierarchicalQuota.keyCross maps q d)+
        Fintype.card A*(288*((k:ℝ)+1)*(1+(1+Real.log ((k:ℝ)+1)))):=by
  have hh:=sum_le_sum (s:=(univ:Finset A)) (fun a _=>refresh_budget H maps q hw hwpos hr hw1 d a N)
  simp only [sum_add_distrib,←mul_sum,sum_const,card_univ,nsmul_eq_mul] at hh
  have he:(∑ a:A,∑ t∈range N,avg w (fun ω=>|count maps q d a (t+1) ω-count maps q d a t ω|))=
      total w N (fun t ω=>∑ a:A,|count maps q d a (t+1) ω-count maps q d a t ω|):=by
    unfold total
    rw [sum_comm]
    simp only [avg_sum]
  rw [he] at hh
  have hl:0≤1+Real.log ((k:ℝ)+1):=by
    have :=Real.log_nonneg (by have :=Nat.cast_nonneg (α:=ℝ) k; linarith : (1:ℝ)≤(k:ℝ)+1)
    linarith
  have hc:=mul_le_mul_of_nonneg_left (total_mono hw (N:=N) (count_variation maps q d))
    (mul_nonneg (by norm_num : (0:ℝ)≤144) hl)
  rw [total_mul] at hc
  change (∑ a,total w N _)≤_ at hh
  nlinarith

include hw hwpos hw1 hr in
omit [Fintype Y] in
lemma refresh_subset {J:Type} [Fintype J] (f:J→A) (hf:Function.Injective f) (d N:ℕ):
    (∑ j:J,total w N (KeySizeTracking.refreshCost (size (w:=w) H maps q d (f j))))≤
      288*(1+Real.log ((k:ℝ)+1))*total w N (HierarchicalQuota.keyCross maps q d)+
        Fintype.card A*(288*((k:ℝ)+1)*(1+(1+Real.log ((k:ℝ)+1)))):=by
  apply le_trans _ (refresh_all hw hwpos hw1 H hr maps q d N)
  let F:=fun a=>total w N (KeySizeTracking.refreshCost (size (w:=w) H maps q d a))
  change (∑ j,F (f j))≤∑ a,F a
  calc _ = ∑ a∈univ.image f,F a := (sum_image (fun i _ j _ h=>hf h)).symm
       _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _)
          (fun a _ _=>total_nonneg hw (refresh_nonneg hw hwpos H hr maps q d a))
end KServer.KeyReferences

end


/-! Fixed bands are disjoint inventories, so grouping never enlarges variation. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I V:Type} [Fintype I] [Fintype V]

lemma disjoint_variation (F:I→Finset V) (hd:Set.PairwiseDisjoint (↑(univ:Finset I)) F)
    (p q W:V→ℝ) (w:I→ℝ) (hw:∀ i,0≤w i) (hW:∀ v,0≤W v)
    (he:∀ i v,v∈F i→w i=W v):
    (∑ i,w i*|(∑ v∈F i,q v)-(∑ v∈F i,p v)|)≤∑ v,W v*|q v-p v|:=by
  have hs:(∑ i,w i*|(∑ v∈F i,q v)-(∑ v∈F i,p v)|)≤
      ∑ i,∑ v∈F i,W v*|q v-p v|:=by
    apply sum_le_sum
    intro i _
    rw [←sum_sub_distrib]
    calc _ ≤ w i * ∑ v∈F i,|q v-p v|:=mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (hw i)
         _ = _:=by
          rw [mul_sum]
          exact sum_congr rfl (fun v hv=>by rw [he i v hv])
  rw [←sum_biUnion hd] at hs
  exact hs.trans (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun v _ _=>mul_nonneg (hW v) (abs_nonneg _)))

variable (A:Type) [Fintype A] (L:ℕ)
lemma bands_disjoint {J:Type} [Fintype J] (f:J→A) (hf:Function.Injective f):
    Set.PairwiseDisjoint (↑(univ:Finset (Fin L×J))) (fun i:Fin L×J=>band A L i.1.val (f i.2)):=by
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro v hi hj
  obtain ⟨hdi,hai⟩:=(mem_filter.mp hi).2
  obtain ⟨hdj,haj⟩:=(mem_filter.mp hj).2
  have hd:i.1=j.1:=Fin.ext (by omega)
  have ha:i.2=j.2:=hf (Option.some.inj (hai.symm.trans haj))
  exact hij (Prod.ext hd ha)

lemma band_variation {J:Type} [Fintype J] (f:J→A) (hf:Function.Injective f)
    (p q W:Node A L→ℝ) (r:Fin L→ℝ) (hr:∀ d,0 ≤ r d) (hW:∀ v,0≤W v)
    (he:∀ d a v,v∈band A L d.val (f a)→ r d=W v):
    (∑ d:Fin L,∑ a:J,r d*|bandMass A L q d.val (f a)-bandMass A L p d.val (f a)|)≤
      ∑ v,W v*|q v-p v|:=by
  have hh:=disjoint_variation (fun i:Fin L×J=>band A L i.1.val (f i.2))
    (bands_disjoint A L f hf) p q W (fun i=>r i.1) (fun i=>hr i.1) hW
    (fun i v hv=>he i.1 i.2 v hv)
  simpa only [Fintype.sum_prod_type,bandMass] using hh
end KServer.PrefixTree

end


/-! Full signed heavy-travel telescope for the actual joint experiment. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointHeavy
open JointExperiment JointAllocation LevelKeys TierProcess AnchorTravel HeavyAnchorDynamics
open RankTracking PosteriorRanks ActualCharges
attribute [local instance] Classical.propDecidable Classical.decEq keyDecEq poolDecEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0 < r d) (hk:1≤(k:ℝ))

lemma potential_bounds (t:ℕ) (ω:Atom (k:=k) law hr):
    potential s law hr hk t ω∈Set.Icc 0 (((6/5:ℝ)*72)*k*(∑ d,r d)):=
  raw_bounds (fun d=>(hr d).le) (by norm_num) _ _ _ _ (c_bounds s law hr hk t ω)

lemma heavy_eq_of_map_eq (t t':ℕ) (ω:Atom (k:=k) law hr) (d:Fin L) (x y:Y)
    (he:maps law hr s t ω d.val x=maps law hr s t' ω d.val y):
    key s law hr t ω d x=key s law hr t' ω d y:=by
  have hmem a:
      key s law hr t ω d x=some a ↔ key s law hr t' ω d y=some a:=by
    have h1:=HeavyAnchorDynamics.level_heavy s law (hr d).le ω.val.1 (ω.val.2 d) t x a
    have h2:=HeavyAnchorDynamics.level_heavy s law (hr d).le ω.val.1 (ω.val.2 d) t' y a
    change _↔_ at h1 h2
    have hm:LevelKeys.map s law (hr d).le ω.val.1 (ω.val.2 d) t x=
        LevelKeys.map s law (hr d).le ω.val.1 (ω.val.2 d) t' y:=by
      simpa only [maps,dite_eq_left d.isLt] using he
    exact h1.symm.trans ((congrArg (fun z=>z=slot (k:=k) a) hm).to_iff.trans h2)
  cases h1:key s law hr t ω d x with
  | none=>
    cases h2:key s law hr t' ω d y with
    | none=>rfl
    | some a=>exact False.elim (by have hh:=(hmem a).mpr h2; rw [h1] at hh; cases hh)
  | some a=>exact ((hmem a).mp h1).symm

lemma heavy_cross_le (t:ℕ) (ω:Atom (k:=k) law hr):
    (∑ i:Fin k,∑ d:Fin L,r d*(if key s law hr (t+1) ω d (hidden law hr s (t+1) ω i)=
      key s law hr t ω d (hidden law hr s t ω i) then 0 else 1))≤
        ∑ d:Fin L,r d*HierarchicalQuota.keyCross (maps law hr s) (hidden law hr s) d.val t ω:=by
  rw [sum_comm]
  apply sum_le_sum
  intro d _
  unfold HierarchicalQuota.keyCross
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hr d).le
  by_cases he:maps law hr s (t+1) ω d.val (hidden law hr s (t+1) ω i)=
      maps law hr s t ω d.val (hidden law hr s t ω i)
  · simp only [ite_eq_left he,ite_eq_left (heavy_eq_of_map_eq s law hr (t+1) t ω d _ _ he),le_refl]
  · simp only [ite_eq_right he]
    split_ifs <;> norm_num

lemma travel_raw {C:ℝ} {R τ:ℝ} (hR:0≤R) (hτ:2≤τ)
    (hrad:∀ d,r d=ParkedCoefficients.radius R τ d.val)
    (hC:(7*((6/5:ℝ)*72)/Real.log 2+2*(6/5:ℝ)*72)*(1+Real.log ((k:ℝ)+1))≤C):
    total (weight law hr) H (travel s law hr hk)≤
      4*((6/5:ℝ)*72)*total (weight law hr) H (fun t ω=>
        ∑ d:Fin L,r d*HierarchicalQuota.keyCross (maps law hr s) (hidden law hr s) d.val t ω)+
      4*C/3*total (weight law hr) H (fun t ω=>(∑ i:Fin k,dist (hidden law hr s t ω i) (hidden law hr s (t+1) ω i)))+
      4*total (weight law hr) H (charge s law hr hk)+4*(((6/5:ℝ)*72)*k*(∑ d,r d)):=by
  let P:=fun t=>avg (weight law hr) (potential s law hr hk t)
  let E:=fun t=> ((6/5:ℝ)*72)*avg (weight law hr) (fun ω=>
      ∑ d:Fin L,r d*HierarchicalQuota.keyCross (maps law hr s) (hidden law hr s) d.val t ω)+
    C/3*avg (weight law hr) (fun ω=>(∑ i:Fin k,dist (hidden law hr s t ω i) (hidden law hr s (t+1) ω i)))+
      avg (weight law hr) (charge s law hr hk t)
  have hp:0≤P H:=sum_nonneg (fun ω _=>mul_nonneg (weight_nonneg law hr ω) (potential_bounds s law hr hk H ω).1)
  have hb:P 0≤((6/5:ℝ)*72)*k*(∑ d,r d):=by
    have hh:=avg_mono (weight_nonneg law hr) (fun ω=>(potential_bounds s law hr hk 0 ω).2)
    simpa only [avg_const,weight_sum,one_mul] using hh
  have hs:∀ t,t<H→P (t+1)-P t+avg (weight law hr) (travel s law hr hk t)/4≤E t:=by
    intro t ht
    have hh:=expected_payment s law hr hk ⟨t,ht⟩ (fun ω i=>(cutoff_sum s law hr hk t ω
      (hidden law hr s t ω i) hR hτ hrad).trans hC)
    have hx:=mul_le_mul_of_nonneg_left (avg_mono (weight_nonneg law hr) (heavy_cross_le s law hr t))
        (by norm_num : (0:ℝ)≤(6/5:ℝ)*72)
    change _≤_ at hh
    dsimp only [P,E]
    linarith
  have hh:=chronological_telescope P (fun t=>avg (weight law hr) (travel s law hr hk t)) E H hp hb hs
  simp only [E,sum_add_distrib,←mul_sum] at hh
  change total _ _ _≤_ at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  unfold total
  ring
end KServer.JointHeavy

end


/-! Actual heavy references and fixed-band changes, charged to full-key
transport and the variation of the complete park inventory. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointHeavy
open JointExperiment JointAllocation LevelKeys TierProcess AnchorTravel HeavyAnchorDynamics
open RankTracking PosteriorRanks ActualCharges
attribute [local instance] Classical.propDecidable Classical.decEq keyDecEq poolDecEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0 < r d) (hk:1≤(k:ℝ))

omit [MetricSpace Y] [NeZero k] in
lemma slot_injective:Function.Injective (slot (Y:=Y) (k:=k)):=by
  intro a b he
  exact Sigma.mk.inj_iff.mp (Sum.inl.inj he) |>.2 |> eq_of_heq

lemma refresh_bound (N:ℕ):
    total (weight law hr) N (fun t ω=>∑ d:Fin L,∑ a:J (Y:=Y),
      r d*KeySizeTracking.refreshCost (size s law hr d.val (slot (k:=k) a)) t ω)≤
      288*(1+Real.log ((k:ℝ)+1))*total (weight law hr) N (fun t ω=>
        ∑ d:Fin L,r d*HierarchicalQuota.keyCross (maps law hr s) (hidden law hr s) d.val t ω)+
      (∑ d,r d)*(Fintype.card (LevelKeys.Key Y k)*(288*((k:ℝ)+1)*(1+(1+Real.log ((k:ℝ)+1))))):=by
  have esize (d:ℕ) (a:LevelKeys.Key Y k):
      size s law hr d a=KeyReferences.size (w:=weight law hr) (history law hr)
        (maps law hr s) (hidden law hr s) d a:=rfl
  have hh:=sum_le_sum (s:=(univ:Finset (Fin L))) (fun d _=>mul_le_mul_of_nonneg_left
    (KeyReferences.refresh_subset (weight_nonneg law hr) (weight_pos law hr) (weight_sum law hr)
      (history law hr) (history_refines law hr) (maps law hr s) (hidden law hr s)
      (slot (k:=k)) slot_injective d.val N) (hr d).le)
  calc
    _ = ∑ d:Fin L,r d*total (weight law hr) N (fun t ω=>∑ a:J (Y:=Y),
      KeySizeTracking.refreshCost (size s law hr d.val (slot (k:=k) a)) t ω):=by
        simp only [total_sum,total_mul,mul_sum]
    _ ≤ ∑ d:Fin L,r d*(288*(1+Real.log ((k:ℝ)+1))*
      total (weight law hr) N (HierarchicalQuota.keyCross (maps law hr s) (hidden law hr s) d.val)+
      Fintype.card (LevelKeys.Key Y k)*(288*((k:ℝ)+1)*(1+(1+Real.log ((k:ℝ)+1))))):=by
        simp only [esize,total_sum]
        exact hh
    _ = _:=by
      simp only [total_sum,total_mul,mul_add,sum_add_distrib,mul_sum,sum_mul]
      congr 1
      apply sum_congr rfl
      intro d _
      ring

lemma band_variation_bound (t:ℕ) (ω:Atom (k:=k) law hr)
    (W:PrefixTree.Node (LevelKeys.Key Y k) L→ℝ) (hW:∀ v,0≤W v)
    (he:∀ d a v,v∈PrefixTree.band (LevelKeys.Key Y k) L d.val (slot (k:=k) a)→ r d=W v):
    (∑ d:Fin L,∑ a:J (Y:=Y),r d*|b s law hr hk (t+1) ω d a-b s law hr hk t ω d a|)≤
      ∑ v,W v*|park s law hr hk (t+1) ω v-park s law hr hk t ω v|:=
  PrefixTree.band_variation (LevelKeys.Key Y k) L (slot (k:=k)) slot_injective _ _ W r
    (fun d=>(hr d).le) hW he

lemma charge_bound (N:ℕ) (W:PrefixTree.Node (LevelKeys.Key Y k) L→ℝ) (hW:∀ v,0≤W v)
    (he:∀ d a v,v∈PrefixTree.band (LevelKeys.Key Y k) L d.val (slot (k:=k) a)→ r d=W v):
    total (weight law hr) N (charge s law hr hk)≤
      ((6/5:ℝ)*72)*288*(1+Real.log ((k:ℝ)+1))*total (weight law hr) N (fun t ω=>
        ∑ d:Fin L,r d*HierarchicalQuota.keyCross (maps law hr s) (hidden law hr s) d.val t ω)+
      2*(6/5:ℝ)*total (weight law hr) N (fun t ω=>∑ v,W v*|park s law hr hk (t+1) ω v-park s law hr hk t ω v|)+
      ((6/5:ℝ)*72)*(∑ d,r d)*(Fintype.card (LevelKeys.Key Y k)*(288*((k:ℝ)+1)*(1+(1+Real.log ((k:ℝ)+1))))):=by
  have h1:=mul_le_mul_of_nonneg_left (refresh_bound s law hr N) (by norm_num : (0:ℝ)≤(6/5:ℝ)*72)
  have h2:=mul_le_mul_of_nonneg_left (total_mono (weight_nonneg law hr) (N:=N)
    (fun t ω=>band_variation_bound s law hr hk t ω W hW he)) (by norm_num : (0:ℝ)≤2*(6/5:ℝ))
  have heqpoint (t:ℕ) (ω:Atom (k:=k) law hr):charge s law hr hk t ω=
      ((6/5:ℝ)*72)*(∑ d:Fin L,∑ a:J (Y:=Y),
        r d*KeySizeTracking.refreshCost (size s law hr d.val (slot (k:=k) a)) t ω)+
      2*(6/5:ℝ)*(∑ d:Fin L,∑ a:J (Y:=Y),
        r d*|b s law hr hk (t+1) ω d a-b s law hr hk t ω d a|):=by
    simp only [JointHeavy.charge,mul_sum,←sum_add_distrib]
    apply sum_congr rfl
    intro d _
    apply sum_congr rfl
    intro a _
    ring
  have heq:=congrArg (total (weight law hr) N) (funext (fun t=>funext (heqpoint t)))
  simp only [total_add,total_mul] at heq
  rw [heq]
  nlinarith
end KServer.JointHeavy

end


/-! Completion of the genuine observed prefix to an atom is used only on
positive fibers. Impossible histories receive the fixed root stock. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointHistory
open JointExperiment
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0 < r d) (hk:1≤(k:ℝ))

omit [MetricSpace Y] [Fintype Y] in
lemma prefix_of_take_eq (σ ρ:Fin H→Y) (t:ℕ)
    (h:(List.ofFn σ).take t=(List.ofFn ρ).take t):
    FiniteExperiment.requestPrefix σ t=FiniteExperiment.requestPrefix ρ t:=by
  funext i
  by_cases hi:i.val<t
  · have hh:=congrArg (fun xs:List Y=>xs[i.val]?) h
    simpa only [List.getElem?_take,ite_eq_left hi,List.getElem?_ofFn,dite_eq_left i.isLt,
      Fin.eta,FiniteExperiment.requestPrefix,ite_eq_left hi] using hh
  · simp only [FiniteExperiment.requestPrefix,ite_eq_right hi]

omit [NeZero k] in
lemma observed_true (ω:Atom (k:=k) law hr) (t:ℕ) (ht:t≤H):
    Observed law hr ω.val.2 ((List.ofFn ω.val.1).take t) ω:=by
  have he:((List.ofFn ω.val.1).take t).length=t:=by simp only [List.length_take,List.length_ofFn,Nat.min_eq_left ht]
  exact ⟨rfl,by rwa [he],by rw [he]⟩

omit [NeZero k] in
lemma observed_history (a:Tape Y k H L r) (h:List Y) (ω ρ:Atom (k:=k) law hr)
    (hω:Observed law hr a h ω) (hρ:Observed law hr a h ρ):
    history law hr h.length ω=history law hr h.length ρ:=by
  apply (FiniteExperiment.history_eq_iff _ _ _).mpr
  exact ⟨hω.1.trans hρ.1.symm,prefix_of_take_eq ω.val.1 ρ.val.1 h.length (hω.2.2.trans hρ.2.2.symm)⟩

lemma q_eq (a:Tape Y k H L r) (h:List Y) (ω:Atom (k:=k) law hr)
    (hω:Observed law hr a h ω):q s law hr hk a h=JointAllocation.quota s law hr hk h.length ω:=by
  have hp:∃ ω,Observed law hr a h ω:=⟨ω,hω⟩
  rw [q,dite_eq_left hp]
  exact JointAllocation.quota_adapted s law hr hk _ hp.choose ω
    (observed_history law hr a h hp.choose ω hp.choose_spec hω)

lemma anchors_adapted (t:ℕ) (ω ρ:Atom (k:=k) law hr)
    (h:history law hr t ω=history law hr t ρ):anchors s law hr t ω=anchors s law hr t ρ:=by
  obtain ⟨ha,hp⟩:=history_eq law hr t ω ρ h
  funext d key
  unfold anchors
  split_ifs with hd
  · rw [ha]
    exact congrFun (KeysAdapted.anchor_adapted s law (hr ⟨d,hd⟩).le (ρ.val.2 ⟨d,hd⟩) t ω.val.1 ρ.val.1
      ((FiniteExperiment.requestHistory_eq_iff _ _ _).mpr hp)) key
  · rfl

lemma a_eq (tape:Tape Y k H L r) (h:List Y) (ω:Atom (k:=k) law hr)
    (hω:Observed law hr tape h ω):a s law hr tape h=anchors s law hr h.length ω:=by
  have hp:∃ ω,Observed law hr tape h ω:=⟨ω,hω⟩
  rw [a,dite_eq_left hp]
  exact anchors_adapted s law hr _ _ _ (observed_history law hr tape h hp.choose ω hp.choose_spec hω)
end KServer.JointHistory

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_MetricMatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! In a finite laminar tree, one matching simultaneously has the optimal
crossing count at every cut. This is proved by the uncrossing minimizer, rather
than assuming a transport/matching interface. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.LaminarMatching
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V Z I:Type*} [Fintype V] [Fintype I]

lemma pair_inequality (a b c d:Bool) (h:a=d ∨ c=b):
    |bit a-bit d|+|bit c-bit b|≤|bit a-bit b|+|bit c-bit d|:=by
  cases a <;> cases b <;> cases c <;> cases d <;> norm_num [bit] at *

omit [Fintype V] in
lemma laminar_pair {c:V→Z→Bool} (hc:Laminar c) (v w:V) {a b d e:Z}
    (ha:c v a=true) (hb:c v b=false) (hd:c v d=false) (he:c v e=true):
    c w a=c w e ∨ c w d=c w b:=by
  rcases hc v w with h|h|h
  · exact Or.inl ((h a ha).trans (h e he).symm)
  · right
    have hb':c w b=false:=by cases hcb:c w b; rfl; have :=h b hcb; simp [hb] at this
    have hd':c w d=false:=by cases hcd:c w d; rfl; have :=h d hcd; simp [hd] at this
    exact hd'.trans hb'.symm
  · exact Or.inl ((h a ha).trans (h e he).symm)

lemma two_term_sum {f g:I→ℝ} {i j:I} (hij:i≠j)
    (h:∀ x,x≠i→x≠j→f x=g x):
    (∑ x,f x)-(∑ x,g x)=(f i+f j)-(g i+g j):=by
  rw [←sum_sub_distrib]
  have hh:(∑ x,(f x-g x))=(f i-g i)+(f j-g j):=by
    rw [←add_sum_erase univ _ (mem_univ i)]
    rw [←add_sum_erase (univ.erase i) _ (mem_erase.mpr ⟨Ne.symm hij,mem_univ j⟩)]
    have hz:(∑ x∈(univ.erase i).erase j,(f x-g x))=0:=by
      apply sum_eq_zero
      intro x hx
      rw [h x (mem_erase.mp (mem_erase.mp hx).2).1 (mem_erase.mp hx).1,sub_self]
    rw [hz,add_zero]
  rw [hh]
  ring

omit [Fintype V] in
lemma swapped_cuts {c:V→Z→Bool} (hc:Laminar c) (f g:I→Z) (π:Equiv.Perm I) (v:V) (i j:I)
    (ha:c v (f i)=true) (hb:c v (g (π i))=false)
    (hd:c v (f j)=false) (he:c v (g (π j))=true):
    ∀ w,(∑ x,cross c f g ((Equiv.swap i j).trans π) w x)≤∑ x,cross c f g π w x:=by
  have hij:i≠j:=by intro hij; subst j; simp [ha] at hd
  intro w
  have hsum:=two_term_sum (f:=cross c f g ((Equiv.swap i j).trans π) w)
    (g:=cross c f g π w) hij (fun x hxi hxj=>by
      simp only [cross,Equiv.trans_apply,Equiv.swap_apply_of_ne_of_ne hxi hxj])
  have hh:=pair_inequality (c w (f i)) (c w (g (π i))) (c w (f j)) (c w (g (π j)))
    (laminar_pair hc v w ha hb hd he)
  simp only [cross,Equiv.trans_apply,Equiv.swap_apply_left,Equiv.swap_apply_right] at hsum
  simp only [cross,Equiv.trans_apply]
  linarith

lemma swapped_strict {c:V→Z→Bool} (hc:Laminar c) (f g:I→Z) (π:Equiv.Perm I) (v:V) (i j:I)
    (ha:c v (f i)=true) (hb:c v (g (π i))=false)
    (hd:c v (f j)=false) (he:c v (g (π j))=true):
    cost c f g ((Equiv.swap i j).trans π) < cost c f g π:=by
  apply sum_lt_sum (fun w _=>swapped_cuts hc f g π v i j ha hb hd he w)
  refine ⟨v,mem_univ _,?_⟩
  have hij:i≠j:=by intro hij; subst j; simp [ha] at hd
  have hsum:=two_term_sum (f:=cross c f g ((Equiv.swap i j).trans π) v)
    (g:=cross c f g π v) hij (fun x hxi hxj=>by
      simp only [cross,Equiv.trans_apply,Equiv.swap_apply_of_ne_of_ne hxi hxj])
  norm_num [cross,Equiv.trans_apply,ha,hb,hd,he,bit] at hsum
  simp only [cross,Equiv.trans_apply,bit]
  linarith

lemma bit_lt {a b:Bool} (h:bit a<bit b):a=false ∧ b=true:=by
  cases a <;> cases b <;> norm_num [bit] at *

/-- An optimal permutation has no opposite crossings at any cut. -/
lemma minimizing_oriented {c:V→Z→Bool} (hc:Laminar c) (f g:I→Z) (π:Equiv.Perm I)
    (hm:∀ ρ,cost c f g π ≤ cost c f g ρ) (v:V):
    (∀ i,bit (c v (f i))≤bit (c v (g (π i)))) ∨
      (∀ i,bit (c v (g (π i)))≤bit (c v (f i))):=by
  by_cases h:∀ i,bit (c v (f i))≤bit (c v (g (π i)))
  · exact Or.inl h
  · right
    push Not at h
    obtain ⟨i,hi⟩:=h
    obtain ⟨hb,ha⟩:=bit_lt hi
    intro j
    by_contra hj
    obtain ⟨hd,he⟩:=bit_lt (lt_of_not_ge hj)
    exact (not_lt_of_ge (hm _)) (swapped_strict hc f g π v i j ha hb hd he)

omit [Fintype V] in
lemma oriented_cross {c:V→Z→Bool} (f g:I→Z) (π:Equiv.Perm I) (v:V)
    (h:(∀ i,bit (c v (f i))≤bit (c v (g (π i)))) ∨
      (∀ i,bit (c v (g (π i)))≤bit (c v (f i)))):
    (∑ i,cross c f g π v i)=|(∑ i,bit (c v (f i)))-(∑ i,bit (c v (g i)))|:=by
  have he:(∑ i,bit (c v (g (π i))))=∑ i,bit (c v (g i)):=Equiv.sum_comp π (fun i=>bit (c v (g i)))
  rw [←he,←sum_sub_distrib]
  rcases h with h|h
  · rw [abs_of_nonpos (sum_nonpos (fun i _=>sub_nonpos.mpr (h i))),←sum_neg_distrib]
    apply sum_congr rfl
    intro i _
    exact abs_of_nonpos (sub_nonpos.mpr (h i))
  · rw [abs_of_nonneg (sum_nonneg (fun i _=>sub_nonneg.mpr (h i)))]
    exact sum_congr rfl (fun i _=>abs_of_nonneg (sub_nonneg.mpr (h i)))

/-- One matching is optimal at every member of the laminar family. -/
theorem exists_simultaneous {c:V→Z→Bool} (hc:Laminar c) (f g:I→Z):
    ∃ π:Equiv.Perm I,∀ v,(∑ i,cross c f g π v i)=
      |(∑ i,bit (c v (f i)))-(∑ i,bit (c v (g i)))|:=by
  obtain ⟨π,_,hm⟩:=Finset.exists_min_image (univ:Finset (Equiv.Perm I)) (cost c f g) univ_nonempty
  refine ⟨π,fun v=>oriented_cross f g π v ?_⟩
  exact minimizing_oriented hc f g π (fun ρ=>hm ρ (mem_univ _)) v

end KServer.LaminarMatching

end


/-! The concrete parent-ordered tree's descendant cuts form a laminar family. -/
noncomputable section
namespace KServer.Rounding
variable {n:ℕ} [NeZero n]

lemma Tree.under_trans (T:Tree n) (a b c:Fin n)
    (hab:T.under a b=true) (hbc:T.under b c=true):T.under a c=true:=by
  by_cases hcb:c=b
  · simpa only [hcb] using hab
  by_cases hc:c=0
  · subst c
    have hb:b=0:=by simpa only [Tree.under_zero,beq_iff_eq] using hbc
    exact False.elim (hcb hb.symm)
  have hp:T.under b (T.parent c)=true:=by
    rw [Tree.under,ite_eq_right hcb,dite_eq_right hc] at hbc
    exact hbc
  have ha:=T.under_trans a b (T.parent c) hab hp
  by_cases hca:c=a
  · rw [hca]; exact T.under_self a
  · rw [Tree.under,ite_eq_right hca,dite_eq_right hc]
    exact ha
termination_by c.val
decreasing_by exact T.lower c hc

lemma Tree.ancestors_comparable (T:Tree n) (a b c:Fin n)
    (ha:T.under a c=true) (hb:T.under b c=true):
    T.under a b=true ∨ T.under b a=true:=by
  by_cases hca:c=a
  · exact Or.inr (hca ▸ hb)
  by_cases hcb:c=b
  · exact Or.inl (hcb ▸ ha)
  by_cases hc:c=0
  · subst c
    have haa:a=0:=by simpa only [Tree.under_zero,beq_iff_eq] using ha
    exact False.elim (hca haa.symm)
  have ha':T.under a (T.parent c)=true:=by
    rw [Tree.under,ite_eq_right hca,dite_eq_right hc] at ha
    exact ha
  have hb':T.under b (T.parent c)=true:=by
    rw [Tree.under,ite_eq_right hcb,dite_eq_right hc] at hb
    exact hb
  exact T.ancestors_comparable a b (T.parent c) ha' hb'
termination_by c.val
decreasing_by exact T.lower c hc

lemma Tree.laminar (T:Tree n):LaminarMatching.Laminar T.under:=by
  intro v w
  by_cases hvw:T.under v w=true
  · right; left; intro z hz; exact T.under_trans v w z hvw hz
  by_cases hwv:T.under w v=true
  · left; intro z hz; exact T.under_trans w v z hwv hz
  right; right
  intro z hz
  cases hh:T.under w z
  · rfl
  · exact False.elim ((T.ancestors_comparable v w z hz hh).elim hvw hwv)

end KServer.Rounding

end


/-! Metric movement of the simultaneous laminar matching. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.Rounding
variable {n:ℕ} [NeZero n]
attribute [local instance] Classical.propDecidable Classical.decEq

lemma Tree.cutDistance_self (T:Tree n) (w:Fin n→ℝ) (u:Fin n):T.cutDistance w u u=0:=by
  simp only [Tree.cutDistance,sub_self,abs_zero,mul_zero,sum_const_zero]

end KServer.Rounding

end


/-! A deepest common ancestor exposes a discrepant cut. This permits bounds
using witnesses only at occupied endpoints; no empty-prefix anchor edge is
assumed short. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.Rounding
attribute [local instance] Classical.propDecidable Classical.decEq
variable {n:ℕ} [NeZero n]

lemma Tree.parent_under (T:Tree n) (u:Fin n):T.under (T.parent u) u=true:=by
  by_cases hu:u=0
  · subst u; rw [T.root]; exact T.under_self 0
  have hn:u≠T.parent u:=by intro he; have hh:=T.lower u hu; have hv:=congrArg Fin.val he; omega
  rw [Tree.under,ite_eq_right hn,dite_eq_right hu]
  exact T.under_self _

lemma Tree.path_child (T:Tree n) (p u:Fin n) (h:T.under p u=true) (hne:p≠u):
    ∃ z:Fin n,z≠0 ∧ T.parent z=p ∧ T.under z u=true:=by
  have hu:u≠0:=by
    intro hu
    subst u
    have hp:p=0:=by simpa only [Tree.under_zero,beq_iff_eq] using h
    exact hne hp
  by_cases he:T.parent u=p
  · exact ⟨u,hu,he,T.under_self u⟩
  have hh:T.under p (T.parent u)=true:=by
    rw [Tree.under,ite_eq_right (Ne.symm hne),dite_eq_right hu] at h
    exact h
  obtain ⟨z,hz,hp,hs⟩:=T.path_child p (T.parent u) hh (Ne.symm he)
  exact ⟨z,hz,hp,T.under_trans z (T.parent u) u hs (T.parent_under u)⟩
termination_by u.val
decreasing_by exact T.lower u hu

lemma Tree.common_cut (T:Tree n) (u v:Fin n) (hne:u≠v):
    ∃ p z:Fin n,T.under p u=true ∧ T.under p v=true ∧ T.parent z=p ∧
      T.under z u≠T.under z v:=by
  let F:Finset (Fin n):=univ.filter (fun p=>T.under p u=true ∧ T.under p v=true)
  have hF:F.Nonempty:=⟨0,mem_filter.mpr ⟨mem_univ _,T.under_root u,T.under_root v⟩⟩
  let p:=F.max' hF
  have hp:p∈F:=max'_mem F hF
  have hp1:T.under p u=true:=(mem_filter.mp hp).2.1
  have hp2:T.under p v=true:=(mem_filter.mp hp).2.2
  have hzfalse:∀ z,z≠0→T.parent z=p→T.under z u=true→T.under z v=true→False:=by
    intro z hz he hzu hzv
    have hzF:z∈F:=mem_filter.mpr ⟨mem_univ _,hzu,hzv⟩
    have hl:z≤p:=le_max' F z hzF
    have hh:=T.lower z hz
    rw [he] at hh
    exact (not_lt_of_ge hl hh)
  by_cases hpu:p=u
  · obtain ⟨z,hz,he,hzv⟩:=T.path_child p v hp2 (by simpa only [hpu] using hne)
    exact ⟨p,z,hp1,hp2,he,fun hze=>hzfalse z hz he (hze.trans hzv) hzv⟩
  · obtain ⟨z,hz,he,hzu⟩:=T.path_child p u hp1 hpu
    exact ⟨p,z,hp1,hp2,he,fun hze=>hzfalse z hz he hzu (hze.symm.trans hzu)⟩

lemma Tree.distinct_le_cut {X:Type*} [PseudoMetricSpace X] (T:Tree n)
    (w:Fin n→ℝ) (hw:∀ z,0≤w z) {C:ℝ} (hC:0≤C)
    (a b:X) (u v:Fin n) (hne:u≠v)
    (hc:∀ p,T.under p u=true→T.under p v=true→dist a b≤C*w p):
    dist a b≤C*T.cutDistance (fun z=>w (T.parent z)) u v:=by
  obtain ⟨p,z,hp1,hp2,he,hz⟩:=T.common_cut u v hne
  have hbit:|T.indicator z u-T.indicator z v|=1:=by
    unfold Tree.indicator
    cases h1:T.under z u <;> cases h2:T.under z v <;> simp_all
  have hh:w p≤T.cutDistance (fun z=>w (T.parent z)) u v:=by
    have hs:=single_le_sum (s:=(univ:Finset (Fin n))) (f:=fun z=>w (T.parent z)*|T.indicator z u-T.indicator z v|)
      (fun z _=>mul_nonneg (hw _) (abs_nonneg _)) (mem_univ z)
    simpa only [he,hbit,mul_one,Tree.cutDistance] using hs
  exact (hc p hp1 hp2).trans (mul_le_mul_of_nonneg_left hh hC)
end KServer.Rounding

end


/-! Every ancestor of an occupied word is witnessed by the same point. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable (A:Type) [Fintype A] (L:ℕ)

omit [Fintype A] in
lemma hit_parent {Y:Type} (maps:ℕ→Y→A) (v:Vertex A L) (y:Y)
    (hy:HierarchyCounts.hit maps v.2 y):
    HierarchyCounts.hit maps (parent A L v).2 y:=by
  rcases v with ⟨⟨d,hd⟩,f⟩
  cases d with
  | zero=>intro i; exact Fin.elim0 i
  | succ d=>
    rw [parent_succ]
    intro i
    exact hy i.castSucc

lemma under_depth (u v:Node A L) (h:(travelTree A L).under u v=true):
    depth A L u≤depth A L v:=by
  by_cases he:v=u
  · subst v; exact le_rfl
  have hv:v≠0:=by
    intro h0; subst v
    have hu:u=0:=by simpa only [Rounding.Tree.under_zero,beq_iff_eq] using h
    exact he hu.symm
  rw [Rounding.Tree.under,ite_eq_right he,dite_eq_right hv] at h
  have ih:=under_depth u ((travelTree A L).parent v) h
  have hd:0<(numbering A L v).1.val:=by
    apply Nat.pos_of_ne_zero
    intro hh
    exact hv ((numbering_eq_root A L v).mp ((depth_zero_iff A L _).mp hh))
  change (numbering A L u).1.val≤(numbering A L v).1.val
  change (numbering A L u).1.val≤(numbering A L ((travelTree A L).parent v)).1.val at ih
  rw [numbering_parent,parent_depth A L _ hd] at ih
  omega
termination_by v.val
decreasing_by exact (travelTree A L).lower v hv

lemma under_hit {Y:Type} (maps:ℕ→Y→A) (u v:Node A L)
    (h:(travelTree A L).under u v=true) (y:Y)
    (hy:HierarchyCounts.hit maps (numbering A L v).2 y):
    HierarchyCounts.hit maps (numbering A L u).2 y:=by
  by_cases he:v=u
  · subst v; exact hy
  have hv:v≠0:=by
    intro h0; subst v
    have hu:u=0:=by simpa only [Rounding.Tree.under_zero,beq_iff_eq] using h
    exact he hu.symm
  rw [Rounding.Tree.under,ite_eq_right he,dite_eq_right hv] at h
  apply under_hit maps u ((travelTree A L).parent v) h y
  rw [numbering_parent]
  exact hit_parent A L maps _ y hy
termination_by v.val
decreasing_by exact (travelTree A L).lower v hv

end KServer.PrefixTree

end


/-! Geometric comparisons only at witnessed occupied words. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable (A:Type) [Fintype A] (L:ℕ)
variable {Y:Type} [MetricSpace Y]

lemma last_none (v:Node A L):lastKey A L v=none ↔ v=0:=by
  unfold lastKey
  split_ifs with h
  · simp only [false_iff]
    intro hv; subst v
    rw [depth,numbering_zero] at h
    change 0<0 at h
    omega
  · have hz:(numbering A L v).1.val=0:=by change ¬0<(numbering A L v).1.val at h; omega
    have hv:= (numbering_eq_root A L v).mp ((depth_zero_iff A L _).mp hz)
    simp only [hv]

lemma last_depth {v:Node A L} {key:A} (h:lastKey A L v=some key):
    0<depth A L v ∧ v∈band A L (depth A L v-1) key:=by
  have hd:0<depth A L v:=by
    by_contra hh
    simp only [lastKey,dite_eq_right hh] at h
    cases h
  exact ⟨hd,mem_filter.mpr ⟨mem_univ _,by omega,h⟩⟩

lemma weight_under {R τ:ℝ} (hR:0≤R) (hτ:1≤τ) {u v:Node A L}
    (h:(travelTree A L).under u v=true):
    weight A L R τ v≤weight A L R τ u:=
  ParkedCoefficients.radius_antitone hR hτ (under_depth A L u v h)

lemma anchor_witness (z:Y) (a:ℕ→A→Y) (maps:ℕ→Y→A) {R τ:ℝ}
    (ha:∀ d,d<L→∀ y,dist (a d (maps d y)) y≤20*(R/τ^(d+1)))
    (v:Node A L) (hv:v≠0) (y:Y) (hy:HierarchyCounts.hit maps (numbering A L v).2 y):
    dist (nodeAnchor A L z a v) y≤20*weight A L R τ v:=by
  cases he:lastKey A L v with
  | none=>exact False.elim (hv ((last_none A L v).mp he))
  | some key=>
    obtain ⟨hd,hb⟩:=last_depth A L he
    have hkey:=band_key A L maps (depth A L v-1) key hb y hy
    have hL:depth A L v-1<L:=by have hh:=(numbering A L v).1.isLt; change depth A L v<L+1 at hh; omega
    have hh:=ha (depth A L v-1) hL y
    rw [hkey] at hh
    have hdep:depth A L v-1+1=depth A L v:=by omega
    rw [hdep] at hh
    simpa only [nodeAnchor,he,weight,depth] using hh

lemma witnessed_common_bound (z:Y) (a b:ℕ→A→Y) (maps next:ℕ→Y→A) {R τ:ℝ}
    (hR:0≤R) (hτ:1≤τ) (hdia:∀ x y:Y,dist x y≤R)
    (ha:∀ d,d<L→∀ y,dist (a d (maps d y)) y≤20*(R/τ^(d+1)))
    (hb:∀ d,d<L→∀ y,dist (b d (next d y)) y≤20*(R/τ^(d+1)))
    (hab:∀ d,d<L→∀ x y key,maps d x=key→next d y=key→dist (a d key) (b d key)≤40*(R/τ^(d+1)))
    (u v p:Node A L) (hpu:(travelTree A L).under p u=true) (hpv:(travelTree A L).under p v=true)
    (x y:Y) (hx:HierarchyCounts.hit maps (numbering A L u).2 x)
    (hy:HierarchyCounts.hit next (numbering A L v).2 y):
    dist (nodeAnchor A L z a u) (nodeAnchor A L z b v)≤120*weight A L R τ p:=by
  by_cases hp:p=0
  · subst p
    have hw:weight A L R τ (0:Node A L)=R:=by
      rw [weight,numbering_zero]
      change R/τ^0=R
      simp
    rw [hw]
    exact (hdia _ _).trans (by nlinarith)
  have hdu:0<depth A L p:=by
    apply Nat.pos_of_ne_zero
    intro hh
    exact hp ((numbering_eq_root A L p).mp ((depth_zero_iff A L _).mp hh))
  have hz:depth A L (0:Node A L)=0:=by rw [depth,numbering_zero]; rfl
  have hu:u≠0:=by intro he; subst u; have hh:=under_depth A L p 0 hpu; rw [hz] at hh; omega
  have hv:v≠0:=by intro he; subst v; have hh:=under_depth A L p 0 hpv; rw [hz] at hh; omega
  have hxp:=under_hit A L maps p u hpu x hx
  have hyp:=under_hit A L next p v hpv y hy
  have h1:=anchor_witness A L z a maps ha u hu x hx
  have h2:=anchor_witness A L z a maps ha p hp x hxp
  have h3:=anchor_witness A L z b next hb p hp y hyp
  have h4:=anchor_witness A L z b next hb v hv y hy
  have huW:=weight_under A L hR hτ hpu
  have hvW:=weight_under A L hR hτ hpv
  have hm:dist (nodeAnchor A L z a p) (nodeAnchor A L z b p)≤40*weight A L R τ p:=by
    cases he:lastKey A L p with
    | none=>exact False.elim (hp ((last_none A L p).mp he))
    | some key=>
      obtain ⟨hp0,hpb⟩:=last_depth A L he
      have hL:depth A L p-1<L:=by have hh:=(numbering A L p).1.isLt; change depth A L p<L+1 at hh; omega
      have hh:=hab (depth A L p-1) hL x y key
        (band_key A L maps _ key hpb x hxp) (band_key A L next _ key hpb y hyp)
      have hd:depth A L p-1+1=depth A L p:=by omega
      rw [hd] at hh
      simpa only [nodeAnchor,he,weight,depth] using hh
  have ht1:=dist_triangle (nodeAnchor A L z a u) x (nodeAnchor A L z a p)
  have ht2:=dist_triangle (nodeAnchor A L z b p) y (nodeAnchor A L z b v)
  rw [dist_comm x (nodeAnchor A L z a p)] at ht1
  rw [dist_comm y (nodeAnchor A L z b v)] at ht2
  have ht3:=dist_triangle4 (nodeAnchor A L z a u) (nodeAnchor A L z a p)
    (nodeAnchor A L z b p) (nodeAnchor A L z b v)
  linarith
end KServer.PrefixTree

end


/-! An actual labeled list of k occupied vertices for every consistent
nonnegative integral count state. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TreeRounding
open Rounding
attribute [local instance] Classical.propDecidable Classical.decEq
variable {n k:ℕ} [NeZero n]

lemma slots_positive (T:Tree n) (c:Counts n) (hc:T.Consistent c)
    (hp:∀ v,0 ≤ c.park v) (hr:c.subtree 0=(k:ℤ)) (i:Fin k):0 < c.park (slots T c hc hp hr i):=by
  have hi:=((countEquiv T c hc hp hr).symm i).2.isLt
  change _<(c.park (slots T c hc hp hr i)).toNat at hi
  omega

end KServer.TreeRounding

end


/-! Cross-time occupied-endpoint matching, without any edge hypothesis on
empty words. New endpoint anchor drift is paid only for coincident vertices. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.Rounding
attribute [local instance] Classical.propDecidable Classical.decEq
variable {n:ℕ} [NeZero n]

theorem Tree.exists_cross_matching {X I:Type*} [PseudoMetricSpace X] [Fintype I]
    (T:Tree n) (a b:Fin n→X) (w D:Fin n→ℝ) (hD:∀ v,0≤D v)
    {C:ℝ} (f g:I→Fin n)
    (hneq:∀ i j,f i≠g j→dist (a (f i)) (b (g j))≤C*T.cutDistance w (f i) (g j))
    (heq:∀ i j,f i=g j→dist (a (f i)) (b (g j))≤D (g j)):
    ∃ π:Equiv.Perm I,(∑ i,dist (a (f i)) (b (g (π i))))≤
      C*(∑ v,w v*|(∑ i,T.indicator v (f i))-(∑ i,T.indicator v (g i))|)+∑ i,D (g i):=by
  obtain ⟨π,hπ⟩:=LaminarMatching.exists_simultaneous T.laminar f g
  refine ⟨π,?_⟩
  have hh:∀ i,dist (a (f i)) (b (g (π i)))≤C*T.cutDistance w (f i) (g (π i))+D (g (π i)):=by
    intro i
    by_cases he:f i=g (π i)
    · rw [he,T.cutDistance_self,mul_zero,zero_add]
      simpa only [he] using heq i (π i) he
    · exact (hneq i (π i) he).trans (le_add_of_nonneg_right (hD _))
  calc
    _ ≤∑ i,(C*T.cutDistance w (f i) (g (π i))+D (g (π i))):=sum_le_sum (fun i _=>hh i)
    _ = C*(∑ v,w v*|(∑ i,T.indicator v (f i))-(∑ i,T.indicator v (g i))|)+∑ i,D (g i):=by
      rw [sum_add_distrib,←mul_sum,Equiv.sum_comp π (fun i=>D (g i))]
      congr 1
      congr 1
      unfold Tree.cutDistance
      rw [sum_comm]
      apply sum_congr rfl
      intro v _
      rw [←mul_sum]
      congr 1
      exact hπ v
end KServer.Rounding

end


/-! The fixed finite inventory of integral count states with total mass k.
The encoding is an actual k-slot list, not a bound on future randomness. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TreeRounding
attribute [local instance] Classical.propDecidable Classical.decEq
variable {n k:ℕ} [NeZero n]

lemma pack_val (T:Tree n) (c:Counts n) (hc:Good T k c):(pack T c:Inventory T k).val=c:=by
  simp only [pack,dite_eq_left hc]

lemma good_of_valid (T:Tree n) (a:Fin n→ℝ) (ha0:a 0=(k:ℝ)) (c:Counts n) (hc:T.Valid a c):Good T k c:=by
  refine ⟨hc.2.2,fun v=>(hc.2.1 v).1,?_⟩
  exact balanced_integer (by exact_mod_cast ha0) ((hc.1 0).2)

end KServer.TreeRounding

end


/-! Genuine occupied-slot matching on the complete prefix tree. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable (A:Type) [Fintype A] (L:ℕ)
variable {Y:Type} [MetricSpace Y] {k:ℕ}

lemma count_matching (z:Y) (a b:ℕ→A→Y) (maps next:ℕ→Y→A) (m:ℕ→A→ℝ) {R τ:ℝ}
    (hR:0≤R) (hτ:1≤τ) (hdia:∀ x y:Y,dist x y≤R)
    (ha:∀ d,d<L→∀ y,dist (a d (maps d y)) y≤20*(R/τ^(d+1)))
    (hb:∀ d,d<L→∀ y,dist (b d (next d y)) y≤20*(R/τ^(d+1)))
    (hab:∀ d,d<L→∀ x y key,maps d x=key→next d y=key→dist (a d key) (b d key)≤40*(R/τ^(d+1)))
    (hm:∀ d key,0 ≤ m d key)
    (hmab:∀ d,d<L→∀ x y key,maps d x=key→next d y=key→dist (a d key) (b d key)≤40*m d key)
    (c e:TreeRounding.Inventory (tree A L) k)
    (hc:∀ i,∃ x,HierarchyCounts.hit maps (numbering A L (c.slots (tree A L) i)).2 x)
    (he:∀ i,∃ y,HierarchyCounts.hit next (numbering A L (e.slots (tree A L) i)).2 y):
    matching (countConfig A L z a c) (countConfig A L z b e)≤
      120*(∑ v,weight A L R τ ((tree A L).parent v)*|(c.val.subtree v:ℝ)-(e.val.subtree v:ℝ)|)+
        40*(∑ v,(e.val.park v:ℝ)*nodeMotion A L m v):=by
  let D:=fun v:Node A L=>40*nodeMotion A L m v
  have hD:∀ v,0≤D v:=by
    intro v
    dsimp only [D,nodeMotion]
    cases lastKey A L v with
    | none=>norm_num
    | some key=>exact mul_nonneg (by norm_num) (hm _ _)
  have hneq:∀ i j,c.slots (tree A L) i≠e.slots (tree A L) j→
      dist (nodeAnchor A L z a (c.slots (tree A L) i)) (nodeAnchor A L z b (e.slots (tree A L) j))≤
        120*(travelTree A L).cutDistance (fun v=>weight A L R τ ((tree A L).parent v))
          (c.slots (tree A L) i) (e.slots (tree A L) j):=by
    intro i j hne
    obtain ⟨x,hx⟩:=hc i
    obtain ⟨y,hy⟩:=he j
    exact (travelTree A L).distinct_le_cut (weight A L R τ) (weight_nonneg A L hR (by linarith))
      (by norm_num) _ _ _ _ hne (fun p hu hv=>witnessed_common_bound A L z a b maps next
        hR hτ hdia ha hb hab _ _ p hu hv x y hx hy)
  have heq:∀ i j,c.slots (tree A L) i=e.slots (tree A L) j→
      dist (nodeAnchor A L z a (c.slots (tree A L) i)) (nodeAnchor A L z b (e.slots (tree A L) j))≤D (e.slots (tree A L) j):=by
    intro i j hij
    obtain ⟨x,hx⟩:=hc i
    obtain ⟨y,hy⟩:=he j
    rw [hij] at hx ⊢
    let v:=e.slots (tree A L) j
    change dist (nodeAnchor A L z a v) (nodeAnchor A L z b v)≤D v
    cases hl:lastKey A L v with
    | none=>simp only [D,nodeAnchor,nodeMotion,hl,dist_self,mul_zero,le_refl]
    | some key=>
      obtain ⟨hp,hmem⟩:=last_depth A L hl
      have hL:depth A L v-1<L:=by have hh:=(numbering A L v).1.isLt; change depth A L v<L+1 at hh; omega
      simp only [nodeAnchor,nodeMotion,hl,D]
      exact hmab _ hL x y key (band_key A L maps _ key hmem x hx) (band_key A L next _ key hmem y hy)
  obtain ⟨π,hπ⟩:=(travelTree A L).exists_cross_matching (nodeAnchor A L z a) (nodeAnchor A L z b)
    (fun v=>weight A L R τ ((tree A L).parent v)) D hD (c.slots _) (e.slots _) hneq heq
  apply (matching_le _ _ π).trans
  change (∑ i,dist (nodeAnchor A L z a (c.slots _ i)) (nodeAnchor A L z b (e.slots _ (π i))))≤_
  have hsub (c:TreeRounding.Inventory (tree A L) k) (v:Node A L):
      (∑ i,(travelTree A L).indicator v (c.slots _ i))=(c.val.subtree v:ℝ):=
    TreeRounding.slots_subtree _ c.val c.property.1 c.property.2.1 c.property.2.2 v
  simp only [hsub] at hπ
  have hs:(∑ i,D (e.slots _ i))=40*(∑ v,(e.val.park v:ℝ)*nodeMotion A L m v):=by
    change (∑ i,D (TreeRounding.slots (tree A L) e.val e.property.1 e.property.2.1 e.property.2.2 i))=_
    rw [TreeRounding.slots_sum]
    dsimp only [D]
    rw [mul_sum]
    apply sum_congr rfl
    intro v _
    ring
  rwa [hs] at hπ
end KServer.PrefixTree

end


/-! Rounded occupied vertices have positive fractional park, and all positive
integer parks occur in the actual labeled list. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TreeRounding
attribute [local instance] Classical.propDecidable Classical.decEq
variable {n k:ℕ} [NeZero n]

lemma Inventory.slot_exists (T:Tree n) (c:Inventory T k) (v:Fin n) (hv:0 < c.val.park v):
    ∃ i,c.slots T i=v:=by
  let p:(Σ u:Fin n,Fin (c.val.park u).toNat):=⟨v,⟨0,by omega⟩⟩
  refine ⟨countEquiv T c.val c.property.1 c.property.2.1 c.property.2.2 p,?_⟩
  unfold Inventory.slots TreeRounding.slots
  rw [Equiv.symm_apply_apply]

lemma Inventory.valid_slot_positive (T:Tree n) (c:Inventory T k) (a:Fin n→ℝ)
    (ha:∀ v,0≤T.park a v) (hc:T.Valid a c.val) (i:Fin k):
    0<T.park a (c.slots T i):=by
  have hp:=slots_positive T c.val c.property.1 c.property.2.1 c.property.2.2 i
  change 0 < c.val.park (c.slots T i) at hp
  apply lt_of_le_of_ne (ha _)
  intro he
  have hh:=balanced_integer (k:=0) (by simpa only [Int.cast_zero] using he.symm) ((hc.2.1 (c.slots T i)).2)
  have hh':c.val.park (c.slots T i)=0:=by exact hh
  omega

lemma balanced_one_le {a:ℝ} {j:ℤ} (ha:1≤a) (hj:Rounding.Balanced a j):1≤j:=by
  have hf:1≤Int.floor a:=by exact Int.le_floor.mpr (by simpa only [Int.cast_one] using ha)
  exact hf.trans ((Rounding.balanced_iff_bounds a j).mp hj).1
end KServer.TreeRounding

namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable (A:Type) [Fintype A] (L:ℕ)
variable {Y:Type} {k:ℕ}

lemma count_witness (c:TreeRounding.Inventory (tree A L) k) (q:Node A L→ℝ)
    (hp:∀ v,0≤(travelTree A L).park q v) (hq:∀ v,(travelTree A L).park q v≤q v)
    (hc:(tree A L).Valid q c.val) (maps:ℕ→Y→A)
    (hw:∀ v,0<q v→∃ x,HierarchyCounts.hit maps (numbering A L v).2 x) (i:Fin k):
    ∃ x,HierarchyCounts.hit maps (numbering A L (c.slots (tree A L) i)).2 x:=by
  have hh:=c.valid_slot_positive (tree A L) q hp hc i
  apply hw
  exact hh.trans_le (hq _)
end KServer.PrefixTree

end


/-! Exact fixed-band aggregation of the occupied anchor drift. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable (A:Type) [Fintype A] (L:ℕ)

lemma nodeMotion_sum (p:Node A L→ℝ) (m:ℕ→A→ℝ):
    (∑ v,p v*nodeMotion A L m v)=∑ d:Fin L,∑ a:A,m d.val a*bandMass A L p d.val a:=by
  simp only [bandMass,mul_sum,band,sum_filter]
  rw [sum_comm]
  conv_rhs => arg 2; ext a; rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  cases hv:lastKey A L v with
  | none=>
    simp [nodeMotion,hv]
  | some a=>
    obtain ⟨hp,hb⟩:=last_depth A L hv
    have hd:depth A L v-1<L:=by have hh:=(numbering A L v).1.isLt; change depth A L v<L+1 at hh; omega
    have he:depth A L v=depth A L v-1+1:=by omega
    simp only [nodeMotion,hv,Option.some.injEq]
    rw [sum_eq_single a]
    · rw [sum_eq_single (⟨depth A L v-1,hd⟩:Fin L)]
      · rw [ite_eq_left ⟨he,rfl⟩]
        ring
      · intro d _ hne
        have hn:depth A L v≠d.val+1:=by intro hh; apply hne; apply Fin.ext; change d.val=depth A L v-1; omega
        simp only [hn,false_and,ite_false,mul_zero]
      · simp only [mem_univ,not_true_eq_false,false_implies]
    · intro b _ hne
      have hn:a≠b:=Ne.symm hne
      simp only [hn,and_false,ite_false,mul_zero,sum_const_zero]
    · simp only [mem_univ,not_true_eq_false,false_implies]
end KServer.PrefixTree

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_MetricService
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common complete keys have controlled anchors. Only common moving heavy
labels incur chronological travel; tiers and singleton fallback are fixed. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.LevelKeys
open FiniteExperiment TierProcess HeavyAnchorDynamics
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (tape:Tape Y k H r)

lemma inl_key (t:ℕ) (x:Y) (a:Sigma (Alphabet Y k))
    (ha:map s law hr.le σ tape t x=Sum.inl a):
    keys s law hr.le σ tape t a.1 x=some a.2:=by
  unfold map PriorityKeys.key at ha
  cases hs:PriorityKeys.selected (keys s law hr.le σ tape t) x with
  | none=>rw [hs] at ha; cases ha
  | some z=>
    rw [hs] at ha
    have he:z=a:=Sum.inl.inj ha
    subst z
    exact (PriorityKeys.selected_some _ x hs).1

include hr in
lemma motion_nonneg (t:ℕ) (a:Key Y k):0 ≤ motion s law σ tape t a:=by
  cases a with
  | inr a=>rfl
  | inl z=>
    rcases z with ⟨i,a⟩
    cases i with
    | none=>change 0 ≤ if _ then r else 0; split_ifs <;> positivity
    | some i=>rfl

include hr in
lemma motion_le (t:ℕ) (a:Key Y k):motion s law σ tape t a ≤ r:=by
  cases a with
  | inr a=>exact hr.le
  | inl z=>
    rcases z with ⟨i,a⟩
    cases i with
    | none=>change (if _ then r else 0) ≤ r; split_ifs <;> linarith
    | some i=>exact hr.le

lemma common_anchor_motion (t:Fin H) (x y:Y) (a:Key Y k)
    (hx:map s law hr.le σ tape t.val x=a) (hy:map s law hr.le σ tape (t.val+1) y=a):
    dist (anchor s law hr.le σ tape t.val a) (anchor s law hr.le σ tape (t.val+1) a)≤
      40*motion s law σ tape t.val a:=by
  cases a with
  | inr a=>simp only [anchor,PriorityKeys.anchor,motion,dist_self,mul_zero,le_refl]
  | inl z=>
    rcases z with ⟨i,a⟩
    have hx':=inl_key s law hr σ tape t.val x ⟨i,a⟩ hx
    have hy':=inl_key s law hr σ tape (t.val+1) y ⟨i,a⟩ hy
    cases i with
    | some i=>
      let :Nonempty Y:=⟨s 0⟩
      have he:=TierKeys.anchors_persist (request s σ) hr.le (tierQualifies s law r σ i)
        (tape.2 i).1 (tape.2 i).2 t.val x y hx' hy'
      change dist (TierKeys.anchor _ _ _ _ _ _) (TierKeys.anchor _ _ _ _ _ _)≤40*0
      rw [he,dist_self,mul_zero]
    | none=>
      obtain ⟨c,hc,hlc,hdc⟩:=(HeavyAnchorDynamics.key_iff s law hr σ tape.1 t.val x a).mp hx'
      obtain ⟨d,hd,hld,hdd⟩:=(HeavyAnchorDynamics.key_iff s law hr σ tape.1 (t.val+1) y a).mp hy'
      have hec:=HeavyAnchorDynamics.anchor_eq s law hr σ tape.1 t.val hc hlc
      have hed:=HeavyAnchorDynamics.anchor_eq s law hr σ tape.1 (t.val+1) hd hld
      have hp:HeavyAnchorDynamics.present s law r σ tape.1 t.val a:=⟨c,hc,hlc⟩
      have hp':HeavyAnchorDynamics.present s law r σ tape.1 (t.val+1) a:=⟨d,hd,hld⟩
      have hc':=HeavyAnchorDynamics.common_centers s law hr σ tape.1 t hc hd (hlc.trans hld.symm)
      change dist (heavyAnchor _ _ _ _ _ _ _) (heavyAnchor _ _ _ _ _ _ _)≤40*(if _ then r else 0)
      by_cases he:c=d
      · rw [hec,hed,he,dist_self]
        simp
      · have hn:heavyAnchor s law r σ tape.1 t.val a≠heavyAnchor s law r σ tape.1 (t.val+1) a:=by
          rwa [hec,hed]
        rw [ite_eq_left ⟨hp,hp',hn⟩,hec,hed]
        exact (hc'.resolve_left he).2.2.1

end KServer.LevelKeys

end


/-! Cross-time metric rounding uses witnesses only for occupied vertices.
Its anchor surcharge is exactly the already-paid heavy travel. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointMetric
open JointExperiment JointAllocation JointHistory
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0 < r d) (hk:1≤(k:ℝ))

lemma motion_nonneg (t:ℕ) (ω:Atom (k:=k) law hr) (d:ℕ) (key:LevelKeys.Key Y k):
    0 ≤ motion s law hr t ω d key:=by
  unfold motion
  split_ifs with hd
  · exact LevelKeys.motion_nonneg s law (hr ⟨d,hd⟩) _ _ _ _
  · rfl

lemma anchor_close {R τ:ℝ} (hrad:∀ d,r d=R/τ^(d.val+1)) (t:ℕ) (ω:Atom (k:=k) law hr)
    (d:ℕ) (hd:d<L) (y:Y):
    dist (anchors s law hr t ω d (maps law hr s t ω d y)) y≤20*(R/τ^(d+1)):=by
  simp only [anchors,maps,dite_eq_left hd]
  simpa only [hrad] using LevelKeys.anchor_distance s law (hr ⟨d,hd⟩) ω.val.1 (ω.val.2 ⟨d,hd⟩) t y

lemma anchor_move (t:Fin H) (ω:Atom (k:=k) law hr) (d:ℕ) (hd:d<L) (x y:Y) (key:LevelKeys.Key Y k)
    (hx:maps law hr s t.val ω d x=key) (hy:maps law hr s (t.val+1) ω d y=key):
    dist (anchors s law hr t.val ω d key) (anchors s law hr (t.val+1) ω d key)≤40*motion s law hr t.val ω d key:=by
  simp only [anchors,motion,dite_eq_left hd]
  exact LevelKeys.common_anchor_motion s law (hr ⟨d,hd⟩) ω.val.1 (ω.val.2 ⟨d,hd⟩) t x y key
    (by simpa only [maps,dite_eq_left hd] using hx) (by simpa only [maps,dite_eq_left hd] using hy)

lemma anchor_move_bound {R τ:ℝ} (hrad:∀ d,r d=R/τ^(d.val+1))
    (t:Fin H) (ω:Atom (k:=k) law hr) (d:ℕ) (hd:d<L) (x y:Y) (key:LevelKeys.Key Y k)
    (hx:maps law hr s t.val ω d x=key) (hy:maps law hr s (t.val+1) ω d y=key):
    dist (anchors s law hr t.val ω d key) (anchors s law hr (t.val+1) ω d key)≤40*(R/τ^(d+1)):=by
  refine (anchor_move s law hr t ω d hd x y key hx hy).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  simp only [motion,dite_eq_left hd]
  rw [←hrad ⟨d,hd⟩]
  exact LevelKeys.motion_le s law (hr ⟨d,hd⟩) _ _ _ _

lemma count_witness (t:ℕ) (ω:Atom (k:=k) law hr)
    (c:TreeRounding.Inventory (PrefixTree.tree (LevelKeys.Key Y k) L) k)
    (hc:(PrefixTree.tree (LevelKeys.Key Y k) L).Valid (quota s law hr hk t ω) c.val) (i:Fin k):
    ∃ x,HierarchyCounts.hit (maps law hr s t ω) (PrefixTree.numbering (LevelKeys.Key Y k) L (c.slots _ i)).2 x:=by
  apply PrefixTree.count_witness _ L c (quota s law hr hk t ω) (park_nonneg s law hr hk t ω)
    (PrefixTree.park_le_Q _ L (weight_nonneg law hr) (history law hr) (history_refines law hr)
      (maps law hr s) (hidden law hr s) hk (weight_pos law hr) t ω) hc
  intro v hv
  obtain ⟨x,hx⟩:=PrefixTree.Q_witness _ L (weight_nonneg law hr) (history law hr) (history_refines law hr)
    (maps law hr s) (hidden law hr s) hk (weight_pos law hr) t ω (fun ρ hh=>maps_adapted law hr s t ρ ω hh) v hv
  exact ⟨x,(mem_filter.mp hx).2⟩

lemma motion_sum (t:ℕ) (ω:Atom (k:=k) law hr):
    (∑ v:Node (Y:=Y) (k:=k) (L:=L),park s law hr hk (t+1) ω v*
      PrefixTree.nodeMotion (LevelKeys.Key Y k) L (motion s law hr t ω) v)=JointHeavy.travel s law hr hk t ω:=by
  rw [PrefixTree.nodeMotion_sum]
  unfold JointHeavy.travel
  apply sum_congr rfl
  intro d _
  simp only [motion,dite_eq_left d.isLt,Fintype.sum_sum_type,Fintype.sum_sigma]
  rw [show (∑ i:LevelKeys.Structure k, ∑ a:LevelKeys.Alphabet Y k i,
      LevelKeys.motion s law ω.val.1 (ω.val.2 d) t (Sum.inl ⟨i,a⟩)*
        PrefixTree.bandMass (LevelKeys.Key Y k) L (park s law hr hk (t+1) ω) d.val (Sum.inl ⟨i,a⟩))=
      (∑ a:HeavyLabels.Pool Y, LevelKeys.motion s law ω.val.1 (ω.val.2 d) t (Sum.inl ⟨none,a⟩)*
        PrefixTree.bandMass (LevelKeys.Key Y k) L (park s law hr hk (t+1) ω) d.val (Sum.inl ⟨none,a⟩))+
      ∑ i:LevelKeys.Tier k, ∑ a:LevelKeys.Alphabet Y k (some i),
        LevelKeys.motion s law ω.val.1 (ω.val.2 d) t (Sum.inl ⟨some i,a⟩)*
        PrefixTree.bandMass (LevelKeys.Key Y k) L (park s law hr hk (t+1) ω) d.val (Sum.inl ⟨some i,a⟩) from
    Fintype.sum_option _]
  simp only [LevelKeys.motion,zero_mul,sum_const_zero,add_zero]
  apply sum_congr rfl
  intro a _
  unfold JointHeavy.present JointHeavy.anchor JointHeavy.b JointAllocation.band
  split_ifs
  · rfl
  · exact zero_mul _

lemma count_matching {R τ:ℝ} (hR:0≤R) (hτ:1≤τ) (hdia:∀ x y:Y,dist x y≤R)
    (hrad:∀ d,r d=R/τ^(d.val+1)) (t:Fin H) (ω:Atom (k:=k) law hr)
    (c e:TreeRounding.Inventory (PrefixTree.tree (LevelKeys.Key Y k) L) k)
    (hc:(PrefixTree.tree (LevelKeys.Key Y k) L).Valid (quota s law hr hk t.val ω) c.val)
    (he:(PrefixTree.tree (LevelKeys.Key Y k) L).Valid (quota s law hr hk (t.val+1) ω) e.val):
    matching (PrefixTree.countConfig _ L (s 0) (anchors s law hr t.val ω) c)
      (PrefixTree.countConfig _ L (s 0) (anchors s law hr (t.val+1) ω) e)≤
      120*(∑ v,PrefixTree.weight (LevelKeys.Key Y k) L R τ ((PrefixTree.tree _ L).parent v)*
        |(c.val.subtree v:ℝ)-(e.val.subtree v:ℝ)|)+
      40*(∑ v,(e.val.park v:ℝ)*PrefixTree.nodeMotion _ L (motion s law hr t.val ω) v):=
  PrefixTree.count_matching _ L (s 0) _ _ _ _ _ hR hτ hdia
    (anchor_close s law hr hrad _ ω) (anchor_close s law hr hrad _ ω)
    (anchor_move_bound s law hr hrad t ω) (motion_nonneg s law hr _ ω)
    (anchor_move s law hr t ω) c e (count_witness s law hr hk _ ω c hc) (count_witness s law hr hk _ ω e he)
end KServer.JointMetric

end


/-! A finest-scale singleton region contains the request with quota at least
one. Balanced parks therefore give actual labeled service, not just a marginal
hitting probability. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointService
open JointExperiment JointAllocation JointHistory
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0 < r d) (hk:1≤(k:ℝ))

lemma leaf_number (t:ℕ) (ω:Atom (k:=k) law hr) (y:Y):
    PrefixTree.numbering (LevelKeys.Key Y k) L (leaf s law hr t ω y)=
      ⟨⟨L,Nat.lt_succ_self L⟩,fun i=>maps law hr s t ω i.val y⟩:=
  (PrefixTree.numbering (LevelKeys.Key Y k) L).apply_symm_apply _

lemma leaf_quota (t:Fin H) (ω:Atom (k:=k) law hr):
    1≤quota s law hr hk (t.val+1) ω (leaf s law hr (t.val+1) ω (ω.val.1 t)):=by
  unfold quota PrefixTree.Q
  rw [leaf_number]
  apply HierarchicalQuota.served _ _ _ _ _ hk (weight_pos law hr)
  intro ρ hh
  obtain ⟨i,hi⟩:=hidden_covers law hr s t ρ
  refine ⟨i,?_⟩
  intro d
  rw [hi,request_history law hr t ρ ω hh]
  exact congrFun (congrFun (maps_adapted law hr s _ ρ ω hh) d.val) _

lemma leaf_park (t:ℕ) (ω:Atom (k:=k) law hr) (y:Y):
    park s law hr hk t ω (leaf s law hr t ω y)=quota s law hr hk t ω (leaf s law hr t ω y):=by
  unfold park Rounding.Tree.park
  have he:(PrefixTree.numbering (LevelKeys.Key Y k) L (leaf s law hr t ω y)).1.val=L:=by rw [leaf_number]
  have hs:=PrefixTree.children_sum_leaf (LevelKeys.Key Y k) L (leaf s law hr t ω y)
    (fun v:PrefixTree.Vertex (LevelKeys.Key Y k) L=>quota s law hr hk t ω ((PrefixTree.numbering _ L).symm v)) he
  simp only [OrderIso.symm_apply_apply] at hs
  change quota s law hr hk t ω (leaf s law hr t ω y)-_=quota s law hr hk t ω (leaf s law hr t ω y)
  have hs' : (∑ u:(PrefixTree.travelTree (LevelKeys.Key Y k) L).Child (leaf s law hr t ω y),
      quota s law hr hk t ω u.val)=0:=by exact hs
  rw [hs',sub_zero]

lemma leaf_anchor (hL:0<L) (hf:∀ x y:Y,dist x y≤20*r ⟨L-1,by omega⟩→x=y)
    (t:ℕ) (ω:Atom (k:=k) law hr) (y:Y):
    PrefixTree.nodeAnchor (LevelKeys.Key Y k) L (s 0) (anchors s law hr t ω) (leaf s law hr t ω y)=y:=by
  have hd:PrefixTree.depth (LevelKeys.Key Y k) L (leaf s law hr t ω y)=L:=by
    unfold PrefixTree.depth; rw [leaf_number]
  have hl:PrefixTree.lastKey (LevelKeys.Key Y k) L (leaf s law hr t ω y)=
      some (maps law hr s t ω (L-1) y):=by
    have hh:=congrArg (fun v:PrefixTree.Vertex (LevelKeys.Key Y k) L=>
      if hp:0<v.1.val then some (v.2 ⟨v.1.val-1,by omega⟩) else none)
      (leaf_number s law hr t ω y)
    change PrefixTree.lastKey (LevelKeys.Key Y k) L (leaf s law hr t ω y)=
      (if hp:0<L then some (maps law hr s t ω (L-1) y) else none) at hh
    simpa only [dite_eq_left hL] using hh
  simp only [PrefixTree.nodeAnchor,hl,hd]
  apply hf
  simp only [anchors,maps,dite_eq_left (show L-1<L by omega)]
  exact LevelKeys.anchor_distance s law (hr ⟨L-1,by omega⟩) _ _ _ _

lemma count_serves (hL:0<L) (hf:∀ x y:Y,dist x y≤20*r ⟨L-1,by omega⟩→x=y)
    (t:Fin H) (ω:Atom (k:=k) law hr)
    (c:TreeRounding.Inventory (PrefixTree.tree (LevelKeys.Key Y k) L) k)
    (hc:(PrefixTree.tree (LevelKeys.Key Y k) L).Valid (quota s law hr hk (t.val+1) ω) c.val):
    ∃ i,PrefixTree.countConfig (LevelKeys.Key Y k) L (s 0) (anchors s law hr (t.val+1) ω) c i=ω.val.1 t:=by
  have hp:1≤park s law hr hk (t.val+1) ω (leaf s law hr (t.val+1) ω (ω.val.1 t)):=by
    rw [leaf_park]; exact leaf_quota s law hr hk t ω
  have hi:=TreeRounding.balanced_one_le hp (hc.2.1 (leaf s law hr (t.val+1) ω (ω.val.1 t))).2
  obtain ⟨i,he⟩:=c.slot_exists _ _ (by omega : 0 < c.val.park (leaf s law hr (t.val+1) ω (ω.val.1 t)))
  refine ⟨i,?_⟩
  unfold PrefixTree.countConfig
  rw [he]
  exact leaf_anchor s law hr hL hf _ ω _
end KServer.JointService

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_CausalRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pushing the actual finite rounded law onto one fixed finite state space. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TreeRounding
attribute [local instance] Classical.propDecidable Classical.decEq
variable {α S:Type} [Fintype S]

lemma Law.mass_average (L:Law α) (f:α→S) (g:S→ℝ):
    (∑ s,L.mass f s*g s)=L.avg (fun a=>g (f a)):=by
  unfold Law.mass Law.avg
  simp only [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro ω _
  simp only [mul_assoc,mul_ite,one_mul,zero_mul,ite_mul,mul_zero,sum_ite_eq,mem_univ,ite_true]
end KServer.TreeRounding

end


/-! Explicit causal finite-state implementation of a family of consecutive
couplings. Only the two prescribed marginals are supplied, not a cost conclusion. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.CausalCouplings
attribute [local instance] Classical.propDecidable Classical.decEq
variable {X S:Type} [Fintype S] [Nonempty S]

variable (F:Family X S)

lemma disintegration (h:List X) (r:X) (s z:S):F.marginal h s*kernel F h r s z=F.joint h r s z:=by
  by_cases hs:0<F.marginal h s
  · simp only [kernel,ite_eq_left hs]
    field_simp
  · have hz:F.marginal h s=0:=le_antisymm (le_of_not_gt hs) (F.nonneg h s)
    have hj:F.joint h r s z=0:=by
      apply le_antisymm _ (F.joint_nonneg h r s z)
      calc _≤ ∑ z,F.joint h r s z:=single_le_sum (fun z _=>F.joint_nonneg h r s z) (mem_univ z)
           _ = 0:=by rw [F.left,hz]
    rw [hz,hj,zero_mul]

variable {k:ℕ} [NeZero k]

lemma machine_transition (h:List (X×Fin k)) (r:X):
    (machine (k:=k) F).transition h r=kernel F (h.map Prod.fst) r:=rfl

variable [MetricSpace X] (start:Configuration k X) (V:List X→ S→ Configuration k X)
variable (hc:∀ h r s,∃ i,V (h++[r]) s i=r)

lemma virtual_eq (h:List (X×Fin k)) (s:S) (σ:List X):
    HiddenMachine.virtualCost (machine F) start V hc h s σ=cost F V (h.map Prod.fst) s σ:=by
  induction σ generalizing h s with
  | nil=>rfl
  | cons r σ ih=>
    simp only [HiddenMachine.virtualCost,cost,machine_transition]
    apply sum_congr rfl
    intro z _
    rw [ih]
    simp only [List.map_append,List.map_cons,List.map_nil]

omit [NeZero k] in
lemma mean_path (h:List X) (σ:List X):
    (∑ s,F.marginal h s*cost F V h s σ)=pathCost F V h σ:=by
  induction σ generalizing h with
  | nil=>simp [cost,pathCost]
  | cons r σ ih=>
    simp only [cost,pathCost,mul_sum,mul_add,←mul_assoc,disintegration,sum_add_distrib]
    congr 1
    rw [sum_comm]
    simp only [←sum_mul,F.right]
    exact ih (h++[r])

include hc in
lemma exists_policy:
    ∃ A:Policy k X,StronglyLazy start A ∧ ∀ σ:List X,
      expectedCost A start σ≤ (∑ s,F.marginal [] s*matching start (V [] s))+pathCost F V [] σ:=by
  obtain ⟨A,hA,hB⟩:=HiddenMachine.causal_random_lazy_simulation (machine F) start V hc
  refine ⟨A,hA,fun σ=>?_⟩
  have hh:=hB σ
  change expectedCost A start σ ≤ (∑ s,F.marginal [] s*matching start (V [] s))+
    ∑ s,F.marginal [] s*HiddenMachine.virtualCost (machine F) start V hc [] s σ at hh
  simpa only [virtual_eq,List.map_nil,mean_path] using hh
end KServer.CausalCouplings

end


/-! Sequential balanced count sampling on one fixed finite tree. The full
old marginal is retained at every request, so one causal machine works at all
horizons. -/


/-! The sequential family keeps exact new park means and the factor-132
weighted subtree transport estimate. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TreeRounding
attribute [local instance] Classical.propDecidable Classical.decEq
variable {X:Type} {n k:ℕ} [NeZero n]
variable (T:Tree n) {τ:ℝ} (hτ:22≤τ) (w:Fin n→ℝ) (hw:∀ u,0≤w u)
  (hscale:∀ u,u≠0→w (T.parent u)=τ*w u)
  (q:List X→Fin n→ℝ) (hq:∀ h v,0≤q h v) (hp:∀ h v,0≤T.park (q h) v)
  (hr:∀ h,q h 0=(k:ℝ))

lemma pair_old_valid (h:List X) (x:X) (ω:(pairLaw T hτ w hw hscale q hq hp hr h x).Ω):
    T.Valid (q h) ((pairLaw T hτ w hw hscale q hq hp hr h x).point ω).old:=
  (countStep_spec T hτ w hw hscale q hq hp hr h x (countState T hτ w hw hscale q hq hp hr h)).2.1 ω |>.1
lemma pair_new_valid (h:List X) (x:X) (ω:(pairLaw T hτ w hw hscale q hq hp hr h x).Ω):
    T.Valid (q (h++[x])) ((pairLaw T hτ w hw hscale q hq hp hr h x).point ω).new:=
  (countStep_spec T hτ w hw hscale q hq hp hr h x (countState T hτ w hw hscale q hq hp hr h)).2.1 ω |>.2.1

lemma joint_average (h:List X) (x:X) (g:Inventory T k→Inventory T k→ℝ):
    (∑ c,∑ e,(countFamily T hτ w hw hscale q hq hp hr).joint h x c e*g c e)=
      (pairLaw T hτ w hw hscale q hq hp hr h x).avg (fun p=>g (pack T p.old) (pack T p.new)):=by
  exact (Fintype.sum_prod_type _).symm.trans
    ((pairLaw T hτ w hw hscale q hq hp hr h x).mass_average (fun p=>(pack T p.old,pack T p.new)) (fun p=>g p.1 p.2))

lemma expected_bound (h:List X) (x:X) (g:Inventory T k→Inventory T k→ℝ) (m:Fin n→ℝ)
    {a b:ℝ} (ha:0≤a)
    (hg:∀ c e:Inventory T k,T.Valid (q h) c.val→T.Valid (q (h++[x])) e.val→
      g c e≤a*(∑ u,w (T.parent u)*|(c.val.subtree u:ℝ)-(e.val.subtree u:ℝ)|)+
        b*(∑ u,(e.val.park u:ℝ)*m u)):
    (∑ c,∑ e,(countFamily T hτ w hw hscale q hq hp hr).joint h x c e*g c e)≤
      a*132*(∑ u,w (T.parent u)*|q h u-q (h++[x]) u|)+b*(∑ u,T.park (q (h++[x])) u*m u):=by
  rw [joint_average]
  let P:=pairLaw T hτ w hw hscale q hq hp hr h x
  have hbound:P.avg (fun p=>g (pack T p.old) (pack T p.new))≤
      P.avg (fun p=>a*(∑ u,w (T.parent u)*|(p.new.subtree u:ℝ)-(p.old.subtree u:ℝ)|)+
        b*(∑ u,(p.new.park u:ℝ)*m u)):=by
    apply Law.avg_le_of_support
    intro ω
    have ho:=pair_old_valid T hτ w hw hscale q hq hp hr h x ω
    have hn:=pair_new_valid T hτ w hw hscale q hq hp hr h x ω
    have hgo:=good_of_valid T _ (hr h) _ ho
    have hgn:=good_of_valid T _ (hr (h++[x])) _ hn
    have hh:=hg (pack T (P.point ω).old) (pack T (P.point ω).new)
      (by rwa [pack_val T _ hgo]) (by rwa [pack_val T _ hgn])
    have heo:(pack T (P.point ω).old:Inventory T k).val=(P.point ω).old:=pack_val T _ hgo
    have hen:(pack T (P.point ω).new:Inventory T k).val=(P.point ω).new:=pack_val T _ hgn
    rw [heo,hen] at hh
    simpa only [abs_sub_comm] using hh
  have hmean:(P.map PairState.new).avg (fun c=>∑ u,(c.park u:ℝ)*m u)=
      ∑ u,T.park (q (h++[x])) u*m u:=by
    rw [Law.avg_sum]
    apply sum_congr rfl
    intro u _
    have hh:=(countStep_spec T hτ w hw hscale q hq hp hr h x
      (countState T hτ w hw hscale q hq hp hr h)).2.2.1.2 u
    change (P.map PairState.new).avg (fun c=>(c.park u:ℝ))=T.park (q (h++[x])) u at hh
    calc
      _=m u*(P.map PairState.new).avg (fun c=>(c.park u:ℝ)):=by
        simpa only [mul_comm] using (P.map PairState.new).avg_mul (m u) (fun c=>(c.park u:ℝ))
      _=T.park (q (h++[x])) u*m u:=by rw [hh,mul_comm]
  have hm:= (countStep_spec T hτ w hw hscale q hq hp hr h x
      (countState T hτ w hw hscale q hq hp hr h)).2.2.2
  rw [Law.avg_add,Law.avg_mul,Law.avg_mul] at hbound
  rw [Law.map_avg] at hmean
  change P.avg (fun p=>∑ u,(p.new.park u:ℝ)*m u)=_ at hmean
  rw [hmean] at hbound
  exact hbound.trans (by simpa only [P,pairLaw,mul_assoc,add_comm] using add_le_add_right (mul_le_mul_of_nonneg_left hm ha) (b*∑ u,T.park (q (h++[x])) u*m u))
end KServer.TreeRounding

end


/-! An independent permanent finite tape, sampled once before the requests. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.CausalCouplings
attribute [local instance] Classical.propDecidable Classical.decEq
variable {X I S:Type} [Fintype I] [Fintype S]
variable (w:I→ℝ) (hw:∀ i,0≤w i) (h1:∑ i,w i=1) (F:I→Family X S)

lemma mixture_transport [MetricSpace X] {k:ℕ} (V:I→List X→S→ Configuration k X) (h:List X) (r:X):
    transport (mixture w hw h1 F) (fun h s=>V s.1 h s.2) h r=
      ∑ i,w i*transport (F i) (V i) h r:=by
  unfold transport mixture
  simp only [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro i _
  rw [mul_sum]
  apply sum_congr rfl
  intro s _
  rw [sum_eq_single i]
  · simp only [ite_true,mul_assoc,mul_sum]
  · intro j _ hj
    simp only [Ne.symm hj,ite_false,zero_mul,sum_const_zero]
  · simp only [mem_univ,not_true_eq_false,false_implies]

variable [Nonempty S] [MetricSpace X] {k:ℕ} [NeZero k]

omit [Fintype S] [Nonempty S] [MetricSpace X] in
lemma safeConfig_serves (z:X) (V:List X→S→ Configuration k X) (h:List X) (r:X) (s:S):
    ∃ i,safeConfig z V (h++[r]) s i=r:=by
  have hn:h++[r]≠[]:=by simp
  have he:(h++[r]).getLastD z=r:=by simp
  unfold safeConfig
  rw [ite_eq_right hn,he]
  split_ifs with hs
  · exact hs
  · exact ⟨0,rfl⟩

omit [Fintype S] [Nonempty S] [MetricSpace X] [NeZero k] in
lemma safeConfig_eq_nil (z:X) (V:List X→S→ Configuration k X) (s:S):
    safeConfig z V [] s=V [] s:=by simp only [safeConfig,ite_true]

omit [Fintype S] [Nonempty S] [MetricSpace X] [NeZero k] in
lemma safeConfig_eq (z:X) (V:List X→S→ Configuration k X) (h:List X) (s:S)
    (hc:∃ i,V h s i=h.getLastD z):safeConfig z V h s=V h s:=by
  unfold safeConfig
  split_ifs <;> rfl
end KServer.CausalCouplings

end


/-! Explicit finite-horizon cost of the same causal machine. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.CausalCouplings
variable {X S:Type} [Fintype S] [Nonempty S] [MetricSpace X] {k:ℕ}

omit [Nonempty S] in
lemma path_ofFn (F:Family X S) (V:List X→ S→ Configuration k X) (h:List X)
    {H:ℕ} (σ:Fin H→X):
    pathCost F V h (List.ofFn σ)=∑ t:Fin H,transport F V (h++(List.ofFn σ).take t.val) (σ t):=by
  induction H generalizing h with
  | zero=>simp only [List.ofFn_zero,pathCost,Fin.sum_univ_zero]
  | succ H ih=>
    rw [List.ofFn_succ,pathCost,ih,Fin.sum_univ_succ]
    simp only [Fin.val_zero,List.take_zero,List.append_nil,Fin.val_succ,List.take_succ_cons]
    congr 1
    apply sum_congr rfl
    intro t _
    congr 1
    simp only [List.append_assoc,List.singleton_append]
end KServer.CausalCouplings

end


/-! Actual history-indexed count laws and their rendered labeled configurations.
Impossible histories are completed by a service-safe output, whereas every
positive experimental prefix uses the genuine allocated occupied anchors. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointRounded
open JointExperiment JointAllocation JointHistory CausalCouplings
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0 < r d) (hk:1≤(k:ℝ))

lemma q_take (t:ℕ) (ht:t≤H) (ω:Atom (k:=k) law hr):
    q s law hr hk ω.val.2 ((List.ofFn ω.val.1).take t)=quota s law hr hk t ω:=by
  rw [q_eq s law hr hk _ _ ω (observed_true law hr ω t ht)]
  simp only [List.length_take,List.length_ofFn,Nat.min_eq_left ht]
lemma a_take (t:ℕ) (ht:t≤H) (ω:Atom (k:=k) law hr):
    a s law hr ω.val.2 ((List.ofFn ω.val.1).take t)=anchors s law hr t ω:=by
  rw [a_eq s law hr _ _ ω (observed_true law hr ω t ht)]
  simp only [List.length_take,List.length_ofFn,Nat.min_eq_left ht]

omit [MetricSpace Y] [Fintype Y] in
lemma take_succ (t:Fin H) (σ:Fin H→Y):
    (List.ofFn σ).take (t.val+1)=(List.ofFn σ).take t.val++[σ t]:=by
  rw [List.take_succ_eq_append_getElem (by simpa only [List.length_ofFn] using t.isLt)]
  rw [List.getElem_ofFn]


lemma raw_take (t:ℕ) (ht:t≤H) (ω:Atom (k:=k) law hr) (c:State (Y:=Y) (k:=k) (L:=L)):
    rawConfig s law hr ω.val.2 ((List.ofFn ω.val.1).take t) c=
      PrefixTree.countConfig _ L (s 0) (anchors s law hr t ω) c:=by
  unfold rawConfig
  rw [a_take s law hr t ht ω]

lemma config_take (hL:0<L) (hf:∀ x y:Y,dist x y≤20*r ⟨L-1,by omega⟩→x=y)
    (t:ℕ) (ht:t≤H) (ω:Atom (k:=k) law hr) (c:State (Y:=Y) (k:=k) (L:=L))
    (hc:T.Valid (quota s law hr hk t ω) c.val):
    config s law hr ω.val.2 ((List.ofFn ω.val.1).take t) c=
      PrefixTree.countConfig _ L (s 0) (anchors s law hr t ω) c:=by
  unfold config
  have he:safeConfig (s 0) (rawConfig s law hr ω.val.2) ((List.ofFn ω.val.1).take t) c=
      rawConfig s law hr ω.val.2 ((List.ofFn ω.val.1).take t) c:=by
    cases t with
    | zero=>simp only [List.take_zero,safeConfig_eq_nil]
    | succ t=>
      apply safeConfig_eq
      obtain ⟨i,hi⟩:=JointService.count_serves s law hr hk hL hf ⟨t,by omega⟩ ω c hc
      refine ⟨i,?_⟩
      rw [raw_take s law hr (t+1) ht ω c,hi,take_succ ⟨t,by omega⟩]
      simp only [List.getLastD_concat]
  rw [he]
  exact raw_take s law hr t ht ω c

lemma step_bound {R τ:ℝ} (hR:0≤R) (hτ:22≤τ) (hdia:∀ x y:Y,dist x y≤R)
    (hrad:∀ d,r d=R/τ^(d.val+1)) (hL:0<L)
    (hf:∀ x y:Y,dist x y≤20*r ⟨L-1,by omega⟩→x=y)
    (t:Fin H) (ω:Atom (k:=k) law hr):
    transport (family s law hr hk hR hτ ω.val.2) (config s law hr ω.val.2)
      ((List.ofFn ω.val.1).take t.val) (ω.val.1 t)≤
      15840*JointBudget.stepQuota s law hr hk R τ t.val ω+40*JointHeavy.travel s law hr hk t.val ω:=by
  have hold:=q_take s law hr hk t.val (Nat.le_of_lt t.isLt) ω
  have hnew:q s law hr hk ω.val.2 ((List.ofFn ω.val.1).take t.val++[ω.val.1 t])=
      quota s law hr hk (t.val+1) ω:=by
    rw [←take_succ t ω.val.1]
    exact q_take s law hr hk _ (by omega) ω
  have hh:=TreeRounding.expected_bound T hτ (PrefixTree.weight (LevelKeys.Key Y k) L R τ)
    (PrefixTree.weight_nonneg _ L hR (by linarith)) (PrefixTree.parent_weight _ L (by linarith))
    (q s law hr hk ω.val.2) (q_nonneg s law hr hk ω.val.2) (q_park_nonneg s law hr hk ω.val.2)
    (q_root s law hr hk ω.val.2) ((List.ofFn ω.val.1).take t.val) (ω.val.1 t)
    (fun c e=>matching (config s law hr ω.val.2 ((List.ofFn ω.val.1).take t.val) c)
      (config s law hr ω.val.2 ((List.ofFn ω.val.1).take t.val++[ω.val.1 t]) e))
    (PrefixTree.nodeMotion _ L (JointMetric.motion s law hr t.val ω)) (a:=120) (b:=40) (by norm_num)
    (fun c e hc he=>by
      rw [hold] at hc
      rw [hnew] at he
      rw [←take_succ t ω.val.1,config_take s law hr hk hL hf _ (by omega) ω c hc,
        config_take s law hr hk hL hf _ (by omega) ω e he]
      exact JointMetric.count_matching s law hr hk hR (by linarith) hdia hrad t ω c e hc he)
  change transport (family s law hr hk hR hτ ω.val.2) (config s law hr ω.val.2) _ _≤_ at hh
  rw [hold,hnew] at hh
  have hm:(∑ v,T.park (quota s law hr hk (t.val+1) ω) v*
      PrefixTree.nodeMotion _ L (JointMetric.motion s law hr t.val ω) v)=JointHeavy.travel s law hr hk t.val ω:=
    JointMetric.motion_sum s law hr hk t.val ω
  rw [hm] at hh
  simpa only [JointBudget.stepQuota,abs_sub_comm,show (120:ℝ)*132=15840 by norm_num] using hh
end KServer.JointRounded

end


/-! The actual permanent-tape sequentially rounded experiment returns a causal
strongly lazy policy. All impossible histories were already service-completed. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointPolicy
open JointExperiment JointRounded CausalCouplings RankTracking ActualCharges
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0 < r d) (hk:1≤(k:ℝ))

omit [NeZero k] in
include hr in
lemma tape_nonempty : Nonempty (Tape Y k H L r):=by
  by_contra h
  have : IsEmpty (Tape Y k H L r):=not_nonempty_iff.mp h
  have hh:=tapeWeight_sum (Y:=Y) (k:=k) (H:=H) hr
  simp only [sum_of_isEmpty,zero_ne_one] at hh

lemma rendered_serves (h:List Y) (x:Y) (z:MixState (Y:=Y) (k:=k) (H:=H) (r:=r)):
    ∃ i,rendered s law hr (h++[x]) z i=x:=
  safeConfig_serves (s 0) (rawConfig s law hr z.1) h x z.2

lemma mean_path {R τ:ℝ} (hR:0≤R) (hτ:22≤τ):
    (∑ σ,law.val σ*pathCost (mixed s law hr hk hR hτ) (rendered s law hr) [] (List.ofFn σ))=
      ∑ t:Fin H,avg (weight law hr) (fun ω=>
        transport (family s law hr hk hR hτ ω.val.2) (config s law hr ω.val.2)
          ((List.ofFn ω.val.1).take t.val) (ω.val.1 t)):=by
  have := tape_nonempty (Y:=Y) (k:=k) (H:=H) hr
  simp_rw [path_ofFn,List.nil_append]
  unfold mixed rendered
  simp_rw [mixture_transport]
  have hav (t:Fin H):avg (weight law hr) (fun ω=>
        transport (family s law hr hk hR hτ ω.val.2) (config s law hr ω.val.2)
          ((List.ofFn ω.val.1).take t.val) (ω.val.1 t))=
      ∑ σ,law.val σ*(∑ a:Tape Y k H L r,tapeWeight r a*
        transport (family s law hr hk hR hτ a) (config s law hr a)
          ((List.ofFn σ).take t.val) (σ t)):=by
    rw [avg_raw law hr (fun z:Raw Y k H L r =>
      transport (family s law hr hk hR hτ z.2) (config s law hr z.2)
        ((List.ofFn z.1).take t.val) (z.1 t))]
    simp only [avg,rawWeight,FiniteExperiment.weight,tapeLaw,Fintype.sum_prod_type,mul_sum,mul_assoc]
  simp_rw [hav,mul_sum]
  rw [sum_comm]

lemma path_bound {R τ:ℝ} (hR:0≤R) (hτ:22≤τ) (hdia:∀ x y:Y,dist x y≤R)
    (hrad:∀ d,r d=R/τ^(d.val+1)) (hL:0<L)
    (hf:∀ x y:Y,dist x y≤20*r ⟨L-1,by omega⟩→x=y):
    (∑ σ,law.val σ*pathCost (mixed s law hr hk hR hτ) (rendered s law hr) [] (List.ofFn σ))≤
      15840*total (weight law hr) H (JointBudget.stepQuota s law hr hk R τ)+
        40*total (weight law hr) H (JointHeavy.travel s law hr hk):=by
  rw [mean_path]
  have hb:=sum_le_sum (s:=univ) (fun t (_:t∈univ)=>
    avg_mono (weight_nonneg law hr) (fun ω=>step_bound s law hr hk hR hτ hdia hrad hL hf t ω))
  simp only [avg_add,avg_mul,sum_add_distrib,←mul_sum] at hb
  unfold total
  rw [←Fin.sum_univ_eq_sum_range (fun t=>avg (weight law hr) (JointBudget.stepQuota s law hr hk R τ t)) H,
    ←Fin.sum_univ_eq_sum_range (fun t=>avg (weight law hr) (JointHeavy.travel s law hr hk t)) H]
  exact hb

lemma exists_policy {R τ:ℝ} (hR:0≤R) (hτ:22≤τ) (hdia:∀ x y:Y,dist x y≤R)
    (hrad:∀ d,r d=R/τ^(d.val+1)) (hL:0<L)
    (hf:∀ x y:Y,dist x y≤20*r ⟨L-1,by omega⟩→x=y):
    ∃ A:Policy k Y,StronglyLazy s A ∧
      (∑ σ,law.val σ*expectedCost A s (List.ofFn σ))≤
        15840*total (weight law hr) H (JointBudget.stepQuota s law hr hk R τ)+
        40*total (weight law hr) H (JointHeavy.travel s law hr hk)+(k:ℝ)*R:=by
  have := tape_nonempty (Y:=Y) (k:=k) (H:=H) hr
  obtain ⟨A,hA,hcost⟩:=CausalCouplings.exists_policy (mixed s law hr hk hR hτ) s
    (rendered s law hr) (rendered_serves s law hr)
  refine ⟨A,hA,?_⟩
  have hi:(∑ z,(mixed s law hr hk hR hτ).marginal [] z*matching s (rendered s law hr [] z))≤(k:ℝ)*R:=by
    have hh:=sum_le_sum (s:=univ) (fun z (_:z∈univ)=>mul_le_mul_of_nonneg_left
      (Episode.matching_le_diameter s (rendered s law hr [] z) R hdia)
      ((mixed s law hr hk hR hτ).nonneg [] z))
    simpa only [←sum_mul,Family.normalized,one_mul] using hh
  have he:=sum_le_sum (s:=univ) (fun σ (_:σ∈univ)=>mul_le_mul_of_nonneg_left (hcost (List.ofFn σ)) (law.property.1 σ))
  simp only [mul_add,sum_add_distrib,←sum_mul,law.property.2,one_mul] at he
  have hp:=path_bound s law hr hk hR hτ hdia hrad hL hf
  linarith
end KServer.JointPolicy

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_FiniteLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute constants for the unconditional finite-law endpoint. No metric,
finite-tree depth, horizon, law or initial tuple enters these coefficients. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.GlobalEndpoint
open ActualCharges RankTracking JointExperiment JointAllocation
attribute [local instance] Classical.propDecidable Classical.decEq

lemma constants_pos : 0 < core ∧ 0 < cutoff ∧ 0<quotaMultiplier ∧ 0<keyMultiplier ∧
    0<optMultiplier ∧ 0<embeddingMultiplier ∧ 0 < competitiveMultiplier:=by
  have hc:0 < core:=by norm_num [core]
  have hl:0<Real.log 2:=Real.log_pos (by norm_num)
  have hcut:0 < cutoff:=by unfold cutoff; positivity
  have hq:0<quotaMultiplier:=by norm_num [quotaMultiplier]
  have hlocal:=output_constants_nonneg.2.2.2
  have hkey:0<keyMultiplier:=by unfold keyMultiplier; positivity
  have ho:0<optMultiplier:=by unfold optMultiplier; positivity
  have he:0<embeddingMultiplier:=by unfold embeddingMultiplier; positivity
  refine ⟨hc,hcut,hq,hkey,ho,he,?_⟩
  unfold competitiveMultiplier
  positivity

lemma embedding_coefficient {k:ℕ} (hk:1≤(k:ℝ)):
    EmbeddedCost.tierCoefficient k+EmbeddedCost.heavyCoefficient k+EmbeddedCost.spatialCoefficient k≤
      embeddingMultiplier*ActualCaps.ell k:=by
  have he:1≤ActualCaps.ell k:=ActualCaps.ell_ge_one hk
  have hkpos:0<(k:ℝ):=by linarith
  have hlog:0≤Real.log (k:ℝ):=Real.log_nonneg hk
  have hle:Real.log (k:ℝ)≤ActualCaps.ell k:=by
    have hh:=Real.log_le_log hkpos (show (k:ℝ)≤(k:ℝ)+1 by linarith)
    unfold ActualCaps.ell
    linarith
  have hA:embA*ActualCaps.ell k≤|embA| *ActualCaps.ell k:=
    mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
  have hB:embB≤|embB| *ActualCaps.ell k:=by
    calc
      embB≤|embB|:=le_abs_self _
      _≤|embB| *ActualCaps.ell k:=by nlinarith [abs_nonneg embB]
  have hC:embC*Real.log (k:ℝ)≤|embC| *ActualCaps.ell k:=
    (mul_le_mul_of_nonneg_right (le_abs_self _) hlog).trans
      (mul_le_mul_of_nonneg_left hle (abs_nonneg _))
  have identity:EmbeddedCost.tierCoefficient k+EmbeddedCost.heavyCoefficient k+EmbeddedCost.spatialCoefficient k=
      embA*ActualCaps.ell k+embB+embC*Real.log (k:ℝ):=by
    unfold EmbeddedCost.tierCoefficient EmbeddedCost.heavyCoefficient EmbeddedCost.spatialCoefficient
      embA embB embC ActualCaps.ell
    ring
  rw [identity]
  unfold embeddingMultiplier
  nlinarith
end KServer.GlobalEndpoint

end


/-! Main finite construction at separation ratio 32. Initial inventories are
explicitly independent of both the request law and its horizon. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.GlobalEndpoint
open ActualCharges RankTracking JointExperiment JointAllocation
attribute [local instance] Classical.propDecidable Classical.decEq

variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y)) (hk:1≤(k:ℝ))

lemma opt_nonneg : 0≤EmbeddedCost.opt s law:=
  sum_nonneg (fun σ _=>mul_nonneg (law.property.1 σ) (optimalCost_nonneg s (List.ofFn σ)))

include hk in
lemma cost_by_keys {R:ℝ} (hR:0<R) (hL:0<L) (hdia:∀ x y:Y,dist x y≤R)
    (hf:∀ x y:Y,dist x y≤20*(R/(32:ℝ)^L)→x=y):
    ∃ A:Policy k Y,StronglyLazy s A ∧
      (∑ σ,law.val σ*expectedCost A s (List.ofFn σ))≤
        keyMultiplier*ActualCaps.ell k*
          total (weight law (radii_pos (L:=L) hR)) H
            (JointBudget.stepKey s law (radii_pos (L:=L) hR))+
        optMultiplier*ActualCaps.ell k*EmbeddedCost.opt s law+baseInventory Y k R L:=by
  let r:=radii R L
  have hr:∀ d:Fin L,0 < r d:=fun d=>div_pos hR (by positivity)
  let Q:=total (weight law hr) H (JointBudget.stepQuota s law hr hk R 32)
  let K:=total (weight law hr) H (JointBudget.stepKey s law hr)
  let P:=total (weight law hr) H (fun t ω=>∑ v:JointBudget.Node (Y:=Y) (k:=k) (L:=L),
    PrefixTree.weight (LevelKeys.Key Y k) L R 32 v*
      |park s law hr hk (t+1) ω v-park s law hr hk t ω v|)
  let T:=total (weight law hr) H (JointHeavy.travel s law hr hk)
  let Ch:=total (weight law hr) H (JointHeavy.charge s law hr hk)
  have hQ0:0≤Q:=total_nonneg (weight_nonneg law hr)
    (JointBudget.stepQuota_nonneg s law hr hk hR.le (by norm_num))
  have hK0:0≤K:=total_nonneg (weight_nonneg law hr) (JointBudget.stepKey_nonneg s law hr)
  have hell:=ActualCaps.ell_ge_one hk
  have hQ:Q≤384*localConstant*ActualCaps.ell k*K+quotaInventory Y k R L:=by
    have hh:=JointBudget.quota_bound s law hr hk hR.le (by norm_num : (2:ℝ)≤32)
      (fun d=>rfl) H
    norm_num only [mul_one,show (12:ℝ)*32=384 by norm_num] at hh
    exact hh
  have hP:P≤2*Q:=by
    have hh:=total_mono (weight_nonneg law hr) (N:=H) (fun t ω=>
      JointBudget.park_bound s law hr hk hR.le (by norm_num : (0:ℝ)<32) t ω)
    rw [total_mul] at hh
    change P≤(1+1/32:ℝ)*Q at hh
    linarith
  have hc:Ch ≤ core*288*ActualCaps.ell k*K+2*(6/5:ℝ)*P+chargeInventory Y k R L:=by
    have hh:=JointHeavy.charge_bound s law hr hk H (PrefixTree.weight (LevelKeys.Key Y k) L R 32)
      (PrefixTree.weight_nonneg _ L hR.le (by norm_num)) (by
        intro d a v hv
        dsimp only [r,radii,PrefixTree.weight]
        rw [PrefixTree.band_depth _ L d.val (HeavyAnchorDynamics.slot (k:=k) a) hv])
    exact hh
  have hrad:∀ d:Fin L,r d=ParkedCoefficients.radius (R/32) 32 d.val:=by
    intro d
    dsimp only [r,radii,ParkedCoefficients.radius]
    rw [pow_succ]
    field_simp
  have hT:T≤4*core*K+(4*cutoff/3)*ActualCaps.ell k*EmbeddedCost.opt s law+
      4*Ch+4*potentialInventory k R L:=by
    have hh:=JointHeavy.travel_raw s law hr hk (div_nonneg hR.le (by norm_num))
      (by norm_num : (2:ℝ)≤32) hrad (C:=cutoff*ActualCaps.ell k) (by
        dsimp only [cutoff,core,ActualCaps.ell]
        ring_nf
        exact le_rfl)
    rw [JointEmbedding.hidden_cost s law hr] at hh
    change T≤4*core*K+4*(cutoff*ActualCaps.ell k)/3*EmbeddedCost.opt s law+
      4*Ch+4*potentialInventory k R L at hh
    nlinarith only [hh]
  obtain ⟨A,hA,hcost⟩:=JointPolicy.exists_policy s law hr hk hR.le (by norm_num : (22:ℝ)≤32)
    hdia (fun d=>rfl) hL (by
      intro x y hxy
      apply hf x y
      have hlast:(⟨L-1,by omega⟩:Fin L).val+1=L:=by simp only; omega
      simpa only [r,radii,hlast] using hxy)
  refine ⟨A,hA,?_⟩
  change (∑ σ,law.val σ*expectedCost A s (List.ofFn σ))≤
    keyMultiplier*ActualCaps.ell k*K+optMultiplier*ActualCaps.ell k*EmbeddedCost.opt s law+
      baseInventory Y k R L
  change _≤15840*Q+40*T+(k:ℝ)*R at hcost
  have hcoreK:core*K ≤ core*ActualCaps.ell k*K:=by
    have hp:=mul_nonneg constants_pos.1.le hK0
    nlinarith
  have hq:=mul_le_mul_of_nonneg_left hQ constants_pos.2.2.1.le
  dsimp only [keyMultiplier,optMultiplier,baseInventory,quotaMultiplier] at hq ⊢
  norm_num only [core] at hcoreK hc hT ⊢
  nlinarith [hc,hP,hT,hcost,hcoreK,hq]

include hk in
lemma finite_geometric {R:ℝ} (hR:0<R) (hL:0<L) (hdia:∀ x y:Y,dist x y≤R)
    (hf:∀ x y:Y,dist x y≤20*(R/(32:ℝ)^L)→x=y):
    ∃ D:ℝ,0≤D ∧ ∀ H:ℕ,∀ law:FiniteDistribution (Fin H→Y),
      ∃ A:Policy k Y,StronglyLazy s A ∧
        (∑ σ,law.val σ*expectedCost A s (List.ofFn σ))≤
          competitiveMultiplier*(1+Real.log ((k:ℝ)+1))^2*
            (∑ σ,law.val σ*optimalCost s (List.ofFn σ))+D:=by
  refine ⟨max (inventory Y k R L) 0,le_max_right _ _,?_⟩
  intro H law
  have hr:∀ d:Fin L,0 < radii R L d:=fun d=>div_pos hR (by positivity)
  obtain ⟨A,hA,hcost⟩:=cost_by_keys s law hk hR hL hdia hf
  refine ⟨A,hA,?_⟩
  have hK:=JointEmbedding.key_bound s law hr hR (by norm_num : (2:ℝ)≤32) (fun d=>rfl)
  have he:=embedding_coefficient hk
  have ho:=opt_nonneg s law
  have hell:=ActualCaps.ell_ge_one hk
  have hm:=constants_pos.2.2.2.1
  have hn:=constants_pos.2.2.2.2.1
  have hc:=mul_le_mul_of_nonneg_right he ho
  have hfinal:=mul_le_mul_of_nonneg_left (hK.trans (add_le_add hc (le_refl _)))
    (mul_nonneg hm.le (by linarith : 0≤ActualCaps.ell k))
  have hpow:optMultiplier*ActualCaps.ell k*EmbeddedCost.opt s law≤
      optMultiplier*(ActualCaps.ell k)^2*EmbeddedCost.opt s law:=by
    have hsq:ActualCaps.ell k≤(ActualCaps.ell k)^2:=by nlinarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hn.le) ho
  have hi:=le_max_left (inventory Y k R L) 0
  change _ ≤ competitiveMultiplier*(ActualCaps.ell k)^2*EmbeddedCost.opt s law+max (inventory Y k R L) 0
  dsimp only [inventory,competitiveMultiplier,embeddingInventory] at hi ⊢
  nlinarith [hcost,hfinal,hpow,hi]
end KServer.GlobalEndpoint

end


/-! Every finite metric admits a finite geometric prefix depth; no discreteness
assumption is introduced at the arbitrary-metric endpoint. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.GlobalEndpoint
attribute [local instance] Classical.propDecidable Classical.decEq

lemma finite_scales (Y:Type*) [MetricSpace Y] [Fintype Y]:
    ∃ R:ℝ,0<R ∧ ∃ L:ℕ,0<L ∧ (∀ x y:Y,dist x y≤R) ∧
      (∀ x y:Y,dist x y≤20*(R/(32:ℝ)^L)→x=y):=by
  let S:ℝ:=∑ x:Y,∑ y:Y,dist x y
  let I:ℝ:=∑ x:Y,∑ y:Y,(dist x y)⁻¹
  have hS:0≤S:=sum_nonneg (fun _ _=>sum_nonneg (fun _ _=>dist_nonneg))
  have hI:0≤I:=sum_nonneg (fun _ _=>sum_nonneg (fun _ _=>inv_nonneg.mpr dist_nonneg))
  let R:=S+1
  have hR:0<R:=by dsimp [R]; linarith
  have hdia:∀ x y:Y,dist x y≤R:=by
    intro x y
    have h1:dist x y≤∑ z:Y,dist x z:=single_le_sum (f:=fun z:Y=>dist x z) (fun _ _=>dist_nonneg) (mem_univ y)
    have h2:(∑ z:Y,dist x z)≤S:=single_le_sum (f:=fun a:Y=>∑ z:Y,dist a z)
      (fun _ _=>sum_nonneg (fun _ _=>dist_nonneg)) (mem_univ x)
    dsimp only [R]
    linarith
  let ε:=1/(I+1)
  have hε:0<ε:=one_div_pos.mpr (by linarith)
  have hsep:∀ x y:Y,x≠y→ε<dist x y:=by
    intro x y hne
    have hp:0<dist x y:=dist_pos.mpr hne
    have h1:(dist x y)⁻¹≤∑ z:Y,(dist x z)⁻¹:=single_le_sum (f:=fun z:Y=>(dist x z)⁻¹)
      (fun _ _=>inv_nonneg.mpr dist_nonneg) (mem_univ y)
    have h2:(∑ z:Y,(dist x z)⁻¹)≤I:=single_le_sum (f:=fun a:Y=>∑ z:Y,(dist a z)⁻¹)
      (fun _ _=>sum_nonneg (fun _ _=>inv_nonneg.mpr dist_nonneg)) (mem_univ x)
    apply (one_div_lt (by linarith : 0<I+1) hp).mpr
    rw [one_div]
    linarith
  obtain ⟨n,hn⟩:=exists_pow_lt_of_lt_one (div_pos hε (by positivity : 0<20*R))
    (show (1/32:ℝ)<1 by norm_num)
  have hl:20*(R/(32:ℝ)^(n+1))<ε:=by
    have hp:(1/32:ℝ)^(n+1)≤(1/32:ℝ)^n:=by
      rw [pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg (by norm_num) _) (by norm_num)
    have hh:=hp.trans_lt hn
    rw [one_div_pow] at hh
    have hh':=(lt_div_iff₀ (show 0<20*R by positivity)).mp hh
    calc
      20*(R/(32:ℝ)^(n+1))=(1/(32:ℝ)^(n+1))*(20*R):=by ring
      _<ε:=hh'
  refine ⟨R,hR,n+1,by omega,hdia,?_⟩
  intro x y hxy
  by_contra hne
  exact (not_lt_of_ge hxy) (hl.trans (hsep x y hne))
end KServer.GlobalEndpoint

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relabel a finite metric across universes without changing the experiment,
initial labels, service constraints, optimal cost or behavior-policy horizon. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.FiniteMetricTransport
attribute [local instance] Classical.propDecidable Classical.decEq
universe u v
variable {Y:Type u} {Z:Type v}

lemma configuration_map {k:ℕ} (f:Y→Z) (s:Configuration k Y) (h:List (Y×Fin k)):
    configurationAfter (f∘s) (mapHistory f h)=f∘configurationAfter s h:=by
  induction h generalizing s with
  | nil=>rfl
  | cons a h ih=>
    simp only [mapHistory,List.map_cons,configurationAfter,List.foldl_cons]
    change configurationAfter (serve (f∘s) a.2 (f a.1)) (mapHistory f h)=
      f∘configurationAfter (serve s a.2 a.1) h
    rw [←map_serve f]
    exact ih _

lemma stronglyLazy {k:ℕ} (e:Y≃Z) (s:Configuration k Y) (A:Policy k Z)
    (hA:StronglyLazy (e∘s) A):StronglyLazy s (retractPolicy e A):=by
  intro h r hi j hj
  apply hA (mapHistory e h) (e r)
  · obtain ⟨i,hi⟩:=hi
    refine ⟨i,?_⟩
    rw [configuration_map]
    exact congrArg e hi
  · rw [configuration_map]
    exact fun he=>hj (e.injective he)

variable [MetricSpace Y] [MetricSpace Z]
lemma cost {k:ℕ} (e:Y≃Z) (he:Isometry e.symm) (s:Configuration k Y) (A:Policy k Z) (σ:List Y):
    expectedCost (retractPolicy e A) s σ=expectedCost A (e∘s) (σ.map e):=by
  have hh:=expectedCost_retract e e.symm e.apply_symm_apply he A (e∘s) (σ.map e)
  simpa [Function.comp_def] using hh

variable [Fintype Y] [Fintype Z]

omit [MetricSpace Y] [MetricSpace Z] in
lemma sum_lawOn {H:ℕ} (e:Y≃Z) (law:FiniteDistribution (Fin H→Y)) (f:(Fin H→Z)→ℝ):
    (∑ σ:Fin H→Z,(lawOn e law).val σ*f σ)=∑ σ:Fin H→Y,law.val σ*f (e∘σ):=by
  apply Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl (Fin H)) e.symm)
  intro σ
  dsimp only [lawOn,Equiv.arrowCongr,Equiv.refl,Equiv.coe_fn_mk,Function.comp_def]
  congr 2
  funext i
  exact (e.apply_symm_apply (σ i)).symm

lemma mean_cost {k H:ℕ} (e:Y≃Z) (he:Isometry e.symm) (s:Configuration k Y)
    (A:Policy k Z) (law:FiniteDistribution (Fin H→Y)):
    (∑ σ:Fin H→Y,law.val σ*expectedCost (retractPolicy e A) s (List.ofFn σ))=
      ∑ σ:Fin H→Z,(lawOn e law).val σ*expectedCost A (e∘s) (List.ofFn σ):=by
  rw [sum_lawOn]
  apply sum_congr rfl
  intro σ _
  rw [cost e he,List.map_ofFn]

lemma mean_opt {k H:ℕ} [NeZero k] (e:Y≃Z) (he:Isometry e) (s:Configuration k Y)
    (law:FiniteDistribution (Fin H→Y)):
    (∑ σ:Fin H→Z,(lawOn e law).val σ*optimalCost (e∘s) (List.ofFn σ))=
      ∑ σ:Fin H→Y,law.val σ*optimalCost s (List.ofFn σ):=by
  rw [sum_lawOn]
  apply sum_congr rfl
  intro σ _
  simpa only [List.map_ofFn] using congrArg (fun c:ℝ=>law.val σ*c)
    (optimalCost_map e he s (List.ofFn σ))
end KServer.FiniteMetricTransport

end


/-! Unconditional finite-law theorem, with one absolute coefficient and a
law/horizon-independent inventory. Finite relabeling removes the construction's
universe-zero implementation restriction. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer
open GlobalEndpoint FiniteMetricTransport
attribute [local instance] Classical.propDecidable Classical.decEq
universe u

theorem finite_law : FiniteLawStatement.{u}:=by
  refine ⟨competitiveMultiplier,?_⟩
  intro Y mY fY _ k hk s
  have : NeZero k:=⟨by omega⟩
  let Z:=Fin (Fintype.card Y)
  let e:Y≃Z:=Fintype.equivFin Y
  let : MetricSpace Z:=e.symm.metricSpace
  have hes:Isometry e.symm:=isometry_iff_dist_eq.mpr (fun _ _=>rfl)
  have he:Isometry e:=isometry_iff_dist_eq.mpr (fun x y=>by
    change dist (e.symm (e x)) (e.symm (e y))=dist x y
    rw [e.symm_apply_apply,e.symm_apply_apply])
  have hkr:1≤(k:ℝ):=by exact_mod_cast (show 1≤k by omega)
  obtain ⟨R,hR,L,hL,hdia,hf⟩:=finite_scales Z
  obtain ⟨D,hD,hall⟩:=finite_geometric (e∘s) hkr hR hL hdia hf
  refine ⟨D,hD,?_⟩
  intro H law
  obtain ⟨A,hA,hcost⟩:=hall H (lawOn e law)
  refine ⟨retractPolicy e A,stronglyLazy e s A hA,?_⟩
  rw [mean_cost e hes s A law]
  rw [mean_opt e he s law] at hcost
  exact hcost

theorem fully_quantified_main : MainStatement.{u}:=by
  obtain ⟨C,hC⟩:=finite_law_suffices_for_main finite_law.{u}
  refine ⟨max C 1,lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right C 1),?_⟩
  intro k hk X mX hX s
  have : NeZero k:=⟨by omega⟩
  obtain ⟨A,B,hB,hzero,hcost⟩:=hC k hk X mX hX s
  refine ⟨A,B,hB,hzero,?_⟩
  intro σ
  have hnp:0≤(Real.log ((k:ℝ)+1))^2*optimalCost s σ:=
    mul_nonneg (sq_nonneg _) (optimalCost_nonneg s σ)
  have hm:=mul_le_mul_of_nonneg_right (le_max_left C 1) hnp
  have hh:=hcost σ
  nlinarith only [hh,hm]
end KServer

end


namespace KServer
universe u
/-- A positive absolute squared-logarithmic competitive bound on arbitrary metrics,
with one causal policy for all horizons and every labeled starting configuration. -/
theorem main_theorem_oai : MainStatement.{u} := fully_quantified_main
end KServer

end OAI
end

theorem solution.{u} : type_of% @OAI.KServer.main_theorem_oai.{u} := @OAI.KServer.main_theorem_oai.{u}
