-- Prove2me | solution 1 for InertialAVD.Algo.theorem_5_3
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-23T03:54:24.332912+00:00
-- url     : https://prove2.me/submissions/15dab978-1d97-45e1-9b17-b0a06006718f

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_NesterovFB_Rates_Algorithm
import Definitions.Def_InertialAVD_Algo_PerturbedRun
import Definitions.Def_InertialFB_IFB_ConvexAnalysis

open Filter Topology NesterovFB.Rates

open Filter Topology NesterovFB.Rates

noncomputable section
namespace PerturbedIFBProof
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def objectiveReal (Φ : H → EReal) (Ψ : H → ℝ) (u : H) : ℝ :=
  (NesterovFB.Rates.theta Φ Ψ u).toReal
def gap (Φ : H → EReal) (Ψ : H → ℝ) (xstar u : H) : ℝ :=
  objectiveReal Φ Ψ u - objectiveReal Φ Ψ xstar
def velocity (x : ℕ → H) (k : ℕ) : H := x (k+1) - x k
def energy (Φ : H → EReal) (Ψ : H → ℝ) (α s : ℝ)
    (x y : ℕ → H) (xstar : H) (k : ℕ) : ℝ :=
  (((k : ℝ) + α - 2) / (α - 1))^2 * gap Φ Ψ xstar (x k) +
    ‖InertialAVD.Algo.zSeq α x y k - xstar‖^2 / (2*s)
end PerturbedIFBProof

noncomputable section
open Filter Topology Set InnerProductSpace
namespace PerturbedIFBProof
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem theta_ne_bot (Φ : H → EReal) (Ψ : H → ℝ)
    (hΦ : ThreeOpSplitting.ConvexRates.IsProperClosedConvex Φ) (u : H) :
    NesterovFB.Rates.theta Φ Ψ u ≠ ⊥ :=
  EReal.add_ne_bot_iff.mpr ⟨hΦ.1 u, by simp⟩

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
theorem theta_finite_iff (Φ : H → EReal) (Ψ : H → ℝ) (u : H) :
    NesterovFB.Rates.theta Φ Ψ u ≠ ⊤ ↔ Φ u ≠ ⊤ := by
  exact EReal.add_ne_top_iff_ne_top_left (by simp) (by simp)

theorem objectiveReal_eq (Φ : H → EReal) (Ψ : H → ℝ)
    (hΦ : ThreeOpSplitting.ConvexRates.IsProperClosedConvex Φ)
    (u : H) (hu : Φ u ≠ ⊤) :
    objectiveReal Φ Ψ u = (Φ u).toReal + Ψ u := by
  exact EReal.toReal_add hu (hΦ.1 u) (by simp) (by simp)

theorem prox_finite (Φ : H → EReal) (s : ℝ) (P : H → H)
    (hΦ : ThreeOpSplitting.ConvexRates.IsProperClosedConvex Φ)
    (hP : ThreeOpSplitting.ConvexRates.IsProx s Φ P) (z : H) : Φ (P z) ≠ ⊤ := by
  obtain ⟨w, hw⟩ := hΦ.2.1
  have h := hP z w
  have hr : Φ w + ((‖w-z‖^2/(2*s) : ℝ) : EReal) ≠ ⊤ :=
    EReal.add_ne_top hw (by simp)
  have hl := ne_top_of_le_ne_top hr h
  exact (EReal.add_ne_top_iff_ne_top_left (by simp) (by simp)).mp hl

theorem phi_segment (Φ : H → EReal)
    (hΦ : ThreeOpSplitting.ConvexRates.IsProperClosedConvex Φ)
    (p u : H) (hp : Φ p ≠ ⊤) (hu : Φ u ≠ ⊤)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Φ ((1-t) • p + t • u) ≠ ⊤ ∧
    (Φ ((1-t) • p + t • u)).toReal ≤ (1-t)*(Φ p).toReal+t*(Φ u).toReal := by
  have h := hΦ.2.2.2
    (show (p, (Φ p).toReal) ∈ {q : H × ℝ | Φ q.1 ≤ (q.2 : EReal)} by
      simpa only [mem_ofPred_eq, EReal.coe_toReal hp (hΦ.1 p)] using (le_refl (Φ p)))
    (show (u, (Φ u).toReal) ∈ {q : H × ℝ | Φ q.1 ≤ (q.2 : EReal)} by
      simpa only [mem_ofPred_eq, EReal.coe_toReal hu (hΦ.1 u)] using (le_refl (Φ u)))
    (sub_nonneg.mpr ht1) ht (by ring : (1-t)+t=1)
  change Φ ((1-t) • p+t • u) ≤ (((1-t)*(Φ p).toReal+t*(Φ u).toReal : ℝ) : EReal) at h
  exact ⟨ne_top_of_le_ne_top (EReal.coe_ne_top _) h,
    by simpa only [EReal.toReal_coe] using EReal.toReal_le_toReal h (hΦ.1 _) (EReal.coe_ne_top _)⟩

theorem prox_subgradient_real (Φ : H → EReal) (s : ℝ) (P : H → H)
    (hΦ : ThreeOpSplitting.ConvexRates.IsProperClosedConvex Φ)
    (hs : 0 < s) (hP : ThreeOpSplitting.ConvexRates.IsProx s Φ P)
    (z u : H) (hu : Φ u ≠ ⊤) :
    (Φ (P z)).toReal + inner ℝ (z-P z) (u-P z)/s ≤ (Φ u).toReal := by
  let p := P z
  have hp : Φ p ≠ ⊤ := prox_finite Φ s P hΦ hP z
  have hs2 : 0 < 2*s := by positivity
  have hsmall (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
      (Φ p).toReal + inner ℝ (z-p) (u-p)/s ≤
        (Φ u).toReal+t*‖u-p‖^2/(2*s) := by
    obtain ⟨hfinite, hconv⟩ := phi_segment Φ hΦ p u hp hu t ht.le ht1.le
    have hprox := hP z ((1-t) • p+t • u)
    change Φ p + ((‖p-z‖^2/(2*s) : ℝ) : EReal) ≤ _ at hprox
    rw [← EReal.coe_toReal hp (hΦ.1 p),
      ← EReal.coe_toReal hfinite (hΦ.1 _), ← EReal.coe_add,
      ← EReal.coe_add, EReal.coe_le_coe_iff] at hprox
    have hvec : (1-t) • p+t • u-z = (p-z)+t • (u-p) := by module
    have hnorm : ‖(1-t) • p+t • u-z‖^2 =
        ‖p-z‖^2-2*t*inner ℝ (z-p) (u-p)+t^2*‖u-p‖^2 := by
      rw [hvec, norm_add_sq_real]
      simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      have hi : inner ℝ (p-z) (u-p) = -inner ℝ (z-p) (u-p) := by
        rw [show p-z = -(z-p) by abel, inner_neg_left]
      rw [hi]
      ring
    rw [hnorm] at hprox
    have hh := (mul_le_mul_iff_right₀ hs2).mpr hprox
    have hc := mul_le_mul_of_nonneg_right hconv hs2.le
    have heq : ((Φ p).toReal + inner ℝ (z-p) (u-p)/s -
        ((Φ u).toReal+t*‖u-p‖^2/(2*s)))*(2*s*t) ≤ 0 := by
      field_simp at hh ⊢
      nlinarith only [hh, hc]
    have hpos : 0 < 2*s*t := mul_pos hs2 ht
    nlinarith only [heq, hpos]
  have hlim : Tendsto (fun t : ℝ => (Φ u).toReal+t*‖u-p‖^2/(2*s))
      (𝓝[>] (0 : ℝ)) (𝓝 ((Φ u).toReal)) := by
    have hc : Continuous (fun t : ℝ => (Φ u).toReal+t*‖u-p‖^2/(2*s)) := by fun_prop
    simpa using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds] with t ht ht1
  exact hsmall t ht ht1

end PerturbedIFBProof

noncomputable section
open Filter Topology Set InnerProductSpace
namespace PerturbedIFBProof
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem gradient_line_derivative (Ψ : H → ℝ) (hΨ : ContDiff ℝ 1 Ψ)
    (x d : H) (t : ℝ) :
    HasDerivAt (fun r : ℝ => Ψ (x+r • d)) (inner ℝ (gradient Ψ (x+t • d)) d) t := by
  have hline : HasDerivAt (fun r : ℝ => x+r • d) d t := by
    convert! (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const d) using 1
    simp
  simpa only [Function.comp_def, toDual_apply_apply] using
    ((hΨ.differentiable (by norm_num)).differentiableAt.hasGradientAt.hasFDerivAt.comp_hasDerivAt t hline)

theorem gradient_support (Ψ : H → ℝ) (hΨc : ConvexOn ℝ Set.univ Ψ)
    (hΨd : ContDiff ℝ 1 Ψ) (x u : H) :
    Ψ x + inner ℝ (gradient Ψ x) (u-x) ≤ Ψ u := by
  have hc : ConvexOn ℝ Set.univ (fun t : ℝ => Ψ (x+t • (u-x))) := by
    refine ⟨convex_univ, ?_⟩
    intro v _ w _ a b ha hb hab
    have he : x+(a*v+b*w) • (u-x) = a • (x+v • (u-x))+b • (x+w • (u-x)) := by
      have hb' : b=1-a := by linarith
      subst b
      module
    simpa only [smul_eq_mul, he] using hΨc.2 (mem_univ _) (mem_univ _) ha hb hab
  have hd := gradient_line_derivative Ψ hΨd x (u-x) 0
  have h := hc.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1) (by norm_num : (0:ℝ)<1) hd
  simp only [zero_smul, add_zero, slope_def_field, one_smul, add_sub_cancel,
    sub_zero, div_one] at h
  linarith

theorem smooth_upper_model (Ψ : H → ℝ) (L : NNReal)
    (hΨ : ContDiff ℝ 1 Ψ) (hL : LipschitzWith L (gradient Ψ)) (x u : H) :
    Ψ u ≤ Ψ x+inner ℝ (gradient Ψ x) (u-x)+(L:ℝ)/2*‖u-x‖^2 := by
  let d := u-x
  let F : ℝ → ℝ := fun t => Ψ (x+t • d)-Ψ x-t*inner ℝ (gradient Ψ x) d-(L:ℝ)/2*t^2*‖d‖^2
  let F' : ℝ → ℝ := fun t => inner ℝ (gradient Ψ (x+t • d)) d-inner ℝ (gradient Ψ x) d-(L:ℝ)*t*‖d‖^2
  have hder (t : ℝ) : HasDerivAt F (F' t) t := by
    dsimp only [F, F']
    convert! (((gradient_line_derivative Ψ hΨ x d t).sub_const (Ψ x)).sub
      ((hasDerivAt_id t).mul_const (inner ℝ (gradient Ψ x) d))).sub
      ((((hasDerivAt_id t).pow 2).const_mul ((L:ℝ)/2)).mul_const (‖d‖^2)) using 1
    dsimp only [id_eq]
    ring
  have hneg (t : ℝ) (ht : t ∈ interior (Icc (0:ℝ) 1)) : F' t ≤ 0 := by
    rw [interior_Icc] at ht
    have hn := hL.norm_sub_le (x+t • d) x
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1] at hn
    have hi := real_inner_le_norm (gradient Ψ (x+t • d)-gradient Ψ x) d
    rw [inner_sub_left] at hi
    have hm := mul_le_mul_of_nonneg_right hn (norm_nonneg d)
    dsimp [F']
    nlinarith only [hi, hm]
  have hcont : ContinuousOn F (Icc (0:ℝ) 1) := by
    exact (continuous_iff_continuousAt.mpr (fun t => (hder t).continuousAt)).continuousOn
  have hanti := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0:ℝ) 1)
    hcont (fun t _ => (hder t).hasDerivWithinAt) hneg
  have h := hanti (show (0:ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    (show (1:ℝ) ∈ Icc 0 1 by constructor <;> norm_num) (by norm_num : (0:ℝ)≤1)
  dsimp [F, d] at h
  simp only [zero_smul, add_zero, zero_mul, sub_zero, one_smul, add_sub_cancel,
    one_mul, one_pow, mul_one, zero_pow (by norm_num : 2≠0)] at h
  linarith


end PerturbedIFBProof

open Filter Topology Finset

namespace PerturbedIFBProof

lemma sqrt_step {A B e : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (he : 0 ≤ e)
    (h : B ≤ A + e * Real.sqrt B) :
    Real.sqrt B ≤ Real.sqrt A + e := by
  have ha := Real.sqrt_nonneg A
  have hb := Real.sqrt_nonneg B
  have hsa := Real.sq_sqrt hA
  have hsb := Real.sq_sqrt hB
  by_contra hn
  have ht : Real.sqrt A + e < Real.sqrt B := lt_of_not_ge hn
  nlinarith [mul_nonneg ha he]

theorem square_root_energy_bound (E e : ℕ → ℝ)
    (hE : ∀ k, 0 ≤ E (k+1)) (he : ∀ k, 0 ≤ e k)
    (hsum : Summable e)
    (hstep : ∀ k, E (k+2) ≤ E (k+1) + e (k+1) * Real.sqrt (E (k+2))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k, E (k+1) ≤ B := by
  have hs : Summable (fun k => e (k+1)) := (summable_nat_add_iff 1).2 hsum
  have hi : ∀ k, Real.sqrt (E (k+1)) ≤
      Real.sqrt (E 1) + ∑ j ∈ range k, e (j+1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have ht := sqrt_step (hE k) (hE (k+1)) (he (k+1)) (hstep k)
      rw [sum_range_succ]
      simp only [Nat.add_assoc]
      linarith
  let C := Real.sqrt (E 1) + ∑' j, e (j+1)
  have hC : 0 ≤ C := add_nonneg (Real.sqrt_nonneg _) (tsum_nonneg fun j => he (j+1))
  refine ⟨C^2, sq_nonneg _, fun k => ?_⟩
  have hsk : Real.sqrt (E (k+1)) ≤ C := by
    have hp := hs.sum_le_tsum (range k) (fun j _ => he (j+1))
    dsimp [C]
    linarith [hi k]
  have hh := Real.sq_sqrt (hE k)
  nlinarith [Real.sqrt_nonneg (E (k+1))]

/-- A genuine finite telescope gives summability; no limit of D is assumed. -/
theorem dissipation_summable (D h r : ℕ → ℝ)
    (hD : ∀ k, 0 ≤ D k) (hh : ∀ k, 0 ≤ h k) (hr : ∀ k, 0 ≤ r k)
    (hs : Summable r) (hstep : ∀ k, D (k+1) + h k ≤ D k + r k) :
    Summable h := by
  have hi : ∀ n, D n + ∑ k ∈ range n, h k ≤ D 0 + ∑ k ∈ range n, r k := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [sum_range_succ]
      have ht := hstep n
      linarith
  apply summable_of_sum_range_le (c := D 0 + ∑' k, r k) hh
  intro n
  have hp := hs.sum_le_tsum (range n) (fun k _ => hr k)
  have ht := hi n
  have hn := hD n
  linarith

theorem inertial_increment_summable (a : ℝ) (ha : 2 < a)
    (d u : ℕ → ℝ) (hd : ∀ k, 0 ≤ d k) (hu : ∀ k, 0 ≤ u k)
    (hsum : Summable (fun k : ℕ => (k:ℝ) * u k))
    (hstep : ∀ k : ℕ, 1 ≤ k →
      d (k+1) ≤ (((k:ℝ)-1)/((k:ℝ)+a)) * d k + u k) :
    Summable d := by
  have ha0 : 0 < a := by linarith
  have hs : Summable (fun j : ℕ => ((j+1:ℕ):ℝ) * u (j+1)) :=
    (summable_nat_add_iff 1).2 hsum
  have hi : ∀ N : ℕ,
      (N:ℝ) * d (N+1) + a * ∑ j ∈ range N, d (j+2) ≤
        ∑ j ∈ range N, ((j:ℝ)+a+1) * u (j+1) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      have hp : 0 < ((N+1:ℕ):ℝ)+a := by positivity
      have ht := (hstep (N+1) (by omega))
      have hm := mul_le_mul_of_nonneg_left ht (le_of_lt hp)
      have heq : (((N+1:ℕ):ℝ)+a) *
          (((((N+1:ℕ):ℝ)-1)/(((N+1:ℕ):ℝ)+a)) * d (N+1)) =
          (N:ℝ)*d (N+1) := by
        push_cast
        field_simp
        ring
      rw [mul_add, heq] at hm
      simp only [sum_range_succ, Nat.cast_add, Nat.cast_one] at hm ⊢
      linarith
  have hb : ∀ N, ∑ j ∈ range N, ((j:ℝ)+a+1)*u (j+1) ≤
      (a+1) * ∑' j : ℕ, ((j+1:ℕ):ℝ)*u (j+1) := by
    intro N
    calc
      _ ≤ ∑ j ∈ range N, (a+1)*(((j+1:ℕ):ℝ)*u (j+1)) := by
        apply sum_le_sum
        intro j _
        have hj : 0 ≤ (j:ℝ) := Nat.cast_nonneg j
        have huj := hu (j+1)
        push_cast
        nlinarith [mul_nonneg (mul_nonneg ha0.le hj) huj]
      _ = (a+1) * ∑ j ∈ range N, (((j+1:ℕ):ℝ)*u (j+1)) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (hs.sum_le_tsum (range N) (fun j _ => mul_nonneg (Nat.cast_nonneg _) (hu _)))
        (by linarith)
  have htail : Summable (fun j => d (j+2)) := by
    apply summable_of_sum_range_le
      (c := ((a+1) * ∑' j : ℕ, ((j+1:ℕ):ℝ)*u (j+1)) / a) (fun j => hd (j+2))
    intro N
    have ht := (hi N).trans (hb N)
    have hn := mul_nonneg (Nat.cast_nonneg N) (hd (N+1))
    apply (le_div_iff₀ ha0).2
    nlinarith
  exact (summable_nat_add_iff 2).1 htail

theorem nonneg_limit_of_pos_increment (h : ℕ → ℝ)
    (hn : ∀ k, 0 ≤ h k)
    (hsum : Summable (fun k => max (h (k+1)-h k) 0)) :
    ∃ l : ℝ, Tendsto h atTop (𝓝 l) := by
  let p : ℕ → ℝ := fun k => max (h (k+1)-h k) 0
  let D : ℕ → ℝ := fun k => h k - ∑ j ∈ range k, p j
  have hp : ∀ k, 0 ≤ p k := fun k => le_max_right _ _
  have hs : Summable p := hsum
  have hanti : Antitone D := by
    apply antitone_nat_of_succ_le
    intro k
    dsimp [D]
    rw [sum_range_succ]
    have ht : h (k+1)-h k ≤ p k := le_max_left _ _
    linarith
  have hb : BddBelow (Set.range D) := by
    refine ⟨-(∑' k, p k), ?_⟩
    rintro _ ⟨k, rfl⟩
    have ht := hs.sum_le_tsum (range k) (fun j _ => hp j)
    dsimp [D]
    linarith [hn k]
  have hlim := (tendsto_atTop_ciInf hanti hb).add hs.hasSum.tendsto_sum_nat
  refine ⟨(⨅ k, D k) + ∑' k, p k, ?_⟩
  convert hlim using 1
  ext k
  dsimp [D]
  ring

end PerturbedIFBProof

noncomputable section
open Filter Topology Set InnerProductSpace
namespace PerturbedIFBProof
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem objective_finite (Φ : H → EReal) (Ψ : H → ℝ) (L : NNReal) (s α : ℝ)
    (P : H → H) (g x y : ℕ → H)
    (hΦ : ThreeOpSplitting.ConvexRates.IsProperClosedConvex Φ)
    (hΨc : ConvexOn ℝ Set.univ Ψ) (hΨd : ContDiff ℝ 1 Ψ)
    (hL : LipschitzWith L (gradient Ψ)) (hs : 0 < s) (hsL : s*(L:ℝ)<1)
    (hP : ThreeOpSplitting.ConvexRates.IsProx s Φ P)
    (hrun : InertialAVD.Algo.IsPerturbedRun Ψ P α s g x y)
    (hα : 3 < α) (hg : Summable (fun k : ℕ => (k:ℝ)*‖g k‖))
    (xstar : H) (hxstar : ∀ v : H, NesterovFB.Rates.theta Φ Ψ xstar ≤ NesterovFB.Rates.theta Φ Ψ v) :
    NesterovFB.Rates.theta Φ Ψ xstar ≠ ⊤ ∧
    (∀ k : ℕ, 1 ≤ k → NesterovFB.Rates.theta Φ Ψ (x k) ≠ ⊤) ∧
    (∀ k : ℕ, 1 ≤ k → 0 ≤ gap Φ Ψ xstar (x k)) := by
  have _ := hΨc; have _ := hΨd; have _ := hL; have _ := hs
  have _ := hsL; have _ := hα; have _ := hg
  obtain ⟨w, hw⟩ := hΦ.2.1
  have hstar : NesterovFB.Rates.theta Φ Ψ xstar ≠ ⊤ :=
    ne_top_of_le_ne_top ((theta_finite_iff Φ Ψ w).mpr hw) (hxstar w)
  have hfinite (k : ℕ) (hk : 1 ≤ k) : NesterovFB.Rates.theta Φ Ψ (x k) ≠ ⊤ := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
    rw [hrun.2 j]
    exact (theta_finite_iff Φ Ψ _).mpr (prox_finite Φ s P hΦ hP _)
  refine ⟨hstar, hfinite, fun k hk => ?_⟩
  exact sub_nonneg.mpr (EReal.toReal_le_toReal (hxstar (x k))
    (theta_ne_bot Φ Ψ hΦ xstar) (hfinite k hk))

theorem proximal_three_point (Φ : H → EReal) (Ψ : H → ℝ) (L : NNReal)
    (s : ℝ) (P : H → H)
    (hΦ : ThreeOpSplitting.ConvexRates.IsProperClosedConvex Φ)
    (hΨc : ConvexOn ℝ Set.univ Ψ) (hΨd : ContDiff ℝ 1 Ψ)
    (hL : LipschitzWith L (gradient Ψ)) (hs : 0 < s) (hsL : s*(L:ℝ)<1)
    (hP : ThreeOpSplitting.ConvexRates.IsProx s Φ P)
    (y g u : H) (hu : NesterovFB.Rates.theta Φ Ψ u ≠ ⊤) :
    objectiveReal Φ Ψ (P (y-s • (gradient Ψ y-g)))-objectiveReal Φ Ψ u ≤
      (‖y-u‖^2-‖P (y-s • (gradient Ψ y-g))-u‖^2)/(2*s)+
        inner ℝ g (P (y-s • (gradient Ψ y-g))-u) := by
  let z := y-s • (gradient Ψ y-g)
  let p := P z
  have hpu := prox_subgradient_real Φ s P hΦ hs hP z u ((theta_finite_iff Φ Ψ u).mp hu)
  have hp := prox_finite Φ s P hΦ hP z
  have hu' := (theta_finite_iff Φ Ψ u).mp hu
  have hsm := smooth_upper_model Ψ L hΨd hL y p
  have hsu := gradient_support Ψ hΨc hΨd y u
  have hi : inner ℝ (z-p) (u-p) =
      inner ℝ (y-p) (u-p)-s*inner ℝ (gradient Ψ y) (u-p)+s*inner ℝ g (u-p) := by
    dsimp [z]
    simp only [inner_sub_left, real_inner_smul_left, inner_sub_right]
    ring
  have hnorm : ‖y-u‖^2-‖p-u‖^2 = ‖p-y‖^2+2*inner ℝ (y-p) (p-u) := by
    have he : y-u = (y-p)+(p-u) := by abel
    rw [he, norm_add_sq_real, norm_sub_rev y p]
    ring
  have hneg (v : H) : inner ℝ v (u-p) = -inner ℝ v (p-u) := by
    rw [show u-p = -(p-u) by abel, inner_neg_right]
  have hgrad : inner ℝ (gradient Ψ y) (p-y)-inner ℝ (gradient Ψ y) (u-y) =
      inner ℝ (gradient Ψ y) (p-u) := by simp only [inner_sub_right]; ring
  rw [hi, hneg, hneg, hneg] at hpu
  have hscaled := mul_le_mul_of_nonneg_right hpu hs.le
  have hs0 : s≠0 := hs.ne'
  field_simp [hs0] at hscaled
  change objectiveReal Φ Ψ p-objectiveReal Φ Ψ u ≤
    (‖y-u‖^2-‖p-u‖^2)/(2*s)+inner ℝ g (p-u)
  rw [objectiveReal_eq Φ Ψ hΦ p hp, objectiveReal_eq Φ Ψ hΦ u hu']
  apply (mul_le_mul_iff_right₀ (by positivity : 0<2*s)).mp
  have hn := sq_nonneg ‖p-y‖
  have hres := mul_nonneg (sub_nonneg.mpr hsL.le) hn
  field_simp [hs0]
  have hsmS := mul_le_mul_of_nonneg_left hsm hs.le
  have hsuS := mul_le_mul_of_nonneg_left hsu hs.le
  have hgradS := congrArg (fun r : ℝ => s*r) hgrad
  change (Φ p).toReal*s + _ ≤ _ at hscaled
  nlinarith only [hscaled, hsmS, hsuS, hnorm, hgradS, hres]

theorem run_three_point (Φ : H → EReal) (Ψ : H → ℝ) (L : NNReal) (s α : ℝ)
    (P : H → H) (g x y : ℕ → H)
    (hΦ : ThreeOpSplitting.ConvexRates.IsProperClosedConvex Φ)
    (hΨc : ConvexOn ℝ Set.univ Ψ) (hΨd : ContDiff ℝ 1 Ψ)
    (hL : LipschitzWith L (gradient Ψ)) (hs : 0 < s) (hsL : s*(L:ℝ)<1)
    (hP : ThreeOpSplitting.ConvexRates.IsProx s Φ P)
    (hrun : InertialAVD.Algo.IsPerturbedRun Ψ P α s g x y)
    (hα : 3 < α) (hg : Summable (fun k : ℕ => (k:ℝ)*‖g k‖))
    (xstar : H) (hxstar : ∀ v : H, NesterovFB.Rates.theta Φ Ψ xstar ≤ NesterovFB.Rates.theta Φ Ψ v) (k : ℕ) (u : H)
    (hu : NesterovFB.Rates.theta Φ Ψ u ≠ ⊤) :
    objectiveReal Φ Ψ (x (k+1))-objectiveReal Φ Ψ u ≤
      (‖y k-u‖^2-‖x (k+1)-u‖^2)/(2*s)+inner ℝ (g k) (x (k+1)-u) := by
  have _ := hα; have _ := hg; have _ := hxstar
  rw [hrun.2 k]
  exact proximal_three_point Φ Ψ L s P hΦ hΨc hΨd hL hs hsL hP (y k) (g k) u hu

 theorem z_current (Ψ : H → ℝ) (P : H → H) (α s : ℝ) (g x y : ℕ → H)
    (hrun : InertialAVD.Algo.IsPerturbedRun Ψ P α s g x y)
    (hα : 3 < α) (k : ℕ) (hk : 1 ≤ k) :
    InertialAVD.Algo.zSeq α x y k = x k+(((k:ℝ)-1)/(α-1)) • (x k-x (k-1)) := by
  have ha : α-1≠0 := by linarith
  have hb : (k:ℝ)+α-1≠0 := ne_of_gt (by nlinarith [show (0:ℝ)≤(k:ℝ) from Nat.cast_nonneg k])
  unfold InertialAVD.Algo.zSeq
  rw [hrun.1 k hk, smul_add, smul_smul]
  rw [show (((k:ℝ)+α-1)/(α-1))*(((k:ℝ)-1)/((k:ℝ)+α-1)) =
    ((k:ℝ)-1)/(α-1) by field_simp]
  rw [show ((k:ℝ)+α-1)/(α-1) = 1+(k:ℝ)/(α-1) by field_simp; ring]
  module

theorem z_next (Ψ : H → ℝ) (P : H → H) (α s : ℝ) (g x y : ℕ → H)
    (hrun : InertialAVD.Algo.IsPerturbedRun Ψ P α s g x y)
    (hα : 3 < α) (k : ℕ) :
    InertialAVD.Algo.zSeq α x y (k+1) =
      (((k:ℝ)+α-1)/(α-1)) • x (k+1)-((k:ℝ)/(α-1)) • x k := by
  rw [z_current Ψ P α s g x y hrun hα (k+1) (by omega)]
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  have ha : α-1≠0 := by linarith
  rw [show ((k:ℝ)+α-1)/(α-1) = 1+(k:ℝ)/(α-1) by field_simp; ring]
  module

omit [CompleteSpace H] in
 theorem weighted_norm_difference (p y x u : H) (t : ℝ) :
    t*(t-1)*(‖y-x‖^2-‖p-x‖^2)+t*(‖y-u‖^2-‖p-u‖^2) =
    ‖t • y-(t-1) • x-u‖^2-‖t • p-(t-1) • x-u‖^2 := by
  simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_sub_left, real_inner_smul_left, inner_smul_right]
  ring

theorem energy_step (Φ : H → EReal) (Ψ : H → ℝ) (L : NNReal) (s α : ℝ)
    (P : H → H) (g x y : ℕ → H)
    (hΦ : ThreeOpSplitting.ConvexRates.IsProperClosedConvex Φ)
    (hΨc : ConvexOn ℝ Set.univ Ψ) (hΨd : ContDiff ℝ 1 Ψ)
    (hL : LipschitzWith L (gradient Ψ)) (hs : 0 < s) (hsL : s*(L:ℝ)<1)
    (hP : ThreeOpSplitting.ConvexRates.IsProx s Φ P)
    (hrun : InertialAVD.Algo.IsPerturbedRun Ψ P α s g x y)
    (hα : 3 < α) (hg : Summable (fun k : ℕ => (k:ℝ)*‖g k‖))
    (xstar : H) (hxstar : ∀ v : H, NesterovFB.Rates.theta Φ Ψ xstar ≤ NesterovFB.Rates.theta Φ Ψ v) (k : ℕ) (hk : 1 ≤ k) :
    energy Φ Ψ α s x y xstar (k+1)+
      (((α-3)*(k:ℝ)+(α-2)^2)/(α-1)^2)*gap Φ Ψ xstar (x k) ≤
    energy Φ Ψ α s x y xstar k+
      (((k:ℝ)+α-1)/(α-1))*inner ℝ (g k)
        (InertialAVD.Algo.zSeq α x y (k+1)-xstar) := by
  obtain ⟨hstar,hfinite,_⟩ := objective_finite Φ Ψ L s α P g x y hΦ hΨc hΨd hL hs hsL hP hrun hα hg xstar hxstar
  have h1 := run_three_point Φ Ψ L s α P g x y hΦ hΨc hΨd hL hs hsL hP hrun hα hg xstar hxstar k (x k) (hfinite k hk)
  have h2 := run_three_point Φ Ψ L s α P g x y hΦ hΨc hΨd hL hs hsL hP hrun hα hg xstar hxstar k xstar hstar
  let t : ℝ := ((k:ℝ)+α-1)/(α-1)
  have ha : 0<α-1 := by linarith
  have ht : 1≤t := by dsimp [t]; apply (le_div_iff₀ ha).mpr; nlinarith [show (0:ℝ)≤(k:ℝ) from Nat.cast_nonneg k]
  have hn := weighted_norm_difference (x (k+1)) (y k) (x k) xstar t
  have hz0 : InertialAVD.Algo.zSeq α x y k = t • y k-(t-1) • x k := by
    unfold InertialAVD.Algo.zSeq
    have he : t-1=(k:ℝ)/(α-1) := by dsimp [t]; field_simp; ring
    rw [he]
  have hz1 : InertialAVD.Algo.zSeq α x y (k+1) = t • x (k+1)-(t-1) • x k := by
    rw [z_next Ψ P α s g x y hrun hα k]
    have he : t-1=(k:ℝ)/(α-1) := by dsimp [t]; field_simp; ring
    rw [he]
  have hi : t*(t-1)*inner ℝ (g k) (x (k+1)-x k)+t*inner ℝ (g k) (x (k+1)-xstar) =
      t*inner ℝ (g k) (InertialAVD.Algo.zSeq α x y (k+1)-xstar) := by
    rw [hz1]
    simp only [inner_sub_right, inner_smul_right]
    ring
  have hm1 := mul_le_mul_of_nonneg_left h1 (show 0≤t*(t-1) by positivity)
  have hm2 := mul_le_mul_of_nonneg_left h2 (show 0≤t by linarith)
  have hc : (((k:ℝ)+α-2)/(α-1))^2-
      (((α-3)*(k:ℝ)+(α-2)^2)/(α-1)^2) = t*(t-1) := by
    dsimp [t]; field_simp; ring
  have hnext : (((k+1:ℕ):ℝ)+α-2)/(α-1)=t := by dsimp [t]; push_cast; congr 1; ring
  rw [← hz0, ← hz1] at hn
  have hadd := add_le_add hm1 hm2
  have hrhs : t*(t-1)*((‖y k-x k‖^2-‖x (k+1)-x k‖^2)/(2*s)+inner ℝ (g k) (x (k+1)-x k))+
      t*((‖y k-xstar‖^2-‖x (k+1)-xstar‖^2)/(2*s)+inner ℝ (g k) (x (k+1)-xstar)) =
      (‖InertialAVD.Algo.zSeq α x y k-xstar‖^2-‖InertialAVD.Algo.zSeq α x y (k+1)-xstar‖^2)/(2*s)+
      t*inner ℝ (g k) (InertialAVD.Algo.zSeq α x y (k+1)-xstar) := by
    calc
      _ = (t*(t-1)*(‖y k-x k‖^2-‖x (k+1)-x k‖^2)+t*(‖y k-xstar‖^2-‖x (k+1)-xstar‖^2))/(2*s)+
        (t*(t-1)*inner ℝ (g k) (x (k+1)-x k)+t*inner ℝ (g k) (x (k+1)-xstar)) := by ring
      _ = _ := by rw [hn, hi]
  rw [hrhs, sub_div] at hadd
  have hcG := congrArg (fun r : ℝ => r*gap Φ Ψ xstar (x k)) hc
  dsimp [energy]
  rw [hnext]
  change _ ≤ _ + t*inner ℝ (g k) (InertialAVD.Algo.zSeq α x y (k+1)-xstar)
  dsimp [gap] at hcG ⊢
  nlinarith only [hadd, hcG]

end PerturbedIFBProof

noncomputable section
open Filter Topology Finset InnerProductSpace
namespace PerturbedIFBProof
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
 theorem error_norm_summable (g : ℕ → H)
    (hg : Summable (fun k : ℕ => (k:ℝ)*‖g k‖)) : Summable (fun k => ‖g k‖) := by
  apply hg.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hkR : (1:ℝ)≤k := by exact_mod_cast hk
  simpa only [norm_norm] using (le_mul_of_one_le_left (norm_nonneg (g k)) hkR)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
 theorem weighted_error_summable (g : ℕ → H) (α : ℝ)
    (hg : Summable (fun k : ℕ => (k:ℝ)*‖g k‖)) :
    Summable (fun k : ℕ => (((k:ℝ)+α-1)/(α-1))*‖g k‖) := by
  have hn := error_norm_summable g hg
  convert! (hg.add (hn.mul_left (α-1))).div_const (α-1) using 1
  ext k
  ring

omit [CompleteSpace H] in
 theorem energy_z_sqrt (Φ : H → EReal) (Ψ : H → ℝ) (α s : ℝ)
    (x y : ℕ → H) (xstar : H) (k : ℕ) (hs : 0<s)
    (hq : 0≤gap Φ Ψ xstar (x k)) :
    0≤energy Φ Ψ α s x y xstar k ∧
    ‖InertialAVD.Algo.zSeq α x y k-xstar‖ ≤
      Real.sqrt (2*s)*Real.sqrt (energy Φ Ψ α s x y xstar k) := by
  have hterm : 0≤(((k:ℝ)+α-2)/(α-1))^2*gap Φ Ψ xstar (x k) := mul_nonneg (sq_nonneg _) hq
  have hE : 0≤energy Φ Ψ α s x y xstar k := by dsimp [energy]; positivity
  refine ⟨hE, ?_⟩
  have hle : ‖InertialAVD.Algo.zSeq α x y k-xstar‖^2/(2*s) ≤ energy Φ Ψ α s x y xstar k := by
    dsimp [energy]; linarith only [hterm]
  have hsq := (div_le_iff₀ (by positivity : 0<2*s)).mp hle
  have h1 := Real.sq_sqrt (show 0≤2*s by positivity)
  have h2 := Real.sq_sqrt hE
  have hp : 0≤Real.sqrt (2*s)*Real.sqrt (energy Φ Ψ α s x y xstar k) := by positivity
  nlinarith only [hsq, h1, h2, hp, norm_nonneg (InertialAVD.Algo.zSeq α x y k-xstar)]

 theorem energy_and_z_bounded (Φ : H → EReal) (Ψ : H → ℝ) (L : NNReal) (s α : ℝ)
    (P : H → H) (g x y : ℕ → H)
    (hΦ : ThreeOpSplitting.ConvexRates.IsProperClosedConvex Φ)
    (hΨc : ConvexOn ℝ Set.univ Ψ) (hΨd : ContDiff ℝ 1 Ψ)
    (hL : LipschitzWith L (gradient Ψ)) (hs : 0 < s) (hsL : s*(L:ℝ)<1)
    (hP : ThreeOpSplitting.ConvexRates.IsProx s Φ P)
    (hrun : InertialAVD.Algo.IsPerturbedRun Ψ P α s g x y)
    (hα : 3 < α) (hg : Summable (fun k : ℕ => (k:ℝ)*‖g k‖))
    (xstar : H) (hxstar : ∀ v : H, NesterovFB.Rates.theta Φ Ψ xstar ≤ NesterovFB.Rates.theta Φ Ψ v) :
    ∃ B : ℝ, 0≤B ∧ ∀ k : ℕ, 1≤k →
      energy Φ Ψ α s x y xstar k ≤ B ∧ ‖InertialAVD.Algo.zSeq α x y k-xstar‖≤B := by
  have hf := objective_finite Φ Ψ L s α P g x y hΦ hΨc hΨd hL hs hsL hP hrun hα hg xstar hxstar
  let E := energy Φ Ψ α s x y xstar
  let e : ℕ → ℝ := fun k => (((k:ℝ)+α-1)/(α-1))*‖g k‖*Real.sqrt (2*s)
  have ha : 0<α-1 := by linarith
  have ha3 : 0<α-3 := by linarith
  have ht (k : ℕ) : 0≤((k:ℝ)+α-1)/(α-1) := div_nonneg (by nlinarith [show (0:ℝ)≤(k:ℝ) from Nat.cast_nonneg k]) ha.le
  have hE (k : ℕ) : 0≤E (k+1) := (energy_z_sqrt Φ Ψ α s x y xstar (k+1) hs (hf.2.2 _ (by omega))).1
  have he (k : ℕ) : 0≤e k := mul_nonneg (mul_nonneg (ht k) (norm_nonneg _)) (Real.sqrt_nonneg _)
  have hsum : Summable e := (weighted_error_summable g α hg).mul_right _
  have hstep (k : ℕ) : E (k+2)≤E (k+1)+e (k+1)*Real.sqrt (E (k+2)) := by
    have h := energy_step Φ Ψ L s α P g x y hΦ hΨc hΨd hL hs hsL hP hrun hα hg xstar hxstar (k+1) (by omega)
    have hq := hf.2.2 (k+1) (by omega)
    have hc : 0≤(((α-3)*((k+1:ℕ):ℝ)+(α-2)^2)/(α-1)^2)*gap Φ Ψ xstar (x (k+1)) := by positivity
    have hi := real_inner_le_norm (g (k+1)) (InertialAVD.Algo.zSeq α x y (k+2)-xstar)
    have hz := (energy_z_sqrt Φ Ψ α s x y xstar (k+2) hs (hf.2.2 _ (by omega))).2
    have hm := mul_le_mul_of_nonneg_left (hi.trans (mul_le_mul_of_nonneg_left hz (norm_nonneg _))) (ht (k+1))
    dsimp [E,e]
    simp only [Nat.add_assoc] at h
    nlinarith only [h,hc,hm]
  obtain ⟨B,hB,hbound⟩ := square_root_energy_bound E e hE he hsum hstep
  let C := Real.sqrt (2*s)*Real.sqrt B
  have hC : 0≤C := by dsimp[C]; positivity
  refine ⟨B+C, by positivity, fun k hk => ?_⟩
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
  have hb := hbound j
  have hz := (energy_z_sqrt Φ Ψ α s x y xstar (j+1) hs (hf.2.2 _ (by omega))).2
  have hzC : ‖InertialAVD.Algo.zSeq α x y (j+1)-xstar‖≤C :=
    hz.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hb) (Real.sqrt_nonneg _))
  exact ⟨by dsimp[E] at hb; linarith only [hb,hC], by linarith only [hzC,hB]⟩

 theorem weighted_gap_summable (Φ : H → EReal) (Ψ : H → ℝ) (L : NNReal) (s α : ℝ)
    (P : H → H) (g x y : ℕ → H)
    (hΦ : ThreeOpSplitting.ConvexRates.IsProperClosedConvex Φ)
    (hΨc : ConvexOn ℝ Set.univ Ψ) (hΨd : ContDiff ℝ 1 Ψ)
    (hL : LipschitzWith L (gradient Ψ)) (hs : 0 < s) (hsL : s*(L:ℝ)<1)
    (hP : ThreeOpSplitting.ConvexRates.IsProx s Φ P)
    (hrun : InertialAVD.Algo.IsPerturbedRun Ψ P α s g x y)
    (hα : 3 < α) (hg : Summable (fun k : ℕ => (k:ℝ)*‖g k‖))
    (xstar : H) (hxstar : ∀ v : H, NesterovFB.Rates.theta Φ Ψ xstar ≤ NesterovFB.Rates.theta Φ Ψ v) :
    Summable (fun k : ℕ => (k:ℝ)*gap Φ Ψ xstar (x k)) := by
  have hf := objective_finite Φ Ψ L s α P g x y hΦ hΨc hΨd hL hs hsL hP hrun hα hg xstar hxstar
  obtain ⟨B,hB,hbound⟩ := energy_and_z_bounded Φ Ψ L s α P g x y hΦ hΨc hΨd hL hs hsL hP hrun hα hg xstar hxstar
  let C := (α-3)/(α-1)^2
  have ha : 0<α-1 := by linarith
  have ha3 : 0<α-3 := by linarith
  have hC : 0<C := by dsimp[C]; positivity
  let D : ℕ → ℝ := fun n => energy Φ Ψ α s x y xstar (n+1)
  let q : ℕ → ℝ := fun n => C*(((n+1:ℕ):ℝ)*gap Φ Ψ xstar (x (n+1)))
  let r : ℕ → ℝ := fun n => B*((((n+1:ℕ):ℝ)+α-1)/(α-1)*‖g (n+1)‖)
  have hD (n : ℕ) : 0≤D n := (energy_z_sqrt Φ Ψ α s x y xstar (n+1) hs (hf.2.2 _ (by omega))).1
  have hq (n : ℕ) : 0≤q n := by have := hf.2.2 (n+1) (by omega); dsimp[q]; positivity
  have ht (n : ℕ) : 0≤(((n:ℝ)+α-1)/(α-1)) := div_nonneg (by nlinarith [show (0:ℝ)≤(n:ℝ) from Nat.cast_nonneg n]) ha.le
  have hr (n : ℕ) : 0≤r n := mul_nonneg hB (mul_nonneg (ht _) (norm_nonneg _))
  have hsumm : Summable r := ((summable_nat_add_iff 1).2 (weighted_error_summable g α hg)).mul_left B
  have hstep (n : ℕ) : D (n+1)+q n≤D n+r n := by
    have h := energy_step Φ Ψ L s α P g x y hΦ hΨc hΨd hL hs hsL hP hrun hα hg xstar hxstar (n+1) (by omega)
    have hgap := hf.2.2 (n+1) (by omega)
    have hz := (hbound (n+2) (by omega)).2
    have hi := real_inner_le_norm (g (n+1)) (InertialAVD.Algo.zSeq α x y (n+2)-xstar)
    have hm := mul_le_mul_of_nonneg_left (hi.trans (mul_le_mul_of_nonneg_left hz (norm_nonneg _)))
      (ht (n+1))
    have hc : C*((n+1:ℕ):ℝ) ≤ (((α-3)*((n+1:ℕ):ℝ)+(α-2)^2)/(α-1)^2) := by
      dsimp[C]; apply (le_div_iff₀ (by positivity : 0<(α-1)^2)).mpr
      field_simp
      nlinarith only [sq_nonneg (α-2)]
    have hcm := mul_le_mul_of_nonneg_right hc hgap
    dsimp[D,q,r]
    simp only [Nat.add_assoc] at h
    nlinarith only [h,hm,hcm]
  have hqs := dissipation_summable D q r hD hq hr hsumm hstep
  have ht : Summable (fun n : ℕ => ((n+1:ℕ):ℝ)*gap Φ Ψ xstar (x (n+1))) := by
    convert! hqs.div_const C using 1
    ext n
    dsimp[q]
    field_simp
  exact (summable_nat_add_iff 1).1 ht

theorem run_bounds (Φ : H → EReal) (Ψ : H → ℝ) (L : NNReal) (s α : ℝ)
    (P : H → H) (g x y : ℕ → H)
    (hΦ : ThreeOpSplitting.ConvexRates.IsProperClosedConvex Φ)
    (hΨc : ConvexOn ℝ Set.univ Ψ) (hΨd : ContDiff ℝ 1 Ψ)
    (hL : LipschitzWith L (gradient Ψ)) (hs : 0 < s) (hsL : s*(L:ℝ)<1)
    (hP : ThreeOpSplitting.ConvexRates.IsProx s Φ P)
    (hrun : InertialAVD.Algo.IsPerturbedRun Ψ P α s g x y)
    (hα : 3 < α) (hg : Summable (fun k : ℕ => (k:ℝ)*‖g k‖))
    (xstar : H) (hxstar : ∀ v : H, NesterovFB.Rates.theta Φ Ψ xstar ≤ NesterovFB.Rates.theta Φ Ψ v) :
    ∃ B : ℝ, 0≤B ∧ (∀ k : ℕ, ‖x k-xstar‖≤B) ∧
      (∀ k : ℕ, (k:ℝ)*‖velocity x k‖≤B) := by
  obtain ⟨B,hB,hbound⟩ := energy_and_z_bounded Φ Ψ L s α P g x y hΦ hΨc hΨd hL hs hsL hP hrun hα hg xstar hxstar
  have ha : 0<α-1 := by linarith
  let C := B+‖x 1-xstar‖
  have hC : 0≤C := by dsimp[C]; positivity
  have hBC : B≤C := by dsimp[C]; linarith [norm_nonneg (x 1-xstar)]
  have hxc : ∀ j : ℕ, ‖x (j+1)-xstar‖≤C := by
    intro j
    induction j with
    | zero => dsimp[C]; linarith only [hB]
    | succ j ih =>
      let k := j+1
      let u : ℝ := (α-1)/((k:ℝ)+α-1)
      let v : ℝ := (k:ℝ)/((k:ℝ)+α-1)
      have hd : 0<(k:ℝ)+α-1 := by nlinarith [show (0:ℝ)≤(k:ℝ) from Nat.cast_nonneg k]
      have hu : 0≤u := by dsimp[u]; positivity
      have hv : 0≤v := by dsimp[v]; positivity
      have huv : u+v=1 := by dsimp[u,v]; field_simp; ring
      have he : x (k+1)-xstar = u • (InertialAVD.Algo.zSeq α x y (k+1)-xstar)+v • (x k-xstar) := by
        rw [z_next Ψ P α s g x y hrun hα k]
        simp only [smul_sub, smul_smul]
        have h1 : u*(((k:ℝ)+α-1)/(α-1))=1 := by dsimp[u]; field_simp
        have h2 : u*((k:ℝ)/(α-1))=v := by dsimp[u,v]; field_simp
        rw [h1,h2,one_smul]
        have h3 : u=1-v := by linarith only [huv]
        rw [h3]
        module
      have hz := (hbound (k+1) (by omega)).2
      have hh : ‖x (k+1)-xstar‖≤C := by
        rw [he]
        calc
          _ ≤ ‖u • (InertialAVD.Algo.zSeq α x y (k+1)-xstar)‖+‖v • (x k-xstar)‖ := norm_add_le _ _
          _ = u*‖InertialAVD.Algo.zSeq α x y (k+1)-xstar‖+v*‖x k-xstar‖ := by
            simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hu,abs_of_nonneg hv]
          _ ≤ u*C+v*C := add_le_add (mul_le_mul_of_nonneg_left (hz.trans hBC) hu)
            (mul_le_mul_of_nonneg_left ih hv)
          _ = C := by rw [← add_mul, huv, one_mul]
      exact hh
  have hvb (k : ℕ) : (k:ℝ)*‖velocity x k‖≤(α-1)*(B+C) := by
    have he : (k:ℝ) • velocity x k = (α-1) • (InertialAVD.Algo.zSeq α x y (k+1)-x (k+1)) := by
      rw [z_next Ψ P α s g x y hrun hα k]
      simp only [smul_sub,smul_smul]
      have h1 : (α-1)*(((k:ℝ)+α-1)/(α-1))=(k:ℝ)+α-1 := by field_simp
      have h2 : (α-1)*((k:ℝ)/(α-1))=(k:ℝ) := by field_simp
      rw [h1,h2]
      dsimp[velocity]
      module
    have hn := congrArg norm he
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (show (0:ℝ)≤(k:ℝ) from Nat.cast_nonneg k),abs_of_pos ha] at hn
    rw [hn]
    apply mul_le_mul_of_nonneg_left _ ha.le
    have htri := norm_add_le (InertialAVD.Algo.zSeq α x y (k+1)-xstar) (xstar-x (k+1))
    rw [sub_add_sub_cancel] at htri
    rw [norm_sub_rev xstar (x (k+1))] at htri
    linarith only [htri,(hbound (k+1) (by omega)).2,hxc k]
  let D := ‖x 0-xstar‖+C+(α-1)*(B+C)
  have hA : 0≤(α-1)*(B+C) := by positivity
  refine ⟨D, by dsimp[D]; positivity, ?_, ?_⟩
  · intro k
    cases k with
    | zero => dsimp[D]; linarith only [hC,hA]
    | succ k => have hh := hxc k; dsimp[D]; linarith only [hh,hA,norm_nonneg (x 0-xstar)]
  · intro k
    have hh := hvb k
    dsimp[D]
    linarith only [hh,hC,norm_nonneg (x 0-xstar)]

end PerturbedIFBProof

open Filter Topology Finset
noncomputable section
namespace PerturbedIFBProof
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (Φ : H → EReal) (Ψ : H → ℝ) (L : NNReal) (s α : ℝ)
  (P : H → H) (g x y : ℕ → H)
  (hΦ : ThreeOpSplitting.ConvexRates.IsProperClosedConvex Φ)
  (hΨc : ConvexOn ℝ Set.univ Ψ) (hΨd : ContDiff ℝ 1 Ψ)
  (hL : LipschitzWith L (gradient Ψ))
  (hs : 0 < s) (hsL : s * (L : ℝ) < 1)
  (hP : ThreeOpSplitting.ConvexRates.IsProx s Φ P)
  (hrun : InertialAVD.Algo.IsPerturbedRun Ψ P α s g x y)
  (hα : 3 < α) (hg : Summable (fun k : ℕ => (k : ℝ) * ‖g k‖))
  (xstar : H) (hxstar : ∀ v : H, NesterovFB.Rates.theta Φ Ψ xstar ≤ NesterovFB.Rates.theta Φ Ψ v)

include hΦ hΨc hΨd hL hs hsL hP hrun hα hg hxstar

theorem velocity_summable :
    Summable (fun k : ℕ => (k:ℝ) * ‖velocity x k‖^2) := by
  let a := α-1
  have ha : 2 < a := by dsimp [a]; linarith
  have ha0 : 0 < a := by linarith
  let q : ℕ → ℝ := fun k => gap Φ Ψ xstar (x k)
  have hfinite := objective_finite Φ Ψ L s α P g x y hΦ hΨc hΨd hL hs hsL hP hrun hα hg xstar hxstar
  have hq (k : ℕ) (hk : 1 ≤ k) : 0 ≤ q k := hfinite.2.2 k hk
  have hqs := weighted_gap_summable Φ Ψ L s α P g x y hΦ hΨc hΨd hL hs hsL hP hrun hα hg xstar hxstar
  obtain ⟨B, hB, _, hv⟩ := run_bounds Φ Ψ L s α P g x y hΦ hΨc hΨd hL hs hsL hP hrun hα hg xstar hxstar
  let D : ℕ → ℝ := fun n => ((n:ℝ)+a)^2 * (‖velocity x n‖^2/2+s*q (n+1))
  let h : ℕ → ℝ := fun n => a*(2*(n:ℝ)+a)*‖velocity x n‖^2/2
  let r : ℕ → ℝ := fun n => s*(2*a+1)*(((n+1:ℕ):ℝ)*q (n+1)) +
    s*B*(a+1)^2*(((n+1:ℕ):ℝ)*‖g (n+1)‖)
  have hr : ∀ n, 0 ≤ r n := by
    intro n
    have hqn := hq (n+1) (by omega)
    dsimp [r]
    positivity
  have hsr : Summable r := by
    have hqsh : Summable (fun n : ℕ => ((n+1:ℕ):ℝ)*q (n+1)) :=
      (summable_nat_add_iff 1).2 hqs
    have hgsh := (summable_nat_add_iff 1).2 hg
    exact (hqsh.mul_left (s*(2*a+1))).add (hgsh.mul_left (s*B*(a+1)^2))
  have hstep : ∀ n, D (n+1)+h n ≤ D n+r n := by
    intro n
    let k := n+1
    have hk : 1 ≤ k := by dsimp [k]; omega
    have hkR : 1 ≤ (k:ℝ) := by exact_mod_cast hk
    have hden : 0 < (k:ℝ)+a := by positivity
    have ht := run_three_point Φ Ψ L s α P g x y hΦ hΨc hΨd hL hs hsL hP hrun hα hg xstar hxstar k (x k) (hfinite.2.1 k hk)
    have hy : ‖y k-x k‖^2 = (((k:ℝ)-1)/((k:ℝ)+a))^2 * ‖velocity x n‖^2 := by
      rw [hrun.1 k hk]
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      have he : k-1 = n := by omega
      rw [he]
      simp only [a, velocity, add_sub_assoc, k]
    rw [hy] at ht
    have hi := real_inner_le_norm (g k) (x (k+1)-x k)
    have hb : q (k+1)-q k ≤
        ((((k:ℝ)-1)/((k:ℝ)+a))^2 * ‖velocity x n‖^2-‖velocity x k‖^2)/(2*s)+
          ‖g k‖*‖velocity x k‖ := by
      dsimp [q, gap, velocity] at ht hi ⊢
      linarith only [ht, hi]
    have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2*s*((k:ℝ)+a)^2 by positivity)
    have hpoly : ((k:ℝ)+a)^2*‖velocity x k‖^2/2 -
        ((k:ℝ)-1)^2*‖velocity x n‖^2/2 ≤
      s*((k:ℝ)+a)^2*(q k-q (k+1))+
        s*((k:ℝ)+a)^2*‖g k‖*‖velocity x k‖ := by
      field_simp at hm
      nlinarith only [hm]
    have hweight : ((k:ℝ)+a)^2 ≤ (a+1)^2*(k:ℝ)^2 := by
      have hp : 0 ≤ (k:ℝ)+a := hden.le
      have ht : (k:ℝ)+a ≤ (a+1)*(k:ℝ) := by
        nlinarith only [mul_nonneg ha0.le (sub_nonneg.mpr hkR)]
      calc
        _ ≤ ((a+1)*(k:ℝ))^2 := pow_le_pow_left₀ hp ht 2
        _ = _ := mul_pow _ _ _
    have herr : ((k:ℝ)+a)^2*‖g k‖*‖velocity x k‖ ≤ B*(a+1)^2*((k:ℝ)*‖g k‖) := by
      calc
        _ ≤ ((a+1)^2*(k:ℝ)^2)*‖g k‖*‖velocity x k‖ := by gcongr
        _ = ((a+1)^2*((k:ℝ)*‖g k‖))*((k:ℝ)*‖velocity x k‖) := by ring
        _ ≤ ((a+1)^2*((k:ℝ)*‖g k‖))*B := by gcongr; exact hv k
        _ = _ := by ring
    have hgap : (2*(k:ℝ)+2*a-1)*q k ≤ (2*a+1)*((k:ℝ)*q k) := by
      have hqn := hq k hk
      have hp : 0 ≤ (2*a-1)*((k:ℝ)-1)*q k :=
        mul_nonneg (mul_nonneg (by linarith only [ha] : 0 ≤ 2*a-1) (sub_nonneg.mpr hkR)) hqn
      nlinarith only [hp]
    have herrs := mul_le_mul_of_nonneg_left herr hs.le
    have hgapS := mul_le_mul_of_nonneg_left hgap hs.le
    dsimp [D,h,r]
    have heq : (k:ℝ) = (n:ℝ)+1 := by dsimp [k]; push_cast; rfl
    rw [heq] at hpoly herrs hgapS
    dsimp [k] at hpoly herrs hgapS
    push_cast
    nlinarith only [hpoly,herrs,hgapS]
  have hsh : Summable h := dissipation_summable D h r
    (fun n => by dsimp [D]; have := hq (n+1) (by omega); positivity)
    (fun n => by dsimp [h]; positivity) hr hsr hstep
  apply (hsh.div_const a).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (k:ℝ)*‖velocity x k‖^2)]
  apply (le_div_iff₀ ha0).2
  dsimp [h]
  have ht : 0 ≤ a^2*‖velocity x k‖^2 := by positivity
  nlinarith only [ht]

end PerturbedIFBProof

open Filter Topology
noncomputable section
namespace PerturbedIFBProof
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (Φ : H → EReal) (Ψ : H → ℝ) (L : NNReal) (s α : ℝ)
  (P : H → H) (g x y : ℕ → H)
  (hΦ : ThreeOpSplitting.ConvexRates.IsProperClosedConvex Φ)
  (hΨc : ConvexOn ℝ Set.univ Ψ) (hΨd : ContDiff ℝ 1 Ψ)
  (hL : LipschitzWith L (gradient Ψ))
  (hs : 0 < s) (hsL : s * (L : ℝ) < 1)
  (hP : ThreeOpSplitting.ConvexRates.IsProx s Φ P)
  (hrun : InertialAVD.Algo.IsPerturbedRun Ψ P α s g x y)
  (hα : 3 < α) (hg : Summable (fun k : ℕ => (k : ℝ) * ‖g k‖))
  (xstar : H) (hxstar : ∀ v : H, NesterovFB.Rates.theta Φ Ψ xstar ≤ NesterovFB.Rates.theta Φ Ψ v)

include hΦ hΨc hΨd hL hs hsL hP hrun hα hg hxstar

theorem distance_squared_limit :
    ∃ l : ℝ, Tendsto (fun k : ℕ => ‖x k-xstar‖^2) atTop (𝓝 l) := by
  let a := α-1
  have ha : 2 < a := by dsimp [a]; linarith
  have ha0 : 0 < a := by linarith
  obtain ⟨B,hB,hxB,_⟩ := run_bounds Φ Ψ L s α P g x y hΦ hΨc hΨd hL hs hsL hP hrun hα hg xstar hxstar
  have hfinite := objective_finite Φ Ψ L s α P g x y hΦ hΨc hΨd hL hs hsL hP hrun hα hg xstar hxstar
  have hvs := velocity_summable Φ Ψ L s α P g x y hΦ hΨc hΨd hL hs hsL hP hrun hα hg xstar hxstar
  have hvs0 : Summable (fun k => ‖velocity x k‖^2) := by
    apply hvs.of_norm_bounded_eventually_nat
    filter_upwards [eventually_ge_atTop 1] with k hk
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hkR : 1 ≤ (k:ℝ) := by exact_mod_cast hk
    nlinarith [sq_nonneg ‖velocity x k‖]
  have hback : Summable (fun k : ℕ => (k:ℝ)*‖x k-x (k-1)‖^2) := by
    apply (summable_nat_add_iff 1).1
    convert! hvs.add hvs0 using 1
    ext k
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, velocity]
    ring
  let h : ℕ → ℝ := fun k => ‖x k-xstar‖^2/2
  let d : ℕ → ℝ := fun k => max (h k-h (k-1)) 0
  let u : ℕ → ℝ := fun k => ‖x k-x (k-1)‖^2+s*B*‖g k‖
  have hu : ∀ k, 0 ≤ u k := by intro k; dsimp [u]; positivity
  have hus : Summable (fun k : ℕ => (k:ℝ)*u k) := by
    convert hback.add (hg.mul_left (s*B)) using 1
    ext k
    dsimp [u]
    ring
  have hds : Summable d := by
    apply inertial_increment_summable a ha d u (fun k => le_max_right _ _) hu hus
    intro k hk
    let β := ((k:ℝ)-1)/((k:ℝ)+a)
    have hkR : 1 ≤ (k:ℝ) := by exact_mod_cast hk
    have hden : 0 < (k:ℝ)+a := by positivity
    have hβ : 0 ≤ β := div_nonneg (by linarith) hden.le
    have hβ1 : β ≤ 1 := (div_le_one hden).2 (by linarith)
    have hnorm : ‖y k-xstar‖^2 =
        (1+β)*‖x k-xstar‖^2-β*‖x (k-1)-xstar‖^2+
          β*(1+β)*‖x k-x (k-1)‖^2 := by
      have hy : y k-xstar = (x k-xstar)+β • (x k-x (k-1)) := by
        rw [hrun.1 k hk]
        dsimp [β,a]
        module
      have hp : ‖x (k-1)-xstar‖^2 = ‖x k-xstar‖^2-
          2*inner ℝ (x k-xstar) (x k-x (k-1))+‖x k-x (k-1)‖^2 := by
        rw [show x (k-1)-xstar = (x k-xstar)-(x k-x (k-1)) by abel, norm_sub_sq_real]
      rw [hy, norm_add_sq_real, hp]
      simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    have ht := run_three_point Φ Ψ L s α P g x y hΦ hΨc hΨd hL hs hsL hP hrun hα hg xstar hxstar k xstar hfinite.1
    have hq := hfinite.2.2 (k+1) (by omega)
    have hi : inner ℝ (g k) (x (k+1)-xstar) ≤ B*‖g k‖ := by
      calc
        _ ≤ ‖g k‖*‖x (k+1)-xstar‖ := real_inner_le_norm _ _
        _ ≤ ‖g k‖*B := mul_le_mul_of_nonneg_left (hxB _) (norm_nonneg _)
        _ = _ := mul_comm _ _
    have hn : ‖x (k+1)-xstar‖^2 ≤ ‖y k-xstar‖^2+2*s*B*‖g k‖ := by
      dsimp [gap] at hq
      have hm := (le_div_iff₀ (show 0 < 2*s by positivity)).1
        (show objectiveReal Φ Ψ (x (k+1))-objectiveReal Φ Ψ xstar-
          inner ℝ (g k) (x (k+1)-xstar) ≤
          (‖y k-xstar‖^2-‖x (k+1)-xstar‖^2)/(2*s) by linarith)
      have hqi := mul_nonneg hs.le hq
      have hii := mul_le_mul_of_nonneg_left hi (show 0 ≤ 2*s by positivity)
      nlinarith only [hm,hqi,hii]
    rw [hnorm] at hn
    have hcoef : β*(1+β)/2 ≤ 1 := by nlinarith
    have hsmall := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖x k-x (k-1)‖)
    have hdelta : h (k+1)-h k ≤ β*(h k-h (k-1))+u k := by
      dsimp [h,u]
      nlinarith only [hn,hsmall]
    have hm := mul_le_mul_of_nonneg_left (le_max_left (h k-h (k-1)) 0) hβ
    change max (h (k+1)-h ((k+1)-1)) 0 ≤ _
    rw [Nat.add_sub_cancel]
    apply max_le
    · dsimp [d] at hm ⊢
      linarith
    · exact add_nonneg (mul_nonneg hβ (le_max_right _ _)) (hu k)
  have hpos : Summable (fun k => max (h (k+1)-h k) 0) := by
    simpa only [d, Nat.add_sub_cancel] using (summable_nat_add_iff 1).2 hds
  obtain ⟨l,hl⟩ := nonneg_limit_of_pos_increment h (fun k => by dsimp [h]; positivity) hpos
  refine ⟨2*l, ?_⟩
  convert hl.const_mul 2 using 1
  ext k
  dsimp [h]
  ring

end PerturbedIFBProof

open Filter Topology Set

noncomputable section
namespace PerturbedIFBProof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem weak_ball_compact (R : ℝ) :
    IsCompact ((toWeakSpace ℝ H) '' Metric.closedBall (0 : H) R) := by
  let F : WeakDual ℝ H → WeakSpace ℝ H := fun f =>
    toWeakSpace ℝ H ((InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual f))
  have hc : Continuous F := by
    apply WeakBilin.continuous_of_continuous_eval
    intro ell
    change Continuous (fun f : WeakDual ℝ H =>
      ell ((InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual f)))
    have heq : (fun f : WeakDual ℝ H =>
        ell ((InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual f))) =
        (fun f : WeakDual ℝ H => f ((InnerProductSpace.toDual ℝ H).symm ell)) := by
      ext f
      rw [← InnerProductSpace.toDual_symm_apply (y := ell), real_inner_comm,
        InnerProductSpace.toDual_symm_apply]
      rfl
    rw [heq]
    exact WeakBilin.eval_continuous _ _
  have heq : F '' (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) R) =
      (toWeakSpace ℝ H) '' Metric.closedBall (0 : H) R := by
    ext w
    constructor
    · rintro ⟨f, hf, rfl⟩
      refine ⟨(InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual f), ?_, rfl⟩
      simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
        LinearIsometryEquiv.norm_map] using hf
    · rintro ⟨x, hx, rfl⟩
      refine ⟨StrongDual.toWeakDual ((InnerProductSpace.toDual ℝ H) x), ?_, ?_⟩
      · simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
          StrongDual.toStrongDual_toWeakDual, LinearIsometryEquiv.norm_map] using hx
      · simp only [F, StrongDual.toStrongDual_toWeakDual, LinearIsometryEquiv.symm_apply_apply]
  rw [← heq]
  exact (WeakDual.isCompact_closedBall (0 : StrongDual ℝ H) R).image hc

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
lemma theta_le_iff_phi_le (Φ : H → EReal) (Ψ : H → ℝ) (u : H) (r : ℝ) :
    NesterovFB.Rates.theta Φ Ψ u ≤ (r : EReal) ↔ Φ u ≤ ((r-Ψ u : ℝ) : EReal) := by
  unfold NesterovFB.Rates.theta
  rw [EReal.coe_sub]
  exact (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _))
    (Or.inl (EReal.coe_ne_top _))).symm

omit [CompleteSpace H] in
theorem theta_sublevel_weak_closed
    (Φ : H → EReal) (Ψ : H → ℝ)
    (hΦ : ThreeOpSplitting.ConvexRates.IsProperClosedConvex Φ)
    (hΨc : ConvexOn ℝ Set.univ Ψ) (hΨd : ContDiff ℝ 1 Ψ) (r : ℝ) :
    IsClosed ((toWeakSpace ℝ H) '' {u : H | NesterovFB.Rates.theta Φ Ψ u ≤ (r : EReal)}) := by
  let C : Set H := {u : H | NesterovFB.Rates.theta Φ Ψ u ≤ (r : EReal)}
  have hc : IsClosed C := by
    have hepi := hΦ.2.2.1.isClosed_epigraph
    have hm : Continuous (fun u : H => (u, ((r-Ψ u : ℝ) : EReal))) :=
      continuous_id.prodMk (continuous_coe_real_ereal.comp (continuous_const.sub hΨd.continuous))
    have heq : C = (fun u : H => (u, ((r-Ψ u : ℝ) : EReal))) ⁻¹'
        {p : H × EReal | Φ p.1 ≤ p.2} := by
      ext u
      exact theta_le_iff_phi_le Φ Ψ u r
    rw [heq]
    exact hepi.preimage hm
  have hv : Convex ℝ C := by
    intro x hx y hy a b ha hb hab
    have hpx : Φ x ≤ ((r-Ψ x : ℝ) : EReal) := (theta_le_iff_phi_le Φ Ψ x r).1 hx
    have hpy : Φ y ≤ ((r-Ψ y : ℝ) : EReal) := (theta_le_iff_phi_le Φ Ψ y r).1 hy
    have hepi := hΦ.2.2.2 (x := (x, r-Ψ x)) (y := (y, r-Ψ y)) hpx hpy ha hb hab
    have hfun := hΨc.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    have hp : Φ (a • x + b • y) ≤ ((a*(r-Ψ x)+b*(r-Ψ y) : ℝ) : EReal) := by
      change Φ (a • x+b • y) ≤ ((a*(r-Ψ x)+b*(r-Ψ y) : ℝ) : EReal) at hepi
      exact hepi
    apply (theta_le_iff_phi_le Φ Ψ (a • x+b • y) r).2
    refine hp.trans (EReal.coe_le_coe ?_)
    simp only [smul_eq_mul] at hfun
    have hr := congrArg (fun t : ℝ => t*r) hab
    nlinarith
  have heq := hv.toWeakSpace_closure ℝ
  rw [hc.closure_eq] at heq
  rw [heq]
  exact isClosed_closure

end PerturbedIFBProof

open Filter Topology Set
noncomputable section
namespace PerturbedIFBProof

lemma cluster_continuous_limit {W : Type*} [TopologicalSpace W]
    (w : ℕ → W) (p : W) (hp : MapClusterPt p atTop w)
    (F : W → ℝ) (hF : Continuous F) (l : ℝ)
    (hl : Tendsto (fun k => F (w k)) atTop (𝓝 l)) : F p = l := by
  let : NeBot (𝓝 p ⊓ Filter.map w atTop) := hp
  have h1 : Tendsto F (𝓝 p ⊓ Filter.map w atTop) (𝓝 (F p)) :=
    (hF.tendsto p).mono_left inf_le_left
  have h2 : Tendsto F (𝓝 p ⊓ Filter.map w atTop) (𝓝 l) :=
    (Filter.tendsto_map'_iff.2 hl).mono_left inf_le_right
  exact tendsto_nhds_unique h1 h2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (Φ : H → EReal) (Ψ : H → ℝ) (L : NNReal) (s α : ℝ)
  (P : H → H) (g x y : ℕ → H)
  (hΦ : ThreeOpSplitting.ConvexRates.IsProperClosedConvex Φ)
  (hΨc : ConvexOn ℝ Set.univ Ψ) (hΨd : ContDiff ℝ 1 Ψ)
  (hL : LipschitzWith L (gradient Ψ))
  (hs : 0 < s) (hsL : s * (L : ℝ) < 1)
  (hP : ThreeOpSplitting.ConvexRates.IsProx s Φ P)
  (hrun : InertialAVD.Algo.IsPerturbedRun Ψ P α s g x y)
  (hα : 3 < α) (hg : Summable (fun k : ℕ => (k : ℝ) * ‖g k‖))
  (xstar : H) (hxstar : ∀ v : H, NesterovFB.Rates.theta Φ Ψ xstar ≤ NesterovFB.Rates.theta Φ Ψ v)

include hΦ hΨc hΨd hL hs hsL hP hrun hα hg hxstar

theorem weak_cluster_minimizer
    (p : WeakSpace ℝ H)
    (hp : MapClusterPt p atTop (fun k => toWeakSpace ℝ H (x k))) :
    ∀ v : H, NesterovFB.Rates.theta Φ Ψ ((toWeakSpace ℝ H).symm p) ≤
      NesterovFB.Rates.theta Φ Ψ v := by
  have hfinite := objective_finite Φ Ψ L s α P g x y hΦ hΨc hΨd hL hs hsL hP hrun hα hg xstar hxstar
  have hsum := weighted_gap_summable Φ Ψ L s α P g x y hΦ hΨc hΨd hL hs hsL hP hrun hα hg xstar hxstar
  have hgap : Tendsto (fun k => gap Φ Ψ xstar (x k)) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hsum.tendsto_atTop_zero
    · filter_upwards [eventually_ge_atTop 1] with k hk using hfinite.2.2 k hk
    · filter_upwards [eventually_ge_atTop 1] with k hk
      have hkR : 1 ≤ (k:ℝ) := by exact_mod_cast hk
      have hn := hfinite.2.2 k hk
      nlinarith
  have hle (ε : ℝ) (hε : 0 < ε) :
      NesterovFB.Rates.theta Φ Ψ ((toWeakSpace ℝ H).symm p) ≤
        ((objectiveReal Φ Ψ xstar+ε : ℝ) : EReal) := by
    let C := (toWeakSpace ℝ H) '' {u : H | NesterovFB.Rates.theta Φ Ψ u ≤
      ((objectiveReal Φ Ψ xstar+ε : ℝ) : EReal)}
    have hc : IsClosed C := theta_sublevel_weak_closed Φ Ψ hΦ hΨc hΨd _
    have he : ∀ᶠ k in atTop, toWeakSpace ℝ H (x k) ∈ C := by
      filter_upwards [hgap.eventually (eventually_lt_nhds hε), eventually_ge_atTop 1] with k hgk hk
      refine ⟨x k, ?_, rfl⟩
      change NesterovFB.Rates.theta Φ Ψ (x k) ≤ _
      rw [← EReal.coe_toReal (hfinite.2.1 k hk) (theta_ne_bot Φ Ψ hΦ (x k))]
      apply EReal.coe_le_coe
      dsimp [gap, objectiveReal] at hgk ⊢
      linarith
    have hmap : Filter.map (fun k => toWeakSpace ℝ H (x k)) atTop ≤ 𝓟 C :=
      Filter.le_principal_iff.2 (Filter.mem_map.2 he)
    have hm : p ∈ C := isClosed_iff_clusterPt.1 hc p (ClusterPt.mono hp hmap)
    rcases hm with ⟨u,hu,rfl⟩
    simpa only [LinearEquiv.symm_apply_apply, Set.mem_ofPred_eq] using hu
  have hpfin : NesterovFB.Rates.theta Φ Ψ ((toWeakSpace ℝ H).symm p) ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top _) (hle 1 zero_lt_one)
  have hr : objectiveReal Φ Ψ ((toWeakSpace ℝ H).symm p) ≤ objectiveReal Φ Ψ xstar := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have ht := EReal.toReal_le_toReal (hle ε hε)
      (theta_ne_bot Φ Ψ hΦ _) (EReal.coe_ne_top _)
    simpa only [objectiveReal, EReal.toReal_coe] using ht
  intro v
  apply le_trans _ (hxstar v)
  rw [← EReal.coe_toReal hpfin (theta_ne_bot Φ Ψ hΦ _),
    ← EReal.coe_toReal hfinite.1 (theta_ne_bot Φ Ψ hΦ _)]
  exact EReal.coe_le_coe hr

theorem weak_cluster_unique
    (p q : WeakSpace ℝ H)
    (hp : MapClusterPt p atTop (fun k => toWeakSpace ℝ H (x k)))
    (hq : MapClusterPt q atTop (fun k => toWeakSpace ℝ H (x k))) : p = q := by
  let P0 := (toWeakSpace ℝ H).symm p
  let Q0 := (toWeakSpace ℝ H).symm q
  have hpm := weak_cluster_minimizer Φ Ψ L s α P g x y hΦ hΨc hΨd hL hs hsL hP hrun hα hg xstar hxstar p hp
  have hqm := weak_cluster_minimizer Φ Ψ L s α P g x y hΦ hΨc hΨd hL hs hsL hP hrun hα hg xstar hxstar q hq
  obtain ⟨lp,hlp⟩ := distance_squared_limit Φ Ψ L s α P g x y hΦ hΨc hΨd hL hs hsL hP hrun hα hg P0 hpm
  obtain ⟨lq,hlq⟩ := distance_squared_limit Φ Ψ L s α P g x y hΦ hΨc hΨd hL hs hsL hP hrun hα hg Q0 hqm
  let F : WeakSpace ℝ H → ℝ := fun w =>
    2*inner ℝ ((toWeakSpace ℝ H).symm w) (Q0-P0)+‖P0‖^2-‖Q0‖^2
  have hc : Continuous F := by
    have he : Continuous (fun w : WeakSpace ℝ H =>
        (InnerProductSpace.toDual ℝ H (Q0-P0)) ((toWeakSpace ℝ H).symm w)) :=
      WeakBilin.eval_continuous (topDualPairing ℝ H).flip (InnerProductSpace.toDual ℝ H (Q0-P0))
    have heq : (fun w : WeakSpace ℝ H => inner ℝ ((toWeakSpace ℝ H).symm w) (Q0-P0)) =
        (fun w : WeakSpace ℝ H => (InnerProductSpace.toDual ℝ H (Q0-P0)) ((toWeakSpace ℝ H).symm w)) := by
      ext w
      exact real_inner_comm _ _
    have hh : Continuous (fun w : WeakSpace ℝ H => inner ℝ ((toWeakSpace ℝ H).symm w) (Q0-P0)) := by rw [heq]; exact he
    exact ((hh.const_mul 2).add continuous_const).sub continuous_const
  have hidentity (v : H) : 2*inner ℝ v (Q0-P0)+‖P0‖^2-‖Q0‖^2 =
      ‖v-P0‖^2-‖v-Q0‖^2 := by
    rw [norm_sub_sq_real, norm_sub_sq_real, inner_sub_right]
    ring
  have ht : Tendsto (fun k => F (toWeakSpace ℝ H (x k))) atTop (𝓝 (lp-lq)) := by
    simpa only [F, LinearEquiv.symm_apply_apply, hidentity] using hlp.sub hlq
  have hpv := cluster_continuous_limit (fun k => toWeakSpace ℝ H (x k)) p hp F hc _ ht
  have hqv := cluster_continuous_limit (fun k => toWeakSpace ℝ H (x k)) q hq F hc _ ht
  have hpq : ‖P0-Q0‖^2 = 0 := by
    change 2*inner ℝ P0 (Q0-P0)+‖P0‖^2-‖Q0‖^2 = _ at hpv
    change 2*inner ℝ Q0 (Q0-P0)+‖P0‖^2-‖Q0‖^2 = _ at hqv
    rw [hidentity] at hpv hqv
    norm_num only [sub_self, norm_zero] at hpv hqv
    rw [norm_sub_rev Q0 P0] at hqv
    linarith
  have heq : P0 = Q0 := sub_eq_zero.1 (norm_eq_zero.1 (by nlinarith [norm_nonneg (P0-Q0)]))
  exact (toWeakSpace ℝ H).symm.injective heq

theorem weak_converges :
    ∃ xbar : H,
      (∀ v : H, NesterovFB.Rates.theta Φ Ψ xbar ≤ NesterovFB.Rates.theta Φ Ψ v) ∧
      InertialFB.IFB.WeakTendsto x xbar := by
  obtain ⟨B,hB,hbound,_⟩ := run_bounds Φ Ψ L s α P g x y hΦ hΨc hΨd hL hs hsL hP hrun hα hg xstar hxstar
  let K := (toWeakSpace ℝ H) '' Metric.closedBall (0 : H) (B+‖xstar‖)
  have hc : IsCompact K := weak_ball_compact _
  have he : ∀ᶠ k in atTop, toWeakSpace ℝ H (x k) ∈ K := by
    apply Filter.Eventually.of_forall
    intro k
    refine ⟨x k, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖x k‖ = ‖(x k-xstar)+xstar‖ := by rw [sub_add_cancel]
      _ ≤ ‖x k-xstar‖+‖xstar‖ := norm_add_le _ _
      _ ≤ B+‖xstar‖ := add_le_add (hbound k) le_rfl
  obtain ⟨p,_,hp⟩ := hc.exists_mapClusterPt (Filter.le_principal_iff.2 (Filter.mem_map.2 he))
  have hlim : Tendsto (fun k => toWeakSpace ℝ H (x k)) atTop (𝓝 p) := by
    apply hc.tendsto_nhds_of_unique_mapClusterPt he
    intro q _ hq
    exact weak_cluster_unique Φ Ψ L s α P g x y hΦ hΨc hΨd hL hs hsL hP hrun hα hg xstar hxstar q p hq hp
  refine ⟨(toWeakSpace ℝ H).symm p,
    weak_cluster_minimizer Φ Ψ L s α P g x y hΦ hΨc hΨd hL hs hsL hP hrun hα hg xstar hxstar p hp, ?_⟩
  intro v
  have heval : Continuous (fun w : WeakSpace ℝ H =>
      (InnerProductSpace.toDual ℝ H v) ((toWeakSpace ℝ H).symm w)) :=
    WeakBilin.eval_continuous (topDualPairing ℝ H).flip (InnerProductSpace.toDual ℝ H v)
  simpa only [Function.comp_def, LinearEquiv.symm_apply_apply,
    InnerProductSpace.toDual_apply_apply, real_inner_comm] using
    (heval.tendsto p).comp hlim

end PerturbedIFBProof

open Filter Topology NesterovFB.Rates

namespace InertialAVD.Algo

/-- Theorem 5.3, p. 21 (iii with `argmin(Φ + Ψ)`, as the proof uses). Under the standing
hypotheses, with `α > 3`, `0 < s`, `sL < 1`, `∑ k‖g_k‖ < ∞` and `x*` a minimizer of `Θ = Φ + Ψ`:
i) `Θ(x_k) < +∞` for `k ≥ 1` and `∑_k k(Θ(x_k) − Θ(x*)) < +∞`;
ii) `∑_k k‖x_{k+1} − x_k‖² < +∞`;
iii) `x_k` converges weakly to some minimizer of `Θ`. -/
theorem theorem_5_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → EReal) (Ψ : H → ℝ) (L : NNReal) (s α : ℝ) (P : H → H) (g : ℕ → H) (x y : ℕ → H)
    (hΦ : ThreeOpSplitting.ConvexRates.IsProperClosedConvex Φ)
    (hΨc : ConvexOn ℝ Set.univ Ψ) (hΨd : ContDiff ℝ 1 Ψ)
    (hL : LipschitzWith L (gradient Ψ))
    (hs : 0 < s) (hsL : s * (L : ℝ) < 1)
    (hP : ThreeOpSplitting.ConvexRates.IsProx s Φ P)
    (hrun : IsPerturbedRun Ψ P α s g x y)
    (hα : 3 < α)
    (hg : Summable (fun k : ℕ => (k : ℝ) * ‖g k‖))
    (xstar : H) (hxstar : ∀ v : H, theta Φ Ψ xstar ≤ theta Φ Ψ v) :
    ((∀ k : ℕ, 1 ≤ k → theta Φ Ψ (x k) ≠ ⊤) ∧
      Summable (fun k : ℕ =>
        (k : ℝ) * ((theta Φ Ψ (x k)).toReal - (theta Φ Ψ xstar).toReal))) ∧
    Summable (fun k : ℕ => (k : ℝ) * ‖x (k + 1) - x k‖ ^ 2) ∧
    ∃ xbar : H, (∀ v : H, theta Φ Ψ xbar ≤ theta Φ Ψ v) ∧ InertialFB.IFB.WeakTendsto x xbar := by
  have hf := PerturbedIFBProof.objective_finite Φ Ψ L s α P g x y hΦ hΨc hΨd hL hs hsL hP hrun hα hg xstar hxstar
  refine ⟨⟨hf.2.1, ?_⟩, ?_, ?_⟩
  · exact PerturbedIFBProof.weighted_gap_summable Φ Ψ L s α P g x y hΦ hΨc hΨd hL hs hsL hP hrun hα hg xstar hxstar
  · exact PerturbedIFBProof.velocity_summable Φ Ψ L s α P g x y hΦ hΨc hΨd hL hs hsL hP hrun hα hg xstar hxstar
  · exact PerturbedIFBProof.weak_converges Φ Ψ L s α P g x y hΦ hΨc hΨd hL hs hsL hP hrun hα hg xstar hxstar

end InertialAVD.Algo

open InertialAVD.Algo

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → EReal) (Ψ : H → ℝ) (L : NNReal) (s α : ℝ) (P : H → H) (g : ℕ → H) (x y : ℕ → H)
    (hΦ : ThreeOpSplitting.ConvexRates.IsProperClosedConvex Φ)
    (hΨc : ConvexOn ℝ Set.univ Ψ) (hΨd : ContDiff ℝ 1 Ψ)
    (hL : LipschitzWith L (gradient Ψ))
    (hs : 0 < s) (hsL : s * (L : ℝ) < 1)
    (hP : ThreeOpSplitting.ConvexRates.IsProx s Φ P)
    (hrun : IsPerturbedRun Ψ P α s g x y)
    (hα : 3 < α)
    (hg : Summable (fun k : ℕ => (k : ℝ) * ‖g k‖))
    (xstar : H) (hxstar : ∀ v : H, theta Φ Ψ xstar ≤ theta Φ Ψ v) :
    ((∀ k : ℕ, 1 ≤ k → theta Φ Ψ (x k) ≠ ⊤) ∧
      Summable (fun k : ℕ =>
        (k : ℝ) * ((theta Φ Ψ (x k)).toReal - (theta Φ Ψ xstar).toReal))) ∧
    Summable (fun k : ℕ => (k : ℝ) * ‖x (k + 1) - x k‖ ^ 2) ∧
    ∃ xbar : H, (∀ v : H, theta Φ Ψ xbar ≤ theta Φ Ψ v) ∧ InertialFB.IFB.WeakTendsto x xbar := by
  exact InertialAVD.Algo.theorem_5_3 Φ Ψ L s α P g x y hΦ hΨc hΨd hL hs hsL hP hrun hα hg xstar hxstar
