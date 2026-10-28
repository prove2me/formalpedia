-- Prove2me | solution 1 for MultPacing.Existence.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T02:48:52.215241+00:00
-- url     : https://prove2.me/submissions/0005d56f-edf4-41cd-ba7b-37962a986b93

import Mathlib
import Definitions.Def_MultPacing_Existence_Limit

section BrouwerSec

open Metric Set MeasureTheory

namespace AGT.BrouwerAux

/-! Brouwer fixed-point theorem, analytic (Milnor–Rogers) route.

* (A)–(D), (L1): there is no `C¹` retraction `r` of the closed unit ball `B ⊆ ℝᵈ` onto the
  sphere. For small `t`, `x ↦ x + t (r x - x)` is a bijection of `B`, so by change of variables
  `∫_B det(1 + t A) = vol B`; the left side is a polynomial in `t`, hence equals `vol B` at
  `t = 1`, where the integrand `det (Dr)` vanishes because `r` takes values on the sphere.
* (L2): a fixed-point-free `C¹` self-map of `B` would give such a retraction.
* (L3): continuous maps are approximated by `C¹` maps (Stone–Weierstrass).
* (L4): a compact convex set is a retract of a ball (nearest-point map) after a linear
  identification of `E` with `ℝᵈ`. -/

/-- Helper for `A_perturb`: a Lipschitz map vanishing on the sphere is controlled by the
distance to any point outside the ball. -/
theorem A_perturb_boundary {d : ℕ} (h : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (L : NNReal) (hL : LipschitzOnWith L h (closedBall 0 1))
    (h0 : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1, h x = 0)
    {x z : EuclideanSpace ℝ (Fin d)} (hx : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)
    (hz : z ∉ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) :
    ‖h x‖ ≤ L * dist x z := by
  have hx' : ‖x‖ ≤ 1 := by simpa using hx
  have hz' : 1 < ‖z‖ := by simpa using hz
  have hcont : ContinuousOn (fun s : ℝ => ‖x + s • (z - x)‖) (Icc 0 1) := by
    fun_prop
  have h1 : (1 : ℝ) ∈ Icc ((fun s : ℝ => ‖x + s • (z - x)‖) 0)
      ((fun s : ℝ => ‖x + s • (z - x)‖) 1) := by
    simp only [zero_smul, add_zero, one_smul, add_sub_cancel]
    exact ⟨hx', hz'.le⟩
  obtain ⟨s, ⟨hs0, hs1⟩, hs⟩ := intermediate_value_Icc zero_le_one hcont h1
  have hwS : x + s • (z - x) ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1 := by simpa using hs
  have hwB : x + s • (z - x) ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 :=
    sphere_subset_closedBall hwS
  have hhw : h (x + s • (z - x)) = 0 := h0 _ hwS
  calc ‖h x‖ = dist (h x) (h (x + s • (z - x))) := by rw [hhw, dist_zero_right]
    _ ≤ L * dist x (x + s • (z - x)) := hL.dist_le_mul x hx _ hwB
    _ ≤ L * dist x z := by
      gcongr
      rw [dist_eq_norm, dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul,
        Real.norm_of_nonneg hs0, norm_sub_rev]
      exact mul_le_of_le_one_left (norm_nonneg _) hs1

/-- Helper for `A_perturb`: the extension by zero outside the ball is globally Lipschitz. -/
theorem A_perturb_ext_lip {d : ℕ} (h : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (L : NNReal) (hL : LipschitzOnWith L h (closedBall 0 1))
    (h0 : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1, h x = 0) :
    LipschitzWith L ((closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).indicator h) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  by_cases hx : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 <;>
    by_cases hy : y ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
    exact hL.dist_le_mul x hx y hy
  · rw [Set.indicator_of_mem hx, Set.indicator_of_notMem hy, dist_zero_right]
    exact A_perturb_boundary h L hL h0 hx hy
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_mem hy, dist_zero_left, dist_comm]
    exact A_perturb_boundary h L hL h0 hy hx
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy, dist_self]
    positivity

/-- (A) Lipschitz perturbation of the identity on the unit ball: injective and onto the ball. -/
theorem A_perturb {d : ℕ} (h : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L : NNReal)
    (hL : LipschitzOnWith L h (closedBall 0 1))
    (h0 : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1, h x = 0)
    (hB : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, x + h x ∈ closedBall 0 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htL : t * L < 1) :
    InjOn (fun x => x + t • h x) (closedBall 0 1) ∧
      (fun x => x + t • h x) '' closedBall 0 1 = closedBall 0 1 := by
  refine ⟨?_, ?_⟩
  · intro x hx y hy hxy
    simp only at hxy
    have h1 : x - y = t • h y - t • h x := by
      rw [sub_eq_sub_iff_add_eq_add, hxy, add_comm]
    have h2 : ‖x - y‖ ≤ t * L * ‖x - y‖ := by
      calc ‖x - y‖ = t * ‖h y - h x‖ := by
            rw [h1, ← smul_sub, norm_smul, Real.norm_of_nonneg ht0]
        _ ≤ t * (L * ‖y - x‖) := by
          gcongr
          rw [← dist_eq_norm, ← dist_eq_norm]
          exact hL.dist_le_mul y hy x hx
        _ = t * L * ‖x - y‖ := by rw [norm_sub_rev]; ring
    have h3 : ‖x - y‖ ≤ 0 := by
      have := norm_nonneg (x - y)
      nlinarith
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h3)
  · apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hc : x + t • h x = (1 - t) • x + t • (x + h x) := by
        rw [smul_add, sub_smul, one_smul]; abel
      simp only
      rw [hc]
      exact convex_closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 hx (hB x hx)
        (sub_nonneg.2 ht1) ht0 (by ring)
    · intro y hy
      set g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
        (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).indicator h with hg
      have hgL : LipschitzWith L g := A_perturb_ext_lip h L hL h0
      set G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun x => y - t • g x
        with hG
      have hGc : ContractingWith (Real.toNNReal t * L) G := by
        refine ⟨?_, ?_⟩
        · rw [← NNReal.coe_lt_coe]
          simpa [Real.coe_toNNReal t ht0] using htL
        · refine LipschitzWith.of_dist_le_mul fun a b => ?_
          have : dist (G a) (G b) = t * dist (g a) (g b) := by
            simp only [hG, dist_eq_norm]
            rw [sub_sub_sub_cancel_left, ← smul_sub, norm_smul, Real.norm_of_nonneg ht0,
              norm_sub_rev]
          rw [this, NNReal.coe_mul, Real.coe_toNNReal t ht0, mul_assoc]
          gcongr
          exact hgL.dist_le_mul a b
      set x := ContractingWith.fixedPoint G hGc with hx
      have hfix : G x = x := ContractingWith.fixedPoint_isFixedPt hGc
      by_cases hxB : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1
      · refine ⟨x, hxB, ?_⟩
        have : y - t • h x = x := by simpa [hG, hg, Set.indicator_of_mem hxB] using hfix
        exact (sub_eq_iff_eq_add.mp this).symm
      · exfalso
        have : y = x := by simpa [hG, hg, Set.indicator_of_notMem hxB] using hfix
        exact hxB (this ▸ hy)

section C_poly_section
open Polynomial

/-- `t ↦ det (1 + t • T)` is a real polynomial of degree `≤ d`. -/
theorem C_poly_det_poly {d : ℕ}
    (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    ∃ p : ℝ[X], p.natDegree ≤ d ∧ ∀ t : ℝ, (1 + t • T).det = p.eval t := by
  classical
  let b := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  let M := LinearMap.toMatrix b b (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))
  refine ⟨Matrix.det ((X : ℝ[X]) • M.map C + (1 : Matrix (Fin d) (Fin d) ℝ).map C), ?_, ?_⟩
  · simpa using natDegree_det_X_add_C_le M 1
  · intro t
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, ← Polynomial.coe_evalRingHom,
      RingHom.map_det]
    congr 1
    ext i j
    by_cases h : i = j <;> simp [M, h] <;> ring

/-- Lagrange interpolation at `d + 1` distinct nodes recovers the value at `1`
of any polynomial of degree `≤ d`. -/
theorem C_poly_interp {d : ℕ} (v : Fin (d+1) → ℝ) (hv : Function.Injective v) (p : ℝ[X])
    (hp : p.natDegree ≤ d) :
    p.eval 1 = ∑ i, (Lagrange.basis Finset.univ v i).eval 1 * p.eval (v i) := by
  have hdeg : p.degree < ((Finset.univ : Finset (Fin (d+1))).card : WithBot ℕ) := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact (Polynomial.degree_le_of_natDegree_le hp).trans_lt
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self d))
  conv_lhs => rw [Lagrange.eq_interpolate hv.injOn hdeg]
  simp [Lagrange.interpolate_apply, eval_finsetSum, mul_comm]

end C_poly_section

/-- (C) If `t ↦ ∫_s det(1 + t A)` is constant on an interval `(0, t₀)`, it has the same value at `t = 1`. -/
theorem C_poly {d : ℕ} (A : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
    (s : Set (EuclideanSpace ℝ (Fin d))) (hs : MeasurableSet s) (hfin : volume s < ⊤)
    (hA : ∃ C, ∀ x ∈ s, ‖A x‖ ≤ C) (hmeas : AEStronglyMeasurable A (volume.restrict s))
    (c t₀ : ℝ) (ht₀ : 0 < t₀)
    (hconst : ∀ t ∈ Ioo 0 t₀, ∫ x in s, (1 + t • A x).det = c) :
    ∫ x in s, (1 + A x).det = c := by
  classical
  obtain ⟨C, hC⟩ := hA
  -- interpolation nodes in `(0, t₀)`
  set v : Fin (d+1) → ℝ := fun i => t₀ * ((i : ℕ) + 1 : ℝ) / ((d : ℝ) + 2) with hv_def
  have hd2 : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  have hv_inj : Function.Injective v := by
    intro i j hij
    simp only [v] at hij
    have h1 : t₀ * (((i : ℕ) : ℝ) + 1) = t₀ * (((j : ℕ) : ℝ) + 1) := by
      have := congrArg (· * ((d : ℝ) + 2)) hij
      simpa [div_mul_cancel₀, hd2.ne'] using this
    have h2 : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by
      have := mul_left_cancel₀ ht₀.ne' h1
      linarith
    exact Fin.ext (by exact_mod_cast h2)
  have hv_mem : ∀ i, v i ∈ Ioo 0 t₀ := by
    intro i
    have hi : ((i : ℕ) : ℝ) + 1 ≤ (d : ℝ) + 1 := by
      have : (i : ℕ) ≤ d := Nat.lt_succ_iff.mp i.isLt
      have : ((i : ℕ) : ℝ) ≤ d := by exact_mod_cast this
      linarith
    refine ⟨by positivity, ?_⟩
    simp only [v]
    rw [div_lt_iff₀ hd2]
    nlinarith
  -- interpolation weights
  set ℓ : Fin (d+1) → ℝ := fun i => (Lagrange.basis Finset.univ v i).eval 1 with hℓ_def
  have key : ∀ T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
      (1 + T).det = ∑ i, ℓ i * (1 + v i • T).det := by
    intro T
    obtain ⟨p, hp, hpt⟩ := C_poly_det_poly T
    have hint := C_poly_interp v hv_inj p hp
    rw [show (1 + T) = 1 + (1 : ℝ) • T by simp, hpt 1, hint]
    simp [ℓ, hpt]
  have hsum : ∑ i, ℓ i = 1 := by
    have h0 : ∀ a : ℝ, a • (0 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) = 0 :=
      fun a => by ext x; simp
    have h1 : (1 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)).det = 1 := by
      simp [ContinuousLinearMap.det]
    have := key 0
    simp only [h0, add_zero, h1, mul_one] at this
    exact this.symm
  -- integrability of `x ↦ det (1 + t • A x)` on `s`
  have hint : ∀ t : ℝ, IntegrableOn (fun x => (1 + t • A x).det) s volume := by
    intro t
    have hcont : Continuous fun T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) =>
        (1 + t • T).det :=
      ContinuousLinearMap.continuous_det.comp (continuous_const.add (continuous_const_smul t))
    obtain ⟨K, hK⟩ := (isCompact_closedBall
      (0 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) C).exists_bound_of_continuousOn
      hcont.continuousOn
    refine IntegrableOn.of_bound hfin (hcont.comp_aestronglyMeasurable hmeas) K ?_
    refine ae_restrict_of_forall_mem hs (fun x hx => hK _ ?_)
    rw [mem_closedBall, dist_zero_right]
    exact hC x hx
  calc ∫ x in s, (1 + A x).det = ∫ x in s, ∑ i, ℓ i * (1 + v i • A x).det := by
        congr 1
        funext x
        exact key (A x)
    _ = ∑ i, ∫ x in s, ℓ i * (1 + v i • A x).det :=
        integral_finsetSum _ (fun i _ => (hint (v i)).const_mul (ℓ i))
    _ = ∑ i, ℓ i * c := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [integral_const_mul, hconst _ (hv_mem i)]
    _ = c := by rw [← Finset.sum_mul, hsum, one_mul]

/-- (D) A map with values on the unit sphere near `x` has singular derivative at `x`. -/
theorem D_det_zero {d : ℕ} (r : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) (U : Set (EuclideanSpace ℝ (Fin d))) (hU : U ∈ nhds x)
    (hr : DifferentiableAt ℝ r x) (hsph : ∀ y ∈ U, ‖r y‖ = 1) :
    (fderiv ℝ r x).det = 0 := by
  classical
  set Dr := fderiv ℝ r x with hDr
  -- derivative of `y ↦ ⟪r y, r y⟫` via the product rule
  have hφ : HasFDerivAt (fun y => inner ℝ (r y) (r y))
      ((fderivInnerCLM ℝ (r x, r x)).comp (Dr.prod Dr)) x :=
    hr.hasFDerivAt.inner ℝ hr.hasFDerivAt
  -- but `⟪r y, r y⟫ = 1` near `x`, so the derivative vanishes
  have hconst : (fun y => inner ℝ (r y) (r y)) =ᶠ[nhds x] fun _ => (1 : ℝ) := by
    filter_upwards [hU] with y hy
    rw [real_inner_self_eq_norm_sq, hsph y hy]
    norm_num
  have h0 : HasFDerivAt (fun y => inner ℝ (r y) (r y))
      (0 : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) x :=
    (hasFDerivAt_const (1 : ℝ) x).congr_of_eventuallyEq hconst
  have heq := hφ.unique h0
  have horth : ∀ v, inner ℝ (r x) (Dr v) = 0 := by
    intro v
    have hv := congrArg (fun L => L v) heq
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      fderivInnerCLM_apply, zero_apply] at hv
    have hc := real_inner_comm (Dr v) (r x)
    linarith
  -- if `det Dr ≠ 0`, then `Dr` is surjective, so `r x ∈ range Dr`, forcing `⟪r x, r x⟫ = 0`
  by_contra hdet
  have hunit : IsUnit (Dr : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) :=
    (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
  have hsurj : Function.Surjective
      (Dr : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) := by
    rw [← LinearMap.range_eq_top]
    exact (LinearMap.isUnit_iff_range_eq_top _).1 hunit
  obtain ⟨v, hv⟩ := hsurj (r x)
  have h1 := horth v
  have hv' : Dr v = r x := hv
  rw [hv', real_inner_self_eq_norm_sq, hsph x (mem_of_mem_nhds hU)] at h1
  norm_num at h1

/-- Helper: `1 + T` has positive determinant when `‖T‖ < 1`. -/
theorem L1_no_retraction_det_pos {d : ℕ}
    (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (hT : ‖T‖ < 1) :
    0 < (1 + T).det := by
  set f : ℝ → ℝ := fun s => (1 + s • T).det with hf
  have hcont : Continuous f :=
    ContinuousLinearMap.continuous_det.comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have hne : ∀ s ∈ Icc (0 : ℝ) 1, f s ≠ 0 := by
    intro s hs
    have hn : ‖-(s • T)‖ < 1 := by
      rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      calc s * ‖T‖ ≤ 1 * ‖T‖ := by gcongr; exact hs.2
        _ = ‖T‖ := one_mul _
        _ < 1 := hT
    have hu : IsUnit (1 + s • T) := by
      have := (Units.oneSub (-(s • T)) hn).isUnit
      simpa [Units.val_oneSub, sub_neg_eq_add] using this
    have hu' : IsUnit ((1 + s • T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
        EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) :=
      hu.map ContinuousLinearMap.toLinearMapRingHom
    exact (LinearMap.isUnit_det _ hu').ne_zero
  have h0 : f 0 = 1 := by simp [hf, ContinuousLinearMap.det]
  by_contra hneg
  rw [not_lt] at hneg
  have h1 : f 1 ≤ 0 := by simpa [hf] using hneg
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' zero_le_one hcont.continuousOn
    (show (0 : ℝ) ∈ Icc (f 1) (f 0) from ⟨h1, by rw [h0]; exact zero_le_one⟩)
  exact hne s hs hs0

/-- (L1) No `C¹` retraction of the closed unit ball onto the unit sphere. -/
theorem L1_no_retraction {d : ℕ} (hd : 0 < d)
    (r : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (U : Set (EuclideanSpace ℝ (Fin d))) (hU : IsOpen U) (hBU : closedBall 0 1 ⊆ U)
    (hr : ContDiffOn ℝ 1 r U)
    (hmaps : MapsTo r (closedBall 0 1) (sphere 0 1))
    (hid : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1, r x = x) : False := by
  classical
  have hdiff : ∀ x ∈ U, HasFDerivAt r (fderiv ℝ r x) x := fun x hx =>
    ((hr.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have hcontD : ContinuousOn (fderiv ℝ r) U := hr.continuousOn_fderiv_of_isOpen hU le_rfl
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).exists_bound_of_continuousOn
    (hcontD.mono hBU)
  set K : ℝ := max M 0 + 1 with hK
  have hK1 : 1 ≤ K := by
    have := le_max_right M 0
    linarith
  have hKpos : 0 < K := by linarith
  set A : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :=
    fun x => fderiv ℝ r x - 1 with hA
  have hAbound : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, ‖A x‖ ≤ K := by
    intro x hx
    calc ‖A x‖ ≤ ‖fderiv ℝ r x‖ +
          ‖(1 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))‖ := norm_sub_le _ _
      _ ≤ max M 0 + 1 :=
          add_le_add ((hM x hx).trans (le_max_left _ _)) ContinuousLinearMap.norm_id_le
  set h : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun x => r x - x with hh
  have hhderiv : ∀ x ∈ U, HasFDerivAt h (A x) x := fun x hx =>
    (hdiff x hx).sub (hasFDerivAt_id x)
  set L : NNReal := ⟨K, hKpos.le⟩ with hL
  have hLip : LipschitzOnWith L h (closedBall 0 1) := by
    apply (convex_closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (f' := A)
    · intro x hx
      exact (hhderiv x (hBU hx)).hasFDerivWithinAt
    · intro x hx
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact hAbound x hx
  have h0 : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1, h x = 0 := by
    intro x hx
    simp [hh, hid x hx]
  have hB : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, x + h x ∈ closedBall 0 1 := by
    intro x hx
    have : x + h x = r x := by simp [hh]
    rw [this]
    exact sphere_subset_closedBall (hmaps hx)
  set t₀ : ℝ := 1 / K with ht₀
  have ht₀pos : 0 < t₀ := by positivity
  have ht₀le : t₀ ≤ 1 := by
    rw [ht₀, div_le_one hKpos]
    exact hK1
  have hconst : ∀ t ∈ Ioo 0 t₀, ∫ x in closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
      (1 + t • A x).det = volume.real (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) := by
    intro t ht
    have htK : t * K < 1 := by
      have := ht.2
      rw [ht₀, lt_div_iff₀ hKpos] at this
      exact this
    have htL : t * (L : ℝ) < 1 := htK
    obtain ⟨hinj, himg⟩ := A_perturb h L hLip h0 hB ht.1.le (ht.2.le.trans ht₀le) htL
    have hFd : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
        HasFDerivWithinAt (fun x => x + t • h x) (1 + t • A x) (closedBall 0 1) x := by
      intro x hx
      exact ((hasFDerivAt_id x).add ((hhderiv x (hBU hx)).const_smul t)).hasFDerivWithinAt
    have hcov := integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_closedBall
      hFd hinj (fun _ => (1 : ℝ))
    rw [himg, setIntegral_const, smul_eq_mul, mul_one] at hcov
    rw [hcov]
    apply setIntegral_congr_fun measurableSet_closedBall
    intro x hx
    simp only [smul_eq_mul, mul_one]
    have hn : ‖t • A x‖ < 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
      calc t * ‖A x‖ ≤ t * K := mul_le_mul_of_nonneg_left (hAbound x hx) ht.1.le
        _ < 1 := htK
    exact (abs_of_pos (L1_no_retraction_det_pos _ hn)).symm
  have hmeas : AEStronglyMeasurable A (volume.restrict (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)) :=
    (measurable_fderiv ℝ r).aestronglyMeasurable.sub aestronglyMeasurable_const
  have hC := C_poly A (closedBall 0 1) measurableSet_closedBall measure_closedBall_lt_top
    ⟨K, hAbound⟩ hmeas _ t₀ ht₀pos hconst
  simp only [hA, add_sub_cancel] at hC
  have hzero : ∫ x in closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, (fderiv ℝ r x).det = 0 := by
    have : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
      Module.finrank_pos_iff.1 (by rw [finrank_euclideanSpace_fin]; exact hd)
    have hsph : volume (sphere (0 : EuclideanSpace ℝ (Fin d)) 1) = 0 :=
      Measure.addHaar_sphere volume 0 1
    have hae : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
        x ∉ sphere (0 : EuclideanSpace ℝ (Fin d)) 1 :=
      measure_eq_zero_iff_ae_notMem.1 hsph
    have : ∫ x in closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, (fderiv ℝ r x).det =
        ∫ x in closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, (0 : ℝ) := by
      apply setIntegral_congr_ae measurableSet_closedBall
      filter_upwards [hae] with x hx hxB
      have hxb : x ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1 := lt_of_le_of_ne hxB hx
      refine D_det_zero r x (ball 0 1) (isOpen_ball.mem_nhds hxb)
        (hdiff x (hBU (ball_subset_closedBall hxb))).differentiableAt ?_
      intro y hy
      have := hmaps (ball_subset_closedBall hy)
      simpa using this
    rw [this, integral_zero]
  have hpos : 0 < volume.real (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (measure_closedBall_pos volume 0 one_pos).ne'
      measure_closedBall_lt_top.ne
  rw [hzero] at hC
  linarith

/-- Expansion of `‖x + λ v‖²`. -/
theorem L2_brouwer_C1_norm_sq_eq {d : ℕ} (x v : EuclideanSpace ℝ (Fin d)) (lam : ℝ) :
    ‖x + lam • v‖ ^ 2 = ‖x‖ ^ 2 + 2 * lam * inner ℝ x v + lam ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- (L2) Brouwer for globally `C¹` self-maps of the closed unit ball. -/
theorem L2_brouwer_C1 {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hf : ContDiff ℝ 1 f) (hmaps : MapsTo f (closedBall 0 1) (closedBall 0 1)) :
    ∃ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, f x = x := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    exact ⟨0, by simp, Subsingleton.elim _ _⟩
  by_contra hne
  push Not at hne
  obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
      v = fun x => x - f x := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : EuclideanSpace ℝ (Fin d) → ℝ, a = fun x => inner ℝ x (v x) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : EuclideanSpace ℝ (Fin d) → ℝ, b = fun x => ‖v x‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : EuclideanSpace ℝ (Fin d) → ℝ, c = fun x => 1 - ‖x‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨disc, hdisc⟩ : ∃ disc : EuclideanSpace ℝ (Fin d) → ℝ,
      disc = fun x => a x ^ 2 + b x * c x := ⟨_, rfl⟩
  obtain ⟨lam, hlam⟩ : ∃ lam : EuclideanSpace ℝ (Fin d) → ℝ,
      lam = fun x => (-(a x) + Real.sqrt (disc x)) / b x := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
      r = fun x => x + lam x • v x := ⟨_, rfl⟩
  -- smoothness of the ingredients
  have hvC : ContDiff ℝ 1 v := by rw [hv]; exact contDiff_id.sub hf
  have haC : ContDiff ℝ 1 a := by rw [ha]; exact contDiff_id.inner ℝ hvC
  have hbC : ContDiff ℝ 1 b := by rw [hb]; exact hvC.norm_sq ℝ
  have hcC : ContDiff ℝ 1 c := by rw [hc]; exact contDiff_const.sub (contDiff_norm_sq ℝ)
  have hdiscC : ContDiff ℝ 1 disc := by rw [hdisc]; exact (haC.pow 2).add (hbC.mul hcC)
  -- the open set
  set U : Set (EuclideanSpace ℝ (Fin d)) := {x | 0 < disc x ∧ 0 < b x} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const hdiscC.continuous).inter
      (isOpen_lt continuous_const hbC.continuous)
  -- key identity: `2 a = ‖x‖² - ‖f x‖² + b`
  have hkey : ∀ x, 2 * a x = ‖x‖ ^ 2 - ‖f x‖ ^ 2 + b x := by
    intro x
    have hfx : f x = x - v x := by rw [hv]; simp
    have h2 := norm_sub_sq_real x (v x)
    rw [← hfx] at h2
    rw [ha, hb]
    simp only
    linarith
  have hb_pos : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, 0 < b x := by
    intro x hx
    have hvx : v x ≠ 0 := by
      rw [hv]; exact sub_ne_zero.mpr (hne x hx).symm
    rw [hb]
    simp only
    have := norm_pos_iff.mpr hvx
    positivity
  have hfx1 : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, ‖f x‖ ≤ 1 :=
    fun x hx => mem_closedBall_zero_iff.mp (hmaps hx)
  have hc_nonneg : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, 0 ≤ c x := by
    intro x hx
    have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
    rw [hc]
    simp only
    nlinarith [norm_nonneg x]
  have hdisc_pos : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, 0 < disc x := by
    intro x hx
    have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
    have hbx := hb_pos x hx
    have hk := hkey x
    have hf1 := hfx1 x hx
    have hcx := hc_nonneg x hx
    rw [hdisc]
    simp only
    rcases hx1.lt_or_eq with hlt | heq
    · have hcpos : 0 < c x := by
        rw [hc]; simp only; nlinarith [norm_nonneg x]
      nlinarith [sq_nonneg (a x), mul_pos hbx hcpos]
    · have hax : 0 < a x := by
        rw [heq] at hk; nlinarith [norm_nonneg (f x)]
      nlinarith [mul_nonneg hbx.le hcx]
  have hBU : closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ U :=
    fun x hx => ⟨hdisc_pos x hx, hb_pos x hx⟩
  -- `r` is `C¹` on `U`
  have hrC : ContDiffOn ℝ 1 r U := by
    intro x hx
    apply ContDiffAt.contDiffWithinAt
    have hsq : ContDiffAt ℝ 1 (fun y => Real.sqrt (disc y)) x :=
      hdiscC.contDiffAt.sqrt hx.1.ne'
    have hlamC : ContDiffAt ℝ 1 lam x := by
      rw [hlam]
      exact (haC.contDiffAt.neg.add hsq).fun_div hbC.contDiffAt hx.2.ne'
    rw [hr]
    exact contDiffAt_id.add (hlamC.smul hvC.contDiffAt)
  -- `r` maps the ball to the sphere
  have hr_norm : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, ‖r x‖ = 1 := by
    intro x hx
    have hbx := hb_pos x hx
    have hdx := hdisc_pos x hx
    have hs : Real.sqrt (disc x) ^ 2 = a x ^ 2 + b x * c x := by
      rw [Real.sq_sqrt hdx.le, hdisc]
    have hl : lam x * b x = -(a x) + Real.sqrt (disc x) := by
      rw [hlam]; simp only; field_simp
    have hcx : c x = 1 - ‖x‖ ^ 2 := by rw [hc]
    have h1 : ‖r x‖ ^ 2 = 1 := by
      have e : ‖r x‖ ^ 2 = ‖x‖ ^ 2 + 2 * lam x * a x + lam x ^ 2 * b x := by
        rw [hr, ha, hb]
        simp only
        exact L2_brouwer_C1_norm_sq_eq x (v x) (lam x)
      rw [e]
      apply mul_left_cancel₀ hbx.ne'
      linear_combination (lam x * b x + Real.sqrt (disc x) + a x) * hl + hs + b x * hcx
    have h0 := norm_nonneg (r x)
    nlinarith
  have hmapsr : MapsTo r (closedBall 0 1) (sphere 0 1) :=
    fun x hx => mem_sphere_zero_iff_norm.mpr (hr_norm x hx)
  -- `r` is the identity on the sphere
  have hid : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1, r x = x := by
    intro x hx
    have hx1 : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
    have hxB : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 :=
      sphere_subset_closedBall hx
    have hbx := hb_pos x hxB
    have hk := hkey x
    have hf1 := hfx1 x hxB
    have hcx : c x = 0 := by rw [hc]; simp [hx1]
    have hax : 0 < a x := by
      rw [hx1] at hk; nlinarith [norm_nonneg (f x)]
    have hdx : disc x = a x ^ 2 := by rw [hdisc]; simp [hcx]
    have hlx : lam x = 0 := by
      rw [hlam]; simp only; rw [hdx, Real.sqrt_sq hax.le]; simp
    rw [hr]; simp [hlx]
  exact L1_no_retraction hd r U hUo hBU hrC hmapsr hid

theorem L3_brouwer_ball_scalar_approx {d : ℕ} (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : ContinuousOn φ (closedBall 0 1)) (η : ℝ) (hη : 0 < η) :
    ∃ G : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 1 G ∧
      ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, |G x - φ x| < η := by
  set B : Set (EuclideanSpace ℝ (Fin d)) := closedBall 0 1 with hB
  have : CompactSpace B := isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  let A : Subalgebra ℝ C(B, ℝ) :=
    { carrier := {g | ∃ G : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 1 G ∧ ∀ x : B, g x = G x}
      mul_mem' := by
        rintro a b ⟨Ga, hGa, ha⟩ ⟨Gb, hGb, hb⟩
        exact ⟨fun x => Ga x * Gb x, hGa.mul hGb, fun x => by simp [ha, hb]⟩
      add_mem' := by
        rintro a b ⟨Ga, hGa, ha⟩ ⟨Gb, hGb, hb⟩
        exact ⟨fun x => Ga x + Gb x, hGa.add hGb, fun x => by simp [ha, hb]⟩
      algebraMap_mem' := fun r => ⟨fun _ => r, contDiff_const, fun x => by simp⟩ }
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    have : ∃ i, (x : EuclideanSpace ℝ (Fin d)) i ≠ (y : EuclideanSpace ℝ (Fin d)) i := by
      by_contra h
      push Not at h
      apply hxy
      apply Subtype.ext
      ext i
      exact h i
    obtain ⟨i, hi⟩ := this
    refine ⟨fun z : B => (z : EuclideanSpace ℝ (Fin d)) i, ?_, hi⟩
    refine ⟨⟨fun z : B => (z : EuclideanSpace ℝ (Fin d)) i, by fun_prop⟩, ?_, rfl⟩
    exact ⟨fun z => z i, (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).contDiff,
      fun z => rfl⟩
  obtain ⟨g, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints A hsep
    (fun x : B => φ x) hφ.domRestrict η hη
  obtain ⟨G, hG, hgG⟩ := g.2
  refine ⟨G, hG, fun x hx => ?_⟩
  have := hg ⟨x, hx⟩
  rw [Real.norm_eq_abs] at this
  simpa [hgG] using this

theorem L3_brouwer_ball_vec_approx {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hf : ContinuousOn f (closedBall 0 1)) (δ : ℝ) (hδ : 0 < δ) :
    ∃ G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d), ContDiff ℝ 1 G ∧
      ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, ‖G x - f x‖ < δ := by
  set η : ℝ := δ / (d + 1) with hη_def
  have hd1 : (0 : ℝ) < d + 1 := by positivity
  have hη : 0 < η := div_pos hδ hd1
  have hcoord : ∀ i : Fin d, ∃ Gi : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 1 Gi ∧
      ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, |Gi x - f x i| < η := by
    intro i
    refine L3_brouwer_ball_scalar_approx (fun x => f x i) ?_ η hη
    exact (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).continuous.comp_continuousOn hf
  choose Gi hGi hGiapprox using hcoord
  refine ⟨fun x => (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => Gi i x), ?_, ?_⟩
  · exact (EuclideanSpace.equiv (Fin d) ℝ).symm.contDiff.comp (contDiff_pi.2 fun i => hGi i)
  · intro x hx
    set v := (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => Gi i x) - f x with hv
    have hvi : ∀ i, v i = Gi i x - f x i := by
      intro i
      simp [hv]
    have hsq : ‖v‖ ^ 2 ≤ d * η ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      calc ∑ i, (v i) ^ 2 ≤ ∑ _i : Fin d, η ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            rw [hvi i]
            have := hGiapprox i x hx
            rw [← sq_abs]
            have h0 : 0 ≤ |Gi i x - f x i| := abs_nonneg _
            nlinarith
        _ = d * η ^ 2 := by simp
    have hlt : ‖v‖ ^ 2 < δ ^ 2 := by
      have hδη : δ = (d + 1) * η := by rw [hη_def]; field_simp
      rw [hδη]
      have : (d : ℝ) * η ^ 2 < ((d : ℝ) + 1) ^ 2 * η ^ 2 := by
        have hdd : (d : ℝ) < ((d : ℝ) + 1) ^ 2 := by nlinarith
        have := pow_pos hη 2
        nlinarith
      nlinarith
    have hn : 0 ≤ ‖v‖ := norm_nonneg _
    nlinarith

/-- (L3) Brouwer for continuous self-maps of the closed unit ball. -/
theorem L3_brouwer_ball {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hf : ContinuousOn f (closedBall 0 1)) (hmaps : MapsTo f (closedBall 0 1) (closedBall 0 1)) :
    ∃ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, f x = x := by
  by_contra hno
  push Not at hno
  -- Step 1: minimal displacement
  have hcpt : IsCompact (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) := isCompact_closedBall 0 1
  have hne : (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).Nonempty :=
    ⟨0, mem_closedBall_self zero_le_one⟩
  have hcont : ContinuousOn (fun x => ‖f x - x‖) (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    (hf.sub continuousOn_id).norm
  obtain ⟨x₀, hx₀, hmin⟩ := hcpt.exists_isMinOn hne hcont
  set ε : ℝ := ‖f x₀ - x₀‖ with hε_def
  have hε : 0 < ε := norm_pos_iff.2 (sub_ne_zero.2 (hno x₀ hx₀))
  have hεle : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, ε ≤ ‖f x - x‖ :=
    fun x hx => hmin hx
  -- Step 2: smooth approximation
  set η : ℝ := ε / 2 with hη_def
  have hη : 0 < η := half_pos hε
  obtain ⟨G, hG, hGapprox⟩ := L3_brouwer_ball_vec_approx f hf η hη
  -- Step 3: rescale
  set c : ℝ := 1 + η with hc_def
  have hc : 0 < c := by positivity
  set g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun x => c⁻¹ • G x with hg_def
  have hgC1 : ContDiff ℝ 1 g := hG.const_smul c⁻¹
  have hGnorm : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, ‖G x‖ ≤ c := by
    intro x hx
    have h1 : ‖f x‖ ≤ 1 := by simpa using hmaps hx
    have h2 := hGapprox x hx
    calc ‖G x‖ = ‖(G x - f x) + f x‖ := by rw [sub_add_cancel]
      _ ≤ ‖G x - f x‖ + ‖f x‖ := norm_add_le _ _
      _ ≤ c := by rw [hc_def]; linarith
  have hgmaps : MapsTo g (closedBall 0 1) (closedBall 0 1) := by
    intro x hx
    rw [mem_closedBall_zero_iff, hg_def]
    simp only
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hc)]
    calc c⁻¹ * ‖G x‖ ≤ c⁻¹ * c := by
          exact mul_le_mul_of_nonneg_left (hGnorm x hx) (inv_pos.2 hc).le
      _ = 1 := inv_mul_cancel₀ hc.ne'
  have hgf : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, ‖g x - f x‖ < ε := by
    intro x hx
    have h1 : ‖f x‖ ≤ 1 := by simpa using hmaps hx
    have h2 := hGapprox x hx
    have hkey : c • (g x - f x) = (G x - f x) - η • f x := by
      rw [hg_def]
      simp only
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hc.ne', one_smul, hc_def, add_smul, one_smul]
      abel
    have hnorm : c * ‖g x - f x‖ ≤ ‖G x - f x‖ + η * ‖f x‖ := by
      have := congrArg norm hkey
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc] at this
      rw [this]
      calc ‖(G x - f x) - η • f x‖ ≤ ‖G x - f x‖ + ‖η • f x‖ := norm_sub_le _ _
        _ = ‖G x - f x‖ + η * ‖f x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
    have hc1 : 1 ≤ c := by rw [hc_def]; linarith
    have hn0 : 0 ≤ ‖g x - f x‖ := norm_nonneg _
    have : η * ‖f x‖ ≤ η := by nlinarith
    nlinarith
  obtain ⟨x, hx, hfix⟩ := L2_brouwer_C1 g hgC1 hgmaps
  have h1 := hεle x hx
  have h2 := hgf x hx
  rw [hfix, norm_sub_rev] at h2
  linarith

/-- Nearest-point retraction onto a nonempty complete convex set in a real inner product space. -/
theorem L4_retraction {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {K : Set F} (hne : K.Nonempty) (hc : IsComplete K) (hconv : Convex ℝ K) :
    ∃ p : F → F, Continuous p ∧ (∀ x, p x ∈ K) ∧ (∀ x ∈ K, p x = x) := by
  choose p hpK hpeq using exists_norm_eq_iInf_of_complete_convex hne hc hconv
  have hin : ∀ x, ∀ w ∈ K, inner ℝ (x - p x) (w - p x) ≤ 0 := fun x =>
    (norm_eq_iInf_iff_real_inner_le_zero hconv (hpK x)).1 (hpeq x)
  refine ⟨p, ?_, hpK, ?_⟩
  · have hlip : LipschitzWith 1 p := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      simp only [NNReal.coe_one, one_mul, dist_eq_norm]
      have h1 := hin x (p y) (hpK y)
      have h2 := hin y (p x) (hpK x)
      have key : ‖p x - p y‖ ^ 2 ≤ inner ℝ (x - y) (p x - p y) := by
        have e : inner ℝ (x - y) (p x - p y) - ‖p x - p y‖ ^ 2 =
            -inner ℝ (x - p x) (p y - p x) - inner ℝ (y - p y) (p x - p y) := by
          rw [← real_inner_self_eq_norm_sq]
          simp only [inner_sub_left, inner_sub_right, real_inner_comm]
          ring
        linarith
      have hcs := real_inner_le_norm (x - y) (p x - p y)
      rcases eq_or_lt_of_le (norm_nonneg (p x - p y)) with h | h
      · rw [← h]; exact norm_nonneg _
      · nlinarith
    exact hlip.continuous
  · intro x hx
    have h0 : ‖x - p x‖ ^ 2 ≤ 0 := by
      rw [← real_inner_self_eq_norm_sq]; exact hin x x hx
    have h1 : ‖x - p x‖ = 0 := by nlinarith [norm_nonneg (x - p x)]
    exact (norm_sub_eq_zero_iff.1 h1).symm

/-- Brouwer for compact convex nonempty subsets of `EuclideanSpace ℝ (Fin d)`. -/
theorem L4_brouwer_euclid {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))} (hKconv : Convex ℝ K)
    (hKcpt : IsCompact K) (hKne : K.Nonempty)
    (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hf : ContinuousOn f K)
    (hfK : MapsTo f K K) : ∃ x ∈ K, f x = x := by
  obtain ⟨p, hpc, hpK, hpid⟩ := L4_retraction hKne hKcpt.isComplete hKconv
  obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hKcpt.isBounded
  set R : ℝ := max R₀ 1 with hR
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hKR : K ⊆ closedBall 0 R := hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  let g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun z => R⁻¹ • f (p (R • z))
  have hgc : ContinuousOn g (closedBall 0 1) := by
    have hc : ContinuousOn (fun z => f (p (R • z))) univ :=
      hf.comp (hpc.comp (continuous_const_smul R)).continuousOn (fun z _ => hpK _)
    exact (hc.mono (subset_univ _)).const_smul R⁻¹
  have hgm : MapsTo g (closedBall 0 1) (closedBall 0 1) := by
    intro z _
    have h1 := hKR (hfK (hpK (R • z)))
    rw [mem_closedBall_zero_iff] at h1 ⊢
    simp only [g, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hRpos]
    rw [inv_mul_le_iff₀ hRpos]
    linarith
  obtain ⟨z, -, hz⟩ := L3_brouwer_ball g hgc hgm
  have hx : f (p (R • z)) = R • z := by
    have := congrArg (fun v => R • v) hz
    simpa [g, smul_smul, mul_inv_cancel₀ hRpos.ne'] using this
  have hxK : R • z ∈ K := hx ▸ hfK (hpK _)
  refine ⟨R • z, hxK, ?_⟩
  rw [hpid _ hxK] at hx
  exact hx

end AGT.BrouwerAux

open AGT.BrouwerAux in
/-- (L4) The target statement. -/
theorem brouwer_fp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {K : Set E}
    (hKconv : Convex ℝ K) (hKcpt : IsCompact K) (hKne : K.Nonempty)
    (f : E → E) (hf : ContinuousOn f K) (hfK : Set.MapsTo f K K) :
    ∃ x ∈ K, f x = x := by
  classical
  let φ : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  have hconv' : Convex ℝ (φ '' K) :=
    hKconv.linear_image (φ : E →ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
  have hcont : ContinuousOn (φ ∘ f ∘ φ.symm) (φ '' K) := by
    refine φ.continuous.comp_continuousOn (hf.comp φ.symm.continuous.continuousOn ?_)
    rintro _ ⟨y, hy, rfl⟩
    simpa using hy
  have hmaps : MapsTo (φ ∘ f ∘ φ.symm) (φ '' K) (φ '' K) := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨f y, hfK hy, by simp⟩
  obtain ⟨x, ⟨y, hyK, rfl⟩, hx⟩ :=
    L4_brouwer_euclid hconv' (hKcpt.image φ.continuous) (hKne.image φ) _ hcont hmaps
  refine ⟨y, hyK, ?_⟩
  apply φ.injective
  simpa using hx

end BrouwerSec

open MultPacing.Existence

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace MPX

variable {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G]

lemma le_topBid (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (j : G) (k : Option N) :
    smBid P ε α j k ≤ topBid P ε α j :=
  Finset.le_sup' (smBid P ε α j) (Finset.mem_univ k)

lemma exists_top (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (j : G) :
    ∃ k, topBid P ε α j = smBid P ε α j k := by
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (smBid P ε α j)
  exact ⟨k, hk⟩

lemma two_eps_le_topBid (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (j : G) :
    2 * ε ≤ topBid P ε α j := le_topBid P ε α j none

lemma bandWeight_nonneg (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (j : G) (k : Option N) :
    0 ≤ bandWeight P ε α j k := le_max_left _ _

lemma eps_le_denom (P : PacingGame N G) (ε : ℝ) (hε : 0 < ε) (α : N → ℝ) (j : G) :
    ε ≤ ∑ k : Option N, bandWeight P ε α j k := by
  obtain ⟨k, hk⟩ := exists_top P ε α j
  have h1 : bandWeight P ε α j k = ε := by
    unfold bandWeight; rw [hk]; simp [hε.le]
  calc ε = bandWeight P ε α j k := h1.symm
    _ ≤ _ := Finset.single_le_sum (fun k _ => bandWeight_nonneg P ε α j k) (Finset.mem_univ k)

lemma denom_pos (P : PacingGame N G) (ε : ℝ) (hε : 0 < ε) (α : N → ℝ) (j : G) :
    0 < ∑ k : Option N, bandWeight P ε α j k := lt_of_lt_of_le hε (eps_le_denom P ε hε α j)

lemma smAlloc_nonneg (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (i : N) (j : G) :
    0 ≤ smAlloc P ε α i j :=
  div_nonneg (bandWeight_nonneg _ _ _ _ _) (Finset.sum_nonneg fun k _ => bandWeight_nonneg _ _ _ _ _)

lemma sum_smAlloc_le (P : PacingGame N G) (ε : ℝ) (hε : 0 < ε) (α : N → ℝ) (j : G) :
    ∑ i, smAlloc P ε α i j ≤ 1 := by
  unfold smAlloc
  rw [← Finset.sum_div, div_le_one (denom_pos P ε hε α j), Fintype.sum_option]
  linarith [bandWeight_nonneg P ε α j none]

lemma smAlloc_le_one (P : PacingGame N G) (ε : ℝ) (hε : 0 < ε) (α : N → ℝ) (i : N) (j : G) :
    smAlloc P ε α i j ≤ 1 := by
  calc smAlloc P ε α i j ≤ ∑ i, smAlloc P ε α i j :=
        Finset.single_le_sum (fun k _ => smAlloc_nonneg P ε α k j) (Finset.mem_univ i)
    _ ≤ 1 := sum_smAlloc_le P ε hε α j

lemma smPrice_add (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (i : N) (j : G) :
    smPrice P ε α i j + ε = (Finset.univ.erase (some i)).sup' ⟨none, by simp⟩ (smBid P ε α j) := by
  unfold smPrice; ring

lemma eps_le_smPrice (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (i : N) (j : G) :
    ε ≤ smPrice P ε α i j := by
  have : smBid P ε α j none ≤ (Finset.univ.erase (some i)).sup' ⟨none, by simp⟩ (smBid P ε α j) :=
    Finset.le_sup' (smBid P ε α j) (by simp)
  have h2 := smPrice_add P ε α i j
  simp [smBid] at this
  linarith

lemma topBid_eq (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (i : N) (j : G) :
    topBid P ε α j = max (α i * P.v i j) (smPrice P ε α i j + ε) := by
  rw [smPrice_add]
  apply le_antisymm
  · apply Finset.sup'_le
    intro k _
    by_cases hk : k = some i
    · subst hk; exact le_max_of_le_left (le_refl _)
    · exact le_max_of_le_right (Finset.le_sup' (smBid P ε α j) (by simp [hk]))
  · apply max_le
    · exact le_topBid P ε α j (some i)
    · exact Finset.sup'_mono _ (Finset.subset_univ _) _

lemma smPrice_update (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (i : N) (a : ℝ) (j : G) :
    smPrice P ε (Function.update α i a) i j = smPrice P ε α i j := by
  unfold smPrice
  congr 1
  apply Finset.sup'_congr _ rfl
  intro k hk
  rcases k with _ | k
  · rfl
  · have : k ≠ i := by rintro rfl; simp at hk
    simp [smBid, Function.update_of_ne this]

lemma budgetTerm_eq (H y : ℝ) : budgetTerm H y = max y 0 + H * min y 0 := by
  unfold budgetTerm
  split_ifs with h
  · simp [h]
  · push Not at h; simp [h.le]

/-! Continuity -/

lemma smBid_cont (P : PacingGame N G) (ε : ℝ) (j : G) (k : Option N) :
    Continuous (fun α : N → ℝ => smBid P ε α j k) := by
  rcases k with _ | k
  · exact continuous_const
  · exact (continuous_apply k).mul continuous_const

lemma topBid_cont (P : PacingGame N G) (ε : ℝ) (j : G) :
    Continuous (fun α : N → ℝ => topBid P ε α j) := by
  unfold topBid
  exact Continuous.finset_sup'_apply _ (fun k _ => smBid_cont P ε j k)

lemma bandWeight_cont (P : PacingGame N G) (ε : ℝ) (j : G) (k : Option N) :
    Continuous (fun α : N → ℝ => bandWeight P ε α j k) := by
  unfold bandWeight
  exact continuous_const.max ((smBid_cont P ε j k).sub ((topBid_cont P ε j).sub continuous_const))

lemma smAlloc_cont (P : PacingGame N G) (ε : ℝ) (hε : 0 < ε) (i : N) (j : G) :
    Continuous (fun α : N → ℝ => smAlloc P ε α i j) := by
  unfold smAlloc
  exact (bandWeight_cont P ε j (some i)).div
    (continuous_finsetSum _ fun k _ => bandWeight_cont P ε j k)
    (fun α => (denom_pos P ε hε α j).ne')

lemma smPrice_cont (P : PacingGame N G) (ε : ℝ) (i : N) (j : G) :
    Continuous (fun α : N → ℝ => smPrice P ε α i j) := by
  unfold smPrice
  exact (Continuous.finset_sup'_apply _ (fun k _ => smBid_cont P ε j k)).sub continuous_const

lemma smPay_cont (P : PacingGame N G) (ε : ℝ) (hε : 0 < ε) (i : N) (j : G) :
    Continuous (fun α : N → ℝ => smPay P ε α i j) :=
  (smAlloc_cont P ε hε i j).mul (smPrice_cont P ε i j)

lemma smSpend_cont (P : PacingGame N G) (ε : ℝ) (hε : 0 < ε) (i : N) :
    Continuous (fun α : N → ℝ => smSpend P ε α i) :=
  ((continuous_apply i).mul continuous_const).add
    (continuous_finsetSum _ fun j _ => smPay_cont P ε hε i j)

lemma smUtility_cont (P : PacingGame N G) (ε H : ℝ) (hε : 0 < ε) (i : N) :
    Continuous (fun α : N → ℝ => smUtility P ε H α i) := by
  unfold smUtility
  simp only [budgetTerm_eq]
  have hs := smSpend_cont P ε hε i
  refine ((((continuous_const.sub hs).max continuous_const).add
    (continuous_const.mul ((continuous_const.sub hs).min continuous_const))).add
    ((continuous_const.mul (continuous_apply i)).mul continuous_const)).add
    (continuous_finsetSum _ fun j _ => (smAlloc_cont P ε hε i j).mul continuous_const)

end MPX

namespace MPX

variable {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G]

lemma bid_update_self (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (i : N) (a : ℝ) (j : G) :
    smBid P ε (Function.update α i a) j (some i) = a * P.v i j := by
  simp [smBid]

lemma bid_update_ne (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (i : N) (a : ℝ) (j : G)
    (k : Option N) (hk : k ≠ some i) :
    smBid P ε (Function.update α i a) j k = smBid P ε α j k := by
  rcases k with _ | k
  · rfl
  · have : k ≠ i := by rintro rfl; exact hk rfl
    simp [smBid, Function.update_of_ne this]

lemma topBid_update (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (i : N) (a : ℝ) (j : G) :
    topBid P ε (Function.update α i a) j = max (a * P.v i j) (smPrice P ε α i j + ε) := by
  rw [topBid_eq P ε _ i j, smPrice_update]; simp

lemma alloc_zero_of_lt (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (i : N) (j : G)
    (h : α i * P.v i j < smPrice P ε α i j) : smAlloc P ε α i j = 0 := by
  have hT := topBid_eq P ε α i j
  have hw : bandWeight P ε α j (some i) = 0 := by
    unfold bandWeight
    apply max_eq_left
    simp only [smBid]
    have := le_max_right (α i * P.v i j) (smPrice P ε α i j + ε)
    linarith
  simp [smAlloc, hw]

lemma price_le_bid_of_pos (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (i : N) (j : G)
    (h : 0 < smAlloc P ε α i j) : smPrice P ε α i j ≤ α i * P.v i j := by
  by_contra h'
  push Not at h'
  rw [alloc_zero_of_lt P ε α i j h'] at h
  exact lt_irrefl _ h

/-- monotonicity of the allocation in the own multiplier -/
lemma alloc_mono (P : PacingGame N G) (ε : ℝ) (hε : 0 < ε) (α : N → ℝ) (i : N) (j : G)
    {a1 a2 : ℝ} (h12 : a1 ≤ a2) :
    smAlloc P ε (Function.update α i a1) i j ≤ smAlloc P ε (Function.update α i a2) i j := by
  set α1 := Function.update α i a1
  set α2 := Function.update α i a2
  have hv := P.v_nonneg i j
  have hb : a1 * P.v i j ≤ a2 * P.v i j := mul_le_mul_of_nonneg_right h12 hv
  set m := smPrice P ε α i j + ε
  have hT1 : topBid P ε α1 j = max (a1 * P.v i j) m := topBid_update P ε α i a1 j
  have hT2 : topBid P ε α2 j = max (a2 * P.v i j) m := topBid_update P ε α i a2 j
  have hTle : topBid P ε α1 j ≤ topBid P ε α2 j := by rw [hT1, hT2]; exact max_le_max hb le_rfl
  -- own weights
  have hw : bandWeight P ε α1 j (some i) ≤ bandWeight P ε α2 j (some i) := by
    unfold bandWeight
    rw [hT1, hT2, bid_update_self, bid_update_self]
    apply max_le_max le_rfl
    rcases le_total (a1 * P.v i j) m with h1 | h1 <;>
    rcases le_total (a2 * P.v i j) m with h2 | h2 <;>
    simp only [max_eq_right h1, max_eq_left h1, max_eq_right h2, max_eq_left h2] <;> linarith
  have hk : ∀ k ∈ Finset.univ.erase (some i), bandWeight P ε α2 j k ≤ bandWeight P ε α1 j k := by
    intro k hk
    have hk' : k ≠ some i := Finset.ne_of_mem_erase hk
    unfold bandWeight
    rw [bid_update_ne P ε α i a1 j k hk', bid_update_ne P ε α i a2 j k hk']
    apply max_le_max le_rfl
    linarith
  set w1 := bandWeight P ε α1 j (some i)
  set w2 := bandWeight P ε α2 j (some i)
  set S1 := ∑ k ∈ Finset.univ.erase (some i), bandWeight P ε α1 j k
  set S2 := ∑ k ∈ Finset.univ.erase (some i), bandWeight P ε α2 j k
  have hD1 : ∑ k : Option N, bandWeight P ε α1 j k = w1 + S1 :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ _)).symm
  have hD2 : ∑ k : Option N, bandWeight P ε α2 j k = w2 + S2 :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ _)).symm
  have hS : S2 ≤ S1 := Finset.sum_le_sum hk
  have hS2 : 0 ≤ S2 := Finset.sum_nonneg fun k _ => bandWeight_nonneg _ _ _ _ _
  have hw1 : 0 ≤ w1 := bandWeight_nonneg _ _ _ _ _
  have hp1 := denom_pos P ε hε α1 j
  have hp2 := denom_pos P ε hε α2 j
  unfold smAlloc
  rw [div_le_div_iff₀ hp1 hp2, hD1, hD2]
  rw [hD1] at hp1
  nlinarith [mul_le_mul hw hS hS2 (hw1.trans hw)]

lemma smSpend_update (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (i : N) (a : ℝ) :
    smSpend P ε (Function.update α i a) i =
      a * ε + ∑ j, smAlloc P ε (Function.update α i a) i j * smPrice P ε α i j := by
  unfold smSpend smPay
  simp [smPrice_update]

lemma smUtility_update (P : PacingGame N G) (ε H : ℝ) (α : N → ℝ) (i : N) (a : ℝ) :
    smUtility P ε H (Function.update α i a) i =
      budgetTerm H (P.B i - smSpend P ε (Function.update α i a) i) + 2 * a * ε +
        ∑ j, smAlloc P ε (Function.update α i a) i j * P.v i j := by
  unfold smUtility
  simp

lemma spend_diff (P : PacingGame N G) (ε : ℝ) (hε : 0 < ε) (α : N → ℝ) (i : N)
    {a1 a2 : ℝ} (h12 : a1 ≤ a2) :
    (a2 - a1) * ε + ε * ∑ j, (smAlloc P ε (Function.update α i a2) i j -
        smAlloc P ε (Function.update α i a1) i j) ≤
      smSpend P ε (Function.update α i a2) i - smSpend P ε (Function.update α i a1) i := by
  rw [smSpend_update, smSpend_update, Finset.mul_sum]
  have : ∀ j ∈ Finset.univ, ε * (smAlloc P ε (Function.update α i a2) i j -
        smAlloc P ε (Function.update α i a1) i j) ≤
      smAlloc P ε (Function.update α i a2) i j * smPrice P ε α i j -
        smAlloc P ε (Function.update α i a1) i j * smPrice P ε α i j := by
    intro j _
    have h1 := alloc_mono P ε hε α i j h12
    have h2 := eps_le_smPrice P ε α i j
    nlinarith
  have := Finset.sum_le_sum this
  rw [Finset.sum_sub_distrib] at this
  linarith

lemma alloc_sum_diff_nonneg (P : PacingGame N G) (ε : ℝ) (hε : 0 < ε) (α : N → ℝ) (i : N)
    {a1 a2 : ℝ} (h12 : a1 ≤ a2) :
    0 ≤ ∑ j, (smAlloc P ε (Function.update α i a2) i j - smAlloc P ε (Function.update α i a1) i j) :=
  Finset.sum_nonneg fun j _ => sub_nonneg.2 (alloc_mono P ε hε α i j h12)

lemma spend_strictMono (P : PacingGame N G) (ε : ℝ) (hε : 0 < ε) (α : N → ℝ) (i : N)
    {a1 a2 : ℝ} (h12 : a1 < a2) :
    smSpend P ε (Function.update α i a1) i < smSpend P ε (Function.update α i a2) i := by
  have h1 := spend_diff P ε hε α i h12.le
  have h2 := alloc_sum_diff_nonneg P ε hε α i h12.le
  nlinarith

lemma util_strictMono_low (P : PacingGame N G) (ε H : ℝ) (hε : 0 < ε) (α : N → ℝ) (i : N)
    {a1 a2 : ℝ} (ha1 : 0 ≤ a1) (ha2 : a2 ≤ 1) (h12 : a1 < a2)
    (hs1 : smSpend P ε (Function.update α i a1) i ≤ P.B i)
    (hs2 : smSpend P ε (Function.update α i a2) i ≤ P.B i) :
    smUtility P ε H (Function.update α i a1) i < smUtility P ε H (Function.update α i a2) i := by
  rw [smUtility_update, smUtility_update]
  unfold budgetTerm
  rw [if_pos (by linarith), if_pos (by linarith)]
  rw [smSpend_update, smSpend_update]
  have key : ∀ j ∈ Finset.univ,
      smAlloc P ε (Function.update α i a1) i j * P.v i j -
        smAlloc P ε (Function.update α i a1) i j * smPrice P ε α i j ≤
      smAlloc P ε (Function.update α i a2) i j * P.v i j -
        smAlloc P ε (Function.update α i a2) i j * smPrice P ε α i j := by
    intro j _
    have hv := P.v_nonneg i j
    rcases lt_or_ge (P.v i j) (smPrice P ε α i j) with h | h
    · have e1 : smAlloc P ε (Function.update α i a1) i j = 0 := by
        apply alloc_zero_of_lt
        simp only [Function.update_self, smPrice_update]
        nlinarith
      have e2 : smAlloc P ε (Function.update α i a2) i j = 0 := by
        apply alloc_zero_of_lt
        simp only [Function.update_self, smPrice_update]
        nlinarith
      rw [e1, e2]
    · have := alloc_mono P ε hε α i j h12.le
      nlinarith
  have := Finset.sum_le_sum key
  simp only [Finset.sum_sub_distrib] at this
  nlinarith

lemma util_strictAnti_high (P : PacingGame N G) (ε H M : ℝ) (hε : 0 < ε) (α : N → ℝ) (i : N)
    (hM : ∑ j, P.v i j + 2 * ε ≤ M) (hH : M / ε < H)
    {a1 a2 : ℝ} (h12 : a1 < a2)
    (hs1 : P.B i ≤ smSpend P ε (Function.update α i a1) i)
    (hs2 : P.B i ≤ smSpend P ε (Function.update α i a2) i) :
    smUtility P ε H (Function.update α i a2) i < smUtility P ε H (Function.update α i a1) i := by
  rw [smUtility_update, smUtility_update]
  have hbt : ∀ y ≤ (0:ℝ), budgetTerm H y = H * y := by
    intro y hy; unfold budgetTerm; split_ifs with h
    · have : y = 0 := le_antisymm hy h
      subst this; simp
    · rfl
  rw [hbt _ (by linarith), hbt _ (by linarith)]
  have hsumv : ∀ j, P.v i j ≤ M := by
    intro j
    have : P.v i j ≤ ∑ j, P.v i j :=
      Finset.single_le_sum (fun k _ => P.v_nonneg i k) (Finset.mem_univ j)
    linarith
  have hHe : M < H * ε := by rwa [div_lt_iff₀ hε] at hH
  have hM0 : 0 < M := by
    have : 0 ≤ ∑ j, P.v i j := Finset.sum_nonneg fun k _ => P.v_nonneg i k
    linarith
  have hH0 : 0 < H := by
    have : 0 < M / ε := div_pos hM0 hε
    linarith
  have hT := alloc_sum_diff_nonneg P ε hε α i h12.le
  have hsd := spend_diff P ε hε α i h12.le
  set T := ∑ j, (smAlloc P ε (Function.update α i a2) i j - smAlloc P ε (Function.update α i a1) i j)
  have hv : ∑ j, smAlloc P ε (Function.update α i a2) i j * P.v i j -
      ∑ j, smAlloc P ε (Function.update α i a1) i j * P.v i j ≤ M * T := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have := alloc_mono P ε hε α i j h12.le
    have := hsumv j
    have := P.v_nonneg i j
    nlinarith
  have hspos : 0 < (a2 - a1) + T := by linarith
  have e1 := mul_le_mul_of_nonneg_left hsd hH0.le
  have e2 := mul_lt_mul_of_pos_right hHe hspos
  have h2e : 2 * ε ≤ M := by
    have : 0 ≤ ∑ j, P.v i j := Finset.sum_nonneg fun k _ => P.v_nonneg i k
    linarith
  have e3 : 2 * ε * (a2 - a1) ≤ M * (a2 - a1) := mul_le_mul_of_nonneg_right h2e (by linarith)
  nlinarith

end MPX

namespace MPX

variable {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G]

lemma spend_zero (P : PacingGame N G) (ε : ℝ) (hε : 0 < ε) (α : N → ℝ) (i : N) :
    smSpend P ε (Function.update α i 0) i = 0 := by
  rw [smSpend_update]
  have : ∀ j, smAlloc P ε (Function.update α i 0) i j = 0 := by
    intro j
    apply alloc_zero_of_lt
    simp only [Function.update_self, smPrice_update, zero_mul]
    linarith [eps_le_smPrice P ε α i j]
  simp [this]

lemma spend_at_zero (P : PacingGame N G) (ε : ℝ) (hε : 0 < ε) (α : N → ℝ) (i : N)
    (h : α i = 0) : smSpend P ε α i = 0 := by
  calc smSpend P ε α i = smSpend P ε (Function.update α i 0) i := by
        rw [← h, Function.update_eq_self]
    _ = 0 := spend_zero P ε hε α i

lemma pne_of_cond (P : PacingGame N G) (ε H M : ℝ) (hε : 0 < ε)
    (hM : ∀ i, ∑ j, P.v i j + 2 * ε ≤ M) (hH : M / ε < H) (α : N → ℝ)
    (hα : ∀ i, α i ∈ Set.Icc (0 : ℝ) 1)
    (hc : ∀ i, smSpend P ε α i ≤ P.B i ∧ (α i < 1 → smSpend P ε α i = P.B i)) :
    IsSmoothedPNE P ε H α := by
  refine ⟨hα, fun i a ha => ?_⟩
  have e : Function.update α i (α i) = α := Function.update_eq_self i α
  rcases lt_trichotomy a (α i) with h | h | h
  · have hs := spend_strictMono P ε hε α i h
    rw [e] at hs
    have := util_strictMono_low P ε H hε α i ha.1 (hα i).2 h (by linarith [(hc i).1])
      (by rw [e]; exact (hc i).1)
    rw [e] at this
    exact this.le
  · rw [h, e]
  · have hs := spend_strictMono P ε hε α i h
    rw [e] at hs
    have hlt : α i < 1 := lt_of_lt_of_le h ha.2
    have hB := (hc i).2 hlt
    have := util_strictAnti_high P ε H M hε α i (hM i) hH h (by rw [e]; exact hB.ge)
      (by linarith)
    rw [e] at this
    exact this.le

lemma cond_of_pne (P : PacingGame N G) (ε H M : ℝ) (hε : 0 < ε)
    (hM : ∀ i, ∑ j, P.v i j + 2 * ε ≤ M) (hH : M / ε < H) (α : N → ℝ)
    (hpne : IsSmoothedPNE P ε H α) (i : N) :
    smSpend P ε α i ≤ P.B i ∧ (α i < 1 → smSpend P ε α i = P.B i) := by
  obtain ⟨hα, hbest⟩ := hpne
  have e : Function.update α i (α i) = α := Function.update_eq_self i α
  have hB := P.B_pos i
  set S : ℝ → ℝ := fun a => smSpend P ε (Function.update α i a) i with hS
  have hS0 : S 0 = 0 := spend_zero P ε hε α i
  have hSα : S (α i) = smSpend P ε α i := by simp [hS]
  have hcont : ContinuousOn S (Set.Icc 0 1) :=
    ((smSpend_cont P ε hε i).comp (continuous_const.update i continuous_id)).continuousOn
  have hai := hα i
  rcases le_or_gt (S 1) (P.B i) with h1 | h1
  · -- spend at 1 within budget: α i = 1
    have hall : ∀ a ∈ Set.Icc (0:ℝ) 1, S a ≤ P.B i := by
      intro a ha
      rcases eq_or_lt_of_le ha.2 with h | h
      · rw [h]; exact h1
      · exact (spend_strictMono P ε hε α i h).le.trans h1
    have hα1 : α i = 1 := by
      by_contra hne
      have hlt : α i < 1 := lt_of_le_of_ne hai.2 hne
      have := util_strictMono_low P ε H hε α i hai.1 le_rfl hlt (hall _ hai)
        (hall 1 ⟨zero_le_one, le_rfl⟩)
      rw [e] at this
      linarith [hbest i 1 ⟨zero_le_one, le_rfl⟩]
    refine ⟨?_, fun h => absurd hα1 h.ne⟩
    rw [← hSα]; exact hall _ hai
  · obtain ⟨c, hc, hSc⟩ : ∃ c ∈ Set.Icc (0:ℝ) 1, S c = P.B i :=
      intermediate_value_Icc zero_le_one hcont ⟨by rw [hS0]; exact hB.le, h1.le⟩
    have hαc : α i = c := by
      rcases lt_trichotomy (α i) c with h | h | h
      · have hs := spend_strictMono P ε hε α i h
        have := util_strictMono_low P ε H hε α i hai.1 hc.2 h (by
          have : S (α i) < S c := hs
          linarith) hSc.le
        rw [e] at this
        linarith [hbest i c hc]
      · exact h
      · have hs := spend_strictMono P ε hε α i h
        have := util_strictAnti_high P ε H M hε α i (hM i) hH h hSc.ge (by
          have : S c < S (α i) := hs
          linarith)
        rw [e] at this
        linarith [hbest i c hc]
    have : smSpend P ε α i = P.B i := by rw [← hSα, hαc, hSc]
    exact ⟨this.le, fun _ => this⟩

end MPX

namespace MPX

variable {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G]

/-- the clamped spend-adjustment map -/
noncomputable def fpMap (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) : N → ℝ :=
  fun i => max 0 (min 1 (α i + (P.B i - smSpend P ε α i)))

lemma exists_pne (P : PacingGame N G) (ε H M : ℝ) (hε : 0 < ε)
    (hM : ∀ i, ∑ j, P.v i j + 2 * ε ≤ M) (hH : M / ε < H) :
    ∃ α : N → ℝ, IsSmoothedPNE P ε H α := by
  set K : Set (N → ℝ) := Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1 with hK
  have hconv : Convex ℝ K := convex_pi fun _ _ => convex_Icc 0 1
  have hcpt : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
  have hne : K.Nonempty := ⟨0, fun i _ => ⟨le_rfl, zero_le_one⟩⟩
  have hcont : Continuous (fpMap P ε) := by
    apply continuous_pi
    intro i
    exact continuous_const.max (continuous_const.min ((continuous_apply i).add
      (continuous_const.sub (smSpend_cont P ε hε i))))
  have hmaps : Set.MapsTo (fpMap P ε) K K := by
    intro α _
    simp only [hK, Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_true_left, fpMap]
    intro i
    exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  obtain ⟨α, hαK, hfix⟩ := brouwer_fp hconv hcpt hne (fpMap P ε) hcont.continuousOn hmaps
  have hα : ∀ i, α i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i; simpa [hK] using hαK i (Set.mem_univ i)
  refine ⟨α, pne_of_cond P ε H M hε hM hH α hα fun i => ?_⟩
  have hfi : max 0 (min 1 (α i + (P.B i - smSpend P ε α i))) = α i := congrFun hfix i
  have hB := P.B_pos i
  have h1 : smSpend P ε α i ≤ P.B i := by
    by_contra hlt
    push Not at hlt
    have ht : α i + (P.B i - smSpend P ε α i) < α i := by linarith
    have hmin : min 1 (α i + (P.B i - smSpend P ε α i)) = α i + (P.B i - smSpend P ε α i) :=
      min_eq_right (by linarith [(hα i).2])
    rw [hmin] at hfi
    rcases le_total 0 (α i + (P.B i - smSpend P ε α i)) with h | h
    · rw [max_eq_right h] at hfi; linarith
    · rw [max_eq_left h] at hfi
      have := spend_at_zero P ε hε α i hfi.symm
      linarith
  refine ⟨h1, fun hlt => ?_⟩
  by_contra hne'
  have hs : smSpend P ε α i < P.B i := lt_of_le_of_ne h1 hne'
  have : α i < min 1 (α i + (P.B i - smSpend P ε α i)) := lt_min hlt (by linarith)
  have : α i < max 0 (min 1 (α i + (P.B i - smSpend P ε α i))) := lt_of_lt_of_le this (le_max_right _ _)
  linarith

end MPX


namespace MPX

open Filter Topology

variable {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G]

section Lim

variable {P : PacingGame N G} {ε H : ℕ → ℝ} {M : ℝ} {α : ℕ → N → ℝ} {αs : N → ℝ}
  {xs ps ss : N → G → ℝ}

lemma L_alpha_mem (hlim : IsSmoothedLimit P ε H M α αs xs ps ss) (l : ℕ) (i : N) :
    α l i ∈ Set.Icc (0 : ℝ) 1 := (hlim.equilibrium l).1 i

lemma L_alpha_tendsto (hlim : IsSmoothedLimit P ε H M α αs xs ps ss) (i : N) :
    Tendsto (fun l => α l i) atTop (𝓝 (αs i)) := tendsto_pi_nhds.1 hlim.alpha_tendsto i

lemma L_alphas_mem (hlim : IsSmoothedLimit P ε H M α αs xs ps ss) (i : N) :
    αs i ∈ Set.Icc (0 : ℝ) 1 :=
  isClosed_Icc.mem_of_tendsto (L_alpha_tendsto hlim i) (Eventually.of_forall fun l => L_alpha_mem hlim l i)

lemma L_xs_mem (hlim : IsSmoothedLimit P ε H M α αs xs ps ss) (i : N) (j : G) :
    xs i j ∈ Set.Icc (0 : ℝ) 1 :=
  isClosed_Icc.mem_of_tendsto (hlim.alloc_tendsto i j) (Eventually.of_forall fun l =>
    ⟨smAlloc_nonneg _ _ _ _ _, smAlloc_le_one _ _ (hlim.eps_pos l) _ _ _⟩)

lemma L_cond (hlim : IsSmoothedLimit P ε H M α αs xs ps ss) (l : ℕ) (i : N) :
    smSpend P (ε l) (α l) i ≤ P.B i ∧ (α l i < 1 → smSpend P (ε l) (α l) i = P.B i) :=
  cond_of_pne P (ε l) (H l) M (hlim.eps_pos l) (hlim.M_bound l) (hlim.H_gt l) (α l)
    (hlim.equilibrium l) i

end Lim

/-- joint continuity of the price in `(ε, α)` -/
lemma smPrice_cont2 (P : PacingGame N G) (i : N) (j : G) :
    Continuous (fun p : ℝ × (N → ℝ) => smPrice P p.1 p.2 i j) := by
  unfold smPrice
  refine (Continuous.finset_sup'_apply _ (fun k _ => ?_)).sub continuous_fst
  rcases k with _ | k
  · exact continuous_const.mul continuous_fst
  · exact ((continuous_apply k).comp continuous_snd).mul continuous_const

lemma smPrice_zero_eq (P : PacingGame N G) (α : N → ℝ) (hα : ∀ k, 0 ≤ α k) (i : N) (j : G) :
    smPrice P 0 α i j = highestOther P.v α i j := by
  unfold smPrice highestOther
  rw [sub_zero]
  have hb : ∀ k, 0 ≤ smBid P 0 α j k := by
    intro k; rcases k with _ | k
    · simp [smBid]
    · exact mul_nonneg (hα k) (P.v_nonneg k j)
  split_ifs with h
  · apply le_antisymm
    · apply Finset.sup'_le
      intro k hk
      rcases k with _ | k
      · simp only [smBid, mul_zero]
        obtain ⟨k0, hk0⟩ := h
        exact le_trans (mul_nonneg (hα k0) (P.v_nonneg k0 j))
          (Finset.le_sup' (fun k => α k * P.v k j) hk0)
      · have : k ≠ i := by rintro rfl; simp at hk
        exact Finset.le_sup' (fun k => α k * P.v k j) (by simp [this])
    · apply Finset.sup'_le
      intro k hk
      have : k ≠ i := Finset.ne_of_mem_erase hk
      exact Finset.le_sup' (smBid P 0 α j) (b := some k) (by simp [this])
  · apply le_antisymm
    · apply Finset.sup'_le
      intro k hk
      rcases k with _ | k
      · simp [smBid]
      · have : k ≠ i := by rintro rfl; simp at hk
        exact absurd ⟨k, by simp [this]⟩ h
    · exact le_trans (hb none) (Finset.le_sup' _ (by simp))

section Lim2

variable {P : PacingGame N G} {ε H : ℕ → ℝ} {M : ℝ} {α : ℕ → N → ℝ} {αs : N → ℝ}
  {xs ps ss : N → G → ℝ}

lemma L_price (hlim : IsSmoothedLimit P ε H M α αs xs ps ss) (i : N) (j : G) :
    ps i j = highestOther P.v αs i j := by
  have ht : Tendsto (fun l => (ε l, α l)) atTop (𝓝 ((0 : ℝ), αs)) :=
    hlim.eps_tendsto.prodMk_nhds hlim.alpha_tendsto
  have h2 := ((smPrice_cont2 P i j).tendsto _).comp ht
  have := tendsto_nhds_unique (hlim.price_tendsto i j) h2
  rw [this]
  exact smPrice_zero_eq P αs (fun k => (L_alphas_mem hlim k).1) i j

lemma L_pay (hlim : IsSmoothedLimit P ε H M α αs xs ps ss) (i : N) (j : G) :
    ss i j = xs i j * ps i j :=
  tendsto_nhds_unique (hlim.pay_tendsto i j)
    ((hlim.alloc_tendsto i j).mul (hlim.price_tendsto i j))

lemma L_budget (hlim : IsSmoothedLimit P ε H M α αs xs ps ss) (i : N) :
    ∑ j, ss i j ≤ P.B i := by
  have ht : Tendsto (fun l => ∑ j, smPay P (ε l) (α l) i j) atTop (𝓝 (∑ j, ss i j)) :=
    tendsto_finsetSum _ fun j _ => hlim.pay_tendsto i j
  refine le_of_tendsto' ht fun l => ?_
  have h1 := (L_cond hlim l i).1
  unfold smSpend at h1
  have := mul_nonneg (L_alpha_mem hlim l i).1 (hlim.eps_pos l).le
  linarith

lemma L_spend_all (hlim : IsSmoothedLimit P ε H M α αs xs ps ss) (i : N) (hi : αs i < 1) :
    ∑ j, ss i j = P.B i := by
  have ht : Tendsto (fun l => ∑ j, smPay P (ε l) (α l) i j) atTop (𝓝 (∑ j, ss i j)) :=
    tendsto_finsetSum _ fun j _ => hlim.pay_tendsto i j
  have hev : ∀ᶠ l in atTop, α l i < 1 := (L_alpha_tendsto hlim i).eventually (gt_mem_nhds hi)
  have ht2 : Tendsto (fun l => P.B i - α l i * ε l) atTop (𝓝 (P.B i - αs i * 0)) :=
    tendsto_const_nhds.sub ((L_alpha_tendsto hlim i).mul hlim.eps_tendsto)
  rw [mul_zero, sub_zero] at ht2
  refine tendsto_nhds_unique ht (ht2.congr' ?_)
  filter_upwards [hev] with l hl
  have := (L_cond hlim l i).2 hl
  unfold smSpend at this
  linarith

lemma L_supply (hlim : IsSmoothedLimit P ε H M α αs xs ps ss) (j : G) :
    ∑ i, xs i j ≤ 1 :=
  le_of_tendsto' (tendsto_finsetSum _ fun i _ => hlim.alloc_tendsto i j)
    fun l => sum_smAlloc_le P (ε l) (hlim.eps_pos l) (α l) j

lemma bid_lt_of_alloc_pos (P : PacingGame N G) (e : ℝ) (a : N → ℝ) (i : N) (j : G)
    (h : 0 < smAlloc P e a i j) (k : Option N) :
    smBid P e a j k < a i * P.v i j + e := by
  have hw : 0 < bandWeight P e a j (some i) := by
    by_contra hw
    push Not at hw
    have : bandWeight P e a j (some i) = 0 := le_antisymm hw (bandWeight_nonneg _ _ _ _ _)
    simp [smAlloc, this] at h
  unfold bandWeight at hw
  have hT := le_topBid P e a j k
  rcases le_total 0 (smBid P e a j (some i) - (topBid P e a j - e)) with h' | h'
  · rw [max_eq_right h'] at hw; simp only [smBid] at hw; linarith
  · rw [max_eq_left h'] at hw; exact absurd hw (lt_irrefl _)

lemma L_winner (hlim : IsSmoothedLimit P ε H M α αs xs ps ss) (i : N) (j : G)
    (hx : 0 < xs i j) (k : N) : αs k * P.v k j ≤ αs i * P.v i j := by
  have hev : ∀ᶠ l in atTop, 0 < smAlloc P (ε l) (α l) i j :=
    (hlim.alloc_tendsto i j).eventually (lt_mem_nhds hx)
  have h1 : Tendsto (fun l => α l k * P.v k j) atTop (𝓝 (αs k * P.v k j)) :=
    (L_alpha_tendsto hlim k).mul_const _
  have h2 : Tendsto (fun l => α l i * P.v i j + ε l) atTop (𝓝 (αs i * P.v i j + 0)) :=
    ((L_alpha_tendsto hlim i).mul_const _).add hlim.eps_tendsto
  rw [add_zero] at h2
  refine le_of_tendsto_of_tendsto h1 h2 ?_
  filter_upwards [hev] with l hl
  exact (bid_lt_of_alloc_pos P (ε l) (α l) i j hl (some k)).le

lemma pay_le_bid (P : PacingGame N G) (e : ℝ) (he : 0 < e) (a : N → ℝ) (i : N) (ha : 0 ≤ a i)
    (j : G) : smPay P e a i j ≤ a i * P.v i j := by
  unfold smPay
  have hb : 0 ≤ a i * P.v i j := mul_nonneg ha (P.v_nonneg i j)
  rcases eq_or_lt_of_le (smAlloc_nonneg P e a i j) with h | h
  · rw [← h, zero_mul]; exact hb
  · have hp := price_le_bid_of_pos P e a i j h
    have h1 := smAlloc_le_one P e he a i j
    have hp0 := eps_le_smPrice P e a i j
    calc smAlloc P e a i j * smPrice P e a i j ≤ 1 * smPrice P e a i j :=
          mul_le_mul_of_nonneg_right h1 (by linarith)
      _ ≤ a i * P.v i j := by linarith

lemma spend_le (P : PacingGame N G) (e M : ℝ) (he : 0 < e) (a : N → ℝ) (i : N) (ha : 0 ≤ a i)
    (hM : ∑ j, P.v i j + 2 * e ≤ M) : smSpend P e a i ≤ a i * M := by
  unfold smSpend
  have h1 : ∑ j, smPay P e a i j ≤ ∑ j, a i * P.v i j :=
    Finset.sum_le_sum fun j _ => pay_le_bid P e he a i ha j
  rw [← Finset.mul_sum] at h1
  have : a i * (e + ∑ j, P.v i j) ≤ a i * M := mul_le_mul_of_nonneg_left (by linarith) ha
  nlinarith

lemma L_alpha_lb (hlim : IsSmoothedLimit P ε H M α αs xs ps ss) (l : ℕ) (i : N) :
    min 1 (P.B i / M) ≤ α l i := by
  have hM := hlim.M_bound l i
  have he := hlim.eps_pos l
  have hM0 : 0 < M := by
    have : 0 ≤ ∑ j, P.v i j := Finset.sum_nonneg fun k _ => P.v_nonneg i k
    linarith
  rcases eq_or_lt_of_le (L_alpha_mem hlim l i).2 with h | h
  · rw [h]; exact min_le_left _ _
  · have hs := (L_cond hlim l i).2 h
    have := spend_le P (ε l) M he (α l) i (L_alpha_mem hlim l i).1 hM
    refine (min_le_right _ _).trans ?_
    rw [div_le_iff₀ hM0]; linarith

lemma L_full (hlim : IsSmoothedLimit P ε H M α αs xs ps ss) (j : G) (hj : ∃ i, 0 < P.v i j) :
    ∑ i, xs i j = 1 := by
  obtain ⟨i, hi⟩ := hj
  have hM0 : 0 < M := by
    have := hlim.M_bound 0 i
    have : 0 ≤ ∑ j, P.v i j := Finset.sum_nonneg fun k _ => P.v_nonneg i k
    linarith [hlim.eps_pos 0]
  have hc : 0 < min 1 (P.B i / M) := lt_min one_pos (div_pos (P.B_pos i) hM0)
  have hαs : min 1 (P.B i / M) ≤ αs i :=
    ge_of_tendsto (L_alpha_tendsto hlim i) (Eventually.of_forall fun l => L_alpha_lb hlim l i)
  have hcpos : 0 < αs i * P.v i j := mul_pos (lt_of_lt_of_le hc hαs) hi
  have h1 : ∀ᶠ l in atTop, αs i * P.v i j / 2 < α l i * P.v i j :=
    ((L_alpha_tendsto hlim i).mul_const (P.v i j)).eventually (lt_mem_nhds (by linarith))
  have h2 : ∀ᶠ l in atTop, ε l < αs i * P.v i j / 6 :=
    hlim.eps_tendsto.eventually (gt_mem_nhds (by linarith))
  have hev : ∀ᶠ l in atTop, ∑ i, smAlloc P (ε l) (α l) i j = 1 := by
    filter_upwards [h1, h2] with l hl1 hl2
    have hT := le_topBid P (ε l) (α l) j (some i)
    simp only [smBid] at hT
    have hw0 : bandWeight P (ε l) (α l) j none = 0 := by
      unfold bandWeight; apply max_eq_left; simp only [smBid]; linarith
    have hD := denom_pos P (ε l) (hlim.eps_pos l) (α l) j
    unfold smAlloc
    rw [← Finset.sum_div, div_eq_one_iff_eq hD.ne', Fintype.sum_option, hw0, zero_add]
  exact tendsto_nhds_unique (tendsto_finsetSum _ fun i _ => hlim.alloc_tendsto i j)
    (tendsto_const_nhds.congr' (hev.mono fun l hl => hl.symm))

end Lim2

end MPX

namespace MPX

open Filter Topology

variable {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G]

lemma highestOther_eq_top (v : N → G → ℝ) (a : N → ℝ) (i i' : N) (j : G) (hne : i' ≠ i)
    (htop : ∀ k, a k * v k j ≤ a i' * v i' j) : highestOther v a i j = a i' * v i' j := by
  unfold highestOther
  have hmem : i' ∈ Finset.univ.erase i := by simp [hne]
  rw [dif_pos ⟨i', hmem⟩]
  exact le_antisymm (Finset.sup'_le _ _ fun k _ => htop k)
    (Finset.le_sup' (fun k => a k * v k j) hmem)

lemma exists_limit (P : PacingGame N G) :
    ∃ (ε H : ℕ → ℝ) (M : ℝ) (α : ℕ → N → ℝ) (αs : N → ℝ) (xs ps ss : N → G → ℝ),
      IsSmoothedLimit P ε H M α αs xs ps ss := by
  set M : ℝ := ∑ i, ∑ j, P.v i j + 2 with hMdef
  set ε0 : ℕ → ℝ := fun l => 1 / ((l : ℝ) + 1) with hε0
  set H0 : ℕ → ℝ := fun l => M / ε0 l + l + 1 with hH0
  have hεpos : ∀ l, 0 < ε0 l := fun l => by simp only [hε0]; positivity
  have hεle : ∀ l, ε0 l ≤ 1 := fun l => by
    simp only [hε0]; rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg l : (0:ℝ) ≤ l)]
  have hvM : ∀ i j, P.v i j ≤ ∑ i, ∑ j, P.v i j := by
    intro i j
    calc P.v i j ≤ ∑ j, P.v i j := Finset.single_le_sum (fun k _ => P.v_nonneg i k) (Finset.mem_univ j)
      _ ≤ ∑ i, ∑ j, P.v i j := Finset.single_le_sum (f := fun i => ∑ j, P.v i j)
          (fun k _ => Finset.sum_nonneg fun j _ => P.v_nonneg k j) (Finset.mem_univ i)
  have hS0 : 0 ≤ ∑ i, ∑ j, P.v i j := Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun j _ => P.v_nonneg k j
  have hMb : ∀ l i, ∑ j, P.v i j + 2 * ε0 l ≤ M := by
    intro l i
    have : ∑ j, P.v i j ≤ ∑ i, ∑ j, P.v i j := Finset.single_le_sum (f := fun i => ∑ j, P.v i j)
          (fun k _ => Finset.sum_nonneg fun j _ => P.v_nonneg k j) (Finset.mem_univ i)
    linarith [hεle l]
  have hM0 : 0 < M := by linarith
  have hHgt : ∀ l, M / ε0 l < H0 l := by
    intro l; simp only [hH0]; linarith [(Nat.cast_nonneg l : (0:ℝ) ≤ l)]
  have hpne : ∀ l, ∃ a : N → ℝ, IsSmoothedPNE P (ε0 l) (H0 l) a :=
    fun l => exists_pne P (ε0 l) (H0 l) M (hεpos l) (hMb l) (hHgt l)
  choose α0 hα0 using hpne
  let z : ℕ → (N → ℝ) × (N → G → ℝ) × (N → G → ℝ) × (N → G → ℝ) := fun l =>
    (α0 l, fun i j => smAlloc P (ε0 l) (α0 l) i j, fun i j => smPrice P (ε0 l) (α0 l) i j,
      fun i j => smPay P (ε0 l) (α0 l) i j)
  -- bounds
  have hα0m : ∀ l i, α0 l i ∈ Set.Icc (0:ℝ) 1 := fun l => (hα0 l).1
  have hpr : ∀ l i j, smPrice P (ε0 l) (α0 l) i j ≤ M := by
    intro l i j
    have h1 : (Finset.univ.erase (some i)).sup' ⟨none, by simp⟩ (smBid P (ε0 l) (α0 l) j) ≤ M := by
      apply Finset.sup'_le
      intro k _
      rcases k with _ | k
      · simp only [smBid]; linarith [hεle l]
      · simp only [smBid]
        have := mul_le_of_le_one_left (P.v_nonneg k j) (hα0m l k).2
        linarith [hvM k j]
    unfold smPrice; linarith [hεpos l]
  have hbd : ∀ l, z l ∈ Metric.closedBall (0 : (N → ℝ) × (N → G → ℝ) × (N → G → ℝ) × (N → G → ℝ)) M := by
    intro l
    rw [mem_closedBall_zero_iff]
    have hx : ∀ i j, 0 ≤ smAlloc P (ε0 l) (α0 l) i j ∧ smAlloc P (ε0 l) (α0 l) i j ≤ 1 :=
      fun i j => ⟨smAlloc_nonneg _ _ _ _ _, smAlloc_le_one _ _ (hεpos l) _ _ _⟩
    have hp : ∀ i j, ε0 l ≤ smPrice P (ε0 l) (α0 l) i j := fun i j => eps_le_smPrice _ _ _ _ _
    simp only [z, Prod.norm_def]
    refine max_le ?_ (max_le ?_ (max_le ?_ ?_))
    · refine (pi_norm_le_iff_of_nonneg hM0.le).2 fun i => ?_
      have hm := hα0m l i
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hm.1, hm.2]
    · refine (pi_norm_le_iff_of_nonneg hM0.le).2 fun i => ?_
      refine (pi_norm_le_iff_of_nonneg hM0.le).2 fun j => ?_
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hx i j]
    · refine (pi_norm_le_iff_of_nonneg hM0.le).2 fun i => ?_
      refine (pi_norm_le_iff_of_nonneg hM0.le).2 fun j => ?_
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hp i j, hpr l i j, hεpos l]
    · refine (pi_norm_le_iff_of_nonneg hM0.le).2 fun i => ?_
      refine (pi_norm_le_iff_of_nonneg hM0.le).2 fun j => ?_
      rw [Real.norm_eq_abs, abs_le]
      have h1 := hx i j
      have h2 := hp i j
      have h3 := hpr l i j
      have h4 := hεpos l
      unfold smPay
      constructor <;> nlinarith
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_closedBall _ _).tendsto_subseq hbd
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hεt : Tendsto ε0 atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hHt : Tendsto H0 atTop atTop := by
    refine tendsto_atTop_mono (fun l => ?_) tendsto_natCast_atTop_atTop
    simp only [hH0]
    have : 0 ≤ M / ε0 l := div_nonneg hM0.le (hεpos l).le
    linarith
  have h1 : Tendsto (fun l => α0 (φ l)) atTop (𝓝 a.1) := (continuous_fst.tendsto _).comp hlim
  have h2 : Tendsto (fun l => (z (φ l)).2.1) atTop (𝓝 a.2.1) :=
    ((continuous_fst.comp continuous_snd).tendsto _).comp hlim
  have h3 : Tendsto (fun l => (z (φ l)).2.2.1) atTop (𝓝 a.2.2.1) :=
    ((continuous_fst.comp (continuous_snd.comp continuous_snd)).tendsto _).comp hlim
  have h4 : Tendsto (fun l => (z (φ l)).2.2.2) atTop (𝓝 a.2.2.2) :=
    ((continuous_snd.comp (continuous_snd.comp continuous_snd)).tendsto _).comp hlim
  refine ⟨ε0 ∘ φ, H0 ∘ φ, M, α0 ∘ φ, a.1, a.2.1, a.2.2.1, a.2.2.2, ?_⟩
  exact {
    eps_pos := fun l => hεpos _
    M_bound := fun l => hMb _
    H_gt := fun l => hHgt _
    eps_tendsto := hεt.comp hφt
    H_tendsto := hHt.comp hφt
    equilibrium := fun l => hα0 _
    alpha_tendsto := h1
    alloc_tendsto := fun i j => tendsto_pi_nhds.1 (tendsto_pi_nhds.1 h2 i) j
    price_tendsto := fun i j => tendsto_pi_nhds.1 (tendsto_pi_nhds.1 h3 i) j
    pay_tendsto := fun i j => tendsto_pi_nhds.1 (tendsto_pi_nhds.1 h4 i) j }

lemma exists_sppe (P : PacingGame N G) :
    ∃ (α : N → ℝ) (x : N → G → ℝ) (p : G → ℝ), IsSPPE P α x p := by
  classical
  obtain ⟨ε, H, M, α, αs, xs, ps, ss, hlim⟩ := exists_limit P
  let p : G → ℝ := fun j => if h : ∃ i, 0 < xs i j then highestOther P.v αs h.choose j else 0
  have hsp : ∀ i j, 0 < xs i j → p j = highestOther P.v αs i j := by
    intro i j hx
    have h : ∃ i, 0 < xs i j := ⟨i, hx⟩
    simp only [p, dif_pos h]
    set i0 := h.choose
    have hx0 : 0 < xs i0 j := h.choose_spec
    by_cases hi : i0 = i
    · rw [hi]
    · have t0 := L_winner hlim i0 j hx0
      have t1 := L_winner hlim i j hx
      rw [highestOther_eq_top P.v αs i0 i j (Ne.symm hi) t1,
        highestOther_eq_top P.v αs i i0 j hi t0]
      exact le_antisymm (t0 i) (t1 i0)
  have hpay : ∀ i j, p j * xs i j = ss i j := by
    intro i j
    rw [L_pay hlim i j]
    rcases eq_or_lt_of_le (L_xs_mem hlim i j).1 with h | h
    · rw [← h]; ring
    · rw [hsp i j h, L_price hlim i j]; ring
  refine ⟨αs, xs, p, {
    alpha_mem := L_alphas_mem hlim
    alloc_mem := L_xs_mem hlim
    supply := L_supply hlim
    full_alloc := L_full hlim
    winner_top := L_winner hlim
    second_price := hsp
    budget := fun i => by simp only [hpay]; exact L_budget hlim i
    no_unnecessary_pacing := fun i hi => by
      simp only [hpay] at hi
      by_contra hne
      have hlt : αs i < 1 := lt_of_le_of_ne (L_alphas_mem hlim i).2 hne
      rw [L_spend_all hlim i hlt] at hi
      exact lt_irrefl _ hi }⟩

end MPX

open MPX in
theorem solution {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G] (P : PacingGame N G) :
    ∃ (α : N → ℝ) (x : N → G → ℝ) (p : G → ℝ), IsSPPE P α x p :=
  exists_sppe P
