-- Prove2me | solution 1 for HartSchmeidler.FinStrat.fset_game_has_ce
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:35:13.08615+00:00
-- url     : https://prove2.me/submissions/3b824b4a-6192-49eb-b0e5-175e18ac9595

import Definitions.Def_HartSchmeidler_FinStrat_Game



namespace HartSchmeidler.FinStrat

open MeasureTheory

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

section Fin

theorem stat_dist {A : Type*} [Fintype A] [Nonempty A] [DecidableEq A] (y : A → A → ℝ)
    (hy : ∀ r t, 0 ≤ y r t) :
    ∃ x : A → ℝ, (∀ a, 0 ≤ x a) ∧ ∑ a, x a = 1 ∧ ∀ t, ∑ r, x r * y r t = x t * ∑ u, y t u := by
  have hrs0 : ∀ r, 0 ≤ ∑ t, y r t := fun r => Finset.sum_nonneg fun t _ => hy r t
  have htot0 : 0 ≤ ∑ r, ∑ t, y r t := Finset.sum_nonneg fun r _ => hrs0 r
  have hrs : ∀ r, ∑ t, y r t ≤ ∑ r, ∑ t, y r t :=
    fun r => Finset.single_le_sum (f := fun r => ∑ t, y r t) (fun r _ => hrs0 r) (Finset.mem_univ r)
  set c : ℝ := 1 + ∑ r, ∑ t, y r t with hcdef
  have hc : 0 < c := by linarith
  have hrsc : ∀ r, (∑ t, y r t) / c ≤ 1 := fun r => by
    rw [div_le_one hc]; linarith [hrs r]
  let Ψ : (A → ℝ) → (A → ℝ) := fun x t => x t * (1 - (∑ u, y t u) / c) + (∑ r, x r * y r t) / c
  have hcont : Continuous Ψ := by
    apply continuous_pi
    intro t
    have : Continuous fun x : A → ℝ => ∑ r, x r * y r t :=
      continuous_finset_sum _ fun r _ => (continuous_apply r).mul continuous_const
    exact ((continuous_apply t).mul continuous_const).add (this.div_const c)
  have hmaps : Set.MapsTo Ψ (stdSimplex ℝ A) (stdSimplex ℝ A) := by
    rintro x ⟨hx0, hx1⟩
    refine ⟨fun t => ?_, ?_⟩
    · have h1 := hx0 t
      have h2 : 0 ≤ 1 - (∑ u, y t u) / c := by linarith [hrsc t]
      have h3 : 0 ≤ (∑ r, x r * y r t) / c :=
        div_nonneg (Finset.sum_nonneg fun r _ => mul_nonneg (hx0 r) (hy r t)) hc.le
      simp only [Ψ]
      positivity
    · simp only [Ψ]
      rw [Finset.sum_add_distrib, ← Finset.sum_div]
      have : ∑ t, x t * (1 - (∑ u, y t u) / c) = 1 - (∑ t, x t * ∑ u, y t u) / c := by
        simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hx1]
        congr 1
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl; intro t _; ring
      rw [this]
      have h2 : ∑ t, ∑ r, x r * y r t = ∑ t, x t * ∑ u, y t u := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun r _ => (Finset.mul_sum _ _ _).symm
      rw [h2]
      ring
  obtain ⟨x, hxK, hfix⟩ := brouwer_fp (convex_stdSimplex ℝ A) (isCompact_stdSimplex ℝ A)
    ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary A)⟩ Ψ hcont.continuousOn hmaps
  refine ⟨x, hxK.1, hxK.2, fun t => ?_⟩
  have h := congrFun hfix t
  simp only [Ψ] at h
  have h2 : (∑ r, x r * y r t) / c = x t * (∑ u, y t u) / c := by
    have : x t * (1 - (∑ u, y t u) / c) + (∑ r, x r * y r t) / c = x t := h
    have e : x t * (1 - (∑ u, y t u) / c) = x t - x t * (∑ u, y t u) / c := by ring
    linarith
  exact (div_left_inj' hc.ne').1 h2


theorem stat_zero {A : Type*} [Fintype A] [DecidableEq A] (x : A → ℝ) (y : A → A → ℝ)
    (hst : ∀ t, ∑ r, x r * y r t = x t * ∑ u, y t u) (G : A → ℝ) :
    ∑ a, x a * ∑ t, y a t * (G a - G t) = 0 := by
  have h1 : ∑ a, x a * ∑ t, y a t * (G a - G t) =
      ∑ a, x a * (∑ t, y a t) * G a - ∑ a, ∑ t, x a * y a t * G t := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib, mul_assoc]
    congr 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have h2 : ∑ a, ∑ t, x a * y a t * G t = ∑ t, x t * (∑ u, y t u) * G t := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    rw [← Finset.sum_mul, hst t]
  rw [h1, h2]
  simp

section KeyIdent

variable {P : Type*} [Fintype P] [DecidableEq P] {A : P → Type*} [∀ i, Fintype (A i)]
  [∀ i, DecidableEq (A i)] [∀ i, Nonempty (A i)]

/-- splitting the profile space at coordinate `i` -/
def splitEquiv (i : P) (a₀ : A i) : (A i × {s : ∀ j, A j // s i = a₀}) ≃ (∀ j, A j) where
  toFun p := Function.update p.2.1 i p.1
  invFun s := (s i, ⟨Function.update s i a₀, by simp⟩)
  left_inv := by
    rintro ⟨a, z, hz⟩
    simp [hz]
  right_inv := by
    intro s
    simp

theorem key_ident (x : ∀ j, A j → ℝ) (i : P) (yi : A i → A i → ℝ)
    (hst : ∀ t, ∑ r, x i r * yi r t = x i t * ∑ u, yi t u) (g : (∀ j, A j) → ℝ) :
    ∑ s : (∀ j, A j), (∏ j, x j (s j)) * ∑ t, yi (s i) t * (g s - g (Function.update s i t)) = 0 := by
  classical
  let a₀ : A i := Classical.arbitrary _
  rw [← Equiv.sum_comp (splitEquiv i a₀), Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro z _
  have hprod : ∀ a : A i, (∏ j, x j ((splitEquiv i a₀ (a, z)) j)) = x i a * ∏ j ∈ Finset.univ.erase i, x j (z.1 j) := by
    intro a
    simp only [splitEquiv, Equiv.coe_fn_mk]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have hterm : ∀ a : A i, (∏ j, x j ((splitEquiv i a₀ (a, z)) j)) *
      ∑ t, yi ((splitEquiv i a₀ (a, z)) i) t * (g (splitEquiv i a₀ (a, z)) - g (Function.update (splitEquiv i a₀ (a, z)) i t))
      = (∏ j ∈ Finset.univ.erase i, x j (z.1 j)) *
        (x i a * ∑ t, yi a t * (g (Function.update z.1 i a) - g (Function.update z.1 i t))) := by
    intro a
    rw [hprod a]
    simp only [splitEquiv, Equiv.coe_fn_mk, Function.update_self, Function.update_idem]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have := stat_zero (x i) yi hst (fun a => g (Function.update z.1 i a))
  rw [this, mul_zero]

end KeyIdent


section FinCE

variable {P : Type*} [Fintype P] [DecidableEq P] {A : P → Type*} [∀ i, Fintype (A i)]
  [∀ i, DecidableEq (A i)] [∀ i, Nonempty (A i)]

/-- the vector of equilibrium conditions of a profile -/
def ceV (u : P → (∀ i, A i) → ℝ) (s : ∀ i, A i) (k : (i : P) × A i × A i) : ℝ :=
  if s k.1 = k.2.1 then u k.1 s - u k.1 (Function.update s k.1 k.2.2) else 0

lemma sumV (u : P → (∀ i, A i) → ℝ) (y : ((i : P) × A i × A i) → ℝ) (s : ∀ i, A i) :
    ∑ k, y k * ceV u s k =
      ∑ i, ∑ t, y ⟨i, s i, t⟩ * (u i s - u i (Function.update s i t)) := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  simp only [ceV, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

theorem fin_ce (u : P → (∀ i, A i) → ℝ) :
    ∃ w : (∀ i, A i) → ℝ, (∀ s, 0 ≤ w s) ∧ ∑ s, w s = 1 ∧
      ∀ k, 0 ≤ ∑ s, w s * ceV u s k := by
  by_contra hno
  push_neg at hno
  let Φ : ((∀ i, A i) → ℝ) →ₗ[ℝ] (((i : P) × A i × A i) → ℝ) :=
    { toFun := fun w k => ∑ s, w s * ceV u s k
      map_add' := by intro a b; ext k; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro c a; ext k; simp [Finset.mul_sum, mul_assoc] }
  let C := Φ '' stdSimplex ℝ (∀ i, A i)
  let Q : Set (((i : P) × A i × A i) → ℝ) := {x | ∀ k, 0 ≤ x k}
  have hCconv : Convex ℝ C := (convex_stdSimplex ℝ _).linear_image Φ
  have hCcpt : IsCompact C :=
    (isCompact_stdSimplex ℝ _).image (LinearMap.continuous_of_finiteDimensional Φ)
  have hQconv : Convex ℝ Q := by
    intro a ha b hb c d hc hd _ k
    have := ha k; have := hb k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    positivity
  have hQcl : IsClosed Q := by
    have : Q = ⋂ k, {x : ((i : P) × A i × A i) → ℝ | 0 ≤ x k} := by ext x; simp [Q]
    rw [this]
    exact isClosed_iInter fun k => isClosed_le continuous_const (continuous_apply k)
  have hdisj : Disjoint C Q := by
    rw [Set.disjoint_left]
    rintro x ⟨w, ⟨hw0, hw1⟩, rfl⟩ hQ
    obtain ⟨k, hk⟩ := hno w hw0 hw1
    have := hQ k
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk] at this
    linarith
  obtain ⟨f, u₀, v₀, hC, huv, hQf⟩ := geometric_hahn_banach_compact_closed hCconv hCcpt hQconv hQcl hdisj
  let e : ((i : P) × A i × A i) → (((i : P) × A i × A i) → ℝ) := fun k j => if k = j then 1 else 0
  let y : ((i : P) × A i × A i) → ℝ := fun k => f (e k)
  have hfx : ∀ x, f x = ∑ k, x k * y k := by
    intro x
    have := LinearMap.pi_apply_eq_sum_univ (f : (((i : P) × A i × A i) → ℝ) →ₗ[ℝ] ℝ) x
    simpa [smul_eq_mul, y, e] using this
  have hv0 : v₀ < 0 := by
    have := hQf 0 (fun k => le_rfl)
    simpa using this
  have hy : ∀ k, 0 ≤ y k := by
    intro k
    by_contra hneg
    push_neg at hneg
    have hpos : 0 < v₀ / y k := div_pos_of_neg_of_neg hv0 hneg
    have hb : (v₀ / y k + 1) • e k ∈ Q := by
      intro j
      simp only [Pi.smul_apply, smul_eq_mul, e]
      split_ifs <;> simp <;> linarith
    have h1 := hQf _ hb
    rw [map_smul, smul_eq_mul] at h1
    have h2 : (v₀ / y k + 1) * y k = v₀ + y k := by
      have : y k ≠ 0 := hneg.ne
      field_simp
    have h3 : f (e k) = y k := rfl
    rw [h3, h2] at h1
    linarith
  have hs : ∀ s, ∑ k, y k * ceV u s k < 0 := by
    intro s
    have hmem : (fun k => ceV u s k) ∈ C := by
      refine ⟨Pi.single s 1, ⟨fun s' => ?_, ?_⟩, ?_⟩
      · by_cases h : s' = s <;> simp [Pi.single_apply, h]
      · simp
      · ext k
        simp [Φ, Pi.single_apply]
    have := hC _ hmem
    rw [hfx] at this
    have h2 : ∑ k, y k * ceV u s k = ∑ k, ceV u s k * y k :=
      Finset.sum_congr rfl fun k _ => mul_comm _ _
    linarith
  -- stationary distributions
  have hstat : ∀ i : P, ∃ x : A i → ℝ, (∀ a, 0 ≤ x a) ∧ ∑ a, x a = 1 ∧
      ∀ t, ∑ r, x r * y ⟨i, r, t⟩ = x t * ∑ v, y ⟨i, t, v⟩ := fun i =>
    stat_dist (fun r t => y ⟨i, r, t⟩) (fun r t => hy _)
  choose x hx0 hx1 hxst using hstat
  let W : (∀ i, A i) → ℝ := fun s => ∏ i, x i (s i)
  have hW0 : ∀ s, 0 ≤ W s := fun s => Finset.prod_nonneg fun i _ => hx0 i (s i)
  have hW1 : ∑ s, W s = 1 := by
    have := Finset.prod_univ_sum (fun i => (Finset.univ : Finset (A i))) (fun i a => x i a)
    simp only [Fintype.piFinset_univ] at this
    rw [← this]
    exact Finset.prod_eq_one fun i _ => hx1 i
  have hzero : ∑ s, W s * ∑ k, y k * ceV u s k = 0 := by
    calc ∑ s, W s * ∑ k, y k * ceV u s k
        = ∑ s, ∑ i, W s * ∑ t, y ⟨i, s i, t⟩ * (u i s - u i (Function.update s i t)) := by
          apply Finset.sum_congr rfl
          intro s _
          rw [sumV, Finset.mul_sum]
      _ = ∑ i, ∑ s, W s * ∑ t, y ⟨i, s i, t⟩ * (u i s - u i (Function.update s i t)) :=
          Finset.sum_comm
      _ = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          exact key_ident x i (fun r t => y ⟨i, r, t⟩) (hxst i) (u i)
  obtain ⟨s0, hs0⟩ : ∃ s0, 0 < W s0 := by
    by_contra h
    push_neg at h
    have : ∑ s, W s = 0 := Finset.sum_eq_zero fun s _ => le_antisymm (h s) (hW0 s)
    linarith
  have hlt : ∑ s, W s * ∑ k, y k * ceV u s k < 0 := by
    calc ∑ s, W s * ∑ k, y k * ceV u s k < ∑ s : (∀ i, A i), (0 : ℝ) := by
          apply Finset.sum_lt_sum
          · intro s _
            exact mul_nonpos_of_nonneg_of_nonpos (hW0 s) (hs s).le
          · exact ⟨s0, Finset.mem_univ _, mul_neg_of_pos_of_neg hs0 (hs s0)⟩
      _ = 0 := by simp
  linarith

end FinCE


section FSet

theorem fset_core {ι : Type*} [Nonempty ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    [∀ i, Nonempty (S i)]
    (h : ι → (∀ i, S i) → ℝ)
    (T : ∀ i, Finset (S i))
    (hT : IsFSet T) :
    ∃ (F : Finset (∀ i, S i)) (w : (∀ i, S i) → ℝ), IsFSetCE h T F w := by
  classical
  let N : Finset ι := hT.2.toFinset
  have hN : ∀ j, j ∉ N → ∃ c, T j = {c} := by
    intro j hj
    have : j ∉ {i | ¬ ∃ a : S i, T i = {a}} := by simpa [N] using hj
    simpa using this
  let P := {i // i ∈ N}
  let A : P → Type _ := fun i => {a : S i.1 // a ∈ T i.1}
  haveI : ∀ i, Nonempty (A i) := fun i => ⟨⟨(hT.1 i.1).choose, (hT.1 i.1).choose_spec⟩⟩
  let b : ∀ j, S j := fun j => (hT.1 j).choose
  have hb : ∀ j, b j ∈ T j := fun j => (hT.1 j).choose_spec
  let φ : (∀ i : P, A i) → (∀ j, S j) := fun a j => if hj : j ∈ N then (a ⟨j, hj⟩).1 else b j
  have hφT : ∀ a j, φ a j ∈ T j := by
    intro a j
    by_cases hj : j ∈ N
    · simp only [φ, hj, dite_true]; exact (a ⟨j, hj⟩).2
    · simp only [φ, hj, dite_false]; exact hb j
  have hφN : ∀ a (i : P), φ a i.1 = (a i).1 := by
    intro a i
    simp [φ, i.2]
  have hφupd : ∀ (a : ∀ i : P, A i) (i : P) (t : A i),
      φ (Function.update a i t) = Function.update (φ a) i.1 t.1 := by
    intro a i t
    funext j
    by_cases hj : j = i.1
    · subst hj
      rw [Function.update_self, hφN]
      simp
    · rw [Function.update_of_ne hj]
      by_cases hjN : j ∈ N
      · have : (⟨j, hjN⟩ : P) ≠ i := fun h => hj (congrArg Subtype.val h)
        simp [φ, hjN, Function.update_of_ne this]
      · simp [φ, hjN]
  let u : P → (∀ i : P, A i) → ℝ := fun i a => h i.1 (φ a)
  obtain ⟨w0, hw0, hw1, hw2⟩ := fin_ce u
  let F : Finset (∀ i, S i) := Finset.univ.image φ
  let w : (∀ i, S i) → ℝ := fun s => ∑ a, if φ a = s then w0 a else 0
  have hsum : ∀ g : (∀ i, S i) → ℝ, ∑ s ∈ F, w s * g s = ∑ a, w0 a * g (φ a) := by
    intro g
    simp only [w, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    simp [ite_mul, F]
  refine ⟨F, w, ?_, ?_, ?_, ?_⟩
  · intro s hs i
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hs
    exact hφT a i
  · intro s _
    exact Finset.sum_nonneg fun a _ => by split_ifs <;> simp [hw0 a]
  · have := hsum (fun _ => 1)
    simp only [mul_one] at this
    rw [this]; exact hw1
  · intro i r t hr ht
    rw [Finset.sum_filter]
    have h1 : ∑ s ∈ F, (if s i = r then w s * (h i s - h i (Function.update s i t)) else 0)
        = ∑ s ∈ F, w s * (if s i = r then (h i s - h i (Function.update s i t)) else 0) := by
      apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp
    rw [h1, hsum (fun s => if s i = r then (h i s - h i (Function.update s i t)) else 0)]
    by_cases hi : i ∈ N
    · have := hw2 ⟨⟨i, hi⟩, ⟨r, hr⟩, ⟨t, ht⟩⟩
      refine le_of_le_of_eq this (Finset.sum_congr rfl fun a _ => ?_)
      congr 1
      simp only [ceV, u]
      by_cases hc : a ⟨i, hi⟩ = ⟨r, hr⟩
      · have hc' : φ a i = r := by
          have e : φ a i = (a ⟨i, hi⟩).1 := hφN a ⟨i, hi⟩
          rw [e, hc]
        rw [if_pos hc, if_pos hc', hφupd]
      · have hc' : ¬ φ a i = r := by
          intro h2
          apply hc
          apply Subtype.ext
          simpa [φ, hi] using h2
        rw [if_neg hc, if_neg hc']
    · obtain ⟨c, hc⟩ := hN i hi
      have hrc : r = c := by rw [hc] at hr; simpa using hr
      have htc : t = c := by rw [hc] at ht; simpa using ht
      apply Finset.sum_nonneg
      intro a _
      by_cases hca : φ a i = r
      · have : Function.update (φ a) i t = φ a := by
          rw [show t = φ a i by rw [hca, hrc, htc]]
          exact Function.update_eq_self _ _
        simp [hca, this]
      · simp [hca]

end FSet

end Fin

end HartSchmeidler.FinStrat

open HartSchmeidler.FinStrat
open MeasureTheory

theorem solution {ι : Type*} [Nonempty ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    [∀ i, Nonempty (S i)]
    (h : ι → (∀ i, S i) → ℝ)
    (hbounded : ∀ i, ∃ C : ℝ, ∀ s, |h i s| ≤ C)
    (T : ∀ i, Finset (S i))
    (hT : IsFSet T) :
    ∃ (F : Finset (∀ i, S i)) (w : (∀ i, S i) → ℝ), IsFSetCE h T F w := by
  exact fset_core h T hT
