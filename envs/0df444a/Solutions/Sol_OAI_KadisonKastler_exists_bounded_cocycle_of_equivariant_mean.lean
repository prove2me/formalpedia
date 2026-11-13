-- Prove2me | solution 1 for OAI.KadisonKastler.exists_bounded_cocycle_of_equivariant_mean
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:12:10.698723+00:00
-- url     : https://prove2.me/submissions/b5a75103-416e-4262-806b-2c98ee60f938

import Mathlib
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.MetricSpace.Cauchy
import Definitions.Def_Q260K023

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryImprovement
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The quadratic step in boundary cocycle correction

Only the structural properties of the boundary mean occur here.  The mean
need not be normal.  Covariance cancellation and polar normalization give
the quadratic improvement used in the measurable iteration.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

universe u v

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

namespace BimoduleMean

variable {ι : B →⋆ₐ[ℂ] A} (m : BimoduleMean ι)

/-- The linear terms cancel exactly in the centered product. -/
theorem covariance (x y : A) :
    m.toCLM (x * y) - m.toCLM x * m.toCLM y =
      m.toCLM ((x - ι (m.toCLM x)) * (y - ι (m.toCLM y))) := by
  simp only [sub_mul, mul_sub, map_sub, m.map_right, m.map_left, m.fixed]
  noncomm_ring

/-- Contractivity of the mean bounds the covariance by its two residuals. -/
theorem norm_covariance_le (x y : A) :
    ‖m.toCLM (x * y) - m.toCLM x * m.toCLM y‖ ≤
      ‖x - ι (m.toCLM x)‖ * ‖y - ι (m.toCLM y)‖ := by
  rw [m.covariance]
  exact (m.norm_le _).trans (norm_mul_le _ _)

/-- For a unitary the covariance identity is the exact unitarity defect. -/
theorem variance (x : unitary A) :
    1 - star (m.toCLM (x : A)) * m.toCLM (x : A) =
      m.toCLM (star ((x : A) - ι (m.toCLM (x : A))) *
        ((x : A) - ι (m.toCLM (x : A)))) := by
  have hc := m.covariance (star (x : A)) (x : A)
  have hi : ι (m.toCLM (star (x : A))) = star (ι (m.toCLM (x : A))) := by
    rw [m.map_star]
    exact StarHomClass.map_star ι _
  rw [hi] at hc
  simpa only [Unitary.star_mul_self_of_mem x.property, m.map_one, m.map_star,
    star_sub] using hc

/-- Averaging preserves the error from a field independent of the mean variable. -/
theorem norm_sub_le (x : A) (b : B) {e : ℝ} (h : ‖x - ι b‖ ≤ e) :
    ‖m.toCLM x - b‖ ≤ e := by
  rw [← m.fixed b, ← map_sub]
  exact (m.norm_le _).trans h

/-- The residual from the average is at most twice the original error. -/
theorem norm_residual_le (x : A) (b : B) {e : ℝ} (h : ‖x - ι b‖ ≤ e) :
    ‖x - ι (m.toCLM x)‖ ≤ 2 * e := by
  calc
    _ ≤ ‖x - ι b‖ + ‖ι b - ι (m.toCLM x)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ e + e := add_le_add h (by
      rw [← map_sub]
      exact (NonUnitalStarAlgHom.norm_apply_le ι _).trans
        (by simpa only [norm_sub_rev] using m.norm_sub_le x b h))
    _ = _ := by ring

/-- Two residuals bounded by `2e` give the quadratic covariance bound. -/
theorem norm_covariance_le_four_mul_sq (x y : A) {e : ℝ} (he : 0 ≤ e)
    (hx : ‖x - ι (m.toCLM x)‖ ≤ 2 * e)
    (hy : ‖y - ι (m.toCLM y)‖ ≤ 2 * e) :
    ‖m.toCLM (x * y) - m.toCLM x * m.toCLM y‖ ≤ 4 * e ^ 2 := by
  calc
    _ ≤ ‖x - ι (m.toCLM x)‖ * ‖y - ι (m.toCLM y)‖ := m.norm_covariance_le x y
    _ ≤ (2 * e) * (2 * e) := mul_le_mul hx hy (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The average of a unitary within `e` of the fixed algebra has unitarity
error at most `4e²`. -/
theorem norm_variance_le_four_mul_sq (x : unitary A) (b : B) {e : ℝ}
    (he : 0 ≤ e) (hx : ‖(x : A) - ι b‖ ≤ e) :
    ‖1 - star (m.toCLM (x : A)) * m.toCLM (x : A)‖ ≤ 4 * e ^ 2 := by
  have hr := m.norm_residual_le (x : A) b hx
  rw [m.variance]
  calc
    _ ≤ ‖star ((x : A) - ι (m.toCLM (x : A))) *
        ((x : A) - ι (m.toCLM (x : A)))‖ := m.norm_le _
    _ ≤ ‖(x : A) - ι (m.toCLM (x : A))‖ *
        ‖(x : A) - ι (m.toCLM (x : A))‖ := by
      simpa only [norm_star] using norm_mul_le
        (star ((x : A) - ι (m.toCLM (x : A))))
        ((x : A) - ι (m.toCLM (x : A)))
    _ ≤ (2 * e) * (2 * e) := mul_le_mul hr hr (norm_nonneg _) (by positivity)
    _ = _ := by ring

end BimoduleMean

private theorem boundary_sqrt_scalar_sub_one_sq_le {t : ℝ} (ht : 0 ≤ t) :
    (Real.sqrt t - 1) ^ 2 ≤ (t - 1) ^ 2 := by
  have hlarge : 1 ≤ (Real.sqrt t + 1) ^ 2 := by nlinarith [Real.sqrt_nonneg t]
  calc
    _ ≤ (Real.sqrt t - 1) ^ 2 * (Real.sqrt t + 1) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hlarge (sq_nonneg (Real.sqrt t - 1))]
    _ = _ := by rw [← mul_pow]; congr 1; nlinarith [Real.sq_sqrt ht]

section Ordered

variable [PartialOrder B] [StarOrderedRing B]

/-- The square root cannot increase the operator-norm error from one. -/
theorem norm_sqrt_sub_one_le (a : B) (ha : 0 ≤ a) :
    ‖CFC.sqrt a - 1‖ ≤ ‖a - 1‖ := by
  let b := CFC.sqrt a
  have hb : star b = b := (CFC.sqrt_nonneg a).isSelfAdjoint.star_eq
  have haStar : star a = a := ha.isSelfAdjoint.star_eq
  have hbCFC : b = cfc Real.sqrt a := by
    dsimp [b]
    rw [CFC.sqrt_eq_real_sqrt a ha, cfcₙ_eq_cfc]
  have hleft : cfc (fun t : ℝ => (Real.sqrt t - 1) ^ 2) a =
      star (b - 1) * (b - 1) := by
    rw [cfc_pow (fun t : ℝ => Real.sqrt t - 1) 2 a,
      cfc_sub Real.sqrt (fun _ : ℝ => 1) a,
      cfc_const_one ℝ a, ← hbCFC, star_sub, hb, star_one, pow_two]
  have hright : cfc (fun t : ℝ => (t - 1) ^ 2) a =
      star (a - 1) * (a - 1) := by
    rw [cfc_pow (fun t : ℝ => t - 1) 2 a,
      cfc_sub (fun t : ℝ => t) (fun _ : ℝ => 1) a,
      cfc_id' ℝ a, cfc_const_one ℝ a, star_sub, haStar, star_one, pow_two]
  have horder : star (b - 1) * (b - 1) ≤ star (a - 1) * (a - 1) := by
    rw [← hleft, ← hright]
    apply (cfc_le_iff _ _ a).mpr
    intro t ht
    exact boundary_sqrt_scalar_sub_one_sq_le (spectrum_nonneg_of_nonneg ha ht)
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg horder (star_mul_self_nonneg _)
  rw [CStarRing.norm_star_mul_self, CStarRing.norm_star_mul_self] at hn
  change ‖b - 1‖ ≤ ‖a - 1‖
  nlinarith [norm_nonneg (b - 1), norm_nonneg (a - 1)]

/-- Polar normalization costs no more than the unitarity defect. -/
theorem exists_polar_unitary_close_of_near_unitary (x : B) (v : unitary B)
    (hx : ‖x - (v : B)‖ < 1) :
    ∃ u : unitary B, (u : B) * CFC.abs x = x ∧
      ‖(u : B) - x‖ ≤ ‖star x * x - 1‖ := by
  nontriviality B
  have hinv : ‖(((Unitary.toUnits v)⁻¹ : Bˣ) : B)‖ = 1 := by
    change ‖star (v : B)‖ = 1
    rw [norm_star, CStarRing.norm_coe_unitary]
  let t : Bˣ := Units.ofNearby (Unitary.toUnits v) x (by
    simpa only [Unitary.val_toUnits_apply, hinv, inv_one] using hx)
  have ht : (t : B) = x := rfl
  obtain ⟨u, hu⟩ := exists_unitary_mul_abs t
  rw [ht] at hu
  refine ⟨u, hu, ?_⟩
  have hid : (u : B) - x = (u : B) * (1 - CFC.abs x) := by
    rw [mul_sub, mul_one, hu]
  rw [hid, CStarRing.norm_coe_unitary_mul, norm_sub_rev]
  exact norm_sqrt_sub_one_le (star x * x) (star_mul_self_nonneg x)

end Ordered

section Transport

variable {G : Type*} [Group G]

/-- The transport construction has an exact factorization even when `V`
is only an approximate cocycle. -/
theorem boundaryTransport_factor (α : G →* (B ≃⋆ₐ[ℂ] B))
    (V : G → unitary B) (g h t : G) :
    boundaryTransport α V (g * h) t =
      boundaryTransport α V g t * α g (boundaryTransport α V h (g⁻¹ * t)) := by
  have hcancel : α g (star (V (g⁻¹ * t) : B)) * α g (V (g⁻¹ * t) : B) = 1 := by
    rw [← map_mul, Unitary.star_mul_self_of_mem (V (g⁻¹ * t)).property, map_one]
  simp only [boundaryTransport, map_mul, StarAlgEquiv.mul_apply, mul_inv_rev, mul_assoc]
  rw [← mul_assoc (α g (star (V (g⁻¹ * t) : B))), hcancel, one_mul]

/-- The pointwise distance from the transport field to the original
unitary is bounded by the original cocycle defect. -/
theorem norm_boundaryTransport_sub_le (α : G →* (B ≃⋆ₐ[ℂ] B))
    (V : G → unitary B) {e : ℝ}
    (hdefect : ∀ g h, ‖(V g : B) * α g (V h : B) - (V (g * h) : B)‖ ≤ e)
    (g t : G) : ‖boundaryTransport α V g t - (V g : B)‖ ≤ e := by
  let W : unitary B := Unitary.map (StarMonoidHom.ofClass (α g)) (V (g⁻¹ * t))
  have hcancel : α g (star (V (g⁻¹ * t) : B)) * (W : B) = 1 := by
    change α g (star (V (g⁻¹ * t) : B)) * α g (V (g⁻¹ * t) : B) = 1
    rw [← map_mul, Unitary.star_mul_self_of_mem (V (g⁻¹ * t)).property, map_one]
  have heq : (boundaryTransport α V g t - (V g : B)) * (W : B) =
      (V t : B) - (V g : B) * α g (V (g⁻¹ * t) : B) := by
    rw [sub_mul, boundaryTransport, mul_assoc, hcancel, mul_one]
    rfl
  calc
    ‖boundaryTransport α V g t - (V g : B)‖ =
        ‖(boundaryTransport α V g t - (V g : B)) * (W : B)‖ :=
      (CStarRing.norm_mul_coe_unitary _ W).symm
    _ = ‖(V t : B) - (V g : B) * α g (V (g⁻¹ * t) : B)‖ := congrArg norm heq
    _ = ‖(V g : B) * α g (V (g⁻¹ * t) : B) - (V t : B)‖ := norm_sub_rev _ _
    _ ≤ e := by simpa only [mul_inv_cancel_left] using hdefect g (g⁻¹ * t)

end Transport

section Improvement

variable {ι : B →⋆ₐ[ℂ] A} (m : BimoduleMean ι)
variable [PartialOrder B] [StarOrderedRing B]

/-- One averaged unitary can be replaced by an actual unitary at quadratic
cost, while retaining its original first-order proximity. -/
theorem BimoduleMean.exists_improved_unitary (X : unitary A) (V : unitary B)
    {e : ℝ} (he : 0 ≤ e) (he1 : e < 1) (hXV : ‖(X : A) - ι (V : B)‖ ≤ e) :
    ∃ W : unitary B,
      ‖(W : B) - m.toCLM (X : A)‖ ≤ 4 * e ^ 2 ∧
      ‖(W : B) - (V : B)‖ ≤ e + 4 * e ^ 2 := by
  have hmV := m.norm_sub_le (X : A) (V : B) hXV
  obtain ⟨W, -, hW⟩ := exists_polar_unitary_close_of_near_unitary
    (m.toCLM (X : A)) V (hmV.trans_lt he1)
  have hquad : ‖(W : B) - m.toCLM (X : A)‖ ≤ 4 * e ^ 2 :=
    hW.trans (by simpa only [norm_sub_rev] using m.norm_variance_le_four_mul_sq X V he hXV)
  refine ⟨W, hquad, ?_⟩
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    ((add_le_add hquad hmV).trans_eq (by ring))

omit [PartialOrder B] [StarOrderedRing B] in
/-- The operator-norm defect of the averaged family is quadratic. -/
theorem BimoduleMean.norm_averaged_defect_le_four_mul_sq
    {G : Type*} [Group G]
    (α : G → B ≃⋆ₐ[ℂ] B) (fieldAction : G → A ≃⋆ₐ[ℂ] A)
    (hequiv : ∀ g x, m.toCLM (fieldAction g x) = α g (m.toCLM x))
    (hι : ∀ g b, fieldAction g (ι b) = ι (α g b))
    (X : G → unitary A) (V : G → unitary B)
    (hfactor : ∀ g h, (X (g * h) : A) = (X g : A) * fieldAction g (X h : A))
    {e : ℝ} (he : 0 ≤ e) (hXV : ∀ g, ‖(X g : A) - ι (V g : B)‖ ≤ e)
    (g h : G) :
    ‖m.toCLM (X (g * h) : A) -
      m.toCLM (X g : A) * α g (m.toCLM (X h : A))‖ ≤ 4 * e ^ 2 := by
  rw [hfactor, ← hequiv]
  apply m.norm_covariance_le_four_mul_sq _ _ he
  · exact m.norm_residual_le _ _ (hXV g)
  · rw [hequiv, ← hι, ← map_sub, StarAlgEquiv.norm_map]
    exact m.norm_residual_le _ _ (hXV h)

/-- Quadratic polar correction for the entire family.  The cocycle
factorization and equivariance are exact structural identities; no correction
conclusion is assumed. -/
theorem BimoduleMean.exists_quadratic_improvement
    {G : Type*} [Group G]
    (α : G → B ≃⋆ₐ[ℂ] B) (fieldAction : G → A ≃⋆ₐ[ℂ] A)
    (hequiv : ∀ g x, m.toCLM (fieldAction g x) = α g (m.toCLM x))
    (hι : ∀ g b, fieldAction g (ι b) = ι (α g b))
    (X : G → unitary A) (V : G → unitary B)
    (hfactor : ∀ g h, (X (g * h) : A) = (X g : A) * fieldAction g (X h : A))
    {e : ℝ} (he : 0 ≤ e) (he1 : e < 1)
    (hXV : ∀ g, ‖(X g : A) - ι (V g : B)‖ ≤ e) :
    ∃ W : G → unitary B,
      (∀ g, ‖(W g : B) - (V g : B)‖ ≤ e + 4 * e ^ 2) ∧
      (∀ g h, ‖(W g : B) * α g (W h : B) - (W (g * h) : B)‖ ≤ 16 * e ^ 2) := by
  choose W hW hWV using fun g => m.exists_improved_unitary (X g) (V g) he he1 (hXV g)
  refine ⟨W, hWV, ?_⟩
  intro g h
  let a := m.toCLM (X g : A)
  let b := m.toCLM (X h : A)
  let c := m.toCLM (X (g * h) : A)
  have ha : ‖a‖ ≤ 1 := (m.norm_le _).trans (norm_unitary_le_one _)
  have hd := m.norm_averaged_defect_le_four_mul_sq α fieldAction hequiv hι X V hfactor he hXV g h
  have hsplit : (W g : B) * α g (W h : B) - (W (g * h) : B) =
      ((W g : B) - a) * α g (W h : B) +
        a * α g ((W h : B) - b) + (a * α g b - c) + (c - (W (g * h) : B)) := by
    rw [map_sub]
    noncomm_ring
  rw [hsplit]
  calc
    _ ≤ ‖((W g : B) - a) * α g (W h : B)‖ + ‖a * α g ((W h : B) - b)‖ +
        ‖a * α g b - c‖ + ‖c - (W (g * h) : B)‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add ((norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ (4 * e ^ 2) * 1 + 1 * (4 * e ^ 2) + 4 * e ^ 2 + 4 * e ^ 2 := by
      apply add_le_add
      · apply add_le_add
        · apply add_le_add
          · exact (norm_mul_le _ _).trans (mul_le_mul (hW g)
              (by rw [StarAlgEquiv.norm_map]; exact norm_unitary_le_one _)
              (norm_nonneg _) (by positivity))
          · exact (norm_mul_le _ _).trans (mul_le_mul ha
              (by rw [StarAlgEquiv.norm_map]; exact hW h)
              (norm_nonneg _) (by positivity))
        · simpa only [a, b, c, norm_sub_rev] using hd
      · simpa only [c, norm_sub_rev] using hW (g * h)
    _ = _ := by ring

end Improvement

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_QuadraticIteration
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Convergence of the quadratic boundary correction

The constants are the ones used by the cocycle averaging step: defect
`e` improves to `16e²`, at displacement at most `e + 4e²`.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

/-- Iterating the quadratic improvement gives an exact solution within
`2e`, where `e ≤ 1/64` is the original defect. -/
theorem exists_zero_of_quadratic_improvement
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (d : X → ℝ) (hd : Continuous d) (hd0 : ∀ x, 0 ≤ d x)
    (hstep : ∀ x, d x ≤ 1 / 64 → ∃ y,
      d y ≤ 16 * (d x) ^ 2 ∧ dist x y ≤ d x + 4 * (d x) ^ 2)
    (x₀ : X) (hx₀ : d x₀ ≤ 1 / 64) :
    ∃ y, d y = 0 ∧ dist x₀ y ≤ 2 * d x₀ := by
  let S := {x : X // d x ≤ 1 / 64}
  have hquarter (x : S) : 16 * (d x.val) ^ 2 ≤ d x.val / 4 := by
    have hp := hd0 x.val
    have hb := x.property
    nlinarith
  let next : S → S := fun x =>
    ⟨Classical.choose (hstep x.val x.property),
      ((Classical.choose_spec (hstep x.val x.property)).1.trans
        (hquarter x)).trans (by have hx := x.property; linarith)⟩
  have hnext (x : S) : d (next x).val ≤ d x.val / 4 ∧
      dist x.val (next x).val ≤ d x.val + 4 * (d x.val) ^ 2 := by
    exact ⟨(Classical.choose_spec (hstep x.val x.property)).1.trans (hquarter x),
      (Classical.choose_spec (hstep x.val x.property)).2⟩
  let s : ℕ → S := fun n => (next^[n]) ⟨x₀, hx₀⟩
  have hs0 : (s 0).val = x₀ := rfl
  have hsnext (n : ℕ) : s (n + 1) = next (s n) := by
    exact Function.iterate_succ_apply' next n ⟨x₀, hx₀⟩
  have hdecay (n : ℕ) : d (s n).val ≤ d x₀ * (1 / 4 : ℝ) ^ n := by
    induction n with
    | zero => simp only [hs0, pow_zero, mul_one, le_refl]
    | succ n ih =>
      rw [hsnext]
      calc
        _ ≤ d (s n).val / 4 := (hnext (s n)).1
        _ ≤ (d x₀ * (1 / 4 : ℝ) ^ n) / 4 := div_le_div_of_nonneg_right ih (by norm_num)
        _ = _ := by rw [pow_succ]; ring
  have hdist (n : ℕ) : dist (s n).val (s (n + 1)).val ≤
      (17 / 16 * d x₀) * (1 / 4 : ℝ) ^ n := by
    rw [hsnext]
    calc
      _ ≤ d (s n).val + 4 * (d (s n).val) ^ 2 := (hnext (s n)).2
      _ ≤ 17 / 16 * d (s n).val := by
        have hp := hd0 (s n).val
        have hb := (s n).property
        nlinarith
      _ ≤ 17 / 16 * (d x₀ * (1 / 4 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left (hdecay n) (by norm_num)
      _ = _ := by ring
  have hc : CauchySeq (fun n => (s n).val) :=
    cauchySeq_of_le_geometric (1 / 4) (17 / 16 * d x₀) (by norm_num) hdist
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hc
  have hdz : Tendsto (fun n => d (s n).val) atTop (𝓝 0) := by
    have hgeom : Tendsto (fun n : ℕ => d x₀ * (1 / 4 : ℝ) ^ n) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one
          (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)))
    exact squeeze_zero (fun n => hd0 (s n).val) hdecay hgeom
  have hdy : d y = 0 := tendsto_nhds_unique (hd.continuousAt.tendsto.comp hy) hdz
  refine ⟨y, hdy, ?_⟩
  have hb := dist_le_of_le_geometric_of_tendsto₀ (1 / 4)
    (17 / 16 * d x₀) (by norm_num) hdist hy
  rw [hs0] at hb
  norm_num at hb
  have hp := hd0 x₀
  linarith

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CocycleMetric
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The complete metric space of uniformly bounded unitary families

The cocycle defect is continuous for the uniform norm. This supplies the
metric-space part of the boundary correction iteration.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction

noncomputable section

variable {G B : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable [CStarAlgebra B]

local instance instCompleteSpaceSubtypeBoundedContinuousFunctionMemSubmonoidUnitary_solutions_r1bbf29_1 : CompleteSpace (unitary (G →ᵇ B)) := isClosed_unitary.completeSpace_coe
theorem unitaryCocycleDefect_nonneg (α : G →* (B ≃⋆ₐ[ℂ] B))
    (V : unitary (G →ᵇ B)) : 0 ≤ unitaryCocycleDefect α V := norm_nonneg _

theorem unitaryCocycleDefect_eq_zero_iff (α : G →* (B ≃⋆ₐ[ℂ] B))
    (V : unitary (G →ᵇ B)) : unitaryCocycleDefect α V = 0 ↔
      ∀ g h, V.val g * α g (V.val h) = V.val (g * h) := by
  rw [unitaryCocycleDefect, norm_eq_zero]
  constructor
  · intro h g k
    exact sub_eq_zero.mp (congrArg (fun f : (G × G) →ᵇ B => f (g, k)) h)
  · intro h
    ext ⟨g, k⟩
    exact sub_eq_zero.mpr (h g k)

private theorem unitary_cocycle_error_difference_le
    (α : G →* (B ≃⋆ₐ[ℂ] B)) (V W : unitary (G →ᵇ B)) (g h : G) :
    ‖unitaryCocycleError α V (g, h) - unitaryCocycleError α W (g, h)‖ ≤
      3 * ‖V.val - W.val‖ := by
  let c := ‖V.val - W.val‖
  have he (g : G) : ‖V.val g - W.val g‖ ≤ c :=
    (V.val - W.val).norm_coe_le_norm g
  have hv : ‖α g (V.val h)‖ ≤ 1 :=
    norm_unitary_le_one (Unitary.map (StarMonoidHom.ofClass (α g)) (unitaryFamilyEval V h))
  have hw : ‖W.val g‖ ≤ 1 := norm_unitary_le_one (unitaryFamilyEval W g)
  have hα : ‖α g (V.val h - W.val h)‖ ≤ c := by
    have hi : ‖α g (V.val h - W.val h)‖ = ‖V.val h - W.val h‖ :=
      NonUnitalStarAlgHom.norm_map (α g).toStarAlgHom (α g).injective _
    rw [hi]
    exact he h
  change ‖(V.val g * α g (V.val h) - V.val (g * h)) -
    (W.val g * α g (W.val h) - W.val (g * h))‖ ≤ 3 * c
  have hid : (V.val g * α g (V.val h) - V.val (g * h)) -
      (W.val g * α g (W.val h) - W.val (g * h)) =
      (V.val g - W.val g) * α g (V.val h) +
        W.val g * α g (V.val h - W.val h) - (V.val (g * h) - W.val (g * h)) := by
    rw [map_sub]
    noncomm_ring
  rw [hid]
  calc
    _ ≤ ‖(V.val g - W.val g) * α g (V.val h)‖ +
        ‖W.val g * α g (V.val h - W.val h)‖ + ‖V.val (g * h) - W.val (g * h)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ c * 1 + 1 * c + c := by
      exact add_le_add (add_le_add
        ((norm_mul_le _ _).trans (mul_le_mul (he g) hv (norm_nonneg _) (norm_nonneg _)))
        ((norm_mul_le _ _).trans (mul_le_mul hw hα (norm_nonneg _) (by norm_num)))) (he _)
    _ = _ := by ring

theorem unitaryCocycleError_lipschitz (α : G →* (B ≃⋆ₐ[ℂ] B)) :
    LipschitzWith 3 (unitaryCocycleError α) := by
  apply LipschitzWith.of_dist_le_mul
  intro V W
  simp only [Subtype.dist_eq, dist_eq_norm]
  change ‖unitaryCocycleError α V - unitaryCocycleError α W‖ ≤
    (3 : ℝ) * ‖V.val - W.val‖
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  rintro ⟨g, h⟩
  exact unitary_cocycle_error_difference_le α V W g h

theorem continuous_unitaryCocycleDefect (α : G →* (B ≃⋆ₐ[ℂ] B)) :
    Continuous (unitaryCocycleDefect α) :=
  (unitaryCocycleError_lipschitz α).continuous.norm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryBoundedTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.Generator.vectorOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded transport fields and the correction step

For an action on a C-star algebra, the transport fields are actual bounded
unitary families.  An equivariant bimodule mean therefore gives the quadratic
step in the complete metric space of unitary families.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction CStarAlgebra

noncomputable section

variable {G B : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable [CStarAlgebra B]

local instance boundaryBoundedComplete : CompleteSpace (unitary (G →ᵇ B)) :=
  isClosed_unitary.completeSpace_coe

attribute [local instance] OAI.KadisonKastler.boundaryBoundedStarOrder
/-- The translation action agrees with the original action on constant fields. -/
theorem boundaryTranslate_constant (α : G →* (B ≃⋆ₐ[ℂ] B)) (g : G) (b : B) :
    boundaryTranslate α g (boundaryConstant (G := G) b) =
      boundaryConstant (G := G) (α g b) := by
  ext t
  rfl

/-- The exact pointwise transport factorization holds in the bounded algebra. -/
theorem boundedBoundaryTransport_factor (α : G →* (B ≃⋆ₐ[ℂ] B))
    (V : unitary (G →ᵇ B)) (g h : G) :
    (boundedBoundaryTransport α V (g * h) : G →ᵇ B) =
      (boundedBoundaryTransport α V g : G →ᵇ B) *
        boundaryTranslate α g (boundedBoundaryTransport α V h : G →ᵇ B) := by
  ext t
  exact boundaryTransport_factor α (unitaryFamilyEval V) g h t

/-- Each pointwise defect is bounded by its actual uniform norm. -/
theorem norm_unitaryCocycleError_le (α : G →* (B ≃⋆ₐ[ℂ] B))
    (V : unitary (G →ᵇ B)) (g h : G) :
    ‖V.val g * α g (V.val h) - V.val (g * h)‖ ≤ unitaryCocycleDefect α V :=
  (unitaryCocycleError α V).norm_coe_le_norm (g, h)

/-- The transport family is uniformly within the actual cocycle defect of
its constant value at the given group element. -/
theorem norm_boundedBoundaryTransport_sub_le (α : G →* (B ≃⋆ₐ[ℂ] B))
    (V : unitary (G →ᵇ B)) (g : G) :
    ‖(boundedBoundaryTransport α V g : G →ᵇ B) -
      boundaryConstant (G := G) (V.val g)‖ ≤ unitaryCocycleDefect α V := by
  apply (BoundedContinuousFunction.norm_le (unitaryCocycleDefect_nonneg α V)).mpr
  intro t
  exact norm_boundaryTransport_sub_le α (unitaryFamilyEval V)
    (norm_unitaryCocycleError_le α V) g t

attribute [local instance] OAI.KadisonKastler.boundaryBoundedCStar
attribute [local instance] OAI.KadisonKastler.boundaryBoundedOrder
/-- An equivariant bimodule mean gives the actual metric-space refinement,
with the precise defect and displacement constants. -/
theorem exists_bounded_cocycle_improvement
    (α : G →* (B ≃⋆ₐ[ℂ] B))
    (m : BimoduleMean (boundaryConstant (G := G) (B := B)))
    (hm : ∀ g f, m.toCLM (boundaryTranslate α g f) = α g (m.toCLM f))
    (V : unitary (G →ᵇ B)) (hV : unitaryCocycleDefect α V < 1) :
    ∃ W : unitary (G →ᵇ B),
      unitaryCocycleDefect α W ≤ 16 * (unitaryCocycleDefect α V) ^ 2 ∧
      dist V W ≤ unitaryCocycleDefect α V + 4 * (unitaryCocycleDefect α V) ^ 2 := by
  obtain ⟨W, hclose, hnew⟩ := m.exists_quadratic_improvement
    (fun g => α g) (boundaryTranslate α) hm (boundaryTranslate_constant α)
    (boundedBoundaryTransport α V) (unitaryFamilyEval V)
    (boundedBoundaryTransport_factor α V) (unitaryCocycleDefect_nonneg α V) hV
    (norm_boundedBoundaryTransport_sub_le α V)
  refine ⟨boundedUnitaryFamily W, ?_, ?_⟩
  · apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    rintro ⟨g, h⟩
    exact hnew g h
  · simp only [Subtype.dist_eq, dist_eq_norm]
    change ‖V.val - (boundedUnitaryFamily W).val‖ ≤ _
    apply (BoundedContinuousFunction.norm_le
      (add_nonneg (unitaryCocycleDefect_nonneg α V) (by positivity))).mpr
    intro g
    have hc := hclose g
    change ‖(W g : B) - V.val g‖ ≤ _ at hc
    simpa only [BoundedContinuousFunction.sub_apply, boundedUnitaryFamily_apply,
      norm_sub_rev] using hc

/-- Iterating the actual bounded-family step gives an exact cocycle.
The sole averaging premise is the explicitly supplied equivariant mean. -/
theorem exists_bounded_cocycle_of_equivariant_mean_oai
    (α : G →* (B ≃⋆ₐ[ℂ] B))
    (m : BimoduleMean (boundaryConstant (G := G) (B := B)))
    (hm : ∀ g f, m.toCLM (boundaryTranslate α g f) = α g (m.toCLM f))
    (V : unitary (G →ᵇ B)) (hV : unitaryCocycleDefect α V ≤ 1 / 64) :
    ∃ W : unitary (G →ᵇ B),
      (∀ g h, W.val g * α g (W.val h) = W.val (g * h)) ∧
      dist V W ≤ 2 * unitaryCocycleDefect α V := by
  obtain ⟨W, hzero, hdist⟩ := exists_zero_of_quadratic_improvement
    (unitaryCocycleDefect α) (continuous_unitaryCocycleDefect α)
    (unitaryCocycleDefect_nonneg α)
    (fun Z hZ => exists_bounded_cocycle_improvement α m hm Z (by linarith)) V hV
  exact ⟨W, (unitaryCocycleDefect_eq_zero_iff α W).mp hzero, hdist⟩

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.exists_bounded_cocycle_of_equivariant_mean_oai.{u_1, u_2} := @OAI.KadisonKastler.exists_bounded_cocycle_of_equivariant_mean_oai.{u_1, u_2}
