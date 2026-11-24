-- Prove2me | solution 1 for GlobalTheory.exists_form_range_matrixUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:16:16.984804+00:00
-- url     : https://prove2.me/submissions/fec52ef0-8bce-4489-9425-b888e9e15e21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_UnimodularSymplecticCoordinatesAndLatticeRank
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSiegelForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsEquivPiRangeOfMatrixUnits
import Theorems.Thm_GlobalTheory_exists_equiv_pi_range_of_matrixUnits
import Theorems.Thm_GlobalTheory_matrixUnits_apply
import Theorems.Thm_GlobalTheory_form_matrixUnits_eq
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {La : Type} [AddCommGroup La] (G : Matrix (Fin 8) (Fin 8) ℤ)
    (EF : LinearMap.BilinForm ℤ La) (r : Matrix (Fin 8) (Fin 8) ℤ →+* Module.End ℤ La)
    (hG : G 0 0 ≠ 0) (hdet : G.det = 1) (hb : Function.Bijective EF) (halt : ∀ x, EF x x = 0)
    (hadj : ∀ a a', a.transpose * G = G * a' → ∀ x y, EF (r a x) y = EF x (r a' y)) :
    ∃ (φ : La ≃ₗ[ℤ] (Fin 8 → LinearMap.range (r (Matrix.single 0 0 1))))
      (E : LinearMap.BilinForm ℤ (LinearMap.range (r (Matrix.single 0 0 1)))),
      (∀ x u, (φ x u : La) = r (Matrix.single 0 u 1) x) ∧ Function.Bijective E ∧ (∀ x, E x x = 0) ∧
      (∀ x y, EF x y = ∑ u, ∑ v, G u v * E (φ x u) (φ y v)) ∧
      ∀ x y : LinearMap.range (r (Matrix.single 0 0 1)), EF x y = G 0 0 * E x y := by
  obtain ⟨h1, h2, h3⟩ := matrixUnits_apply r
  obtain ⟨φ, hφ, hφ'⟩ := exists_equiv_pi_range_of_matrixUnits (fun u => r (Matrix.single 0 u 1))
    (fun u => r (Matrix.single u 0 1)) (r (Matrix.single 0 0 1)) h1 h2 h3
  have hu : IsUnit G.det := by simp [hdet]
  let E : LinearMap.BilinForm ℤ (LinearMap.range (r (Matrix.single 0 0 1))) :=
    EF.compl₁₂ (Submodule.subtype _) (r (G⁻¹ * Matrix.single 0 0 1) ∘ₗ Submodule.subtype _)
  have hE : ∀ x y, E x y = EF x (r (G⁻¹ * Matrix.single 0 0 1) y) := fun _ _ => rfl
  have hsum : ∀ x y, EF x y = ∑ u, ∑ v, G u v * E (φ x u) (φ y v) := fun x y => by
    conv_lhs => rw [hφ' x, hφ' y]
    simp only [map_sum, LinearMap.sum_apply, form_matrixUnits_eq G EF r hdet hadj, hE]
    rw [Finset.sum_comm]
  have hfix : ∀ x : LinearMap.range (r (Matrix.single 0 0 1)), r (Matrix.single 0 0 1) x = x := by
    rintro ⟨_, z, rfl⟩; exact h3 z
  have h00 : ∀ x y : LinearMap.range (r (Matrix.single 0 0 1)), EF x y = G 0 0 * E x y :=
    fun x y => by
      rw [hE, ← form_matrixUnits_eq G EF r hdet hadj, hfix, hfix]
  refine ⟨φ, E, hφ, ⟨(injective_iff_map_eq_zero E).2 fun x hx => ?_, fun f => ?_⟩, fun x => ?_,
    hsum, h00⟩
  · have : EF (φ.symm (Pi.single 0 x)) = 0 := by
      ext y
      rw [hsum]
      refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v _ => ?_
      rw [LinearEquiv.apply_symm_apply]
      by_cases h : u = 0
      · subst h; simp [hx]
      · simp [h]
    have h0 := (injective_iff_map_eq_zero EF).1 hb.1 _ this
    have := congrFun (φ.symm.map_eq_zero_iff.1 h0) 0
    simpa using this
  · obtain ⟨x, hx⟩ := hb.2 (∑ v, G 0 v • (f ∘ₗ LinearMap.proj v ∘ₗ φ.toLinearMap))
    refine ⟨φ x 0, LinearMap.ext fun y => ?_⟩
    have key : ∀ v, ∑ u, E (φ x u) y * G u v = f y * G 0 v := fun v => by
      have := LinearMap.congr_fun hx (φ.symm (Pi.single v y))
      rw [hsum] at this
      simpa [Pi.single_apply, apply_ite, mul_comm] using this
    have k2 : Matrix.vecMul (fun u => E (φ x u) y) G = Matrix.vecMul (Pi.single 0 (f y)) G := by
      funext v
      rw [Matrix.single_vecMul]
      exact key v
    have k3 := congrArg (fun w => Matrix.vecMul w G⁻¹ 0) k2
    simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one] at k3
    simpa using k3
  · have := h00 x x
    rw [halt] at this
    exact (mul_eq_zero.1 this.symm).resolve_left hG
end GlobalTheory
