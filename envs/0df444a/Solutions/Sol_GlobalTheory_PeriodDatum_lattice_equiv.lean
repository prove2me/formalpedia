-- Prove2me | solution 1 for GlobalTheory.PeriodDatum.lattice_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:22:49.323918+00:00
-- url     : https://prove2.me/submissions/a10a2040-2b45-4538-b6f3-d2f322bda968

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HostGeneratorPowFourTraceNormModEight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TwoMulEqOfIsTypeFn
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_IsSymplecticBasisOfType_finrank_eq
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul
attribute [local simp] GlobalTheory.coe_symplecticGroupMap
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct
open GlobalTheory GlobalTheory.PeriodDatum
noncomputable section
namespace GlobalTheory.PeriodDatum
theorem _root_.solution {La : Type} [AddCommGroup La] {g : ℕ} (P : La →+ (Fin g → ℂ)) (hinj : Function.Injective P)
    (hdisc : DiscreteTopology P.range) (hspan : Submodule.span ℝ (Set.range P) = ⊤) :
    Module.Finite ℤ La ∧ Module.finrank ℤ La = 2 * g ∧
      ∃ e : ℝ ⊗[ℤ] La ≃ₗ[ℝ] (Fin g → ℂ), ∀ x, e (1 ⊗ₜ x) = P x := by
  let L : Submodule ℤ (Fin g → ℂ) := LinearMap.range P.toIntLinearMap
  haveI : DiscreteTopology L := hdisc
  haveI : IsZLattice ℝ L := ⟨hspan⟩
  let f : La ≃ₗ[ℤ] L := LinearEquiv.ofInjective P.toIntLinearMap hinj
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  haveI : Module.Free ℤ L := ZLattice.module_free ℝ L
  haveI : Module.Finite ℤ La := Module.Finite.equiv f.symm
  haveI : Module.Free ℤ La := Module.Free.of_equiv f.symm
  have hr : Module.finrank ℤ La = Module.finrank ℝ (Fin g → ℂ) := by
    rw [f.finrank_eq, ZLattice.rank ℝ L]
  have hg : Module.finrank ℝ (Fin g → ℂ) = 2 * g := by
    rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, Module.finrank_fin_fun]
  let φ : ℝ ⊗[ℤ] La →ₗ[ℝ] (Fin g → ℂ) := P.toIntLinearMap.liftBaseChange ℝ
  have hφ : ∀ x, φ (1 ⊗ₜ x) = P x := fun x => by simp [φ]
  have hs : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨_, hφ x⟩
  have hd : Module.finrank ℝ (ℝ ⊗[ℤ] La) = Module.finrank ℝ (Fin g → ℂ) := by
    rw [Module.finrank_baseChange, hr]
  exact ⟨inferInstance, hr.trans hg, LinearEquiv.ofBijective φ
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).2 hs, hs⟩, hφ⟩
end GlobalTheory.PeriodDatum
