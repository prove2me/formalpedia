-- Prove2me | solution 1 for GlobalTheory.ThetaTranslSpan.exists_im_eq_lattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:39:47.090723+00:00
-- url     : https://prove2.me/submissions/7579b5e8-db96-4268-b48e-c59aa902922b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EntirePeriodicEqZeroOfFourierCoeffEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CardLePowOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CardLePowOfLinearIndependentThetaPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Theorems.Thm_GlobalTheory_ThetaTranslSpan_exists_im_eq
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
open Matrix
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaTranslSpan
variable {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}
namespace GlobalTheory.ThetaTranslSpan
theorem _root_.solution (hH : Hm.PosDef) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (hsp : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (φ : Λ →ₗ[ℤ] ℝ) :
    ∃ y, ∀ a : Λ, (star y ⬝ᵥ Hm.mulVec a).im = φ a := by
  haveI : IsZLattice ℝ Λ := ⟨hsp⟩
  let b := Module.Free.chooseBasis ℤ Λ
  let f := (b.ofZLatticeBasis ℝ Λ).constr ℝ (fun i => φ (b i))
  obtain ⟨y, hy⟩ := exists_im_eq hH f
  have : (f.restrictScalars ℤ) ∘ₗ Λ.subtype = φ := b.ext fun i => by
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.restrictScalars_apply]
    rw [← Module.Basis.ofZLatticeBasis_apply ℝ Λ b i, Module.Basis.constr_basis]
  exact ⟨y, fun a => by rw [hy, ← this]; rfl⟩
end GlobalTheory.ThetaTranslSpan
