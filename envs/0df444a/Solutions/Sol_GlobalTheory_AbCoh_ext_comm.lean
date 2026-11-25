-- Prove2me | solution 1 for GlobalTheory.AbCoh.ext_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:01:22.407895+00:00
-- url     : https://prove2.me/submissions/3030db5b-d9e1-48fc-9428-19b585a32f0d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NonemptyStructureSheafCohomologyModelOfQuasiIso
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_TopForm_formMap_dForm
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.TopForm.formMap_dForm
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbCoh
variable {R : Type} [CommRing R] {K C : CochainComplex (ModuleCat.{0} R) ℕ} (φ : K ⟶ C)
  (R' : Type) [CommRing R'] [Algebra R R']
namespace GlobalTheory.AbCoh
theorem _root_.solution {R'' : Type} [CommRing R''] [Algebra R R''] (α : R' →ₐ[R] R'') (i : ℕ) (y : R' ⊗[R] K.X i) :
    (φ.f i).hom.baseChange R'' (ext α _ y) = ext α _ ((φ.f i).hom.baseChange R' y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp [ext]
  | add x y hx hy => simp only [map_add, hx, hy]
end GlobalTheory.AbCoh
