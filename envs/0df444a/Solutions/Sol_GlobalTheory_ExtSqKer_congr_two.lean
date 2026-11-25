-- Prove2me | solution 1 for GlobalTheory.ExtSqKer.congr_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:16:41.434238+00:00
-- url     : https://prove2.me/submissions/66941ec6-d9b2-455e-9c19-ae89daf0b5f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExteriorSquareKerOfSurjective
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ExtSqKer
variable {R : Type} [CommRing R] {M H Q : Type} [AddCommGroup M] [Module R M]
  [AddCommGroup H] [Module R H] [AddCommGroup Q] [Module R Q]
namespace GlobalTheory.ExtSqKer
theorem _root_.solution (p : M →ₗ[R] H) (F : M [⋀^Fin 2]→ₗ[R] Q)
    (hF : ∀ (u : Fin 2 → M) (j : Fin 2), p (u j) = 0 → F u = 0)
    (u u' : Fin 2 → M) (h : ∀ k, p (u k) = p (u' k)) : F u = F u' := by
  calc F u = F (Function.update u 0 (u 0)) := by rw [Function.update_eq_self]
    _ = F (Function.update u 0 (u' 0)) := upd_congr p F hF u 0 _ _ (h 0)
    _ = F (Function.update (Function.update u 0 (u' 0)) 1 ((Function.update u 0 (u' 0)) 1)) := by
        rw [Function.update_eq_self]
    _ = F (Function.update (Function.update u 0 (u' 0)) 1 (u' 1)) :=
        upd_congr p F hF _ 1 _ _ (by simpa using h 1)
    _ = F u' := by
        congr 1; ext k; fin_cases k <;> simp
end GlobalTheory.ExtSqKer
