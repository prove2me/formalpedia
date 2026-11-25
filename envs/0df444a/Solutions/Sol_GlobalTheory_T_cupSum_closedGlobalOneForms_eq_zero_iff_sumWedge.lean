-- Prove2me | solution 1 for GlobalTheory.T.cupSum_closedGlobalOneForms_eq_zero_iff_sumWedge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:31:45.680914+00:00
-- url     : https://prove2.me/submissions/eb84497d-fab3-4a29-9154-1be65a316253

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CupSumClosedGlobalOneFormsEqZeroIffSumWedge
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CupSumClosedGlobalOneFormsEqZeroIffSumWedgeStatement
import Theorems.Thm_GlobalTheory_AbCoh_cupSum_eq_zero_iff_wsum_eq_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_toO


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), ∀ hc : Closed1 F = ⊤, Function.Surjective (toO F) → ∀ (n : ℕ) (u v : Fin n → Glob1 F), ∑ k, cupHyp F (clAll F hc (u k)) (clAll F hc (v k)) = 0 ↔ wsum F u v = 0 := by
  first | exact @GlobalTheory.AbCoh.cupSum_eq_zero_iff_wsum_eq_zero | exact GlobalTheory.AbCoh.cupSum_eq_zero_iff_wsum_eq_zero | (intros; apply GlobalTheory.AbCoh.cupSum_eq_zero_iff_wsum_eq_zero <;> assumption)
end _root_.GlobalTheory.T
