-- Prove2me | solution 1 for GlobalTheory.T.pull_closed_form_class
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:23:22.719766+00:00
-- url     : https://prove2.me/submissions/915073c5-8b4d-4af9-aba7-ab9ac1bc1355

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PullClosedFormClass
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PullClosedFormClassStatement
import Theorems.Thm_GlobalTheory_AbCoh_pullHH1_clAll


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
theorem _root_.solution : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (hc : Closed1 (OAff s) = ⊤) (hc' : Closed1 (OAff s') = ⊤) (w : GlobForm s), pullHH1 h (clAll (OAff s) hc w) = clAll (OAff s') hc' (GlobalTheory.CechDR.pullForm h w) := by
  first | exact @GlobalTheory.AbCoh.pullHH1_clAll | exact GlobalTheory.AbCoh.pullHH1_clAll | (intros; apply GlobalTheory.AbCoh.pullHH1_clAll <;> assumption)
end _root_.GlobalTheory.T
