-- Prove2me | solution 1 for GlobalTheory.T.spec_functions_eq_of_restrictions_on_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:22:25.26118+00:00
-- url     : https://prove2.me/submissions/7c61a724-bd63-414e-80ee-1f28cbbbf5a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecFunctionsEqOfRestrictionsOnPairs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecPullA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecFunctionsEqOfRestrictionsOnPairsStatement
import Theorems.Thm_GlobalTheory_CechDR_AffLoc_eq_of_secMap_eq_on_pairs


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {X : Scheme.{0}} (B B' : Type) [CommRing B] [CommRing B'] (x : Sp B ⟶ X) (ψ : Sp B' ⟶ Sp B) (a b : B'), (∀ (V' : (Sp B').affineOpens) (p : Pair x), V'.1 ≤ ψ ⁻¹ᵁ p.1.1.1 → (secMap (𝟙 (Sp B')) V'.1).hom a = (secMap (𝟙 (Sp B')) V'.1).hom b) → a = b := by
  first | exact @GlobalTheory.CechDR.AffLoc.eq_of_secMap_eq_on_pairs | exact GlobalTheory.CechDR.AffLoc.eq_of_secMap_eq_on_pairs | (intros; apply GlobalTheory.CechDR.AffLoc.eq_of_secMap_eq_on_pairs <;> assumption)
end _root_.GlobalTheory.T
