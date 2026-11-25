-- Prove2me | solution 1 for GlobalTheory.T.isArtinianLocal_length_finite_and_exists_socle_elem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:22:36.586407+00:00
-- url     : https://prove2.me/submissions/007ff8a7-94d8-4635-b51e-6f15904c411c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ArtinianLocalFiniteLengthAndSocleElement
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ArtinianLocalFiniteLengthAndSocleElementStatement
import Theorems.Thm_GlobalTheory_artinianLocal_finiteLength_and_socle_element


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
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsArtinianRing R] [IsLocalRing R], (∃ n : ℕ, Module.length R R = n) ∧ (¬ IsField R → ∃ t : R, t ≠ 0 ∧ (∀ a ∈ IsLocalRing.maximalIdeal R, a * t = 0) ∧ Module.length (R ⧸ Ideal.span {t}) (R ⧸ Ideal.span {t}) < Module.length R R) := by
  first | exact @GlobalTheory.artinianLocal_finiteLength_and_socle_element | exact GlobalTheory.artinianLocal_finiteLength_and_socle_element | (intros; apply GlobalTheory.artinianLocal_finiteLength_and_socle_element <;> assumption)
end _root_.GlobalTheory.T
