-- Prove2me | solution 1 for GlobalTheory.T.spec_localRing_hom_ext_of_injective_localHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:38:16.976306+00:00
-- url     : https://prove2.me/submissions/0f7a040c-e4ef-4286-99eb-db382d4a7342

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecLocalRingHomExtOfInjectiveLocalHom
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_SRelOneOneIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecLocalRingHomExtOfInjectiveLocalHomStatement
import Theorems.Thm_GlobalTheory_spec_local_hom_ext_of_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (φ : R →+* R'), IsLocalHom φ → Function.Injective φ → ∀ (Y : Scheme.{0}) (x y : Sp R ⟶ Y), spMap φ ≫ x = spMap φ ≫ y → x = y := by
  first | exact @GlobalTheory.spec_local_hom_ext_of_injective | exact GlobalTheory.spec_local_hom_ext_of_injective | (intros; apply GlobalTheory.spec_local_hom_ext_of_injective <;> assumption)
end _root_.GlobalTheory.T
