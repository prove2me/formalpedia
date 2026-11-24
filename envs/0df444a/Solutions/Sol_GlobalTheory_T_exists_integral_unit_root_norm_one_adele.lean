-- Prove2me | solution 1 for GlobalTheory.T.exists_integral_unit_root_norm_one_adele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:08:21.730285+00:00
-- url     : https://prove2.me/submissions/6a760b7c-d1f6-42da-bba4-af8a62e16313

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIntegralUnitRootNormOneAdele
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIntegralUnitRootNormOneAdeleStatement
import Theorems.Thm_GlobalTheory_AdLat_exists_integral_unit_root


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 → (∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ t s : 𝓞 E, (s : E) = c (t : E) ∧ t - s ∉ P) → ∀ u ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), u * sg (FiniteAdeleRing (𝓞 F) F) c u = 1 → ∃ x ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), (∃ y ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), x * y = 1) ∧ x = u * sg (FiniteAdeleRing (𝓞 F) F) c x := by
  first | exact @GlobalTheory.AdLat.exists_integral_unit_root | exact GlobalTheory.AdLat.exists_integral_unit_root | (intros; apply GlobalTheory.AdLat.exists_integral_unit_root <;> assumption)
end _root_.GlobalTheory.T
