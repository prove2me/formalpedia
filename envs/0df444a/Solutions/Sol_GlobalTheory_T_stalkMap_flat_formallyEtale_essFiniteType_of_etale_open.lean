-- Prove2me | solution 1 for GlobalTheory.T.stalkMap_flat_formallyEtale_essFiniteType_of_etale_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:33:39.893176+00:00
-- url     : https://prove2.me/submissions/a9c08652-498d-4d63-8920-f46e94bf1929

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleRes
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleResStatement
import Theorems.Thm_GlobalTheory_stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (M W : Scheme.{0}) (f : M ⟶ W) (U : M.Opens), Etale (U.ι ≫ f) → ∀ y ∈ U, (f.stalkMap y).hom.Flat ∧ (f.stalkMap y).hom.FormallyEtale ∧ (f.stalkMap y).hom.EssFiniteType := by
  first | exact @GlobalTheory.stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict | exact GlobalTheory.stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict | (intros; apply GlobalTheory.stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict <;> assumption)
end _root_.GlobalTheory.T
