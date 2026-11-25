-- Prove2me | solution 1 for GlobalTheory.T.exists_algClosed_transcendental_specialising_everywhere
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:14:45.43509+00:00
-- url     : https://prove2.me/submissions/0bd0b516-9ed1-4bac-8ea6-d30b6a6acc05

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAlgClosedTranscendentalSpecialisingEverywh
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAlgClosedTranscendentalSpecialisingEverywhStatement
import Theorems.Thm_GlobalTheory_genval


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [IsAlgClosed K], ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (ι : K →+* L) (s : L), (∀ P : Polynomial K, P.eval₂ ι s = 0 → P = 0) ∧ ∀ a : K, ∃ (V : ValuationSubring L) (ιV : K →+* V) (r : V →+* K) (sV : V), (algebraMap V L).comp ιV = ι ∧ r.comp ιV = RingHom.id K ∧ RingHom.ker r = IsLocalRing.maximalIdeal V ∧ algebraMap V L sV = s ∧ r sV = a := by
  first | exact @GlobalTheory.genval | exact GlobalTheory.genval | (intros; apply GlobalTheory.genval <;> assumption)
end _root_.GlobalTheory.T
