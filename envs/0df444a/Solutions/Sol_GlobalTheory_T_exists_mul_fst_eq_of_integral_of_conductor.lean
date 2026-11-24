-- Prove2me | solution 1 for GlobalTheory.T.exists_mul_fst_eq_of_integral_of_conductor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:42:44.657805+00:00
-- url     : https://prove2.me/submissions/b051931e-e478-4d60-8b92-8e14090e3d14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ConductorProdFst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ConductorProdFstStatement
import Theorems.Thm_GlobalTheory_conductor_prod_fst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R S' S : Type) [CommRing R] [CommRing S'] [CommRing S] (e : S ≃+* R × S') (d : S), (∀ c : FractionRing S, IsIntegral S c → ∃ s : S, algebraMap S (FractionRing S) s = algebraMap S (FractionRing S) d * c) → ∀ c : FractionRing R, IsIntegral R c → ∃ s : R, algebraMap R (FractionRing R) s = algebraMap R (FractionRing R) (e d).1 * c := by
  first | exact @GlobalTheory.conductor_prod_fst | exact GlobalTheory.conductor_prod_fst | (intros; apply GlobalTheory.conductor_prod_fst <;> assumption)
end _root_.GlobalTheory.T
