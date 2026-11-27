-- Prove2me | solution 1 for GroundTheory.Automorphic.Iwasawa.borel_mul_integralGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:44:35.208631+00:00
-- url     : https://prove2.me/submissions/393734bd-076b-4e45-b202-2e94aab41912

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open ValuativeRel Matrix Filter
open scoped Pointwise
open GroundTheory.Automorphic.Iwasawa
open GLnLocal
variable (F : Type*) [Field F] (n : ℕ)
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.Iwasawa
theorem _root_.solution :
    (borel F n : Set (GL (Fin n) F)) * (integralGL F n : Set (GL (Fin n) F)) = Set.univ := by
  refine Set.eq_univ_of_forall fun g => ?_
  obtain ⟨b, hb, k, hk, rfl⟩ := exists_borel_mul_integralGL F n g
  exact Set.mul_mem_mul hb hk
end GroundTheory.Automorphic.Iwasawa
