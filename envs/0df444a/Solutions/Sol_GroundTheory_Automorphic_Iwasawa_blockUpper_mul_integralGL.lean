-- Prove2me | solution 1 for GroundTheory.Automorphic.Iwasawa.blockUpper_mul_integralGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:44:31.725935+00:00
-- url     : https://prove2.me/submissions/1254980f-a965-4158-bb96-15f863e5d903

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_exists_blockUpper_mul_integralGL

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
theorem _root_.solution {α : Type*} [LinearOrder α] {β : Fin n → α}
    (hβ : Monotone β) :
    (blockUpper F n β : Set (GL (Fin n) F)) * (integralGL F n : Set (GL (Fin n) F)) =
      Set.univ := by
  refine Set.eq_univ_of_forall fun g => ?_
  obtain ⟨p, hp, k, hk, rfl⟩ := exists_blockUpper_mul_integralGL F n hβ g
  exact Set.mul_mem_mul hp hk
end GroundTheory.Automorphic.Iwasawa
