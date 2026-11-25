-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.isOpen_setOf_forall_le_llRank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:13:33.794807+00:00
-- url     : https://prove2.me/submissions/4ddf21f2-3d8e-476f-bbe9-9138862bce67

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_isOpen_setOf_le_llRank
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
variable [TopologicalSpace F] [IsTopologicalRing F] [T1Space F]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (r : Fin n → Fin n → ℕ) :
    IsOpen {g : GL (Fin n) F | ∀ i j, r i j ≤ llRank i j g} := by
  simp only [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    isOpen_setOf_le_llRank i j (r i j)
end GroundTheory.Automorphic.Whittaker
