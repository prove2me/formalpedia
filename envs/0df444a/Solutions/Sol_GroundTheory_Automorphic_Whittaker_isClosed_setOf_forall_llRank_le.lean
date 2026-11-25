-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.isClosed_setOf_forall_llRank_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:13:31.817156+00:00
-- url     : https://prove2.me/submissions/76e53ada-df19-46d3-8964-a104b9d53927

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
    IsClosed {g : GL (Fin n) F | ∀ i j, llRank i j g ≤ r i j} := by
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
  have : {g : GL (Fin n) F | llRank i j g ≤ r i j} = {g | r i j + 1 ≤ llRank i j g}ᶜ := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
    omega
  rw [this]
  exact (isOpen_setOf_le_llRank i j (r i j + 1)).isClosed_compl
end GroundTheory.Automorphic.Whittaker
