-- Prove2me | solution 1 for GroundTheory.Brauer.BrauerGroup.exists_mem_relBrauer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:42:23.713475+00:00
-- url     : https://prove2.me/submissions/7135039e-3e8a-4233-b0e0-83e8d68ab692

import Mathlib
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer
import Definitions.Def_GroundTheory_Brauer_Degree
import Definitions.Def_GroundTheory_Brauer_Splitting
import Theorems.Thm_GroundTheory_Brauer_exists_isGalois_splits
import Theorems.Thm_GroundTheory_Brauer_BrauerGroup_mk_mem_relBrauer_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open TensorProduct Module
universe u v w
variable {K : Type u} [Field K]
namespace GroundTheory.Brauer
namespace BrauerGroup
theorem _root_.solution (x : BrauerGroup.{u, u} K) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L), FiniteDimensional K L ∧ IsGalois K L ∧
      x ∈ BrauerGroup.relBrauer K L := by
  induction x using Quotient.inductionOn with
  | h A =>
    obtain ⟨L, _, _, h1, h2, n, ⟨e⟩⟩ := exists_isGalois_splits (K := K) A
    exact ⟨L, _, _, h1, h2, (BrauerGroup.mk_mem_relBrauer_iff A).mpr ⟨n, ⟨e⟩⟩⟩
end BrauerGroup
end GroundTheory.Brauer
