-- Prove2me | solution 1 for GroundTheory.PAdicHodge.finrank_DBK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:37:08.452094+00:00
-- url     : https://prove2.me/submissions/08adb607-2861-401c-8359-6ab245dbac38

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_Admissible
import Definitions.Def_GroundTheory_PAdicHodge_AdmissibleField
import Theorems.Thm_GroundTheory_PAdicHodge_coe_toInvariantRing
import Theorems.Thm_GroundTheory_PAdicHodge_rank_DBK
import Theorems.Thm_GroundTheory_PAdicHodge_IsRegular_coe_basisOfIsAdmissible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.IsRegular.coe_basisOfIsAdmissible


attribute [local simp] GroundTheory.PAdicHodge.coe_toInvariantRing

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open TensorProduct Module
variable (G F K B : Type*) [Group G] [Field F] [Field K] [CommRing B] [Algebra F K] [Algebra K B]
  [Algebra F B] [IsScalarTower F K B] [MulSemiringAction G B] [SMulCommClass G F B]
  [SMulCommClass G K B]
variable {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)
variable {G F K B}
namespace GroundTheory.PAdicHodge
theorem _root_.solution [Nontrivial B]
    (hK : ∀ b : B, (∀ g : G, g • b = b) → ∃ k : K, algebraMap K B k = b) :
    finrank K (DBK G F K B ρ) = finrank (invariantRing G F B) (DB B ρ) := by
  simp only [Module.finrank, rank_DBK ρ hK]
end GroundTheory.PAdicHodge
