-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsRegular.finrank_DBK_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:50:01.241905+00:00
-- url     : https://prove2.me/submissions/07227bc4-a680-4e08-a535-330a38c7b9ef

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_Admissible
import Definitions.Def_GroundTheory_PAdicHodge_AdmissibleField
import Theorems.Thm_GroundTheory_PAdicHodge_finrank_DBK
import Theorems.Thm_GroundTheory_PAdicHodge_IsRegular_finrank_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open TensorProduct Module
variable (G F K B : Type*) [Group G] [Field F] [Field K] [CommRing B] [Algebra F K] [Algebra K B]
  [Algebra F B] [IsScalarTower F K B] [MulSemiringAction G B] [SMulCommClass G F B]
  [SMulCommClass G K B]
variable {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)
variable {G F K B}
variable [IsDomain B]
namespace GroundTheory.PAdicHodge
namespace IsRegular
theorem _root_.solution (h : IsRegular G F B)
    (hK : ∀ b : B, (∀ g : G, g • b = b) → ∃ k : K, algebraMap K B k = b) [FiniteDimensional F V] :
    finrank K (DBK G F K B ρ) ≤ finrank F V := by
  rw [finrank_DBK ρ hK]
  exact h.finrank_le ρ
end IsRegular
end GroundTheory.PAdicHodge
