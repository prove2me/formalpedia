-- Prove2me | solution 1 for GroundTheory.PAdicHodge.isAdmissible_iff_finrank_DBK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:50:10.803004+00:00
-- url     : https://prove2.me/submissions/f1e88fd5-0267-493e-b9ba-c05221e2213f

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_Admissible
import Definitions.Def_GroundTheory_PAdicHodge_AdmissibleField
import Theorems.Thm_GroundTheory_PAdicHodge_finrank_DBK

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
theorem _root_.solution
    (hK : ∀ b : B, (∀ g : G, g • b = b) → ∃ k : K, algebraMap K B k = b) :
    IsAdmissible B ρ ↔ finrank K (DBK G F K B ρ) = finrank F V := by
  rw [finrank_DBK ρ hK]
  rfl
end GroundTheory.PAdicHodge
