-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsRegular.finiteDimensional_DBK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:37:07.088973+00:00
-- url     : https://prove2.me/submissions/b1d74870-523e-4f61-9cb7-467346b419eb

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_Admissible
import Definitions.Def_GroundTheory_PAdicHodge_AdmissibleField
import Theorems.Thm_GroundTheory_PAdicHodge_rank_DBK

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
    FiniteDimensional K (DBK G F K B ρ) := by
  let := h.field
  have := h.free ρ
  have := h.finite ρ
  have : Module.Free K (DBK G F K B ρ) := Module.Free.of_divisionRing K (DBK G F K B ρ)
  exact Module.rank_lt_aleph0_iff.1 (by rw [rank_DBK ρ hK]; exact Module.rank_lt_aleph0_iff.2 ‹_›)
end IsRegular
end GroundTheory.PAdicHodge
