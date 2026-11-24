-- Prove2me | solution 1 for GlobalTheory.CoefEmbed.norm_prime_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:13:34.490603+00:00
-- url     : https://prove2.me/submissions/1a2778f0-b64a-43a6-9aec-eaccde323174

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EmbeddingClosedIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CoefEmbed
open IsLocalRing Topology
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
open IsLocalRing Topology
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
namespace GlobalTheory.CoefEmbed
namespace _root_.GlobalTheory.CoefEmbed
theorem _root_.solution : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
  have h : ((l : ℕ) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']
  exact Padic.norm_p_lt_one
end _root_.GlobalTheory.CoefEmbed
end GlobalTheory.CoefEmbed
