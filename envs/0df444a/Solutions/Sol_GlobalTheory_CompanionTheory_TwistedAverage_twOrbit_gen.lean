-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TwistedAverage.twOrbit_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:42:54.034264+00:00
-- url     : https://prove2.me/submissions/1e5bc761-33bc-4df5-baec-6289693e37c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemTwKerIffAverage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TwistedAverage
open GlobalTheory.PRep
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.TwistedAverage
theorem _root_.solution (ρ : Representation ℂ G V) (L : Subgroup G) (θ : L →* ℂˣ) (w : V) (l t : L) :
    twOrbit ρ L θ (ρ (l : G) w - (θ l : ℂ) • w) t =
      (θ l : ℂ) • (twOrbit ρ L θ w (t * l) - twOrbit ρ L θ w t) := by
  simp only [twOrbit]
  have h : (θ l : ℂ) * (((θ (t * l))⁻¹ : ℂˣ) : ℂ) = (((θ t)⁻¹ : ℂˣ) : ℂ) := by
    rw [← Units.val_mul, map_mul, mul_inv, mul_comm (θ t)⁻¹, mul_inv_cancel_left]
  rw [smul_sub, smul_smul, h, Subgroup.coe_mul, map_mul, Module.End.mul_apply, map_sub, map_smul,
    smul_sub, smul_smul, smul_smul, mul_comm]
end GlobalTheory.CompanionTheory.TwistedAverage
