-- Prove2me | solution 1 for GlobalTheory.NB.LT.algHom_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:02:40.021697+00:00
-- url     : https://prove2.me/submissions/69b22b4b-fd78-42c8-a91c-b10373a17791

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvdSubOfDvdSubX

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open GlobalTheory GlobalTheory.NB GlobalTheory.NB.LT
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ}
open PowerSeries
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ}
namespace GlobalTheory.NB.LT
namespace _root_.GlobalTheory.NB.LT
theorem _root_.solution {B : Type} [CommRing B] [Algebra R B] (σ : R⟦X⟧ →ₐ[R] B) (r : Polynomial R) :
    σ (r : R⟦X⟧) = Polynomial.aeval (σ X) r := by
  have e : σ.comp (Polynomial.coeToPowerSeries.algHom R) = Polynomial.aeval (σ X) :=
    Polynomial.algHom_ext (by simp)
  simpa using DFunLike.congr_fun e r
end _root_.GlobalTheory.NB.LT
end GlobalTheory.NB.LT
