-- Prove2me | solution 1 for GlobalTheory.NB.TypedOnto.jumps_width
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:05:17.456106+00:00
-- url     : https://prove2.me/submissions/cd05080b-e581-45ba-9655-e6891885a781

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_RoundDown
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_OfKillsOne

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
open GlobalTheory GlobalTheory.NB
variable {l : ℕ} {O : Type} [CommRing O] [IsDomain O] {R : Fr l O} {n r₁ r : ℕ}
variable {S₁ : Sys R n r₁} {S : Sys R n r} {F : Hom S₁ S}
namespace GlobalTheory.NB
namespace TypedOnto
theorem _root_.solution {up : ZMod n → Fin R.e → Bool} {b : ZMod n → Fin R.e → ℕ}
    {Sn η m h : ℕ} (H : TypedOnto F up b Sn η m h) (i : ZMod n) (τ : Fin R.e) :
    S₁.JumpsIn i τ (Set.Icc (-((if up i τ then η else b i τ + Sn : ℕ) : ℤ))
      ((if up i τ then b i τ + Sn else η : ℕ) : ℤ)) := by
  intro a ha
  have h1 := H.jumps i τ a ha
  have h2 := H.size i τ
  unfold win winU winD at h1
  cases hu : up i τ <;> simp [hu] at h1 ⊢ <;> omega
end TypedOnto
end GlobalTheory.NB
