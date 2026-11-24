-- Prove2me | solution 1 for GlobalTheory.Proof.SplitPlaceGoodSignature.isSplitPl_of_not_isConjPl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:39:59.216137+00:00
-- url     : https://prove2.me/submissions/94f9bf19-1135-4f31-bb87-526ff694981a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_ThetaLiftOfEachRow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_HeckeSplitOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_SplitLiftOfLiftParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_SplitPlaceGoodSignature

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.SplitPlaceGoodSignature
open NumberField Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.ThetaExh
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
namespace GlobalTheory.Proof.SplitPlaceGoodSignature
theorem _root_.solution (w : IsDedekindDomain.HeightOneSpectrum (𝓞 H.E))
    (h : ¬ IsConjPl H w w) : IsSplitPl H w := by
  by_contra hs
  apply h
  let c : 𝓞 H.E →+* 𝓞 H.E := RingOfIntegers.mapRingHom (H.conj : H.E →+* H.E)
  have hc : ∀ x y : 𝓞 H.E, (y : H.E) = H.conj (x : H.E) → y = c x := fun x y hy =>
    RingOfIntegers.ext hy
  have hle : w.asIdeal ≤ w.asIdeal.comap c := by
    intro x hx
    by_contra hx'
    exact hs ⟨x, hx, fun y hy => by rw [hc x y hy]; exact hx'⟩
  have heq : w.asIdeal = w.asIdeal.comap c :=
    w.isMaximal.eq_of_le (Ideal.comap_ne_top c w.isPrime.ne_top) hle
  intro x y hy
  rw [hc x y hy, ← Ideal.mem_comap, ← heq]
end GlobalTheory.Proof.SplitPlaceGoodSignature
