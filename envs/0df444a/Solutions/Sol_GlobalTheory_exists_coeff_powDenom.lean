-- Prove2me | solution 1 for GlobalTheory.exists_coeff_powDenom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:22:00.748986+00:00
-- url     : https://prove2.me/submissions/837aacd0-f3bd-41e2-af0c-bbd05e920053

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIsUnitMatrixOfPowSmulSpanInvert

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {S EE W RW Y : Type} [CommRing S] [CommRing EE]
    [CommRing W] [CommRing RW] [AddCommGroup Y] [Module RW Y] (a : S →+* EE) (ι : EE →+* RW)
    (c : W →+* RW) (ψ : S →+* W) (Q : S)
    (hc : ∀ s, ι (a s) = c (ψ s)) (hQ : IsUnit (a Q)) {q : ℕ} (x : Fin q → Y) (y : Y)
    (hy : ∃ (k : ℕ) (s : Fin q → S), c (ψ Q) ^ k • y = ∑ i, c (ψ (s i)) • x i) :
    ∃ E : Fin q → EE, (∀ i, E i ∈ powDenomSubring a Q) ∧ y = ∑ i, ι (E i) • x i := by
  obtain ⟨k, s, hs⟩ := hy
  obtain ⟨v, hv⟩ := (hQ.pow k).exists_left_inv
  refine ⟨fun i => v * a (s i), fun i => ⟨k, s i, ?_⟩, ?_⟩
  · rw [← mul_assoc, mul_comm _ v, hv, one_mul]
  · have : ∀ i, ι (v * a (s i)) • x i = ι v • (c (ψ (s i)) • x i) := by
      intro i
      rw [map_mul, mul_smul, hc]
    simp only [this]
    rw [← Finset.smul_sum, ← hs, ← hc, ← map_pow, ← mul_smul, ← map_mul, hv, map_one, one_smul]
end GlobalTheory
