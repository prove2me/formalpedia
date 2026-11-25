-- Prove2me | solution 1 for GlobalTheory.eq_zero_of_sum_smul_eq_zero_of_powDenom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:21:22.433073+00:00
-- url     : https://prove2.me/submissions/20cf02c3-f649-4f94-b450-be4634f1258d

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
    (c : W →+* RW) (ψ : S →+* W) (Q : S) (hι : Function.Injective ι)
    (hc : ∀ s, ι (a s) = c (ψ s)) (hQ : IsUnit (a Q)) {q : ℕ} (x : Fin q → Y)
    (hx : ∀ w : Fin q → W, ∑ i, c (w i) • x i = 0 → w = 0) (E : Fin q → EE)
    (hE : ∀ m, E m ∈ powDenomSubring a Q) (h0 : ∑ m, ι (E m) • x m = 0) (m : Fin q) :
    E m = 0 := by
  choose n t ht using hE
  set N := ∑ m, n m with hN
  have hle : ∀ m, n m ≤ N := fun m =>
    Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)
  have h1 : ∀ m, a Q ^ N * E m = a (Q ^ (N - n m) * t m) := by
    intro m
    rw [map_mul, map_pow, ← ht, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (hle m)]
  have h2 := hx (fun m => ψ (Q ^ (N - n m) * t m)) (by
    have : ∀ m, c (ψ (Q ^ (N - n m) * t m)) • x m = ι (a Q ^ N) • (ι (E m) • x m) := by
      intro m
      rw [← hc, ← h1, map_mul, mul_smul]
    simp only [this]
    rw [← Finset.smul_sum, h0, smul_zero])
  have h3 : ψ (Q ^ (N - n m) * t m) = 0 := congrFun h2 m
  have h4 : a Q ^ N * E m = 0 := by
    apply hι
    rw [h1, hc, h3, map_zero, map_zero]
  exact ((hQ.pow N).mul_right_eq_zero).1 h4
end GlobalTheory
