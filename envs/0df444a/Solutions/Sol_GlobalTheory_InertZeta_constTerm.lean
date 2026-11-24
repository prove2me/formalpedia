-- Prove2me | solution 1 for GlobalTheory.InertZeta.constTerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:43:52.253836+00:00
-- url     : https://prove2.me/submissions/a2ed003b-e48e-4318-9930-a005dea37843

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumSpherical
import Theorems.Thm_GlobalTheory_InertZeta_det_mat_ne_zero
import Theorems.Thm_GlobalTheory_InertZeta_len_mat_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {ϖ : L} {q N : ℕ}
namespace GlobalTheory.InertZeta
theorem _root_.solution (hF : FracExists) (hP : Pointwise) (hC : Count) (hS : SmallCorner) (hG : GenFun)
    (hU : IsUnramInv ϖ σ q) {a : ℤ} {g₀ : GU σ N} {m : GU σ (N + 2)} (hm : IsLeviElt ϖ a g₀ m) (X : ℂ)
    (hX : ‖(q : ℂ) ^ (N + 1) * X‖ < 1) :
    HasSum (fun c : RadQuot σ N => X ^ len (mat (m * (c.out : radQ σ N).1)))
      ((q : ℂ) ^ (2 * len (mat g₀) + (2 * N + 2) * a.toNat) * X ^ (a.natAbs + len (mat g₀)) * jFac q N X) := by
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  have hq : 1 ≤ q := le_trans (by norm_num) hU.2.2.2.2.2.1
  obtain ⟨U, V, C, hfr, hdet⟩ := hF L ϖ N hv (mat g₀) (det_mat_ne_zero g₀)
  have hPt := hP L ϖ σ q N hU a g₀ m hm U V C (len (mat g₀)) hfr hdet
  have hcard : ∀ j : ℕ, Nat.card {c : RadQuot σ N //
      len (mat (m * (c.out : radQ σ N).1)) ≤ a.natAbs + len (mat g₀) + j} =
      q ^ (2 * len (mat g₀) + (2 * N + 2) * a.toNat) * q ^ (2 * N * (j / 2) + j) := by
    intro j
    have hiff : ∀ c : RadQuot σ N, len (mat (m * (c.out : radQ σ N).1)) ≤ a.natAbs + len (mat g₀) + j ↔
        Small ϖ (a.toNat + j / 2) (2 * a.toNat + j) C (C * V * mat g₀) (c.out : radQ σ N).1 :=
      fun c => (hPt _ (c.out : radQ σ N).2).2 j
    rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
    rw [hC L ϖ σ q N hU C (C * V * mat g₀) (len (mat g₀)) (a.toNat + j / 2) (2 * a.toNat + j) hfr.2.2.1 hdet
      (fun r hr => hS L ϖ σ q N hU g₀ U V C hfr _ _ r (by omega) hr) ?_]
    · rw [← pow_add]; congr 1; generalize j / 2 = t; ring
    · intro u hu k hk hkK hsm
      have hlen : len (mat (m * (u * k))) = len (mat (m * u)) := by
        have h := len_mat_mul (KU σ (N + 2)).one_mem hkK (m * u)
        rwa [one_mul, mul_assoc] at h
      refine ((hPt _ (mul_mem hu hk)).2 j).mp ?_
      rw [hlen]
      exact ((hPt u hu).2 j).mpr hsm
  have key := hG (RadQuot σ N) (fun c => len (mat (m * (c.out : radQ σ N).1))) (a.natAbs + len (mat g₀))
    (q ^ (2 * len (mat g₀) + (2 * N + 2) * a.toNat)) q N X (Nat.one_le_pow _ _ hq) hq
    (fun c => (hPt _ (c.out : radQ σ N).2).1) hcard hX
  push_cast at key
  exact key
end GlobalTheory.InertZeta
