-- Prove2me | solution 1 for GlobalTheory.CoprimeNatNotMem.natCast_not_mem_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:37:44.433547+00:00
-- url     : https://prove2.me/submissions/df50234c-f0b1-4c2b-8146-56cc71938a54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatCastNotMemOfCoprime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.CoprimeNatNotMem
namespace GlobalTheory.CoprimeNatNotMem
theorem _root_.solution {Rg : Type u_1} [CommRing Rg] {P : Ideal Rg} (hP : P ≠ ⊤)
    {p n : ℕ} (h : Nat.Coprime p n) (hp : (p : Rg) ∈ P) : (n : Rg) ∉ P := by
  intro hn

  obtain ⟨u, v, huv⟩ : IsCoprime (p : Rg) (n : Rg) := by
    have hz : IsCoprime (p : ℤ) (n : ℤ) := Nat.isCoprime_iff_coprime.mpr h
    simpa using hz.map (Int.castRingHom Rg)
  apply hP
  rw [Ideal.eq_top_iff_one, ← huv]
  exact P.add_mem (P.mul_mem_left u hp) (P.mul_mem_left v hn)
end GlobalTheory.CoprimeNatNotMem
