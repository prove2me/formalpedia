-- Prove2me | solution 1 for LatticePrepro.QuadraticVerifier.enc_assignOf
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:28:10.38621+00:00
-- url     : https://prove2.me/submissions/94c4733c-3cdb-4296-b3e1-6a7728c0b744

import Mathlib
import Definitions.Def_LatticePrepro_Verifier_Quadratic

namespace LatticePrepro end LatticePrepro
namespace LatticePrepro.QuadraticVerifier end LatticePrepro.QuadraticVerifier

namespace LatticePrepro

namespace QuadraticVerifier

variable {p : ℕ} (V : QuadraticVerifier p)

lemma assignOf_zero (x : Fin V.n → Bool) (u : V.AuxIdx → ZMod p) : V.assignOf x u 0 = 1 := by
  simp [assignOf]

lemma assignOf_apply_of_le (x : Fin V.n → Bool) (u : V.AuxIdx → ZMod p) {i : Fin (V.S + 1)}
    (h0 : i.val ≠ 0) (hn : i.val ≤ V.n) :
    V.assignOf x u i = if x ⟨i.val - 1, by omega⟩ then 1 else 0 := by
  simp only [assignOf, h0, hn, ↓reduceDIte]

lemma assignOf_apply_of_eq (x : Fin V.n → Bool) (u : V.AuxIdx → ZMod p) {i : Fin (V.S + 1)}
    (h : i.val = V.n + 1) : V.assignOf x u i = 1 := by
  simp [assignOf, h]

lemma assignOf_apply_of_lt (x : Fin V.n → Bool) (u : V.AuxIdx → ZMod p) {i : Fin (V.S + 1)}
    (h : V.n + 1 < i.val) : V.assignOf x u i = u ⟨i, h⟩ := by
  have h0 : i.val ≠ 0 := by omega
  have hn : ¬ i.val ≤ V.n := by omega
  have hout : i.val ≠ V.n + 1 := by omega
  simp only [assignOf, h0, hn, hout, ↓reduceDIte]

end QuadraticVerifier

namespace QuadraticVerifier

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
  (V : QuadraticVerifier p) (ε : EncodingTuple p K V.S)

/-- The encoding of `assignOf x u` is `θ_x` plus the auxiliary contribution. -/
private lemma enc_assignOf (x : Fin V.n → Bool) (u : V.AuxIdx → ZMod p) :
    ε.enc (V.assignOf x u) = V.instanceEnc ε x + ∑ i : V.AuxIdx, u i • ε.E i.1 := by
  classical
  unfold instanceEnc EncodingTuple.enc
  -- extend `u` by zero to all coordinates
  let u' : Fin (V.S + 1) → ZMod p := fun i => if h : V.n + 1 < i.val then u ⟨i, h⟩ else 0
  have key : ∀ i : Fin (V.S + 1), V.assignOf x u i • ε.E i =
      V.assignOf x 0 i • ε.E i + u' i • ε.E i := by
    intro i
    by_cases h : V.n + 1 < i.val
    · simp only [u', h, ↓reduceDIte]
      rw [V.assignOf_apply_of_lt x u h, V.assignOf_apply_of_lt x 0 h]
      simp
    · simp only [u', h, ↓reduceDIte, zero_smul, add_zero]
      by_cases hi : i.val = 0
      · rw [show i = 0 from Fin.ext hi, V.assignOf_zero, V.assignOf_zero]
      by_cases hn : i.val ≤ V.n
      · rw [V.assignOf_apply_of_le x u hi hn, V.assignOf_apply_of_le x 0 hi hn]
      · rw [V.assignOf_apply_of_eq x u (by omega), V.assignOf_apply_of_eq x 0 (by omega)]
  simp_rw [key]
  rw [Finset.sum_add_distrib]
  congr 1
  have h1 : ∑ i : V.AuxIdx, u i • ε.E i.1 = ∑ i : V.AuxIdx, u' i.1 • ε.E i.1 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [u', i.2]
  rw [h1, ← Finset.sum_subtype (Finset.univ.filter fun i : Fin (V.S + 1) => V.n + 1 < i.val)
    (by simp) (fun i => u' i • ε.E i), Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : V.n + 1 < i.val
  · simp [h]
  · simp [u', h]

end QuadraticVerifier

end LatticePrepro

open LatticePrepro
open LatticePrepro.QuadraticVerifier
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
  (V : QuadraticVerifier p) (ε : EncodingTuple p K V.S)
theorem solution (x : Fin V.n → Bool) (u : V.AuxIdx → ZMod p) :
    ε.enc (V.assignOf x u) = V.instanceEnc ε x + ∑ i : V.AuxIdx, u i • ε.E i.1 :=
  @LatticePrepro.QuadraticVerifier.enc_assignOf p _ K _ _ V ε x u
