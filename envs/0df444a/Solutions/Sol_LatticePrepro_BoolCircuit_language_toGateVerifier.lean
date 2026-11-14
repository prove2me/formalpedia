-- Prove2me | solution 1 for LatticePrepro.BoolCircuit.language_toGateVerifier
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:28:18.237673+00:00
-- url     : https://prove2.me/submissions/2556a931-8141-4148-8cfd-23f556ca0342

import Mathlib
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Verifier_Gates
import Definitions.Def_LatticePrepro_Verifier_Circuit

namespace LatticePrepro end LatticePrepro
namespace LatticePrepro.BoolCircuit end LatticePrepro.BoolCircuit

namespace LatticePrepro

namespace BoolCircuit

variable (C : BoolCircuit)

lemma evalAux_input (x : Fin C.n → Bool) (wit : Fin C.w → Bool) {i : ℕ} (h : i < C.n) :
    C.evalAux x wit i = x ⟨i, h⟩ := by
  rw [evalAux]; simp [h]

lemma evalAux_wit (x : Fin C.n → Bool) (wit : Fin C.w → Bool) {i : ℕ} (h1 : C.n ≤ i)
    (h2 : i < C.n + C.w) : C.evalAux x wit i = wit ⟨i - C.n, by omega⟩ := by
  rw [evalAux]
  have h1' : ¬ i < C.n := by omega
  simp [h1', h2]

lemma evalAux_gate (x : Fin C.n → Bool) (wit : Fin C.w → Bool) (k : Fin C.g) :
    C.evalAux x wit (C.n + C.w + k.val) =
      C.gateFn k (C.evalAux x wit (C.gateIn k).1.val) (C.evalAux x wit (C.gateIn k).2.val) := by
  obtain ⟨kv, hkv⟩ := k
  rw [evalAux]
  have h1 : ¬ (C.n + C.w + kv < C.n) := by omega
  have h2 : ¬ (C.n + C.w + kv < C.n + C.w) := by omega
  have h3 : C.n + C.w + kv < C.n + C.w + C.g := by omega
  simp only [h1, h2, h3, ↓reduceDIte]
  have e : (⟨C.n + C.w + kv - (C.n + C.w), by omega⟩ : Fin C.g) = ⟨kv, hkv⟩ := Fin.ext (by simp)
  exact congrArg (fun k : Fin C.g =>
    C.gateFn k (C.evalAux x wit (C.gateIn k).1.val) (C.evalAux x wit (C.gateIn k).2.val)) e

/-- The wire of a coordinate. -/
def wireOfNat (c : ℕ) : ℕ :=
  if c < C.n then c else if c = C.n then C.outW else if c - 1 < C.outW then c - 1 else c

lemma wireOfNat_coordOfNat {wi : ℕ} (_h : wi < C.n + C.w + C.g) :
    C.wireOfNat (C.coordOfNat wi) = wi := by
  unfold coordOfNat wireOfNat
  have := C.outW_lt; have := C.n_le_outW
  split_ifs <;> omega

lemma coordOfNat_of_lt {wi : ℕ} (h : wi < C.n) : C.coordOfNat wi = wi := by
  simp [coordOfNat, h]

lemma coordOfNat_outW : C.coordOfNat C.outW = C.n := by
  have := C.n_le_outW
  simp [coordOfNat, show ¬ C.outW < C.n by omega]

lemma wireOfNat_of_lt {c : ℕ} (h : c < C.n) : C.wireOfNat c = c := by
  simp [wireOfNat, h]

lemma wireOfNat_n : C.wireOfNat C.n = C.outW := by
  simp [wireOfNat]

/-- Evaluations of the circuit, reordered, are valid assignments of the gate verifier. -/
lemma isValid_eval (x : Fin C.n → Bool) (wit : Fin C.w → Bool) :
    C.toGateVerifier.IsValid (fun c => C.evalAux x wit (C.wireOfNat c)) := by
  intro k
  simp only [GateVerifier.out, GateVerifier.in1, GateVerifier.in2, GateVerifier.fn, toGateVerifier,
    coordOf]
  rw [C.wireOfNat_coordOfNat (C.gateWire k).isLt, C.wireOfNat_coordOfNat (C.inWire1 k).isLt,
    C.wireOfNat_coordOfNat (C.inWire2 k).isLt]
  exact C.evalAux_gate x wit k

lemma hasPrefix_eval (x : Fin C.n → Bool) (wit : Fin C.w → Bool) (hout : C.evalAux x wit C.outW = true) :
    C.toGateVerifier.HasPrefix x (fun c => C.evalAux x wit (C.wireOfNat c)) := by
  refine ⟨fun i => ?_, ?_⟩
  · simp only [GateVerifier.inputWire, toGateVerifier]
    rw [C.wireOfNat_of_lt i.isLt, C.evalAux_input x wit i.isLt]
  · simp only [GateVerifier.outputWire, toGateVerifier]
    rw [C.wireOfNat_n]
    exact hout

/-- The witness read off a wire assignment of the gate verifier. -/
def witOf (z : Fin C.S → Bool) (j : Fin C.w) : Bool :=
  z ⟨C.coordOfNat (C.n + j.val), C.coordOfNat_lt (by have := j.isLt; omega)⟩

/-- A valid assignment of the gate verifier with prefix `(x, _)` is the evaluation of the
circuit on `x` and the witness it contains. -/
lemma evalAux_eq_of_isValid {x : Fin C.n → Bool} {z : Fin C.S → Bool}
    (hz : C.toGateVerifier.IsValid z) (hpre : ∀ i, z (C.toGateVerifier.inputWire i) = x i) :
    ∀ wi (hwi : wi < C.n + C.w + C.g),
      C.evalAux x (C.witOf z) wi = z ⟨C.coordOfNat wi, C.coordOfNat_lt hwi⟩ := by
  intro wi
  induction wi using Nat.strong_induction_on with
  | _ wi ih =>
    intro hwi
    by_cases h1 : wi < C.n
    · rw [C.evalAux_input x _ h1, ← hpre ⟨wi, h1⟩]
      congr 1
      exact Fin.ext (by simp [GateVerifier.inputWire, toGateVerifier, C.coordOfNat_of_lt h1])
    by_cases h2 : wi < C.n + C.w
    · rw [C.evalAux_wit x _ (by omega) h2]
      unfold witOf
      congr 1
      exact Fin.ext (by simp; congr 1; omega)
    · obtain ⟨k, hk⟩ : ∃ k : Fin C.g, wi = C.n + C.w + k.val :=
        ⟨⟨wi - (C.n + C.w), by omega⟩, by simp; omega⟩
      subst hk
      rw [C.evalAux_gate x _ k]
      have e1 := (C.gateIn k).1.isLt
      have e2 := (C.gateIn k).2.isLt
      rw [ih _ e1 (by have := k.isLt; omega), ih _ e2 (by have := k.isLt; omega)]
      exact (hz k).symm

/-- The wire reordering preserves the language. -/
private theorem language_toGateVerifier : C.toGateVerifier.Language = C.Language := by
  ext x
  simp only [GateVerifier.Language, Language, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨z, hz, hpre⟩
    refine ⟨C.witOf z, ?_⟩
    rw [C.evalAux_eq_of_isValid hz hpre.1 C.outW C.outW_lt]
    have := hpre.2
    simp only [GateVerifier.outputWire, toGateVerifier] at this
    rw [← this]
    congr 1
    exact Fin.ext (by simp [C.coordOfNat_outW])
  · rintro ⟨wit, hout⟩
    exact ⟨fun c => C.evalAux x wit (C.wireOfNat c), C.isValid_eval x wit,
      C.hasPrefix_eval x wit hout⟩

end BoolCircuit

end LatticePrepro

open LatticePrepro
open LatticePrepro.BoolCircuit
variable (C : BoolCircuit)
theorem solution : C.toGateVerifier.Language = C.Language :=
  @LatticePrepro.BoolCircuit.language_toGateVerifier C
