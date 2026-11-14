-- Prove2me | solution 1 for LatticePrepro.ThreeSAT.exists_code_gap
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T15:57:17.483205+00:00
-- url     : https://prove2.me/submissions/0a5a6faa-54ad-4f99-99ff-842296b15ccc

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices
import Definitions.Def_LatticePrepro_Lattices_Distance
import Definitions.Def_LatticePrepro_Lattices_Mathlib
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Reduction_FixedSystem
import Definitions.Def_LatticePrepro_Tables_Digits
import Definitions.Def_LatticePrepro_Tables_FieldSetup
import Definitions.Def_LatticePrepro_Tables_Hankel
import Definitions.Def_LatticePrepro_Tables_Construction
import Definitions.Def_LatticePrepro_Tables_ElementTable
import Definitions.Def_LatticePrepro_Tables_TableSoundness
import Definitions.Def_LatticePrepro_Tables_Explicit
import Definitions.Def_LatticePrepro_Main
import Definitions.Def_LatticePrepro_Verifier_Gates
import Definitions.Def_LatticePrepro_Verifier_Circuit
import Definitions.Def_LatticePrepro_Verifier_Expr
import Definitions.Def_LatticePrepro_Verifier_ThreeSAT
import Definitions.Def_LatticePrepro_ThreeSAT
import Theorems.Thm_LatticePrepro_BoolCircuit_language_toGateVerifier
import Theorems.Thm_LatticePrepro_GateVerifier_language_toQuadratic
import Theorems.Thm_LatticePrepro_ThreeSAT_mem_language_iff
import Theorems.Thm_LatticePrepro_code_gap

namespace LatticePrepro end LatticePrepro
namespace LatticePrepro.GateList end LatticePrepro.GateList
namespace LatticePrepro.ThreeSAT end LatticePrepro.ThreeSAT

namespace LatticePrepro

/-- Transport a fixed code gap along a map of instances that respects the languages. -/
def CodeGap.comap {F : Type} [Field F] [DecidableEq F] {ε : ℝ} {X Y : Type} {Lang : Set X}
    {n C : ℕ} (G : CodeGap F ε Lang n C) {Lang' : Set Y} (f : Y → X)
    (hf : ∀ y, f y ∈ Lang ↔ y ∈ Lang') {n' C' : ℕ} (hn : n ^ C ≤ n' ^ C') :
    CodeGap F ε Lang' n' C' where
  𝒞 := { M := G.𝒞.M, code := G.𝒞.code, target := fun y => G.𝒞.target (f y) }
  R := G.R
  one_le_R := G.one_le_R
  one_le_card := G.one_le_card
  card_le := G.card_le.trans hn
  yes := fun y hy => G.yes (f y) ((hf y).mpr hy)
  no := fun y hy => G.no (f y) (fun h => hy ((hf y).mp h))

end LatticePrepro

namespace LatticePrepro

namespace BExpr

open GateList

variable {base : ℕ}

variable {n w : ℕ} (e : BExpr (n + w)) (he : 0 < e.size)

lemma toCircuit_g : (toCircuit n w e he).g = e.size := by
  show (compile (n + w) e []).1.length = e.size
  rw [length_compile_fst, List.length_nil, zero_add]

/-- The number of wires of the circuit of an expression. -/
lemma toCircuit_S : (toCircuit n w e he).S = n + w + e.size := by
  show n + w + (toCircuit n w e he).g = _
  rw [toCircuit_g]

end BExpr

end LatticePrepro

namespace LatticePrepro

namespace ThreeSAT

variable {v : ℕ}

lemma le_len (v : ℕ) : v ≤ len v := by
  rw [len_eq]
  rcases Nat.eq_zero_or_pos v with h | h
  · simp [h]
  · calc v = v * 1 * 1 := by ring
      _ ≤ (2 * v) * (2 * v) * (2 * v) := by gcongr <;> omega
      _ = (2 * v) ^ 3 := by ring

lemma eight_le_len (hv : 1 ≤ v) : 8 ≤ len v := by
  rw [len_eq]
  calc 8 = (2 * 1) ^ 3 := by norm_num
    _ ≤ (2 * v) ^ 3 := by gcongr

/-- The number of wires of the 3SAT verifier circuit. -/
theorem S_circuit_eq (v : ℕ) : (circuit v).S = 8 * len v + v + 2 := by
  rw [circuit, BExpr.toCircuit_S, size_formula]
  ring

/-- The 3SAT verifier circuit has linearly many wires in the instance length. -/
theorem S_circuit_le (v : ℕ) : (circuit v).S ≤ 9 * len v + 2 := by
  rw [S_circuit_eq]
  have := le_len v
  omega

/-- The number of wires of the 3SAT verifier circuit is polynomial in the instance length:
`S + 1 ≤ (len v)^3` for `v ≥ 1`. -/
theorem S_succ_le_len_pow (hv : 1 ≤ v) : (circuit v).S + 1 ≤ len v ^ 3 := by
  have h8 := eight_le_len hv
  have hS := S_circuit_le v
  calc (circuit v).S + 1 ≤ 9 * len v + 3 := by omega
    _ ≤ len v * len v * len v := by nlinarith
    _ = len v ^ 3 := by ring

end ThreeSAT

end LatticePrepro

namespace LatticePrepro

namespace ThreeSAT

/-- The quadratic verifier of the 3SAT verifier circuit over `𝔽_p`. -/
abbrev verifier (p v : ℕ) : QuadraticVerifier p := (circuit v).toGateVerifier.toQuadratic p

/-- The quadratic verifier accepts exactly the (encodings of) satisfiable instances. -/
theorem mem_language_verifier_iff (p : ℕ) [Fact p.Prime] {v : ℕ} (x : Instance v) :
    encode x ∈ (verifier p v).Language ↔ Satisfiable x := by
  show encode x ∈ ((circuit v).toGateVerifier.toQuadratic p).Language ↔ _
  rw [GateVerifier.language_toQuadratic, BoolCircuit.language_toGateVerifier, mem_language_iff]

/-- The size parameter `S + 1` of the quadratic verifier is at most `n^3`, `n = len v`. -/
theorem S_verifier_succ_le (p : ℕ) {v : ℕ} (hv : 1 ≤ v) :
    (verifier p v).S + 1 ≤ len v ^ 3 :=
  S_succ_le_len_pow hv

/-- **Theorem 5.1 for 3SAT, codes**: for every finite field `F` of characteristic `p` and every
`0 < ε < 1`, there is a constant `C` such that for every `v ≥ 1` there is a fixed code of block
length `M ≤ n^C` (`n = (2v)^3` the instance length) with gap `M^{1 - ε}` for 3SAT on `v`
variables. -/
private theorem exists_code_gap (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F]
    [DecidableEq F] [Algebra (ZMod p) F] (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℕ, ∀ v : ℕ, 1 ≤ v → Nonempty (CodeGap F ε (SAT v) (len v) C) := by
  refine ⟨3 * sizeExp p (1 - ε), fun v hv => ?_⟩
  obtain ⟨G⟩ := code_gap p F ε hε hε1 (verifier p v)
  refine ⟨G.comap encode (fun x => mem_language_verifier_iff p x) ?_⟩
  rw [pow_mul]
  exact Nat.pow_le_pow_left (S_verifier_succ_le p hv) _

end ThreeSAT

end LatticePrepro

open LatticePrepro
open LatticePrepro.ThreeSAT
theorem solution (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F]
    [DecidableEq F] [Algebra (ZMod p) F] (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℕ, ∀ v : ℕ, 1 ≤ v → Nonempty (CodeGap F ε (SAT v) (len v) C) :=
  @LatticePrepro.ThreeSAT.exists_code_gap p _ F _ _ _ _ ε hε hε1
