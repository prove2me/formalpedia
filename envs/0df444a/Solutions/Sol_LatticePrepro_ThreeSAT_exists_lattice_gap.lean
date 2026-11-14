-- Prove2me | solution 1 for LatticePrepro.ThreeSAT.exists_lattice_gap
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T15:57:18.253266+00:00
-- url     : https://prove2.me/submissions/718c1657-46ac-4845-ac72-84fa04d55b49

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
import Theorems.Thm_LatticePrepro_lattice_gap

namespace LatticePrepro end LatticePrepro
namespace LatticePrepro.GateList end LatticePrepro.GateList
namespace LatticePrepro.ThreeSAT end LatticePrepro.ThreeSAT

namespace LatticePrepro

namespace LatticeGap

variable {pn : PNorm} {ε : ℝ} {X : Type} {Lang : Set X} {n C : ℕ} (G : LatticeGap pn ε Lang n C)

/-- Transport a fixed lattice gap along a map of instances that respects the languages. -/
def comap {Y : Type} {Lang' : Set Y} (f : Y → X) (hf : ∀ y, f y ∈ Lang ↔ y ∈ Lang')
    {n' C' : ℕ} (hn : n ^ C ≤ n' ^ C') : LatticeGap pn ε Lang' n' C' where
  Λ := { M := G.Λ.M, lattice := G.Λ.lattice, target := fun y => G.Λ.target (f y) }
  R := G.R
  one_le_R := G.one_le_R
  one_le_card := G.one_le_card
  card_le := G.card_le.trans hn
  N := G.N
  N_pos := G.N_pos
  smul_mem := G.smul_mem
  yes := fun y hy => G.yes (f y) ((hf y).mpr hy)
  no := fun y hy => G.no (f y) (fun h => hy ((hf y).mp h))

end LatticeGap

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

/-- **Theorem 5.1 for 3SAT, lattices**: for every norm exponent `1 ≤ p ≤ ∞` with
`s = min {p, 2}` and every `0 < ε < 1/s`, there is a constant `C` such that for every `v ≥ 1`
there is a fixed full-rank lattice `Λ ⊆ ℤ^M` with `M ≤ n^C` (`n = (2v)^3` the instance length)
and gap `M^{1/s - ε}` for 3SAT on `v` variables. -/
private theorem exists_lattice_gap (pn : PNorm) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / pn.s) :
    ∃ C : ℕ, ∀ v : ℕ, 1 ≤ v → Nonempty (LatticeGap pn ε (SAT v) (len v) C) := by
  refine ⟨3 * sizeExp 2 (1 - pn.s * ε), fun v hv => ?_⟩
  obtain ⟨G⟩ := lattice_gap pn ε hε hε1 (verifier 2 v)
  refine ⟨G.comap encode (fun x => mem_language_verifier_iff 2 x) ?_⟩
  rw [pow_mul]
  exact Nat.pow_le_pow_left (S_verifier_succ_le 2 hv) _

end ThreeSAT

end LatticePrepro

open LatticePrepro
open LatticePrepro.ThreeSAT
theorem solution (pn : PNorm) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / pn.s) :
    ∃ C : ℕ, ∀ v : ℕ, 1 ≤ v → Nonempty (LatticeGap pn ε (SAT v) (len v) C) :=
  @LatticePrepro.ThreeSAT.exists_lattice_gap pn ε hε hε1
