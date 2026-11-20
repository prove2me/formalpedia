-- Prove2me | solution 1 for LatticePrepro.ThreeSAT.explicit_lattice_gap
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-20T00:26:50.619318+00:00
-- url     : https://prove2.me/submissions/422041c2-a9cf-48fc-b262-9e51f3738172

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_Codes_Ext
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_ConstructionA_Ext
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Hadamard_Ext
import Definitions.Def_LatticePrepro_Conversions_Padding
import Definitions.Def_LatticePrepro_Conversions_Lattices
import Definitions.Def_LatticePrepro_Conversions_Lattices_Ext
import Definitions.Def_LatticePrepro_Lattices_Distance
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
import Definitions.Def_LatticePrepro_Lattices_Mathlib
import Definitions.Def_LatticePrepro_Main
import Definitions.Def_LatticePrepro_Verifier_Gates
import Definitions.Def_LatticePrepro_Verifier_Circuit
import Definitions.Def_LatticePrepro_Verifier_Expr
import Definitions.Def_LatticePrepro_Verifier_ThreeSAT
import Definitions.Def_LatticePrepro_ThreeSAT
import Definitions.Def_LatticePrepro_ThreeSAT_Ext
import Definitions.Def_LatticePrepro_Explicit
import Theorems.Thm_LatticePrepro_BoolCircuit_language_toGateVerifier
import Theorems.Thm_LatticePrepro_GateVerifier_language_toQuadratic
import Theorems.Thm_LatticePrepro_QuadraticVerifier_Tables_latticeFamily_hasGap
import Theorems.Thm_LatticePrepro_QuadraticVerifier_Tables_nonempty
import Theorems.Thm_LatticePrepro_ThreeSAT_mem_language_iff

namespace LatticePrepro end LatticePrepro
namespace LatticePrepro.GateList end LatticePrepro.GateList
namespace LatticePrepro.QuadraticVerifier end LatticePrepro.QuadraticVerifier
namespace LatticePrepro.ThreeSAT end LatticePrepro.ThreeSAT

namespace LatticePrepro

namespace PNorm

lemma one_le_s (pn : PNorm) : 1 ≤ pn.s := by
  cases pn with
  | fin p hp => exact le_min hp (by norm_num)
  | inf => norm_num [PNorm.s]

end PNorm

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

/-- The quadratic verifier accepts exactly the (encodings of) satisfiable instances. -/
theorem mem_language_verifier_iff (p : ℕ) [Fact p.Prime] {v : ℕ} (x : Instance v) :
    encode x ∈ (verifier p v).Language ↔ Satisfiable x := by
  show encode x ∈ ((circuit v).toGateVerifier.toQuadratic p).Language ↔ _
  rw [GateVerifier.language_toQuadratic, BoolCircuit.language_toGateVerifier, mem_language_iff]

/-- The size parameter `S + 1` of the quadratic verifier is at most `n^3`, `n = len v`. -/
theorem S_verifier_succ_le (p : ℕ) {v : ℕ} (hv : 1 ≤ v) :
    (verifier p v).S + 1 ≤ len v ^ 3 :=
  S_succ_le_len_pow hv

end ThreeSAT

end LatticePrepro

namespace LatticePrepro

/-- A gap is transported along a map of instances that respects the languages. -/
theorem LatticeFamily.HasGap.comap {X Y : Type} {Λ : LatticeFamily X} {pn : PNorm} {R : ℕ}
    {ε : ℝ} {Lang : Set X} {n C : ℕ} (h : Λ.HasGap pn R ε Lang n C) {Lang' : Set Y} (f : Y → X)
    (hf : ∀ y, f y ∈ Lang ↔ y ∈ Lang') {n' C' : ℕ} (hn : n ^ C ≤ n' ^ C') :
    (Λ.comap f).HasGap pn R ε Lang' n' C' :=
  ⟨h.one_le_R, h.one_le_card, h.card_le.trans hn, h.full_rank,
    fun y hy => h.yes (f y) ((hf y).mpr hy), fun y hy => h.no (f y) fun hx => hy ((hf y).mp hx)⟩

namespace ThreeSAT

open QuadraticVerifier

/-- The 3SAT verifier has at least two assignment coordinates. -/
lemma two_le_S_verifier (p : ℕ) {v : ℕ} (hv : 1 ≤ v) : 2 ≤ (verifier p v).S := by
  have h1 := S_verifier_succ_le p hv
  have h2 := (verifier p v).n_succ_le
  have h3 : (verifier p v).n = len v := rfl
  have h8 := eight_le_len hv
  omega

/-- **Theorem 5.1 for 3SAT, lattices, for the paper's construction**: for every norm exponent
`1 ≤ p ≤ ∞` with `s = min {p, 2}` and every `0 < ε < 1/s`, there is a constant `C` such that for
every `v ≥ 1` there are tables `T` for the 3SAT verifier on `v` variables for which the lattice
family `T.latticeFamily pn`, with the instances encoded by `encode`, has full rank, dimension
`M ≤ n^C` (`n = (2v)^3` the instance length) and gap `M^{1/s - ε}` for 3SAT, with the radius
`T.latticeRadius pn`. -/
private theorem explicit_lattice_gap (pn : PNorm) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / pn.s) :
    ∃ C : ℕ, ∀ v : ℕ, 1 ≤ v → ∃ T : (verifier 2 v).Tables (1 - pn.s * ε),
      ((T.latticeFamily pn).comap encode).HasGap pn (T.latticeRadius pn) ε (SAT v) (len v) C := by
  have hδ1 : 1 - pn.s * ε < 1 := by nlinarith [pn.one_le_s]
  refine ⟨3 * sizeExp 2 (1 - pn.s * ε), fun v hv => ?_⟩
  obtain ⟨T⟩ := Tables.nonempty (verifier 2 v) (two_le_S_verifier 2 hv) hδ1
  refine ⟨T, (T.latticeFamily_hasGap pn hε hε1).comap encode
    (fun x => mem_language_verifier_iff 2 x) ?_⟩
  rw [pow_mul]
  exact Nat.pow_le_pow_left (S_verifier_succ_le 2 hv) _

end ThreeSAT

end LatticePrepro

open LatticePrepro
open LatticePrepro.ThreeSAT
open QuadraticVerifier
theorem solution (pn : PNorm) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / pn.s) :
    ∃ C : ℕ, ∀ v : ℕ, 1 ≤ v → ∃ T : (verifier 2 v).Tables (1 - pn.s * ε),
      ((T.latticeFamily pn).comap encode).HasGap pn (T.latticeRadius pn) ε (SAT v) (len v) C :=
  @LatticePrepro.ThreeSAT.explicit_lattice_gap pn ε hε hε1
