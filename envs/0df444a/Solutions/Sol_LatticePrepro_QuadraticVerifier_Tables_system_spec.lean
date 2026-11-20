-- Prove2me | solution 1 for LatticePrepro.QuadraticVerifier.Tables.system_spec
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-20T00:19:34.441268+00:00
-- url     : https://prove2.me/submissions/0ccd1402-6bde-4d94-b8c6-41a84f52520e

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
import Theorems.Thm_LatticePrepro_FixedSystem_isGapReduction
import Theorems.Thm_LatticePrepro_QuadraticVerifier_card_tblIdx_le

namespace LatticePrepro end LatticePrepro
namespace LatticePrepro.QuadraticVerifier end LatticePrepro.QuadraticVerifier
namespace LatticePrepro.QuadraticVerifier.Tables end LatticePrepro.QuadraticVerifier.Tables

namespace LatticePrepro

namespace MomentRepresentation

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    {Ω : Type} [Field Ω] [Algebra (ZMod p) Ω] [Algebra K Ω] [IsScalarTower (ZMod p) K Ω]

variable (R : MomentRepresentation p K Ω)

/-- A natural number `k ≤ 2r - 2` as a moment order. -/
def ord (k : ℕ) (hk : k ≤ 2 * R.r - 2) : R.Order := ⟨k, by have := R.two_le_r; omega⟩

@[simp] lemma ord_val (k : ℕ) (hk : k ≤ 2 * R.r - 2) : (R.ord k hk : ℕ) = k := rfl

/-- The evaluation table length `D · b`. -/
lemma card_ι : Fintype.card R.ι = R.numBlocks * R.blockSize := by
  classical
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := R.blk) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  simp [R.card_fiber, Finset.sum_const, numBlocks]

/-- A chosen block-unit table for `α` (Completeness). -/
noncomputable def elemTable (α : K) : R.ι → ZMod p := (R.complete α).choose

lemma momentMap_elemTable (α : K) (k : R.Order) :
    R.momentMap k (R.elemTable α) = α ^ (k : ℕ) :=
  (R.complete α).choose_spec.2.2.2 k

/-- A moment representation has at least one block (otherwise no table could have zeroth
moment `1`). -/
lemma numBlocks_pos : 0 < R.numBlocks := by
  by_contra h
  have hβ : Fintype.card R.β = 0 := by simpa [numBlocks] using h
  have hι : Fintype.card R.ι = 0 := by rw [R.card_ι, numBlocks, hβ, zero_mul]
  have hy : R.elemTable 1 = 0 := by
    funext i
    exact absurd (Fintype.card_pos_iff.mpr ⟨i⟩) (by omega)
  have h0 := R.momentMap_elemTable 1 (R.ord 0 (Nat.zero_le _))
  rw [hy, map_zero, ord_val, pow_zero] at h0
  exact zero_ne_one h0

end MomentRepresentation

end LatticePrepro

namespace LatticePrepro

section FixedSystem

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    {Ω : Type} [Field Ω] [Algebra (ZMod p) Ω] [Algebra K Ω] [IsScalarTower (ZMod p) K Ω]
    (V : QuadraticVerifier p) (R : MomentRepresentation p K Ω) (ε : EncodingTuple p K V.S)

namespace FixedSystem

/-- The number of blocks of the system is `N · D`. -/
lemma numBlocks_eq : (fixedSystem V R ε).numBlocks = Fintype.card V.TblIdx * R.numBlocks :=
  Fintype.card_prod _ _

end FixedSystem

end FixedSystem

end LatticePrepro

namespace LatticePrepro

/-- Exponent bookkeeping for the size bound of Theorem 4.8. -/
lemma size_bound_aux {p m S N q B g : ℕ} (hp : 2 ≤ p) (hm : 1 ≤ m) (hS : 1 ≤ S)
    (hN : N ≤ (S + 1) ^ 2) (hq : q ≤ 8 * p ^ 3 * m * (S + 1) * B)
    (hB : B ^ m ≤ p ^ m * (8 * N * g)) :
    (N * q ^ (m + 1)) ^ m ≤ (8 * p ^ 4 * m * (S + 1)) ^ ((m + 7) * m) * g ^ (m + 1) := by
  set X := 8 * p ^ 3 * m * (S + 1) with hX
  have h8pm : 1 ≤ 8 * p ^ 3 * m :=
    Nat.mul_pos (Nat.mul_pos (by norm_num) (Nat.pow_pos (by omega))) hm
  have hX1 : 1 ≤ X := by rw [hX]; nlinarith
  have hSX : S + 1 ≤ X := by rw [hX]; nlinarith
  have hNX : N ≤ X ^ 2 := hN.trans (Nat.pow_le_pow_left hSX 2)
  have h8 : 8 ^ (m + 1) ≤ p ^ (6 * m) := by
    calc 8 ^ (m + 1) = 8 * 8 ^ m := by ring
      _ ≤ 8 ^ m * 8 ^ m := by
          apply Nat.mul_le_mul_right
          calc 8 = 8 ^ 1 := by norm_num
            _ ≤ 8 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      _ = 64 ^ m := by rw [← mul_pow]; norm_num
      _ ≤ (p ^ 6) ^ m := by
          apply Nat.pow_le_pow_left
          calc 64 = 2 ^ 6 := by norm_num
            _ ≤ p ^ 6 := Nat.pow_le_pow_left hp 6
      _ = p ^ (6 * m) := by rw [← pow_mul]
  have hexp : m * m + 5 * m + 2 ≤ m * (m + 7) := by nlinarith
  have hpX : 8 * p ^ 4 * m * (S + 1) = p * X := by rw [hX]; ring
  calc (N * q ^ (m + 1)) ^ m = N ^ m * (q ^ m) ^ (m + 1) := by ring
    _ ≤ N ^ m * ((X * B) ^ m) ^ (m + 1) := by gcongr
    _ = N ^ m * (X ^ m * B ^ m) ^ (m + 1) := by rw [mul_pow]
    _ ≤ N ^ m * (X ^ m * (p ^ m * (8 * N * g))) ^ (m + 1) := by gcongr
    _ = 8 ^ (m + 1) * N ^ (2 * m + 1) * (X ^ (m * (m + 1)) * p ^ (m * (m + 1))) * g ^ (m + 1) := by
        ring
    _ ≤ p ^ (6 * m) * (X ^ 2) ^ (2 * m + 1) * (X ^ (m * (m + 1)) * p ^ (m * (m + 1))) *
          g ^ (m + 1) := by gcongr
    _ = p ^ (m * (m + 7)) * X ^ (m * m + 5 * m + 2) * g ^ (m + 1) := by ring_nf
    _ ≤ p ^ (m * (m + 7)) * X ^ (m * (m + 7)) * g ^ (m + 1) := by
        gcongr
    _ = (8 * p ^ 4 * m * (S + 1)) ^ ((m + 7) * m) * g ^ (m + 1) := by
        rw [hpX]; ring_nf

lemma momentAxes_spec {δ : ℝ} (hδ1 : δ < 1) :
    1 ≤ momentAxes δ ∧ δ * (momentAxes δ + 1) < momentAxes δ := by
  refine ⟨by unfold momentAxes; omega, ?_⟩
  have h1δ : 0 < 1 - δ := by linarith
  have hm : δ / (1 - δ) < momentAxes δ := by
    unfold momentAxes
    push_cast
    linarith [Nat.le_ceil (δ / (1 - δ))]
  rw [div_lt_iff₀ h1δ] at hm
  nlinarith

end LatticePrepro

namespace LatticePrepro

namespace QuadraticVerifier

variable {p : ℕ} [hp : Fact p.Prime]

namespace Tables

variable {V : QuadraticVerifier p} {δ : ℝ}

/-- **Theorem 4.8** for the fixed linear system of the tables `T`, with `m = momentAxes δ` and
the gap `g = (S + 1)^{gapExp p δ}`: the system is a gap reduction from `L(V)` with gap `g`, the
gap is smaller than the block size, there is at least one block, and the number `n` of columns
satisfies `n^m ≤ (8 p^4 m (S + 1))^{(m+7) m} · g^{m+1}`. -/
private theorem system_spec (T : V.Tables δ) (hδ1 : δ < 1) :
    T.system.IsGapReduction V.Language ((V.S + 1) ^ gapExp p δ) ∧
      (V.S + 1) ^ gapExp p δ < T.system.blockSize ∧ 0 < T.system.numBlocks ∧
      Fintype.card T.system.ι ^ momentAxes δ ≤
        (8 * p ^ 4 * momentAxes δ * (V.S + 1)) ^ ((momentAxes δ + 7) * momentAxes δ) *
          ((V.S + 1) ^ gapExp p δ) ^ (momentAxes δ + 1) := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have hS1 : 1 ≤ V.S := by have := V.n_succ_le; omega
  have hm := (momentAxes_spec hδ1).1
  set m := momentAxes δ with hmdef
  set g := (V.S + 1) ^ gapExp p δ with hgdef
  set N := Fintype.card V.TblIdx with hNdef
  have hg : 1 ≤ g := Nat.one_le_pow _ _ (by omega)
  have hN1 : 1 ≤ N := Fintype.card_pos_iff.mpr ⟨Sum.inl V.mainIdx⟩
  have hNle : N ≤ (V.S + 1) ^ 2 := V.card_tblIdx_le
  have hYB : 8 * N * g ≤ T.B ^ m := T.le_pow
  have hBY : T.B ^ m ≤ 2 ^ m * (8 * N * g) := T.pow_le
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- gap reduction: `2 g N < r = B^m`
    show (fixedSystem V T.E.R T.E.ε).IsGapReduction V.Language g
    apply FixedSystem.isGapReduction
    rw [T.E.r_eq]
    calc 2 * g * N < 8 * N * g := by nlinarith
      _ ≤ T.B ^ m := hYB
  · -- `g < b = q^m`
    show g < T.E.R.blockSize
    rw [T.E.blockSize_eq]
    calc g < 8 * N * g := by nlinarith
      _ ≤ T.B ^ m := hYB
      _ ≤ T.E.q ^ m := Nat.pow_le_pow_left T.E.le_q m
  · -- the number of blocks `N · D` is positive
    show 0 < (fixedSystem V T.E.R T.E.ε).numBlocks
    rw [FixedSystem.numBlocks_eq]
    exact Nat.mul_pos hN1 T.E.R.numBlocks_pos
  · -- the size bound
    have hcard : Fintype.card (FixedSystem.Col V T.E.R) = N * T.E.q ^ (m + 1) := by
      rw [Fintype.card_prod, T.E.R.card_ι, T.E.numBlocks_eq, T.E.blockSize_eq]; ring
    show Fintype.card (FixedSystem.Col V T.E.R) ^ m ≤ _
    rw [hcard]
    refine size_bound_aux (B := T.B) hp2 hm hS1 hNle ?_ ?_
    · calc T.E.q ≤ 8 * p ^ 3 * m * V.S * T.B := T.E.q_lt.le
        _ ≤ 8 * p ^ 3 * m * (V.S + 1) * T.B := by gcongr; omega
    · calc T.B ^ m ≤ 2 ^ m * (8 * N * g) := hBY
        _ ≤ p ^ m * (8 * N * g) := by gcongr

end Tables

end QuadraticVerifier

end LatticePrepro

open LatticePrepro
open LatticePrepro.QuadraticVerifier
variable {p : ℕ} [hp : Fact p.Prime]
open LatticePrepro.QuadraticVerifier.Tables
variable {V : QuadraticVerifier p} {δ : ℝ}
theorem solution (T : V.Tables δ) (hδ1 : δ < 1) :
    T.system.IsGapReduction V.Language ((V.S + 1) ^ gapExp p δ) ∧
      (V.S + 1) ^ gapExp p δ < T.system.blockSize ∧ 0 < T.system.numBlocks ∧
      Fintype.card T.system.ι ^ momentAxes δ ≤
        (8 * p ^ 4 * momentAxes δ * (V.S + 1)) ^ ((momentAxes δ + 7) * momentAxes δ) *
          ((V.S + 1) ^ gapExp p δ) ^ (momentAxes δ + 1) :=
  @LatticePrepro.QuadraticVerifier.Tables.system_spec p _ V δ T hδ1
