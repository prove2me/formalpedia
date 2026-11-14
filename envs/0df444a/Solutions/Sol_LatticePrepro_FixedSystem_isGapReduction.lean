-- Prove2me | solution 1 for LatticePrepro.FixedSystem.isGapReduction
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:34:50.961225+00:00
-- url     : https://prove2.me/submissions/c43273e2-b04a-45d0-b687-61102d9a39db

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Reduction_FixedSystem
import Theorems.Thm_LatticePrepro_FixedSystem_mem_language_of_solves

namespace LatticePrepro end LatticePrepro
namespace LatticePrepro.FixedSystem end LatticePrepro.FixedSystem

namespace LatticePrepro

variable {ι β F : Type*}

variable [Fintype ι] [DecidableEq β]

section

variable [Zero F] [DecidableEq F] (blk : ι → β)

lemma ExactlyOnePerBlock.atMostOne {y : ι → F} (h : ExactlyOnePerBlock blk y) :
    AtMostOnePerBlock blk y := fun s => (h s).le

end

section Scalar

variable [MulZeroOneClass F] [DecidableEq F] [NoZeroDivisors F] (blk : ι → β)

lemma blockSupport_smul_subset (c : F) (y : ι → F) (s : β) :
    blockSupport blk (fun i => c * y i) s ⊆ blockSupport blk y s := by
  intro i
  simp only [blockSupport, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, mul_eq_zero,
    not_or]
  tauto

lemma AtMostOnePerBlock.smul {y : ι → F} (h : AtMostOnePerBlock blk y) (c : F) :
    AtMostOnePerBlock blk (fun i => c * y i) := fun s =>
  (Finset.card_le_card (blockSupport_smul_subset blk c y s)).trans (h s)

end Scalar

end LatticePrepro

namespace LatticePrepro

variable {K : Type*} [AddCommGroup K]

/-- A telescoping sum over `Finset.Ico a b`. -/
lemma sum_Ico_telescope (f : ℕ → K) {a b : ℕ} (hab : a ≤ b) :
    ∑ m ∈ Finset.Ico a b, (f m - f (m - 1)) = f (b - 1) - f (a - 1) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab, ih, Nat.add_sub_cancel]
    abel

end LatticePrepro

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

lemma elemTable_binary (α : K) : IsBinary (R.elemTable α) := (R.complete α).choose_spec.1

lemma elemTable_onePerBlock (α : K) : ExactlyOnePerBlock R.blk (R.elemTable α) :=
  (R.complete α).choose_spec.2.1

lemma constraint_elemTable (α : K) : R.constraint (R.elemTable α) = 0 :=
  (R.complete α).choose_spec.2.2.1

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

end LatticePrepro

namespace LatticePrepro

section FixedSystem

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    {Ω : Type} [Field Ω] [Algebra (ZMod p) Ω] [Algebra K Ω] [IsScalarTower (ZMod p) K Ω]
    (V : QuadraticVerifier p) (R : MomentRepresentation p K Ω) (ε : EncodingTuple p K V.S)

namespace FixedSystem

/-- `A v = b_x` holds exactly when `v` satisfies the equations of Construction 4.5. -/
theorem sysMap_eq_rhs_iff (x : Fin V.n → Bool) (v : Col V R → ZMod p) :
    sysMap V R ε v = sysRhs V R ε x ↔ Solves V R ε x v := by
  simp only [sysMap_apply, sysFun, sysRhs, Prod.mk.injEq, funext_iff, Pi.zero_apply, Prod.forall]
  exact ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩, fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩⟩

end FixedSystem

namespace FixedSystem

lemma isSolution_iff (x : Fin V.n → Bool) (v : Col V R → ZMod p) :
    (fixedSystem V R ε).IsSolution x v ↔ Solves V R ε x v :=
  sysMap_eq_rhs_iff V R ε x v

/-- The number of blocks of the system is `N · D`. -/
lemma numBlocks_eq : (fixedSystem V R ε).numBlocks = Fintype.card V.TblIdx * R.numBlocks :=
  Fintype.card_prod _ _

end FixedSystem

end FixedSystem

end LatticePrepro

namespace LatticePrepro

namespace FixedSystem

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    {Ω : Type} [Field Ω] [Algebra (ZMod p) Ω] [Algebra K Ω] [IsScalarTower (ZMod p) K Ω]
    (V : QuadraticVerifier p) (R : MomentRepresentation p K Ω) (ε : EncodingTuple p K V.S)

/-- The partial encoding `α_i = ∑_{j ≤ i} z_j • E_j`. -/
def partialEnc (z : Fin (V.S + 1) → ZMod p) (i : ℕ) : K :=
  ∑ j : Fin (V.S + 1), (if j.val ≤ i then z j else 0) • ε.E j

lemma partialEnc_top (z : Fin (V.S + 1) → ZMod p) : partialEnc V ε z V.S = ε.enc z := by
  unfold partialEnc EncodingTuple.enc
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [if_pos (Nat.le_of_lt_succ j.isLt)]

lemma partialEnc_succ (z : Fin (V.S + 1) → ZMod p) {i : ℕ} (hi : 1 ≤ i) (hiS : i ≤ V.S) :
    partialEnc V ε z i =
      partialEnc V ε z (i - 1) + z ⟨i, by omega⟩ • ε.E ⟨i, by omega⟩ := by
  unfold partialEnc
  have key : ∀ j : Fin (V.S + 1), (if j.val ≤ i then z j else 0) • ε.E j =
      (if j.val ≤ i - 1 then z j else 0) • ε.E j +
        (if j = ⟨i, by omega⟩ then z j • ε.E j else 0) := by
    intro j
    by_cases hj : j = ⟨i, by omega⟩
    · subst hj
      simp only [ite_true]
      rw [if_pos le_rfl, if_neg (by omega), zero_smul, zero_add]
    · rw [if_neg hj, add_zero]
      have hj' : j.val ≠ i := fun h => hj (Fin.ext h)
      by_cases h : j.val ≤ i
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
  simp_rw [key]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]

/-- For an assignment with prefix `(x, 1)`, the partial encoding up to `n + 1` is `θ_x`. -/
lemma partialEnc_prefix {x : Fin V.n → Bool} {z : Fin (V.S + 1) → ZMod p} (h0 : z 0 = 1)
    (hpre : V.HasPrefix x z) : partialEnc V ε z (V.n + 1) = V.instanceEnc ε x := by
  unfold partialEnc QuadraticVerifier.instanceEnc EncodingTuple.enc
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  by_cases hj : j.val ≤ V.n + 1
  · rw [if_pos hj]
    by_cases hj0 : j.val = 0
    · rw [show j = 0 from Fin.ext hj0, h0, V.assignOf_zero]
    by_cases hjn : j.val ≤ V.n
    · rw [V.assignOf_apply_of_le x 0 hj0 hjn]
      have := hpre.1 ⟨j.val - 1, by omega⟩
      rw [show V.inputIdx ⟨j.val - 1, by omega⟩ = j from
        Fin.ext (by simp [QuadraticVerifier.inputIdx]; omega)] at this
      exact this
    · have hje : j.val = V.n + 1 := by omega
      rw [V.assignOf_apply_of_eq x 0 hje, show j = V.outputIdx from Fin.ext hje]
      exact hpre.2
  · rw [if_neg hj, V.assignOf_apply_of_lt x 0 (by omega)]
    rfl

/-- The tables of the honest solution. -/
noncomputable def honestTbl (z : Fin (V.S + 1) → ZMod p) : V.TblIdx → R.ι → ZMod p :=
  Sum.elim (fun T => (z T.1.1 * z T.1.2) • R.elemTable (partialEnc V ε z V.S))
    (fun i => z i.1 • R.elemTable (partialEnc V ε z (i.1.val - 1)))

/-- The honest solution. -/
noncomputable def honest (z : Fin (V.S + 1) → ZMod p) : Col V R → ZMod p :=
  fun c => honestTbl V R ε z c.1 c.2

lemma tbl_honest (z : Fin (V.S + 1) → ZMod p) (T : V.TblIdx) :
    tbl V R (honest V R ε z) T = honestTbl V R ε z T := rfl

/-- For a Boolean assignment, the product of the coordinates of the representative of `(i, j)`
is `z_i z_j`. -/
lemma rep_mul {z : Fin (V.S + 1) → ZMod p} (hz : V.IsBooleanAssignment z) (i j : Fin (V.S + 1)) :
    z (V.rep i j).1.1 * z (V.rep i j).1.2 = z i * z j := by
  obtain ⟨h0, hb⟩ := hz
  unfold QuadraticVerifier.rep
  split_ifs with h1 h2 h3
  · rfl
  · exact mul_comm _ _
  · have hij : i = j := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
    subst hij
    subst h3
    rfl
  · have hij : i = j := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
    subst hij
    simp only [h0, mul_one]
    rcases hb i with h | h <;> simp [h]

lemma momentMap_ptbl_honest {z : Fin (V.S + 1) → ZMod p} (hz : V.IsBooleanAssignment z)
    (i j : Fin (V.S + 1)) (k : R.Order) :
    R.momentMap k (ptbl V R (honest V R ε z) i j) =
      (z i * z j) • partialEnc V ε z V.S ^ (k : ℕ) := by
  simp only [ptbl, tbl_honest, honestTbl, Sum.elim_inl, map_smul, R.momentMap_elemTable,
    rep_mul V hz]

lemma momentMap_atbl_honest (z : Fin (V.S + 1) → ZMod p) (i : V.AuxIdx) (k : R.Order) :
    R.momentMap k (atbl V R (honest V R ε z) i) =
      z i.1 • partialEnc V ε z (i.1.val - 1) ^ (k : ℕ) := by
  simp only [atbl, tbl_honest, honestTbl, Sum.elim_inr, map_smul, R.momentMap_elemTable]

omit [Fact (Nat.Prime p)] [Algebra (ZMod p) K] in
/-- Summing a telescoping difference over the auxiliary indices. -/
lemma sum_aux_telescope (f : ℕ → K) :
    ∑ i : V.AuxIdx, (f i.1.val - f (i.1.val - 1)) = f V.S - f (V.n + 1) := by
  classical
  have h1 : ∑ i : V.AuxIdx, (f i.1.val - f (i.1.val - 1)) =
      ∑ m ∈ Finset.Ico (V.n + 2) (V.S + 1), (f m - f (m - 1)) := by
    rw [← Finset.sum_subtype (Finset.univ.filter fun i : Fin (V.S + 1) => V.n + 1 < i.val)
      (by simp) (fun i : Fin (V.S + 1) => f i.val - f (i.val - 1)), Finset.sum_filter,
      Fin.sum_univ_eq_sum_range (fun m => if V.n + 1 < m then f m - f (m - 1) else 0) (V.S + 1),
      ← Finset.sum_filter]
    congr 1
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [h1, sum_Ico_telescope f (by have := V.n_succ_le; omega)]
  rfl

lemma honest_constraint (z : Fin (V.S + 1) → ZMod p) (T : V.TblIdx) :
    R.constraint (tbl V R (honest V R ε z) T) = 0 := by
  rw [tbl_honest]
  rcases T with T | i <;> simp [honestTbl, map_smul, R.constraint_elemTable]

lemma honest_encoding {z : Fin (V.S + 1) → ZMod p} (hz : V.IsBooleanAssignment z)
    (j : Fin (V.S + 1)) (k : Fin R.r) :
    R.momentMap (R.lowSucc k) (ptbl V R (honest V R ε z) 0 j) =
      ∑ i, ε.E i * R.momentMap (R.low k) (ptbl V R (honest V R ε z) i j) := by
  rw [momentMap_ptbl_honest V R ε hz 0 j]
  simp_rw [momentMap_ptbl_honest V R ε hz _ j]
  rw [hz.1, one_mul, MomentRepresentation.lowSucc_val, MomentRepresentation.low_val]
  set α := partialEnc V ε z V.S with hα
  have hαs : α = ∑ i, algebraMap (ZMod p) K (z i) * ε.E i := by
    rw [hα, partialEnc_top, EncodingTuple.enc]
    simp [Algebra.smul_def]
  calc z j • α ^ ((k : ℕ) + 1)
      = (∑ i, algebraMap (ZMod p) K (z i) * ε.E i) * (z j • α ^ (k : ℕ)) := by
        rw [← hαs, Algebra.smul_def, Algebra.smul_def]; ring
    _ = ∑ i, ε.E i * ((z i * z j) • α ^ (k : ℕ)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Algebra.smul_def, map_mul]
        ring

lemma honest_gate {z : Fin (V.S + 1) → ZMod p} (hz : V.IsBooleanAssignment z)
    (hval : V.IsValid z) (b : Fin V.G) (k : Fin R.r) :
    ∑ i, ∑ j, V.coeff b i j • R.momentMap (R.low k) (ptbl V R (honest V R ε z) i j) = 0 := by
  simp_rw [momentMap_ptbl_honest V R ε hz _ _, smul_smul, ← Finset.sum_smul]
  have := hval b
  unfold QuadraticVerifier.gateEq at this
  rw [this, zero_smul]

lemma honest_translation {x : Fin V.n → Bool} {z : Fin (V.S + 1) → ZMod p}
    (hz : V.IsBooleanAssignment z) (hpre : V.HasPrefix x z) (k : R.Order) :
    transLhs V R ε (honest V R ε z) k = V.instanceEnc ε x ^ (k : ℕ) := by
  have hterm : ∀ i : V.AuxIdx, ∑ j : Fin k, ((k : ℕ).choose j : K) * ε.E i.1 ^ ((k : ℕ) - j) *
      R.momentMap (R.below k j) (atbl V R (honest V R ε z) i) =
      partialEnc V ε z i.1.val ^ (k : ℕ) - partialEnc V ε z (i.1.val - 1) ^ (k : ℕ) := by
    intro i
    have hi1 : 1 ≤ i.1.val := by have := i.2; omega
    have hiS : i.1.val ≤ V.S := Nat.le_of_lt_succ i.1.isLt
    have hstep := partialEnc_succ V ε z hi1 hiS
    have hfin : (⟨i.1.val, by omega⟩ : Fin (V.S + 1)) = i.1 := Fin.ext rfl
    rw [hfin] at hstep
    simp_rw [momentMap_atbl_honest V R ε z i, MomentRepresentation.below_val]
    rw [Fin.sum_univ_eq_sum_range (fun j => ((k : ℕ).choose j : K) * ε.E i.1 ^ ((k : ℕ) - j) *
      (z i.1 • partialEnc V ε z (i.1.val - 1) ^ j)) (k : ℕ)]
    set β := partialEnc V ε z (i.1.val - 1)
    rcases hz.2 i.1 with h | h
    · rw [hstep, h, zero_smul, add_zero, sub_self]
      simp
    · rw [hstep, h, one_smul]
      have hexp : (β + ε.E i.1) ^ (k : ℕ) =
          (∑ j ∈ Finset.range (k : ℕ), β ^ j * ε.E i.1 ^ ((k : ℕ) - j) * ((k : ℕ).choose j : K)) +
            β ^ (k : ℕ) := by
        rw [add_pow, Finset.sum_range_succ]
        simp
      rw [hexp, add_sub_cancel_right]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [one_smul]
      ring
  rw [transLhs, momentMap_ptbl_honest V R ε hz 0 0, Finset.sum_congr rfl fun i _ => hterm i,
    sum_aux_telescope V (fun m => partialEnc V ε z m ^ (k : ℕ)), hz.1, one_mul, one_smul,
    sub_sub_cancel, partialEnc_prefix V ε hz.1 hpre]

/-- The honest solution satisfies all equations of Construction 4.5. -/
theorem honest_solves {x : Fin V.n → Bool} {z : Fin (V.S + 1) → ZMod p}
    (hz : V.IsBooleanAssignment z) (hval : V.IsValid z) (hpre : V.HasPrefix x z) :
    Solves V R ε x (honest V R ε z) where
  constraint := honest_constraint V R ε z
  encoding := fun j k => sub_eq_zero.mpr (honest_encoding V R ε hz j k)
  gate := fun b k => honest_gate V R ε hz hval b k
  translation := fun k => honest_translation V R ε hz hpre k

lemma binary_mul {a b : ZMod p} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    a * b = 0 ∨ a * b = 1 := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]

lemma honest_binary {z : Fin (V.S + 1) → ZMod p} (hz : V.IsBooleanAssignment z) :
    IsBinary (honest V R ε z) := by
  rintro ⟨T | i, c⟩
  · exact binary_mul (binary_mul (hz.2 _) (hz.2 _)) (R.elemTable_binary _ c)
  · exact binary_mul (hz.2 _) (R.elemTable_binary _ c)

/-- The block support of a column block is the block support of the corresponding table. -/
lemma card_blockSupport_blk (v : Col V R → ZMod p) (T : V.TblIdx) (b : R.β) :
    (blockSupport (blk V R) v (T, b)).card = (blockSupport R.blk (tbl V R v T) b).card := by
  refine Finset.card_bij (fun c _ => c.2) ?_ ?_ ?_
  · rintro ⟨T', i⟩ hc
    rw [blockSupport, Finset.mem_filter] at hc ⊢
    obtain ⟨-, hblk, hne⟩ := hc
    simp only [blk, Prod.mk.injEq] at hblk
    exact ⟨Finset.mem_univ _, hblk.2, by rw [tbl, ← hblk.1]; exact hne⟩
  · rintro ⟨T₁, i₁⟩ hc₁ ⟨T₂, i₂⟩ hc₂ h
    rw [blockSupport, Finset.mem_filter] at hc₁ hc₂
    simp only [blk, Prod.mk.injEq] at hc₁ hc₂
    simp only at h
    rw [h, hc₁.2.1.1, hc₂.2.1.1]
  · intro i hi
    rw [blockSupport, Finset.mem_filter] at hi
    refine ⟨(T, i), ?_, rfl⟩
    rw [blockSupport, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [blk, hi.2.1], hi.2.2⟩

lemma honest_atMostOnePerBlock (z : Fin (V.S + 1) → ZMod p) :
    AtMostOnePerBlock (blk V R) (honest V R ε z) := by
  rintro ⟨T, b⟩
  rw [card_blockSupport_blk, tbl_honest]
  rcases T with T | i
  · exact ((R.elemTable_onePerBlock _).atMostOne.smul R.blk (z T.1.1 * z T.1.2)) b
  · exact ((R.elemTable_onePerBlock _).atMostOne.smul R.blk (z i.1)) b

/-- **Completeness** (Theorem 4.6). -/
theorem complete {x : Fin V.n → Bool} (hx : x ∈ V.Language) : (fixedSystem V R ε).IsYes x := by
  obtain ⟨z, hz, hval, hpre⟩ := hx
  exact ⟨honest V R ε z, (isSolution_iff V R ε x _).mpr (honest_solves V R ε hz hval hpre),
    honest_binary V R ε hz, honest_atMostOnePerBlock V R ε z⟩

end FixedSystem

end LatticePrepro

namespace LatticePrepro

open Finsupp

namespace FixedSystem

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    {Ω : Type} [Field Ω] [Algebra (ZMod p) Ω] [Algebra K Ω] [IsScalarTower (ZMod p) K Ω]
    (V : QuadraticVerifier p) (R : MomentRepresentation p K Ω) (ε : EncodingTuple p K V.S)

/-- **Soundness** (Theorem 4.6). -/
theorem sound {g : ℕ} (hg : 2 * g * Fintype.card V.TblIdx < R.r) {x : Fin V.n → Bool}
    (hx : x ∉ V.Language) : (fixedSystem V R ε).IsNo g x := by
  intro v hv
  have hv : Solves V R ε x v := (isSolution_iff V R ε x v).mp hv
  by_contra hcon
  rw [not_lt] at hcon
  apply hx
  apply mem_language_of_solves V R ε hv
  rw [numBlocks_eq] at hcon
  have hD : 0 < R.numBlocks := R.numBlocks_pos
  calc 2 * hammingNorm v ≤ 2 * (g * (Fintype.card V.TblIdx * R.numBlocks)) := by
        exact Nat.mul_le_mul_left 2 hcon
    _ = (2 * g * Fintype.card V.TblIdx) * R.numBlocks := by ring
    _ < R.r * R.numBlocks := Nat.mul_lt_mul_of_pos_right hg hD

/-- **Theorem 4.6**: the fixed-verifier system is a gap reduction with gap `g`
whenever `2 · g · N < r`. -/
private theorem isGapReduction {g : ℕ} (hg : 2 * g * Fintype.card V.TblIdx < R.r) :
    (fixedSystem V R ε).IsGapReduction V.Language g :=
  ⟨fun _ hx => complete V R ε hx, fun _ hx => sound V R ε hg hx⟩

end FixedSystem

end LatticePrepro

open LatticePrepro
open Finsupp
open LatticePrepro.FixedSystem
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    {Ω : Type} [Field Ω] [Algebra (ZMod p) Ω] [Algebra K Ω] [IsScalarTower (ZMod p) K Ω]
    (V : QuadraticVerifier p) (R : MomentRepresentation p K Ω) (ε : EncodingTuple p K V.S)
theorem solution {g : ℕ} (hg : 2 * g * Fintype.card V.TblIdx < R.r) :
    (fixedSystem V R ε).IsGapReduction V.Language g :=
  @LatticePrepro.FixedSystem.isGapReduction p _ K _ _ Ω _ _ _ _ V R ε g hg
