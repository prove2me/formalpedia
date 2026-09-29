-- Prove2me | solution 1 for LT.LatticeTree.finite_setOf_isWithin_or_isWithin_and_card_eq_of_isWithin_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/3768d7a9-3008-5fde-a973-201dfa30b45b

import Definitions.Def_LatticeTreeBaseChange
import Theorems.Thm_LT_LatticeTree_finite_setOf_isWithin_and_card_eq
import Theorems.Thm_LT_LatticeTree_Vertex_exists_isWithin_one_and_isWithin_and_forall_not_isWithin_succ_of_isWithin_succ_of_not_isWithin
import Theorems.Thm_LT_LatticeTree_Vertex_isWithin_add_of_isWithin_of_isWithin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LT_LatticeTree_finite_setOf_isWithin_or_isWithin_and_card_eq_of_isWithin_one

set_option autoImplicit false

namespace LT
p2m_export "LT" "LatticeTree.Vertex.IsWithin LatticeTree.Vertex LatticeTree.unitOfNeZero LatticeTree.finite_setOf_isWithin_and_card_eq LatticeTree.Vertex.isWithin_add_of_isWithin_of_isWithin"
namespace LatticeTree
p2m_export "LT.LatticeTree" "Vertex.IsWithin Vertex.isWithin_zero_iff latticeMap mem_latticeMap scalarGL scalarGL_mulVec Vertex unitOfNeZero unitOfNeZero_coe finite_setOf_isWithin_and_card_eq Vertex.exists_isWithin_one_and_isWithin_and_forall_not_isWithin_succ_of_isWithin_succ_of_not_isWithin Vertex.isWithin_add_of_isWithin_of_isWithin"
p2m_open "LT.LatticeTree LT"

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K]

section EdgeTubeCount

variable {V : Type} (W : ℕ → V → V → Prop)

private theorem one_add_sum_regular_eq (q n : ℕ) :
    1 + ∑ i ∈ Finset.range n, (q + 1) * q ^ i =
      ∑ i ∈ Finset.range (n + 1), q ^ i + ∑ i ∈ Finset.range n, q ^ i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ _ n, ← add_assoc, ih, Finset.sum_range_succ _ (n + 1), Finset.sum_range_succ _ n]
      ring

variable {W}

private theorem setOf_zero_inter_eq_empty (hzero : ∀ a b : V, W 0 a b ↔ a = b) {x₀ x₁ : V} (hne : x₀ ≠ x₁) :
    {x : V | W 0 x₀ x} ∩ {x : V | W 0 x₁ x} = ∅ := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, hzero]
  rintro rfl h
  exact hne h.symm

private theorem setOf_succ_inter_eq (hmono : ∀ {m n : ℕ}, m ≤ n → ∀ {a b : V}, W m a b → W n a b) {x₀ x₁ : V}
    (hedge : ∀ (x : V) (r : ℕ), (W r x₀ x → W (r + 1) x₁ x) ∧ (W r x₁ x → W (r + 1) x₀ x))
    (hstep : ∀ (x : V) (r : ℕ), W (r + 1) x₀ x → W (r + 1) x₁ x → W r x₀ x ∨ W r x₁ x) (r : ℕ) :
    {x : V | W (r + 1) x₀ x} ∩ {x : V | W (r + 1) x₁ x} = {x : V | W r x₀ x ∨ W r x₁ x} := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h₀, h₁⟩
    exact hstep x r h₀ h₁
  · rintro (h | h)
    · exact ⟨hmono (Nat.le_succ r) h, (hedge x r).1 h⟩
    · exact ⟨(hedge x r).2 h, hmono (Nat.le_succ r) h⟩

private theorem finite_setOf_or_and_ncard_eq (q : ℕ) (hmono : ∀ {m n : ℕ}, m ≤ n → ∀ {a b : V}, W m a b → W n a b)
    (hzero : ∀ a b : V, W 0 a b ↔ a = b) {x₀ x₁ : V} (hne : x₀ ≠ x₁)
    (hball : ∀ (v : V) (d : ℕ), {w : V | W d v w}.Finite ∧
      {w : V | W d v w}.ncard = 1 + ∑ i ∈ Finset.range d, (q + 1) * q ^ i)
    (hedge : ∀ (x : V) (r : ℕ), (W r x₀ x → W (r + 1) x₁ x) ∧ (W r x₁ x → W (r + 1) x₀ x))
    (hstep : ∀ (x : V) (r : ℕ), W (r + 1) x₀ x → W (r + 1) x₁ x → W r x₀ x ∨ W r x₁ x) (r : ℕ) :
    {x : V | W r x₀ x ∨ W r x₁ x}.Finite ∧
      {x : V | W r x₀ x ∨ W r x₁ x}.ncard = 2 * ∑ i ∈ Finset.range (r + 1), q ^ i := by
  have hunion : ∀ n : ℕ, {x : V | W n x₀ x ∨ W n x₁ x} = {x : V | W n x₀ x} ∪ {x : V | W n x₁ x} :=
    fun n => Set.setOf_or
  have hfin : ∀ n : ℕ, {x : V | W n x₀ x ∨ W n x₁ x}.Finite := fun n => by
    rw [hunion]
    exact (hball x₀ n).1.union (hball x₁ n).1
  refine ⟨hfin r, ?_⟩

  have hie : ∀ n : ℕ, {x : V | W n x₀ x ∨ W n x₁ x}.ncard + ({x : V | W n x₀ x} ∩ {x : V | W n x₁ x}).ncard =
      2 * (1 + ∑ i ∈ Finset.range n, (q + 1) * q ^ i) := fun n => by
    rw [hunion, Set.ncard_union_add_ncard_inter _ _ (hball x₀ n).1 (hball x₁ n).1, (hball x₀ n).2, (hball x₁ n).2,
      two_mul]
  induction r with
  | zero =>
      have h := hie 0
      rw [setOf_zero_inter_eq_empty hzero hne, Set.ncard_empty, add_zero] at h
      simpa using h
  | succ r ih =>
      have h := hie (r + 1)
      rw [setOf_succ_inter_eq hmono hedge hstep r, ih, one_add_sum_regular_eq, mul_add] at h
      exact Nat.add_right_cancel h

end EdgeTubeCount

section EdgeTube

private theorem latticeMap_scalarGL_unitOfNeZero_le [IsFractionRing R K] {ϖ : R} (hϖ : ϖ ≠ 0)
    (L : Submodule R (Fin 2 → K)) : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) L ≤ L := by
  intro x hx
  obtain ⟨w, hw, rfl⟩ := mem_latticeMap.mp hx
  rw [scalarGL_mulVec, unitOfNeZero_coe, algebraMap_smul K ϖ w]
  exact L.smul_mem ϖ hw

variable [IsFractionRing R K]

variable [IsDomain R] [IsDiscreteValuationRing R]

private theorem finite_setOf_isWithin_or_and_card_eq {ϖ : R} (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (x₀ x₁ : Vertex R K) (hadj : Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) 1 x₀ x₁) (hne : x₀ ≠ x₁)
    (r : ℕ) :
    {x : Vertex R K | Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) r x₀ x ∨
        Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) r x₁ x}.Finite ∧
      Nat.card ↥{x : Vertex R K | Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) r x₀ x ∨
        Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) r x₁ x} =
          2 * ∑ i ∈ Finset.range (r + 1), Nat.card (R ⧸ Ideal.span {ϖ}) ^ i := by
  have hc := latticeMap_scalarGL_unitOfNeZero_le (K := K) hϖ.ne_zero
  have hmono : ∀ {m n : ℕ}, m ≤ n → ∀ {a b : Vertex R K},
      Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) m a b →
        Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n a b := by
    intro m n hmn a b h
    exact h.mono hc hmn
  have hedge : ∀ (x : Vertex R K) (n : ℕ),
      (Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n x₀ x →
          Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) (n + 1) x₁ x) ∧
        (Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n x₁ x →
          Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) (n + 1) x₀ x) := by
    intro x n
    constructor
    · intro hx
      have h := LT.LatticeTree.Vertex.isWithin_add_of_isWithin_of_isWithin R K ϖ hϖ x₁ x₀ x 1 n hadj.symm hx
      rwa [add_comm] at h
    · intro hx
      have h := LT.LatticeTree.Vertex.isWithin_add_of_isWithin_of_isWithin R K ϖ hϖ x₀ x₁ x 1 n hadj hx
      rwa [add_comm] at h
  have hstep : ∀ (x : Vertex R K) (n : ℕ), Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) (n + 1) x₀ x →
      Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) (n + 1) x₁ x →
        Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n x₀ x ∨
          Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n x₁ x := by
    intro x n h₀ h₁
    by_cases hn : Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n x₀ x
    · exact Or.inl hn
    obtain ⟨y, -, hy, hz⟩ :=
      Vertex.exists_isWithin_one_and_isWithin_and_forall_not_isWithin_succ_of_isWithin_succ_of_not_isWithin
        R K ϖ hϖ x x₀ n h₀.symm (fun h => hn h.symm)
    by_cases hxy : x₁ = y
    · subst hxy
      exact Or.inr hy.symm
    · exact absurd h₁.symm (hz x₁ hadj hne.symm hxy)
  exact finite_setOf_or_and_ncard_eq (W := Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero))
    (Nat.card (R ⧸ Ideal.span {ϖ})) hmono (Vertex.isWithin_zero_iff _) hne
    (fun v d => LT.LatticeTree.finite_setOf_isWithin_and_card_eq R K ϖ hϖ v d) hedge hstep r

end EdgeTube

end LT.LatticeTree

theorem solution
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (x₀ x₁ : LT.LatticeTree.Vertex R K)
    (hadj : LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 x₀ x₁)
    (hne : x₀ ≠ x₁) (r : ℕ) :
    ({x : LT.LatticeTree.Vertex R K |
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) r x₀ x ∨
          LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) r x₁ x}).Finite ∧
    Nat.card ↥({x : LT.LatticeTree.Vertex R K |
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) r x₀ x ∨
          LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) r x₁ x}) =
      2 * ∑ i ∈ Finset.range (r + 1), Nat.card (R ⧸ Ideal.span {ϖ}) ^ i := by
  exact LT.LatticeTree.finite_setOf_isWithin_or_and_card_eq hϖ x₀ x₁ hadj hne r

end S_LT_LatticeTree_finite_setOf_isWithin_or_isWithin_and_card_eq_of_isWithin_one
end P2MW
export P2MW.S_LT_LatticeTree_finite_setOf_isWithin_or_isWithin_and_card_eq_of_isWithin_one (solution)
