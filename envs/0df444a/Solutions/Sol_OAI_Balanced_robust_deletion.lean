-- Prove2me | solution 1 for OAI.Balanced.robust_deletion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:26:03.65279+00:00
-- url     : https://prove2.me/submissions/f155e039-94e6-426e-bdd8-709a6d0b09fa

import Mathlib
import Definitions.Def_BalancedRyser
import Definitions.Def_OAIQ63Br004
import Theorems.Thm_OAI_Balanced_ProfileCountingAssembly_profileCounting_of_sourceRareTailBound
import Theorems.Thm_OAI_Balanced_robustDeletion_of_profileCounting

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_Hypergraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.PartiteHypergraph

variable {r n : ℕ}

@[simp] theorem covers_empty_iff (H : PartiteHypergraph r n) :
    H.Covers ∅ ↔ H.edges = ∅ := by
  constructor
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    rcases h e he with ⟨i, hi⟩
    exact Finset.notMem_empty _ hi
  · intro h e he
    simp [h] at he

end Balanced.PartiteHypergraph

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PermutationSubsetLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.PermutationSubsetLaw

theorem expect_comp_of_fiber_card_eq {Ω β : Type*} [DecidableEq β]
    (s : Finset Ω) (t : Finset β) (f : Ω → β) (m : ℕ) (hm : 0 < m)
    (hmap : ∀ ω ∈ s, f ω ∈ t)
    (hfiber : ∀ b ∈ t, (s.filter (fun ω => f ω = b)).card = m)
    (g : β → ℝ) :
    (𝔼 ω ∈ s, g (f ω)) = 𝔼 b ∈ t, g b := by
  classical
  have hcard : s.card = t.card * m := by
    have h := Finset.sum_card_fiberwise_eq_card_filter s t f
    rw [Finset.filter_eq_self.mpr hmap] at h
    calc
      s.card = ∑ b ∈ t, (s.filter (fun ω => f ω = b)).card := h.symm
      _ = ∑ _b ∈ t, m := Finset.sum_congr rfl hfiber
      _ = t.card * m := by simp
  have hsum : (∑ ω ∈ s, g (f ω)) = (m : ℝ) * ∑ b ∈ t, g b := by
    rw [← Finset.sum_fiberwise_of_maps_to hmap]
    calc
      _ = ∑ b ∈ t, (m : ℝ) * g b := by
        apply Finset.sum_congr rfl
        intro b hb
        calc
          (∑ ω ∈ s.filter (fun ω => f ω = b), g (f ω)) =
              ∑ _ω ∈ s.filter (fun ω => f ω = b), g b := by
            apply Finset.sum_congr rfl
            intro ω hω
            rw [(Finset.mem_filter.mp hω).2]
          _ = _ := by simp [hfiber b hb]
      _ = _ := (Finset.mul_sum _ _ _).symm
  rw [Finset.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card, hsum, hcard]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  by_cases ht : (t.card : ℝ) = 0
  · simp [ht]
  · field_simp

variable {α : Type*} [DecidableEq α]

theorem expect_eq_expect_fiber_of_card_eq {Ω β : Type*} [DecidableEq β]
    (s : Finset Ω) (t : Finset β) (f : Ω → β) (m : ℕ)
    (hmap : ∀ ω ∈ s, f ω ∈ t)
    (hfiber : ∀ b ∈ t, (s.filter (fun ω => f ω = b)).card = m)
    (g : Ω → ℝ) :
    (𝔼 ω ∈ s, g ω) = 𝔼 b ∈ t, 𝔼 ω ∈ s.filter (fun ω => f ω = b), g ω := by
  classical
  have hcard : s.card = t.card * m := by
    have h := Finset.sum_card_fiberwise_eq_card_filter s t f
    rw [Finset.filter_eq_self.mpr hmap] at h
    calc
      s.card = ∑ b ∈ t, (s.filter (fun ω => f ω = b)).card := h.symm
      _ = ∑ _b ∈ t, m := Finset.sum_congr rfl hfiber
      _ = t.card * m := by simp
  have hsum : (∑ b ∈ t, 𝔼 ω ∈ s.filter (fun ω => f ω = b), g ω) =
      (∑ ω ∈ s, g ω) / (m : ℝ) := by
    calc
      _ = ∑ b ∈ t, (∑ ω ∈ s.filter (fun ω => f ω = b), g ω) / (m : ℝ) := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [Finset.expect_eq_sum_div_card, hfiber b hb]
      _ = _ := by rw [← Finset.sum_div, Finset.sum_fiberwise_of_maps_to hmap]
  rw [Finset.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card, hsum, hcard]
  simp only [Nat.cast_mul, div_div, mul_comm]

end Balanced.PermutationSubsetLaw

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_InjectionExposureLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.InjectionExposureLaw

noncomputable section

variable {ι α : Type*} [Fintype ι] [Fintype α]
  [DecidableEq ι] [DecidableEq α]

theorem next_fiber_card_eq (S : Finset ι) (h : ι ↪ α) (i : ι)
    (a b : α) (ha : a ∈ available S h) (hb : b ∈ available S h) :
    ((history S h).filter (fun f => f i = a)).card =
      ((history S h).filter (fun f => f i = b)).card := by
  classical
  let τ := Equiv.swap a b
  have hfix (j : ι) (hj : j ∈ S) : τ (h j) = h j := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro heq
      exact (mem_available S h a).mp ha (heq ▸ Finset.mem_map.mpr ⟨j, hj, rfl⟩)
    · intro heq
      exact (mem_available S h b).mp hb (heq ▸ Finset.mem_map.mpr ⟨j, hj, rfl⟩)
  apply Finset.card_equiv (postcompose τ)
  intro f
  simp only [Finset.mem_filter, mem_history, postcompose_apply]
  constructor
  · rintro ⟨hf, hfi⟩
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [hf j hj, hfix j hj]
    · simp [τ, hfi]
  · rintro ⟨hf, hfi⟩
    refine ⟨fun j hj => ?_, ?_⟩
    · apply τ.injective
      exact (hf j hj).trans (hfix j hj).symm
    · apply τ.injective
      simpa [τ] using hfi

theorem next_mem_available (S : Finset ι) (h f : ι ↪ α) (i : ι)
    (hi : i ∉ S) (hf : f ∈ history S h) : f i ∈ available S h := by
  rw [mem_available]
  intro he
  obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp he
  have hfj : f j = f i := ((mem_history S h f).mp hf j hj).trans hji
  exact hi ((f.injective hfj) ▸ hj)

theorem expect_next_given_history (S : Finset ι) (h : ι ↪ α) (i : ι)
    (hi : i ∉ S) (g : α → ℝ) :
    (𝔼 f ∈ history S h, g (f i)) = 𝔼 x ∈ available S h, g x := by
  let m := ((history S h).filter (fun f => f i = h i)).card
  have hm : 0 < m := Finset.card_pos.mpr
    ⟨h, Finset.mem_filter.mpr ⟨self_mem_history S h, rfl⟩⟩
  apply PermutationSubsetLaw.expect_comp_of_fiber_card_eq
    (history S h) (available S h) (fun f => f i) m hm
    (fun f hf => next_mem_available S h f i hi hf)
  intro x hx
  exact next_fiber_card_eq S h i x (h i) hx
    (next_mem_available S h h i hi (self_mem_history S h))

omit [DecidableEq ι] in

theorem range_fiber_card_eq (S T : Finset α) (hST : S.card = T.card) :
    ((Finset.univ.filter (fun f : ι ↪ α => Finset.univ.map f = S)).card) =
      ((Finset.univ.filter (fun f : ι ↪ α => Finset.univ.map f = T)).card) := by
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_map_finset_eq S T hST
  apply Finset.card_equiv (postcompose τ)
  intro f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hf
    change Finset.univ.map (f.trans τ.toEmbedding) = T
    rw [← Finset.map_map, hf, hτ]
  · intro hf
    apply Finset.map_injective τ.toEmbedding
    rw [hτ]
    change Finset.univ.map (f.trans τ.toEmbedding) = T at hf
    simpa only [Finset.map_map] using hf

theorem expect_permutation_next_given_history (S : Finset α) (h : Equiv.Perm α)
    (i : α) (hi : i ∉ S) (g : α → ℝ) :
    (𝔼 σ ∈ permutationHistory S h, g (σ i)) =
      𝔼 x ∈ available S h.toEmbedding, g x := by
  calc
    _ = 𝔼 f ∈ history S h.toEmbedding, g (f i) := by
      symm
      apply Finset.expect_equiv selfEmbeddingEquivPerm
      · intro f
        simp only [history, permutationHistory, Finset.mem_filter, Finset.mem_univ, true_and]
        rfl
      · intro f _
        rfl
    _ = _ := expect_next_given_history S h.toEmbedding i hi g

end
end Balanced.InjectionExposureLaw

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_AffineDoubleCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open scoped BigOperators

section DoubleCounting

variable {P L : Type*} [Fintype L]
variable (I : P → L → Prop) [DecidableRel I]

theorem sum_line_count_eq_sum_point_count (U : Finset P) :
    (∑ l : L, (U.filter fun p => I p l).card) =
      ∑ p ∈ U, ((Finset.univ : Finset L).filter fun l => I p l).card := by
  simpa only [Finset.bipartiteAbove, Finset.bipartiteBelow] using
    (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (r := I) (s := U) (t := Finset.univ)).symm

theorem sum_line_count (U : Finset P) (r : ℕ)
    (hpoint : ∀ p ∈ U,
      ((Finset.univ : Finset L).filter fun l => I p l).card = r) :
    (∑ l : L, (U.filter fun p => I p l).card) = r * U.card := by
  rw [sum_line_count_eq_sum_point_count]
  calc
    (∑ p ∈ U, ((Finset.univ : Finset L).filter fun l => I p l).card) =
        ∑ _p ∈ U, r := Finset.sum_congr rfl hpoint
    _ = r * U.card := by simp [Nat.mul_comm]

theorem sum_sq_line_count_eq_sum_pair_count (U : Finset P) :
    (∑ l : L, (U.filter fun p => I p l).card ^ 2) =
      ∑ p ∈ U, ∑ p' ∈ U,
        ((Finset.univ : Finset L).filter fun l => I p l ∧ I p' l).card := by
  classical
  have hline (l : L) :
      (U.filter fun p => I p l).card ^ 2 =
        ∑ p ∈ U, ∑ p' ∈ U, if I p l ∧ I p' l then 1 else 0 := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro p' hp'
    by_cases h : I p l <;> by_cases h' : I p' l <;> simp [h, h']
  simp_rw [hline]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p' hp'
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]

theorem sum_sq_line_count (U : Finset P) (q : ℕ)
    (hpoint : ∀ p ∈ U,
      ((Finset.univ : Finset L).filter fun l => I p l).card = q + 1)
    (hpair : ∀ p ∈ U, ∀ p' ∈ U, p ≠ p' →
      ((Finset.univ : Finset L).filter fun l => I p l ∧ I p' l).card = 1) :
    (∑ l : L, (U.filter fun p => I p l).card ^ 2) =
      U.card ^ 2 + q * U.card := by
  classical
  rw [sum_sq_line_count_eq_sum_pair_count]
  have hcommon (p : P) (hp : p ∈ U) (p' : P) (hp' : p' ∈ U) :
      ((Finset.univ : Finset L).filter fun l => I p l ∧ I p' l).card =
        1 + if p' = p then q else 0 := by
    by_cases h : p' = p
    · subst p'
      simp [hpoint p hp, Nat.add_comm]
    · simp [h, hpair p hp p' hp' (Ne.symm h)]
  calc
    (∑ p ∈ U, ∑ p' ∈ U,
      ((Finset.univ : Finset L).filter fun l => I p l ∧ I p' l).card) =
        ∑ p ∈ U, ∑ p' ∈ U, (1 + if p' = p then q else 0) := by
          apply Finset.sum_congr rfl
          intro p hp
          apply Finset.sum_congr rfl
          intro p' hp'
          exact hcommon p hp p' hp'
    _ = ∑ p ∈ U, (U.card + q) := by
      apply Finset.sum_congr rfl
      intro p hp
      simp [Finset.sum_add_distrib, hp]
    _ = U.card ^ 2 + q * U.card := by
      simp only [Finset.sum_const, smul_eq_mul]
      ring

theorem common_line_count_of_existsUnique (p p' : P)
    (h : ∃! l : L, I p l ∧ I p' l) :
    ((Finset.univ : Finset L).filter fun l => I p l ∧ I p' l).card = 1 := by
  classical
  obtain ⟨l, hl, hunique⟩ := h
  apply Finset.card_eq_one.mpr
  refine ⟨l, ?_⟩
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun hk => hunique k hk, fun hk => hk ▸ hl⟩

theorem sum_sq_line_count_of_unique (U : Finset P) (q : ℕ)
    (hpoint : ∀ p ∈ U,
      ((Finset.univ : Finset L).filter fun l => I p l).card = q + 1)
    (hpair : ∀ p ∈ U, ∀ p' ∈ U, p ≠ p' → ∃! l : L, I p l ∧ I p' l) :
    (∑ l : L, (U.filter fun p => I p l).card ^ 2) =
      U.card ^ 2 + q * U.card := by
  apply sum_sq_line_count I U q hpoint
  intro p hp p' hp' hne
  exact common_line_count_of_existsUnique I p p' (hpair p hp p' hp' hne)

end DoubleCounting

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_AffineIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

variable {F : Type*} [Field F]

section Finite

variable [Fintype F] [DecidableEq F]

theorem card_lines_through (p : Point F) :
    ((Finset.univ : Finset (Line F)).filter fun l => OnLine p l).card =
      Fintype.card F + 1 := by
  rw [← Fintype.card_subtype]
  exact (Fintype.card_congr (linesThroughEquiv p)).trans Fintype.card_option

end Finite

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_AffineMomentAlgebraLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace Balanced.MomentAlgebra

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem centered_sum_expansion (a : ι → ℝ) (m : ℝ) :
    ∑ i, (a i - m) ^ 2 =
      (∑ i, (a i) ^ 2) - 2 * m * (∑ i, a i) +
        (Fintype.card ι : ℝ) * m ^ 2 := by
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  ring

theorem affine_centered_sum (a : ι → ℝ) (q N : ℝ) (hq : q ≠ 0)
    (hcard : (Fintype.card ι : ℝ) = q * (q + 1))
    (hfirst : ∑ i, a i = (q + 1) * N)
    (hsecond : ∑ i, (a i) ^ 2 = N ^ 2 + q * N) :
    ∑ i, (a i - N / q) ^ 2 = q * N - N ^ 2 / q := by
  rw [centered_sum_expansion, hcard, hfirst, hsecond]
  field_simp
  ring

theorem affine_variance_bound (q N : ℝ) (hq : 0 < q) :
    q * N - N ^ 2 / q ≤ q ^ 3 / 4 := by
  have hsq := sq_nonneg (N - q ^ 2 / 2)
  apply (le_div_iff₀ (show (0 : ℝ) < 4 by norm_num)).2
  apply (mul_le_mul_iff_right₀ hq).mp
  field_simp
  nlinarith

theorem affine_centered_sum_le (a : ι → ℝ) (q N : ℝ) (hq : 0 < q)
    (hcard : (Fintype.card ι : ℝ) = q * (q + 1))
    (hfirst : ∑ i, a i = (q + 1) * N)
    (hsecond : ∑ i, (a i) ^ 2 = N ^ 2 + q * N) :
    ∑ i, (a i - N / q) ^ 2 ≤ q ^ 3 / 4 := by
  rw [affine_centered_sum a q N hq.ne' hcard hfirst hsecond]
  exact affine_variance_bound q N hq

theorem directional_variance_sum {δ κ : Type*} [Fintype δ] [Fintype κ]
    (a : δ × κ → ℝ) (q N : ℝ) (hq : q ≠ 0)
    (htotal : ∑ i, (a i - N / q) ^ 2 = q * N - N ^ 2 / q) :
    ∑ d, (1 / q) * ∑ j, (a (d, j) - N / q) ^ 2 =
      N - N ^ 2 / q ^ 2 := by
  rw [← Finset.mul_sum, ← Fintype.sum_prod_type (fun i : δ × κ => (a i - N / q) ^ 2), htotal]
  field_simp

theorem directional_variance_le_count (q N : ℝ) :
    N - N ^ 2 / q ^ 2 ≤ N := by
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (sq_nonneg _))

end Balanced.MomentAlgebra

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_AffineSecondMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] [DecidableEq F] in

theorem affine_point_count_le (U : Finset (Point F)) :
    (U.card : ℝ) ≤ (Fintype.card F : ℝ) ^ 2 := by
  have h := Finset.card_le_univ U
  simp only [Point, Fintype.card_prod] at h
  rw [pow_two]
  exact_mod_cast h

omit [Field F] [DecidableEq F] in

theorem affine_line_count_real :
    (Fintype.card (Line F) : ℝ) =
      (Fintype.card F : ℝ) * ((Fintype.card F : ℝ) + 1) := by
  simp only [Line, Direction, Fintype.card_prod, Fintype.card_option,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  ring

theorem affine_second_moment_of_raw_counts
    (hfirst : ∀ U : Finset (Point F),
      ∑ l : Line F, affineIntersectionCount U l =
        (Fintype.card F + 1) * U.card)
    (hsecond : ∀ U : Finset (Point F),
      ∑ l : Line F, affineIntersectionCount U l ^ 2 =
        U.card ^ 2 + Fintype.card F * U.card) :
    AffineSecondMoment F := by
  intro U
  let q : ℝ := Fintype.card F
  let N : ℝ := U.card
  let a : Line F → ℝ := fun l => affineIntersectionCount U l
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast Fintype.card_pos (α := F)
  have hc : (Fintype.card (Line F) : ℝ) = q * (q + 1) :=
    affine_line_count_real
  have h₁ : ∑ l, a l = (q + 1) * N := by
    dsimp [a, q, N]
    exact_mod_cast hfirst U
  have h₂ : ∑ l, a l ^ 2 = N ^ 2 + q * N := by
    dsimp [a, q, N]
    exact_mod_cast hsecond U
  have h₃ := MomentAlgebra.affine_centered_sum a q N hq.ne' hc h₁ h₂
  have h₄ := MomentAlgebra.affine_centered_sum_le a q N hq hc h₁ h₂
  have h₅ : (∑ d : Direction F, affineDirectionalVariance U d) =
      N - N ^ 2 / q ^ 2 := by
    exact MomentAlgebra.directional_variance_sum a q N hq.ne' h₃
  refine ⟨h₁, h₂, h₃, h₄, h₅, ?_, affine_point_count_le U⟩
  rw [h₅]
  exact MomentAlgebra.directional_variance_le_count q N

theorem affineSecondMoment_proof : AffineSecondMoment F := by
  apply affine_second_moment_of_raw_counts
  · intro U
    exact sum_line_count OnLine U (Fintype.card F + 1)
      (fun p _ => card_lines_through p)
  · intro U
    exact sum_sq_line_count_of_unique OnLine U (Fintype.card F)
      (fun p _ => card_lines_through p)
      (fun p _ r _ hne => existsUnique_line_of_ne p r hne)

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_MarkedExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ENNReal
open MeasureTheory

namespace Balanced.MarkedExposure

variable {Ω ι : Type*}

theorem atLeast_subset_union (s : Finset ι) (E : ι → Set Ω) (r : ℕ) :
    atLeast s E r ⊆ ⋃ t ∈ s.powersetCard r, ⋂ i ∈ t, E i := by
  classical
  intro ω hω
  change r ≤ (s.filter fun i => ω ∈ E i).card at hω
  obtain ⟨t, ht, hcard⟩ := Finset.exists_subset_card_eq hω
  refine Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
  · exact Finset.mem_powersetCard.mpr ⟨ht.trans (Finset.filter_subset _ _), hcard⟩
  · simp only [Set.mem_iInter]
    intro i hi
    exact (Finset.mem_filter.mp (ht hi)).2

variable [MeasurableSpace Ω]

theorem tail_le_choose_mul (μ : Measure Ω) (s : Finset ι) (E : ι → Set Ω)
    (r : ℕ) (p : ℝ≥0∞)
    (h : ∀ t ∈ s.powersetCard r, μ (⋂ i ∈ t, E i) ≤ p ^ r) :
    μ (atLeast s E r) ≤ (s.card.choose r : ℝ≥0∞) * p ^ r := by
  classical
  calc
    μ (atLeast s E r) ≤ μ (⋃ t ∈ s.powersetCard r, ⋂ i ∈ t, E i) :=
      measure_mono (atLeast_subset_union s E r)
    _ ≤ ∑ t ∈ s.powersetCard r, μ (⋂ i ∈ t, E i) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _t ∈ s.powersetCard r, p ^ r := Finset.sum_le_sum h
    _ = (s.card.choose r : ℝ≥0∞) * p ^ r := by simp

theorem tail_le_two_pow_mul (μ : Measure Ω) (s : Finset ι) (E : ι → Set Ω)
    (r : ℕ) (p : ℝ≥0∞)
    (h : ∀ t ∈ s.powersetCard r, μ (⋂ i ∈ t, E i) ≤ p ^ r) :
    μ (atLeast s E r) ≤ (2 : ℝ≥0∞) ^ s.card * p ^ r := by
  refine (tail_le_choose_mul μ s E r p h).trans ?_
  apply mul_le_mul_left
  exact_mod_cast Nat.choose_le_two_pow s.card r

theorem normalized_deviation_iff (x N q ε : ℝ) (hq : 0 < q) :
    ε < |x / q - N / q ^ 2| ↔ ε * q < |x - N / q| := by
  have heq : x / q - N / q ^ 2 = (x - N / q) / q := by
    field_simp
  rw [heq, abs_div, abs_of_pos hq, lt_div_iff₀ hq]

theorem card_large_deviations_le (s : Finset ι) (x : ι → ℝ)
    (mean q ε : ℝ) (hq : 0 < q) (hε : 0 < ε)
    (hvariance : ∑ i ∈ s, (x i - mean) ^ 2 ≤ q ^ 3 / 4) :
    ((s.filter fun i => ε * q < |x i - mean|).card : ℝ) ≤ q / (4 * ε ^ 2) := by
  classical
  let b := s.filter fun i => ε * q < |x i - mean|
  have hlower : (b.card : ℝ) * (ε * q) ^ 2 ≤ q ^ 3 / 4 := by
    calc
      (b.card : ℝ) * (ε * q) ^ 2 = ∑ _i ∈ b, (ε * q) ^ 2 := by simp
      _ ≤ ∑ i ∈ b, (x i - mean) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := (Finset.mem_filter.mp hi).2
        have hs := (sq_le_sq₀ (by positivity : 0 ≤ ε * q) (abs_nonneg (x i - mean))).2 hi'.le
        simpa only [sq_abs] using hs
      _ ≤ ∑ i ∈ s, (x i - mean) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => sq_nonneg _)
      _ ≤ q ^ 3 / 4 := hvariance
  change (b.card : ℝ) ≤ q / (4 * ε ^ 2)
  apply (le_div_iff₀ (by positivity : 0 < 4 * ε ^ 2)).mpr
  apply (mul_le_mul_iff_left₀ (by positivity : 0 < q ^ 2)).mp
  nlinarith [hlower]

theorem mass_large_deviations_le (s : Finset ι) (x w : ι → ℝ)
    (mean q ε C : ℝ) (hq : 0 < q) (hε : 0 < ε) (hC : 0 ≤ C)
    (hvariance : ∑ i ∈ s, (x i - mean) ^ 2 ≤ q ^ 3 / 4)
    (hweight : ∀ i ∈ s, w i ≤ C / q ^ 2) :
    (∑ i ∈ s.filter (fun i => ε * q < |x i - mean|), w i) ≤ C / (4 * ε ^ 2 * q) := by
  classical
  let b := s.filter fun i => ε * q < |x i - mean|
  have hcard := card_large_deviations_le s x mean q ε hq hε hvariance
  change (b.card : ℝ) ≤ q / (4 * ε ^ 2) at hcard
  calc
    (∑ i ∈ b, w i) ≤ ∑ _i ∈ b, C / q ^ 2 := by
      exact Finset.sum_le_sum (fun i hi => hweight i (Finset.mem_filter.mp hi).1)
    _ = (b.card : ℝ) * (C / q ^ 2) := by simp
    _ ≤ (q / (4 * ε ^ 2)) * (C / q ^ 2) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = C / (4 * ε ^ 2 * q) := by field_simp

end Balanced.MarkedExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_CountingExposureKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
namespace Balanced.CountingExposureKernel
noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
theorem uniformSetWeight_nonneg (s : Finset α) (a : α) :
    0 ≤ uniformSetWeight s a := by
  unfold uniformSetWeight
  split_ifs <;> positivity

omit [Fintype α] in
theorem uniformSetWeight_le (s : Finset α) (a : α) :
    uniformSetWeight s a ≤ (s.card : ℝ)⁻¹ := by
  unfold uniformSetWeight
  split_ifs
  · exact le_rfl
  · positivity

variable {F : Type*} [Fintype F] [DecidableEq F]

theorem tokenWeight_le_two_div (r : Direction F → ℕ)
    (used : Direction F → Finset F) (k : ℕ) (η : ℝ)
    (hk : 0 < k) (hη : 0 < η) (hqk : 2 * k ≤ Fintype.card F)
    (hr : ∀ d, r d ≤ k) (hu : ∀ d, (used d).card ≤ k)
    (hremaining : η * (k : ℝ) * ((Fintype.card F : ℝ) + 1) ≤
      ∑ d, (r d : ℝ)) (l : Line F) :
    tokenWeight r used l ≤ 2 / (η * (Fintype.card F : ℝ) ^ 2) := by
  let q : ℝ := Fintype.card F
  have hq : 0 < q := by dsimp [q]; exact_mod_cast (by omega : 0 < Fintype.card F)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkq : k ≤ Fintype.card F := by omega
  have htot : 0 < ∑ d, (r d : ℝ) :=
    lt_of_lt_of_le (mul_pos (mul_pos hη hkR) (by positivity)) hremaining
  have hdir : (r l.1 : ℝ) / (∑ d, (r d : ℝ)) ≤ 1 / (η * q) := by
    apply (div_le_div_iff₀ htot (mul_pos hη hq)).mpr
    have hrR : (r l.1 : ℝ) ≤ k := by exact_mod_cast hr l.1
    have hm := mul_le_mul_of_nonneg_right hrR (mul_nonneg hη.le hq.le)
    dsimp [q] at hm ⊢
    nlinarith [mul_nonneg hη.le hkR.le]
  have hused : (used l.1).card ≤ Fintype.card F := (hu l.1).trans hkq
  have hcard : ((available (used l.1)).card : ℝ) = q - (used l.1).card := by
    rw [card_available, Nat.cast_sub hused]
  have havail : q / 2 ≤ ((available (used l.1)).card : ℝ) := by
    rw [hcard]
    have hx : ((used l.1).card : ℝ) ≤ k := by exact_mod_cast hu l.1
    have hy : 2 * (k : ℝ) ≤ q := by dsimp [q]; exact_mod_cast hqk
    linarith
  have hoff : uniformSetWeight (available (used l.1)) l.2 ≤ 2 / q := by
    calc
      uniformSetWeight (available (used l.1)) l.2 ≤
          ((available (used l.1)).card : ℝ)⁻¹ := uniformSetWeight_le _ _
      _ ≤ 1 / (q / 2) := by
        simpa only [one_div] using one_div_le_one_div_of_le (by positivity : 0 < q / 2) havail
      _ = 2 / q := by ring
  calc
    tokenWeight r used l ≤ (1 / (η * q)) * (2 / q) :=
      mul_le_mul hdir hoff (uniformSetWeight_nonneg _ _) (by positivity)
    _ = 2 / (η * (Fintype.card F : ℝ) ^ 2) := by dsimp [q]; ring

variable [Field F]

theorem markedLines_eq (U : Finset (Point F)) (ε : ℝ) :
    markedLines U ε = Finset.univ.filter (fun l =>
      ε * Fintype.card F < |(affineIntersectionCount U l : ℝ) -
        (U.card : ℝ) / Fintype.card F|) := by
  apply Finset.filter_congr
  intro l _
  exact MarkedExposure.normalized_deviation_iff _ _ _ _
    (by exact_mod_cast Fintype.card_pos (α := F))

theorem marked_mass_le (U : Finset (Point F)) (ε C : ℝ) (w : Line F → ℝ)
    (hε : 0 < ε) (hC : 0 ≤ C)
    (hw : ∀ l, w l ≤ C / (Fintype.card F : ℝ) ^ 2) :
    (∑ l ∈ markedLines U ε, w l) ≤ C / (4 * ε ^ 2 * Fintype.card F) := by
  rw [markedLines_eq]
  exact MarkedExposure.mass_large_deviations_le Finset.univ
    (fun l => (affineIntersectionCount U l : ℝ)) w
    ((U.card : ℝ) / Fintype.card F) (Fintype.card F) ε C
    (by exact_mod_cast Fintype.card_pos (α := F)) hε hC
    (affineSecondMoment_proof (F := F) U).2.2.2.1 (fun l _ => hw l)

theorem token_marked_mass_le (U : Finset (Point F)) (ε : ℝ)
    (r : Direction F → ℕ) (used : Direction F → Finset F) (k : ℕ) (η : ℝ)
    (hε : 0 < ε) (hk : 0 < k) (hη : 0 < η)
    (hqk : 2 * k ≤ Fintype.card F)
    (hr : ∀ d, r d ≤ k) (hu : ∀ d, (used d).card ≤ k)
    (hremaining : η * (k : ℝ) * ((Fintype.card F : ℝ) + 1) ≤
      ∑ d, (r d : ℝ)) :
    (∑ l ∈ markedLines U ε, tokenWeight r used l) ≤
      (2 / η) / (4 * ε ^ 2 * Fintype.card F) := by
  apply marked_mass_le U ε (2 / η) (tokenWeight r used) hε (by positivity)
  intro l
  simpa only [div_div] using tokenWeight_le_two_div r used k η hk hη hqk hr hu
    hremaining l

end
end Balanced.CountingExposureKernel

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_CountingExposurePosterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.CountingExposurePosterior

noncomputable section
attribute [local instance] Classical.propDecidable
open InjectionExposureLaw

theorem expect_subtype {α : Type*} (s : Finset α) (g : α → ℝ) :
    (𝔼 x ∈ s, g x) = 𝔼 x : s, g x := by
  rw [Finset.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card, Fintype.card_coe]
  congr 1
  exact Finset.sum_subtype s (fun _ => Iff.rfl) g

theorem expect_pi_apply {G : Type*} [Fintype G] [DecidableEq G]
    (Ω : G → Type*) [∀ d, Fintype (Ω d)] [∀ d, Nonempty (Ω d)]
    (d : G) (g : Ω d → ℝ) :
    (𝔼 f : ∀ d, Ω d, g (f d)) = 𝔼 x : Ω d, g x := by
  calc
    _ = 𝔼 x : Ω d × (∀ j : {j // j ≠ d}, Ω j), g x.1 := by
      apply Fintype.expect_equiv (Equiv.piSplitAt d Ω)
      intro f
      rfl
    _ = _ := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
      simp only [Fintype.expect_const]

variable {G ι α : Type*} [Fintype G] [Fintype ι] [Fintype α]
  [DecidableEq G] [DecidableEq ι] [DecidableEq α]

omit [Fintype G] in
theorem offsetHistoryCoordinateNonempty (S : Finset (G × ι)) (h : G → ι ↪ α)
    (d : G) : Nonempty {f : ι ↪ α // f ∈ history (exposedIndices S d) (h d)} :=
  ⟨⟨h d, self_mem_history _ _⟩⟩

theorem expect_offset_given_history (S : Finset (G × ι)) (h : G → ι ↪ α)
    (t : G × ι) (ht : t ∉ S) (g : α → ℝ) :
    (𝔼 f : OffsetHistory S h, g ((f t.1).val t.2)) =
      𝔼 x ∈ available (exposedIndices S t.1) (h t.1), g x := by
  let (d : G) : Nonempty {f : ι ↪ α // f ∈ history (exposedIndices S d) (h d)} :=
    offsetHistoryCoordinateNonempty S h d
  have hi : t.2 ∉ exposedIndices S t.1 := by simpa [exposedIndices] using ht
  calc
    _ = 𝔼 f : {f : ι ↪ α // f ∈ history (exposedIndices S t.1) (h t.1)},
        g (f.val t.2) := expect_pi_apply
          (fun d : G => {f : ι ↪ α // f ∈ history (exposedIndices S d) (h d)})
          t.1 (fun f => g (f.val t.2))
    _ = 𝔼 f ∈ history (exposedIndices S t.1) (h t.1), g (f t.2) :=
      (expect_subtype (history (exposedIndices S t.1) (h t.1))
        (fun f : ι ↪ α => g (f t.2))).symm
    _ = _ := expect_next_given_history (exposedIndices S t.1) (h t.1) t.2 hi g

theorem expect_history_factorization (P : Finset (G × ι))
    (π : Equiv.Perm (G × ι)) (h : G → ι ↪ α)
    (g : Experiment (G := G) (ι := ι) (α := α) → ℝ) :
    (𝔼 ω ∈ countingHistory P π h, g ω) =
      𝔼 σ ∈ permutationHistory P π,
        𝔼 f : OffsetHistory (P.map π.toEmbedding) h,
          g (σ, fun d => (f d).val) := by
  let S := P.map π.toEmbedding
  calc
    _ = 𝔼 ω : ↥(countingHistory P π h), g ω.val :=
      expect_subtype (countingHistory P π h) g
    _ = 𝔼 x : ↥(permutationHistory P π) × OffsetHistory S h,
        g (x.1.val, fun d => (x.2 d).val) := by
      apply Fintype.expect_equiv (historyEquiv P π h)
      intro ω
      rfl
    _ = 𝔼 σ : ↥(permutationHistory P π), 𝔼 f : OffsetHistory S h,
        g (σ.val, fun d => (f d).val) := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
    _ = _ := (expect_subtype (permutationHistory P π)
      (fun σ => 𝔼 f : OffsetHistory S h, g (σ, fun d => (f d).val))).symm

theorem expect_nextLine_given_history (P : Finset (G × ι))
    (π : Equiv.Perm (G × ι)) (h : G → ι ↪ α) (i : G × ι) (hi : i ∉ P)
    (g : G × α → ℝ) :
    (𝔼 ω ∈ countingHistory P π h, g (nextLine ω i)) =
      𝔼 t ∈ available P π.toEmbedding,
        𝔼 x ∈ available (exposedIndices (P.map π.toEmbedding) t.1) (h t.1),
          g (t.1, x) := by
  rw [expect_history_factorization P π h (fun ω => g (nextLine ω i))]
  let S := P.map π.toEmbedding
  calc
    _ = 𝔼 σ ∈ permutationHistory P π,
        𝔼 x ∈ available (exposedIndices S (σ i).1) (h (σ i).1),
          g ((σ i).1, x) := by
      apply Finset.expect_congr rfl
      intro σ hσ
      have he : σ i ∉ S := by
        apply (mem_available P π.toEmbedding (σ i)).mp
        apply next_mem_available P π.toEmbedding σ.toEmbedding i hi
        simpa [history, permutationHistory] using hσ
      exact expect_offset_given_history S h (σ i) he (fun x => g ((σ i).1, x))
    _ = _ := expect_permutation_next_given_history P π i hi
      (fun t => 𝔼 x ∈ available (exposedIndices S t.1) (h t.1), g (t.1, x))

theorem sum_remaining_by_direction (S : Finset (G × ι)) (a : G → ℝ) :
    (∑ t ∈ Finset.univ \ S, a t.1) =
      ∑ d, (remainingTokens S d : ℝ) * a d := by
  have heq : Finset.univ \ S = Finset.univ.filter (fun t : G × ι => t ∉ S) := by
    ext t; simp
  rw [heq, Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_filter]
  simp [remainingTokens]

theorem sum_remainingTokens (S : Finset (G × ι)) :
    (∑ d, (remainingTokens S d : ℝ)) = ((Finset.univ \ S).card : ℝ) := by
  simpa using (sum_remaining_by_direction S (fun _ => (1 : ℝ))).symm

theorem expect_remaining_by_direction (S : Finset (G × ι)) (a : G → ℝ) :
    (𝔼 t ∈ Finset.univ \ S, a t.1) =
      ∑ d, ((remainingTokens S d : ℝ) / ∑ e, (remainingTokens S e : ℝ)) * a d := by
  rw [Finset.expect_eq_sum_div_card, sum_remaining_by_direction, sum_remainingTokens,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem expect_nextLine_direction_mixture (P : Finset (G × ι))
    (π : Equiv.Perm (G × ι)) (h : G → ι ↪ α) (i : G × ι) (hi : i ∉ P)
    (g : G × α → ℝ) :
    (𝔼 ω ∈ countingHistory P π h, g (nextLine ω i)) =
      ∑ d, ((remainingTokens (P.map π.toEmbedding) d : ℝ) /
        ∑ e, (remainingTokens (P.map π.toEmbedding) e : ℝ)) *
        (𝔼 x ∈ available (exposedIndices (P.map π.toEmbedding) d) (h d), g (d, x)) := by
  rw [expect_nextLine_given_history P π h i hi g]
  exact expect_remaining_by_direction (P.map π.toEmbedding)
    (fun d => 𝔼 x ∈ available (exposedIndices (P.map π.toEmbedding) d) (h d), g (d, x))

section AffineTokens
variable {F : Type*} [Fintype F] [DecidableEq F] {k : ℕ}

theorem nextLine_probability_eq_tokenWeight
    (P : Finset (Direction F × Fin k)) (π : Equiv.Perm (Direction F × Fin k))
    (h : Direction F → Fin k ↪ F) (i : Direction F × Fin k) (hi : i ∉ P)
    (l : Line F) :
    (𝔼 ω ∈ countingHistory P π h, if nextLine ω i = l then (1 : ℝ) else 0) =
      CountingExposureKernel.tokenWeight (remainingTokens (P.map π.toEmbedding))
        (usedOffsets (P.map π.toEmbedding) h) l := by
  rw [expect_nextLine_direction_mixture P π h i hi
    (fun y => if y = l then (1 : ℝ) else 0)]
  rw [Finset.sum_eq_single l.1]
  · unfold CountingExposureKernel.tokenWeight
    congr 1
    rw [Finset.expect_eq_sum_div_card]
    have hpair (x : F) : (l.1, x) = l ↔ x = l.2 := by cases l; simp
    simp [hpair, InjectionExposureLaw.available, usedOffsets,
      CountingExposureKernel.uniformSetWeight, CountingExposureKernel.available,
      ite_div, one_div]
  · intro d _ hd
    have he (x : F) : (d, x) ≠ l := by
      intro hx
      exact hd (congrArg Prod.fst hx)
    simp [he, Finset.expect]
  · simp

omit [Fintype F] in

theorem history_counts_le (S : Finset (Direction F × Fin k))
    (h : Direction F → Fin k ↪ F) (d : Direction F) :
    remainingTokens S d ≤ k ∧ (usedOffsets S h d).card ≤ k := by
  constructor
  · simpa [remainingTokens] using
      (Finset.card_filter_le (s := (Finset.univ : Finset (Fin k)))
        (p := fun j => (d, j) ∉ S))
  · simpa [usedOffsets, exposedIndices] using
      (Finset.card_filter_le (s := (Finset.univ : Finset (Fin k)))
        (p := fun j => (d, j) ∈ S))

variable [Field F]

theorem marked_probability_given_history_le
    (P : Finset (Direction F × Fin k)) (π : Equiv.Perm (Direction F × Fin k))
    (h : Direction F → Fin k ↪ F) (i : Direction F × Fin k) (hi : i ∉ P)
    (U : Finset (Point F)) (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η)
    (hk : 0 < k) (hqk : 2 * k ≤ Fintype.card F)
    (hremaining : η * (k : ℝ) * ((Fintype.card F : ℝ) + 1) ≤
      ∑ d, (remainingTokens (P.map π.toEmbedding) d : ℝ)) :
    (𝔼 ω ∈ countingHistory P π h,
      if nextLine ω i ∈ CountingExposureKernel.markedLines U ε then (1 : ℝ) else 0) ≤
        (2 / η) / (4 * ε ^ 2 * Fintype.card F) := by
  let A := CountingExposureKernel.markedLines U ε
  calc
    _ = 𝔼 ω ∈ countingHistory P π h,
        ∑ l ∈ A, if nextLine ω i = l then (1 : ℝ) else 0 := by
      apply Finset.expect_congr rfl
      intro ω _
      simp [A]
    _ = ∑ l ∈ A, 𝔼 ω ∈ countingHistory P π h,
        if nextLine ω i = l then (1 : ℝ) else 0 :=
      Finset.expect_sum_comm _ _ _
    _ = ∑ l ∈ A, CountingExposureKernel.tokenWeight
        (remainingTokens (P.map π.toEmbedding)) (usedOffsets (P.map π.toEmbedding) h) l := by
      apply Finset.sum_congr rfl
      intro l _
      exact nextLine_probability_eq_tokenWeight P π h i hi l
    _ ≤ _ := CountingExposureKernel.token_marked_mass_le U ε
      (remainingTokens (P.map π.toEmbedding)) (usedOffsets (P.map π.toEmbedding) h)
      k η hε hk hη hqk
      (fun d => (history_counts_le (P.map π.toEmbedding) h d).1)
      (fun d => (history_counts_le (P.map π.toEmbedding) h d).2) hremaining

end AffineTokens

end
end Balanced.CountingExposurePosterior

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_AtypicalLines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace AtypicalLines

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem card_large_abs_le (a : ι → ℝ) (r B : ℝ) (hr : 0 < r)
    (hsum : ∑ i, a i ^ 2 ≤ B) :
    ((Finset.univ.filter (fun i => r < |a i|)).card : ℝ) ≤ B / r ^ 2 := by
  classical
  apply (le_div_iff₀ (sq_pos_of_pos hr)).2
  calc
    ((Finset.univ.filter (fun i => r < |a i|)).card : ℝ) * r ^ 2 =
        ∑ i ∈ Finset.univ.filter (fun i => r < |a i|), r ^ 2 := by simp
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i => r < |a i|), a i ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply le_of_lt
      apply sq_lt_sq.mpr
      simpa [abs_of_pos hr] using (Finset.mem_filter.mp hi).2
    _ ≤ ∑ i, a i ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro i hi hnot
      exact sq_nonneg _
    _ ≤ B := hsum

theorem normalized_sum_sq_le (a : ι → ℝ) (q N : ℝ) (hq : 0 < q)
    (hsum : ∑ i, (a i - N / q) ^ 2 ≤ q ^ 3 / 4) :
    ∑ i, (a i / q - N / q ^ 2) ^ 2 ≤ q / 4 := by
  have heq (i : ι) : (a i / q - N / q ^ 2) ^ 2 =
      (a i - N / q) ^ 2 / q ^ 2 := by
    field_simp
  simp_rw [heq]
  rw [← Finset.sum_div]
  apply (div_le_iff₀ (sq_pos_of_pos hq)).2
  nlinarith [hsum]

theorem card_normalized_deviation_le (a : ι → ℝ) (q N ε : ℝ)
    (hq : 0 < q) (hε : 0 < ε)
    (hsum : ∑ i, (a i - N / q) ^ 2 ≤ q ^ 3 / 4) :
    ((Finset.univ.filter (fun i => ε < |a i / q - N / q ^ 2|)).card : ℝ) ≤
      q / (4 * ε ^ 2) := by
  have h := card_large_abs_le (fun i => a i / q - N / q ^ 2) ε (q / 4) hε
    (normalized_sum_sq_le a q N hq hsum)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem affine_card_marked_lines_le {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] (U : Finset (Point F)) (ε : ℝ) (hε : 0 < ε) :
    ((Finset.univ.filter (fun l : Line F =>
      ε < |(affineIntersectionCount U l : ℝ) / (Fintype.card F : ℝ) -
        (U.card : ℝ) / (Fintype.card F : ℝ) ^ 2|)).card : ℝ) ≤
      (Fintype.card F : ℝ) / (4 * ε ^ 2) := by
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := F)
  exact card_normalized_deviation_le
    (fun l : Line F => (affineIntersectionCount U l : ℝ))
    (Fintype.card F : ℝ) (U.card : ℝ) ε hq hε
    (affineSecondMoment_proof (F := F) U).2.2.2.1

end AtypicalLines
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PermutationHistoryLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.PermutationHistoryLaw

noncomputable section
open Finset PermutationSubsetLaw

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem histories_nonempty (I : Finset α) (σ₀ : Equiv.Perm α) :
    (histories I σ₀).Nonempty := by
  exact ⟨σ₀, by simp⟩

theorem next_mem_unused (I : Finset α) (σ₀ : Equiv.Perm α)
    (i : α) (hi : i ∉ I) (σ : Equiv.Perm α) (hσ : σ ∈ histories I σ₀) :
    σ i ∈ unused I σ₀ := by
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro h
  obtain ⟨j, hj, heq⟩ := Finset.mem_map.mp h
  have hval := (mem_histories I σ₀ σ).mp hσ j hj
  have hji : j = i := σ.injective (hval.trans heq)
  exact hi (hji ▸ hj)

theorem swap_preserves_history (I : Finset α) (σ₀ σ : Equiv.Perm α)
    (x y : α) (hx : x ∈ unused I σ₀) (hy : y ∈ unused I σ₀)
    (hσ : σ ∈ histories I σ₀) :
    σ.trans (Equiv.swap x y) ∈ histories I σ₀ := by
  apply (mem_histories _ _ _).mpr
  intro j hj
  have hval := (mem_histories I σ₀ σ).mp hσ j hj
  change Equiv.swap x y (σ j) = σ₀ j
  rw [hval]
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    exact (Finset.mem_sdiff.mp hx).2
      (Finset.mem_map.mpr ⟨j, hj, h⟩)
  · intro h
    exact (Finset.mem_sdiff.mp hy).2
      (Finset.mem_map.mpr ⟨j, hj, h⟩)

theorem next_fiber_card_eq (I : Finset α) (σ₀ : Equiv.Perm α) (i x y : α)
    (hx : x ∈ unused I σ₀) (hy : y ∈ unused I σ₀) :
    ((histories I σ₀).filter (fun σ => σ i = x)).card =
      ((histories I σ₀).filter (fun σ => σ i = y)).card := by
  apply Finset.card_equiv (postcompose (Equiv.swap x y))
  intro σ
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hσ, hi⟩
    refine ⟨swap_preserves_history I σ₀ σ x y hx hy hσ, ?_⟩
    change Equiv.swap x y (σ i) = y
    simp [hi]
  · rintro ⟨hσ, hi⟩
    have hback := swap_preserves_history I σ₀
      (σ.trans (Equiv.swap x y)) x y hx hy hσ
    have hσ' : σ ∈ histories I σ₀ := by
      simpa using hback
    refine ⟨hσ', ?_⟩
    change Equiv.swap x y (σ i) = y at hi
    apply (Equiv.swap x y).injective
    simpa using hi

theorem expect_next (I : Finset α) (σ₀ : Equiv.Perm α)
    (i : α) (hi : i ∉ I) (g : α → ℝ) :
    (𝔼 σ ∈ histories I σ₀, g (σ i)) = 𝔼 x ∈ unused I σ₀, g x := by
  let m := ((histories I σ₀).filter (fun σ => σ i = σ₀ i)).card
  have hm : 0 < m := by
    apply Finset.card_pos.mpr
    exact ⟨σ₀, by simp⟩
  apply expect_comp_of_fiber_card_eq (histories I σ₀) (unused I σ₀)
    (fun σ => σ i) m hm (fun σ hσ => next_mem_unused I σ₀ i hi σ hσ)
  intro x hx
  exact next_fiber_card_eq I σ₀ i x (σ₀ i) hx
    (next_mem_unused I σ₀ i hi σ₀ (by simp))

theorem histories_card_eq (I : Finset α) (σ₀ τ₀ : Equiv.Perm α) :
    (histories I σ₀).card = (histories I τ₀).card := by
  apply Finset.card_equiv (postcompose (σ₀.symm.trans τ₀))
  intro σ
  simp only [mem_histories]
  constructor
  · intro h j hj
    change τ₀ (σ₀.symm (σ j)) = τ₀ j
    simp [h j hj]
  · intro h j hj
    have heq : τ₀ (σ₀.symm (σ j)) = τ₀ j := h j hj
    exact (Equiv.symm_apply_eq σ₀).mp (τ₀.injective heq)

theorem histories_symm (I : Finset α) (σ τ : Equiv.Perm α) :
    σ ∈ histories I τ ↔ τ ∈ histories I σ := by
  simp only [mem_histories]
  exact ⟨fun h j hj => (h j hj).symm, fun h j hj => (h j hj).symm⟩

theorem expect_histories (I : Finset α) (g : Equiv.Perm α → ℝ) :
    (𝔼 τ : Equiv.Perm α, 𝔼 σ ∈ histories I τ, g σ) =
      𝔼 σ : Equiv.Perm α, g σ := by
  let m := (histories I (Equiv.refl α)).card
  have hm : (m : ℝ) ≠ 0 := by
    exact_mod_cast (histories_nonempty I (Equiv.refl α)).card_pos.ne'
  have hc (τ : Equiv.Perm α) : (histories I τ).card = m :=
    histories_card_eq I τ (Equiv.refl α)
  simp only [Finset.expect_eq_sum_div_card, hc]
  rw [← Finset.sum_div]
  have hs : (∑ τ : Equiv.Perm α, ∑ σ ∈ histories I τ, g σ) =
      (m : ℝ) * ∑ σ : Equiv.Perm α, g σ := by
    calc
      _ = ∑ τ : Equiv.Perm α, ∑ σ : Equiv.Perm α,
          if σ ∈ histories I τ then g σ else 0 := by
        simp only [Finset.sum_ite_mem, Finset.univ_inter]
      _ = ∑ σ : Equiv.Perm α, ∑ τ : Equiv.Perm α,
          if σ ∈ histories I τ then g σ else 0 := Finset.sum_comm
      _ = ∑ σ : Equiv.Perm α, (m : ℝ) * g σ := by
        apply Finset.sum_congr rfl
        intro σ _
        simp_rw [histories_symm I σ]
        simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
          nsmul_eq_mul, hc]
      _ = _ := (Finset.mul_sum _ _ _).symm
  rw [hs]
  field_simp

theorem expect_past_next (I : Finset α) (i : α) (hi : i ∉ I)
    (f : Equiv.Perm α → α → ℝ)
    (hf : ∀ σ τ, σ ∈ histories I τ → f σ = f τ) :
    (𝔼 σ : Equiv.Perm α, f σ (σ i)) =
      𝔼 τ : Equiv.Perm α, 𝔼 x ∈ unused I τ, f τ x := by
  rw [← expect_histories I (fun σ => f σ (σ i))]
  apply Finset.expect_congr rfl
  intro τ _
  calc
    (𝔼 σ ∈ histories I τ, f σ (σ i)) =
        𝔼 σ ∈ histories I τ, f τ (σ i) := by
      apply Finset.expect_congr rfl
      intro σ hσ
      rw [hf σ τ hσ]
    _ = _ := expect_next I τ i hi (f τ)

theorem map_eq_of_history (I : Finset α) (σ τ : Equiv.Perm α)
    (h : σ ∈ histories I τ) : I.map σ.toEmbedding = I.map τ.toEmbedding := by
  ext x
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨j, hj, heq⟩
    refine ⟨j, hj, ?_⟩
    exact ((mem_histories I τ σ).mp h j hj).symm.trans heq
  · rintro ⟨j, hj, heq⟩
    refine ⟨j, hj, ?_⟩
    exact ((mem_histories I τ σ).mp h j hj).trans heq

omit [DecidableEq α] in

theorem uniform_measureReal_eq_expect [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (A : α → Prop) [DecidablePred A] :
    (PMF.uniformOfFintype α).toMeasure.real {ω | A ω} =
      𝔼 ω : α, if A ω then (1 : ℝ) else 0 := by
  classical
  unfold MeasureTheory.Measure.real
  rw [PMF.toMeasure_uniformOfFintype_apply _ (Set.toFinite _).measurableSet]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast,
    Fintype.card_subtype, Finset.expect_eq_sum_div_card,
    Finset.sum_boole, Finset.card_univ, Set.mem_ofPred_eq]

end
end Balanced.PermutationHistoryLaw

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_CoverCountingExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CoverCountingExposure

noncomputable section
open Finset PermutationHistoryLaw
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] in

theorem order_sq_le_card_unused (I : Finset (Line F))
    (hI : I.card ≤ Fintype.card F) (σ : Equiv.Perm (Line F)) :
    (Fintype.card F : ℝ) ^ 2 ≤ ((unused I σ).card : ℝ) := by
  have hcard := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (I.map σ.toEmbedding))
  have hcast := congrArg (fun n : ℕ => (n : ℝ)) hcard
  have hIR : (I.card : ℝ) ≤ Fintype.card F := by exact_mod_cast hI
  simp only [Finset.card_map, Finset.card_univ, Fintype.card_prod,
    Fintype.card_option, Nat.cast_add, Nat.cast_mul, Nat.cast_one] at hcast
  change (Fintype.card F : ℝ) ^ 2 ≤
    ((Finset.univ \ I.map σ.toEmbedding).card : ℝ)
  nlinarith

theorem conditional_mark_le (I : Finset (Line F))
    (hI : I.card ≤ Fintype.card F) (σ : Equiv.Perm (Line F))
    (U : Finset (Point F)) {ε : ℝ} (hε : 0 < ε) :
    (𝔼 l ∈ unused I σ, if Marked U ε l then (1 : ℝ) else 0) ≤
      1 / (4 * ε ^ 2 * (Fintype.card F : ℝ)) := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have hden := order_sq_le_card_unused I hI σ
  have hdenpos : (0 : ℝ) < (unused I σ).card :=
    (sq_pos_of_pos hq).trans_le hden
  have hcount : (((unused I σ).filter (Marked U ε)).card : ℝ) ≤
      (Fintype.card F : ℝ) / (4 * ε ^ 2) := by
    apply le_trans _ (AtypicalLines.affine_card_marked_lines_le U ε hε)
    exact Nat.cast_le.mpr (Finset.card_le_card
      (Finset.filter_subset_filter (Marked U ε) (Finset.subset_univ (unused I σ))))
  rw [Finset.expect_eq_sum_div_card]
  simp only [Finset.sum_boole]
  calc
    (((unused I σ).filter (Marked U ε)).card : ℝ) / ((unused I σ).card : ℝ) ≤
        ((Fintype.card F : ℝ) / (4 * ε ^ 2)) / ((unused I σ).card : ℝ) :=
      div_le_div_of_nonneg_right hcount hdenpos.le
    _ ≤ ((Fintype.card F : ℝ) / (4 * ε ^ 2)) / (Fintype.card F : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hq) hden
    _ = _ := by field_simp

theorem past_event_and_mark_le
    (I : Finset (Line F)) (hI : I.card ≤ Fintype.card F)
    (i : Line F) (hi : i ∉ I)
    (A : Equiv.Perm (Line F) → Prop)
    (U : Equiv.Perm (Line F) → Finset (Point F))
    (hA : ∀ σ τ, σ ∈ histories I τ → (A σ ↔ A τ))
    (hU : ∀ σ τ, σ ∈ histories I τ → U σ = U τ)
    {ε : ℝ} (hε : 0 < ε) :
    (𝔼 σ : Equiv.Perm (Line F),
      if A σ ∧ Marked (U σ) ε (σ i) then (1 : ℝ) else 0) ≤
      (1 / (4 * ε ^ 2 * (Fintype.card F : ℝ))) *
        (𝔼 σ : Equiv.Perm (Line F), if A σ then (1 : ℝ) else 0) := by
  rw [expect_past_next I i hi
    (fun σ l => if A σ ∧ Marked (U σ) ε l then (1 : ℝ) else 0) (by
      intro σ τ hστ
      funext l
      simp only [hA σ τ hστ, hU σ τ hστ])]
  rw [Finset.mul_expect]
  apply Finset.expect_le_expect
  intro σ _
  by_cases h : A σ
  · simp only [h, true_and, ite_true, mul_one]
    exact conditional_mark_le I hI σ (U σ) hε
  · simp only [h, false_and, ite_false, Finset.expect_const_zero, mul_zero, le_refl]

theorem pastUncovered_eq_of_history (D I : Finset (Line F))
    (σ τ : Equiv.Perm (Line F)) (h : σ ∈ histories I τ) :
    pastUncovered D I σ = pastUncovered D I τ := by
  simp only [pastUncovered, map_eq_of_history I σ τ h]

theorem pastUncovered_eq_of_larger_history (D J I : Finset (Line F))
    (hJI : J ⊆ I) (σ τ : Equiv.Perm (Line F)) (h : σ ∈ histories I τ) :
    pastUncovered D J σ = pastUncovered D J τ := by
  apply pastUncovered_eq_of_history D J σ τ
  apply (mem_histories J τ σ).mpr
  intro j hj
  exact (mem_histories I τ σ).mp h j (hJI hj)

theorem earlier_cover_mark_iff (D J I : Finset (Line F))
    (hJI : J ⊆ I) (j : Line F) (hj : j ∈ I)
    (σ τ : Equiv.Perm (Line F)) (h : σ ∈ histories I τ) (ε : ℝ) :
    Marked (pastUncovered D J σ) ε (σ j) ↔
      Marked (pastUncovered D J τ) ε (τ j) := by
  rw [pastUncovered_eq_of_larger_history D J I hJI σ τ h,
    (mem_histories I τ σ).mp h j hj]

theorem earlier_deletion_mark_iff (D J I : Finset (Line F))
    (hJI : J ⊆ I) (l : Line F)
    (σ τ : Equiv.Perm (Line F)) (h : σ ∈ histories I τ) (ε : ℝ) :
    Marked (pastUncovered D J σ) ε l ↔
      Marked (pastUncovered D J τ) ε l := by
  rw [pastUncovered_eq_of_larger_history D J I hJI σ τ h]

theorem past_event_and_actual_mark_le
    (D I : Finset (Line F)) (hI : I.card ≤ Fintype.card F)
    (i : Line F) (hi : i ∉ I)
    (A : Equiv.Perm (Line F) → Prop)
    (hA : ∀ σ τ, σ ∈ histories I τ → (A σ ↔ A τ))
    {ε : ℝ} (hε : 0 < ε) :
    (𝔼 σ : Equiv.Perm (Line F),
      if A σ ∧ Marked (pastUncovered D I σ) ε (σ i) then (1 : ℝ) else 0) ≤
      (1 / (4 * ε ^ 2 * (Fintype.card F : ℝ))) *
        (𝔼 σ : Equiv.Perm (Line F), if A σ then (1 : ℝ) else 0) :=
  past_event_and_mark_le I hI i hi A (pastUncovered D I) hA
    (pastUncovered_eq_of_history D I) hε

end
end Balanced.CoverCountingExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FiniteUniformTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.FiniteUniformTower

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem sum_fiberMean {Ω Y : Type*} [Fintype Ω] [Fintype Y]
    (expose : Ω → Y) (g : Ω → ℝ) :
    (∑ x, fiberMean expose g (expose x)) = ∑ x, g x := by
  classical
  rw [← Fintype.sum_fiberwise expose (fun x => fiberMean expose g (expose x)),
    ← Fintype.sum_fiberwise expose g]
  apply Finset.sum_congr rfl
  intro z _
  have hval (x : {x // expose x = z}) :
      fiberMean expose g (expose x.1) = fiberMean expose g z := by rw [x.2]
  simp only [hval, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  cases isEmpty_or_nonempty {x // expose x = z} with
  | inl h =>
    let := h
    simp [fiberMean]
  | inr h =>
    let := h
    have hc : (Fintype.card {x // expose x = z} : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    unfold fiberMean
    field_simp

theorem average_fiberMean {Ω Y : Type*} [Fintype Ω] [Fintype Y]
    (expose : Ω → Y) (g : Ω → ℝ) :
    average (fun x => fiberMean expose g (expose x)) = average g := by
  unfold average
  rw [sum_fiberMean]

end
end Balanced.FiniteUniformTower

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_DeletionCountingExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.DeletionCountingExposure

noncomputable section
open scoped BigOperators
open CountingExposurePosterior InjectionExposureLaw
attribute [local instance] Classical.propDecidable

variable {G ι α : Type*} [Fintype G] [Fintype ι] [Fintype α]
  [DecidableEq G] [DecidableEq ι] [DecidableEq α]

theorem mem_countingHistory_iff_observation_eq (P : Finset (G × ι))
    (ω τ : Experiment (G := G) (ι := ι) (α := α)) :
    ω ∈ countingHistory P τ.1 τ.2 ↔ observation P ω = observation P τ := by
  constructor
  · intro h
    obtain ⟨hp, ho⟩ := (Finset.mem_filter.mp h).2
    funext j
    have ht : ω.1 j = τ.1 j := by
      simpa [permutationHistory] using
        (show ∀ t ∈ P, ω.1 t = τ.1 t from by simpa [permutationHistory] using hp) j j.property
    have hj : (τ.1 j).2 ∈ exposedIndices (P.map τ.1.toEmbedding) (τ.1 j).1 := by
      simp only [exposedIndices, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Finset.mem_map.mpr ⟨j, j.property, rfl⟩
    have hv := (mem_history _ _ _).mp (ho (τ.1 j).1) (τ.1 j).2 hj
    simp only [observation, ht]
    exact Prod.ext rfl hv
  · intro h
    have ht (j : G × ι) (hj : j ∈ P) : ω.1 j = τ.1 j :=
      congrArg Prod.fst (congrFun h ⟨j, hj⟩)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · simpa [permutationHistory] using ht
    · intro d
      apply (mem_history _ _ _).mpr
      intro j hj
      have hm : (d, j) ∈ P.map τ.1.toEmbedding := by
        simpa [exposedIndices] using hj
      obtain ⟨t, htP, he⟩ := Finset.mem_map.mp hm
      have hv := congrArg Prod.snd (congrFun h ⟨t, htP⟩)
      change ω.2 (ω.1 t).1 (ω.1 t).2 = τ.2 (τ.1 t).1 (τ.1 t).2 at hv
      rw [ht t htP] at hv
      change τ.1 t = (d, j) at he
      simpa [he] using hv

theorem fiberMean_eq_history (P : Finset (G × ι))
    (g : Experiment (G := G) (ι := ι) (α := α) → ℝ)
    (τ : Experiment (G := G) (ι := ι) (α := α)) :
    FiniteUniformTower.fiberMean (observation P) g (observation P τ) =
      𝔼 ω ∈ countingHistory P τ.1 τ.2, g ω := by
  classical
  let : DecidablePred (fun ω : Experiment (G := G) (ι := ι) (α := α) =>
      observation P ω = observation P τ) := fun _ => Classical.propDecidable _
  rw [expect_subtype (countingHistory P τ.1 τ.2) g]
  unfold FiniteUniformTower.fiberMean
  rw [← Fintype.expect_eq_sum_div_card]
  apply Fintype.expect_equiv
    (Equiv.subtypeEquivRight (fun ω =>
      (mem_countingHistory_iff_observation_eq P ω τ).symm))
  intro ω
  rfl

theorem expect_history_tower (P : Finset (G × ι))
    (g : Experiment (G := G) (ι := ι) (α := α) → ℝ) :
    (𝔼 τ : Experiment (G := G) (ι := ι) (α := α),
      𝔼 ω ∈ countingHistory P τ.1 τ.2, g ω) =
      𝔼 ω : Experiment (G := G) (ι := ι) (α := α), g ω := by
  simp_rw [← fiberMean_eq_history]
  simpa only [FiniteUniformTower.average, Fintype.expect_eq_sum_div_card] using
    FiniteUniformTower.average_fiberMean (observation P) g

theorem nextLine_eq_of_history (P : Finset (G × ι))
    (ω τ : Experiment (G := G) (ι := ι) (α := α))
    (h : ω ∈ countingHistory P τ.1 τ.2) (j : G × ι) (hj : j ∈ P) :
    nextLine ω j = nextLine τ j := by
  have he := congrFun ((mem_countingHistory_iff_observation_eq P ω τ).mp h) ⟨j, hj⟩
  exact congrArg (fun x : (G × ι) × α => (x.1.1, x.2)) he

theorem exposedLines_eq_of_history (J P : Finset (G × ι)) (hJP : J ⊆ P)
    (ω τ : Experiment (G := G) (ι := ι) (α := α))
    (h : ω ∈ countingHistory P τ.1 τ.2) : exposedLines J ω = exposedLines J τ := by
  apply Finset.image_congr
  intro j hj
  exact nextLine_eq_of_history P ω τ h j (hJP hj)

section Affine
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {k : ℕ}

theorem pastUncovered_eq_of_history (C : Finset (Line F))
    (J P : Finset (Direction F × Fin k)) (hJP : J ⊆ P)
    (ω τ : Experiment (G := Direction F) (ι := Fin k) (α := F))
    (h : ω ∈ countingHistory P τ.1 τ.2) :
    pastUncovered C J ω = pastUncovered C J τ := by
  rw [pastUncovered, pastUncovered, exposedLines_eq_of_history J P hJP ω τ h]

theorem earlier_deletion_mark_iff (C : Finset (Line F))
    (J P : Finset (Direction F × Fin k)) (hJP : J ⊆ P)
    (j : Direction F × Fin k) (hj : j ∈ P)
    (ω τ : Experiment (G := Direction F) (ι := Fin k) (α := F))
    (h : ω ∈ countingHistory P τ.1 τ.2) (ε : ℝ) :
    CoverCountingExposure.Marked (pastUncovered C J ω) ε (nextLine ω j) ↔
      CoverCountingExposure.Marked (pastUncovered C J τ) ε (nextLine τ j) := by
  rw [pastUncovered_eq_of_history C J P hJP ω τ h,
    nextLine_eq_of_history P ω τ h j hj]

theorem earlier_cover_mark_iff (C : Finset (Line F))
    (J P : Finset (Direction F × Fin k)) (hJP : J ⊆ P) (l : Line F)
    (ω τ : Experiment (G := Direction F) (ι := Fin k) (α := F))
    (h : ω ∈ countingHistory P τ.1 τ.2) (ε : ℝ) :
    CoverCountingExposure.Marked (pastUncovered C J ω) ε l ↔
      CoverCountingExposure.Marked (pastUncovered C J τ) ε l := by
  rw [pastUncovered_eq_of_history C J P hJP ω τ h]

omit [Field F] in

theorem sum_remainingTokens_eq (P : Finset (Direction F × Fin k))
    (π : Equiv.Perm (Direction F × Fin k)) :
    (∑ d, (remainingTokens (P.map π.toEmbedding) d : ℝ)) =
      ((k * (Fintype.card F + 1) - P.card : ℕ) : ℝ) := by
  rw [sum_remainingTokens, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, Finset.card_map]
  simp [Direction, Nat.mul_comm]

theorem marked_iff (U : Finset (Point F)) (ε : ℝ) (l : Line F) :
    CoverCountingExposure.Marked U ε l ↔ l ∈ CountingExposureKernel.markedLines U ε := by
  simp [CoverCountingExposure.Marked, CountingExposureKernel.markedLines]

theorem conditional_event_and_mark_le
    (P : Finset (Direction F × Fin k)) (i : Direction F × Fin k) (hi : i ∉ P)
    (A : Experiment (G := Direction F) (ι := Fin k) (α := F) → Prop)
    (U : Experiment (G := Direction F) (ι := Fin k) (α := F) → Finset (Point F))
    (hA : ∀ ω τ, ω ∈ countingHistory P τ.1 τ.2 → (A ω ↔ A τ))
    (hU : ∀ ω τ, ω ∈ countingHistory P τ.1 τ.2 → U ω = U τ)
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) (hk : 0 < k)
    (hqk : 2 * k ≤ Fintype.card F)
    (hremaining : η * (k : ℝ) * ((Fintype.card F : ℝ) + 1) ≤
      ((k * (Fintype.card F + 1) - P.card : ℕ) : ℝ))
    (τ : Experiment (G := Direction F) (ι := Fin k) (α := F)) :
    (𝔼 ω ∈ countingHistory P τ.1 τ.2,
      if A ω ∧ CoverCountingExposure.Marked (U ω) ε (nextLine ω i)
        then (1 : ℝ) else 0) ≤
      ((2 / η) / (4 * ε ^ 2 * Fintype.card F)) * (if A τ then (1 : ℝ) else 0) := by
  have heq :
      (𝔼 ω ∈ countingHistory P τ.1 τ.2,
        if A ω ∧ CoverCountingExposure.Marked (U ω) ε (nextLine ω i)
          then (1 : ℝ) else 0) =
      (𝔼 ω ∈ countingHistory P τ.1 τ.2,
        if A τ ∧ CoverCountingExposure.Marked (U τ) ε (nextLine ω i)
          then (1 : ℝ) else 0) := by
    apply Finset.expect_congr rfl
    intro ω hω
    simp only [hA ω τ hω, hU ω τ hω]
  rw [heq]
  by_cases h : A τ
  · simp only [h, true_and, ite_true, mul_one]
    simp_rw [marked_iff]
    apply marked_probability_given_history_le P τ.1 τ.2 i hi (U τ) ε η hε hη hk hqk
    rwa [sum_remainingTokens_eq]
  · simp [h]

theorem past_event_and_mark_le
    (P : Finset (Direction F × Fin k)) (i : Direction F × Fin k) (hi : i ∉ P)
    (A : Experiment (G := Direction F) (ι := Fin k) (α := F) → Prop)
    (U : Experiment (G := Direction F) (ι := Fin k) (α := F) → Finset (Point F))
    (hA : ∀ ω τ, ω ∈ countingHistory P τ.1 τ.2 → (A ω ↔ A τ))
    (hU : ∀ ω τ, ω ∈ countingHistory P τ.1 τ.2 → U ω = U τ)
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) (hk : 0 < k)
    (hqk : 2 * k ≤ Fintype.card F)
    (hremaining : η * (k : ℝ) * ((Fintype.card F : ℝ) + 1) ≤
      ((k * (Fintype.card F + 1) - P.card : ℕ) : ℝ)) :
    (𝔼 ω : Experiment (G := Direction F) (ι := Fin k) (α := F),
      if A ω ∧ CoverCountingExposure.Marked (U ω) ε (nextLine ω i)
        then (1 : ℝ) else 0) ≤
      ((2 / η) / (4 * ε ^ 2 * Fintype.card F)) *
        (𝔼 ω : Experiment (G := Direction F) (ι := Fin k) (α := F),
          if A ω then (1 : ℝ) else 0) := by
  rw [← expect_history_tower P]
  rw [Finset.mul_expect]
  apply Finset.expect_le_expect
  intro τ _
  exact conditional_event_and_mark_le P i hi A U hA hU ε η hε hη hk hqk hremaining τ

theorem past_event_and_actual_mark_le
    (C : Finset (Line F)) (P : Finset (Direction F × Fin k))
    (i : Direction F × Fin k) (hi : i ∉ P)
    (A : Experiment (G := Direction F) (ι := Fin k) (α := F) → Prop)
    (hA : ∀ ω τ, ω ∈ countingHistory P τ.1 τ.2 → (A ω ↔ A τ))
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) (hk : 0 < k)
    (hqk : 2 * k ≤ Fintype.card F)
    (hremaining : η * (k : ℝ) * ((Fintype.card F : ℝ) + 1) ≤
      ((k * (Fintype.card F + 1) - P.card : ℕ) : ℝ)) :
    (𝔼 ω : Experiment (G := Direction F) (ι := Fin k) (α := F),
      if A ω ∧ CoverCountingExposure.Marked (pastUncovered C P ω) ε (nextLine ω i)
        then (1 : ℝ) else 0) ≤
      ((2 / η) / (4 * ε ^ 2 * Fintype.card F)) *
        (𝔼 ω : Experiment (G := Direction F) (ι := Fin k) (α := F),
          if A ω then (1 : ℝ) else 0) :=
  past_event_and_mark_le P i hi A (pastUncovered C P) hA
    (pastUncovered_eq_of_history C P P (Finset.Subset.refl P))
    ε η hε hη hk hqk hremaining

theorem independent_outer_past_event_and_actual_mark_le {Ω : Type*} [Fintype Ω]
    (C : Ω → Finset (Line F)) (P : Finset (Direction F × Fin k))
    (i : Direction F × Fin k) (hi : i ∉ P)
    (A : Ω → Experiment (G := Direction F) (ι := Fin k) (α := F) → Prop)
    (hA : ∀ ζ ω τ, ω ∈ countingHistory P τ.1 τ.2 → (A ζ ω ↔ A ζ τ))
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) (hk : 0 < k)
    (hqk : 2 * k ≤ Fintype.card F)
    (hremaining : η * (k : ℝ) * ((Fintype.card F : ℝ) + 1) ≤
      ((k * (Fintype.card F + 1) - P.card : ℕ) : ℝ)) :
    (𝔼 ζ : Ω, 𝔼 ω : Experiment (G := Direction F) (ι := Fin k) (α := F),
      if A ζ ω ∧ CoverCountingExposure.Marked (pastUncovered (C ζ) P ω) ε (nextLine ω i)
        then (1 : ℝ) else 0) ≤
      ((2 / η) / (4 * ε ^ 2 * Fintype.card F)) *
        (𝔼 ζ : Ω, 𝔼 ω : Experiment (G := Direction F) (ι := Fin k) (α := F),
          if A ζ ω then (1 : ℝ) else 0) := by
  rw [Finset.mul_expect]
  apply Finset.expect_le_expect
  intro ζ _
  exact past_event_and_actual_mark_le (C ζ) P i hi (A ζ) (hA ζ)
    ε η hε hη hk hqk hremaining

end Affine
end
end Balanced.DeletionCountingExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_DeletionFieldTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Balanced.FieldTransport

variable {F G : Type*} [Field F] [Field G]

variable [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G]

omit [DecidableEq F] [DecidableEq G] in
@[simp] theorem cardinal_field (e : F ≃+* G) : Fintype.card G = Fintype.card F :=
  (Fintype.card_congr e.toEquiv).symm

end Balanced.FieldTransport

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_UniformDeletionEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.UniformDeletionEnumeration

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {k : ℕ}

theorem deletionOutcome_surjective :
    Function.Surjective (deletionOutcome (F := F) (k := k)) := by
  intro D
  let S (d : Direction F) := D.val.filter (fun l => l.1 = d)
  have hcard (d : Direction F) : Fintype.card (S d) = k := by
    rw [Fintype.card_coe]
    exact D.property d
  let e (d : Direction F) : Fin k ≃ S d := (Fintype.equivFinOfCardEq (hcard d)).symm
  let f (d : Direction F) : Fin k ↪ F :=
    ⟨fun j => (e d j).val.2, by
      intro i j hij
      apply (e d).injective
      apply Subtype.ext
      apply Prod.ext
      · exact ((Finset.mem_filter.mp (e d i).property).2).trans
          ((Finset.mem_filter.mp (e d j).property).2).symm
      · exact hij⟩
  refine ⟨f, Subtype.ext ?_⟩
  ext l
  change l ∈ selectedLines f ↔ l ∈ D.val
  rw [mem_selectedLines]
  constructor
  · rintro ⟨j, hj⟩
    have hmem := (Finset.mem_filter.mp (e l.1 j).property).1
    have heq : (e l.1 j).val = l := by
      apply Prod.ext
      · exact (Finset.mem_filter.mp (e l.1 j).property).2
      · exact hj
    exact heq ▸ hmem
  · intro hl
    let x : S l.1 := ⟨l, Finset.mem_filter.mpr ⟨hl, rfl⟩⟩
    refine ⟨(e l.1).symm x, ?_⟩
    change ((e l.1) ((e l.1).symm x)).val.2 = l.2
    simp [x]

omit [Field F] [DecidableEq F] in

theorem selectedLines_relabel (τ : Direction F → Equiv.Perm F)
    (f : Direction F → Fin k ↪ F) :
    selectedLines (arrayRelabel τ f) = (selectedLines f).map (lineRelabel τ).toEmbedding := by
  unfold selectedLines
  rw [Finset.map_map]
  congr 1

theorem exists_relabel_outcomes (D E : DeletionSet F k) :
    ∃ τ : Direction F → Equiv.Perm F,
      D.val.map (lineRelabel τ).toEmbedding = E.val := by
  obtain ⟨f, rfl⟩ := deletionOutcome_surjective D
  obtain ⟨g, rfl⟩ := deletionOutcome_surjective E
  have hex (d : Direction F) := Equiv.Perm.exists_extending_pair
    (f d) (g d) (f d).injective (g d).injective
  choose τ hτ using hex
  refine ⟨τ, ?_⟩
  change (selectedLines f).map (lineRelabel τ).toEmbedding = selectedLines g
  rw [← selectedLines_relabel]
  congr 1
  funext d
  apply Function.Embedding.ext
  intro j
  exact hτ d j

theorem outcome_fiber_card_eq (D E : DeletionSet F k) :
    ((Finset.univ.filter (fun f : Direction F → Fin k ↪ F => deletionOutcome f = D)).card) =
      ((Finset.univ.filter (fun f : Direction F → Fin k ↪ F => deletionOutcome f = E)).card) := by
  obtain ⟨τ, hτ⟩ := exists_relabel_outcomes D E
  apply Finset.card_equiv (arrayRelabel τ)
  intro f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hf
    apply Subtype.ext
    change selectedLines (arrayRelabel τ f) = E.val
    rw [selectedLines_relabel]
    have hv : selectedLines f = D.val := congrArg Subtype.val hf
    rw [hv, hτ]
  · intro hf
    apply Subtype.ext
    change selectedLines f = D.val
    apply Finset.map_injective (lineRelabel τ).toEmbedding
    rw [hτ, ← selectedLines_relabel]
    exact congrArg Subtype.val hf

theorem expect_deletionOutcome (h : Direction F → Fin k ↪ F)
    (g : DeletionSet F k → ℝ) :
    (𝔼 f : Direction F → Fin k ↪ F, g (deletionOutcome f)) =
      𝔼 D : DeletionSet F k, g D := by
  let m := ((Finset.univ : Finset (Direction F → Fin k ↪ F)).filter
    (fun f => deletionOutcome f = deletionOutcome h)).card
  have hm : 0 < m := Finset.card_pos.mpr ⟨h, by simp⟩
  apply PermutationSubsetLaw.expect_comp_of_fiber_card_eq Finset.univ Finset.univ
    deletionOutcome m hm (fun _ _ => Finset.mem_univ _)
  intro D _
  exact outcome_fiber_card_eq D (deletionOutcome h)

theorem expect_ordering (f : Direction F → Fin k ↪ F)
    (g : ((Direction F × Fin k) ≃ (deletionOutcome f).val) → ℝ) :
    (𝔼 π : Equiv.Perm (Direction F × Fin k), g (π.trans (tokenEquiv f))) =
      𝔼 e : (Direction F × Fin k) ≃ (deletionOutcome f).val, g e := by
  apply Fintype.expect_equiv (orderingEquiv f)
  intro π
  rfl

theorem expect_uniform_deletion_and_order (h : Direction F → Fin k ↪ F)
    (g : (D : DeletionSet F k) → ((Direction F × Fin k) ≃ D.val) → ℝ) :
    (𝔼 f : Direction F → Fin k ↪ F,
      𝔼 π : Equiv.Perm (Direction F × Fin k),
        g (deletionOutcome f) (π.trans (tokenEquiv f))) =
      𝔼 D : DeletionSet F k, 𝔼 e : (Direction F × Fin k) ≃ D.val, g D e := by
  calc
    _ = 𝔼 f : Direction F → Fin k ↪ F,
        𝔼 e : (Direction F × Fin k) ≃ (deletionOutcome f).val,
          g (deletionOutcome f) e := by
      apply Finset.expect_congr rfl
      intro f _
      exact expect_ordering f (g (deletionOutcome f))
    _ = _ := expect_deletionOutcome h
      (fun D => 𝔼 e : (Direction F × Fin k) ≃ D.val, g D e)

theorem expect_uniform_deletion_and_order_of_le (hk : k ≤ Fintype.card F)
    (g : (D : DeletionSet F k) → ((Direction F × Fin k) ≃ D.val) → ℝ) :
    (𝔼 f : Direction F → Fin k ↪ F,
      𝔼 π : Equiv.Perm (Direction F × Fin k),
        g (deletionOutcome f) (π.trans (tokenEquiv f))) =
      𝔼 D : DeletionSet F k, 𝔼 e : (Direction F × Fin k) ≃ D.val, g D e :=
  expect_uniform_deletion_and_order (canonicalOffsets hk) g

theorem expect_originalExperiment (hk : k ≤ Fintype.card F)
    (g : (D : DeletionSet F k) → ((Direction F × Fin k) ≃ D.val) → ℝ) :
    (𝔼 ω : CountingExposurePosterior.Experiment
        (G := Direction F) (ι := Fin k) (α := F),
      g (deletionOutcome ω.2) (ω.1.trans (tokenEquiv ω.2))) =
      𝔼 D : DeletionSet F k, 𝔼 e : (Direction F × Fin k) ≃ D.val, g D e := by
  rw [← Finset.univ_product_univ, Finset.expect_product, Finset.expect_comm]
  exact expect_uniform_deletion_and_order_of_le hk g

theorem expect_originalExperiment_time (hk : k ≤ Fintype.card F)
    (g : (D : DeletionSet F k) → (Fin (k * (Fintype.card F + 1)) ≃ D.val) → ℝ) :
    (𝔼 ω : CountingExposurePosterior.Experiment
        (G := Direction F) (ι := Fin k) (α := F),
      g (deletionOutcome ω.2) (timeToToken.trans (ω.1.trans (tokenEquiv ω.2)))) =
      𝔼 D : DeletionSet F k,
        𝔼 e : Fin (k * (Fintype.card F + 1)) ≃ D.val, g D e := by
  rw [expect_originalExperiment hk (fun D e => g D (timeToToken.trans e))]
  apply Finset.expect_congr rfl
  intro D _
  apply Fintype.expect_equiv (timeOrderingEquiv D)
  intro e
  rfl

end
end Balanced.UniformDeletionEnumeration

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_AffineProfileIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.FiniteProfile

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] in

theorem deletionSet_card {k : ℕ} {D : Finset (Line F)} (hD : IsDeletionSet k D) :
    D.card = k * (Fintype.card F + 1) := by
  have h := Finset.sum_card_fiberwise_eq_card_filter D
    (Finset.univ : Finset (Direction F)) Prod.fst
  have heach (d : Direction F) : (D.filter fun l ↦ l.1 = d).card = k := hD d
  simpa [heach, Fintype.card_option, Nat.mul_comm] using h.symm

end Balanced.FiniteProfile

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_UniformOrderedSubset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.UniformOrderedSubset

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι] [DecidableEq α]

omit [DecidableEq ι] in

theorem restriction_fiber_card_eq (e f g : ι ↪ α) :
    (Finset.univ.filter (fun σ : Equiv.Perm α => e.trans σ.toEmbedding = f)).card =
      (Finset.univ.filter (fun σ : Equiv.Perm α => e.trans σ.toEmbedding = g)).card := by
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_extending_pair f g f.injective g.injective
  apply Finset.card_equiv (PermutationSubsetLaw.postcompose τ)
  intro σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    apply Function.Embedding.ext
    intro i
    change τ (σ (e i)) = g i
    rw [show σ (e i) = f i from congrArg (fun z : ι ↪ α => z i) h]
    exact hτ i
  · intro h
    apply Function.Embedding.ext
    intro i
    apply τ.injective
    exact (congrArg (fun z : ι ↪ α => z i) h).trans (hτ i).symm

omit [DecidableEq ι] in

theorem expect_restriction (e : ι ↪ α) (g : (ι ↪ α) → ℝ) :
    (𝔼 σ : Equiv.Perm α, g (e.trans σ.toEmbedding)) = 𝔼 f : ι ↪ α, g f := by
  let n := (Finset.univ.filter
    (fun σ : Equiv.Perm α => e.trans σ.toEmbedding = e)).card
  have hn : 0 < n := Finset.card_pos.mpr ⟨Equiv.refl α, by simp⟩
  apply PermutationSubsetLaw.expect_comp_of_fiber_card_eq Finset.univ Finset.univ
    (fun σ : Equiv.Perm α => e.trans σ.toEmbedding) n hn (fun _ _ => Finset.mem_univ _)
  intro f _
  exact restriction_fiber_card_eq e f e

theorem expect_embedding_by_image (e : ι ↪ α) (g : (ι → α) → ℝ) :
    (𝔼 f : ι ↪ α, g f) =
      𝔼 C ∈ (Finset.univ : Finset α).powersetCard (Fintype.card ι),
        𝔼 c : ι ≃ C, g (fun i => (c i).val) := by
  let R := Finset.univ.map e
  let n := (Finset.univ.filter (fun f : ι ↪ α => Finset.univ.map f = R)).card
  rw [PermutationSubsetLaw.expect_eq_expect_fiber_of_card_eq
    Finset.univ ((Finset.univ : Finset α).powersetCard (Fintype.card ι))
    (fun f : ι ↪ α => Finset.univ.map f) n
    (fun f _ => Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by simp⟩)
    (by
      intro C hC
      apply InjectionExposureLaw.range_fiber_card_eq C R
      simpa [R] using (Finset.mem_powersetCard.mp hC).2)]
  apply Finset.expect_congr rfl
  intro C _
  rw [CountingExposurePosterior.expect_subtype]
  let t := Finset.univ.filter (fun f : ι ↪ α => Finset.univ.map f = C)
  let E : t ≃ {f : ι ↪ α // Finset.univ.map f = C} :=
    Equiv.subtypeEquivRight (fun f => by simp [t])
  apply Fintype.expect_equiv (E.trans (imageFiberEquiv C))
  intro f
  rfl

theorem expect_permutation_ordered_subset (e : ι ↪ α) (g : (ι → α) → ℝ) :
    (𝔼 σ : Equiv.Perm α, g (fun i => σ (e i))) =
      𝔼 C ∈ (Finset.univ : Finset α).powersetCard (Fintype.card ι),
        𝔼 c : ι ≃ C, g (fun i => (c i).val) := by
  rw [show (𝔼 σ : Equiv.Perm α, g (fun i => σ (e i))) =
    𝔼 f : ι ↪ α, g f from expect_restriction e (fun f => g f)]
  exact expect_embedding_by_image e g

end
end Balanced.UniformOrderedSubset

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_CountingJointLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CountingJointLaw

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open UniformDeletionEnumeration CountingExposurePosterior

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {k m : ℕ}

theorem expect_joint_eq_pairMarkAverage (hk : k ≤ Fintype.card F)
    (e : Fin m ↪ Line F)
    (g : (Fin (k * (Fintype.card F + 1)) → Line F) → (Fin m → Line F) → ℝ) :
    (𝔼 ω : Experiment (G := Direction F) (ι := Fin k) (α := F),
      𝔼 σ : Equiv.Perm (Line F), g (deletionArray ω) (coverArray e σ)) =
      ProfileWitnessPayment.pairMarkAverage k m (fixedPairMean g) := by
  calc
    _ = 𝔼 D : DeletionSet F k,
        𝔼 d : Fin (k * (Fintype.card F + 1)) ≃ D.val,
          𝔼 σ : Equiv.Perm (Line F),
            g (fun i => (d i).val) (coverArray e σ) :=
      expect_originalExperiment_time hk (fun D d =>
        𝔼 σ : Equiv.Perm (Line F), g (fun i => (d i).val) (coverArray e σ))
    _ = 𝔼 D : DeletionSet F k,
        𝔼 d : Fin (k * (Fintype.card F + 1)) ≃ D.val,
          𝔼 C ∈ ProfileWitnessPayment.witnesses F m,
            𝔼 c : Fin m ≃ C, g (fun i => (d i).val) (fun i => (c i).val) := by
      apply Finset.expect_congr rfl
      intro D _
      apply Finset.expect_congr rfl
      intro d _
      change (𝔼 σ : Equiv.Perm (Line F), g (fun i => (d i).val) (fun i => σ (e i))) =
        𝔼 C ∈ (Finset.univ : Finset (Line F)).powersetCard m,
          𝔼 c : Fin m ≃ C, g (fun i => (d i).val) (fun i => (c i).val)
      simpa only [Fintype.card_fin] using
        UniformOrderedSubset.expect_permutation_ordered_subset e (g (fun i => (d i).val))
    _ = 𝔼 D : DeletionSet F k,
        𝔼 C ∈ ProfileWitnessPayment.witnesses F m, fixedPairMean g D C := by
      apply Finset.expect_congr rfl
      intro D _
      exact Finset.expect_comm _ _ _
    _ = _ := by
      unfold ProfileWitnessPayment.pairMarkAverage
      simp only [Finset.expect_eq_sum_div_card, Finset.card_univ]
      rw [← Finset.sum_div]
      ring

theorem expect_product_eq_pairMarkAverage (hk : k ≤ Fintype.card F)
    (e : Fin m ↪ Line F)
    (g : (Fin (k * (Fintype.card F + 1)) → Line F) → (Fin m → Line F) → ℝ) :
    (𝔼 ω : Experiment (G := Direction F) (ι := Fin k) (α := F) ×
        Equiv.Perm (Line F), g (deletionArray ω.1) (coverArray e ω.2)) =
      ProfileWitnessPayment.pairMarkAverage k m (fixedPairMean g) := by
  rw [← Finset.univ_product_univ, Finset.expect_product]
  exact expect_joint_eq_pairMarkAverage hk e g

theorem fixedPairMean_eq_permutation_average
    (g : (Fin (k * (Fintype.card F + 1)) → Line F) → (Fin m → Line F) → ℝ)
    (D : DeletionSet F k) (C : Finset (Line F))
    (d₀ : Fin (k * (Fintype.card F + 1)) ≃ D.val) (c₀ : Fin m ≃ C) :
    fixedPairMean g D C =
      𝔼 p : Equiv.Perm D.val × Equiv.Perm C,
        g (fun i => (p.1 (d₀ i)).val) (fun i => (p.2 (c₀ i)).val) := by
  rw [← Finset.univ_product_univ, Finset.expect_product]
  unfold fixedPairMean
  symm
  calc
    _ = 𝔼 d : Fin (k * (Fintype.card F + 1)) ≃ D.val,
        𝔼 p : Equiv.Perm C,
          g (fun i => (d i).val) (fun i => (p (c₀ i)).val) := by
      apply Fintype.expect_equiv (UniformOrderedSubset.enumerationEquiv d₀)
      intro p
      rfl
    _ = _ := by
      apply Finset.expect_congr rfl
      intro d _
      apply Fintype.expect_equiv (UniformOrderedSubset.enumerationEquiv c₀)
      intro p
      rfl

end
end Balanced.CountingJointLaw

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_DistinctRoleLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal Classical

namespace Balanced.DistinctRole

variable {D F : Type*} [Field F]

variable [Fintype D] [Fintype F]

instance distinctNonempty :
    Nonempty {M : D → Bool → F // ∀ d, M d false ≠ M d true} :=
  ⟨⟨fun _ b => if b then 0 else 1, by simp⟩⟩

end Balanced.DistinctRole

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_ExposureInterleaving
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace Balanced.ExposureInterleaving

theorem grid_le_one {n : ℕ} (i : Fin n) : grid i ≤ 1 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  rw [grid, div_le_iff₀ hn, one_mul]
  exact_mod_cast Nat.succ_le_iff.mpr i.isLt

theorem coverGrid_le_one {m : ℕ} {γ : ℝ} (hγ : 0 < γ) (i : Fin m) :
    coverGrid γ i ≤ 1 :=
  Real.rpow_le_one (grid_pos i).le (grid_le_one i) (inv_nonneg.mpr hγ.le)

theorem remainingD_at_D {n m : ℕ} (γ : ℝ) (i : Fin n) :
    (remainingD γ (Sum.inl i : Step n m)).card = i.val + 1 := by
  classical
  have hs : remainingD γ (Sum.inl i : Step n m) =
      (Finset.range (i.val + 1)).attachFin (fun j hj =>
        (Finset.mem_range.mp hj).trans_le (Nat.succ_le_iff.mpr i.isLt)) := by
    ext j
    simp only [remainingD, Finset.mem_filter, Finset.mem_univ, true_and,
      Before, not_lt, Finset.mem_attachFin, Finset.mem_range]
    change j.val ≤ i.val ↔ j.val < i.val + 1
    omega
  rw [hs, Finset.card_attachFin, Finset.card_range]

theorem parameter_le_one {n m : ℕ} {γ : ℝ} (hγ : 0 < γ) (s : Step n m) :
    parameter γ s ≤ 1 := by
  cases s with
  | inl i => exact grid_le_one i
  | inr j => exact coverGrid_le_one hγ j

theorem previousD_add_remainingD {n m : ℕ} (γ : ℝ) (s : Step n m) :
    (previousD γ s).card + (remainingD γ s).card = n := by
  simpa [previousD, remainingD] using
    (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i => Before γ (Sum.inl i) s))

end Balanced.ExposureInterleaving

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PatternExposureBoundary
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace Balanced.PatternModel

variable (P : PatternModel)

@[simp] theorem count_eq_zero_of_isEmpty [IsEmpty P.Label] (ω : P.Sample) :
    P.count ω = 0 := by
  simp [count]

end Balanced.PatternModel

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_MarkedExposureNumerics
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.MarkedExposureNumerics

open scoped BigOperators ENNReal Classical
open MeasureTheory

theorem two_pow_mul_pow_le (q m N r : ℕ) (A B ξ : ℝ)
    (hq : 1 ≤ q) (hB : 0 ≤ B) (hBq : max 1 B ≤ (q : ℝ))
    (hm : m ≤ q) (hN : (N : ℝ) ≤ A * q)
    (hr : (m : ℝ) + ξ * q ≤ r) :
    (2 : ℝ) ^ N * (B / q) ^ r ≤
      Real.exp (exponentialCost A B ξ * q - ξ * q * Real.log q) / (q : ℝ) ^ m := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  let b : ℝ := max 1 B
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hbq : b / q ≤ 1 := (div_le_one hqR).mpr hBq
  have hbl : 0 ≤ Real.log b := Real.log_nonneg (le_max_left _ _)
  have h2l : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hmr : (m : ℝ) ≤ q := by exact_mod_cast hm
  have hbase : (B / (q : ℝ)) ^ r ≤ (b / q) ^ r := by
    gcongr
    exact le_max_right _ _
  have hexponent :
      (N : ℝ) * Real.log 2 + Real.log (b / q) * ((m : ℝ) + ξ * q) ≤
        exponentialCost A B ξ * q - ξ * q * Real.log q -
          (m : ℝ) * Real.log q := by
    rw [Real.log_div hb.ne' hqR.ne']
    have h1 := mul_le_mul_of_nonneg_right hN h2l
    have h2 := mul_le_mul_of_nonneg_right hmr hbl
    dsimp [exponentialCost, b] at *
    nlinarith
  calc
    (2 : ℝ) ^ N * (B / q) ^ r ≤ (2 : ℝ) ^ N * (b / q) ^ r := by
      exact mul_le_mul_of_nonneg_left hbase (by positivity)
    _ ≤ (2 : ℝ) ^ N * (b / q) ^ ((m : ℝ) + ξ * q) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge (div_pos hb hqR) hbq hr
    _ = Real.exp ((N : ℝ) * Real.log 2 +
        Real.log (b / q) * ((m : ℝ) + ξ * q)) := by
      rw [Real.rpow_def_of_pos (div_pos hb hqR), Real.exp_add,
        Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ Real.exp (exponentialCost A B ξ * q - ξ * q * Real.log q -
        (m : ℝ) * Real.log q) := Real.exp_le_exp.mpr hexponent
    _ = _ := by
      rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log hqR]

theorem exposure_length_le (k q m : ℕ) (hq : 1 ≤ q) (hm : m ≤ q) :
    ((k * (q + 1) + m : ℕ) : ℝ) ≤ (2 * (k : ℝ) + 1) * q := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hmR : (m : ℝ) ≤ q := by exact_mod_cast hm
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hqR (show (0 : ℝ) ≤ k by positivity)]

end Balanced.MarkedExposureNumerics

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_StrictOrderMarkedExposure
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Balanced.MarkedExposure

variable {Ω ι : Type*} [MeasurableSpace Ω]

theorem intersection_le_pow_of_strict_order
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : ι → ι → Prop) [IsStrictTotalOrder ι R]
    (E : ι → Set Ω) (s : Finset ι) (p : ℝ≥0∞)
    (hstep : ∀ j ∈ s, ∀ t : Finset ι, t ⊆ s → (∀ i ∈ t, R i j) →
      μ (E j ∩ (⋂ i ∈ t, E i)) ≤ p * μ (⋂ i ∈ t, E i))
    (t : Finset ι) (ht : t ⊆ s) :
    μ (⋂ i ∈ t, E i) ≤ p ^ t.card := by
  classical
  let : LinearOrder ι := linearOrderOfSTO R
  induction t using Finset.induction_on_max with
  | empty => simp
  | insert j t hj ih =>
    have hjs : j ∈ s := ht (Finset.mem_insert_self j t)
    have hts : t ⊆ s := fun i hi => ht (Finset.mem_insert_of_mem hi)
    have hjt : j ∉ t := fun h => (hj j h).false
    have hbefore : ∀ i ∈ t, R i j := hj
    calc
      μ (⋂ i ∈ insert j t, E i) = μ (E j ∩ (⋂ i ∈ t, E i)) := by
        congr 1
        ext ω
        simp
      _ ≤ p * μ (⋂ i ∈ t, E i) := hstep j hjs t hts hbefore
      _ ≤ p * p ^ t.card := mul_le_mul_right (ih hts) p
      _ = p ^ (insert j t).card := by
        rw [Finset.card_insert_of_notMem hjt, pow_succ']

theorem tail_le_two_pow_mul_of_strict_order
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : ι → ι → Prop) [IsStrictTotalOrder ι R]
    (E : ι → Set Ω) (s : Finset ι) (r : ℕ) (p : ℝ≥0∞)
    (hstep : ∀ j ∈ s, ∀ t : Finset ι, t ⊆ s → (∀ i ∈ t, R i j) →
      μ (E j ∩ (⋂ i ∈ t, E i)) ≤ p * μ (⋂ i ∈ t, E i)) :
    μ (atLeast s E r) ≤ (2 : ℝ≥0∞) ^ s.card * p ^ r := by
  apply tail_le_two_pow_mul μ s E r p
  intro t ht
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp ht
  simpa only [hcard] using
    intersection_le_pow_of_strict_order μ R E s p hstep t hsub

end Balanced.MarkedExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_ScheduledCountingExposure
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ScheduledCountingExposure

universe u

noncomputable section
open scoped Classical BigOperators ENNReal
open ExposureInterleaving CountingExposurePosterior
open UniformDeletionEnumeration

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {k m : ℕ}

theorem mark_eq_arrayMark (c : Fin m ↪ Line F) (γ η ε : ℝ)
    (s : Steps F k m) (ω : Sample F k) :
    Mark c γ η ε s ω = arrayMark
      (fun i => nextLine ω.1 (timeToToken i)) (fun i => ω.2 (c i)) γ η ε s := by
  have hu : uncovered c γ s ω = arrayUncovered
      (fun i => nextLine ω.1 (timeToToken i)) (fun i => ω.2 (c i)) γ s := by
    simp [uncovered, arrayUncovered, DeletionCountingExposure.exposedLines,
      pastD, pastC, Finset.map_eq_image, Finset.image_image, Function.comp_def]
  cases s <;> simp only [Mark, arrayMark, hu, target, Sum.elim_inl, Sum.elim_inr]

theorem markCount_eq_arrayMarkCount (c : Fin m ↪ Line F) (γ η ε : ℝ)
    (ω : Sample F k) :
    markCount c γ η ε ω = arrayMarkCount
      (fun i => nextLine ω.1 (timeToToken i)) (fun i => ω.2 (c i)) γ η ε := by
  simp only [markCount, arrayMarkCount, mark_eq_arrayMark]

omit [Field F] [DecidableEq F] in
theorem pastD_mono {γ : ℝ} (hγ : 0 < γ) {s t : Steps F k m}
    (hst : Before γ s t) : pastD γ s ⊆ pastD γ t := by
  apply Finset.map_subset_map.mpr
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    before_trans hγ (Finset.mem_filter.mp hi).2 hst⟩

omit [Field F] [DecidableEq F] in
theorem pastC_mono (c : Fin m ↪ Line F) {γ : ℝ} (hγ : 0 < γ)
    {s t : Steps F k m} (hst : Before γ s t) : pastC c γ s ⊆ pastC c γ t := by
  apply Finset.map_subset_map.mpr
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    before_trans hγ (Finset.mem_filter.mp hi).2 hst⟩

omit [Field F] [DecidableEq F] in
theorem deletion_position_mem {γ : ℝ} {i : Fin (k * (Fintype.card F + 1))}
    {s : Steps F k m} (h : Before γ (Sum.inl i) s) :
    timeToToken i ∈ pastD γ s :=
  Finset.mem_map.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩

omit [Field F] [DecidableEq F] in
theorem cover_position_mem (c : Fin m ↪ Line F) {γ : ℝ} {i : Fin m}
    {s : Steps F k m} (h : Before γ (Sum.inr i) s) : c i ∈ pastC c γ s :=
  Finset.mem_map.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩

omit [Field F] [DecidableEq F] in
theorem deletion_position_not_mem (γ : ℝ) (i : Fin (k * (Fintype.card F + 1))) :
    timeToToken i ∉ pastD γ (Sum.inl i : Steps F k m) := by
  simpa only [pastD, Finset.mem_map_equiv, Equiv.symm_apply_apply] using currentD_not_previousD (m := m) γ i

omit [Field F] [DecidableEq F] in
theorem cover_position_not_mem (c : Fin m ↪ Line F) (γ : ℝ) (i : Fin m) :
    c i ∉ pastC c γ (Sum.inr i : Steps F k m) := by
  simpa only [pastC, Finset.mem_map, c.injective.eq_iff, exists_eq_right] using currentC_not_previousC
    (n := k * (Fintype.card F + 1)) γ i

theorem uncovered_eq_D (c : Fin m ↪ Line F) (γ : ℝ) (s : Steps F k m)
    (ω : Sample F k) :
    uncovered c γ s ω = DeletionCountingExposure.pastUncovered
      ((pastC c γ s).map ω.2.toEmbedding) (pastD γ s) ω.1 := rfl

theorem uncovered_eq_C (c : Fin m ↪ Line F) (γ : ℝ) (s : Steps F k m)
    (ω : Sample F k) :
    uncovered c γ s ω = CoverCountingExposure.pastUncovered
      (DeletionCountingExposure.exposedLines (pastD γ s) ω.1) (pastC c γ s) ω.2 := rfl

theorem mark_iff_D_history (c : Fin m ↪ Line F) {γ : ℝ} (hγ : 0 < γ)
    (η ε : ℝ) {s t : Steps F k m} (hst : Before γ s t)
    (σ : Equiv.Perm (Line F)) (ω τ : DExperiment F k)
    (h : ω ∈ countingHistory (pastD γ t) τ.1 τ.2) :
    Mark c γ η ε s (ω, σ) ↔ Mark c γ η ε s (τ, σ) := by
  unfold Mark
  apply and_congr_right
  intro _
  rw [uncovered_eq_D, uncovered_eq_D]
  cases s with
  | inl i =>
    exact DeletionCountingExposure.earlier_deletion_mark_iff _ _ _
      (pastD_mono hγ hst) _ (deletion_position_mem hst) ω τ h ε
  | inr i =>
    exact DeletionCountingExposure.earlier_cover_mark_iff _ _ _
      (pastD_mono hγ hst) _ ω τ h ε

theorem mark_iff_C_history (c : Fin m ↪ Line F) {γ : ℝ} (hγ : 0 < γ)
    (η ε : ℝ) {s t : Steps F k m} (hst : Before γ s t)
    (ω : DExperiment F k) (σ τ : Equiv.Perm (Line F))
    (h : σ ∈ PermutationHistoryLaw.histories (pastC c γ t) τ) :
    Mark c γ η ε s (ω, σ) ↔ Mark c γ η ε s (ω, τ) := by
  unfold Mark
  apply and_congr_right
  intro _
  rw [uncovered_eq_C, uncovered_eq_C]
  cases s with
  | inl i =>
    exact CoverCountingExposure.earlier_deletion_mark_iff _ _ _
      (pastC_mono c hγ hst) _ σ τ h ε
  | inr i =>
    exact CoverCountingExposure.earlier_cover_mark_iff _ _ _
      (pastC_mono c hγ hst) _ (cover_position_mem c hst) σ τ h ε

theorem cylinder_iff_D_history (c : Fin m ↪ Line F) {γ : ℝ} (hγ : 0 < γ)
    (η ε : ℝ) (s : Steps F k m) (t : Finset (Steps F k m))
    (ht : ∀ u ∈ t, Before γ u s) (σ : Equiv.Perm (Line F))
    (ω τ : DExperiment F k) (h : ω ∈ countingHistory (pastD γ s) τ.1 τ.2) :
    Cylinder c γ η ε t (ω, σ) ↔ Cylinder c γ η ε t (τ, σ) := by
  constructor
  · intro ha u hu
    exact (mark_iff_D_history c hγ η ε (ht u hu) σ ω τ h).mp (ha u hu)
  · intro ha u hu
    exact (mark_iff_D_history c hγ η ε (ht u hu) σ ω τ h).mpr (ha u hu)

theorem cylinder_iff_C_history (c : Fin m ↪ Line F) {γ : ℝ} (hγ : 0 < γ)
    (η ε : ℝ) (s : Steps F k m) (t : Finset (Steps F k m))
    (ht : ∀ u ∈ t, Before γ u s) (ω : DExperiment F k)
    (σ τ : Equiv.Perm (Line F))
    (h : σ ∈ PermutationHistoryLaw.histories (pastC c γ s) τ) :
    Cylinder c γ η ε t (ω, σ) ↔ Cylinder c γ η ε t (ω, τ) := by
  constructor
  · intro ha u hu
    exact (mark_iff_C_history c hγ η ε (ht u hu) ω σ τ h).mp (ha u hu)
  · intro ha u hu
    exact (mark_iff_C_history c hγ η ε (ht u hu) ω σ τ h).mpr (ha u hu)

omit [Field F] [DecidableEq F] in
theorem activeD_remaining (γ η : ℝ) (i : Fin (k * (Fintype.card F + 1)))
    (hactive : η < parameter γ (Sum.inl i : Steps F k m)) :
    η * (k : ℝ) * ((Fintype.card F : ℝ) + 1) ≤
      ((k * (Fintype.card F + 1) - (pastD γ (Sum.inl i : Steps F k m)).card : ℕ) : ℝ) := by
  have hc := previousD_add_remainingD γ (Sum.inl i : Steps F k m)
  rw [remainingD_at_D] at hc
  have he : k * (Fintype.card F + 1) -
      (pastD γ (Sum.inl i : Steps F k m)).card = i.val + 1 := by
    simp only [pastD, Finset.card_map]
    omega
  rw [he]
  have hn : (0 : ℝ) < (k * (Fintype.card F + 1) : ℕ) := by
    exact_mod_cast Nat.zero_lt_of_lt i.isLt
  change η < (i.val + 1 : ℝ) / (k * (Fintype.card F + 1) : ℕ) at hactive
  have hb := (lt_div_iff₀ hn).mp hactive
  push_cast at hb ⊢
  nlinarith

omit [Field F] [DecidableEq F] in
theorem pastC_card_le (c : Fin m ↪ Line F) (γ : ℝ) (s : Steps F k m) :
    (pastC c γ s).card ≤ m := by
  simp only [pastC, Finset.card_map]
  exact (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin m)

omit [Field F] in
theorem expect_sample (g : Sample F k → ℝ) :
    (𝔼 ω : Sample F k, g ω) =
      𝔼 ω : DExperiment F k, 𝔼 σ : Equiv.Perm (Line F), g (ω, σ) := by
  rw [← Finset.univ_product_univ, Finset.expect_product]

omit [Field F] in
theorem expect_sample_swap (g : Sample F k → ℝ) :
    (𝔼 ω : Sample F k, g ω) =
      𝔼 σ : Equiv.Perm (Line F), 𝔼 ω : DExperiment F k, g (ω, σ) := by
  rw [expect_sample, Finset.expect_comm]

theorem step_expect_le (c : Fin m ↪ Line F) {γ η ε : ℝ}
    (hγ : 0 < γ) (hη : 0 < η) (hη1 : η ≤ 1) (hε : 0 < ε)
    (hk : 0 < k) (hqk : 2 * k ≤ Fintype.card F) (hm : m ≤ Fintype.card F)
    (s : Steps F k m) (t : Finset (Steps F k m))
    (ht : ∀ u ∈ t, Before γ u s) :
    (𝔼 ω : Sample F k, if Mark c γ η ε s ω ∧ Cylinder c γ η ε t ω
      then (1 : ℝ) else 0) ≤
      ((2 / η) / (4 * ε ^ 2 * Fintype.card F)) *
        (𝔼 ω : Sample F k, if Cylinder c γ η ε t ω then (1 : ℝ) else 0) := by
  by_cases hactive : η < parameter γ s
  · cases s with
    | inl i =>
      rw [expect_sample_swap, expect_sample_swap]
      have h := DeletionCountingExposure.independent_outer_past_event_and_actual_mark_le
        (fun σ : Equiv.Perm (Line F) => (pastC c γ (Sum.inl i)).map σ.toEmbedding)
        (pastD γ (Sum.inl i)) (timeToToken i) (deletion_position_not_mem γ i)
        (fun σ ω => Cylinder c γ η ε t (ω, σ))
        (fun σ ω τ h => cylinder_iff_D_history c hγ η ε (Sum.inl i) t ht σ ω τ h)
        ε η hε hη hk hqk (activeD_remaining γ η i hactive)
      simpa only [Mark, hactive, true_and, uncovered_eq_D, target, and_comm] using h
    | inr i =>
      rw [expect_sample, expect_sample, Finset.mul_expect]
      apply Finset.expect_le_expect
      intro ω _
      have h := CoverCountingExposure.past_event_and_actual_mark_le
        (DeletionCountingExposure.exposedLines (pastD γ (Sum.inr i)) ω)
        (pastC c γ (Sum.inr i)) ((pastC_card_le c γ _).trans hm)
        (c i) (cover_position_not_mem c γ i)
        (fun σ => Cylinder c γ η ε t (ω, σ))
        (fun σ τ h => cylinder_iff_C_history c hγ η ε (Sum.inr i) t ht ω σ τ h) hε
      have hf : (1 : ℝ) / (4 * ε ^ 2 * Fintype.card F) ≤
          (2 / η) / (4 * ε ^ 2 * Fintype.card F) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact (le_div_iff₀ hη).mpr (by linarith)
      have hp : 0 ≤ (𝔼 σ : Equiv.Perm (Line F),
          if Cylinder c γ η ε t (ω, σ) then (1 : ℝ) else 0) := by
        apply Finset.expect_nonneg
        intro σ _
        split_ifs <;> norm_num
      have h' := h.trans (mul_le_mul_of_nonneg_right hf hp)
      simpa only [Mark, hactive, true_and, uncovered_eq_C, target, and_comm] using h'
  · have hzero : (𝔼 ω : Sample F k,
        if Mark c γ η ε s ω ∧ Cylinder c γ η ε t ω then (1 : ℝ) else 0) = 0 := by
      simp [Mark, hactive]
    rw [hzero]
    apply mul_nonneg (by positivity)
    apply Finset.expect_nonneg
    intro ω _
    split_ifs <;> norm_num

omit [Field F] [DecidableEq F] in
theorem sampleNonempty (hk : k ≤ Fintype.card F) : Nonempty (Sample F k) :=
  ⟨((Equiv.refl _, canonicalOffsets hk), Equiv.refl _)⟩

section Measure
variable [Nonempty (Sample F k)] [MeasurableSpace (Sample F k)]
  [MeasurableSingletonClass (Sample F k)]

theorem step_measure_le (c : Fin m ↪ Line F) {γ η ε : ℝ}
    (hγ : 0 < γ) (hη : 0 < η) (hη1 : η ≤ 1) (hε : 0 < ε)
    (hk : 0 < k) (hqk : 2 * k ≤ Fintype.card F) (hm : m ≤ Fintype.card F)
    (s : Steps F k m) (t : Finset (Steps F k m))
    (ht : ∀ u ∈ t, Before γ u s) :
    (PMF.uniformOfFintype (Sample F k)).toMeasure
        ({ω | Mark c γ η ε s ω} ∩ (⋂ u ∈ t, {ω | Mark c γ η ε u ω})) ≤
      ENNReal.ofReal ((2 / η) / (4 * ε ^ 2 * Fintype.card F)) *
        (PMF.uniformOfFintype (Sample F k)).toMeasure
          (⋂ u ∈ t, {ω | Mark c γ η ε u ω}) := by
  have hc : (⋂ u ∈ t, {ω | Mark c γ η ε u ω}) =
      {ω | Cylinder c γ η ε t ω} := by
    ext ω
    simp [Cylinder]
  rw [hc]
  apply (ENNReal.toReal_le_toReal
    (MeasureTheory.measure_ne_top _ _)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (MeasureTheory.measure_ne_top _ _))).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have h := step_expect_le c hγ hη hη1 hε hk hqk hm s t ht
  rw [← PermutationHistoryLaw.uniform_measureReal_eq_expect,
    ← PermutationHistoryLaw.uniform_measureReal_eq_expect] at h
  exact h

theorem markCount_tail_measure_le (c : Fin m ↪ Line F) {γ η ε : ℝ}
    (hγ : 0 < γ) (hη : 0 < η) (hη1 : η ≤ 1) (hε : 0 < ε)
    (hk : 0 < k) (hqk : 2 * k ≤ Fintype.card F) (hm : m ≤ Fintype.card F)
    (r : ℕ) :
    (PMF.uniformOfFintype (Sample F k)).toMeasure
        {ω | r ≤ markCount c γ η ε ω} ≤
      (2 : ℝ≥0∞) ^ (k * (Fintype.card F + 1) + m) *
        ENNReal.ofReal ((2 / η) / (4 * ε ^ 2 * Fintype.card F)) ^ r := by
  let : IsStrictTotalOrder (Steps F k m) (Before γ) := beforeStrictTotalOrder hγ
  have h := MarkedExposure.tail_le_two_pow_mul_of_strict_order
    (PMF.uniformOfFintype (Sample F k)).toMeasure (Before γ)
    (fun s : Steps F k m => {ω | Mark c γ η ε s ω}) Finset.univ r
    (ENNReal.ofReal ((2 / η) / (4 * ε ^ 2 * Fintype.card F))) (by
      intro s _ t _ ht
      exact step_measure_le c hγ hη hη1 hε hk hqk hm s t ht)
  simpa only [MarkedExposure.atLeast, markCount, Finset.card_univ,
    Steps, Step, Fintype.card_sum, Fintype.card_fin, Set.mem_ofPred_eq] using h

end Measure

theorem markCount_tail_expect_le (c : Fin m ↪ Line F) {γ η ε : ℝ}
    (hγ : 0 < γ) (hη : 0 < η) (hη1 : η ≤ 1) (hε : 0 < ε)
    (hk : 0 < k) (hqk : 2 * k ≤ Fintype.card F) (hm : m ≤ Fintype.card F)
    (r : ℕ) :
    (𝔼 ω : Sample F k, if r ≤ markCount c γ η ε ω then (1 : ℝ) else 0) ≤
      (2 : ℝ) ^ (k * (Fintype.card F + 1) + m) *
        ((2 / η) / (4 * ε ^ 2 * Fintype.card F)) ^ r := by
  let : Nonempty (Sample F k) := sampleNonempty (by omega)
  let : MeasurableSpace (Sample F k) := ⊤
  have h := markCount_tail_measure_le c hγ hη hη1 hε hk hqk hm r
  have hr := ENNReal.toReal_mono (by finiteness) h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (show 0 ≤ (2 / η) / (4 * ε ^ 2 * Fintype.card F) by positivity)] at hr
  rw [← PermutationHistoryLaw.uniform_measureReal_eq_expect]
  exact hr

theorem rare_mark_expect_le (c : Fin m ↪ Line F) {γ η ε : ℝ}
    (hγ : 0 < γ) (hη : 0 < η) (hη1 : η ≤ 1) (hε : 0 < ε)
    (hk : 0 < k) (hqk : 2 * k ≤ Fintype.card F) (hm : m ≤ Fintype.card F)
    (ξ : ℝ) (hBq : max 1 ((2 / η) / (4 * ε ^ 2)) ≤ (Fintype.card F : ℝ)) :
    (𝔼 ω : Sample F k,
      if (m : ℝ) + ξ * Fintype.card F ≤ (markCount c γ η ε ω : ℝ)
        then (1 : ℝ) else 0) ≤
      Real.exp (MarkedExposureNumerics.exponentialCost (2 * k + 1)
        ((2 / η) / (4 * ε ^ 2)) ξ * Fintype.card F -
          ξ * Fintype.card F * Real.log (Fintype.card F)) / (Fintype.card F : ℝ) ^ m := by
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  have ht := markCount_tail_expect_le c hγ hη hη1 hε hk hqk hm
    ⌈(m : ℝ) + ξ * Fintype.card F⌉₊
  have hn := MarkedExposureNumerics.two_pow_mul_pow_le (Fintype.card F) m
    (k * (Fintype.card F + 1) + m) ⌈(m : ℝ) + ξ * Fintype.card F⌉₊
    (2 * k + 1) ((2 / η) / (4 * ε ^ 2)) ξ hq (by positivity) hBq hm
    (MarkedExposureNumerics.exposure_length_le k (Fintype.card F) m hq hm)
    (Nat.le_ceil _)
  rw [div_div] at hn
  simpa only [Nat.ceil_le] using ht.trans hn

theorem markCount_eq_zero_of_one_le_cutoff (c : Fin m ↪ Line F)
    {γ η : ℝ} (hγ : 0 < γ) (hη : 1 ≤ η) (ε : ℝ) (ω : Sample F k) :
    markCount c γ η ε ω = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro s _ hs
  exact (not_lt_of_ge ((parameter_le_one hγ s).trans hη)) hs.1

theorem rare_mark_expect_le_all_cutoffs (c : Fin m ↪ Line F) {γ η ε ξ : ℝ}
    (hγ : 0 < γ) (hη : 0 < η) (hε : 0 < ε) (hξ : 0 < ξ)
    (hk : 0 < k) (hqk : 2 * k ≤ Fintype.card F) (hm : m ≤ Fintype.card F)
    (hBq : max 1 ((2 / η) / (4 * ε ^ 2)) ≤ (Fintype.card F : ℝ)) :
    (𝔼 ω : Sample F k,
      if (m : ℝ) + ξ * Fintype.card F ≤ (markCount c γ η ε ω : ℝ)
        then (1 : ℝ) else 0) ≤
      Real.exp (MarkedExposureNumerics.exponentialCost (2 * k + 1)
        ((2 / η) / (4 * ε ^ 2)) ξ * Fintype.card F -
          ξ * Fintype.card F * Real.log (Fintype.card F)) / (Fintype.card F : ℝ) ^ m := by
  by_cases hη1 : η ≤ 1
  · exact rare_mark_expect_le c hγ hη hη1 hε hk hqk hm ξ hBq
  · have hη' : 1 ≤ η := (lt_of_not_ge hη1).le
    have hpos : (0 : ℝ) < (m : ℝ) + ξ * Fintype.card F := by positivity
    simp only [markCount_eq_zero_of_one_le_cutoff c hγ hη', Nat.cast_zero,
      not_le_of_gt hpos, ite_false, Finset.expect_const_zero]
    positivity

theorem uniform_rare_mark_bound (k : ℕ) (hk : 0 < k) (γ η ε ξ : ℝ)
    (hγ : 0 < γ) (hη : 0 < η) (hε : 0 < ε) (hξ : 0 < ξ) :
    ∃ L : ℝ, ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
        (m : ℕ) (c : Fin m ↪ Line F), N ≤ Fintype.card F → m ≤ Fintype.card F →
        (𝔼 ω : Sample F k,
          if (m : ℝ) + ξ * Fintype.card F ≤ (markCount c γ η ε ω : ℝ)
            then (1 : ℝ) else 0) ≤
          Real.exp (L * Fintype.card F - ξ * Fintype.card F *
            Real.log (Fintype.card F)) / (Fintype.card F : ℝ) ^ m := by
  let B : ℝ := (2 / η) / (4 * ε ^ 2)
  refine ⟨MarkedExposureNumerics.exponentialCost (2 * k + 1) B ξ,
    max (2 * k) ⌈max 1 B⌉₊, ?_⟩
  intro F _ _ _ m c hN hm
  have hqk : 2 * k ≤ Fintype.card F := (le_max_left _ _).trans hN
  have hceil : ⌈max 1 B⌉₊ ≤ Fintype.card F := (le_max_right _ _).trans hN
  have hBq : max 1 B ≤ (Fintype.card F : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  exact rare_mark_expect_le_all_cutoffs c hγ hη hε hξ hk hqk hm hBq

end
end Balanced.ScheduledCountingExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_ScheduledCountingLaw
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ScheduledCountingExposure

noncomputable section
open scoped BigOperators Classical
open CountingJointLaw ProfileWitnessPayment

universe u

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {k m : ℕ}

theorem tail_expect_eq_pairMarkAverage (c : Fin m ↪ Line F)
    (hk : k ≤ Fintype.card F) (γ η ε a : ℝ) :
    (𝔼 ω : Sample F k, if a ≤ (markCount c γ η ε ω : ℝ) then (1 : ℝ) else 0) =
      pairMarkAverage (F := F) k m (fixedPairTail (F := F) (k := k) (m := m) γ η ε a) := by
  simp_rw [markCount_eq_arrayMarkCount]
  exact expect_product_eq_pairMarkAverage hk c (fun d c =>
    if a ≤ (arrayMarkCount (k := k) d c γ η ε : ℝ) then (1 : ℝ) else 0)

theorem uniform_pair_rare_tail (k : ℕ) (hk : 0 < k) (γ η ε ξ : ℝ)
    (hγ : 0 < γ) (hη : 0 < η) (hε : 0 < ε) (hξ : 0 < ξ) :
    ∃ L : ℝ, ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
        (m : ℕ), N ≤ Fintype.card F → k ≤ Fintype.card F → m ≤ Fintype.card F →
        pairMarkAverage (F := F) k m
          (fixedPairTail (F := F) (k := k) (m := m) γ η ε ((m : ℝ) + ξ * Fintype.card F)) ≤
          Real.exp (L * Fintype.card F - ξ * Fintype.card F *
            Real.log (Fintype.card F)) / (Fintype.card F : ℝ) ^ m := by
  obtain ⟨L, N, htail⟩ := uniform_rare_mark_bound.{u} k hk γ η ε ξ hγ hη hε hξ
  refine ⟨L, N, ?_⟩
  intro F _ _ _ m hN hkq hm
  rw [← tail_expect_eq_pairMarkAverage (coverPositions hm) hkq]
  exact htail F m (coverPositions hm) hN hm

end
end Balanced.ScheduledCountingExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_ScheduledMarksBridge
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ScheduledMarksBridge

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open ExposureInterleaving ConditionalOrderVariance ProfileScheduledMarks
open UncoveredSampling

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem marked_iff_fraction (S T : Finset (Line F)) (l : Line F) (ε : ℝ) :
    CoverCountingExposure.Marked (uncoveredBy (S ∪ T)) ε l ↔
      ε < |targetFraction l S T - planeFraction S T| := by
  have hset : (uncoveredBy (S ∪ T)).filter (fun p => OnLine p l) =
      linePoints l ∩ uncoveredBy (S ∪ T) := by
    ext p
    simp [linePoints, and_comm]
  simp only [CoverCountingExposure.Marked, affineIntersectionCount, hset,
    targetFraction, planeFraction]

omit [Field F] [Fintype F] in

theorem population_prefix (D : Finset (Line F)) (p : Equiv.Perm D)
    (s : Finset (Fin D.card)) :
    populationLines D ((s.map (label D).symm.toEmbedding).map p.toEmbedding) =
      s.image (orderedArray D p) := by
  simp only [populationLines, Finset.map_eq_image, Finset.image_image]
  rfl

theorem rankMark_inl (D C : Finset (Line F)) (η ε : ℝ)
    (p : OrderPair D C) (i : Fin D.card) :
    rankMark (orderedArray D p.1) (orderedArray C p.2) η ε (Sum.inl i) ↔
      ProfileMarkedOrders.firstMark D C (ID D C) (JD D C) (zD D) η ε
        ((label D).symm i) p := by
  simp only [ProfileMarkedOrders.firstMark, ID, JD, prefixD, prefixC, stepD,
    zD, Equiv.apply_symm_apply, population_prefix]
  exact and_congr Iff.rfl (marked_iff_fraction _ _ _ _)

theorem rankMark_inr (D C : Finset (Line F)) (η ε : ℝ)
    (p : OrderPair D C) (i : Fin C.card) :
    rankMark (orderedArray D p.1) (orderedArray C p.2) η ε (Sum.inr i) ↔
      ProfileMarkedOrders.firstMark C D (IC D C) (JC D C) (zC C) η ε
        ((label C).symm i) p.swap := by
  simp only [ProfileMarkedOrders.firstMark, IC, JC, prefixD, prefixC, stepC,
    zC, Equiv.apply_symm_apply, Prod.fst_swap, Prod.snd_swap, population_prefix]
  unfold rankMark
  simp only [parameter, Sum.elim_inr]
  rw [Finset.union_comm]
  exact and_congr Iff.rfl (marked_iff_fraction _ _ _ _)

theorem rankCount_eq_sourceMarkCount (D C : Finset (Line F)) (η ε : ℝ)
    (p : OrderPair D C) :
    rankCount (orderedArray D p.1) (orderedArray C p.2) η ε =
      sourceMarkCount D C η ε p := by
  simp only [rankCount, sourceMarkCount, ProfileMarkedOrders.markCount,
    ProfileMarkedOrders.firstMarkCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fintype.sum_sum_type]
  congr 1
  · apply Fintype.sum_equiv (label D).symm
    intro i
    simp only [rankMark_inl]
  · apply Fintype.sum_equiv (label C).symm
    intro i
    simp only [rankMark_inr]

theorem rankCount_cast {n n' m m' : ℕ} (hn : n = n') (hm : m = m')
    (d : Fin n' → Line F) (c : Fin m' → Line F) (η ε : ℝ) :
    rankCount (fun i => d (Fin.cast hn i)) (fun i => c (Fin.cast hm i)) η ε =
      rankCount d c η ε := by
  subst n'
  subst m'
  rfl

theorem arrayMarkCount_eq_sourceMarkCount {k m : ℕ} (D C : Finset (Line F))
    (hD : k * (Fintype.card F + 1) = D.card) (hC : m = C.card)
    (η ε : ℝ) (p : OrderPair D C) :
    ScheduledCountingExposure.arrayMarkCount
      (fun i => (p.1 (populationOrder D hD i)).val)
      (fun i => (p.2 (populationOrder C hC i)).val)
      (Real.sqrt 2) η ε = sourceMarkCount D C η ε p := by
  change rankCount
    (fun i => orderedArray D p.1 (Fin.cast hD i))
    (fun i => orderedArray C p.2 (Fin.cast hC i)) η ε = _
  rw [rankCount_cast]
  exact rankCount_eq_sourceMarkCount D C η ε p

end
end Balanced.ScheduledMarksBridge

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileCountingEndpoint
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Balanced.ProfileCountingAssembly
open scoped _root_.Balanced

universe u
open ProfileWitnessPayment ScheduledCountingExposure

theorem sourceRareTailBound_of_fixedPairTail
    (heq : ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (k m : ℕ) (D : DeletionSet F k) (C : Finset (Line F)),
      C.card = m → ∀ η ε ξ : ℝ,
        fixedPairTail (k := k) (m := m) (Real.sqrt 2) η ε
          ((m : ℝ) + (ξ / 2) * Fintype.card F) D C =
        ProfileScheduledMargin.tailProbability D.val C η ε ξ)
    (k : ℕ) (hk : 1 ≤ k) : SourceRareTailBound.{u} k := by
  intro η ε ξ hη _hηone hε hξ
  obtain ⟨L, N, hrare⟩ := uniform_pair_rare_tail.{u} k (by omega)
    (Real.sqrt 2) η ε (ξ / 2) (Real.sqrt_pos.2 (by norm_num)) hη hε (half_pos hξ)
  refine ⟨L, N, ?_⟩
  intro F _ _ _ m hN hkq hm
  apply le_trans ?_ (hrare F m hN hkq hm)
  unfold pairMarkAverage
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro D _
  apply Finset.sum_le_sum
  intro C hC
  rw [heq F k m D C ((mem_witnesses m C).mp hC) η ε ξ]

private theorem fixedPairTail_source (F : Type u) [Field F] [Fintype F]
    [DecidableEq F] (k m : ℕ) (D : DeletionSet F k) (C : Finset (Line F))
    (hC : C.card = m) (η ε ξ : ℝ) :
    fixedPairTail (k := k) (m := m) (Real.sqrt 2) η ε
      ((m : ℝ) + (ξ / 2) * Fintype.card F) D C =
      ProfileScheduledMargin.tailProbability D.val C η ε ξ := by
  classical
  have hD : k * (Fintype.card F + 1) = D.val.card :=
    (FiniteProfile.deletionSet_card D.property).symm
  unfold fixedPairTail
  rw [CountingJointLaw.fixedPairMean_eq_permutation_average _ D C
    (ScheduledMarksBridge.populationOrder D.val hD)
    (ScheduledMarksBridge.populationOrder C hC.symm)]
  unfold ProfileScheduledMargin.tailProbability
  apply Finset.expect_congr rfl
  intro p _
  rw [ScheduledMarksBridge.arrayMarkCount_eq_sourceMarkCount D.val C hD hC.symm]
  have ht : (m : ℝ) + (ξ / 2) * Fintype.card F =
      (C.card : ℝ) + ξ * (Fintype.card F : ℝ) / 2 := by rw [hC]; ring
  rw [ht]

theorem sourceRareTailBound (k : ℕ) (hk : 1 ≤ k) : SourceRareTailBound.{u} k :=
  sourceRareTailBound_of_fixedPairTail fixedPairTail_source k hk

end Balanced.ProfileCountingAssembly

namespace Balanced
open scoped _root_.Balanced
universe u

theorem profileCounting_proof : ProfileCountingResult.{u} :=
  ProfileCountingAssembly.profileCounting_of_sourceRareTailBound
    ProfileCountingAssembly.sourceRareTailBound
end Balanced

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Results
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w

open scoped BigOperators

namespace Balanced
open scoped _root_.Balanced

theorem profile_counting : ProfileCountingResult.{u} := profileCounting_proof

theorem robust_deletion_oai : RobustDeletionResult.{u} :=
  robustDeletion_of_profileCounting profile_counting

end Balanced

end OAI
end

theorem solution.{u} : type_of% @OAI.Balanced.robust_deletion_oai.{u} := @OAI.Balanced.robust_deletion_oai.{u}
