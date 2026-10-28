-- Prove2me | solution 1 for OAI.Kadison.SchurWeyl.centered_expansion_pairings
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:32:22.209708+00:00
-- url     : https://prove2.me/submissions/5e694d11-8921-4c7f-8387-f39fdf249f61

import Mathlib
import Definitions.Def_OAIQ039C029

section
-- module Solutions.OAIQ039_CM.Commutator_CycleInvariants
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.SchurWeyl

open Matrix

variable {𝕜 : Type*} [CommRing 𝕜]

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

lemma rawCycleTrace_eq_sum (σ : Equiv.Perm J) (A : J → Matrix I I 𝕜) :
    rawCycleTrace σ A = ∑ a : J → I, ∏ j, A j (a (σ j)) (a j) := by
  classical
  simp only [rawCycleTrace, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    permutationMatrix, tensorMatrices]
  apply Finset.sum_congr rfl
  intro a _
  have he (b : J → I) : a = b ∘ σ.symm ↔ b = a ∘ σ := by
    constructor
    · intro h; ext j; simpa using (congrFun h (σ j)).symm
    · rintro rfl; simp [Function.comp_def]
  simp only [he, ite_mul, one_mul, zero_mul]
  simp

end Kadison.SchurWeyl
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CycleInvariants2
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.SchurWeyl

variable {J : Type*} [Fintype J]

lemma sum_cycleCard (σ : Equiv.Perm J) :
    ∑ q, cycleCard σ q = Fintype.card J := by
  classical
  simp only [cycleCard]
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv (cycleMap σ))

lemma cycleCard_pos (σ : Equiv.Perm J) (q : cycleSet σ) : 0 < cycleCard σ q := by
  let j : J := Quotient.out q
  have hj : cycleMap σ j = q := Quotient.out_eq q
  let : Nonempty {j : J // cycleMap σ j = q} := ⟨⟨j, hj⟩⟩
  exact Fintype.card_pos

lemma two_le_cycleCard (σ : Equiv.Perm J) (j : J) (hj : σ j ≠ j) :
    2 ≤ cycleCard σ (cycleMap σ j) := by
  unfold cycleCard
  apply Fintype.one_lt_card_iff.mpr
  exact ⟨⟨σ j, cycleMap_apply σ j⟩, ⟨j, rfl⟩, fun h => hj (congrArg Subtype.val h)⟩

lemma three_le_cycleCard (σ : Equiv.Perm J) (j : J) (hj : σ (σ j) ≠ j) :
    3 ≤ cycleCard σ (cycleMap σ j) := by
  have h : σ j ≠ j := by intro e; apply hj; rw [e, e]
  unfold cycleCard
  apply Fintype.two_lt_card_iff.mpr
  refine ⟨⟨j, rfl⟩, ⟨σ j, cycleMap_apply σ j⟩,
    ⟨σ (σ j), by simp⟩, ?_, ?_, ?_⟩
  · exact fun e => h (congrArg Subtype.val e).symm
  · exact fun e => hj (congrArg Subtype.val e).symm
  · exact fun e => h (σ.injective (congrArg Subtype.val e)).symm

omit [Fintype J] in
lemma cycleMap_eq_fixed (σ : Equiv.Perm J) {a j : J} (ha : σ a = a)
    (hj : cycleMap σ j = cycleMap σ a) : j = a :=
  ((Quotient.exact hj).symm.eq_of_left ha).symm

lemma minimal_cycle_sum (σ : Equiv.Perm J) (a : J) :
    (∑ q : cycleSet σ, if q = cycleMap σ a then 1 else 2) + 1 =
      2 * cycleCount σ := by
  classical
  calc
    _ = (∑ q : cycleSet σ, if q = cycleMap σ a then 1 else 2) +
        ∑ q : cycleSet σ, if q = cycleMap σ a then 1 else 0 := by simp
    _ = ∑ q : cycleSet σ, ((if q = cycleMap σ a then 1 else 2) +
        if q = cycleMap σ a then 1 else 0) := by rw [Finset.sum_add_distrib]
    _ = ∑ _q : cycleSet σ, 2 := by
      apply Finset.sum_congr rfl
      intro q _
      split_ifs <;> rfl
    _ = _ := by simp [cycleCount, mul_comm]

lemma minimal_cycle_bound (σ : Equiv.Perm J) (a : J)
    (h : ∀ j, σ j = j → j = a) (q : cycleSet σ) :
    (if q = cycleMap σ a then 1 else 2) ≤ cycleCard σ q := by
  classical
  by_cases hq : q = cycleMap σ a
  · rw [ite_eq_left hq]; exact cycleCard_pos σ q
  · rw [ite_eq_right hq]
    have hj : cycleMap σ (Quotient.out q) = q := Quotient.out_eq q
    rw [← hj]
    apply two_le_cycleCard
    intro hfix
    exact hq (hj.symm.trans (congrArg (cycleMap σ) (h _ hfix)))

theorem endpoint_cycle_classification (σ : Equiv.Perm J) (a : J)
    (h : ∀ j, σ j = j → j = a)
    (hc : Fintype.card J + 1 ≤ 2 * cycleCount σ) :
    σ a = a ∧ ∀ j, σ (σ j) = j := by
  classical
  have ha : σ a = a := by
    by_contra hn
    have hall : ∀ j, σ j ≠ j := fun j hj => hn (by simpa [h j hj] using hj)
    have hbound (q : cycleSet σ) : 2 ≤ cycleCard σ q := by
      have hq : cycleMap σ (Quotient.out q) = q := Quotient.out_eq q
      rw [← hq]
      exact two_le_cycleCard σ _ (hall _)
    have hs := Finset.sum_le_sum (fun q (_ : q ∈ Finset.univ) => hbound q)
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, sum_cycleCard] at hs
    change cycleCount σ * 2 ≤ Fintype.card J at hs
    omega
  refine ⟨ha, fun j => ?_⟩
  by_contra hj
  have hne : cycleMap σ j ≠ cycleMap σ a := by
    intro he
    have heq := cycleMap_eq_fixed σ ha he
    subst j
    exact hj (by rw [ha, ha])
  have hstrict : (∑ q : cycleSet σ, if q = cycleMap σ a then 1 else 2) <
      ∑ q : cycleSet σ, cycleCard σ q := by
    apply Finset.sum_lt_sum
    · exact fun q _ => minimal_cycle_bound σ a h q
    · refine ⟨cycleMap σ j, Finset.mem_univ _, ?_⟩
      rw [ite_eq_right hne]
      exact three_le_cycleCard σ j hj
  rw [sum_cycleCard] at hstrict
  have hs := minimal_cycle_sum σ a
  omega

end Kadison.SchurWeyl
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CycleInvariants3
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.SchurWeyl

variable {𝕜 I J : Type*} [CommRing 𝕜] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]

theorem rawCycleTrace_zero_of_fixed_centered (σ : Equiv.Perm J)
    (A : J → Matrix I I 𝕜) (j : J) (hj : σ j = j)
    (htrace : Matrix.trace (A j) = 0) : rawCycleTrace σ A = 0 := by
  classical
  have hne (r : {r : J // r ≠ j}) : σ r.1 ≠ j := by
    intro he
    exact r.2 (σ.injective (he.trans hj.symm))
  let C (b : {r : J // r ≠ j} → I) : 𝕜 :=
    ∏ r : {r : J // r ≠ j}, A r.1 (b ⟨σ r.1, hne r⟩) (b r)
  have hprod (b : {r : J // r ≠ j} → I) (i : I) :
      (∏ r, A r ((Equiv.funSplitAt j I).symm (i, b) (σ r))
        ((Equiv.funSplitAt j I).symm (i, b) r)) = A j i i * C b := by
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ j]
    simp only [hj, Equiv.funSplitAt_symm_apply]
    congr 1
    apply Finset.prod_congr rfl
    intro r _
    simp [hne r, r.2]
  rw [rawCycleTrace_eq_sum]
  calc
    _ = ∑ bi : I × ({r : J // r ≠ j} → I),
        ∏ r, A r ((Equiv.funSplitAt j I).symm bi (σ r))
          ((Equiv.funSplitAt j I).symm bi r) := by
      exact Fintype.sum_equiv (Equiv.funSplitAt j I) _ _
        (fun _ => by simp only [Equiv.symm_apply_apply])
    _ = ∑ b : {r : J // r ≠ j} → I, ∑ i : I, A j i i * C b := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_congr rfl (fun i _ => hprod b i)
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      rw [← Finset.sum_mul]
      change Matrix.trace (A j) * C b = 0
      rw [htrace, zero_mul]

theorem cycleTrace_zero_of_fixed_centered (σ : Equiv.Perm J)
    (A : J → Matrix I I ℂ) (j : J) (hj : σ j = j)
    (htrace : Matrix.trace (A j) = 0) : cycleTrace σ A = 0 := by
  rw [cycleTrace, rawCycleTrace_zero_of_fixed_centered σ A j hj htrace, mul_zero]

theorem centered_expansion_pairings_oai (a : J) (d : Equiv.Perm J → ℂ)
    (hd : ∀ σ, 2 * cycleCount σ < Fintype.card J + 1 → d σ = 0)
    (A : J → Matrix I I ℂ) (hA : ∀ j, j ≠ a → Matrix.trace (A j) = 0) :
    (∑ σ, d σ * cycleTrace σ A) =
      ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm J =>
        σ a = a ∧ (∀ j, σ (σ j) = j) ∧ ∀ j, σ j = j → j = a),
      d σ * cycleTrace σ A := by
  classical
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro σ _ hn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hn
  by_cases he : 2 * cycleCount σ < Fintype.card J + 1
  · rw [hd σ he, zero_mul]
  by_cases hf : ∀ j, σ j = j → j = a
  · obtain ⟨ha, hi⟩ := endpoint_cycle_classification σ a hf (Nat.le_of_not_gt he)
    exact (hn ⟨ha, hi, hf⟩).elim
  · obtain ⟨j, hj, hja⟩ := by simpa only [not_forall, Classical.not_imp] using hf
    rw [cycleTrace_zero_of_fixed_centered σ A j hj (hA j hja), mul_zero]

end Kadison.SchurWeyl
end

end OAI
end

theorem solution.{u_2, u_3} : type_of% @OAI.Kadison.SchurWeyl.centered_expansion_pairings_oai.{u_2, u_3} := @OAI.Kadison.SchurWeyl.centered_expansion_pairings_oai.{u_2, u_3}
