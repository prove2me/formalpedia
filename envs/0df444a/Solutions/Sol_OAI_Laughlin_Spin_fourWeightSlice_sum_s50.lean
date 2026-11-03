-- Prove2me | solution 1 for OAI.Laughlin.Spin.fourWeightSlice_sum_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:04:11.166428+00:00
-- url     : https://prove2.me/submissions/ed2652d5-ceca-4454-9d6e-21d0a54285c3

import Mathlib
import Definitions.Def_OAIQ050L012
import Definitions.Def_OAIQ050L014

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_LocalFourIndexEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem localFourIndex_sum {M : Type*} [AddCommMonoid M] (Q D : ℕ) (hDQ : D ≤ Q)
    (f : ℕ → Fin (Q+1) → Fin (Q+1) → M) :
    (∑ p : Fin (D+1), ∑ j : Fin (Q+1), ∑ k : Fin (Q+1),
      if p.val+j.val+k.val=D ∧ j<k then f p.val j k else 0) =
      ∑ b : LocalFourIndex D, f b.val.1.val ⟨b.val.2.1.val,by omega⟩ ⟨b.val.2.2.val,by omega⟩ := by
  classical
  let P := fun b : Fin (D+1) × Fin (Q+1) × Fin (Q+1) =>
    b.1.val+b.2.1.val+b.2.2.val=D ∧ b.2.1<b.2.2
  have he : (∑ b : Fin (D+1) × Fin (Q+1) × Fin (Q+1),
      if P b then f b.1.val b.2.1 b.2.2 else 0) =
      ∑ p : Fin (D+1), ∑ j : Fin (Q+1), ∑ k : Fin (Q+1),
        if p.val+j.val+k.val=D ∧ j<k then f p.val j k else 0 := by
    simp only [Fintype.sum_prod_type,P]
  rw [← he,← Finset.sum_filter,Finset.sum_subtype (p := P) _ (by simp)]
  exact (localFourIndexEquiv Q D hDQ).sum_comp
    (fun b => f b.val.1.val b.val.2.1 b.val.2.2) |>.symm

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_WeightSlice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem fourWeightSlice_sum_s50_oai {M : Type*} [AddCommMonoid M] (Q D : ℕ) (hQ : D+2 ≤ Q)
    (f : ℕ → Fin (Q+1) → Fin (Q+1) → M) :
    (∑ p : Fin (2*Q-2+1), ∑ i : WedgePairIndex Q,
      if p.val+i.val.1.val+i.val.2.val=D then f p.val i.val.1 i.val.2 else 0) =
      ∑ b : LocalFourIndex D, f b.val.1.val ⟨b.val.2.1.val,by omega⟩ ⟨b.val.2.2.val,by omega⟩ := by
  classical
  let F := fun p : ℕ => ∑ j : Fin (Q+1), ∑ k : Fin (Q+1),
    if p+j.val+k.val=D ∧ j < k then f p j k else 0
  have hi (p : ℕ) : (∑ i : WedgePairIndex Q,
      if p+i.val.1.val+i.val.2.val=D then f p i.val.1 i.val.2 else 0) = F p := by
    have hs := Finset.sum_subtype (F := inferInstance) (p := fun i : SpinIndex Q Q => i.1 < i.2)
      (Finset.univ.filter (fun i : SpinIndex Q Q => i.1 < i.2)) (by simp)
      (fun i => if p+i.1.val+i.2.val=D then f p i.1 i.2 else 0)
    rw [← hs,Finset.sum_filter,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro j hj
    apply Finset.sum_congr rfl; intro k hk
    by_cases h₁ : j < k <;> by_cases h₂ : p+j.val+k.val=D <;> simp [h₁,h₂]
  simp_rw [hi]
  rw [Fin.sum_univ_eq_sum_range]
  have hsub : (∑ p ∈ Finset.range (D+1), F p) = ∑ p ∈ Finset.range (2*Q-2+1), F p := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro p hp hn
    have hpD : D < p := by simpa using hn
    apply Finset.sum_eq_zero; intro j hj
    apply Finset.sum_eq_zero; intro k hk
    simp [show p+j.val+k.val≠D by omega]
  rw [← hsub,← Fin.sum_univ_eq_sum_range]
  exact localFourIndex_sum Q D (by omega) f

end Laughlin.Spin

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Laughlin.Spin.fourWeightSlice_sum_s50_oai.{u_1} := @OAI.Laughlin.Spin.fourWeightSlice_sum_s50_oai.{u_1}
