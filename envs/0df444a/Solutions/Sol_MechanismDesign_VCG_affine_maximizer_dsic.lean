-- Prove2me | solution 1 for MechanismDesign.VCG.affine_maximizer_dsic
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:03:39.99936+00:00
-- url     : https://prove2.me/submissions/630b8ccb-483c-454c-a568-934fdc0b1f15

import Mathlib
import Definitions.Def_MechanismDesign_VCG_Model



namespace MechanismDesign.VCG

theorem affine_maximizer_dsic_core {ι A : Type*} {Θ : ι → Type*} [Fintype ι] [DecidableEq ι]
    (u : ∀ i, A → Θ i → ℝ)
    (q : (∀ i, Θ i) → A) (k : ι → ℝ) (hk : ∀ i, 0 < k i) (F : A → ℝ)
    (hmax : ∀ (θ : ∀ j, Θ j) (a : A),
      ∑ i, k i * u i (q θ) (θ i) + F (q θ) ≥ ∑ i, k i * u i a (θ i) + F a) :
    ∃ t : ι → (∀ i, Θ i) → ℝ, DSIC u ⟨q, t⟩ := by
  refine ⟨fun i θ => -((∑ j ∈ Finset.univ.erase i, k j * u j (q θ) (θ j)) + F (q θ)) / k i, ?_⟩
  intro θ i x
  simp only
  set θ' := Function.update θ i x
  have hs : ∑ j ∈ Finset.univ.erase i, k j * u j (q θ') (θ' j)
      = ∑ j ∈ Finset.univ.erase i, k j * u j (q θ') (θ j) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [θ', Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hs]
  have h1 := Finset.add_sum_erase Finset.univ (fun j => k j * u j (q θ) (θ j)) (Finset.mem_univ i)
  have h2 := Finset.add_sum_erase Finset.univ (fun j => k j * u j (q θ') (θ j)) (Finset.mem_univ i)
  have hm := hmax θ (q θ')
  have hki := hk i
  rw [← h1, ← h2] at hm
  rw [ge_iff_le, ← sub_nonneg]
  have : u i (q θ) (θ i) - -(∑ j ∈ Finset.univ.erase i, k j * u j (q θ) (θ j) + F (q θ)) / k i -
      (u i (q θ') (θ i) - -(∑ j ∈ Finset.univ.erase i, k j * u j (q θ') (θ j) + F (q θ')) / k i)
      = ((k i * u i (q θ) (θ i) + ∑ j ∈ Finset.univ.erase i, k j * u j (q θ) (θ j) + F (q θ)) -
        (k i * u i (q θ') (θ i) + ∑ j ∈ Finset.univ.erase i, k j * u j (q θ') (θ j) + F (q θ'))) / k i := by
    field_simp
    ring
  rw [this]
  apply div_nonneg _ hki.le
  linarith

end MechanismDesign.VCG

open MechanismDesign.VCG


theorem solution {ι A : Type*} {Θ : ι → Type*} [Fintype ι] [DecidableEq ι]
    [Finite A] (u : ∀ i, A → Θ i → ℝ)
    (hrich : ∀ (i : ι) (ν : A → ℝ), ∃ x : Θ i, ∀ a, u i a x = ν a)
    (q : (∀ i, Θ i) → A) (k : ι → ℝ) (hk : ∀ i, 0 < k i) (F : A → ℝ)
    (hmax : ∀ (θ : ∀ j, Θ j) (a : A),
      ∑ i, k i * u i (q θ) (θ i) + F (q θ) ≥ ∑ i, k i * u i a (θ i) + F a) :
    ∃ t : ι → (∀ i, Θ i) → ℝ, DSIC u ⟨q, t⟩ := by
  exact affine_maximizer_dsic_core u q k hk F hmax
