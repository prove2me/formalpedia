-- Prove2me | solution 1 for MechanismDesign.VCG.vcg_dsic
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:05:15.611347+00:00
-- url     : https://prove2.me/submissions/6ad18fe6-b03b-4bdd-adad-21bc8b4022ca

import Mathlib
import Definitions.Def_MechanismDesign_VCG_Model



namespace MechanismDesign.VCG

theorem vcg_dsic_core {ι A : Type*} {Θ : ι → Type*} [Fintype ι] [DecidableEq ι]
    (u : ∀ i, A → Θ i → ℝ) (M : DirectMechanism Θ A) (hM : IsVCG u M) : DSIC u M := by
  obtain ⟨heff, hτ⟩ := hM
  intro θ i x
  obtain ⟨τ, hτi⟩ := hτ i
  set θ' := Function.update θ i x with hθ'
  have hr : restrict θ' i = restrict θ i := by
    funext j
    simp only [restrict, θ', Function.update_of_ne j.2]
  have hs : ∑ j ∈ Finset.univ.erase i, u j (M.q θ') (θ' j)
      = ∑ j ∈ Finset.univ.erase i, u j (M.q θ') (θ j) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [θ', Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hτi θ, hτi θ', hr, hs]
  have h1 := Finset.add_sum_erase Finset.univ (fun j => u j (M.q θ) (θ j)) (Finset.mem_univ i)
  have h2 := Finset.add_sum_erase Finset.univ (fun j => u j (M.q θ') (θ j)) (Finset.mem_univ i)
  have hm := heff θ (M.q θ')
  rw [← h1, ← h2] at hm
  linarith

end MechanismDesign.VCG

open MechanismDesign.VCG


theorem solution {ι A : Type*} {Θ : ι → Type*} [Fintype ι] [DecidableEq ι]
    (u : ∀ i, A → Θ i → ℝ) (M : DirectMechanism Θ A) (hM : IsVCG u M) : DSIC u M := by
  exact vcg_dsic_core u M hM
