-- Prove2me | solution 1 for GlobalTheory.FullFlag.exists_isAdapted_of_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:04:53.903256+00:00
-- url     : https://prove2.me/submissions/fc5bc10a-2863-4a78-99ab-d5331cca658c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsAdaptedOfIsLocalRing
import Theorems.Thm_GlobalTheory_FullFlag_monotone
import Theorems.Thm_GlobalTheory_FullFlag_map_sub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FullFlag.map_sub

set_option autoImplicit false
open Module TensorProduct
open GlobalTheory
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
open GlobalTheory.FullFlag
variable {n : ℕ}
namespace GlobalTheory.FullFlag
theorem _root_.solution (F : FullFlag R M n) (h : ∀ i, Module.Free R (F.Step i)) :
    ∃ b : Basis (Fin n) R M, F.IsAdapted b := by
  choose π σ h₁ h₂ h₃ h₄ using F.exists_splitting
  have e : ∀ i, F.Step i ≃ₗ[R] R := fun i => (Module.Invertible.free_iff_linearEquiv.mp (h i)).some
  let v : Fin n → M := fun i => σ i ((e i).symm 1)
  have hv : ∀ (i) (l : F.Step i), σ i l = e i l • v i := fun i l => by
    simp only [v, ← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
  have hspan : ∀ k, Submodule.span R (v '' {i | i.castSucc < k}) = F.sub k := by
    intro k
    refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      exact F.monotone (Fin.castSucc_lt_iff_succ_le.mp hi) (h₃ i _)
    · induction k using Fin.induction with
      | zero => rw [F.sub_zero]; exact bot_le
      | succ i ih =>
        intro x hx
        rw [← sub_add_cancel x (σ i (π i x))]
        refine add_mem (Submodule.span_mono (Set.image_mono ?_) (ih (h₄ i x hx))) ?_
        · exact fun j hj => lt_trans hj Fin.castSucc_lt_succ
        · rw [hv]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Fin.castSucc_lt_succ, rfl⟩)
  have hli : LinearIndependent R v := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    by_contra hne
    push Not at hne
    classical
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun i => a i ≠ 0) id
      (by obtain ⟨i, hi⟩ := hne; exact ⟨i, by simpa using hi⟩)
    have h0 : e i (π i (∑ j, a j • v j)) = a i := by
      rw [map_sum, map_sum, Finset.sum_eq_single i _ (by simp)]
      · simp [v, h₁]
      · intro j _ hj
        by_cases haj : a j = 0
        · simp [haj]
        have hji : j < i := lt_of_le_of_ne (hmax j (by simpa using haj)) hj
        rw [map_smul, h₂ i (v j) (F.monotone (Fin.succ_le_castSucc_iff.mpr hji) (h₃ j _))]
        simp
    rw [ha] at h0
    simp only [map_zero] at h0
    exact (Finset.mem_filter.mp hi).2 h0.symm
  refine ⟨Basis.mk hli ?_, funext fun k => ?_⟩
  · have := hspan (Fin.last n)
    rw [F.sub_last] at this
    exact this.ge.trans (Submodule.span_mono (Set.image_subset_range _ _))
  · rw [Basis.flag, Basis.coe_mk]
    exact hspan k
end GlobalTheory.FullFlag
