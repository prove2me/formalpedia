-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermAniso.exists_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:09:39.924961+00:00
-- url     : https://prove2.me/submissions/233052e0-1543-4c1d-8be7-bca6f69ed581

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AnisotropicOfHenselAndSandwich
import Theorems.Thm_GlobalTheory_CompanionTheory_HermAniso_q_add
import Theorems.Thm_GlobalTheory_CompanionTheory_HermAniso_norm_q_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermAniso
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L}
namespace GlobalTheory.CompanionTheory.HermAniso
theorem _root_.solution [IsUltrametricDist L] (hs : IsInv s) (hh : IsHerm s h)
    (hp : ∀ x y : V, ‖h x x‖ ≤ 1 → ‖h y y‖ ≤ 1 → ‖h x y + h y x‖ ≤ 1) :
    ∃ V₀ : AddSubgroup V, ∀ x, x ∈ V₀ ↔ ‖h x x‖ ≤ 1 := by
  refine ⟨{ carrier := {x | ‖h x x‖ ≤ 1}, add_mem' := ?_, zero_mem' := ?_, neg_mem' := ?_ }, fun x => Iff.rfl⟩
  · intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [q_add hh]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (hp a b ha hb))
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  · have := hh.2.1 (0 : L) (0 : V) (0 : V)
    simp only [zero_smul, zero_mul] at this
    simp [this]
  · intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have := norm_q_smul hs hh (-1 : L) a
    simp only [neg_smul, one_smul, norm_neg, norm_one, one_mul] at this
    rwa [this]
end GlobalTheory.CompanionTheory.HermAniso
