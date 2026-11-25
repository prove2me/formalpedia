-- Prove2me | solution 1 for GlobalTheory.UnitLemma.isLat_of_comap_inl_map_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:13:50.304348+00:00
-- url     : https://prove2.me/submissions/fb330bc6-a0b5-49a7-9da5-2fe731aab2fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComapInlMemStLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NcardFibreStableLatticePairProjection
import Theorems.Thm_GlobalTheory_UnitLemma_inf_ker_snd_eq
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma
open Polynomial
variable {O E A₁ A₂ : Type} [CommRing O] [Field E] [Algebra O E]
  [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂]
  [IsScalarTower O E A₁] [IsScalarTower O E A₂]
namespace GlobalTheory.UnitLemma
theorem _root_.solution {M : Submodule O (A₁ × A₂)}
    (h₁ : IsLat O E (M.comap (LinearMap.inl O A₁ A₂)))
    (h₂ : IsLat O E (M.map (LinearMap.snd O A₁ A₂))) : IsLat O E M := by
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker (LinearMap.snd O A₁ A₂) h₂.1 ?_, ?_⟩
  · rw [inf_ker_snd_eq]; exact h₁.1.map _
  · set S := Submodule.span E (M : Set (A₁ × A₂)) with hS
    have hl : LinearMap.range (LinearMap.inl E A₁ A₂) ≤ S := by
      rw [LinearMap.range_eq_map, ← h₁.2, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      exact Submodule.subset_span (by simpa using hx)
    have hr : S.map (LinearMap.snd E A₁ A₂) = ⊤ := by
      rw [hS, Submodule.map_span, ← h₂.2]
      congr 1
    rw [eq_top_iff]
    rintro ⟨a, b⟩ -
    have hb : b ∈ S.map (LinearMap.snd E A₁ A₂) := by rw [hr]; trivial
    obtain ⟨z, hz, hzb⟩ := hb
    have hab : ((a, b) : A₁ × A₂) = z + LinearMap.inl E A₁ A₂ (a - z.1) := by
      ext <;> simp [← hzb]
    rw [hab]
    exact S.add_mem hz (hl ⟨_, rfl⟩)
end GlobalTheory.UnitLemma
