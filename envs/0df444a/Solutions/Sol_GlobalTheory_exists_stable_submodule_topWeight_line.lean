-- Prove2me | solution 1 for GlobalTheory.exists_stable_submodule_topWeight_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:35:28.592048+00:00
-- url     : https://prove2.me/submissions/67db56cb-4f55-4e65-8403-d1d4f2677bde

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsStableSubmoduleTopWeightLine
import Theorems.Thm_GlobalTheory_loweringWord_apply_mem
import Theorems.Thm_GlobalTheory_loweringWord_height
import Theorems.Thm_GlobalTheory_loweringWord_zero_or_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
      (ν : Fin n → ℂ) (v : V), GlRel E → IsHW E ν v →
      ∃ S : Submodule ℂ V, (∀ a b, ∀ x ∈ S, E a b x ∈ S) ∧ v ∈ S ∧
        ∀ x ∈ S, (∀ a, E a a x = ν a • x) → ∃ c : ℂ, x = c • v := by
  intro V _ _ n E ν v hE hv
  refine ⟨Submodule.span ℂ {x | ∃ N, LoweringWord E v N x}, ?_,
    Submodule.subset_span ⟨0, LoweringWord.base⟩, ?_⟩
  · intro a b x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨N, hN⟩ := hx
      exact loweringWord_apply_mem hE hv hN a b
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  · intro x hx hw
    set H : Module.End ℂ V := ∑ a : Fin n, ((a.val : ℕ) : ℂ) • E a a with hH
    set h : ℂ := ∑ a : Fin n, ((a.val : ℕ) : ℂ) * ν a with hh
    have hle : Submodule.span ℂ {x | ∃ N, LoweringWord E v N x}
        ≤ Submodule.span ℂ {v} ⊔ ⨆ (μ : ℂ) (_ : μ ≠ h), H.eigenspace μ := by
      rw [Submodule.span_le]
      rintro y ⟨N, hN⟩
      rcases loweringWord_zero_or_pos hN with rfl | hpos
      · exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
      · refine Submodule.mem_sup_right ?_
        have hne : h + (N : ℂ) ≠ h := by
          have : (N : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
          simpa using this
        refine Submodule.mem_iSup_of_mem (h + (N : ℂ)) (Submodule.mem_iSup_of_mem hne ?_)
        rw [Module.End.mem_eigenspace_iff]
        exact loweringWord_height hE hv hN
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (hle hx)
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have hxe : x ∈ H.eigenspace h := by
      rw [Module.End.mem_eigenspace_iff]
      simp [hH, hh, LinearMap.sum_apply, hw, Finset.sum_smul, mul_smul]
    have hve : v ∈ H.eigenspace h := by
      rw [Module.End.mem_eigenspace_iff]
      simp [hH, hh, LinearMap.sum_apply, hv.1, Finset.sum_smul, mul_smul]
    have hze : z ∈ H.eigenspace h := by
      have : z = x - c • v := by rw [← hyz]; abel
      rw [this]
      exact Submodule.sub_mem _ hxe (Submodule.smul_mem _ _ hve)
    have hd := Module.End.eigenspaces_iSupIndep H h
    have hz0 : z = 0 := (Submodule.disjoint_def.1 hd) z hze hz
    exact ⟨c, by rw [← hyz, hz0, add_zero]⟩
end GlobalTheory
