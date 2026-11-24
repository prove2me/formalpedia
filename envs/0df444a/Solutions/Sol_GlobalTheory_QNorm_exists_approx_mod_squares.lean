-- Prove2me | solution 1 for GlobalTheory.QNorm.exists_approx_mod_squares
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:24:36.669646+00:00
-- url     : https://prove2.me/submissions/e3138392-0732-4297-948c-bb33a5a9fd0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsForallAbvSubLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsApproxModLocalSquares
import Theorems.Thm_GlobalTheory_LocalQuad_denseRange_finite_real
import Theorems.Thm_GlobalTheory_LocalQuad_isSquare_of_valued_sub_one_lt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
open NumberField IsDedekindDomain
open scoped WithZero
namespace GlobalTheory.QNorm
namespace _root_.GlobalTheory.QNorm
theorem _root_.solution :
    ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (y : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F) (z : (F →+* ℝ) → ℝ), (∀ v, y v ≠ 0) → (∀ σ, z σ ≠ 0) → ∃ x : F, x ≠ 0 ∧ (∀ v ∈ S, IsSquare (algebraMap F (v.adicCompletion F) x * y v)) ∧ ∀ σ : F →+* ℝ, 0 < σ x * z σ := by
  intro F _ _ S y z hy hz
  set U : Set ((∀ v : S, (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) × ((F →+* ℝ) → ℝ)) :=
    (⋂ v : S, {p | ‖p.1 v * y v - 1‖ < min ‖(4 : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)‖ 1}) ∩
      ⋂ σ, {p | 0 < p.2 σ * z σ} with hUdef
  have hU : IsOpen U := by
    refine IsOpen.inter (isOpen_iInter_of_finite fun v => ?_) (isOpen_iInter_of_finite fun σ => ?_)
    · exact isOpen_lt
        ((((continuous_apply v).comp continuous_fst).mul continuous_const).sub continuous_const).norm
        continuous_const
    · exact isOpen_lt continuous_const (((continuous_apply σ).comp continuous_snd).mul continuous_const)
  have hne : U.Nonempty := by
    refine ⟨(fun v => (y v)⁻¹, z), ?_⟩
    simp only [hUdef, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    refine ⟨fun v => ?_, fun σ => mul_self_pos.2 (hz σ)⟩
    rw [inv_mul_cancel₀ (hy v), sub_self, norm_zero, lt_min_iff]
    have h4 := (map_ne_zero (algebraMap F ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F))).2
      (by norm_num : (4 : F) ≠ 0)
    rw [map_ofNat] at h4
    exact ⟨norm_pos_iff.2 h4, one_pos⟩
  obtain ⟨x, hx⟩ := (_root_.GlobalTheory.LocalQuad.denseRange_finite_real F S).exists_mem_open hU hne
  simp only [hUdef, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq] at hx
  obtain ⟨hxS, hxR⟩ := hx
  by_cases hx0 : x = 0
  · subst hx0
    refine ⟨1, one_ne_zero, fun v hv => ?_, fun σ => ?_⟩
    · have h := hxS ⟨v, hv⟩
      simp at h
    · have h := hxR σ
      simp at h
  refine ⟨x, hx0, fun v hv => ?_, hxR⟩
  have h := (hxS ⟨v, hv⟩).trans_le (min_le_left _ _)
  exact _root_.GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt F v _ (Valued.toNormedField.norm_lt_iff.1 h)
end _root_.GlobalTheory.QNorm
end GlobalTheory.QNorm
