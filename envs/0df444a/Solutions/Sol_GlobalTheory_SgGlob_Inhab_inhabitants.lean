-- Prove2me | solution 1 for GlobalTheory.SgGlob.Inhab.inhabitants
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:16:33.760019+00:00
-- url     : https://prove2.me/submissions/1eae69e7-8484-4289-ae10-33c7740c23f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_mem_genConf_zero
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_gq_zero
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_mem_lzSet
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_mass_ne_zero
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_isHermU_splitJ
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_mem_genConf_one
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_gq_one
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_exists_different_pair
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_norm_add_norm_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SgGlob GlobalTheory.SgGlob.Inhab
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.SgGlob.Inhab
theorem _root_.solution (σ : E →+* E) {g : ℕ} (hg : g ≠ 0) :
    (IsHermU σ (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) E) ∧
      ((Submodule.span (𝓞 E) {![0, 1], ![1, 1]}, !![0; 1], !![(g : E); 1 + g]) : Tri E 2 0) ∈
        GenConf σ !![1, 0; 0, -1] 1 (1 + 2 * g) g !![-1 - (g : E)] ∧
      Gq (r := 0) σ 1 (1 + 2 * g) !![-1 - (g : E)] = (g : E) ^ 2) ∧
    ((Submodule.span (𝓞 E) {![0, 1], ![1, 1]}, ![0, 1]) ∈ LzSet σ !![1, 0; 0, -1] (1 : E)) ∧
    ((∀ x, σ (σ x) = x) → IsHermU σ (splitJ E) ∧
      ∃ (Q : Matrix (Fin 8) (Fin (1 + 1)) E) (Z : Matrix (Fin (1 + 1)) (Fin (1 + 1)) E),
        ((splitLat E, splitP E, Q) : Tri E 8 1) ∈ GenConf σ (splitJ E) 1 (1 + 2 * g) g Z ∧
        ((∃ τ : E →+* ℂ, ∀ x, τ (σ x) = starRingEnd ℂ (τ x)) → Gq σ 1 (1 + 2 * g) Z ≠ 0)) ∧
    Mass (r := 0) σ !![1, 0; 0, -1] 1 (1 + 2 * g) g !![-1 - (g : E)] ≠ 0 := by
  refine ⟨⟨⟨?_, by simp [Matrix.det_fin_two]⟩, mem_genConf_zero σ hg, gq_zero σ g⟩, mem_lzSet σ,
    fun hσ => ⟨isHermU_splitJ σ, ?_⟩, mass_ne_zero σ hg⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [cT]
  · obtain ⟨a, b, ha, hab⟩ := exists_different_pair E
    refine ⟨_, _, mem_genConf_one σ hσ hg hab, fun ⟨τ, hτ⟩ => ?_⟩
    rw [gq_one σ hσ]
    exact pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 hg))
      (norm_add_norm_ne_zero σ τ hτ (RingOfIntegers.coe_ne_zero_iff.2 ha) _))
end GlobalTheory.SgGlob.Inhab
