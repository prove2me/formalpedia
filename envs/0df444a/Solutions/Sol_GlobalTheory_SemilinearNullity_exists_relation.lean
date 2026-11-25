-- Prove2me | solution 1 for GlobalTheory.SemilinearNullity.exists_relation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:51:24.293279+00:00
-- url     : https://prove2.me/submissions/5b105747-33f2-4271-95a5-196442a4240b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowerSemilinearRankNullityModMaxIdeal
import Theorems.Thm_GlobalTheory_SemilinearNullity_mm_zero
import Theorems.Thm_GlobalTheory_SemilinearNullity_mm_int_mul
import Theorems.Thm_GlobalTheory_SemilinearNullity_mm_sub
import Theorems.Thm_GlobalTheory_SemilinearNullity_ge_inv
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
open GlobalTheory GlobalTheory.SemilinearNullity
variable {C : Type} [Field C] {V : VF C}
namespace GlobalTheory.SemilinearNullity
theorem _root_.solution {m : ℕ} {σ : Type} {Y : Fin m → σ → C} (hY : ∀ δ x, V.Ge 0 (Y δ x))
    {T : Finset (Fin m)} (hT : IndepOn V Y T) {δ : Fin m}
    (hn : ¬ IndepOn V Y (insert δ T)) :
    ∃ r : Fin m → C, (∀ ε, V.Ge 0 (r ε)) ∧ r δ = 1 ∧ (∀ ε, ε ∉ T → ε ≠ δ → r ε = 0) ∧
      ∀ s, V.MM (∑ ε, r ε * Y ε s) := by
  unfold IndepOn at hn
  push Not at hn
  obtain ⟨c, hc, hc0, hs, ε₀, hε₀⟩ := hn
  have hcd : ¬ V.MM (c δ) := by
    intro hm
    have key := hT (fun ε => if ε = δ then 0 else c ε) (fun ε => by
        split_ifs
        · exact VF.Ge.zero 0
        · exact hc ε)
      (fun ε hε => by
        split_ifs with h
        · rfl
        · exact hc0 ε (by simp [h, hε]))
      (fun s => by
        have h1 : V.MM (Y δ s * c δ) := mm_int_mul (hY δ s) hm
        convert mm_sub (hs s) h1 using 1
        rw [eq_sub_iff_add_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ δ),
          ← Finset.add_sum_erase _ (fun ε => c ε * Y ε s) (Finset.mem_univ δ)]
        rw [Finset.sum_congr rfl (g := fun ε => c ε * Y ε s)
          (fun ε hε => by rw [if_neg (Finset.ne_of_mem_erase hε)])]
        simp only [if_true]
        ring) ε₀
    by_cases h : ε₀ = δ
    · exact hε₀ (h ▸ hm)
    · exact hε₀ (by simpa [h] using key)
  have h0 : c δ ≠ 0 := by intro h; exact hcd (h ▸ mm_zero)
  refine ⟨fun ε => (c δ)⁻¹ * c ε, fun ε => (ge_inv hcd).mul_int (hc ε), inv_mul_cancel₀ h0,
    fun ε h1 h2 => ?_, fun s => ?_⟩
  · simp only [hc0 ε (by simp [h1, h2]), mul_zero]
  · convert mm_int_mul (ge_inv hcd) (hs s) using 1
    simp only [Finset.mul_sum, mul_assoc]
end GlobalTheory.SemilinearNullity
