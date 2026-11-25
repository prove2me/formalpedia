-- Prove2me | solution 1 for GlobalTheory.TateDecomp.tate_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:02:37.188619+00:00
-- url     : https://prove2.me/submissions/d5e3eec1-5e1c-45a2-a18d-c51f62bb1cb4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Theorems.Thm_GlobalTheory_TateDecomp_inC_iff
import Theorems.Thm_GlobalTheory_TateDecomp_Xsum_le
import Theorems.Thm_GlobalTheory_TateDecomp_mem_Xj
import Theorems.Thm_GlobalTheory_TateDecomp_mul_Xj
import Theorems.Thm_GlobalTheory_TateDecomp_act_Xj
import Theorems.Thm_GlobalTheory_TateDecomp_Xj_inter
import Theorems.Thm_GlobalTheory_TateDecomp_Ohat_decomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.TateDecomp
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.TateDecomp
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ j : ℕ, 1 ≤ j → (∀ z ∈ Ohat K, ∃ y ∈ intC (Ks K j), ∃ x ∈ Xj K j, z = y + x) ∧ (∀ y ∈ inC (Ks K j), ∀ x ∈ Xj K j, ∀ n : ℕ, (l : PadicComplex l) ^ n * y = x → y = 0) ∧ (∀ x ∈ Xj K j, x ∈ Ohat K) ∧ (∀ y ∈ intC (Ks K j), ∀ x ∈ Xj K j, y * x ∈ Xj K j) ∧ (∀ g ∈ (K0 K).fixingSubgroup, ∀ x ∈ Xj K j, act g x ∈ Xj K j) ∧ (∀ x ∈ Ohat K, ∀ y ∈ intC (Ks K j), y ≠ 0 → y * x ∈ Xj K j → x ∈ Xj K j) := by
  intro l _ act χ ha _ K j hj
  refine ⟨fun z hz => Ohat_decomp K hj hz, ?_, ?_, fun y hy x hx => mul_Xj hy hx,
    fun g hg x hx => act_Xj ha hg hx, ?_⟩
  · rintro y hy x hx n rfl
    have h := Xj_inter K hj hx (mul_mem (pow_mem (natCast_mem _ _) _) (inC_iff.1 hy))
    exact (mul_eq_zero.1 h).resolve_left
      (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero))
  · exact fun x hx => closure_mono (Xsum_le K j) (mem_Xj.1 hx)
  · intro x hx y hy h0 hyx
    obtain ⟨a, ha, b, hb, rfl⟩ := Ohat_decomp K hj hx
    have h1 := sub_mem hyx (mul_Xj hy hb)
    rw [mul_add, add_sub_cancel_right] at h1
    have h2 := Xj_inter K hj h1 (mul_mem (intC_iff.1 hy).1 (intC_iff.1 ha).1)
    rw [(mul_eq_zero.1 h2).resolve_left h0, zero_add]
    exact hb
end GlobalTheory.TateDecomp
