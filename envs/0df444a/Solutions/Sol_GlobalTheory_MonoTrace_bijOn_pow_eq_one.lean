-- Prove2me | solution 1 for GlobalTheory.MonoTrace.bijOn_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:21:21.117745+00:00
-- url     : https://prove2.me/submissions/9114acff-a155-450f-ae0f-efb6c08ecab4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinrankEigenspaceMonomialMatrixLiftStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SumCharpolyRootsEqFinsumEigenspaceFinrankStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_TraceLiftMonomialMatrixEqSumEigenvalues
import Theorems.Thm_GlobalTheory_MonoTrace_ncard_pow_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.MonoTrace
namespace GlobalTheory.MonoTrace
theorem _root_.solution (k : Type) [Field k] [IsAlgClosed k] (θ : k →* ℂ)
    (hθ : ∀ x y : k, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (N : ℕ) (hN : (N : k) ≠ 0) :
    Set.BijOn θ {μ : k | μ ^ N = 1} {μ : ℂ | μ ^ N = 1} := by
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  have hne : ∀ μ : k, μ ^ N = 1 → μ ≠ 0 := by
    rintro μ h rfl
    simp [hN0] at h
  have hmaps : Set.MapsTo θ {μ : k | μ ^ N = 1} {μ : ℂ | μ ^ N = 1} := by
    intro μ h
    simp only [Set.mem_setOf_eq] at h ⊢
    rw [← map_pow, h, map_one]
  have hinj : Set.InjOn θ {μ : k | μ ^ N = 1} :=
    fun x hx y hy h => hθ x y (hne x hx) (hne y hy) h
  obtain ⟨_, h1⟩ := ncard_pow_eq_one k N hN
  obtain ⟨f2, h2⟩ := ncard_pow_eq_one ℂ N (by exact_mod_cast hN0)
  have himg : θ '' {μ : k | μ ^ N = 1} = {μ : ℂ | μ ^ N = 1} := by
    apply Set.eq_of_subset_of_ncard_le hmaps.image_subset _ f2
    rw [hinj.ncard_image, h1, h2]
  exact ⟨hmaps, hinj, himg.ge⟩
end GlobalTheory.MonoTrace
