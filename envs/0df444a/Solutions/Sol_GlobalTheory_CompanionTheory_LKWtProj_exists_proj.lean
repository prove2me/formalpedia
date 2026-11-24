-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LKWtProj.exists_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:48:28.36529+00:00
-- url     : https://prove2.me/submissions/64a0a3b6-89ac-4802-a6c7-2b585d5c1b94

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_WtProj
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Finset
open scoped InnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LKWtProj
open CompanionTheory.D.LK
open CompanionTheory.D.DSIC (KRel KUnit KStab)
namespace GlobalTheory.CompanionTheory.LKWtProj
theorem _root_.solution {M : Type} [AddCommGroup M] [Module ℂ M] (F : Module.End ℂ M) (τ : ℂ) (t : M)
    (ht : t ∈ ⨆ μ : ℂ, F.eigenspace μ) :
    ∃ P : Module.End ℂ M, (∀ G, Commute F G → Commute P G) ∧
      (∀ W : Submodule ℂ M, (∀ x ∈ W, F x ∈ W) → ∀ x ∈ W, P x ∈ W) ∧
      (∀ y, F y = τ • y → P y = y) ∧ F (P t) = τ • P t := by
  induction ht using Submodule.iSup_induction' with
  | mem μ x hx =>
    rw [Module.End.mem_eigenspace_iff] at hx
    by_cases h : μ = τ
    · subst h
      exact ⟨1, fun G _ => Commute.one_left G, fun W _ x hx => hx, fun y _ => rfl, hx⟩
    · refine ⟨(τ - μ)⁻¹ • (F - μ • 1), fun G hG => ?_, fun W hW y hy => ?_, fun y hy => ?_, ?_⟩
      · exact (hG.sub_left ((Commute.one_left G).smul_left μ)).smul_left _
      · simpa using W.smul_mem _ (W.sub_mem (hW y hy) (W.smul_mem μ hy))
      · have h' : τ - μ ≠ 0 := sub_ne_zero.2 (Ne.symm h)
        simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, hy, ← sub_smul, smul_smul,
          inv_mul_cancel₀ h', one_smul]
      · simp [hx]
  | zero => exact ⟨1, fun G _ => Commute.one_left G, fun W _ x hx => hx, fun y _ => rfl, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨P, hP1, hP2, hP3, hP4⟩ := ihx
    obtain ⟨Q, hQ1, hQ2, hQ3, hQ4⟩ := ihy
    have hPQ : Commute P Q := hP1 Q (hQ1 F (Commute.refl F)).symm
    refine ⟨P * Q, fun G hG => (hP1 G hG).mul_left (hQ1 G hG), fun W hW z hz => hP2 W hW _ (hQ2 W hW z hz),
      fun z hz => ?_, ?_⟩
    · rw [Module.End.mul_apply, hQ3 z hz, hP3 z hz]
    · have h1 : (P * Q) x = P x := by rw [hPQ.eq, Module.End.mul_apply, hQ3 _ hP4]
      have h2 : (P * Q) y = Q y := by rw [Module.End.mul_apply, hP3 _ hQ4]
      rw [map_add, h1, h2, map_add, hP4, hQ4, smul_add]
end GlobalTheory.CompanionTheory.LKWtProj
