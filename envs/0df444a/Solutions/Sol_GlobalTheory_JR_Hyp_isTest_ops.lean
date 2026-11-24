-- Prove2me | solution 1 for GlobalTheory.JR.Hyp.isTest_ops
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:19:53.81123+00:00
-- url     : https://prove2.me/submissions/f7d98371-a427-4c39-92b8-42ff0fa3e4fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WHyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportHyperbolicOperati
import Theorems.Thm_GlobalTheory_JR_Hyp_isTest_comp_homeomorph

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Hyp
namespace GlobalTheory.JR.Hyp
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), (∀ (g : SpecialLinearGroup (Fin 2) A.K) (Φ : A.K × A.K → ℂ), IsTest Φ → IsTest (Hyp.rg A g Φ)) ∧ (∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (fun p : A.K × A.K => Φ (p.1, -p.2))) ∧ (∀ (s : A.Kˣ) (Φ : A.K × A.K → ℂ), IsTest Φ → IsTest (fun p : A.K × A.K => Φ ((s : A.K) * p.1, (s : A.K) * p.2))) ∧ (∀ (h Φ : A.K × A.K → ℂ), IsLocallyConstant h → IsTest Φ → IsTest (fun p => h p * Φ p)) ∧ ∀ (c : ℂ) (Φ Φ' : A.K × A.K → ℂ), IsTest Φ → IsTest Φ' → IsTest (c • Φ + Φ') := by
  intro F E _ _ _ _ _ A
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g Φ hΦ
    set a := (g : Matrix (Fin 2) (Fin 2) A.K) 0 0
    set b := (g : Matrix (Fin 2) (Fin 2) A.K) 0 1
    set c := (g : Matrix (Fin 2) (Fin 2) A.K) 1 0
    set d := (g : Matrix (Fin 2) (Fin 2) A.K) 1 1
    have hdet : a * d - b * c = 1 := by
      have := g.2
      rw [Matrix.det_fin_two] at this
      simpa [a, b, c, d] using this
    let e : A.K × A.K ≃ₜ A.K × A.K :=
      { toFun := fun p => (p.1 * a + p.2 * c, p.1 * b + p.2 * d)
        invFun := fun p => (p.1 * d - p.2 * c, -(p.1 * b) + p.2 * a)
        left_inv := by
          intro p
          ext
          · simp only; linear_combination p.1 * hdet
          · simp only; linear_combination p.2 * hdet
        right_inv := by
          intro p
          ext
          · simp only; linear_combination p.1 * hdet
          · simp only; linear_combination p.2 * hdet
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    exact isTest_comp_homeomorph e hΦ
  · intro Φ hΦ
    let e : A.K × A.K ≃ₜ A.K × A.K :=
      { toFun := fun p => (p.1, -p.2)
        invFun := fun p => (p.1, -p.2)
        left_inv := by intro p; simp
        right_inv := by intro p; simp
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    exact isTest_comp_homeomorph e hΦ
  · intro s Φ hΦ
    let e : A.K × A.K ≃ₜ A.K × A.K :=
      { toFun := fun p => ((s : A.K) * p.1, (s : A.K) * p.2)
        invFun := fun p => (((s⁻¹ : A.Kˣ) : A.K) * p.1, ((s⁻¹ : A.Kˣ) : A.K) * p.2)
        left_inv := by intro p; ext <;> simp [← mul_assoc]
        right_inv := by intro p; ext <;> simp [← mul_assoc]
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    exact isTest_comp_homeomorph e hΦ
  · intro h Φ hh hΦ
    exact ⟨hh.mul hΦ.1, hΦ.2.mul_left⟩
  · intro c Φ Φ' hΦ hΦ'
    refine ⟨?_, ?_⟩
    · exact (hΦ.1.comp (fun z : ℂ => c • z)).add hΦ'.1
    · exact (hΦ.2.smul_left).add hΦ'.2
end GlobalTheory.JR.Hyp
