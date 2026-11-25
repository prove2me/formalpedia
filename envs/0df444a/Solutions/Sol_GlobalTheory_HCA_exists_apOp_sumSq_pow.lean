-- Prove2me | solution 1 for GlobalTheory.HCA.exists_apOp_sumSq_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:52:46.727339+00:00
-- url     : https://prove2.me/submissions/ec26c145-e7fe-41d8-a7f5-323b3b387c7e

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoefVFContDiffOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSumSquaresRightDerivPowDifferentialOperato
import Theorems.Thm_GlobalTheory_HCA_apOp_sum_coef
import Theorems.Thm_GlobalTheory_HCA_symb_sum_coef
import Theorems.Thm_GlobalTheory_HCA_apOp_zero_one
import Theorems.Thm_GlobalTheory_VFComp_vectorField_comp
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_contDiff_comp_coordEquiv
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conjCME_apply
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.AdL_apply
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.Ad_one
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_Ad
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_bracket
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightDerivEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightTranslateEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] GroundTheory.Automorphic.conjCME_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a



set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
open GlobalTheory GlobalTheory.HCA
namespace GlobalTheory.HCA
theorem _root_.solution : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (r : ℝ) (c : 𝔤 → Fin d → E d → ℝ), ((∀ X j, ContDiffOn ℝ ∞ (c X j) (Metric.ball 0 r)) ∧ (∀ x ∈ Metric.ball (0 : E d) r, ∀ ξ : E d, ξ ≠ 0 → ∃ i, ∑ j, c (b i) j x * ξ j ≠ 0) ∧ ∀ f : G → ℂ, h.IsSmoothFun f → ∀ X : 𝔤, ∀ x ∈ Metric.ball (0 : E d) r, h.rightDeriv X f (h.expG (coordEquiv b (x))) = ∑ j, (c X j x : ℂ) * fderiv ℝ (fun y => f (h.expG (coordEquiv b (y)))) x (ev j)) → ∀ k : ℕ, ∃ a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ, (∀ n w, ContDiffOn ℝ ∞ (a n w) (Metric.ball 0 r)) ∧ (∀ x ξ : E d, symb (2 * k) a x ξ = (((∑ i, (∑ j, c (b i) j x * ξ j) ^ 2) ^ k : ℝ) : ℂ)) ∧ ∀ f : h.smoothFuns (F := ℂ), ∀ x ∈ Metric.ball (0 : E d) r, (((∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) ^ k) f : G → ℂ) (h.expG (coordEquiv b (x))) = apOp (2 * k) a (fun y => (f : G → ℂ) (h.expG (coordEquiv b (y)))) x := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b r c ⟨hc, _, hder⟩ k
  set U : Set (E d) := Metric.ball 0 r with hUdef
  have hU : IsOpen U := Metric.isOpen_ball
  have hchart : ∀ f : G → ℂ, h.IsSmoothFun f →
      ContDiff ℝ ∞ (fun y : E d => f (h.expG (coordEquiv b y))) := by
    intro f hf
    simpa using h.contDiff_comp_coordEquiv hf 1 b
  have step : ∀ (X : 𝔤) (f : G → ℂ), h.IsSmoothFun f → ∀ v : E d → ℂ,
      (∀ y ∈ U, f (h.expG (coordEquiv b y)) = v y) → ∀ x ∈ U,
      h.rightDeriv X f (h.expG (coordEquiv b x)) = ∑ j, (c X j x : ℂ) * fderiv ℝ v x (ev j) := by
    intro X f hf v hv x hx
    rw [hder f hf X x hx]
    have e : (fun y : E d => f (h.expG (coordEquiv b y))) =ᶠ[nhds x] v :=
      Filter.eventually_of_mem (hU.mem_nhds hx) hv
    rw [e.fderiv_eq]
  have hcC : ∀ i j, ContDiffOn ℝ ∞ (fun y => ((c (b i) j y : ℝ) : ℂ)) U := fun i j =>
    Complex.ofRealCLM.contDiff.comp_contDiffOn (hc (b i) j)
  induction k with
  | zero =>
    refine ⟨fun _ _ _ => 1, fun _ _ => contDiffOn_const, ?_, ?_⟩
    · intro x ξ; simp [symb]
    · intro f x _
      simp [apOp_zero_one]
  | succ k ih =>
    obtain ⟨a, ha, hsa, hap⟩ := ih
    choose a1 ha1 hs1 hap1 using fun i : Fin d =>
      GlobalTheory.VFComp.vectorField_comp d (2 * k) U hU a (fun j y => ((c (b i) j y : ℝ) : ℂ)) ha (hcC i)
    choose a2 ha2 hs2 hap2 using fun i : Fin d =>
      GlobalTheory.VFComp.vectorField_comp d (2 * k + 1) U hU (a1 i) (fun j y => ((c (b i) j y : ℝ) : ℂ)) (ha1 i) (hcC i)
    have e2 : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    refine ⟨fun n w y => ∑ i, a2 i n w y, fun n w => ContDiffOn.sum fun i _ => ha2 i n w, ?_, ?_⟩
    · intro x ξ
      rw [symb_sum_coef, e2]
      simp only [hs2, hs1, hsa]
      push_cast
      rw [pow_succ', Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    · intro f x hx
      rw [apOp_sum_coef, e2, pow_succ', Module.End.mul_apply]
      set g := ((∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) ^ k) f with hg
      simp only [LinearMap.sum_apply, Finset.sum_apply, Submodule.coe_sum, Module.End.mul_apply,
        IsExpLieAlgebra.coe_rightDerivEnd]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hf0 := hchart _ f.2
      have h1 : ∀ y ∈ U, h.rightDeriv (b i) (g : G → ℂ) (h.expG (coordEquiv b y)) =
          apOp (2 * k + 1) (a1 i) (fun y => (f : G → ℂ) (h.expG (coordEquiv b y))) y := by
        intro y hy
        rw [step (b i) _ g.2 _ (fun z hz => hap f z hz) y hy]
        exact hap1 i _ hf0.contDiffOn y hy
      rw [step (b i) _ (h.isSmoothFun_rightDeriv g.2 (b i)) _ h1 x hx]
      exact hap2 i _ hf0.contDiffOn x hx
end GlobalTheory.HCA
