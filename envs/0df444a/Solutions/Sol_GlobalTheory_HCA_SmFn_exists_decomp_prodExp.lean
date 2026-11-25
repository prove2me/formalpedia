-- Prove2me | solution 1 for GlobalTheory.HCA.SmFn.exists_decomp_prodExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:10:01.810224+00:00
-- url     : https://prove2.me/submissions/737b25de-4fb1-4099-a02e-d86ab8cac82a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsExpLieAlgebraComplexUnits
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DixmierMalliavinFactorisationBasisStepStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousLeftTranslateBoundedDerivFunctional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDixmierMalliavinDecompProdExp
import Theorems.Thm_GlobalTheory_HCA_integral_mul_sum_cons_kernel
import Theorems.Thm_GlobalTheory_HCA_SmFn_continuous_leftTranslate
import Theorems.Thm_GlobalTheory_T_dixmierMalliavin_factorisation_basis_step
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conjCME_apply
import Theorems.Thm_GroundTheory_Automorphic_contDiff_cons_kernel
import Theorems.Thm_GroundTheory_Automorphic_tsupport_cons_kernel
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
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
open GlobalTheory GlobalTheory.HCA
namespace GlobalTheory.HCA
namespace SmFn
theorem _root_.solution : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ ε : ℝ, 0 < ε → ∀ (n : ℕ) (j : Fin n → Fin d) (Λ : List (Fin d) → (G → ℂ) → ℂ), SmFn h b μ S K Λ → ∃ (N : ℕ) (Λ' : Fin N → List (Fin d) → (G → ℂ) → ℂ) (κ : Fin N → (Fin n → ℝ) → ℂ), (∀ m, SmFn h b μ S K (Λ' m) ∧ ContDiff ℝ ∞ (κ m) ∧ tsupport (κ m) ⊆ Metric.closedBall 0 ε) ∧ ∀ f ∈ S, Λ [] f = ∑ m, ∫ t, κ m t * Λ' m [] fun y => f (h.prodExp (fun k => b (j k)) t * y) := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b _ _ μ hμ S hS hL K hK ε hε n
  induction n with
  | zero =>
    intro j Λ hΛ
    refine ⟨1, fun _ => Λ, fun _ _ => 1, fun _ => ⟨hΛ, contDiff_const, ?_⟩, fun f hf => ?_⟩
    · intro t _
      rw [Subsingleton.elim t 0]; exact Metric.mem_closedBall_self hε.le
    · have hv : (volume : Measure (Fin 0 → ℝ)).real Set.univ = 1 := by
        simp [Measure.real, MeasureTheory.volume_pi]
      have hP : ∀ t : Fin 0 → ℝ, h.prodExp (fun k => b (j k)) t = 1 := fun t => by
        simp [IsExpLieAlgebra.prodExp]
      simp [hP, hv]
  | succ n ih =>
    intro j Λ hΛ
    obtain ⟨Λ', u, v, hΛ', hu, hv, hus, hvs, hdec⟩ :=
      GlobalTheory.T.dixmierMalliavin_factorisation_basis_step 𝔸 G 𝔤 h d b μ hμ S hS hL K hK Λ hΛ (j 0) ε hε
    obtain ⟨N₁, Λ₁, κ₁, h₁, hd₁⟩ := ih (Fin.tail j) Λ' hΛ'
    obtain ⟨N₂, Λ₂, κ₂, h₂, hd₂⟩ := ih (Fin.tail j) Λ hΛ
    refine ⟨N₁ + N₂, Fin.append Λ₁ Λ₂,
      Fin.append (fun m t => u (t 0) * κ₁ m (Fin.tail t)) (fun m t => v (t 0) * κ₂ m (Fin.tail t)),
      ?_, ?_⟩
    · intro m
      refine Fin.addCases (fun m => ?_) (fun m => ?_) m
      · simp only [Fin.append_left]
        exact ⟨(h₁ m).1, contDiff_cons_kernel hu (h₁ m).2.1, tsupport_cons_kernel hε.le hus (h₁ m).2.2⟩
      · simp only [Fin.append_right]
        exact ⟨(h₂ m).1, contDiff_cons_kernel hv (h₂ m).2.1, tsupport_cons_kernel hε.le hvs (h₂ m).2.2⟩
    · intro f hf
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [hdec f hf]
      have hc : ∀ (Λ₀ : List (Fin d) → (G → ℂ) → ℂ), SmFn h b μ S K Λ₀ →
          Continuous fun x : G => Λ₀ [] fun y => f (x * y) := fun Λ₀ hΛ₀ =>
        SmFn.continuous_leftTranslate 𝔸 G 𝔤 h d b μ hμ S hS hL K hK Λ₀ hΛ₀ [] f hf
      congr 1
      · exact integral_mul_sum_cons_kernel h (fun k => b (j k)) hε.le hu.continuous hus
          (fun m => (h₁ m).2.1.continuous) (fun m => (h₁ m).2.2)
          (Φ := fun m x => Λ₁ m [] fun y => f (x * y)) (fun m => hc _ (h₁ m).1) _
          (fun s => by
            rw [hd₁ _ (hL f hf _)]
            simp only [mul_assoc]
            rfl)
      · exact integral_mul_sum_cons_kernel h (fun k => b (j k)) hε.le hv.continuous hvs
          (fun m => (h₂ m).2.1.continuous) (fun m => (h₂ m).2.2)
          (Φ := fun m x => Λ₂ m [] fun y => f (x * y)) (fun m => hc _ (h₂ m).1) _
          (fun s => by
            rw [hd₂ _ (hL f hf _)]
            simp only [mul_assoc]
            rfl)
end SmFn
end GlobalTheory.HCA
