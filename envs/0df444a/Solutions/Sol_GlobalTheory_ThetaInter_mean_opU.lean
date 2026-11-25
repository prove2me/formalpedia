-- Prove2me | solution 1 for GlobalTheory.ThetaInter.mean_opU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:51:30.142812+00:00
-- url     : https://prove2.me/submissions/30a6a951-b1d0-4161-8435-2463fc239b91

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Theorems.Thm_GlobalTheory_ThetaInter_rho_opU
import Theorems.Thm_GlobalTheory_ThetaInter_rho_add_of_fixed
import Theorems.Thm_GlobalTheory_ThetaInter_exists_basis
import Theorems.Thm_GlobalTheory_ThetaInter_continuous_rho
import Theorems.Thm_GlobalTheory_ThetaInter_mean_eq
import Theorems.Thm_GlobalTheory_average_fundamentalDomain_eq_real


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaInter
open Formalism.L2.Th1.H Complex
open scoped BigOperators ComplexConjugate
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {H : Sesq V}
variable {α : V → ℂ}
open MeasureTheory
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace ℝ W] [IsScalarTower ℝ ℂ W]
  [FiniteDimensional ℝ W] {H : Sesq W} {α : W → ℂ}
variable [MeasurableSpace W] [BorelSpace W] (μ : Measure W) [μ.IsAddHaarMeasure]
namespace GlobalTheory.ThetaInter
theorem _root_.solution (hH : IsHerm H) {A : AddSubgroup W} (hA : DiscreteTopology A)
    (hsp : Submodule.span ℝ (A : Set W) = ⊤) (hs : IsSemiChar H A α) {F : W → ℂ} (hc : Continuous F)
    (hF : F ∈ fixedBy H α A) (x : W) : mean μ A (rho H (opU H x F)) = mean μ A (rho H F) := by
  obtain ⟨n, b, hb⟩ := exists_basis hA hsp
  rw [mean_eq μ b hb fun y hy z => by rw [rho_opU hH, rho_opU hH, add_right_comm, rho_add_of_fixed hH hs hF hy],
    mean_eq μ b hb fun y hy z => rho_add_of_fixed hH hs hF hy z]
  simp only [rho_opU hH]
  exact average_fundamentalDomain_eq_real μ b b _ (continuous_rho hH hc)
    (fun y hy z => rho_add_of_fixed hH hs hF (hb.le hy) z) le_rfl x
end GlobalTheory.ThetaInter
