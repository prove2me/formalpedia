-- Prove2me | solution 1 for GlobalTheory.HeisLine.heis_invariant_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:46:29.173354+00:00
-- url     : https://prove2.me/submissions/e9d45d9c-f02f-4338-abe0-5d943696785d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_AddCharDotProductTrivialOnTsupportNhds
import Theorems.Thm_GlobalTheory_HeisLine_nonarch
import Theorems.Thm_GlobalTheory_HeisLine_ell_translate
import Theorems.Thm_GlobalTheory_HeisLine_form_eq_ell
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_fourier_mem_SB
import Theorems.Thm_GlobalTheory_SplitWeil_exists_hasConductor_of_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
import Theorems.Thm_GlobalTheory_WeilM_HaarUniq_exists_eq_mul_integral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SplitWeil MeasureTheory ValuativeRel Matrix
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.HeisLine
open GlobalTheory.SplitWeil.FourierPi
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n]
variable [MeasurableSpace k] [BorelSpace k]
variable {χ : AddChar k Circle} {c : kˣ}
namespace GlobalTheory.HeisLine
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] (χ : AddChar k Circle), Continuous χ → χ ≠ 1 → ∀ (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (B : SB (n → k) →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ), (∀ (a a' b b' : SB (n → k)) (t : n → k), (∀ y, a'.1 y = (χ (t ⬝ᵥ y) : ℂ) * a.1 y) → (∀ η, b'.1 η = b.1 (η - t)) → B a' b = B a b') → (∀ (a a' b b' : SB (n → k)) (t : n → k), (∀ y, a'.1 y = a.1 (y - t)) → (∀ η, b'.1 η = (χ (η ⬝ᵥ t) : ℂ) * b.1 η) → B a' b = B a b') → ∃ c : ℂ, ∀ a b : SB (n → k), B a b = c * ∫ η, (∫ y, a.1 y * (χ (η ⬝ᵥ y) : ℂ) ∂μ) * b.1 η ∂μ := by
  intro k _ _ _ _ _ _ n _ χ hc hne μ _ B hL1 hL2
  classical
  obtain ⟨c, hχ⟩ := exists_hasConductor_of_continuous χ hc hne
  haveI := secondCountable k
  haveI := t2Space k
  haveI := nonarch (k := k) (n := n)
  have hm : ∀ a b : SB (n → k), (fun η => (∫ y, a.1 y * (χ (η ⬝ᵥ y) : ℂ) ∂μ) * b.1 η) ∈ SB (n → k) := by
    intro a b
    have h3 := fourier_mem_SB μ hχ a.2
    have h4 : (fun η => ∫ y, a.1 y * (χ (η ⬝ᵥ y) : ℂ) ∂μ) = fun η => ∫ x, a.1 x * (χ (x ⬝ᵥ η) : ℂ) ∂μ := by
      funext η
      simp only [dotProduct_comm η]
    rw [← h4] at h3
    exact ⟨h3.1.mul b.2.1, b.2.2.mul_left⟩
  obtain ⟨M, hM⟩ := LinearMap.exists_extend (ellL hχ μ B hL2)
  have hMe : ∀ g : SB (n → k), M g.1 = ell χ μ B g := fun g => LinearMap.congr_fun hM g
  obtain ⟨C, hC⟩ := GlobalTheory.WeilM.HaarUniq.exists_eq_mul_integral (n → k) μ M (fun φ hφ u => by
    have hmem : (fun x => φ (x + u)) ∈ SB (n → k) :=
      ⟨hφ.1.comp_continuous (continuous_id.add continuous_const), hφ.2.comp_homeomorph (Homeomorph.addRight u)⟩
    rw [hMe ⟨_, hmem⟩, ell_translate hχ μ B hL2 hL1 ⟨φ, hφ⟩ u hmem]
    exact (hMe ⟨φ, hφ⟩).symm)
  refine ⟨C, fun a b => ?_⟩
  rw [form_eq_ell hχ μ B hL2 a b (hm a b), ← hMe, hC _ (hm a b)]
end GlobalTheory.HeisLine
