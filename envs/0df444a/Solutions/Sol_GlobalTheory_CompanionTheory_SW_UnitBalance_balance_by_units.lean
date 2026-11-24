-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.UnitBalance.balance_by_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:54:56.330403+00:00
-- url     : https://prove2.me/submissions/f47fbed2-124d-4f55-8c28-662badd9c74c

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitBalancingImaginaryParts
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_UnitBalance_exists_bound_log_centered

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.UnitBalance
namespace GlobalTheory.CompanionTheory.SW.UnitBalance
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
    ∀ ρ : InfinitePlace F → (F →+* ℝ), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) →
    ∃ κ : ℝ, 0 < κ ∧ ∀ y : InfinitePlace F → ℝ, (∀ w, 0 < y w) →
      ∃ u : (𝓞 F)ˣ, ∀ v w, κ * (ρ w ((u : 𝓞 F) : F) ^ 2 * y w) ≤ ρ v ((u : 𝓞 F) : F) ^ 2 * y v := by
  intro F _ _ _ ρ hρ
  obtain ⟨R, hR⟩ := exists_bound_log_centered F
  refine ⟨Real.exp (-(4 * R)), Real.exp_pos _, fun y hy => ?_⟩
  obtain ⟨u, s, hu⟩ := hR (fun w => Real.log (y w) / 2)
  refine ⟨u, fun v w => ?_⟩
  have hne : ((u : 𝓞 F) : F) ≠ 0 := NumberField.Units.coe_ne_zero u
  have hexp : ∀ w : InfinitePlace F, ρ w ((u : 𝓞 F) : F) ^ 2 * y w =
      Real.exp (2 * (Real.log (y w) / 2 + Real.log (w ((u : 𝓞 F) : F)))) := by
    intro w
    have habs : w ((u : 𝓞 F) : F) = |ρ w ((u : 𝓞 F) : F)| := by
      rw [← InfinitePlace.norm_embedding_eq, ← hρ, Complex.norm_real, Real.norm_eq_abs]
    have hpos : 0 < w ((u : 𝓞 F) : F) := w.pos_iff.2 hne
    have e1 : 2 * (Real.log (y w) / 2 + Real.log (w ((u : 𝓞 F) : F))) =
        Real.log (w ((u : 𝓞 F) : F)) + Real.log (w ((u : 𝓞 F) : F)) + Real.log (y w) := by ring
    rw [e1, Real.exp_add, Real.exp_add, Real.exp_log hpos, Real.exp_log (hy w), habs, ← sq, sq_abs]
  rw [hexp v, hexp w, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 := abs_le.1 (hu v)
  have h2 := abs_le.1 (hu w)
  linarith [h1.1, h1.2, h2.1, h2.2]
end GlobalTheory.CompanionTheory.SW.UnitBalance
