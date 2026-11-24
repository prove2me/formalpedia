-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.Density.chi_neg_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:14:01.122812+00:00
-- url     : https://prove2.me/submissions/096ccabb-e214-4863-8960-e3bcb5ae910b

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FourierInversionSchwartzBruhatStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PositiveDefiniteDensity

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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.Density
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
namespace GlobalTheory.CompanionTheory.SW.Core.Density
theorem _root_.solution {χ : V → V → ℂ} (hs : ∀ x y, χ x y = χ y x) (hn : ∀ x y, ‖χ x y‖ = 1)
    (ha : ∀ x x' y, χ (x + x') y = χ x y * χ x' y) (x y : V) : χ (-x) y = χ x (-y) := by
  have hne : ∀ x y, χ x y ≠ 0 := fun x y h => by simpa [h] using hn x y
  have h0 : ∀ y, χ 0 y = 1 := fun y => by
    have h := ha 0 0 y
    rw [add_zero] at h
    have h' : χ 0 y * χ 0 y = χ 0 y * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel₀ (hne 0 y) h'
  have hi : ∀ x y, χ (-x) y * χ x y = 1 := fun x y => by
    rw [← ha, neg_add_cancel, h0]
  have h1 := hi x y
  have h2 := hi y x
  rw [hs (-y) x, hs y x] at h2
  exact mul_right_cancel₀ (hne x y) (h1.trans h2.symm)
end GlobalTheory.CompanionTheory.SW.Core.Density
