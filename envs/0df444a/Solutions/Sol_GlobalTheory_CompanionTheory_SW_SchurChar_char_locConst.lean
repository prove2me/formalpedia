-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.SchurChar.char_locConst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:54:52.36979+00:00
-- url     : https://prove2.me/submissions/4ba40457-c235-407d-ad0c-b9f8c739b884

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AdelicProofs_SchurTranslationsCharacters
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_SchurChar_char_zero

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.SchurChar
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
  {χ : V → V → ℂ} {μ : Measure V}
namespace GlobalTheory.CompanionTheory.SW.SchurChar
theorem _root_.solution (h : NADual V χ μ) (y : V) : IsLocallyConstant (fun u => χ u y) := by
  have h0 := char_zero h
  obtain ⟨hTG, -, -, -, -, -, -, hcover, -, hsymm, -, hadd, hperp⟩ := h
  haveI := hTG
  obtain ⟨L, hLc, hLo, hy⟩ := hcover y
  obtain ⟨-, hPo, -, -⟩ := hperp L hLc hLo
  have h0P : (0 : V) ∈ perp χ L := fun x _ => by rw [hsymm]; exact h0 x
  rw [IsLocallyConstant.iff_exists_open]
  intro u
  refine ⟨(fun v => v - u) ⁻¹' perp χ L, hPo.preimage (continuous_sub_right u), by simpa using h0P, ?_⟩
  intro v hv
  have h1 : χ (v - u) y = 1 := by rw [hsymm]; exact hv y hy
  calc χ v y = χ ((v - u) + u) y := by simp
    _ = χ u y := by rw [hadd, h1, one_mul]
end GlobalTheory.CompanionTheory.SW.SchurChar
