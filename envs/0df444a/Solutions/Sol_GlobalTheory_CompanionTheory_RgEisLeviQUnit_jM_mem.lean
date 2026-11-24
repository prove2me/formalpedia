-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLeviQUnit.jM_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:04:07.045307+00:00
-- url     : https://prove2.me/submissions/cf072b68-3146-4795-aa0b-f9f5edb39c8a

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviQuotientOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_jM_off_left
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_jM_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLeviQUnit
open PositivityTheory.RgEis
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.RgEisLeviQUnit
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set ι} [Fintype ↥sᶜ] [DecidableEq ↥sᶜ] (O : Subring R)
    (m : Matrix (↥sᶜ ⊕ ↥sᶜ) (↥sᶜ ⊕ ↥sᶜ) R) (h : ∀ x y, m x y ∈ O) (r c : ι ⊕ ι) : jM (emb s) m r c ∈ O := by
  have h1 : ((1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) r c) ∈ O := by
    rw [Matrix.one_apply]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  by_cases hr : r ∈ Set.range (emb s)
  · by_cases hc : c ∈ Set.range (emb s)
    · obtain ⟨x, rfl⟩ := hr
      obtain ⟨y, rfl⟩ := hc
      rw [jM_apply emb_inj]
      exact h x y
    · rw [jM_off_right _ _ _ _ hc]
      exact h1
  · rw [jM_off_left _ _ _ _ hr]
    exact h1
end GlobalTheory.CompanionTheory.RgEisLeviQUnit
