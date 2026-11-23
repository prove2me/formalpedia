-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.rep_cls
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:29:07.781245+00:00
-- url     : https://prove2.me/submissions/42e024bb-bdb7-448b-b56e-a43f1b4431fd

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_StagedEstimateHolds
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_cls_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_cls_rep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis
open PositivityTheory.RgEis
variable {G : Type} [Group G] {P Δ Γ : Subgroup G}
namespace GlobalTheory.CompanionTheory.RgEis
theorem _root_.solution (y : Γ) : ∃ p ∈ P, p ∈ Γ ∧ rep (cls y : Cos P Γ) = p * y := by
  have h : (cls y : Cos P Γ) = cls ⟨rep (cls y : Cos P Γ), rep_mem _⟩ := (cls_rep _).symm
  refine ⟨rep (cls y : Cos P Γ) * (y : G)⁻¹, cls_eq.1 h, Γ.mul_mem (rep_mem _) (Γ.inv_mem y.2), by group⟩
end GlobalTheory.CompanionTheory.RgEis
