-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CptModel.half_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:44.055326+00:00
-- url     : https://prove2.me/submissions/9770432d-0d19-4a1b-a387-af78277f4a98

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_mem_regAt_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.CptModel
open AlgebraicGeometry CategoryTheory
namespace GlobalTheory.CompanionTheory.Ar.CptModel
theorem _root_.solution : (2 : ℚ)⁻¹ ∉ regAt _ two := by
  rw [mem_regAt_iff]
  rintro ⟨a, s, hs, -, h⟩
  apply hs
  change s ∈ Ideal.span {(2 : ℤ)}
  rw [Ideal.mem_span_singleton]
  refine ⟨a, ?_⟩
  simp only [algebraMap_int_eq, eq_intCast] at h
  have : (s : ℚ) = 2 * a := by rw [← h]; ring
  exact_mod_cast this
end GlobalTheory.CompanionTheory.Ar.CptModel
