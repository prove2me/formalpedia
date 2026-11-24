-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.exists_div_of_mem_closure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:17:26.075961+00:00
-- url     : https://prove2.me/submissions/1b0cf50a-509a-49b5-80ab-88a313fbd43d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_CoordTieCompEquiv
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_FrameMatrixChartRatios

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
namespace GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen
theorem _root_.solution {K : Type*} [Field K] [Algebra ℤ K] {t : Set K} {a : K} (ha : a ∈ Subfield.closure t) :
    ∃ g ∈ Algebra.adjoin ℤ t, ∃ h ∈ Algebra.adjoin ℤ t, h ≠ 0 ∧ a = g / h := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Subfield.mem_closure_iff.1 ha
  have key : ∀ w ∈ Subring.closure t, w ∈ Algebra.adjoin ℤ t := by
    intro w hw
    induction hw using Subring.closure_induction with
    | mem a ha => exact Algebra.subset_adjoin ha
    | zero => exact zero_mem _
    | one => exact one_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | neg a _ ha => exact neg_mem ha
    | mul a b _ _ ha hb => exact mul_mem ha hb
  by_cases h0 : z = 0
  · exact ⟨0, zero_mem _, 1, one_mem _, one_ne_zero, by simp [h0]⟩
  · exact ⟨y, key y hy, z, key z hz, h0, rfl⟩
end GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen
