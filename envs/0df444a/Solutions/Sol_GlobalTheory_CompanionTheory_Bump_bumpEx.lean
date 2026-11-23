-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Bump.bumpEx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:13:49.240216+00:00
-- url     : https://prove2.me/submissions/ae86273e-04ca-4482-9d50-40bbcb1d1d47

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_VecClose
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BumpEx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Bump
namespace GlobalTheory.CompanionTheory.Bump
theorem _root_.solution : BumpEx := by
  intro X W hW
  obtain ⟨N, hNn, hNW, hNc⟩ := local_compact_nhds hW
  have h1 : (1 : X.G) ∈ interior N := mem_interior_iff_mem_nhds.mpr hNn
  obtain ⟨b, hb1, hb0, hbc, hbI⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_singleton (x := (1 : X.G))) isOpen_interior.isClosed_compl
    (Set.disjoint_singleton_left.mpr (fun h => h h1))
  have hbnn : ∀ z, 0 ≤ b z := fun z => (hbI z).1
  have hb11 : b 1 = 1 := hb1 (Set.mem_singleton _)
  have hsupp : Function.support b ⊆ N := by
    intro x hx
    by_contra hxN
    exact hx (hb0 (fun hi => hxN (interior_subset hi)))
  have hts : tsupport b ⊆ N := closure_minimal hsupp hNc.isClosed
  have hcc : Continuous fun z : X.G => b z⁻¹ := b.continuous.comp continuous_inv
  have hcs : HasCompactSupport fun z : X.G => b z⁻¹ :=
    hbc.comp_homeomorph (Homeomorph.inv X.G)
  have hI : 0 < ∫ z, b z⁻¹ ∂X.μ :=
    hcc.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs (fun z => hbnn _)
      (x := 1) (by simp [hb11])
  set I := ∫ z, b z⁻¹ ∂X.μ with hIdef
  have hnorm : ∀ z, ‖((b z / I : ℝ) : ℂ)‖ = b z / I := fun z => by
    rw [Complex.norm_real, Real.norm_of_nonneg (div_nonneg (hbnn z) hI.le)]
  have hsub : Function.support (fun z => ((b z / I : ℝ) : ℂ)) ⊆ Function.support b := by
    intro x hx h0
    apply hx
    simp [h0]
  refine ⟨fun z => ((b z / I : ℝ) : ℂ), ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · exact Complex.continuous_ofReal.comp (b.continuous.div_const I)
  · exact hbc.mono hsub
  · intro z
    simp only [hnorm]
  · simp only [hnorm]
    rw [integral_div, ← hIdef, div_self hI.ne']
  · exact (closure_mono hsub).trans (hts.trans hNW)
end GlobalTheory.CompanionTheory.Bump
