-- Prove2me | solution 1 for GlobalTheory.ConvexCutOff.fderiv_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:38:31.619798+00:00
-- url     : https://prove2.me/submissions/df56d008-56ff-4fcb-84ce-08194f4bd42a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPermOfOfFnPerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PolyDerivRenameOfConvex
import Theorems.Thm_GlobalTheory_ConvexCutOff_uniqueDiffWithinAt_compl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open GlobalTheory GlobalTheory.ConvexCutOff
namespace GlobalTheory.ConvexCutOff
theorem _root_.solution {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] {K : Set V} (hK : Convex ℝ K) {G : V → W}
    (hG : ∀ z, z ∉ K → G z = 0) {x : V} (hx : x ∉ interior K) : fderiv ℂ G x = 0 := by
  by_cases hd : DifferentiableAt ℂ G x
  swap
  · exact fderiv_zero_of_not_differentiableAt hd
  have hU := uniqueDiffWithinAt_compl hK hx
  have hx0 : G x = 0 := by
    have := hd.continuousAt.continuousWithinAt.mem_closure_image hU.mem_closure
    have hs : G '' Kᶜ ⊆ {0} := by
      rintro _ ⟨z, hz, rfl⟩
      exact hG z hz
    exact closure_minimal hs isClosed_singleton this
  have h1 : HasFDerivWithinAt G ((fderiv ℂ G x).restrictScalars ℝ) Kᶜ x :=
    (hd.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have h2 : HasFDerivWithinAt G (0 : V →L[ℝ] W) Kᶜ x :=
    (hasFDerivWithinAt_const (0 : W) x Kᶜ).congr (fun z hz => hG z hz) hx0
  have h3 := hU.eq h1 h2
  ext z
  simpa using congrArg (fun φ : V →L[ℝ] W => φ z) h3
end GlobalTheory.ConvexCutOff
