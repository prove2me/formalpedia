-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeMul.out_mk_of_right_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:36:56.806624+00:00
-- url     : https://prove2.me/submissions/22b930ad-cca3-420b-958e-a59db53c3e16

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FinsumOutTranslate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2 Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeMul
variable {G : Type} [Group G]
namespace GlobalTheory.CompanionTheory.HeckeMul
theorem _root_.solution {M : Type} (K : Subgroup G) (φ : G → M)
    (hφ : ∀ x, ∀ k ∈ K, φ (x * k) = φ x) (x : G) :
    φ (QuotientGroup.mk x : G ⧸ K).out = φ x := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K x
  rw [hh]
  exact hφ x h h.2
end GlobalTheory.CompanionTheory.HeckeMul
