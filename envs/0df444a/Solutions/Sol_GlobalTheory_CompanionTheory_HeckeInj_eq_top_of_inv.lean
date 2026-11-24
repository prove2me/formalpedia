-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeInj.eq_top_of_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:37:03.389802+00:00
-- url     : https://prove2.me/submissions/cd149d71-b8ca-4b45-87bc-00163413252e

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IrreducibleHomFixedVectors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeInj
variable {G : Type} [Group G]
namespace GlobalTheory.CompanionTheory.HeckeInj
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    (hρ : ρ.IsIrreducible) (N : Submodule ℂ V) (hN : ∀ g, ∀ v ∈ N, ρ g v ∈ N) {w : V} (hw : w ∈ N)
    (h0 : w ≠ 0) : N = ⊤ := by
  let S : Subrepresentation ρ := { toSubmodule := N, apply_mem_toSubmodule := fun g v hv => hN g v hv }
  rcases hρ.eq_bot_or_eq_top S with h | h
  · exfalso
    have h1 : w ∈ S.toSubmodule := hw
    rw [h] at h1
    exact h0 h1
  · exact congrArg Subrepresentation.toSubmodule h
end GlobalTheory.CompanionTheory.HeckeInj
