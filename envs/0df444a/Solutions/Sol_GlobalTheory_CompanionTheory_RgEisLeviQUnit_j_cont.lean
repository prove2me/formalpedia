-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLeviQUnit.j_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:24:08.307204+00:00
-- url     : https://prove2.me/submissions/54cb082d-81dd-4f9b-8caf-84c07d9c3b9f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviQuotientOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_jM_cont

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
variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set ι} [Fintype ↥sᶜ] [DecidableEq ↥sᶜ] (A : Ad E R) (ε : ℤˣ)
namespace GlobalTheory.CompanionTheory.RgEisLeviQUnit
theorem _root_.solution : Continuous (jQ (s := s) A ε) := by
  refine continuous_induced_rng.2 (continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩))
  · exact jM_cont.comp (Units.continuous_val.comp continuous_subtype_val)
  · have : (fun m : A.U ε ↥sᶜ => (((jQ (s := s) A ε m : A.U ε ι).1)⁻¹ : GL (ι ⊕ ι) R).val) =
        fun m => jM (emb s) ((m.1)⁻¹ : GL (↥sᶜ ⊕ ↥sᶜ) R).val := by
      funext m
      exact jG_inv m.1
    exact this ▸ jM_cont.comp (Units.continuous_coe_inv.comp continuous_subtype_val)
end GlobalTheory.CompanionTheory.RgEisLeviQUnit
