-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MackeyFn.conj_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:52:40.256808+00:00
-- url     : https://prove2.me/submissions/7bbee535-1ff8-454f-9833-5724f19e2186

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MackeyInnerProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.MackeyFn
variable {Γ : Type} [Group Γ] [Fintype Γ]
namespace GlobalTheory.CompanionTheory.MackeyFn
theorem _root_.solution (H : Subgroup Γ) {u h : Γ} (hu : u ∈ H) : u * h * u⁻¹ ∈ H ↔ h ∈ H := by
  constructor
  · intro hh
    have : u⁻¹ * (u * h * u⁻¹) * u⁻¹⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (H.inv_mem hu) hh) (H.inv_mem (H.inv_mem hu))
    simpa [mul_assoc] using this
  · intro hh
    exact H.mul_mem (H.mul_mem hu hh) (H.inv_mem hu)
end GlobalTheory.CompanionTheory.MackeyFn
