-- Prove2me | solution 1 for GlobalTheory.WeilTr.trRep_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:17.953745+00:00
-- url     : https://prove2.me/submissions/c2d1a487-7827-4340-b74c-6c0eb27bb637

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUSplittingTrRep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Matrix
open GlobalTheory GlobalTheory.WeilTr
open GlobalTheory.WeilM
variable {R : Type} [CommRing R] {κ : Type} [Fintype κ]
namespace GlobalTheory.WeilTr
theorem _root_.solution {G : Type} [Group G] (T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)) (om : G →* Module.End ℂ ((κ → R) → ℂ))
    (g : G) (φ : (κ → R) → ℂ) : trRep T om g φ = T (om g (T.symm φ)) := rfl
end GlobalTheory.WeilTr
