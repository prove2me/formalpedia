-- Prove2me | solution 1 for GlobalTheory.InertiaAlmostAll.val_le_one_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:47:37.673552+00:00
-- url     : https://prove2.me/submissions/44f2ddbf-6760-406f-b57a-4199e3b8b6bd

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinitePlacesInertiaNotFixingFiniteExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.InertiaAlmostAll
namespace GlobalTheory.InertiaAlmostAll
theorem _root_.solution {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {w : Ω}
    (hw : IsIntegral ℤ w) : B.valuation w ≤ 1 := by
  have h : IsIntegral B w := hw.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  rw [B.valuation_le_one_iff, ← hy]
  exact y.2
end GlobalTheory.InertiaAlmostAll
