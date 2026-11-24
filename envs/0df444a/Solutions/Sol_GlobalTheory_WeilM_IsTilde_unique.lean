-- Prove2me | solution 1 for GlobalTheory.WeilM.IsTilde.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:35:56.805901+00:00
-- url     : https://prove2.me/submissions/8ddbc03f-269e-4140-93ca-3faa3cc13b80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Theorems.Thm_GlobalTheory_WeilM_isTilde_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped NNReal Classical
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {c}
namespace GlobalTheory.WeilM
namespace IsTilde
theorem _root_.solution {χ : Eˣ →* Circle} (hχ : ∀ z : Eˣ, c z = z → χ z = 1) {u : Eˣ} {t t' : Circle}
    (h : IsTilde c χ u t) (h' : IsTilde c χ u t') : t = t' := by
  obtain ⟨_, rfl⟩ := (isTilde_iff χ hχ u t).mp h
  obtain ⟨_, rfl⟩ := (isTilde_iff χ hχ u t').mp h'
  rfl
end IsTilde
end GlobalTheory.WeilM
