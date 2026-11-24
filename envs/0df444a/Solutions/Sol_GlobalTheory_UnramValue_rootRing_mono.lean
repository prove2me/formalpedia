-- Prove2me | solution 1 for GlobalTheory.UnramValue.rootRing_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:08:28.511895+00:00
-- url     : https://prove2.me/submissions/b22d3dd3-965d-42b7-b16e-6618a83878f1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEqZpowOfMemMaxUnramifiedSubfield

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
noncomputable section
open GlobalTheory GlobalTheory.UnramValue
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.UnramValue
theorem _root_.solution {m m' : ℕ} (h : m ∣ m') : rootRing l m ≤ rootRing l m' := by
  unfold rootRing
  apply Algebra.adjoin_mono
  intro x hx
  have hx' : x ^ m = 1 := hx
  obtain ⟨k, rfl⟩ := h
  show x ^ (m * k) = 1
  rw [pow_mul, hx', one_pow]
end GlobalTheory.UnramValue
