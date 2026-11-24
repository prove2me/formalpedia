-- Prove2me | solution 1 for GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:31:34.134025+00:00
-- url     : https://prove2.me/submissions/7a197972-50ce-4151-9dad-d97e14d5536d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQCoeffIffHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQMdifferentiableAndIsBoundedAtImInfty
import Theorems.Thm_GlobalTheory_QFam_HasQ_mdifferentiable
import Theorems.Thm_GlobalTheory_QFam_HasQ_isBoundedAtImInfty
import Theorems.Thm_GlobalTheory_HasQExpansion_isBoundedAtImInfty
import Theorems.Thm_GlobalTheory_HasQExpansion_mdifferentiable
import Theorems.Thm_GlobalTheory_QFam_hasQ_coeff_iff_hasQExpansion


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory GlobalTheory.QFam
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
namespace GlobalTheory.QFam
namespace _root_.GlobalTheory.QFam
theorem _root_.solution :
    ∀ (N : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ), 0 < N → _root_.GlobalTheory.QFam.HasQ N f a →
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧ UpperHalfPlane.IsBoundedAtImInfty f := by
  intro N f a hN h
  have h' : _root_.GlobalTheory.QFam.HasQ N f (fun n => PowerSeries.coeff n (PowerSeries.mk a)) := by
    simpa only [PowerSeries.coeff_mk] using h
  have hq := (_root_.GlobalTheory.QFam.hasQ_coeff_iff_hasQExpansion N f _).1 h'
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  exact ⟨hq.mdifferentiable hpos, hq.isBoundedAtImInfty hpos⟩
end _root_.GlobalTheory.QFam
end GlobalTheory.QFam
