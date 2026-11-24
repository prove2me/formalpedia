-- Prove2me | solution 1 for GlobalTheory.QFam.HasQ.mdifferentiable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:22:15.172711+00:00
-- url     : https://prove2.me/submissions/a9a19d4c-da66-4b1c-ae3a-8a790abeb36a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQCoeffIffHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQMdifferentiableAndIsBoundedAtImInfty
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
namespace _root_.GlobalTheory.QFam.HasQ
theorem _root_.solution {N : ℕ} {f : ℍ → ℂ} {a : ℕ → ℂ} (hN : 0 < N)
    (h : _root_.GlobalTheory.QFam.HasQ N f a) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
  have h' : _root_.GlobalTheory.QFam.HasQ N f (fun n => PowerSeries.coeff n (PowerSeries.mk a)) := by
    simpa only [PowerSeries.coeff_mk] using h
  exact ((_root_.GlobalTheory.QFam.hasQ_coeff_iff_hasQExpansion N f _).1 h').mdifferentiable (by exact_mod_cast hN)
end _root_.GlobalTheory.QFam.HasQ
end GlobalTheory.QFam
