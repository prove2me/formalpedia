-- Prove2me | solution 1 for GlobalTheory.QFam.hasQ_powerSeries_bridge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:56:35.438805+00:00
-- url     : https://prove2.me/submissions/1f2f3e6d-d90d-489d-ba50-5ae74638e588

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQCoeffIffHasQExpansion
import Theorems.Thm_GlobalTheory_QFam_hasQ_iff_hasQExpansion_mk
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
namespace GlobalTheory.QFam
theorem _root_.solution :
    (∀ (N : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ),
      HasQ N f a ↔ GlobalTheory.HasQExpansion (N : ℝ) f (PowerSeries.mk a)) ∧
    (∀ (N : ℕ) (f : ℍ → ℂ) (φ : PowerSeries ℂ),
      HasQ N f (fun n => PowerSeries.coeff n φ) ↔ GlobalTheory.HasQExpansion (N : ℝ) f φ) :=
  ⟨hasQ_iff_hasQExpansion_mk, hasQ_coeff_iff_hasQExpansion⟩
end GlobalTheory.QFam
