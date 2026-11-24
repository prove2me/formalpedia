-- Prove2me | solution 1 for GlobalTheory.Chow.exists_field_generic_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:58:57.918352+00:00
-- url     : https://prove2.me/submissions/8be90dc1-c16e-4bed-a3fc-4fd8cdfd7e3a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimeSaturationGenericHyperplaneSection
import Theorems.Thm_GlobalTheory_Chow_aeval_genericPoint_eq_zero_iff
import Theorems.Thm_GlobalTheory_Chow_genericPoint_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
namespace GlobalTheory.Chow
theorem _root_.solution {σ K : Type} [CommRing K] {p : Ideal (MvPolynomial σ K)}
    [p.IsPrime] (hp : ∃ j, X j ∉ p) :
    ∃ (F : Type) (_ : Field F) (_ : Algebra K F) (ξ : σ → F),
      (∀ g, aeval ξ g = 0 ↔ g ∈ p) ∧ ξ ≠ 0 :=
  ⟨FractionRing (MvPolynomial σ K ⧸ p), inferInstance, inferInstance, genericPoint p,
    aeval_genericPoint_eq_zero_iff p, genericPoint_ne_zero hp⟩
end GlobalTheory.Chow
