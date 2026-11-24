-- Prove2me | solution 1 for GlobalTheory.T.lattice_hom_submodule_fg_and_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:36:08.016863+00:00
-- url     : https://prove2.me/submissions/94162643-f142-49f6-ac1c-85af474734f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LatticeHomSubmoduleFgAndSpanEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdEApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LatticeHomSubmoduleFgAndSpanEqTopStatement
import Theorems.Thm_GlobalTheory_StableLatCount_homLat_fg_and_span_eq_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (E : Type) [Field E] [Algebra O E] [IsFractionRing O E] (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (M₁ : Submodule O A₁) (M₂ : Submodule O A₂), IsLat O E M₁ → IsLat O E M₂ → (homLat E M₁ M₂).FG ∧ Submodule.span E (homLat E M₁ M₂ : Set (A₂ →ₗ[E] A₁)) = ⊤ := by
  first | exact @GlobalTheory.StableLatCount.homLat_fg_and_span_eq_top | exact GlobalTheory.StableLatCount.homLat_fg_and_span_eq_top | (intros; apply GlobalTheory.StableLatCount.homLat_fg_and_span_eq_top <;> assumption)
end _root_.GlobalTheory.T
