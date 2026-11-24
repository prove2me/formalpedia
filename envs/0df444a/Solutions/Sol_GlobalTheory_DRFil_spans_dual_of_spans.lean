-- Prove2me | solution 1 for GlobalTheory.DRFil.spans_dual_of_spans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:24:15.918467+00:00
-- url     : https://prove2.me/submissions/740bec11-9656-4ad5-a623-5bca8b68db9e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFinBasisSubsetOfIsField
import Theorems.Thm_GlobalTheory_DRFil_spans_dual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DRFil
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module
namespace GlobalTheory.DRFil
theorem _root_.solution : ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F] [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F] (PD : PeriodData G Qp K₀ K B F) {LL : Type} [Field LL] [Algebra Qp LL] [FiniteDimensional Qp LL] [FiniteDimensional Qp K] [CharZero Qp] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [FiniteDimensional LL V] (ρ : Representation LL G V) {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V'] [FiniteDimensional LL V'] (ρ' : Representation LL G V') (β : V →ₗ[LL] V' →ₗ[LL] LL), IsField F → (∀ g x y, β (ρ g x) (ρ' g y) = β x y) → Function.Bijective β.flip → Spans PD ρ → Spans PD ρ' := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B F _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ _ _ _ V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' β hF hβ hb h
  exact spans_dual PD ρ ρ' β hF hβ hb h
end GlobalTheory.DRFil
