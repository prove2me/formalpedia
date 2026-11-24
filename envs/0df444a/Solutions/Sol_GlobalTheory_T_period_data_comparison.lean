-- Prove2me | solution 1 for GlobalTheory.T.period_data_comparison
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:34:03.359834+00:00
-- url     : https://prove2.me/submissions/11ae80d5-faa6-46b0-a8b6-47745cc020a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PeriodDataComparison
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PeriodDataComparisonStatement
import Theorems.Thm_GlobalTheory_SplitJump_jump_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {n : ℕ} (e : Module.Basis (Fin n) Qp V) (W W' : Matrix (Fin n) (Fin n) BdR), W * W' = 1 → (∀ i j, W i j ∈ PD.Fil 0) → (∀ i j, W' i j ∈ PD.Fil 0) → (∀ g, (Matrix.of fun i j => algebraMap Qp BdR (e.repr (ρ g (e j)) i)) * W.map (PD.actdR g) = W) → ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), Formalism.WeaklyAdmissibleFiltrations.IsJumpV PD ρ τ a → a = 0 := by
  first | exact @GlobalTheory.SplitJump.jump_eq_zero | exact GlobalTheory.SplitJump.jump_eq_zero | (intros; apply GlobalTheory.SplitJump.jump_eq_zero <;> assumption)
end _root_.GlobalTheory.T
