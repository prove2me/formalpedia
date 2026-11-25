-- Prove2me | solution 1 for GlobalTheory.SW.exists_linearIndependent_of_rat_independent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:08:04.886694+00:00
-- url     : https://prove2.me/submissions/b1e502cb-2011-49ee-b2ad-67b1bdb8b8b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsLinearIndependentOfRatIndependent
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW
namespace GlobalTheory.SW
theorem _root_.solution {E U : Type} [Field E] [NumberField E]
    [AddCommGroup U] [Module E U] [Module ℚ U] [IsScalarTower ℚ E U] (S : ℕ → Set U) (N : ℕ)
    (h : ∀ i < N, ∃ u : Fin (Module.finrank ℚ E * i + 1) → U,
      LinearIndependent ℚ u ∧ ∀ k, u k ∈ S i) :
    ∃ w : Fin N → U, LinearIndependent E w ∧ ∀ i : Fin N, w i ∈ S i := by
  induction N with
  | zero => exact ⟨Fin.elim0, linearIndependent_empty_type, fun i => i.elim0⟩
  | succ N ih =>
    obtain ⟨w, hw, hS⟩ := ih fun i hi => h i (by omega)
    obtain ⟨u, hu, huS⟩ := h N (by omega)
    obtain ⟨k, hk⟩ : ∃ k, u k ∉ Submodule.span E (Set.range w) := by
      by_contra! hc
      have : Module.Finite E (Submodule.span E (Set.range w)) :=
        Module.Finite.span_of_finite E (Set.finite_range w)
      have : Module.Finite ℚ (Submodule.span E (Set.range w)) := Module.Finite.trans E _
      have h1 : LinearIndependent ℚ (fun k => (⟨u k, hc k⟩ : Submodule.span E (Set.range w))) :=
        LinearIndependent.of_comp
          ((Submodule.span E (Set.range w)).subtype.restrictScalars ℚ) hu
      have h2 := h1.fintype_card_le_finrank
      rw [← Module.finrank_mul_finrank ℚ E (Submodule.span E (Set.range w)),
        finrank_span_eq_card hw] at h2
      simp at h2
    refine ⟨Fin.snoc w (u k), linearIndependent_finSnoc.2 ⟨hw, hk⟩, fun i => ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using huS k
    · simpa using hS j
end GlobalTheory.SW
