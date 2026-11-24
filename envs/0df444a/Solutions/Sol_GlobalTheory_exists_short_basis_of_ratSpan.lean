-- Prove2me | solution 1 for GlobalTheory.exists_short_basis_of_ratSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:34:39.285305+00:00
-- url     : https://prove2.me/submissions/936e4abf-966a-47db-a3ac-656f3aa790ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsShortBasisAdaptedOfSubsetSpan
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsReducedBasisIntegralPartOfLinearIndependen
import Theorems.Thm_GlobalTheory_exists_short_basis_adapted_of_subset_span
import Theorems.Thm_GlobalTheory_norm_sq_add_sum_Iio_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule MvPolynomial NumberField
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {V E ι : Type*} [AddCommGroup V] [Module ℚ V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (H : Submodule ℤ V) (φ : V →+ E) {ε : ℝ} (hε : 0 < ε)
    (hφ : ∀ x ∈ H, x ≠ 0 → ε ≤ ‖φ x‖) (v : ι → V) (hvH : ∀ j, v j ∈ H)
    (hsp : (H : Set V) ⊆ span ℚ (Set.range v)) {r : ℝ} (hr : ∀ j, ‖φ (v j)‖ ≤ r) {R : ℕ}
    (hR : R = finrank ℚ (span ℚ (Set.range v))) :
    ∃ b : Basis (Fin R) ℤ H, ∀ i, ‖φ (b i)‖ ^ 2 ≤ ((R + 3 : ℝ) / 4) * r ^ 2 := by
  classical
  let ψ : H →ₗ[ℤ] E := φ.toIntLinearMap ∘ₗ H.subtype
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h
    have := hφ x x.2 (fun h' => h (Subtype.ext h'))
    have hx' : φ x = 0 := hx
    rw [hx', norm_zero] at this
    linarith
  let L : Submodule ℤ E := LinearMap.range ψ
  haveI : DiscreteTopology L := by
    refine discreteTopology_of_isOpen_singleton_zero ?_
    have : ({0} : Set L) = Metric.ball 0 ε := by
      ext y
      simp only [Set.mem_singleton_iff, Metric.mem_ball, dist_zero_right]
      refine ⟨fun h => by simpa [h] using hε, fun h => ?_⟩
      obtain ⟨_, x, rfl⟩ := y
      by_contra h0
      have hx : (x : V) ≠ 0 := fun h' => h0 (by
        have : x = 0 := Subtype.ext h'
        simp [this])
      exact absurd (hφ x x.2 hx) (not_le.2 h)
    rw [this]; exact Metric.isOpen_ball
  obtain ⟨κ, a, -, hspan, hli⟩ := exists_linearIndependent' ℝ (fun j => φ (v j))
  haveI : Finite κ := hli.finite
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin κ
  have hli' := hli.comp e.symm e.symm.injective
  have hL : ∀ i, (((fun j => φ (v j)) ∘ a) ∘ e.symm) i ∈ L := fun i => ⟨⟨_, hvH _⟩, rfl⟩
  have hsub : (L : Set E) ⊆ span ℝ (Set.range (((fun j => φ (v j)) ∘ a) ∘ e.symm)) := by
    rw [e.symm.surjective.range_comp, hspan]
    rintro _ ⟨x, rfl⟩
    have key : ∀ y ∈ span ℚ (Set.range v), φ y ∈ span ℝ (Set.range fun j => φ (v j)) := by
      intro y hy
      induction hy using span_induction with
      | mem y hy => obtain ⟨j, rfl⟩ := hy; exact subset_span ⟨j, rfl⟩
      | zero => simp
      | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
      | smul q y _ hy =>
        rw [show φ (q • y) = (q : ℝ) • φ y by simpa using map_ratCast_smul φ ℚ ℝ q y]
        exact smul_mem _ _ hy
    exact key x (hsp x.2)
  obtain ⟨b, -, hb⟩ := exists_short_basis_adapted_of_subset_span L hli' hL hsub
  let b' : Basis (Fin n) ℤ H := b.map (LinearEquiv.ofInjective ψ hψ).symm
  have hb' : ∀ i, φ (b' i) = b i := fun i => by
    have := LinearEquiv.ofInjective_apply ψ (h := hψ) (b' i)
    simp only [b', Basis.map_apply, LinearEquiv.apply_symm_apply] at this
    exact this.symm
  have hn : n = R := by
    have h1 : LinearIndependent ℚ (fun i => (b' i : V)) :=
      (LinearIndependent.iff_fractionRing ℤ ℚ).1
        (b'.linearIndependent.map' H.subtype H.ker_subtype)
    have h2 : span ℚ (Set.range fun i => (b' i : V)) = span ℚ (Set.range v) := by
      refine le_antisymm (span_le.2 ?_) (span_le.2 ?_)
      · rintro _ ⟨i, rfl⟩; exact hsp (b' i).2
      · rintro _ ⟨j, rfl⟩
        have h3 := b'.mem_span (⟨v j, hvH j⟩ : H)
        have h4 := Submodule.mem_map_of_mem (f := H.subtype) h3
        rw [Submodule.map_span, ← Set.range_comp] at h4
        exact span_subset_span ℤ ℚ _ h4
    rw [hR, ← h2, finrank_span_eq_card h1, Fintype.card_fin]
  subst hn
  refine ⟨b', fun i => ?_⟩
  rw [hb']
  refine (hb i).trans ((norm_sq_add_sum_Iio_le (r := r) fun j _ => hr (a (e.symm j))).trans
    (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)))
  have : ((i : ℕ) + 1 : ℝ) ≤ n := by exact_mod_cast i.2
  linarith
end GlobalTheory
