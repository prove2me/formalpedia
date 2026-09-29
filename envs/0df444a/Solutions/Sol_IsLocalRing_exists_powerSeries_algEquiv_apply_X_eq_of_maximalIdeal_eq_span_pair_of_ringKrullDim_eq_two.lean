-- Prove2me | solution 1 for IsLocalRing.exists_powerSeries_algEquiv_apply_X_eq_of_maximalIdeal_eq_span_pair_of_ringKrullDim_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/356e58c3-3643-5af4-b917-23f17afddf6f

import Mathlib
import Theorems.Thm_IsLocalRing_exists_algHom_powerSeries_map_X_eq_of_mem_maximalIdeal
import Theorems.Thm_RingHom_surjective_of_isAdicComplete_of_le_map_sup_sq
import Theorems.Thm_MvPowerSeries_isAdicComplete_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_powerSeries_algEquiv_apply_X_eq_of_maximalIdeal_eq_span_pair_of_ringKrullDim_eq_two

set_option autoImplicit false

open IsLocalRing

theorem solution
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀] [IsAdicComplete (maximalIdeal W₀) W₀]
    (ϖ : W₀) (hϖ : maximalIdeal W₀ = Ideal.span {ϖ})
    (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    [Algebra W₀ R] (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap W₀ R)))
    (y : R) (h𝔪 : maximalIdeal R = Ideal.span {algebraMap W₀ R ϖ, y})
    (hdim : ringKrullDim R = 2) :
    ∃ e : PowerSeries W₀ ≃ₐ[W₀] R, e PowerSeries.X = y := by
  classical
  set A := PowerSeries W₀ with hA
  have hymem : y ∈ maximalIdeal R := by rw [h𝔪]; exact Ideal.subset_span (by simp)

  obtain ⟨ev, hevX, -, -⟩ :=
    IsLocalRing.exists_algHom_powerSeries_map_X_eq_of_mem_maximalIdeal (𝒪 := W₀) (R := R) y hymem
  set φ : PowerSeries W₀ →+* R := ev.toRingHom with hφ
  have hφC : ∀ w : W₀, φ (PowerSeries.C w) = algebraMap W₀ R w := fun w => by
    rw [hφ, PowerSeries.C_eq_algebraMap]; exact ev.commutes w
  have hφX : φ PowerSeries.X = y := hevX

  have hmaxA : maximalIdeal (PowerSeries W₀) = Ideal.span {PowerSeries.C ϖ, PowerSeries.X} := by
    apply le_antisymm
    · intro f hf
      have hfu : ¬IsUnit f := (IsLocalRing.mem_maximalIdeal _).mp hf
      have hc : PowerSeries.constantCoeff f ∈ maximalIdeal W₀ :=
        (IsLocalRing.mem_maximalIdeal _).mpr fun hu => hfu (PowerSeries.isUnit_iff_constantCoeff.mpr hu)
      rw [hϖ, Ideal.mem_span_singleton] at hc
      obtain ⟨c, hc⟩ := hc
      have e := PowerSeries.eq_X_mul_shift_add_const f
      rw [e, hc, map_mul]
      refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
    · rw [Ideal.span_le]
      rintro f hf
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
      rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
      rcases hf with rfl | rfl
      · rw [PowerSeries.constantCoeff_C]
        have : ϖ ∈ maximalIdeal W₀ := by rw [hϖ]; exact Ideal.subset_span rfl
        exact this
      · rw [PowerSeries.constantCoeff_X]; exact not_isUnit_zero

  have hmapJ : Ideal.map φ (maximalIdeal (PowerSeries W₀)) = maximalIdeal R := by
    rw [hmaxA, Ideal.map_span, Set.image_insert_eq, Set.image_singleton, hφC, hφX, h𝔪]

  haveI : IsAdicComplete (maximalIdeal (PowerSeries W₀)) (PowerSeries W₀) :=
    MvPowerSeries.isAdicComplete_maximalIdeal (σ := Unit) (R := W₀)
  have hsurj : Function.Surjective φ := by
    refine RingHom.surjective_of_isAdicComplete_of_le_map_sup_sq (maximalIdeal (PowerSeries W₀)) (maximalIdeal R) φ
      (le_of_eq hmapJ) ?_ (by rw [hmapJ]; exact le_sup_left)
    intro r
    obtain ⟨w, hw⟩ := hres (residue R r)
    refine ⟨PowerSeries.C w, ?_⟩
    rw [hφC, ← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact hw.symm

  have hdimA : ringKrullDim (PowerSeries W₀) ≤ 2 := by
    refine (ringKrullDim_le_spanFinrank_maximalIdeal (PowerSeries W₀)).trans ?_
    rw [hmaxA]
    have h2 : (Submodule.span (PowerSeries W₀) ({PowerSeries.C ϖ, PowerSeries.X} : Set (PowerSeries W₀))).spanFinrank ≤ 2 := by
      refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite _)).trans ?_
      exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    exact_mod_cast h2
  have hinj : Function.Injective φ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra hker
    obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have h3 : ringKrullDim R + 1 ≤ ringKrullDim (PowerSeries W₀) :=
      ringKrullDim_succ_le_of_surjective φ hsurj (mem_nonZeroDivisors_of_ne_zero hr0) hr
    rw [hdim] at h3
    have : (2 : WithBot ℕ∞) + 1 ≤ 2 := h3.trans hdimA
    exact absurd this (by decide)
  refine ⟨AlgEquiv.ofBijective ev ⟨hinj, hsurj⟩, ?_⟩
  rw [AlgEquiv.ofBijective_apply]
  exact hevX

end S_IsLocalRing_exists_powerSeries_algEquiv_apply_X_eq_of_maximalIdeal_eq_span_pair_of_ringKrullDim_eq_two
end P2MW
export P2MW.S_IsLocalRing_exists_powerSeries_algEquiv_apply_X_eq_of_maximalIdeal_eq_span_pair_of_ringKrullDim_eq_two (solution)
