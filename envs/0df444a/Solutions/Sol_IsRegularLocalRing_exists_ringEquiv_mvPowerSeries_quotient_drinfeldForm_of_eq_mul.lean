-- Prove2me | solution 1 for IsRegularLocalRing.exists_ringEquiv_mvPowerSeries_quotient_drinfeldForm_of_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/602372f3-e18f-5e40-9190-27dc4b66b508

import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import Theorems.Thm_IsRegularLocalRing_exists_algEquiv_mvPowerSeries_quotient_span_C_sub_of_maximalIdeal_eq_span_pair
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsRegularLocalRing_exists_ringEquiv_mvPowerSeries_quotient_drinfeldForm_of_eq_mul
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

open IsLocalRing MvPowerSeries

namespace PairCoreAux

variable {W : Type} [CommRing W]

lemma constantCoeff_eq_zero_of_mem_span_X {r : MvPowerSeries (Fin 2) W}
    (hr : r ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}) : constantCoeff r = 0 := by
  have hle : Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1} ≤
      RingHom.ker (constantCoeff : MvPowerSeries (Fin 2) W →+* W) := by
    rw [Ideal.span_le]
    rintro x hx
    rcases hx with rfl | rfl <;> simp [RingHom.mem_ker, constantCoeff_X]
  exact hle hr

lemma constantCoeff_eq_zero_of_mem_span_X_pow {n : ℕ} (hn : n ≠ 0) {r : MvPowerSeries (Fin 2) W}
    (hr : r ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1} ^ n) : constantCoeff r = 0 :=
  constantCoeff_eq_zero_of_mem_span_X (Ideal.pow_le_self hn hr)

lemma constantCoeff_drinfeldForm (q : ℕ) [Fact q.Prime] :
    constantCoeff (DrinfeldCurve.LocalChart.drinfeldForm q W) = 0 := by
  have hq : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  simp [DrinfeldCurve.LocalChart.drinfeldForm, constantCoeff_X, hq]

end PairCoreAux

open PairCoreAux in
set_option maxHeartbeats 3200000 in
theorem solution
    (q : ℕ) [Fact q.Prime]
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    (hreg : IsRegularLocalRing R) (hdim : ringKrullDim R = 2)
    (x₀ x₁ : R) (hmax : maximalIdeal R = Ideal.span {x₀, x₁})
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : maximalIdeal W = Ideal.span {π})
    (g : W →+* R) [IsLocalHom g] (hres : ∀ r : R, ∃ w : W, r - g w ∈ maximalIdeal R)
    (F uF : R) (huF : IsUnit uF) (hπF : g π = uF * F)
    (hF : F - (x₀ * x₁ ^ q - x₀ ^ q * x₁) ∈ maximalIdeal R ^ (q + 2)) :
    ∃ (f u v : MvPowerSeries (Fin 2) W) (_ : IsUnit u) (_ : IsUnit v)
      (_ : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
        (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
      (e : R ≃+* MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C π * v - f * u}),
      (∀ w : W, e (g w) = Ideal.Quotient.mk _ (MvPowerSeries.C w)) ∧
      e x₀ = Ideal.Quotient.mk _ (MvPowerSeries.X 0) ∧ e x₁ = Ideal.Quotient.mk _ (MvPowerSeries.X 1) := by
  classical
  letI : Algebra W R := g.toAlgebra
  haveI : IsRegularLocalRing R := hreg
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have hq2 : q + 2 ≠ 0 := by omega

  have hπW : π ∈ maximalIdeal W := by rw [hπ]; exact Ideal.mem_span_singleton_self π
  have hπnu : ¬ IsUnit π := (mem_maximalIdeal π).mp hπW
  have hπ0 : π ≠ 0 := by
    rintro rfl
    apply IsDiscreteValuationRing.not_a_field W
    rw [hπ, Ideal.span_singleton_eq_bot]
  have hπR : algebraMap W R π ∈ maximalIdeal R := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => hπnu (IsLocalHom.map_nonunit π hu)

  obtain ⟨h, hh0, e, hex₀, hex₁⟩ :=
    IsRegularLocalRing.exists_algEquiv_mvPowerSeries_quotient_span_C_sub_of_maximalIdeal_eq_span_pair
      W π hπ R hdim (fun r => hres r) hπR x₀ x₁ hmax

  have hθ : Function.Surjective (Ideal.Quotient.mk (Ideal.span {C π - h})) := Ideal.Quotient.mk_surjective
  have heg : ∀ w : W, e (g w) = Ideal.Quotient.mk (Ideal.span {C π - h}) (C w) := fun w => by
    change e (algebraMap W R w) = _
    rw [AlgEquiv.commutes]
    rfl

  have hmapmax : (maximalIdeal R).map (e : R →+* MvPowerSeries (Fin 2) W ⧸ Ideal.span {C π - h}) =
      (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}).map (Ideal.Quotient.mk (Ideal.span {C π - h})) := by
    rw [hmax, Ideal.map_span, Ideal.map_span, Set.image_insert_eq, Set.image_singleton, Set.image_insert_eq,
      Set.image_singleton]
    change Ideal.span {e x₀, e x₁} = _
    rw [hex₀, hex₁]

  have hFD : e (F - (x₀ * x₁ ^ q - x₀ ^ q * x₁)) ∈
      ((Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}) ^ (q + 2)).map
        (Ideal.Quotient.mk (Ideal.span {C π - h})) := by
    rw [Ideal.map_pow, ← hmapmax, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hF
  obtain ⟨r, hrJ, hr⟩ := (Ideal.mem_map_iff_of_surjective _ hθ).mp hFD

  have hCπh : ¬ IsUnit (C π - h) := by
    rw [isUnit_iff_constantCoeff, map_sub, constantCoeff_C, hh0, sub_zero]
    exact hπnu
  have hItop : Ideal.span {C π - h} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]; exact hCπh
  haveI : Nontrivial (MvPowerSeries (Fin 2) W ⧸ Ideal.span {C π - h}) := Ideal.Quotient.nontrivial_iff.mpr hItop
  haveI : IsLocalRing (MvPowerSeries (Fin 2) W ⧸ Ideal.span {C π - h}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {C π - h})) hθ
  haveI : IsLocalHom (Ideal.Quotient.mk (Ideal.span {C π - h})) := hθ.isLocalHom _
  obtain ⟨u, hu⟩ := hθ (e uF)
  have huunit : IsUnit u := IsLocalHom.map_nonunit u (by rw [hu]; exact huF.map e)

  have hθD : e (x₀ * x₁ ^ q - x₀ ^ q * x₁) =
      Ideal.Quotient.mk (Ideal.span {C π - h}) (DrinfeldCurve.LocalChart.drinfeldForm q W) := by
    simp only [DrinfeldCurve.LocalChart.drinfeldForm, map_sub, map_mul, map_pow, hex₀, hex₁]
  have hθf : Ideal.Quotient.mk (Ideal.span {C π - h}) (DrinfeldCurve.LocalChart.drinfeldForm q W + r) = e F := by
    rw [map_add, hr, map_sub, hθD]; ring
  have hrel : C π - (DrinfeldCurve.LocalChart.drinfeldForm q W + r) * u ∈ Ideal.span {C π - h} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hθf, hu, ← heg, hπF, map_mul]
    ring
  obtain ⟨m, hm⟩ := Ideal.mem_span_singleton'.mp hrel

  have hcf : constantCoeff (DrinfeldCurve.LocalChart.drinfeldForm q W + r) = 0 := by
    rw [map_add, constantCoeff_drinfeldForm, constantCoeff_eq_zero_of_mem_span_X_pow hq2 hrJ, add_zero]
  have hcm : constantCoeff m = 1 := by
    have hc := congrArg constantCoeff hm
    simp only [map_mul, map_sub, constantCoeff_C, hh0, hcf, sub_zero, zero_mul] at hc

    exact mul_right_cancel₀ hπ0 (hc.trans (one_mul π).symm)
  have hmunit : IsUnit m := by rw [isUnit_iff_constantCoeff, hcm]; exact isUnit_one
  have hIeq : Ideal.span {C π - h} =
      Ideal.span {C π * 1 - (DrinfeldCurve.LocalChart.drinfeldForm q W + r) * u} := by
    rw [mul_one, ← hm]
    exact (Ideal.span_singleton_mul_left_unit hmunit _).symm
  refine ⟨DrinfeldCurve.LocalChart.drinfeldForm q W + r, u, 1, huunit, isUnit_one, by simpa using hrJ,
    e.toRingEquiv.trans (Ideal.quotEquivOfEq hIeq), ?_, ?_, ?_⟩
  · intro w
    simp only [RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv, heg,
      Ideal.quotEquivOfEq_mk]
  · simp only [RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv, hex₀,
      Ideal.quotEquivOfEq_mk]
  · simp only [RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv, hex₁,
      Ideal.quotEquivOfEq_mk]

end S_IsRegularLocalRing_exists_ringEquiv_mvPowerSeries_quotient_drinfeldForm_of_eq_mul
end P2MW
export P2MW.S_IsRegularLocalRing_exists_ringEquiv_mvPowerSeries_quotient_drinfeldForm_of_eq_mul (solution)
