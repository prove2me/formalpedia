-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.exists_pow_map_germ_mem_span_of_mem_asIdeal_of_ringEquiv_adicCompletion_stalk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/705fa330-14bb-573e-a4fb-502091949e0e

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_DrinfeldCurve_LocalChart
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_atPrime_of_iotaFin_apply_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_pow_map_germ_mem_span_of_mem_asIdeal_of_ringEquiv_adicCompletion_stalk

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

namespace A4cCentreRadical

theorem mem_span_X_of_constantCoeff_eq_zero {W : Type} [CommRing W]
    (p : MvPowerSeries (Fin 2) W) (hp : MvPowerSeries.constantCoeff p = 0) :
    p ∈ Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1} := by
  classical

  let p₁ : MvPowerSeries (Fin 2) W := fun m => if m 0 = 0 then MvPowerSeries.coeff m p else 0
  have hp₁ : ∀ m : Fin 2 →₀ ℕ, MvPowerSeries.coeff m p₁ = if m 0 = 0 then MvPowerSeries.coeff m p else 0 :=
    fun m => rfl
  have h1 : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) W) ∣ p₁ := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm
    rw [hp₁]
    split_ifs with h0
    · have hm0 : m = 0 := by
        ext i
        fin_cases i
        · simpa using h0
        · simpa using hm
      subst hm0
      simpa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using hp
    · rfl
  have h0 : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) ∣ (p - p₁) := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm
    rw [map_sub, hp₁, if_pos hm, sub_self]
  have hsplit : p = (p - p₁) + p₁ := by ring
  rw [hsplit]
  refine Ideal.add_mem _ ?_ ?_
  · obtain ⟨c, hc⟩ := h0
    rw [hc]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · obtain ⟨c, hc⟩ := h1
    rw [hc]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

theorem mem_span_of_not_isUnit {W : Type} [CommRing W] [IsLocalRing W] (ϖ : W)
    (hϖ : maximalIdeal W = Ideal.span {ϖ}) (I : Ideal (MvPowerSeries (Fin 2) W))
    (x : MvPowerSeries (Fin 2) W ⧸ I) (hx : ¬ IsUnit x) :
    x ∈ Ideal.span {Ideal.Quotient.mk I (MvPowerSeries.C ϖ),
      Ideal.Quotient.mk I (MvPowerSeries.X 0), Ideal.Quotient.mk I (MvPowerSeries.X 1)} := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hp : ¬ IsUnit p := fun h => hx (h.map _)
  rw [MvPowerSeries.isUnit_iff_constantCoeff] at hp
  have hc : MvPowerSeries.constantCoeff p ∈ maximalIdeal W :=
    (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hp)
  rw [hϖ, Ideal.mem_span_singleton'] at hc
  obtain ⟨c, hc⟩ := hc
  have hr : p - MvPowerSeries.C (c * ϖ) ∈
      Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1} :=
    mem_span_X_of_constantCoeff_eq_zero _ (by simp [hc])
  have hsplit : p = MvPowerSeries.C c * MvPowerSeries.C ϖ + (p - MvPowerSeries.C (c * ϖ)) := by
    rw [← map_mul]; ring
  rw [hsplit, map_add, map_mul]
  refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))) ?_
  have him := Ideal.mem_map_of_mem (Ideal.Quotient.mk I) hr
  rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton] at him
  refine (Ideal.span_mono ?_) him
  intro t ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht ⊢
  tauto

theorem pow_mem_of_mem_span {S : Type} [CommRing S] (g t₀ t₁ x : S) (N : Ideal S) (n : ℕ)
    (hg : g ^ n ∈ N) (h0 : t₀ ∈ N) (h1 : t₁ ∈ N) (hx : x ∈ Ideal.span {g, t₀, t₁}) :
    x ^ n ∈ N := by
  rw [← Ideal.Quotient.eq_zero_iff_mem] at hg h0 h1 ⊢
  have hx' := Ideal.mem_map_of_mem (Ideal.Quotient.mk N) hx
  rw [Ideal.map_span, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton, h0, h1] at hx'
  have hx'' : Ideal.Quotient.mk N x ∈ Ideal.span {Ideal.Quotient.mk N g} := by
    refine (Ideal.span_le.mpr ?_) hx'
    intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl
    · exact Ideal.subset_span (by simp)
    · exact zero_mem _
    · exact zero_mem _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hx''
  rw [map_pow, ← hc, mul_pow, ← map_pow, hg, mul_zero]

theorem not_isUnit_equiv_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (e : S ≃+* T) (f : R →+* S) (r : R) (h : ¬ IsUnit (f r)) :
    ¬ IsUnit (((e : S →+* T).comp f) r) := by
  intro hu
  apply h
  simpa using hu.map e.symm

theorem not_isUnit_algebraMap_adicCompletion {R : Type*} [CommRing R] (I : Ideal R) (hI : I ≠ ⊤)
    (r : R) (hr : r ∈ I) : ¬ IsUnit (algebraMap R (AdicCompletion I R) r) := by
  intro hu
  have hu2 := hu.map (AdicCompletion.evalOneₐ I)
  rw [AlgHom.commutes, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hr] at hu2
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  exact not_isUnit_zero hu2

end A4cCentreRadical

open A4cCentreRadical in
theorem solution
    (q : ℕ) [Fact q.Prime]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})
    (ϖt : A) (hϖt : ∃ u : A, IsUnit u ∧ ϖt ^ (q ^ 2 - 1) = (q : A) * u)
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
    (y' : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
    (hy' : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y' = z)
    (W₁ : Type) [CommRing W₁] [IsDomain W₁] [IsDiscreteValuationRing W₁]
    [IsAdicComplete (IsLocalRing.maximalIdeal W₁) W₁] (σ₁ : A →+* W₁)
    (hσ₁ : IsLocalRing.maximalIdeal W₁ = Ideal.span {σ₁ ϖ})
    (f₁ u₁ v₁ : MvPowerSeries (Fin 2) W₁)
    (hf₁ : f₁ - DrinfeldCurve.LocalChart.drinfeldForm q W₁ ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ (q + 2))
    (e₁ : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
      MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁}) :
        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let mkS : MvPowerSeries (Fin 2) W₁ →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)
        ∃ n : ℕ, 1 ≤ n ∧ ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), a ∈ y'.asIdeal →
          (((e₁ : CMP →+* S).comp (toC.comp germY)) a) ^ n ∈
            Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} := by
  intro STK CMP toC S mkS germY

  have hq0 : (q : A) ≠ 0 := by
    intro h
    have hL : (q : L) = 0 := by
      have := congrArg (algebraMap A L) h
      simpa using this
    exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) hL
  have hϖt0 : ϖt ≠ 0 := by
    rintro rfl
    obtain ⟨u, hu, h⟩ := hϖt
    have hpos : q ^ 2 - 1 ≠ 0 := by
      have h2 := (Fact.out : q.Prime).two_le
      have : 2 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left h2 2
      omega
    rw [zero_pow hpos] at h
    exact hq0 ((hu.mul_left_eq_zero).mp h.symm)
  have hϖirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ
  have hassoc := IsDiscreteValuationRing.associated_pow_irreducible hϖt0 hϖirr
  obtain ⟨n, w, hw⟩ := hassoc
  have hϖt_mem : ϖt ∈ maximalIdeal A := by
    obtain ⟨u, hu, h⟩ := hϖt
    have hpow : ϖt ^ (q ^ 2 - 1) ∈ maximalIdeal A := by
      rw [h]; exact Ideal.mul_mem_right _ _ hAq
    exact Ideal.IsPrime.mem_of_pow_mem inferInstance _ hpow
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      subst h
      rw [pow_zero] at hw
      exact (IsLocalRing.mem_maximalIdeal _).mp hϖt_mem (IsUnit.of_mul_eq_one _ hw)
    · exact h
  refine ⟨n, hn1, fun a ha => ?_⟩

  have hdict :=
    AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_atPrime_of_iotaFin_apply_eq
      A (↥K) j z y' hy'
  obtain ⟨eL, -, heL⟩ := hdict
  have hgerm : germY a ∈ maximalIdeal STK := by
    have h1 : eL.hom.hom (germY a) ∈ maximalIdeal (Localization.AtPrime y'.asIdeal) := by
      have h := heL a
      have h' : eL.hom.hom (germY a) = algebraMap _ (Localization.AtPrime y'.asIdeal) a := h
      rw [h']
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ y'.asIdeal a).mpr ha
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h1 ⊢
    exact fun hu => h1 (hu.map eL.hom.hom)

  have hxnu : ¬ IsUnit (((e₁ : CMP →+* S).comp (toC.comp germY)) a) := by
    refine not_isUnit_equiv_comp e₁ (toC.comp germY) a ?_
    have hne : maximalIdeal STK ≠ ⊤ := (maximalIdeal.isMaximal STK).ne_top
    have := not_isUnit_algebraMap_adicCompletion (maximalIdeal STK) hne (germY a)
      ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hgerm))
    exact this

  have hxM := mem_span_of_not_isUnit (σ₁ ϖ) hσ₁ _ _ hxnu

  refine pow_mem_of_mem_span (mkS (MvPowerSeries.C (σ₁ ϖ))) (mkS (MvPowerSeries.X 0))
    (mkS (MvPowerSeries.X 1)) _ _ n ?_ (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp)) hxM
  rw [← map_pow, ← map_pow, ← map_pow, ← hw, map_mul, map_mul, map_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

end S_ModularCurve_FullLevel_AuxLevel_exists_pow_map_germ_mem_span_of_mem_asIdeal_of_ringEquiv_adicCompletion_stalk
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_pow_map_germ_mem_span_of_mem_asIdeal_of_ringEquiv_adicCompletion_stalk (solution)
