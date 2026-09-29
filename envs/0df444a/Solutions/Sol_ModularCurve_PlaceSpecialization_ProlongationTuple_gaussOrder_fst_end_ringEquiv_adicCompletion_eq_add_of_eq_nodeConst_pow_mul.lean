-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.gaussOrder_fst_end_ringEquiv_adicCompletion_eq_add_of_eq_nodeConst_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/c1dd4449-ac62-5c15-aa47-17b579f6316a

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Theorems.Thm_ModularCurve_UVCrossingModel_gaussOrder_mul
import Theorems.Thm_ModularCurve_UVCrossingModel_gaussOrder_scaled_eq_repGaussOrder_normalForm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_gaussOrder_fst_end_ringEquiv_adicCompletion_eq_add_of_eq_nodeConst_pow_mul

set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace AnnulusEVD

section Model

variable {W : Type*} [CommRing W]

theorem coeff_X_mul_X_mul_single (G : MvPowerSeries (Fin 2) W) (s : Fin 2) (j : ℕ) :
    MvPowerSeries.coeff (Finsupp.single s j)
      ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 * G) = 0 := by
  classical
  have hXX : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 =
      MvPowerSeries.monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 := by
    rw [MvPowerSeries.X, MvPowerSeries.X, MvPowerSeries.monomial_mul_monomial, one_mul]
  rw [hXX, MvPowerSeries.coeff_monomial_mul, if_neg]
  intro h
  fin_cases s
  · have := h 1
    simp at this
  · have := h 0
    simp at this

theorem coeff_axis_of_congr (π ϖ : W) (e : ℕ) (he : 1 ≤ e) (hπ : π = ϖ ^ e) (s s' : Fin 2) (hss' : s ≠ s')
    (F G : MvPowerSeries (Fin 2) W) (n : ℕ)
    (h : mk π F - mk π G * mk π (MvPowerSeries.X s) ^ n ∈
      Ideal.span {mk π (MvPowerSeries.C ϖ), mk π (MvPowerSeries.X s')}) (j : ℕ) :
    ∃ z : W, MvPowerSeries.coeff (Finsupp.single s j) F =
      (if n ≤ j then MvPowerSeries.coeff (Finsupp.single s (j - n)) G else 0) + ϖ * z := by
  classical
  obtain ⟨r, t, hrt⟩ := Ideal.mem_span_pair.mp h
  obtain ⟨Rr, rfl⟩ := mk_surjective π r
  obtain ⟨T, rfl⟩ := mk_surjective π t
  have hmem : F - G * MvPowerSeries.X s ^ n - (Rr * MvPowerSeries.C ϖ + T * MvPowerSeries.X s') ∈
      uvCrossingIdeal W π := by
    rw [← Ideal.Quotient.eq]
    change mk π _ = mk π _
    rw [map_sub, map_mul, map_pow, map_add, map_mul, map_mul, hrt]
  rw [Ideal.mem_span_singleton'] at hmem
  obtain ⟨Q, hQ⟩ := hmem
  have hc := congrArg (MvPowerSeries.coeff (Finsupp.single s j)) hQ
  rw [mul_comm, sub_mul, map_sub, coeff_X_mul_X_mul_single, MvPowerSeries.coeff_C_mul, zero_sub,
    map_sub, map_sub, map_add, MvPowerSeries.coeff_mul_C, MvPowerSeries.X_pow_eq,
    MvPowerSeries.coeff_mul_monomial, MvPowerSeries.X, MvPowerSeries.coeff_mul_monomial] at hc
  have hle : Finsupp.single s n ≤ Finsupp.single s j ↔ n ≤ j := by
    constructor
    · intro h'
      simpa using h' s
    · intro h' i
      by_cases hi : s = i
      · subst hi; simpa using h'
      · simp [hi]
  have hsub : Finsupp.single s j - Finsupp.single s n = Finsupp.single s (j - n) := by
    ext i
    simp only [Finsupp.tsub_apply, Finsupp.single_apply]
    split_ifs <;> simp
  have hle' : ¬ Finsupp.single s' 1 ≤ Finsupp.single s j := by
    intro h'
    have := h' s'
    simp [hss'] at this
  rw [if_neg hle', add_zero, hsub, mul_one] at hc
  simp only [hle] at hc
  have hπ' : π = ϖ * ϖ ^ (e - 1) := by rw [hπ, ← pow_succ', Nat.sub_add_cancel he]
  rw [hπ'] at hc
  exact ⟨MvPowerSeries.coeff (Finsupp.single s j) Rr - ϖ ^ (e - 1) * MvPowerSeries.coeff (Finsupp.single s j) Q,
    by linear_combination -hc⟩

theorem constantCoeff_mul_eq_of_isUnit_mk (π : W) (G : MvPowerSeries (Fin 2) W) (hG : IsUnit (mk π G)) :
    ∃ D Q : MvPowerSeries (Fin 2) W,
      MvPowerSeries.constantCoeff G * MvPowerSeries.constantCoeff D = 1 - π * MvPowerSeries.constantCoeff Q := by
  obtain ⟨δ, hδ⟩ := hG.exists_right_inv
  obtain ⟨D, rfl⟩ := mk_surjective π δ
  have hmem : G * D - 1 ∈ uvCrossingIdeal W π := by
    rw [← Ideal.Quotient.eq]
    change mk π _ = mk π _
    rw [map_mul, map_one, hδ]
  rw [Ideal.mem_span_singleton'] at hmem
  obtain ⟨Q, hQ⟩ := hmem
  have hc := congrArg MvPowerSeries.constantCoeff hQ
  simp only [map_mul, map_sub, map_one, MvPowerSeries.constantCoeff_X, MvPowerSeries.constantCoeff_C,
    mul_zero, zero_sub] at hc
  exact ⟨D, Q, by linear_combination -hc⟩

end Model

section DVR

variable {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

theorem one_le_addVal_of_eq_mul {ϖ : W} (hϖ : Irreducible ϖ) {c z : W} (h : c = ϖ * z) :
    1 ≤ IsDiscreteValuationRing.addVal W c := by
  rw [h, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_uniformizer hϖ]
  exact le_self_add

theorem addVal_eq_zero_of_isUnit {ϖ : W} (hϖ : Irreducible ϖ) {c : W} (hc : IsUnit c) :
    IsDiscreteValuationRing.addVal W c = 0 := by
  obtain ⟨u, rfl⟩ := hc
  have := IsDiscreteValuationRing.addVal_def (u : W) u hϖ 0 (by simp)
  simpa using this

theorem isUnit_add_mul {ϖ : W} (hϖ : Irreducible ϖ) {g z : W} (hg : IsUnit g) : IsUnit (g + ϖ * z) := by
  by_contra h
  have h1 : g + ϖ * z ∈ maximalIdeal W := (mem_maximalIdeal _).mpr h
  have h2 : ϖ * z ∈ maximalIdeal W := Ideal.mul_mem_right _ _ ((mem_maximalIdeal _).mpr hϖ.not_isUnit)
  have h3 : g ∈ maximalIdeal W := by simpa using sub_mem h1 h2
  exact (mem_maximalIdeal _).mp h3 hg

theorem isUnit_constantCoeff_of_isUnit_mk {ϖ : W} (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (G : MvPowerSeries (Fin 2) W) (hG : IsUnit (mk (ϖ ^ e) G)) : IsUnit (MvPowerSeries.constantCoeff G) := by
  obtain ⟨D, Q, hGD⟩ := constantCoeff_mul_eq_of_isUnit_mk (ϖ ^ e) G hG
  have hu : IsUnit (1 - ϖ ^ e * MvPowerSeries.constantCoeff Q) := by
    apply isUnit_one_sub_self_of_mem_nonunits
    rw [← Nat.sub_add_cancel he, pow_succ', mul_assoc]
    exact mul_mem_nonunits_left hϖ.not_isUnit
  rw [← hGD] at hu
  exact isUnit_of_mul_isUnit_left hu

theorem addVal_coeff_axis_eq_zero {ϖ : W} (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (s s' : Fin 2) (hss' : s ≠ s')
    (F G : MvPowerSeries (Fin 2) W) (hG : IsUnit (mk (ϖ ^ e) G)) (n : ℕ)
    (h : mk (ϖ ^ e) F - mk (ϖ ^ e) G * mk (ϖ ^ e) (MvPowerSeries.X s) ^ n ∈
      Ideal.span {mk (ϖ ^ e) (MvPowerSeries.C ϖ), mk (ϖ ^ e) (MvPowerSeries.X s')}) :
    IsDiscreteValuationRing.addVal W (MvPowerSeries.coeff (Finsupp.single s n) F) = 0 := by
  obtain ⟨z, hz⟩ := coeff_axis_of_congr (ϖ ^ e) ϖ e he rfl s s' hss' F G n h n
  rw [if_pos le_rfl, Nat.sub_self, Finsupp.single_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at hz
  rw [hz]
  exact addVal_eq_zero_of_isUnit hϖ (isUnit_add_mul hϖ (isUnit_constantCoeff_of_isUnit_mk hϖ e he G hG))

theorem gaussOrder_fst_end_eq_zero {ϖ : W} (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x γ : UVCrossingModel W (ϖ ^ e)) (hγ : IsUnit γ) (n : ℕ)
    (hxγ : x - γ * V (ϖ ^ e) ^ n ∈ Ideal.span {const (ϖ ^ e) ϖ, U (ϖ ^ e)}) :
    gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e e x = 0 := by
  obtain ⟨G, rfl⟩ := mk_surjective (ϖ ^ e) γ
  refine le_antisymm ?_ zero_le
  rw [gaussOrder_le_iff]
  intro F hF
  refine le_trans (repGaussOrder_le _ _ _ F (Finsupp.single 1 n)) ?_
  have hw : annulusWeight e e (Finsupp.single (1 : Fin 2) n) = 0 := by simp [annulusWeight]
  rw [hw, addVal_coeff_axis_eq_zero hϖ e he 1 0 (by decide) F G hγ n (by rw [hF]; exact hxγ)]
  simp

theorem gaussOrder_snd_end_eq_zero {ϖ : W} (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x γ : UVCrossingModel W (ϖ ^ e)) (hγ : IsUnit γ) (m : ℕ)
    (hxγ : x - γ * U (ϖ ^ e) ^ m ∈ Ideal.span {const (ϖ ^ e) ϖ, V (ϖ ^ e)}) :
    gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e 0 x = 0 := by
  obtain ⟨G, rfl⟩ := mk_surjective (ϖ ^ e) γ
  refine le_antisymm ?_ zero_le
  rw [gaussOrder_le_iff]
  intro F hF
  refine le_trans (repGaussOrder_le _ _ _ F (Finsupp.single 0 m)) ?_
  have hw : annulusWeight e 0 (Finsupp.single (0 : Fin 2) m) = 0 := by simp [annulusWeight]
  rw [hw, addVal_coeff_axis_eq_zero hϖ e he 0 1 (by decide) F G hγ m (by rw [hF]; exact hxγ)]
  simp

theorem gaussOrder_const [IsAdicComplete (maximalIdeal W) W] (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (c : W) (t : ℕ) (ht : t ≤ e) :
    gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e t (const (ϖ ^ e) c) =
      IsDiscreteValuationRing.addVal W c := by
  classical
  have hnf : inU (PowerSeries.C c) + inV (0 : PowerSeries W) = MvPowerSeries.C c := by
    ext d
    rw [map_add, coeff_inU, coeff_inV, MvPowerSeries.coeff_C, (PowerSeries.coeff (d 1)).map_zero,
      PowerSeries.coeff_C]
    simp only [ite_self, add_zero]
    by_cases hd : d = 0
    · subst hd; simp
    · rw [if_neg hd]
      have hne : ¬ (d 1 = 0 ∧ d 0 = 0) := by
        rintro ⟨h1, h0⟩; apply hd; ext i; fin_cases i <;> simp [h0, h1]
      by_cases h1 : d 1 = 0
      · rw [if_pos h1, if_neg (fun h0 => hne ⟨h1, h0⟩)]
      · rw [if_neg h1]
  have hA := gaussOrder_scaled_eq_repGaussOrder_normalForm ϖ hϖ e he 1 le_rfl (const (ϖ ^ e) c)
    (PowerSeries.C c, 0) (by simp) (by rw [hnf]; rfl) t (by simpa using ht)
  simp only [Nat.cast_one, one_mul, Nat.one_mul] at hA
  rw [hA, hnf]

  apply le_antisymm
  · refine le_trans (repGaussOrder_le _ _ _ _ 0) ?_
    simp [annulusWeight, MvPowerSeries.coeff_C]
  · rw [le_repGaussOrder_iff]
    intro d
    by_cases hd : d = 0
    · subst hd; simp [annulusWeight, MvPowerSeries.coeff_C]
    · rw [MvPowerSeries.coeff_C, if_neg hd, IsDiscreteValuationRing.addVal_zero, top_add]
      exact le_top

theorem gaussOrder_const_pow [IsAdicComplete (maximalIdeal W) W] (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (t : ℕ) (ht : t ≤ e) (d : ℕ) :
    gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e t (const (ϖ ^ e) ϖ ^ d) = d := by
  induction d with
  | zero =>
      rw [pow_zero, show (1 : UVCrossingModel W (ϖ ^ e)) = const (ϖ ^ e) 1 by
        rw [← constHom_apply, map_one], gaussOrder_const ϖ hϖ e he 1 t ht,
        IsDiscreteValuationRing.addVal_one, Nat.cast_zero]
  | succ d ih =>
      rw [pow_succ, gaussOrder_mul ϖ hϖ e t he ht, ih, gaussOrder_const ϖ hϖ e he ϖ t ht,
        IsDiscreteValuationRing.addVal_uniformizer hϖ, Nat.cast_succ]

theorem model_fst [IsAdicComplete (maximalIdeal W) W] {ϖ : W} (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (Y Z : UVCrossingModel W (ϖ ^ e)) (d : ℕ) (γ : UVCrossingModel W (ϖ ^ e)) (hγ : IsUnit γ) (n : ℕ)
    (hY : Y - γ * V (ϖ ^ e) ^ n ∈ Ideal.span {const (ϖ ^ e) ϖ, U (ϖ ^ e)}) :
    gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e e (const (ϖ ^ e) ϖ ^ d * Y * Z) =
      d + gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e e Z := by
  rw [gaussOrder_mul ϖ hϖ e e he le_rfl, gaussOrder_mul ϖ hϖ e e he le_rfl,
    gaussOrder_const_pow ϖ hϖ e he e le_rfl d, gaussOrder_fst_end_eq_zero hϖ e he Y γ hγ n hY, add_zero]

theorem model_snd [IsAdicComplete (maximalIdeal W) W] {ϖ : W} (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (Y Z : UVCrossingModel W (ϖ ^ e)) (d : ℕ) (γ : UVCrossingModel W (ϖ ^ e)) (hγ : IsUnit γ) (m : ℕ)
    (hY : Y - γ * U (ϖ ^ e) ^ m ∈ Ideal.span {const (ϖ ^ e) ϖ, V (ϖ ^ e)}) :
    gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e 0 (const (ϖ ^ e) ϖ ^ d * Y * Z) =
      d + gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e 0 Z := by
  rw [gaussOrder_mul ϖ hϖ e 0 he (Nat.zero_le _), gaussOrder_mul ϖ hϖ e 0 he (Nat.zero_le _),
    gaussOrder_const_pow ϖ hϖ e he 0 (Nat.zero_le _) d, gaussOrder_snd_end_eq_zero hϖ e he Y γ hγ m hY, add_zero]

end DVR

end AnnulusEVD

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N))
    [IsLocalRing ↥(R.nodeIntegersOver K w)]
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) (E : ℕ) (hE : 1 ≤ E)
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (ι : AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E))
    (hιϖ : ι (algebraMap _ _ (R.nodeConst K w ϖ)) = const (π ^ E) π)
    (hord : ∀ (f : ↥(R.nodeIntegersOver K w)) (n : ℕ), R.nodeResidue₁ w ⟨f, f.2.1⟩ ≠ 0 →
        w.ord (R.nodeResidue₁ w ⟨f, f.2.1⟩) = (n : ℤ) →
        ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ f) - γ * V (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, U (π ^ E)})
    (x x' u : ↥(R.nodeIntegersOver K w)) (n : ℕ) (hu : R.nodeResidue₁ w ⟨u, u.2.1⟩ ≠ 0)
    (hn : w.ord (R.nodeResidue₁ w ⟨u, u.2.1⟩) = (n : ℤ))
    (d : ℕ) (hrel : x = R.nodeConst K w ϖ ^ d * u * x') :
    gaussOrder (IsDiscreteValuationRing.addVal W) (π ^ E) E E (ι (algebraMap _ _ x)) =
      d + gaussOrder (IsDiscreteValuationRing.addVal W) (π ^ E) E E (ι (algebraMap _ _ x')) := by
  obtain ⟨γ, hγ, hcong⟩ := hord u n hu hn
  subst hrel
  simp only [map_mul, map_pow, hιϖ]
  exact AnnulusEVD.model_fst hπ E hE _ _ d γ hγ n hcong

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_gaussOrder_fst_end_ringEquiv_adicCompletion_eq_add_of_eq_nodeConst_pow_mul
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_gaussOrder_fst_end_ringEquiv_adicCompletion_eq_add_of_eq_nodeConst_pow_mul (solution)
