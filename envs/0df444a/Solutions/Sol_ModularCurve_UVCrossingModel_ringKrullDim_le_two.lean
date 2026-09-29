-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.ringKrullDim_le_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/ccd37277-f0c3-5c66-93af-d8d111280461

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete
import Theorems.Thm_ModularCurve_UVCrossingModel_isNoetherianRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_ringKrullDim_le_two

set_option maxHeartbeats 800000
set_option autoImplicit false

universe u

namespace P1Arch
open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

section Dim
variable {W : Type u} [CommRing W]

theorem exists_eq_C_add_X_mul_add_X_mul (F : MvPowerSeries (Fin 2) W) :
    ∃ G H : MvPowerSeries (Fin 2) W,
      F = MvPowerSeries.C (MvPowerSeries.constantCoeff F) + MvPowerSeries.X 0 * G + MvPowerSeries.X 1 * H := by
  classical
  let F₁ : MvPowerSeries (Fin 2) W := fun d => if d 0 = 0 then 0 else MvPowerSeries.coeff d F
  let F₂ : MvPowerSeries (Fin 2) W := fun d => if d 0 = 0 ∧ d ≠ 0 then MvPowerSeries.coeff d F else 0
  have h1 : MvPowerSeries.X (0 : Fin 2) ∣ F₁ := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm
    change (if m 0 = 0 then 0 else MvPowerSeries.coeff m F) = 0
    rw [if_pos hm]
  have h2 : MvPowerSeries.X (1 : Fin 2) ∣ F₂ := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm
    change (if m 0 = 0 ∧ m ≠ 0 then MvPowerSeries.coeff m F else 0) = 0
    rw [if_neg]
    rintro ⟨h0, hne⟩
    apply hne
    ext i
    fin_cases i
    · exact h0
    · exact hm
  obtain ⟨G, hG⟩ := h1
  obtain ⟨H, hH⟩ := h2
  refine ⟨G, H, ?_⟩
  rw [← hG, ← hH]
  ext d
  simp only [map_add, MvPowerSeries.coeff_C]
  change _ = _ + (if d 0 = 0 then 0 else MvPowerSeries.coeff d F) + (if d 0 = 0 ∧ d ≠ 0 then MvPowerSeries.coeff d F else 0)
  by_cases hd : d = 0
  · subst hd
    simp
  · rw [if_neg hd]
    by_cases h0 : d 0 = 0
    · rw [if_pos h0, if_pos ⟨h0, hd⟩]; ring
    · rw [if_neg h0, if_neg (fun h => h0 h.1)]; ring

variable [IsDomain W] [IsDiscreteValuationRing W]

noncomputable def residueMap (π : W) (E : ℕ) (hE : 1 ≤ E) : UVCrossingModel W (π ^ E) →+* W ⧸ Ideal.span {π} :=
  Ideal.Quotient.lift (uvCrossingIdeal W (π ^ E))
    ((Ideal.Quotient.mk (Ideal.span {π})).comp MvPowerSeries.constantCoeff) (by
      intro F hF
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hF
      · rintro _ ⟨rfl⟩
        simp only [RingHom.comp_apply, map_sub, map_mul, MvPowerSeries.constantCoeff_X, MvPowerSeries.constantCoeff_C]
        rw [map_zero, zero_mul, zero_sub, neg_eq_zero, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_singleton π)) E hE
      · exact map_zero _
      · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
      · intro a x _ hx; rw [smul_eq_mul, map_mul, hx, mul_zero])

theorem residueMap_mk (π : W) (E : ℕ) (hE : 1 ≤ E) (F : MvPowerSeries (Fin 2) W) :
    residueMap π E hE (mk (π ^ E) F) = Ideal.Quotient.mk (Ideal.span {π}) (MvPowerSeries.constantCoeff F) := rfl

theorem not_isUnit_of_residueMap_eq_zero (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (x : UVCrossingModel W (π ^ E)) (hx : residueMap π E hE x = 0) : ¬ IsUnit x := by
  intro hu
  have hmax : (Ideal.span {π} : Ideal W).IsMaximal := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ]; exact IsLocalRing.maximalIdeal.isMaximal W
  haveI : Nontrivial (W ⧸ Ideal.span {π}) := Ideal.Quotient.nontrivial_iff.mpr hmax.ne_top
  exact not_isUnit_zero (hx ▸ hu.map (residueMap π E hE))

theorem isUnit_of_not_mem_span (π : W) (hπ : Irreducible π) (E : ℕ) (x : UVCrossingModel W (π ^ E))
    (hx : x ∉ Ideal.span {const (π ^ E) π, U (π ^ E), V (π ^ E)}) : IsUnit x := by
  obtain ⟨F, rfl⟩ := mk_surjective (π ^ E) x
  obtain ⟨G, H, hF⟩ := exists_eq_C_add_X_mul_add_X_mul F
  by_cases hc : IsUnit (MvPowerSeries.constantCoeff F)
  · exact (MvPowerSeries.isUnit_iff_constantCoeff.mpr hc).map _
  · exfalso
    apply hx
    have hmem : MvPowerSeries.constantCoeff F ∈ maximalIdeal W := (IsLocalRing.mem_maximalIdeal _).mpr hc
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ, Ideal.mem_span_singleton] at hmem
    obtain ⟨c, hc'⟩ := hmem
    rw [hF, hc', map_add, map_add, map_mul, map_mul, map_mul, map_mul]
    refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
    · exact Ideal.mul_mem_right _ _
        (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))

end Dim
end P1Arch

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing in
theorem solution
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E) :
    ringKrullDim (UVCrossingModel W (π ^ E)) ≤ 2 := by
  classical
  obtain ⟨-, hloc, -⟩ := ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete π hπ E hE
  haveI := hloc
  haveI : IsNoetherianRing (UVCrossingModel W (π ^ E)) := ModularCurve.UVCrossingModel.isNoetherianRing (π ^ E)
  set S : UVCrossingModel W (π ^ E) := U (π ^ E) + V (π ^ E) with hS
  set I : Ideal (UVCrossingModel W (π ^ E)) := Ideal.span {const (π ^ E) π, S} with hI

  have hres0 : ∀ y ∈ ({const (π ^ E) π, S, U (π ^ E), V (π ^ E)} : Set (UVCrossingModel W (π ^ E))),
      P1Arch.residueMap π E hE y = 0 := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · change P1Arch.residueMap π E hE (mk (π ^ E) (MvPowerSeries.C π)) = 0
      rw [P1Arch.residueMap_mk, MvPowerSeries.constantCoeff_C, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (Set.mem_singleton π)
    · change P1Arch.residueMap π E hE (mk (π ^ E) (MvPowerSeries.X 0) + mk (π ^ E) (MvPowerSeries.X 1)) = 0
      rw [map_add, P1Arch.residueMap_mk, P1Arch.residueMap_mk, MvPowerSeries.constantCoeff_X, MvPowerSeries.constantCoeff_X,
        map_zero, add_zero]
    · change P1Arch.residueMap π E hE (mk (π ^ E) (MvPowerSeries.X 0)) = 0
      rw [P1Arch.residueMap_mk, MvPowerSeries.constantCoeff_X, map_zero]
    · change P1Arch.residueMap π E hE (mk (π ^ E) (MvPowerSeries.X 1)) = 0
      rw [P1Arch.residueMap_mk, MvPowerSeries.constantCoeff_X, map_zero]
  have hmemM : ∀ y ∈ ({const (π ^ E) π, S, U (π ^ E), V (π ^ E)} : Set (UVCrossingModel W (π ^ E))),
      y ∈ maximalIdeal (UVCrossingModel W (π ^ E)) :=
    fun y hy => (IsLocalRing.mem_maximalIdeal y).mpr (P1Arch.not_isUnit_of_residueMap_eq_zero π hπ E hE y (hres0 y hy))
  have hIM : I ≤ maximalIdeal (UVCrossingModel W (π ^ E)) := by
    rw [hI, Ideal.span_le]
    intro y hy
    exact hmemM y (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢; tauto)

  have hUU : U (π ^ E) * U (π ^ E) ∈ I := by
    have hUV : U (π ^ E) * V (π ^ E) = const (π ^ E) π ^ E := by
      rw [← constHom_apply, ← map_pow, constHom_apply]
      change mk (π ^ E) (MvPowerSeries.X 0) * mk (π ^ E) (MvPowerSeries.X 1) = mk (π ^ E) (MvPowerSeries.C (π ^ E))
      rw [← map_mul]
      change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
      rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      exact Ideal.subset_span (Set.mem_singleton _)
    have h : U (π ^ E) * U (π ^ E) = U (π ^ E) * S - const (π ^ E) π ^ E := by rw [hS, mul_add, hUV]; ring
    rw [h]
    refine Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))) ?_
    exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (by simp)) E hE
  have hprime : ∀ P : Ideal (UVCrossingModel W (π ^ E)), P.IsPrime → I ≤ P → P = maximalIdeal _ := by
    intro P hP hIP
    have hU : U (π ^ E) ∈ P := (hP.mem_or_mem (hIP hUU)).elim id id
    have hV : V (π ^ E) ∈ P := by
      have : V (π ^ E) = S - U (π ^ E) := by rw [hS]; ring
      rw [this]
      exact Ideal.sub_mem _ (hIP (Ideal.subset_span (by simp))) hU
    have hc : const (π ^ E) π ∈ P := hIP (Ideal.subset_span (by simp))

    have hMP : maximalIdeal (UVCrossingModel W (π ^ E)) ≤ P := by
      intro y hy
      by_contra hyP
      have hyn : y ∉ Ideal.span {const (π ^ E) π, U (π ^ E), V (π ^ E)} := by
        intro hmem
        apply hyP
        have : Ideal.span {const (π ^ E) π, U (π ^ E), V (π ^ E)} ≤ P := by
          rw [Ideal.span_le]
          intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with rfl | rfl | rfl
          exacts [hc, hU, hV]
        exact this hmem
      exact (IsLocalRing.mem_maximalIdeal y).mp hy (P1Arch.isUnit_of_not_mem_span π hπ E y hyn)
    exact ((IsLocalRing.maximalIdeal.isMaximal _).eq_of_le hP.ne_top hMP).symm
  have hmin : maximalIdeal (UVCrossingModel W (π ^ E)) ∈ I.minimalPrimes := by
    refine ⟨⟨IsLocalRing.maximalIdeal.isMaximal _ |>.isPrime, hIM⟩, ?_⟩
    rintro P ⟨hP, hIP⟩ -
    exact (hprime P hP hIP).symm.le

  have hh := Ideal.height_le_spanRank_toENat_of_mem_minimalPrimes I _ hmin
  have hcard : Cardinal.toENat (Submodule.spanRank I) ≤ 2 := by
    have h1 := Submodule.spanRank_span_le_card (R := UVCrossingModel W (π ^ E)) (M := UVCrossingModel W (π ^ E))
      ({const (π ^ E) π, S} : Set (UVCrossingModel W (π ^ E)))
    have h2 : Cardinal.mk (↥({const (π ^ E) π, S} : Set (UVCrossingModel W (π ^ E)))) ≤ 2 := by
      calc Cardinal.mk (↥({const (π ^ E) π, S} : Set (UVCrossingModel W (π ^ E))))
          ≤ Cardinal.mk (↥({S} : Set (UVCrossingModel W (π ^ E)))) + 1 := Cardinal.mk_insert_le
        _ = 1 + 1 := by rw [Cardinal.mk_singleton]
        _ = 2 := by norm_num
    exact Cardinal.toENat_le_ofNat.mpr (h1.trans h2)
  have hheight : (maximalIdeal (UVCrossingModel W (π ^ E))).height ≤ 2 := hh.trans hcard
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  exact (WithBot.coe_le rfl).mpr hheight

end S_ModularCurve_UVCrossingModel_ringKrullDim_le_two
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_ringKrullDim_le_two (solution)
