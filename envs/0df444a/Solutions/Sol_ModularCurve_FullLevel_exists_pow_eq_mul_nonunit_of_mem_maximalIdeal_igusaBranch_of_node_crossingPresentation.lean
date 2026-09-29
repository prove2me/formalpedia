-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_pow_eq_mul_nonunit_of_mem_maximalIdeal_igusaBranch_of_node_crossingPresentation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/b7b5fcf9-8bbb-53c9-8659-0d52edc2ffa5

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_AdicCompletionLocalRing
import Theorems.Thm_Ideal_comap_map_adicCompletion_eq_of_isNoetherianRing
import Theorems.Thm_IsDiscreteValuationRing_adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_pow_eq_mul_nonunit_of_mem_maximalIdeal_igusaBranch_of_node_crossingPresentation

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup ModularCurve.UVCrossingModel
open scoped MatrixGroups

namespace NodePowSol

section Surgery

variable {W : Type*} [CommRing W]

open MvPowerSeries

noncomputable def freePart (s : Fin 2) (f : MvPowerSeries (Fin 2) W) : MvPowerSeries (Fin 2) W :=
  fun m => if m s = 0 then MvPowerSeries.coeff m f else 0

noncomputable def quotPart (s : Fin 2) (f : MvPowerSeries (Fin 2) W) : MvPowerSeries (Fin 2) W :=
  fun m => MvPowerSeries.coeff (m + Finsupp.single s 1) f

theorem coeff_freePart (s : Fin 2) (f : MvPowerSeries (Fin 2) W) (m : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff m (freePart s f) = if m s = 0 then MvPowerSeries.coeff m f else 0 := rfl

theorem coeff_quotPart (s : Fin 2) (f : MvPowerSeries (Fin 2) W) (m : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff m (quotPart s f) = MvPowerSeries.coeff (m + Finsupp.single s 1) f := rfl

theorem coeff_X_mul' (s : Fin 2) (g : MvPowerSeries (Fin 2) W) (m : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff m (MvPowerSeries.X s * g) =
      if m s = 0 then 0 else MvPowerSeries.coeff (m - Finsupp.single s 1) g := by
  rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
  by_cases hm : m s = 0
  · rw [if_pos hm, if_neg]
    intro hle
    have := hle s
    rw [Finsupp.single_eq_same, hm] at this
    omega
  · rw [if_neg hm, if_pos, one_mul]
    intro t
    rw [Finsupp.single_apply]
    split_ifs with hts
    · subst hts; omega
    · exact Nat.zero_le _

theorem eq_X_mul_quotPart_add_freePart (s : Fin 2) (f : MvPowerSeries (Fin 2) W) :
    f = MvPowerSeries.X s * quotPart s f + freePart s f := by
  ext m
  rw [map_add, coeff_X_mul', coeff_freePart, coeff_quotPart]
  by_cases hm : m s = 0
  · rw [if_pos hm, if_pos hm, zero_add]
  · rw [if_neg hm, if_neg hm, add_zero]
    have hm' : m - Finsupp.single s 1 + Finsupp.single s 1 = m := by
      ext t
      rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs with hts
      · subst hts; omega
      · omega
    rw [hm']

theorem freePart_free (s : Fin 2) (f : MvPowerSeries (Fin 2) W) (m : Fin 2 →₀ ℕ) (hm : m s ≠ 0) :
    MvPowerSeries.coeff m (freePart s f) = 0 := by
  rw [coeff_freePart, if_neg hm]

theorem eq_single_one_of_apply_zero_eq_zero (m : Fin 2 →₀ ℕ) (hm : m 0 = 0) :
    m = Finsupp.single 1 (m 1) := by
  ext t
  fin_cases t
  · simpa using hm
  · simp

theorem exists_isUnit_and_sub_X_pow_mul_mem [IsDomain W] [IsDiscreteValuationRing W] {π : W} (hπ : Irreducible π)
    (G : MvPowerSeries (Fin 2) W)
    (hG : G ∉ Ideal.span {MvPowerSeries.C π, (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W)}) :
    ∃ (m : ℕ) (H : MvPowerSeries (Fin 2) W), IsUnit H ∧
      G - MvPowerSeries.X 1 ^ m * H ∈ Ideal.span {MvPowerSeries.C π, (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W)} := by
  classical

  have hdiv : ∀ a : W, ¬ IsUnit a → ∃ c : W, a = π * c := fun a ha => by
    have hmem : a ∈ maximalIdeal W := (mem_maximalIdeal _).mpr ha
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
    exact hmem

  have key : ∃ j : ℕ, IsUnit (MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) j) G) := by
    by_contra hall
    push Not at hall
    apply hG
    have hq : ∀ j : ℕ, ∃ c : W, MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) j) G = π * c :=
      fun j => hdiv _ (hall j)
    choose c hc using hq
    set P : MvPowerSeries (Fin 2) W := fun n => if n 0 = 0 then c (n 1) else 0 with hP
    have hfree : freePart 0 G = MvPowerSeries.C π * P := by
      ext n
      rw [coeff_freePart, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_apply P, hP]
      dsimp only
      split_ifs with h0
      · rw [← hc (n 1), ← eq_single_one_of_apply_zero_eq_zero n h0]
      · rw [mul_zero]
    rw [eq_X_mul_quotPart_add_freePart 0 G, hfree]
    exact add_mem (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
  set m := Nat.find key with hmdef
  have hm : IsUnit (MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) m) G) := Nat.find_spec key
  have hlt : ∀ j : ℕ, j < m → ¬ IsUnit (MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) j) G) :=
    fun j hj => Nat.find_min key hj
  have hq : ∀ j : ℕ, ∃ c : W, j < m → MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) j) G = π * c := by
    intro j
    by_cases hj : j < m
    · obtain ⟨c, hc⟩ := hdiv _ (hlt j hj)
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose c hc using hq
  set Plow : MvPowerSeries (Fin 2) W := fun n => if n 0 = 0 ∧ n 1 < m then c (n 1) else 0 with hPlow
  set H : MvPowerSeries (Fin 2) W :=
    fun n => if n 0 = 0 then MvPowerSeries.coeff (n + Finsupp.single 1 m) G else 0 with hH
  have hs_le : ∀ n : Fin 2 →₀ ℕ, Finsupp.single (1 : Fin 2) m ≤ n ↔ m ≤ n 1 := fun n => Finsupp.single_le_iff
  have hfree : freePart 0 G = MvPowerSeries.C π * Plow + MvPowerSeries.X 1 ^ m * H := by
    ext n
    rw [coeff_freePart, map_add, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_apply Plow, hPlow,
      MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial_mul, MvPowerSeries.coeff_apply H, hH]
    dsimp only
    by_cases h0 : n 0 = 0
    · rw [if_pos h0]
      by_cases h1 : n 1 < m
      · rw [if_pos ⟨h0, h1⟩, if_neg (by rw [hs_le]; omega), add_zero, ← hc (n 1) h1,
          ← eq_single_one_of_apply_zero_eq_zero n h0]
      · rw [if_neg (fun h => h1 h.2), mul_zero, zero_add, if_pos (by rw [hs_le]; omega), one_mul,
          if_pos (by rw [Finsupp.tsub_apply, h0]; simp),
          tsub_add_cancel_of_le ((hs_le n).mpr (by omega))]
    · rw [if_neg h0, if_neg (fun h => h0 h.1), mul_zero, zero_add]
      split_ifs with h2 h3
      · exfalso
        apply h0
        rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (by decide)] at h3
        simpa using h3
      · rw [one_mul]
      · rfl
  refine ⟨m, H, ?_, ?_⟩
  · rw [MvPowerSeries.isUnit_iff_constantCoeff, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      MvPowerSeries.coeff_apply H, hH]
    dsimp only
    rw [if_pos (by simp), zero_add]
    exact hm
  · have : G - MvPowerSeries.X 1 ^ m * H = MvPowerSeries.X 0 * quotPart 0 G + MvPowerSeries.C π * Plow := by
      have h := eq_X_mul_quotPart_add_freePart 0 G
      rw [hfree] at h
      linear_combination h
    rw [this]
    exact add_mem (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))

end Surgery

section Model

variable {W : Type*} [CommRing W]

theorem mk_eq_mk (τ : W) (f : MvPowerSeries (Fin 2) W) :
    UVCrossingModel.mk τ f = Ideal.Quotient.mk (uvCrossingIdeal W τ) f := rfl

theorem exists_mul_eq_one_of_sub_mem (τ : W) (P Z : MvPowerSeries (Fin 2) W)
    (hP : MvPowerSeries.constantCoeff P = 0)
    (h : P * Z - 1 ∈ uvCrossingIdeal W τ) : ∃ w : W, τ * w = 1 := by
  rw [Ideal.mem_span_singleton] at h
  obtain ⟨Q, hQ⟩ := h
  have := congrArg MvPowerSeries.constantCoeff hQ
  simp only [map_sub, map_mul, hP, zero_mul, map_one, MvPowerSeries.constantCoeff_X,
    MvPowerSeries.constantCoeff_C, mul_zero, zero_sub] at this
  refine ⟨MvPowerSeries.constantCoeff Q, ?_⟩
  linear_combination this

theorem not_isUnit_pow [IsDomain W] {π : W} (hπ : Irreducible π) {E : ℕ} (hE : 1 ≤ E) : ¬ IsUnit (π ^ E) := by
  intro h
  exact hπ.not_isUnit (isUnit_of_dvd_unit (dvd_pow_self π (by omega)) h)

theorem not_isUnit_U [IsDomain W] {π : W} (hπ : Irreducible π) {E : ℕ} (hE : 1 ≤ E) : ¬ IsUnit (U (π ^ E)) := by
  rintro ⟨z, hz⟩
  obtain ⟨Z, hZ⟩ := mk_surjective (π ^ E) (↑z⁻¹ : UVCrossingModel W (π ^ E))
  have h1 : U (π ^ E) * UVCrossingModel.mk (π ^ E) Z = 1 := by rw [hZ, ← hz, Units.mul_inv]
  rw [U, ← map_mul, ← map_one (UVCrossingModel.mk (π ^ E)), mk_eq_mk, mk_eq_mk, Ideal.Quotient.eq] at h1
  obtain ⟨w, hw⟩ := exists_mul_eq_one_of_sub_mem (π ^ E) _ Z (MvPowerSeries.constantCoeff_X 0) h1
  exact not_isUnit_pow hπ hE (isUnit_iff_exists_inv.mpr ⟨_, hw⟩)

theorem not_isUnit_V [IsDomain W] {π : W} (hπ : Irreducible π) {E : ℕ} (hE : 1 ≤ E) : ¬ IsUnit (V (π ^ E)) := by
  rintro ⟨z, hz⟩
  obtain ⟨Z, hZ⟩ := mk_surjective (π ^ E) (↑z⁻¹ : UVCrossingModel W (π ^ E))
  have h1 : V (π ^ E) * UVCrossingModel.mk (π ^ E) Z = 1 := by rw [hZ, ← hz, Units.mul_inv]
  rw [V, ← map_mul, ← map_one (UVCrossingModel.mk (π ^ E)), mk_eq_mk, mk_eq_mk, Ideal.Quotient.eq] at h1
  obtain ⟨w, hw⟩ := exists_mul_eq_one_of_sub_mem (π ^ E) _ Z (MvPowerSeries.constantCoeff_X 1) h1
  exact not_isUnit_pow hπ hE (isUnit_iff_exists_inv.mpr ⟨_, hw⟩)

theorem not_isUnit_const [IsDomain W] {π : W} (hπ : Irreducible π) {E : ℕ} (hE : 1 ≤ E) :
    ¬ IsUnit (const (π ^ E) π) := by
  rintro ⟨z, hz⟩
  obtain ⟨Z, hZ⟩ := mk_surjective (π ^ E) (↑z⁻¹ : UVCrossingModel W (π ^ E))
  have h1 : const (π ^ E) π * UVCrossingModel.mk (π ^ E) Z = 1 := by rw [hZ, ← hz, Units.mul_inv]
  rw [const, ← map_mul, ← map_one (UVCrossingModel.mk (π ^ E)), mk_eq_mk, mk_eq_mk, Ideal.Quotient.eq,
    Ideal.mem_span_singleton] at h1
  obtain ⟨Q, hQ⟩ := h1
  have := congrArg MvPowerSeries.constantCoeff hQ
  simp only [map_sub, map_mul, map_one, MvPowerSeries.constantCoeff_X, MvPowerSeries.constantCoeff_C,
    zero_mul, zero_sub] at this
  apply hπ.not_isUnit
  refine isUnit_iff_exists_inv.mpr ⟨MvPowerSeries.constantCoeff Z + π ^ (E - 1) * MvPowerSeries.constantCoeff Q, ?_⟩
  have hE' : π ^ E = π * π ^ (E - 1) := by rw [← pow_succ']; congr 1; omega
  rw [hE'] at this
  linear_combination this

theorem map_mk_span_pair (π : W) (E : ℕ) :
    Ideal.map (UVCrossingModel.mk (π ^ E))
        (Ideal.span {MvPowerSeries.C π, (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W)}) =
      Ideal.span {const (π ^ E) π, U (π ^ E)} := by
  rw [Ideal.map_span, Set.image_pair]
  rfl

theorem exists_isUnit_and_sub_mul_V_pow_mem [IsDomain W] [IsDiscreteValuationRing W] {π : W} (hπ : Irreducible π)
    (E : ℕ) (g : UVCrossingModel W (π ^ E)) (hg : g ∉ Ideal.span {const (π ^ E) π, U (π ^ E)}) :
    ∃ (m : ℕ) (γ : UVCrossingModel W (π ^ E)), IsUnit γ ∧
      g - γ * V (π ^ E) ^ m ∈ Ideal.span {const (π ^ E) π, U (π ^ E)} := by
  obtain ⟨G, rfl⟩ := mk_surjective (π ^ E) g
  have hG : G ∉ Ideal.span {MvPowerSeries.C π, (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W)} := by
    intro h
    apply hg
    rw [← map_mk_span_pair]
    exact Ideal.mem_map_of_mem _ h
  obtain ⟨m, H, hH, hmem⟩ := exists_isUnit_and_sub_X_pow_mul_mem hπ G hG
  refine ⟨m, UVCrossingModel.mk (π ^ E) H, hH.map _, ?_⟩
  have := Ideal.mem_map_of_mem (UVCrossingModel.mk (π ^ E)) hmem
  rw [map_mk_span_pair, map_sub, map_mul, map_pow] at this
  have hV : UVCrossingModel.mk (π ^ E) (MvPowerSeries.X 1) = V (π ^ E) := rfl
  rw [hV] at this
  convert this using 2
  ring

end Model

section Primes

variable {W : Type*} [CommRing W]

theorem U_mul_V_eq (π : W) (E : ℕ) : U (π ^ E) * V (π ^ E) = const (π ^ E) π ^ E := by
  rw [U, V, const, ← map_mul, ← map_pow, ← map_pow, mk_eq_mk, mk_eq_mk, Ideal.Quotient.eq]
  exact Ideal.subset_span rfl

theorem le_span_pair_of_isPrime [IsDomain W] [IsDiscreteValuationRing W] {π : W} (hπ : Irreducible π) (E : ℕ)
    (𝔮 : Ideal (UVCrossingModel W (π ^ E))) [h𝔮 : 𝔮.IsPrime]
    (hU : U (π ^ E) ∈ 𝔮) (hπq : const (π ^ E) π ∈ 𝔮) (hV : V (π ^ E) ∉ 𝔮) :
    𝔮 ≤ Ideal.span {const (π ^ E) π, U (π ^ E)} := by
  intro r hr
  by_contra hno
  obtain ⟨m, γ, hγ, hmem⟩ := exists_isUnit_and_sub_mul_V_pow_mem hπ E r hno
  have hsub : Ideal.span {const (π ^ E) π, U (π ^ E)} ≤ 𝔮 := by
    rw [Ideal.span_le]
    rintro w (rfl | rfl)
    · exact hπq
    · exact hU
  have hγV : γ * V (π ^ E) ^ m ∈ 𝔮 := by
    have := 𝔮.sub_mem hr (hsub hmem)
    rwa [sub_sub_cancel] at this
  rcases h𝔮.mem_or_mem hγV with h | h
  · exact h𝔮.ne_top (Ideal.eq_top_of_isUnit_mem _ h hγ)
  · rcases Nat.eq_zero_or_pos m with hm | hm
    · rw [hm, pow_zero] at h
      exact h𝔮.ne_top ((Ideal.eq_top_iff_one _).mpr h)
    · exact hV (h𝔮.mem_of_pow_mem m h)

theorem pow_mem_span_U_of_mem_span_pair (π : W) (E : ℕ)
    (β : UVCrossingModel W (π ^ E)) (hβ : β ∈ Ideal.span {const (π ^ E) π, U (π ^ E)}) :
    β ^ E ∈ Ideal.span {U (π ^ E)} := by
  obtain ⟨a, c, hac⟩ := Ideal.mem_span_pair.mp hβ
  obtain ⟨k, hk⟩ := sub_dvd_pow_sub_pow β (a * const (π ^ E) π) E
  have h1 : β - a * const (π ^ E) π = c * U (π ^ E) := by rw [← hac]; ring
  rw [h1] at hk
  have h2 : β ^ E = (a * const (π ^ E) π) ^ E + c * U (π ^ E) * k := by rw [← hk]; ring
  have h3 : β ^ E = U (π ^ E) * (a ^ E * V (π ^ E) + c * k) := by
    rw [h2, mul_pow, ← U_mul_V_eq]; ring
  rw [h3]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

end Primes

section Core

theorem core {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] {π : W} (hπ : Irreducible π)
    {E : ℕ} (hE : 1 ≤ E)
    {O : Type*} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    (ι : AdicCompletion (maximalIdeal O) O ≃+* UVCrossingModel W (π ^ E))
    (cx cy : O) (γU γV : (UVCrossingModel W (π ^ E))ˣ)
    (hcx : ι (algebraMap O (AdicCompletion (maximalIdeal O) O) cx) =
      (γU : UVCrossingModel W (π ^ E)) * U (π ^ E))
    (hcy : ι (algebraMap O (AdicCompletion (maximalIdeal O) O) cy) =
      (γV : UVCrossingModel W (π ^ E)) * V (π ^ E))
    (𝔭 : Ideal O) [h𝔭 : 𝔭.IsPrime] (hcxp : cx ∈ 𝔭) (hcyp : cy ∉ 𝔭)
    (b : O) (hb : b ∈ 𝔭) :
    ∃ m : O, ¬ IsUnit m ∧ b ^ (E + 1) = cx * m := by

  have hcm := Ideal.comap_map_adicCompletion_eq_of_isNoetherianRing (S := O) 𝔭
  obtain ⟨𝔔, h𝔔, h𝔔c⟩ := (Ideal.comap_map_eq_self_iff_of_isPrime 𝔭).mp hcm
  haveI := h𝔔
  let 𝔮 : Ideal (UVCrossingModel W (π ^ E)) := 𝔔.comap (ι.symm : UVCrossingModel W (π ^ E) →+* _)
  haveI h𝔮 : 𝔮.IsPrime := Ideal.comap_isPrime _ _
  have hmem : ∀ f : O, f ∈ 𝔭 ↔ ι (algebraMap O (AdicCompletion (maximalIdeal O) O) f) ∈ 𝔮 := by
    intro f
    rw [← h𝔔c, Ideal.mem_comap, Ideal.mem_comap]
    simp

  have hUq : U (π ^ E) ∈ 𝔮 := by
    have h1 : (γU : UVCrossingModel W (π ^ E)) * U (π ^ E) ∈ 𝔮 := hcx ▸ (hmem cx).mp hcxp
    have h2 := 𝔮.mul_mem_left (↑γU⁻¹ : UVCrossingModel W (π ^ E)) h1
    rwa [← mul_assoc, Units.inv_mul, one_mul] at h2
  have hπq : const (π ^ E) π ∈ 𝔮 := by
    refine h𝔮.mem_of_pow_mem E ?_
    rw [← U_mul_V_eq]
    exact 𝔮.mul_mem_right _ hUq
  have hVq : V (π ^ E) ∉ 𝔮 := by
    intro hV
    apply hcyp
    rw [hmem cy, hcy]
    exact 𝔮.mul_mem_left _ hV

  have hle : 𝔮 ≤ Ideal.span {const (π ^ E) π, U (π ^ E)} := le_span_pair_of_isPrime hπ E 𝔮 hUq hπq hVq

  have hβq : ι (algebraMap O (AdicCompletion (maximalIdeal O) O) b) ∈ 𝔮 := (hmem b).mp hb
  have hβ : ι (algebraMap O (AdicCompletion (maximalIdeal O) O) b) ∈
      Ideal.span {const (π ^ E) π, U (π ^ E)} := hle hβq
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp (pow_mem_span_U_of_mem_span_pair π E _ hβ)
  have hβunit : ¬ IsUnit (ι (algebraMap O (AdicCompletion (maximalIdeal O) O) b)) := fun hu =>
    h𝔮.ne_top (Ideal.eq_top_of_isUnit_mem _ hβq hu)
  have hn : ¬ IsUnit ((↑γU⁻¹ : UVCrossingModel W (π ^ E)) * d *
      ι (algebraMap O (AdicCompletion (maximalIdeal O) O) b)) := fun hu =>
    hβunit (isUnit_of_mul_isUnit_right hu)
  have hβE1 : ι (algebraMap O (AdicCompletion (maximalIdeal O) O) b) ^ (E + 1) =
      ι (algebraMap O (AdicCompletion (maximalIdeal O) O) cx) *
        ((↑γU⁻¹ : UVCrossingModel W (π ^ E)) * d * ι (algebraMap O (AdicCompletion (maximalIdeal O) O) b)) := by
    rw [pow_succ, ← hd, hcx]
    calc d * U (π ^ E) * ι (algebraMap O (AdicCompletion (maximalIdeal O) O) b)
        = ((γU : UVCrossingModel W (π ^ E)) * (↑γU⁻¹ : UVCrossingModel W (π ^ E))) *
            (d * U (π ^ E) * ι (algebraMap O (AdicCompletion (maximalIdeal O) O) b)) := by
          rw [Units.mul_inv, one_mul]
      _ = (γU : UVCrossingModel W (π ^ E)) * U (π ^ E) *
            ((↑γU⁻¹ : UVCrossingModel W (π ^ E)) * d * ι (algebraMap O (AdicCompletion (maximalIdeal O) O) b)) := by
          ring

  have hO : algebraMap O (AdicCompletion (maximalIdeal O) O) (b ^ (E + 1)) =
      algebraMap O (AdicCompletion (maximalIdeal O) O) cx *
        ι.symm ((↑γU⁻¹ : UVCrossingModel W (π ^ E)) * d *
          ι (algebraMap O (AdicCompletion (maximalIdeal O) O) b)) := by
    apply ι.injective
    rw [map_pow, map_pow, hβE1, map_mul, RingEquiv.apply_symm_apply]
  have hn' : ι.symm ((↑γU⁻¹ : UVCrossingModel W (π ^ E)) * d *
      ι (algebraMap O (AdicCompletion (maximalIdeal O) O) b)) ∈
        (maximalIdeal O).map (algebraMap O (AdicCompletion (maximalIdeal O) O)) := by
    rw [← AdicCompletion.maximalIdeal_eq_map, mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply hn
    simpa using hu.map ι
  have hmemJ : algebraMap O (AdicCompletion (maximalIdeal O) O) (b ^ (E + 1)) ∈
      (Ideal.span {cx} * maximalIdeal O).map (algebraMap O (AdicCompletion (maximalIdeal O) O)) := by
    rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton, hO]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hn'
  have hbO : b ^ (E + 1) ∈ Ideal.span {cx} * maximalIdeal O := by
    rw [← Ideal.comap_map_adicCompletion_eq_of_isNoetherianRing (S := O) (Ideal.span {cx} * maximalIdeal O),
      Ideal.mem_comap]
    exact hmemJ
  obtain ⟨m, hm, hmeq⟩ := Ideal.mem_span_singleton_mul.mp hbO
  exact ⟨m, (mem_maximalIdeal _).mp hm, hmeq.symm⟩

end Core

end NodePowSol

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')) (W₀ : ValuationSubring ↥F₀),

      ((∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ W₀) ∧
      IsDiscreteValuationRing ↥W₀ ∧
      (∃ hπW : algebraMap ↥k₀ ↥F₀ π₀ ∈ W₀, maximalIdeal ↥W₀ = Ideal.span {(⟨_, hπW⟩ : ↥W₀)})) →

    ∀ (O : Subring ↥F₀) [IsLocalRing ↥O] [IsNoetherianRing ↥O],
      (∀ f : ↥F₀, f ∈ O → f ∈ W₀) →
      (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ O) →
      (∀ (f : ↥F₀) (hf : f ∈ O), ∃ (x : ↥k₀) (hx : algebraMap ↥k₀ ↥F₀ x ∈ O), (x : (AlgebraicClosure ℚ)) ∈ A ∧
              ¬ IsUnit ((⟨f, hf⟩ : ↥O) - ⟨_, hx⟩)) →

      (∀ f : ↥F₀, ∃ g h : ↥F₀, g ∈ O ∧ h ∈ O ∧ h ≠ 0 ∧ f * h = g) →
    ∀ (E₀ : ℕ) (_ : 1 ≤ E₀) (hπO : algebraMap ↥k₀ ↥F₀ π₀ ∈ O) (cx cy : ↥O) (u : (↥O)ˣ)
      (ι : (AdicCompletion (maximalIdeal ↥O) ↥O) ≃+* UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))
      (γU γV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))ˣ),
      cx * cy = (⟨_, hπO⟩ : ↥O) ^ E₀ * (u : ↥O) →
      (∀ (x : ↥k₀) (hx : (x : (AlgebraicClosure ℚ)) ∈ A) (hxO : algebraMap ↥k₀ ↥F₀ x ∈ O),
                ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hxO⟩) =
                  UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨x, hx⟩)) →
      ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cx) = (γU : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * UVCrossingModel.U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) →
      ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cy) = (γV : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) →

    ∀ (Wx : ValuationSubring ↥F₀),
      (∀ f : ↥F₀, f ∈ O → f ∈ Wx) →
      IsDiscreteValuationRing ↥Wx →
      (∃ hπW : algebraMap ↥k₀ ↥F₀ π₀ ∈ Wx, maximalIdeal ↥Wx = Ideal.span {(⟨_, hπW⟩ : ↥Wx)}) →
      (∀ hcx : (cx : ↥F₀) ∈ Wx, (⟨(cx : ↥F₀), hcx⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
      (∀ hcy : (cy : ↥F₀) ∈ Wx, (⟨(cy : ↥F₀), hcy⟩ : ↥Wx) ∉ maximalIdeal ↥Wx) →

    ∀ (b : ↥O), (∀ hb : ((b : ↥F₀)) ∈ Wx, (⟨(b : ↥F₀), hb⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
      ∃ m : ↥O, ¬ IsUnit m ∧ b ^ (E₀ + 1) = cx * m := by
  intro F₀ W₀ _hW₀ O _ _ _hOW₀ _hconstO _hresO _hfrac E₀ hE₀ hπO cx cy u ι γU γV _hcxcy _hconst hcx hcy Wx hOWx
    _hWxdvr _hWxunif hcxW hcyW b hbW

  haveI := hdvr
  have hirr : Irreducible (⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hunif
  obtain ⟨instDom, instDVR, _, hϖirr, -, -⟩ :=
    IsDiscreteValuationRing.adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete
      ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⟨π₀, hπ⟩ hirr
  haveI := instDom
  haveI := instDVR

  let incl : ↥O →+* ↥Wx :=
    { toFun := fun f => ⟨(f : ↥F₀), hOWx _ f.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  let 𝔭 : Ideal ↥O := (maximalIdeal ↥Wx).comap incl
  haveI : 𝔭.IsPrime := Ideal.comap_isPrime incl (maximalIdeal ↥Wx)
  have hb' : b ∈ 𝔭 := hbW (hOWx _ b.2)
  have hcx' : cx ∈ 𝔭 := hcxW (hOWx _ cx.2)
  have hcy' : cy ∉ 𝔭 := fun h => hcyW (hOWx _ cy.2) h
  exact NodePowSol.core hϖirr hE₀ ι cx cy γU γV hcx hcy 𝔭 hcx' hcy' b hb'

end S_ModularCurve_FullLevel_exists_pow_eq_mul_nonunit_of_mem_maximalIdeal_igusaBranch_of_node_crossingPresentation
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_pow_eq_mul_nonunit_of_mem_maximalIdeal_igusaBranch_of_node_crossingPresentation (solution)
