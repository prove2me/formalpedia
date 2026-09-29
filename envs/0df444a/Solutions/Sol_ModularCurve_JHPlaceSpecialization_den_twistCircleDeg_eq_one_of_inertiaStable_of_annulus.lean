-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.den_twistCircleDeg_eq_one_of_inertiaStable_of_annulus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/02e2ff35-10be-5546-88aa-47eeddfce339

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_JHNodeDepth
import Definitions.Def_ModularCurve_JHNodeDepthInf
import Definitions.Def_ModularCurve_JHTwistType
import Theorems.Thm_ValuationSubring_exists_dvr_subring_of_forall_mem_inertiaSubgroupIn
import Theorems.Thm_AlgebraicCurve_SemilinearAut_restrict_smul
import Theorems.Thm_ModularCurve_evalAt_eq_apply_evalAt_of_coe_eq_coeffMap
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_den_twistCircleDeg_eq_one_of_inertiaStable_of_annulus
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

namespace OrbIntH

theorem exists_valuation_eq_pow_of_mem_of_forall_mem_inertiaSubgroupIn
    {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    (hA : ((p : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits)
    {z : AlgebraicClosure ℚ} (hzA : z ∈ A) (hz0 : z ≠ 0)
    (hzfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ z = z) :
    ∃ d : ℕ, A.valuation z = A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ^ d := by
  classical
  obtain ⟨O, hSO, hOA, -, hDVR, hirr, -⟩ :=
    ValuationSubring.exists_dvr_subring_of_forall_mem_inertiaSubgroupIn p A hA {z}
      (fun x hx => by
        rw [Finset.mem_singleton] at hx
        subst hx
        exact ⟨hzA, fun σ hσ => hzfix σ hσ⟩)
  have hzO : z ∈ O := hSO (by simp)
  haveI : IsDiscreteValuationRing O := hDVR
  have hz0' : (⟨z, hzO⟩ : O) ≠ 0 := fun h => hz0 (congrArg Subtype.val h)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hz0' hirr
  refine ⟨n, ?_⟩
  have hvu : A.valuation (((u : O) : O) : AlgebraicClosure ℚ) = 1 := by
    apply le_antisymm
    · exact (A.valuation_le_one_iff _).mpr (hOA (u : O).2)
    · have h1 : A.valuation (((u⁻¹ : Oˣ) : O) : AlgebraicClosure ℚ) ≤ 1 :=
        (A.valuation_le_one_iff _).mpr (hOA ((u⁻¹ : Oˣ) : O).2)
      have hmul : (((u : O) : AlgebraicClosure ℚ)) * (((u⁻¹ : Oˣ) : O) : AlgebraicClosure ℚ) = 1 := by
        rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
      have h2 : A.valuation (((u : O) : AlgebraicClosure ℚ)) * A.valuation (((u⁻¹ : Oˣ) : O) : AlgebraicClosure ℚ) = 1 := by
        rw [← map_mul, hmul, map_one]
      by_contra hlt
      push Not at hlt
      have := mul_lt_one_of_lt_of_le hlt h1
      exact absurd h2 this.ne
  have h := congrArg (fun t : O => A.valuation (t : AlgebraicClosure ℚ)) hu
  simp only [Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, hvu, mul_one] at h
  convert h using 2
  rfl

theorem exists_valuation_eq_zpow_of_forall_mem_inertiaSubgroupIn
    {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    (hA : ((p : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits)
    {z : AlgebraicClosure ℚ} (hz0 : z ≠ 0)
    (hzfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ z = z) :
    ∃ e : ℤ, A.valuation z = A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ^ e := by
  rcases A.mem_or_inv_mem z with h | h
  · obtain ⟨d, hd⟩ := exists_valuation_eq_pow_of_mem_of_forall_mem_inertiaSubgroupIn hA h hz0 hzfix
    exact ⟨d, by rw [hd, zpow_natCast]⟩
  · obtain ⟨d, hd⟩ := exists_valuation_eq_pow_of_mem_of_forall_mem_inertiaSubgroupIn hA h (inv_ne_zero hz0)
      (fun σ hσ => by rw [map_inv₀, hzfix σ hσ])
    refine ⟨-(d : ℤ), ?_⟩
    rw [map_inv₀] at hd
    rw [zpow_neg, zpow_natCast, ← hd, inv_inv]

section ValueGroup
variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

theorem zpow_injective_of_lt_one {γ : Γ} (h0 : γ ≠ 0) (h1 : γ < 1) : Function.Injective fun n : ℤ => γ ^ n := by
  intro m n hmn
  simp only at hmn
  set u : Γˣ := Units.mk0 γ h0 with hu
  have hu1 : u < 1 := by
    rw [← Units.val_lt_val, hu, Units.val_mk0, Units.val_one]; exact h1
  have hum : ∀ k : ℤ, ((u ^ k : Γˣ) : Γ) = γ ^ k := fun k => by
    rw [Units.val_zpow_eq_zpow_val, hu, Units.val_mk0]
  have h' : u ^ m = u ^ n := Units.ext (by rw [hum, hum]; exact hmn)
  have hinv : 1 < u⁻¹ := one_lt_inv'.mpr hu1
  have hsm : StrictMono fun k : ℤ => (u⁻¹) ^ k := zpow_right_strictMono hinv
  have : (u⁻¹) ^ (-m) = (u⁻¹) ^ (-n) := by
    rw [inv_zpow', inv_zpow', neg_neg, neg_neg, h']
  have := hsm.injective this
  omega

end ValueGroup

theorem den_eq_one_of_eq_intCast {x : ℚ} {m : ℤ} (h : x = m) : x.den = 1 := by
  rw [h]; exact Rat.den_intCast m

theorem exists_int_mul_eq_of_den_dvd (t : ℚ) (n : ℤ) (h : (t.den : ℤ) ∣ n) : ∃ m : ℤ, (n : ℚ) * t = m := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c * t.num, ?_⟩
  rw [hc]
  push_cast
  have := Rat.mul_den_eq_num t
  calc (t.den : ℚ) * c * t = c * (t * t.den) := by ring
    _ = c * t.num := by rw [this]

theorem exists_int_mul_tent (n : ℤ) (t : ℚ) (d : ℕ) (h : ∃ m : ℤ, (n : ℚ) * t = m) :
    ∃ m : ℤ, (n : ℚ) * max 0 (1 - |t - d|) = m := by
  obtain ⟨m, hm⟩ := h
  rcases le_or_gt 1 |t - (d : ℚ)| with h1 | h1
  · refine ⟨0, ?_⟩
    rw [max_eq_left (by linarith), mul_zero, Int.cast_zero]
  · rw [max_eq_right (by linarith)]

    have habs : ∃ m' : ℤ, (n : ℚ) * |t - d| = m' := by
      rcases lt_trichotomy n 0 with hn | hn | hn
      · refine ⟨-|m - n * d|, ?_⟩
        have : (n : ℚ) = -|(n : ℚ)| := by
          rw [abs_of_neg (by exact_mod_cast hn), neg_neg]
        rw [this, neg_mul, ← abs_mul, mul_sub, hm]
        push_cast
        ring_nf
      · exact ⟨0, by rw [hn]; simp⟩
      · refine ⟨|m - n * d|, ?_⟩
        have : (n : ℚ) = |(n : ℚ)| := (abs_of_pos (by exact_mod_cast hn)).symm
        rw [this, ← abs_mul, mul_sub, hm]
        push_cast
        ring_nf
    obtain ⟨m', hm'⟩ := habs
    refine ⟨n - m', ?_⟩
    rw [mul_sub, mul_one, hm']
    push_cast
    ring

theorem prod_zpow_eq_zpow_sum₀ {Γ : Type*} [CommGroupWithZero Γ] {ι : Type*} (s : Finset ι) (γ : Γ) (hγ : γ ≠ 0)
    (f : ι → ℤ) : ∏ i ∈ s, γ ^ f i = γ ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hγ]

theorem zpow_pow_comm₀ {Γ : Type*} [CommGroupWithZero Γ] (a : Γ) (e : ℤ) (d : ℕ) :
    (a ^ e) ^ d = (a ^ d) ^ e := by
  rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, mul_comm]

end OrbIntH

namespace OrbEqv

theorem restrictAlong_semilinearAut_smul
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    {g : SemilinearAut K F} {g' : SemilinearAut K F'}
    (hgg' : SemilinearAut.IntertwinesAlong φ.toRingHom g g') (w : Place K F') :
    (g' • w).restrictAlong φ hφ = g • (w.restrictAlong φ hφ) := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact SemilinearAut.restrict_smul (F := F) (g := g) (g' := g') (fun x => hgg' x) w

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} [CharP (ResidueField ↥A) p]

theorem smul_alpha
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) :
    arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • α u =
      α (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField (M / p) (infSubgroup p M H hpM)) σ • u) := by
  apply Subtype.ext
  rw [coe_arithmeticGalois_smul, hα_coe, hα_coe, coe_arithmeticGalois_smul]

theorem reduceFst_smul (Psp : JHPlaceSpecialization p M H hpM A)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    Psp.reduceFst α hα (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • W) = Psp.reduceFst α hα W := by
  show Psp.sp ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • W).restrictAlong α hα) = Psp.sp (W.restrictAlong α hα)
  rw [restrictAlong_semilinearAut_smul α hα
      (g := arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField (M / p) (infSubgroup p M H hpM)) σ)
      (g' := arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ)
      (fun x => smul_alpha α hα_coe σ x) W]
  exact Psp.d6_inertia σ hσ _

theorem reduceSnd_smul (Psp : JHPlaceSpecialization p M H hpM A)
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (δ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • W) =
      Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W := by
  show δ (Psp.sp ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • W).restrictAlong (θ.toAlgHom.comp α) hβ)) =
    δ (Psp.sp (W.restrictAlong (θ.toAlgHom.comp α) hβ))
  rw [restrictAlong_semilinearAut_smul (θ.toAlgHom.comp α) hβ
      (g := arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField (M / p) (infSubgroup p M H hpM)) σ)
      (g' := arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ)
      (fun x => by
        show arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ (α x) = θ (α _)
        rw [← hθgal, smul_alpha α hα_coe σ x]) W]
  exact congrArg δ (Psp.d6_inertia σ hσ _)

end OrbEqv

namespace OrbIntH
section Core
variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {A : ValuationSubring (AlgebraicClosure ℚ)}

open Classical in

theorem core (hA : ((p : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits)
    (An : AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H)) (pos : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ℚ) (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (c : ℤ)
    (hlaw : ∀ V ∈ An.dom, A.valuation (V.evalAt An.param) ^ (pos V).den =
        A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ^ (c * (pos V).den - (pos V).num))
    (hne0 : ∀ V ∈ An.dom, V.evalAt An.param ≠ 0)
    (hdomσ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V ∈ An.dom, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V ∈ An.dom)
    (hval : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V ∈ An.dom, ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V).evalAt An.param = σ (V.evalAt An.param))
    (hposσ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), pos ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V) = pos V)
    (hXσ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), X ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V) = X V)
    (t : ℚ) :
    ∃ m : ℤ, ((∑ V ∈ (X.support.filter (fun V => V ∈ An.dom)).filter (fun V => pos V = t), X V : ℤ) : ℚ) * t = m := by
  classical
  obtain ⟨St, hSt⟩ : ∃ St : Finset (Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), St = (X.support.filter (fun V => V ∈ An.dom)).filter (fun V => pos V = t) := ⟨_, rfl⟩
  rw [← hSt]
  have hmemSt : ∀ V, V ∈ St ↔ (V ∈ X.support ∧ V ∈ An.dom) ∧ pos V = t := fun V => by
    rw [hSt, Finset.mem_filter, Finset.mem_filter]
  by_cases hne : St = ∅
  · refine ⟨0, ?_⟩
    simp [hne]
  obtain ⟨V₀, hV₀⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨γ, hγ⟩ : ∃ γ : A.ValueGroup, γ = A.valuation ((p : ℕ) : AlgebraicClosure ℚ) := ⟨_, rfl⟩
  have hq0 : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hγ0 : γ ≠ 0 := by rw [hγ]; exact (Valuation.ne_zero_iff _).mpr hq0
  have hγ1 : γ < 1 := by rw [hγ]; exact (ValuationSubring.mem_nonunits_iff A).mp hA

  have hlawSt : ∀ V ∈ St, A.valuation (V.evalAt An.param) ^ t.den = γ ^ (c * t.den - t.num) := by
    intro V hV
    obtain ⟨⟨-, hd⟩, h4⟩ := (hmemSt V).mp hV
    rw [← h4, hγ]; exact hlaw V hd
  have hyne : ∀ V ∈ St, V.evalAt An.param ≠ 0 := fun V hV => hne0 V ((hmemSt V).mp hV).1.2

  have hSσ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V ∈ St, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V ∈ St := by
    intro σ hσ V hV
    obtain ⟨⟨h0, hd⟩, h4⟩ := (hmemSt V).mp hV
    refine (hmemSt _).mpr ⟨⟨?_, hdomσ σ hσ V hd⟩, ?_⟩
    · rw [Finsupp.mem_support_iff] at h0 ⊢
      rw [hXσ σ hσ]; exact h0
    · rw [hposσ σ hσ]; exact h4

  obtain ⟨z, hz⟩ : ∃ z : AlgebraicClosure ℚ, z = ∏ V ∈ St, (V.evalAt An.param) ^ (X V) := ⟨_, rfl⟩
  have hz0 : z ≠ 0 := by
    rw [hz]; exact Finset.prod_ne_zero_iff.mpr fun V hV => zpow_ne_zero _ (hyne V hV)
  have hzfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ z = z := by
    intro σ hσ
    rw [hz, map_prod]
    simp_rw [map_zpow₀]
    have step : ∏ V ∈ St, σ (V.evalAt An.param) ^ X V = ∏ V ∈ St, (((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V).evalAt An.param) ^ X ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V) :=
      Finset.prod_congr rfl fun V hV => by rw [hval σ hσ V ((hmemSt V).mp hV).1.2, hXσ σ hσ V]
    rw [step]
    refine Finset.prod_nbij (fun V => (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V) (fun V hV => hSσ σ hσ V hV) ?_ ?_ (fun V _ => rfl)
    · intro V₁ _ V₂ _ h
      exact MulAction.injective (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) h
    · intro V' hV'
      refine ⟨(arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ⁻¹) • V', ?_, ?_⟩
      · exact hSσ σ⁻¹ (Subgroup.inv_mem _ hσ) V' hV'
      · show (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ⁻¹) • V') = V'
        rw [map_inv, smul_inv_smul]

  obtain ⟨e, he⟩ := OrbIntH.exists_valuation_eq_zpow_of_forall_mem_inertiaSubgroupIn hA hz0 hzfix
  rw [← hγ] at he
  have hvz : A.valuation z = ∏ V ∈ St, A.valuation (V.evalAt An.param) ^ (X V) := by
    rw [hz, map_prod]; simp_rw [map_zpow₀]
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = ∑ V ∈ St, X V := ⟨_, rfl⟩
  rw [← hn]
  have hpow : γ ^ (e * t.den) = γ ^ ((c * t.den - t.num) * n) := by
    calc γ ^ (e * t.den) = (A.valuation z) ^ t.den := by rw [zpow_mul, ← he, zpow_natCast]
      _ = ∏ V ∈ St, (A.valuation (V.evalAt An.param) ^ (X V)) ^ t.den := by rw [hvz, Finset.prod_pow]
      _ = ∏ V ∈ St, (γ ^ (c * t.den - t.num)) ^ (X V) := Finset.prod_congr rfl fun V hV => by
            rw [OrbIntH.zpow_pow_comm₀, hlawSt V hV]
      _ = ∏ V ∈ St, γ ^ ((c * t.den - t.num) * X V) := Finset.prod_congr rfl fun V _ => by rw [zpow_mul]
      _ = γ ^ (∑ V ∈ St, (c * t.den - t.num) * X V) := OrbIntH.prod_zpow_eq_zpow_sum₀ St γ hγ0 _
      _ = γ ^ ((c * t.den - t.num) * n) := by rw [hn, Finset.mul_sum]
  have hexp : e * t.den = (c * t.den - t.num) * n := OrbIntH.zpow_injective_of_lt_one hγ0 hγ1 hpow
  have hdvd : (t.den : ℤ) ∣ t.num * n := ⟨c * n - e, by linear_combination hexp⟩
  have hgcd : Int.gcd (t.den : ℤ) t.num = 1 := by
    rw [Int.gcd_comm]
    exact t.reduced
  have hdvd' : (t.den : ℤ) ∣ n := Int.dvd_of_dvd_mul_right_of_gcd_one hdvd hgcd
  exact OrbIntH.exists_int_mul_eq_of_den_dvd t n hdvd'

end Core
end OrbIntH

open Classical in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hFix : ∀ y ∈ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p,
      JHPlaceSpecialization.Fixed p M H hpM A δ y ∧
        JHPlaceSpecialization.Fixed p M H hpM A δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p y))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ)
    (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ) (hO : Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ)
    (hreg : Rpd.RegularityLaw α (θ.toAlgHom.comp α) hα hβ δ SS) (hnv : Rpd.NodeValueLaw α (θ.toAlgHom.comp α) hα hβ δ SS)

    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))

    (hFixFin : {v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) | JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v}.Finite)

    (hLFst : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q → Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q' →
      Psp.reduceFst α hα Q' = Psp.reduceFst α hα Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₁ : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg₁⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₁ : ε ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨ε, hε₁⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceFst α hα Q).ord (Rpd.R₁.residue ⟨ε, hε₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hLSnd : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q → Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q' →
      Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q' = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₂ : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg₂⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₂ : ε ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨ε, hε₂⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q).ord (Rpd.R₂.residue ⟨ε, hε₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))

    (hUnit : ∃ (u₁ u₂ : ↥(xHFunctionFieldBar M H)) (D₁ D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      (∀ W, D₁ W = W.ord u₁) ∧ (∀ W, D₂ W = W.ord u₂) ∧

      (∃ h₁ : u₁ ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨u₁, h₁⟩ ≠ 0 ∧ u₁⁻¹ ∈ Rpd.R₁.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D₁) v = v.ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceFst α hα) (D₁.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα C) =
            (Psp.reduceFst α hα C).ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₂ : f ^ m * u₁ ^ j ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨f ^ m * u₁ ^ j, h₂⟩ ≠ 0) ∧

      (∃ h₂ : u₂ ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨u₂, h₂⟩ ≠ 0 ∧ u₂⁻¹ ∈ Rpd.R₂.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D₂) v = v.ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (D₂.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C) =
            (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C).ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₁ : f ^ m * u₂ ^ j ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨f ^ m * u₂ ^ j, h₁⟩ ≠ 0))
    (hcusp : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) w →
        (∃ C, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceFst α hα C = w) ∧
        (∃ C, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C = w))

    (horientInf : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
      δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα C)) = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C)
    (horient0 : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
      Psp.reduceFst α hα C = qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C))

    (e : ↥SS → ℕ) (he : ∀ s, 0 < e s)
    (hAnn : ∀ s : ↥SS, ∃ An : AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H),
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        W ∈ An.dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
      (∃ u : ↥A, IsUnit u ∧ An.modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
        (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • An.param = An.param) ∧
      algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : AlgebraicClosure ℚ))⁻¹ * An.param ∈ Rpd.R₁.integers ∧
      (∃ h₂ : An.param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨An.param, h₂⟩ ≠ 0) ∧

      (∃ h₂ : An.param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨An.param, h₂⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
      (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹ ∈ Rpd.R₁.integers,
        s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹)) ^
              (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))

    (An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
    (hAn : ∀ s : ↥SS,
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        W ∈ (An s).dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
      (∃ u : ↥A, IsUnit u ∧ (An s).modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
        (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (An s).param = (An s).param) ∧
      algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : AlgebraicClosure ℚ))⁻¹ * (An s).param ∈ Rpd.R₁.integers ∧
      (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨(An s).param, h₂⟩ ≠ 0) ∧

      (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨(An s).param, h₂⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
            ∃ h : P.evalAt f * (P.evalAt (An s).param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
      (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹ ∈ Rpd.R₁.integers,
        s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
            ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹)) ^
              (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))
    (pos : ↥SS → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ℚ)
    (hpos : JHPlaceSpecialization.AnnulusPositionLaw SS e An pos)
    (hposσ : ∀ (s : ↥SS), ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      pos s ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V) = pos s V)
    (X : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))))
    (hXst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = X) :
    ∀ (s : ↥SS) (d : ℕ), (JHPlaceSpecialization.twistCircleDeg SS An pos (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s d).den = 1 := by
  classical
  intro s d
  haveI : PerfectField (AlgebraicClosure ℚ) := PerfectField.ofCharZero
  haveI hCObar : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) :=
    (ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) M H).1
  have hrat : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.IsRational := fun V => (Place.isRational_iff_deg_eq_one V).mpr (IsCurveOver.deg_eq_one_of_isAlgClosed V)

  have hdom := (hAn s).1
  have hdomσ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ W ∈ (An s).dom, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • W ∈ (An s).dom := by
    intro σ hσ W hW
    rw [hdom] at hW ⊢
    simp only [JHPlaceSpecialization.IsStrictFst, JHPlaceSpecialization.IsStrictSnd,
      OrbEqv.reduceFst_smul Psp α hα hα_coe σ hσ, OrbEqv.reduceSnd_smul Psp θ hθgal α hβ hα_coe δ σ hσ] at hW ⊢
    exact hW

  have hXσ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V) = (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) V := by
    intro σ hσ V
    have := SemilinearAut.divisor_smul_apply_smul (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) V
    rw [hXst σ hσ] at this
    exact this

  have hzfix := (hAn s).2.2.1
  have hval : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V ∈ (An s).dom, ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V).evalAt (An s).param = σ (V.evalAt (An s).param) := by
    intro σ hσ V hV
    obtain ⟨-, hzO, -⟩ := (An s).mem_dom V hV
    refine ModularCurve.evalAt_eq_apply_evalAt_of_coe_eq_coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) (xHFunctionField M H)
      V ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V) ?_ (hrat V) (An s).param (An s).param ?_ hzO
    · intro x x' hx'
      have hx : x' = (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • x := by
        apply Subtype.ext
        rw [hx', coe_arithmeticGalois_smul]
      first
        | (rw [hx]; done)
        | (rw [hx]; exact SemilinearAut.ord_smul _ _ _)
    · have h := congrArg (fun f : ↥(xHFunctionFieldBar M H) => (f : LaurentSeries (AlgebraicClosure ℚ))) (hzfix σ hσ)
      simp only [coe_arithmeticGalois_smul] at h
      exact h.symm

  obtain ⟨u, hu, hmod⟩ := (hAn s).2.1
  have hp0 : A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hvu : A.valuation ((u : ↥A) : AlgebraicClosure ℚ) = 1 := A.valuation_unit hu.unit
  have hvmod : A.valuation ((((An s).modulus : ↥A) : AlgebraicClosure ℚ)) = A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ^ (e s) := by
    rw [hmod]; push_cast; rw [map_mul, map_pow, hvu, mul_one]
  have hne0 : ∀ V ∈ (An s).dom, V.evalAt (An s).param ≠ 0 := fun V hV => ((An s).mem_dom V hV).2.2.2.1
  have hlaw : ∀ V ∈ (An s).dom, A.valuation (V.evalAt (An s).param) ^ (pos s V).den =
      A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ^ (((e s : ℕ) : ℤ) * (pos s V).den - (pos s V).num) := by
    intro V hV
    obtain ⟨hVrat, hzO, -, hz0, -⟩ := (An s).mem_dom V hV
    obtain ⟨h0, -, hl⟩ := hpos s V hV

    have hzval : V.HasValue (An s).param (V.evalAt (An s).param) := ⟨hzO, (Place.algebraMap_evalAt V hVrat hzO).symm⟩
    have hval' : V.HasValue (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((((An s).modulus : ↥A) : AlgebraicClosure ℚ)) * ((An s).param)⁻¹)
        (((((An s).modulus : ↥A) : AlgebraicClosure ℚ)) * (V.evalAt (An s).param)⁻¹) :=
      (Place.hasValue_algebraMap V _).mul (hzval.inv hz0)
    have hev : V.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((((An s).modulus : ↥A) : AlgebraicClosure ℚ)) * ((An s).param)⁻¹) =
        ((((An s).modulus : ↥A) : AlgebraicClosure ℚ)) * (V.evalAt (An s).param)⁻¹ := by
      have h1 := Place.algebraMap_evalAt V hVrat hval'.mem
      rw [hval'.residue_eq] at h1
      exact (algebraMap (AlgebraicClosure ℚ) V.ResidueField).injective h1
    rw [hev, map_mul, map_inv₀, hvmod, mul_pow, inv_pow] at hl

    have hvz0 : A.valuation (V.evalAt (An s).param) ≠ 0 := (Valuation.ne_zero_iff _).mpr hz0
    have hnum : ((pos s V).num.toNat : ℤ) = (pos s V).num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr h0.le)
    have key : A.valuation (V.evalAt (An s).param) ^ (pos s V).den =
        (A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ^ (e s)) ^ (pos s V).den * (A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ^ (pos s V).num.toNat)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ hp0), ← hl, mul_left_comm, mul_inv_cancel₀ (pow_ne_zero _ hvz0), mul_one]
    rw [key, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_neg, ← zpow_add₀ hp0, hnum]
    congr 1

  have hA' : ((p : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits := hA
  have keyt : ∀ t : ℚ, ∃ m : ℤ, ((∑ V ∈ ((X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support.filter (fun V => V ∈ (An s).dom)).filter (fun V => pos s V = t), (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) V : ℤ) : ℚ) * t = m :=
    fun t => OrbIntH.core hA' (An s) (pos s) (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ((e s : ℕ) : ℤ) hlaw hne0 hdomσ hval (hposσ s) hXσ t

  obtain ⟨S0, hS0⟩ : ∃ S0 : Finset (Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), S0 = (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support.filter (fun V => V ∈ (An s).dom) := ⟨_, rfl⟩
  have regroup : ∀ (φ : ℚ → ℚ) (hφ : ∀ (t : ℚ) (n : ℤ), (∃ m : ℤ, (n : ℚ) * t = m) → ∃ m : ℤ, (n : ℚ) * φ t = m),
      ∃ Mz : ℤ, (∑ V ∈ S0, ((X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) V : ℚ) * φ (pos s V)) = Mz := by
    intro φ hφ
    rw [← Finset.sum_fiberwise_of_maps_to (s := S0) (t := S0.image (pos s)) (g := pos s)
      (fun V hV => Finset.mem_image_of_mem _ hV) (fun V => ((X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) V : ℚ) * φ (pos s V))]
    have inner : ∀ t ∈ S0.image (pos s), ∃ m : ℤ, (∑ V ∈ S0.filter (fun V => pos s V = t), ((X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) V : ℚ) * φ (pos s V)) = m := by
      intro t _
      have h1 : (∑ V ∈ S0.filter (fun V => pos s V = t), ((X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) V : ℚ) * φ (pos s V)) =
          (∑ V ∈ S0.filter (fun V => pos s V = t), ((X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) V : ℚ)) * φ t := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun V hV => ?_
        rw [(Finset.mem_filter.mp hV).2]
      rw [h1, ← Int.cast_sum]
      refine hφ t _ ?_
      rw [hS0]; exact keyt t
    choose m hm using inner
    refine ⟨∑ t ∈ (S0.image (pos s)).attach, m t t.2, ?_⟩
    rw [← Finset.sum_attach (S0.image (pos s))]
    push_cast
    exact Finset.sum_congr rfl fun t _ => hm t t.2
  obtain ⟨Mz, hM⟩ := regroup (fun t => max 0 (1 - |t - d|)) (fun t n h => OrbIntH.exists_int_mul_tent n t d h)
  unfold JHPlaceSpecialization.twistCircleDeg
  rw [← hS0]
  exact OrbIntH.den_eq_one_of_eq_intCast hM

end S_ModularCurve_JHPlaceSpecialization_den_twistCircleDeg_eq_one_of_inertiaStable_of_annulus
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_den_twistCircleDeg_eq_one_of_inertiaStable_of_annulus (solution)
