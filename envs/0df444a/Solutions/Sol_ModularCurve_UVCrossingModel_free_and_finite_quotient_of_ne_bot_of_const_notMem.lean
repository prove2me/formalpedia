-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.free_and_finite_quotient_of_ne_bot_of_const_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/725effb5-cae5-5fc7-b73d-d3350bb6bbe9

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete
import Theorems.Thm_ModularCurve_UVCrossingModel_isNoetherianRing
import Theorems.Thm_ModularCurve_UVCrossingModel_moduleFinite_quotient_of_not_le_span_pair
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_free_and_finite_quotient_of_ne_bot_of_const_notMem

set_option autoImplicit false

universe u

p2m_open "ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_and_finite_quotient_of_ne_bot_of_const_notMem.ModularCurve ModularCurve.UVCrossingModel P2MW.S_ModularCurve_UVCrossingModel_free_and_finite_quotient_of_ne_bot_of_const_notMem.ModularCurve.UVCrossingModel IsLocalRing"

namespace ModularCurve
p2m_export "ModularCurve" "uvCrossingIdeal UVCrossingModel UVCrossingModel.isNoetherianRing"
namespace UVCrossingModel
p2m_export "ModularCurve.UVCrossingModel" "mk U V const constHom isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete isNoetherianRing moduleFinite_quotient_of_not_le_span_pair"
p2m_open "ModularCurve.UVCrossingModel ModularCurve"

variable {W : Type u} [CommRing W]

noncomputable def axisFun (π : W) (j : Fin 2) : Fin 2 → MvPowerSeries Unit (W ⧸ Ideal.span {π}) :=
  fun i => if i = j then MvPowerSeries.X () else 0

theorem hasSubst_axisFun (π : W) (j : Fin 2) : MvPowerSeries.HasSubst (axisFun π j) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by
    unfold axisFun
    split_ifs <;> simp)

noncomputable def axisHomAmbient (π : W) (j : Fin 2) :
    MvPowerSeries (Fin 2) W →ₐ[W] MvPowerSeries Unit (W ⧸ Ideal.span {π}) :=
  MvPowerSeries.substAlgHom (hasSubst_axisFun π j)

theorem axisHomAmbient_X (π : W) (j i : Fin 2) :
    axisHomAmbient π j (MvPowerSeries.X i) = axisFun π j i := by
  rw [axisHomAmbient, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X (hasSubst_axisFun π j)]

theorem axisHomAmbient_C (π : W) (j : Fin 2) (w : W) :
    axisHomAmbient π j (MvPowerSeries.C w) = MvPowerSeries.C (Ideal.Quotient.mk (Ideal.span {π}) w) := by
  rw [show (MvPowerSeries.C w : MvPowerSeries (Fin 2) W) = algebraMap W _ w from rfl, AlgHom.commutes,
    MvPowerSeries.algebraMap_apply]
  rfl

theorem axisHomAmbient_rel (θ π : W) (hdiv : π ∣ θ) (j : Fin 2) :
    axisHomAmbient π j (MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C θ) = 0 := by
  rw [map_sub, map_mul, axisHomAmbient_X, axisHomAmbient_X, axisHomAmbient_C,
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 hdiv), map_zero, sub_zero]
  unfold axisFun
  fin_cases j <;> simp

noncomputable def axisHom (θ π : W) (hdiv : π ∣ θ) (j : Fin 2) :
    UVCrossingModel W θ →+* MvPowerSeries Unit (W ⧸ Ideal.span {π}) :=
  Ideal.Quotient.lift (uvCrossingIdeal W θ) (axisHomAmbient π j).toRingHom (fun a ha => by
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, axisHomAmbient_rel θ π hdiv j, mul_zero])

theorem axisHom_mk (θ π : W) (hdiv : π ∣ θ) (j : Fin 2) (F : MvPowerSeries (Fin 2) W) :
    axisHom θ π hdiv j (mk θ F) = axisHomAmbient π j F :=
  Ideal.Quotient.lift_mk _ _ _

theorem axisHom_U (θ π : W) (hdiv : π ∣ θ) (j : Fin 2) : axisHom θ π hdiv j (U θ) = axisFun π j 0 := by
  rw [U, axisHom_mk, axisHomAmbient_X]

theorem axisHom_V (θ π : W) (hdiv : π ∣ θ) (j : Fin 2) : axisHom θ π hdiv j (V θ) = axisFun π j 1 := by
  rw [V, axisHom_mk, axisHomAmbient_X]

theorem axisHom_const (θ π : W) (hdiv : π ∣ θ) (j : Fin 2) (w : W) :
    axisHom θ π hdiv j (const θ w) = MvPowerSeries.C (Ideal.Quotient.mk (Ideal.span {π}) w) := by
  rw [const, axisHom_mk, axisHomAmbient_C]

theorem exists_isPrime_U_mem_const_mem_V_notMem (θ π : W) (hdiv : π ∣ θ) [IsDomain (W ⧸ Ideal.span {π})] :
    ∃ P : Ideal (UVCrossingModel W θ), P.IsPrime ∧ U θ ∈ P ∧ const θ π ∈ P ∧ V θ ∉ P := by
  refine ⟨RingHom.ker (axisHom θ π hdiv 1), RingHom.ker_isPrime _, ?_, ?_, ?_⟩
  · rw [RingHom.mem_ker, axisHom_U]; simp [axisFun]
  · rw [RingHom.mem_ker, axisHom_const, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self π), map_zero]
  · rw [RingHom.mem_ker, axisHom_V]
    simp only [axisFun, if_true]
    intro h
    have h1 := congrArg (MvPowerSeries.coeff (Finsupp.single () 1)) h
    rw [MvPowerSeries.coeff_X, map_zero, if_pos rfl] at h1
    exact one_ne_zero h1

theorem exists_isPrime_V_mem_const_mem_U_notMem (θ π : W) (hdiv : π ∣ θ) [IsDomain (W ⧸ Ideal.span {π})] :
    ∃ P : Ideal (UVCrossingModel W θ), P.IsPrime ∧ V θ ∈ P ∧ const θ π ∈ P ∧ U θ ∉ P := by
  refine ⟨RingHom.ker (axisHom θ π hdiv 0), RingHom.ker_isPrime _, ?_, ?_, ?_⟩
  · rw [RingHom.mem_ker, axisHom_V]; simp [axisFun]
  · rw [RingHom.mem_ker, axisHom_const, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self π), map_zero]
  · rw [RingHom.mem_ker, axisHom_U]
    simp only [axisFun, if_true]
    intro h
    have h1 := congrArg (MvPowerSeries.coeff (Finsupp.single () 1)) h
    rw [MvPowerSeries.coeff_X, map_zero, if_pos rfl] at h1
    exact one_ne_zero h1

end ModularCurve.UVCrossingModel

open _root_.ModularCurve.UVCrossingModel _root_.P2MW.S_ModularCurve_UVCrossingModel_free_and_finite_quotient_of_ne_bot_of_const_notMem.ModularCurve.UVCrossingModel in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3200000 in
theorem solution
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (Q : Ideal (UVCrossingModel W (π ^ E))) [Q.IsPrime] (hQ0 : Q ≠ ⊥) (hQπ : const (π ^ E) π ∉ Q) :
    Module.Free W (UVCrossingModel W (π ^ E) ⧸ Q) ∧ Module.Finite W (UVCrossingModel W (π ^ E) ⧸ Q) := by
  classical
  obtain ⟨hdom, hloc, -⟩ := isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete π hπ E hE
  haveI := hdom
  haveI := hloc
  haveI : IsNoetherianRing (UVCrossingModel W (π ^ E)) := UVCrossingModel.isNoetherianRing (π ^ E)
  haveI : IsDomain (W ⧸ Ideal.span {π}) :=
    (Ideal.Quotient.isDomain_iff_prime _).2
      ((Ideal.span_singleton_prime hπ.ne_zero).2 ((UniqueFactorizationMonoid.irreducible_iff_prime).1 hπ))
  have hE0 : E ≠ 0 := by omega
  have hdiv : π ∣ π ^ E := dvd_pow_self π hE0
  have hUV : U (π ^ E) * V (π ^ E) = const (π ^ E) π ^ E := by
    have h1 : const (π ^ E) π ^ E = const (π ^ E) (π ^ E) := (map_pow (constHom (π ^ E)) π E).symm
    rw [h1, ← sub_eq_zero]
    show mk (π ^ E) (MvPowerSeries.X 0) * mk (π ^ E) (MvPowerSeries.X 1) - mk (π ^ E) (MvPowerSeries.C (π ^ E)) = 0
    rw [← map_mul, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

  have key : ∀ p : Ideal (UVCrossingModel W (π ^ E)), p ∈ (Ideal.span {const (π ^ E) π}).minimalPrimes → ¬ Q ≤ p := by
    intro p hp hQp
    haveI hpP : p.IsPrime := hp.1.1
    have hph : p.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ p hp
    have hQne : Q ≠ p := by
      intro h; apply hQπ; rw [h]; exact hp.1.2 (Ideal.subset_span (Set.mem_singleton _))
    have hQlt : Q < p := lt_of_le_of_ne hQp hQne
    haveI : Q.FiniteHeight := ⟨Or.inr (ne_top_of_le_ne_top (by simp)
      ((Ideal.height_mono hQp).trans hph))⟩
    haveI : (⊥ : Ideal (UVCrossingModel W (π ^ E))).FiniteHeight := ⟨Or.inr (by rw [Ideal.height_bot]; simp)⟩
    have h1 : (⊥ : Ideal (UVCrossingModel W (π ^ E))).height < Q.height :=
      Ideal.height_strict_mono_of_isPrime (bot_lt_iff_ne_bot.mpr hQ0)
    have h2 : Q.height < p.height := Ideal.height_strict_mono_of_isPrime hQlt
    rw [Ideal.height_bot] at h1
    have h3 : Q.height < 1 := lt_of_lt_of_le h2 hph
    have h4 : Q.height = 0 := by
      have := ENat.lt_one_iff_eq_zero.mp h3; exact this
    rw [h4] at h1
    exact lt_irrefl _ h1

  have hQU : ¬ Q ≤ Ideal.span {const (π ^ E) π, U (π ^ E)} := by
    obtain ⟨P₁, hP₁, hUP, hcP, hVP⟩ := exists_isPrime_U_mem_const_mem_V_notMem (π ^ E) π hdiv
    haveI := hP₁
    obtain ⟨p, hp, hpP⟩ := Ideal.exists_minimalPrimes_le
      (show Ideal.span {const (π ^ E) π} ≤ P₁ from (Ideal.span_singleton_le_iff_mem _).mpr hcP)
    haveI hpP' : p.IsPrime := hp.1.1
    have hcp : const (π ^ E) π ∈ p := hp.1.2 (Ideal.subset_span (Set.mem_singleton _))
    have hUp : U (π ^ E) ∈ p := by
      have : U (π ^ E) * V (π ^ E) ∈ p := by rw [hUV]; exact Ideal.pow_mem_of_mem p hcp E (by omega)
      exact ((hpP'.mem_or_mem this).resolve_right fun hV => hVP (hpP hV))
    intro hle
    exact key p hp (hle.trans (Ideal.span_le.2 (by rintro z (rfl | rfl); exacts [hcp, hUp])))
  have hQV : ¬ Q ≤ Ideal.span {const (π ^ E) π, V (π ^ E)} := by
    obtain ⟨P₂, hP₂, hVP, hcP, hUP⟩ := exists_isPrime_V_mem_const_mem_U_notMem (π ^ E) π hdiv
    haveI := hP₂
    obtain ⟨p, hp, hpP⟩ := Ideal.exists_minimalPrimes_le
      (show Ideal.span {const (π ^ E) π} ≤ P₂ from (Ideal.span_singleton_le_iff_mem _).mpr hcP)
    haveI hpP' : p.IsPrime := hp.1.1
    have hcp : const (π ^ E) π ∈ p := hp.1.2 (Ideal.subset_span (Set.mem_singleton _))
    have hVp : V (π ^ E) ∈ p := by
      have : U (π ^ E) * V (π ^ E) ∈ p := by rw [hUV]; exact Ideal.pow_mem_of_mem p hcp E (by omega)
      exact ((hpP'.mem_or_mem this).resolve_left fun hU => hUP (hpP hU))
    intro hle
    exact key p hp (hle.trans (Ideal.span_le.2 (by rintro z (rfl | rfl); exacts [hcp, hVp])))
  haveI hfin : Module.Finite W (UVCrossingModel W (π ^ E) ⧸ Q) := moduleFinite_quotient_of_not_le_span_pair π hπ E hE Q hQU hQV

  have hQp : Q.IsPrime := inferInstance
  have hinj : Function.Injective ((Ideal.Quotient.mk Q).comp (algebraMap W (UVCrossingModel W (π ^ E)))) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    rw [RingHom.comp_apply] at ha
    by_contra ha0
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hπ
    rw [Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow] at ha
    rcases hQp.mem_or_mem ha with hu | hp
    · exact hQp.ne_top (Ideal.eq_top_of_isUnit_mem _ hu (u.isUnit.map (algebraMap W (UVCrossingModel W (π ^ E)))))
    · exact hQπ (hQp.mem_of_pow_mem n hp)
  haveI : Module.IsTorsionFree W (UVCrossingModel W (π ^ E) ⧸ Q) :=
    (Module.isTorsionFree_iff_algebraMap_injective (R := W) (A := UVCrossingModel W (π ^ E) ⧸ Q)).mpr
      (by rw [← Ideal.Quotient.mk_comp_algebraMap W Q]; exact hinj)
  exact ⟨Module.free_of_finite_type_torsion_free', hfin⟩

end S_ModularCurve_UVCrossingModel_free_and_finite_quotient_of_ne_bot_of_const_notMem
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_free_and_finite_quotient_of_ne_bot_of_const_notMem (solution)
