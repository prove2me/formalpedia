-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.ProlongationDatum.mem_integers_and_residue_mem_and_mem_of_mem_cuspChartSetInf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/ec2745ed-6a92-5457-ab78-719d795c3727

import Theorems.Thm_ModularCurve_isCurveOver_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_ModularPolynomialData_exists_monic_eval2_inv_div_pow_eq_zero_and_map_eq_X_pow_mul_X_sub_one
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_JHCuspChartSet
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_integers_and_residue_mem_and_mem_of_mem_cuspChartSetInf
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

namespace Ws47
namespace ZeroN
theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) [NeZero n]
    (x : LaurentSeries R) : coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk, map_zero]
theorem coeffEmb_jqModC (L : Type*) [Field L] [Algebra ℚ L] :
    coeffEmb L (jqModC ℚ) = jqModC L := by
  rw [coeffEmb, coeffMap_jqModC]
end Ws47.ZeroN

namespace Ws47
namespace D3a

open AlgebraicCurve IsLocalRing

theorem mem_of_monic {E : Type*} [Field E] (O : ValuationSubring E) {T : Type*} [CommRing T]
    (g : T →+* E) (hg : ∀ t, g t ∈ O) {x : E} {p : Polynomial T} (hp : p.Monic) (hx : Polynomial.eval₂ g x p = 0) :
    x ∈ O := by
  let g' : T →+* O := g.codRestrict O hg
  have hcomp : (algebraMap O E).comp g' = g := RingHom.ext fun t => rfl
  have hint : IsIntegral O x := by
    refine ⟨p.map g', hp.map g', ?_⟩
    rw [Polynomial.eval₂_map, hcomp]
    exact hx
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hy]
  exact y.2

theorem residue_mem_of_monic {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb] {k : Type*} [Field k] [Algebra k Fb]
    (R : RegularProlongation A F Fb) (v : Place k Fb) {T : Type*} [CommRing T] (g : T →+* F)
    (hgI : ∀ t, g t ∈ R.integers) (hgv : ∀ t, (R.residue ⟨g t, hgI t⟩ : Fb) ∈ v.toValuationSubring)
    {x : F} (hx : x ∈ R.integers) {p : Polynomial T} (hp : p.Monic) (hroot : Polynomial.eval₂ g x p = 0) :
    (R.residue ⟨x, hx⟩ : Fb) ∈ v.toValuationSubring := by
  let g₁ : T →+* R.integers := g.codRestrict R.integers hgI
  have h2 : (R.integers.subtype).comp g₁ = g := RingHom.ext fun t => rfl
  have h1 : Polynomial.eval₂ g₁ ⟨x, hx⟩ p = 0 := by
    apply Subtype.ext
    show R.integers.subtype (Polynomial.eval₂ g₁ ⟨x, hx⟩ p) = 0
    rw [Polynomial.hom_eval₂, h2]
    exact hroot
  have h3 : Polynomial.eval₂ (R.residue.comp g₁) (R.residue ⟨x, hx⟩) p = 0 := by
    rw [← Polynomial.hom_eval₂, h1, map_zero]
  exact mem_of_monic v.toValuationSubring (R.residue.comp g₁) hgv hp h3

theorem inv_mem_of_ord_le_zero {K F : Type*} [Field K] [Field F] [Algebra K F] (W : Place K F) {x : F}
    (hx0 : x ≠ 0) (h : W.ord x ≤ 0) : x⁻¹ ∈ W.toValuationSubring := by
  rcases W.toValuationSubring.mem_or_inv_mem x with hx | hx
  ·
    have hle : W.adicValuation x ≤ 1 := by
      rw [show x = ((⟨x, hx⟩ : W.toValuationSubring) : F) from rfl, W.adicValuation_coe]
      exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
    have hne : W.adicValuation x ≠ 0 := W.adicValuation_ne_zero hx0
    have hge : 0 ≤ W.ord x := by
      unfold Place.ord
      have : WithZero.log (W.adicValuation x) ≤ 0 := by
        rw [WithZero.log_le_iff_le_exp hne, WithZero.exp_zero]; exact hle
      omega
    have h0 : W.ord x = 0 := le_antisymm h hge
    have hval : W.adicValuation x = 1 := by
      unfold Place.ord at h0
      have hlog : WithZero.log (W.adicValuation x) = 0 := by omega
      rw [← WithZero.exp_log hne, hlog, WithZero.exp_zero]
    have hu : IsUnit (⟨x, hx⟩ : W.toValuationSubring) := (W.adicValuation_coe_eq_one_iff ⟨x, hx⟩).mp hval
    obtain ⟨b, hb⟩ := hu.exists_right_inv
    have hb' : x * (b : F) = 1 := by
      have := congrArg (fun t : W.toValuationSubring => (t : F)) hb
      simpa using this
    rw [← eq_inv_of_mul_eq_one_right hb']
    exact b.2
  · exact hx

end Ws47.D3a

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα : α.IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (hx' : ((x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (t : ↥(xHFunctionFieldBar M H))
    (ht : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((t : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) * ((jqModC (AlgebraicClosure ℚ))⁻¹) ^ p)
    (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hvna : ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) v)
    (hcuspv : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα W = v →
      (JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A)) W)
    (s : ↥(xHFunctionFieldBar M H)) (hs : s ∈ (JHPlaceSpecialization.cuspChartSetInf (p := p) A α x' t)) :
    ∃ h₁ : s ∈ Rpd.R₁.integers,
      (Rpd.R₁.residue ⟨s, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) ∈ v.toValuationSubring ∧
      ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα W = v → s ∈ W.toValuationSubring := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  let G : ↥(xHFunctionFieldBar M H) → Prop := fun s => s ∈ Rpd.R₁.integers ∧
    (∀ h : s ∈ Rpd.R₁.integers, (Rpd.R₁.residue ⟨s, h⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) ∈ v.toValuationSubring) ∧
    ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα W = v → s ∈ W.toValuationSubring
  have hG_out : ∀ s, G s → ∃ h₁ : s ∈ Rpd.R₁.integers,
      (Rpd.R₁.residue ⟨s, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) ∈ v.toValuationSubring ∧
      ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα W = v → s ∈ W.toValuationSubring :=
    fun s ⟨h₁, hv, hW⟩ => ⟨h₁, hv h₁, hW⟩

  have hG_const : ∀ a : (AlgebraicClosure ℚ), a ∈ A → G (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) a) := by
    intro a ha
    refine ⟨(Rpd.R₁.algebraMap_mem_iff _).mpr ha, fun h => ?_, fun W _ => W.algebraMap_mem' _⟩
    have : (⟨algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) a, h⟩ : ↥Rpd.R₁.integers) =
        ⟨algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((⟨a, ha⟩ : ↥A) : (AlgebraicClosure ℚ)), (Rpd.R₁.algebraMap_mem_iff _).mpr ha⟩ := rfl
    rw [this, Rpd.R₁.residue_algebraMap]
    exact v.algebraMap_mem' _

  have hG_add : ∀ s t, G s → G t → G (s + t) := by
    rintro s t ⟨hs₁, hsv, hsW⟩ ⟨ht₁, htv, htW⟩
    refine ⟨add_mem hs₁ ht₁, fun h => ?_, fun W hW => add_mem (hsW W hW) (htW W hW)⟩
    have : (⟨s + t, h⟩ : ↥Rpd.R₁.integers) = ⟨s, hs₁⟩ + ⟨t, ht₁⟩ := rfl
    rw [this, map_add]; exact add_mem (hsv hs₁) (htv ht₁)
  have hG_mul : ∀ s t, G s → G t → G (s * t) := by
    rintro s t ⟨hs₁, hsv, hsW⟩ ⟨ht₁, htv, htW⟩
    refine ⟨mul_mem hs₁ ht₁, fun h => ?_, fun W hW => mul_mem (hsW W hW) (htW W hW)⟩
    have : (⟨s * t, h⟩ : ↥Rpd.R₁.integers) = ⟨s, hs₁⟩ * ⟨t, ht₁⟩ := rfl
    rw [this, map_mul]; exact mul_mem (hsv hs₁) (htv ht₁)
  have hG_neg : ∀ s, G s → G (-s) := by
    rintro s ⟨hs₁, hsv, hsW⟩
    refine ⟨neg_mem hs₁, fun h => ?_, fun W hW => neg_mem (hsW W hW)⟩
    have : (⟨-s, h⟩ : ↥Rpd.R₁.integers) = -⟨s, hs₁⟩ := rfl
    rw [this, map_neg]; exact neg_mem (hsv hs₁)
  have hG_pow : ∀ s (n : ℕ), G s → G (s ^ n) := by
    intro s n hs
    induction n with
    | zero => rw [pow_zero]; simpa using hG_const 1 (one_mem A)
    | succ n ih => rw [pow_succ]; exact hG_mul _ _ ih hs

  have hG_root : ∀ {T : Type} [CommRing T] (g : T →+* ↥(xHFunctionFieldBar M H)) (hg : ∀ z, G (g z)) {x : ↥(xHFunctionFieldBar M H)} {P : Polynomial T},
      P.Monic → Polynomial.eval₂ g x P = 0 → G x := by
    intro T _ g hg x P hPm hroot
    have hgI : ∀ z, g z ∈ Rpd.R₁.integers := fun z => (hg z).1
    have hx₁ : x ∈ Rpd.R₁.integers := Ws47.D3a.mem_of_monic Rpd.R₁.integers g hgI hPm hroot
    refine ⟨hx₁, fun h => ?_, fun W hW => ?_⟩
    · exact Ws47.D3a.residue_mem_of_monic Rpd.R₁ v g hgI (fun z => (hg z).2.1 (hgI z)) h hPm hroot
    · exact Ws47.D3a.mem_of_monic W.toValuationSubring g (fun z => (hg z).2.2 W hW) hPm hroot

  have hjMcoe : ((α x' : ↥(xHFunctionFieldBar M H)) : (LaurentSeries (AlgebraicClosure ℚ))) = jqModC (AlgebraicClosure ℚ) := by rw [hα_coe, hx']
  have hyA : coeffMap A.subtype (jqModC ↥A) = jqModC (AlgebraicClosure ℚ) := coeffMap_jqModC _
  have hymem : coeffMap A.subtype (jqModC ↥A) ∈ xHFunctionFieldBar M H := by
    rw [hyA, ← hjMcoe]; exact (α x').2
  obtain ⟨hj₁', hres₁'⟩ := Rpd.residue₁_coeffMap (jqModC ↥A) hymem
  have heqx : (⟨coeffMap A.subtype (jqModC ↥A), hymem⟩ : ↥(xHFunctionFieldBar M H)) = α x' :=
    Subtype.ext (show coeffMap A.subtype (jqModC ↥A) = _ by rw [hyA, hjMcoe])
  have hj₁ : α x' ∈ Rpd.R₁.integers := heqx ▸ hj₁'
  have hres₁ser : ((Rpd.R₁.residue ⟨α x', hj₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A) := by
    have : (⟨α x', hj₁⟩ : ↥Rpd.R₁.integers) = ⟨_, hj₁'⟩ := Subtype.ext heqx.symm
    rw [this, hres₁', coeffMap_jqModC]
  have hres₁ne : Rpd.R₁.residue ⟨α x', hj₁⟩ ≠ 0 := by
    intro h0
    have : ((Rpd.R₁.residue ⟨α x', hj₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) = ((0 : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) := by rw [h0]
    rw [hres₁ser, ZeroMemClass.coe_zero] at this
    exact jqModC_ne_zero_of_nontrivial (ResidueField ↥A) this
  have hj0 : jqModC (AlgebraicClosure ℚ) ≠ 0 := jqModC_ne_zero_of_nontrivial (AlgebraicClosure ℚ)
  have hjM0 : (α x' : ↥(xHFunctionFieldBar M H)) ≠ 0 := by
    intro h0
    have : ((α x' : ↥(xHFunctionFieldBar M H)) : (LaurentSeries (AlgebraicClosure ℚ))) = ((0 : ↥(xHFunctionFieldBar M H)) : (LaurentSeries (AlgebraicClosure ℚ))) := by rw [h0]
    rw [hjMcoe, ZeroMemClass.coe_zero] at this
    exact hj0 this
  have hG_jinv : G (α x')⁻¹ := by
    have hu : IsUnit (⟨α x', hj₁⟩ : ↥Rpd.R₁.integers) := Rpd.R₁.isUnit_of_residue_ne_zero hres₁ne
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have hw' : (α x' : ↥(xHFunctionFieldBar M H)) * (w : ↥(xHFunctionFieldBar M H)) = 1 := by
      have := congrArg (fun z : ↥Rpd.R₁.integers => (z : ↥(xHFunctionFieldBar M H))) hw
      simpa using this
    have hwinv : (w : ↥(xHFunctionFieldBar M H)) = (α x')⁻¹ := eq_inv_of_mul_eq_one_right hw'
    have hinv₁ : (α x')⁻¹ ∈ Rpd.R₁.integers := hwinv ▸ w.2
    refine ⟨hinv₁, fun h => ?_, fun W hW => ?_⟩
    · have hres : Rpd.R₁.residue ⟨(α x')⁻¹, h⟩ = (Rpd.R₁.residue ⟨α x', hj₁⟩)⁻¹ := by
        have hwh : (⟨(α x')⁻¹, h⟩ : ↥Rpd.R₁.integers) = w := Subtype.ext hwinv.symm
        rw [hwh]
        exact eq_inv_of_mul_eq_one_right (by rw [← map_mul, hw, map_one])
      rw [hres]
      rcases v.toValuationSubring.mem_or_inv_mem (Rpd.R₁.residue ⟨α x', hj₁⟩) with hm | hm
      · exfalso
        apply hvna
        haveI : AlgebraicCurve.IsCurveOver (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) :=
          ModularCurve.isCurveOver_qExpFunctionFieldC_of_isAlgClosed (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) (translation_mem_GammaH _ _)
        haveI : Module.Finite (ResidueField ↥A) v.ResidueField := AlgebraicCurve.IsCurveOver.finiteResidue v
        have hsurj : Function.Surjective (algebraMap (ResidueField ↥A) v.ResidueField) := IsSepClosed.algebraMap_surjective _ _
        obtain ⟨a, ha, -⟩ := v.exists_hasValue_of_surjective hsurj hm
        exact ⟨_, a, hres₁ser, ha⟩
      · exact hm
    · have h0 : W.ord (α x') ≤ 0 := by
        have := hcuspv W hW (α x') hjMcoe 0
        simpa using this
      exact Ws47.D3a.inv_mem_of_ord_le_zero W hjM0 h0

  rcases hs with ⟨s₀, hs₀, rfl⟩ | ⟨a, rfl⟩
  ·
    letI instA : Algebra ↥A ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) := ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))).comp A.subtype).toAlgebra
    have hs₀' : IsIntegral ↥(Algebra.adjoin ↥A ({x'⁻¹} : Set ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) s₀ := hs₀
    obtain ⟨P, hPm, hP⟩ := hs₀'
    let g : ↥(Algebra.adjoin ↥A ({x'⁻¹} : Set ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) →+* ↥(xHFunctionFieldBar M H) :=
      α.toRingHom.comp (algebraMap ↥(Algebra.adjoin ↥A ({x'⁻¹} : Set ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    have hroot : Polynomial.eval₂ g (α s₀) P = 0 := by
      have := congrArg α.toRingHom hP
      rwa [Polynomial.hom_eval₂, map_zero] at this
    have hg : ∀ z, G (g z) := by
      rintro ⟨z, hz⟩
      show G (α z)
      induction hz using Algebra.adjoin_induction with
      | mem y hy =>
        rw [Set.mem_singleton_iff] at hy
        subst hy
        rw [map_inv₀]; exact hG_jinv
      | algebraMap a =>
        show G (α (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ))))
        rw [α.commutes]; exact hG_const _ a.2
      | add y z _ _ hy hz => rw [map_add]; exact hG_add _ _ hy hz
      | mul y z _ _ hy hz => rw [map_mul]; exact hG_mul _ _ hy hz
    exact hG_out _ (hG_root g hg hPm hroot)
  ·
    suffices hGt : G t by
      apply hG_out
      show G (t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ))
      rw [sub_eq_add_neg]
      exact hG_add _ _ hGt (hG_neg _ (hG_const _ a.2))
    obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData p
    obtain ⟨Q, hQm, -, hQi, -⟩ :=
      ModularCurve.ModularPolynomialData.exists_monic_eval2_inv_div_pow_eq_zero_and_map_eq_X_pow_mul_X_sub_one.{0, 0} p data

    have hΦ : data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries (AlgebraicClosure ℚ))) (jqModC (AlgebraicClosure ℚ))) (jqNModC (AlgebraicClosure ℚ) p) = 0 := by
      have h := congrArg (coeffEmb (AlgebraicClosure ℚ)) data.eval_eq_zero
      rw [Polynomial.hom_eval₂, map_zero] at h
      have hcomp : (coeffEmb (AlgebraicClosure ℚ)).comp evalAtJ = Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries (AlgebraicClosure ℚ))) (jqModC (AlgebraicClosure ℚ)) := by
        refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
        rw [RingHom.comp_apply, evalAtJ_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
        exact Ws47.ZeroN.coeffEmb_jqModC (AlgebraicClosure ℚ)
      have hN : coeffEmb (AlgebraicClosure ℚ) (jqN p) = jqNModC (AlgebraicClosure ℚ) p := by
        rw [jqN, coeffEmb, Ws47.ZeroN.coeffMap_qExpand, ← coeffEmb]
        show qExpand (AlgebraicClosure ℚ) p (coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ)) = _
        rw [Ws47.ZeroN.coeffEmb_jqModC]; rfl
      rwa [hcomp, hN] at h
    have hQL := hQi (LaurentSeries (AlgebraicClosure ℚ)) (jqModC (AlgebraicClosure ℚ)) (jqNModC (AlgebraicClosure ℚ) p) hj0 hΦ

    let gt : Polynomial ℤ →+* ↥(xHFunctionFieldBar M H) := Polynomial.eval₂RingHom (Int.castRingHom ↥(xHFunctionFieldBar M H)) (α x')⁻¹
    have hroot : Polynomial.eval₂ gt t Q = 0 := by
      have hinj : Function.Injective (algebraMap ↥(xHFunctionFieldBar M H) (LaurentSeries (AlgebraicClosure ℚ))) := (algebraMap ↥(xHFunctionFieldBar M H) (LaurentSeries (AlgebraicClosure ℚ))).injective
      apply hinj
      rw [Polynomial.hom_eval₂, map_zero]
      have hcomp : (algebraMap ↥(xHFunctionFieldBar M H) (LaurentSeries (AlgebraicClosure ℚ))).comp gt = Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries (AlgebraicClosure ℚ))) (jqModC (AlgebraicClosure ℚ))⁻¹ := by
        refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
        simp only [gt, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, map_inv₀]
        show ((α x' : ↥(xHFunctionFieldBar M H)) : (LaurentSeries (AlgebraicClosure ℚ)))⁻¹ = _
        rw [hjMcoe]
      rw [hcomp]
      have htc : algebraMap ↥(xHFunctionFieldBar M H) (LaurentSeries (AlgebraicClosure ℚ)) t = jqNModC (AlgebraicClosure ℚ) p / jqModC (AlgebraicClosure ℚ) ^ p := by
        show ((t : ↥(xHFunctionFieldBar M H)) : (LaurentSeries (AlgebraicClosure ℚ))) = _
        rw [ht, div_eq_mul_inv, inv_pow]; rfl
      rw [htc]
      exact hQL
    have hgt : ∀ P : Polynomial ℤ, G (gt P) := by
      intro P
      induction P using Polynomial.induction_on with
      | C n =>
        show G (Polynomial.eval₂ (Int.castRingHom ↥(xHFunctionFieldBar M H)) (α x')⁻¹ (Polynomial.C n))
        rw [Polynomial.eval₂_C]
        have : (Int.castRingHom ↥(xHFunctionFieldBar M H)) n = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (n : (AlgebraicClosure ℚ)) := by simp
        rw [this]; exact hG_const _ (intCast_mem A n)
      | add P Q hP hQ => rw [map_add]; exact hG_add _ _ hP hQ
      | monomial n c _ =>
        show G (Polynomial.eval₂ (Int.castRingHom ↥(xHFunctionFieldBar M H)) (α x')⁻¹ (Polynomial.C c * Polynomial.X ^ (n + 1)))
        rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
        refine hG_mul _ _ ?_ (hG_pow _ _ hG_jinv)
        have : (Int.castRingHom ↥(xHFunctionFieldBar M H)) c = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : (AlgebraicClosure ℚ)) := by simp
        rw [this]; exact hG_const _ (intCast_mem A c)
    exact hG_root gt hgt hQm hroot

end S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_integers_and_residue_mem_and_mem_of_mem_cuspChartSetInf
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_integers_and_residue_mem_and_mem_of_mem_cuspChartSetInf (solution)
