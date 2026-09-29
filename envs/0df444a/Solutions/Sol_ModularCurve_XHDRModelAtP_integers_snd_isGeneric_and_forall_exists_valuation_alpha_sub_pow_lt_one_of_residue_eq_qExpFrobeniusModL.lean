-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.integers_snd_isGeneric_and_forall_exists_valuation_alpha_sub_pow_lt_one_of_residue_eq_qExpFrobeniusModL
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/c650b69a-0a9b-55b5-841e-b020bb6c9637

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_integers_comap_eq_integers_comap_of_residue_eq_qExpFrobeniusModL
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_qExpFrobeniusModL_eq_inv_qExpArithFrobC_smul_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_integers_snd_isGeneric_and_forall_exists_valuation_alpha_sub_pow_lt_one_of_residue_eq_qExpFrobeniusModL
p2m_attr_erase "simp" "ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

namespace Ws30IdentSZero

theorem qExpand_ne_zero {K : Type} [Field K] (N : ℕ) [NeZero N] {s : LaurentSeries K} (hs : s ≠ 0) : qExpand K N s ≠ 0 :=
  fun h => hs (qExpand_injective N (h.trans (map_zero _).symm))

theorem residue_eq_zero_iff {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fb : Type*} [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
    (R : RegularProlongation A F Fb) (f : F) (h : f ∈ R.integers) :
    R.residue ⟨f, h⟩ = 0 ↔ R.integers.valuation f < 1 := by
  rw [← RingHom.mem_ker, R.ker_residue]
  exact R.integers.valuation_lt_one_iff ⟨f, h⟩

theorem inv_mem_of_residue_ne_zero {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fb : Type*} [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
    (R : RegularProlongation A F Fb) (f : F) (h : f ∈ R.integers) (hr : R.residue ⟨f, h⟩ ≠ 0) :
    f⁻¹ ∈ R.integers := by
  have hlt : ¬ R.integers.valuation f < 1 := fun hh => hr ((residue_eq_zero_iff R f h).mpr hh)
  have hle : R.integers.valuation f ≤ 1 := (R.integers.valuation_le_one_iff f).mpr h
  have h1 : R.integers.valuation f = 1 := le_antisymm hle (not_lt.mp hlt)
  exact (R.integers.valuation_le_one_iff _).mp (by rw [map_inv₀, h1, inv_one])

theorem aeval_mem {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fb : Type*} [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
    (R : RegularProlongation A F Fb) (x : F) (hx : x ∈ R.integers) (Q : Polynomial ↥A) :
    Polynomial.aeval x (Q.map A.subtype) ∈ R.integers := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [Polynomial.map_add, map_add]
    exact add_mem hP hQ
  | monomial n a =>
    rw [Polynomial.map_monomial, Polynomial.aeval_monomial]
    exact mul_mem ((R.algebraMap_mem_iff (a : L)).mpr a.2) (pow_mem hx n)

theorem mem₁_iff_mem₂ (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hres₂α : ∀ (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h₁ : α v ∈ Rpd.R₁.integers) (h₂ : α v ∈ Rpd.R₂.integers),
      Rpd.R₂.residue ⟨α v, h₂⟩ = qExpFrobeniusModL (ResidueField ↥A) (ΓN p M H hpM) p (Rpd.R₁.residue ⟨α v, h₁⟩)) (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) :
    α v ∈ Rpd.R₁.integers ↔ α v ∈ Rpd.R₂.integers := by
  have h := ModularCurve.JHPlaceSpecialization.ProlongationDatum.integers_comap_eq_integers_comap_of_residue_eq_qExpFrobeniusModL
    p M H hpM A θ α Psp Rpd hres₂α
  have := SetLike.ext_iff.mp h v
  simp only [ValuationSubring.mem_comap] at this
  exact this.symm

theorem exists_alpha_eq (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (x : ↥(xHFunctionFieldBar M H))
    (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) :
    ∃ x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), α x' = x := by

  have hj' : jqModC ℚ ∈ xHFunctionField (M / p) (infSubgroup p M H hpM) := by
    show jqModC ℚ ∈ qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))
    exact qExpFunctionFieldC_mono ℚ le_top hj

  have hmem : jqModC (AlgebraicClosure ℚ) ∈ xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) := by
    have h := coeffEmb_mem_laurentBaseChange (L := AlgebraicClosure ℚ) hj'
    have he : coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ) = jqModC (AlgebraicClosure ℚ) := coeffMap_jqModC _
    rw [he] at h
    exact h
  refine ⟨⟨jqModC (AlgebraicClosure ℚ), hmem⟩, Subtype.ext ?_⟩
  rw [hα_coe, hx]

theorem x_mem₁ (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (x : ↥(xHFunctionFieldBar M H))
    (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) :
    ∃ h : x ∈ Rpd.R₁.integers,
      ((Rpd.R₁.residue ⟨x, h⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) =
        jqModC (ResidueField ↥A) := by
  have hmem : coeffMap A.subtype (jqModC ↥A) ∈ xHFunctionFieldBar M H := by
    rw [coeffMap_jqModC, ← hx]; exact x.2
  obtain ⟨h, hres⟩ := Rpd.residue₁_coeffMap (jqModC ↥A) hmem
  have hxe : (⟨coeffMap A.subtype (jqModC ↥A), hmem⟩ : ↥(xHFunctionFieldBar M H)) = x :=
    Subtype.ext (by show coeffMap A.subtype (jqModC ↥A) = (x : LaurentSeries (AlgebraicClosure ℚ)); rw [coeffMap_jqModC, hx])
  subst hxe
  exact ⟨h, by rw [hres, coeffMap_jqModC]⟩

theorem gen₂ (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hres₂α : ∀ (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h₁ : α v ∈ Rpd.R₁.integers) (h₂ : α v ∈ Rpd.R₂.integers),
      Rpd.R₂.residue ⟨α v, h₂⟩ = qExpFrobeniusModL (ResidueField ↥A) (ΓN p M H hpM) p (Rpd.R₁.residue ⟨α v, h₁⟩)) (x : ↥(xHFunctionFieldBar M H))
    (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) :
    ∀ Q : Polynomial ↥A, Q.map (IsLocalRing.residue ↥A) ≠ 0 →
      Polynomial.aeval x (Q.map A.subtype) ∈ Rpd.R₂.integers ∧ (Polynomial.aeval x (Q.map A.subtype))⁻¹ ∈ Rpd.R₂.integers := by
  intro Q hQ
  obtain ⟨x', hx'⟩ := exists_alpha_eq p M H hpM hj α hα_coe x hx
  obtain ⟨h₁, hres₁⟩ := x_mem₁ p M H hpM A θ Psp Rpd x hx
  have h₁' : α x' ∈ Rpd.R₁.integers := by rw [hx']; exact h₁
  have h₂' : α x' ∈ Rpd.R₂.integers := (mem₁_iff_mem₂ p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ θ hwgen Psp Rpd α hα_coe hres₂α x').mp h₁'
  have h₂ : x ∈ Rpd.R₂.integers := by rw [← hx']; exact h₂'
  have hmem : Polynomial.aeval x (Q.map A.subtype) ∈ Rpd.R₂.integers := aeval_mem Rpd.R₂ x h₂ Q
  refine ⟨hmem, inv_mem_of_residue_ne_zero Rpd.R₂ _ hmem ?_⟩

  set O := Rpd.R₂.integers with hO
  let ι : ↥A →+* ↥O := ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).comp A.subtype).codRestrict O
    (fun a => (Rpd.R₂.algebraMap_mem_iff (a : AlgebraicClosure ℚ)).mpr a.2)
  have hev : (⟨Polynomial.aeval x (Q.map A.subtype), hmem⟩ : ↥O) = Polynomial.eval₂ ι ⟨x, h₂⟩ Q := by
    apply Subtype.ext
    show Polynomial.aeval x (Q.map A.subtype) = O.subtype (Polynomial.eval₂ ι ⟨x, h₂⟩ Q)
    rw [Polynomial.hom_eval₂, Polynomial.aeval_def, Polynomial.eval₂_map]
    rfl

  have hresQ : Rpd.R₂.residue ⟨Polynomial.aeval x (Q.map A.subtype), hmem⟩ =
      Polynomial.eval₂ (Rpd.R₂.residue.comp ι) (Rpd.R₂.residue ⟨x, h₂⟩) Q := by
    rw [hev, Polynomial.hom_eval₂]
  have hι : Rpd.R₂.residue.comp ι = (algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).comp
      (IsLocalRing.residue ↥A) := by
    refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply]
    exact Rpd.R₂.residue_algebraMap a

  have hres₂x : ((Rpd.R₂.residue ⟨x, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) =
      qExpand (ResidueField ↥A) p (jqModC (ResidueField ↥A)) := by
    have e := hres₂α x' h₁' h₂'
    have e2 : (⟨α x', h₂'⟩ : ↥Rpd.R₂.integers) = ⟨x, h₂⟩ := Subtype.ext hx'
    have e1 : (⟨α x', h₁'⟩ : ↥Rpd.R₁.integers) = ⟨x, h₁⟩ := Subtype.ext hx'
    rw [e2, e1] at e
    rw [e, coe_qExpFrobeniusModL, hres₁]

  have hcoe : ((Rpd.R₂.residue ⟨Polynomial.aeval x (Q.map A.subtype), hmem⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) :
        LaurentSeries (ResidueField ↥A)) =
      qExpand (ResidueField ↥A) p (Polynomial.eval₂ (algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)))
        (jqModC (ResidueField ↥A)) (Q.map (IsLocalRing.residue ↥A))) := by
    rw [hresQ, hι]
    show algebraMap (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (LaurentSeries (ResidueField ↥A))
      (Polynomial.eval₂ ((algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).comp
        (IsLocalRing.residue ↥A)) (Rpd.R₂.residue ⟨x, h₂⟩) Q) = _
    rw [Polynomial.hom_eval₂ Q _ (algebraMap (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (LaurentSeries (ResidueField ↥A)))
      (Rpd.R₂.residue ⟨x, h₂⟩), Polynomial.eval₂_map,
      Polynomial.hom_eval₂ Q _ (qExpand (ResidueField ↥A) p) (jqModC (ResidueField ↥A))]
    have hX : algebraMap (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (LaurentSeries (ResidueField ↥A))
        (Rpd.R₂.residue ⟨x, h₂⟩) = qExpand (ResidueField ↥A) p (jqModC (ResidueField ↥A)) := hres₂x
    have hF : (algebraMap (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (LaurentSeries (ResidueField ↥A))).comp
          ((algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).comp (IsLocalRing.residue ↥A)) =
        (qExpand (ResidueField ↥A) p).comp ((algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A))).comp
          (IsLocalRing.residue ↥A)) := by
      refine RingHom.ext fun a => ?_
      simp only [RingHom.comp_apply]
      rw [← IsScalarTower.algebraMap_apply, algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]
    rw [hX, hF]

  intro h0
  have h0' := congrArg (fun z : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A) => (z : LaurentSeries (ResidueField ↥A))) h0
  simp only [ZeroMemClass.coe_zero] at h0'
  rw [hcoe] at h0'
  have hne : Polynomial.eval₂ (algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A))) (jqModC (ResidueField ↥A))
      (Q.map (IsLocalRing.residue ↥A)) ≠ 0 := by
    intro hz
    exact ModularCurve.transcendental_jqModC (ResidueField ↥A) ⟨Q.map (IsLocalRing.residue ↥A), hQ, hz⟩
  exact qExpand_ne_zero p hne h0'

theorem insep₂ (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hres₂α : ∀ (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h₁ : α v ∈ Rpd.R₁.integers) (h₂ : α v ∈ Rpd.R₂.integers),
      Rpd.R₂.residue ⟨α v, h₂⟩ = qExpFrobeniusModL (ResidueField ↥A) (ΓN p M H hpM) p (Rpd.R₁.residue ⟨α v, h₁⟩))
    (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h₂ : (α u : ↥(xHFunctionFieldBar M H)) ∈ Rpd.R₂.integers) :
    ∃ g : ↥(xHFunctionFieldBar M H), g ∈ Rpd.R₂.integers ∧ Rpd.R₂.integers.valuation (α u - g ^ p) < 1 := by
  have h₁ : α u ∈ Rpd.R₁.integers := (mem₁_iff_mem₂ p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ θ hwgen Psp Rpd α hα_coe hres₂α u).mpr h₂
  have hres := hres₂α u h₁ h₂
  haveI : PerfectField (ResidueField ↥A) := IsAlgClosed.perfectField _

  have hfrob := ModularCurve.qExpFrobeniusModL_eq_inv_qExpArithFrobC_smul_pow p (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM)
    (Rpd.R₁.residue ⟨α u, h₁⟩)

  obtain ⟨g, hg⟩ := Rpd.R₂.residue_surjective ((ModularCurve.qExpArithFrobC p (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM))⁻¹ • Rpd.R₁.residue ⟨α u, h₁⟩)
  refine ⟨(g : ↥(xHFunctionFieldBar M H)), g.2, ?_⟩
  have hmem : α u - (g : ↥(xHFunctionFieldBar M H)) ^ p ∈ Rpd.R₂.integers := sub_mem h₂ (pow_mem g.2 p)
  rw [← residue_eq_zero_iff Rpd.R₂ _ hmem]
  have hsub : (⟨α u - (g : ↥(xHFunctionFieldBar M H)) ^ p, hmem⟩ : ↥Rpd.R₂.integers) = ⟨α u, h₂⟩ - g ^ p :=
    Subtype.ext (by simp)
  rw [hsub, map_sub, map_pow, hg, sub_eq_zero]

  exact hres.trans hfrob

end Ws30IdentSZero

open Ws30IdentSZero in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)

    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))

    (hres₂α : ∀ (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h₁ : α v ∈ Rpd.R₁.integers) (h₂ : α v ∈ Rpd.R₂.integers),
      Rpd.R₂.residue ⟨α v, h₂⟩ = qExpFrobeniusModL (ResidueField ↥A) (ΓN p M H hpM) p (Rpd.R₁.residue ⟨α v, h₁⟩))

    (x : ↥(xHFunctionFieldBar M H)) (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) :

    ((∀ c : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) c ∈ Rpd.R₂.integers ↔ c ∈ A) ∧
        (∀ Q : Polynomial ↥A, Q.map (IsLocalRing.residue ↥A) ≠ 0 →
          Polynomial.aeval x (Q.map A.subtype) ∈ Rpd.R₂.integers ∧ (Polynomial.aeval x (Q.map A.subtype))⁻¹ ∈ Rpd.R₂.integers)) ∧

    (∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), (α u : ↥(xHFunctionFieldBar M H)) ∈ Rpd.R₂.integers → ∃ g : ↥(xHFunctionFieldBar M H), g ∈ Rpd.R₂.integers ∧ Rpd.R₂.integers.valuation (α u - g ^ p) < 1) := by
  refine ⟨⟨fun c => Rpd.R₂.algebraMap_mem_iff c, gen₂ p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ θ hwgen Psp Rpd α hα_coe hres₂α x hx⟩, ?_⟩
  intro u hu
  exact insep₂ p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ θ hwgen Psp Rpd α hα_coe hres₂α u hu

#print axioms solution

end S_ModularCurve_XHDRModelAtP_integers_snd_isGeneric_and_forall_exists_valuation_alpha_sub_pow_lt_one_of_residue_eq_qExpFrobeniusModL
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_integers_snd_isGeneric_and_forall_exists_valuation_alpha_sub_pow_lt_one_of_residue_eq_qExpFrobeniusModL (solution)
