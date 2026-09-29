-- Prove2me | solution 1 for ModularCurve.IgusaScheme.piFin_image_spans_chartAlg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/14393a75-e7d1-592e-98cb-6991039d078c

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_JacJ1_ChartAlgebra
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ValuationSubring_RatPlaceCenterHelpers
import Theorems.Thm_ModularCurve_IgusaScheme_exists_algHom_tensor_chartAlg_injective_isIntegrallyClosed
import Theorems.Thm_ModularCurve_IgusaScheme_chartRing_le_span_coeffEmb_chartAlg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_piFin_image_spans_chartAlg
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open scoped TensorProduct
p2m_open "IsLocalRing ModularCurve P2MW.S_ModularCurve_IgusaScheme_piFin_image_spans_chartAlg.ModularCurve ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_piFin_image_spans_chartAlg.ModularCurve.IgusaScheme ModularCurve.CharPModel AlgebraicCurve"

noncomputable section

namespace FibreIsoAux

theorem mem_of_isIntegral_of_mul_mem {T : Type*} [Field T] (R : Subring T) [IsIntegrallyClosed R]
    (x : T) (r₁ r₂ : R) (hr₁ : r₁ ≠ 0) (hx : (r₁ : T) * x = r₂) (hint : IsIntegral R x) : x ∈ R := by
  classical
  let K := FractionRing R
  have hinj : Function.Injective (algebraMap R T) := Subtype.val_injective
  let lift : K →+* T := IsFractionRing.lift hinj
  have hlift : ∀ r : R, lift (algebraMap R K r) = (r : T) := fun r => IsFractionRing.lift_algebraMap hinj r
  have hliftinj : Function.Injective lift := lift.injective

  let z : K := algebraMap R K r₂ / algebraMap R K r₁
  have hr₁K : algebraMap R K r₁ ≠ 0 :=
    fun h => hr₁ ((IsFractionRing.injective R K) (by rw [h, map_zero]))
  have hz : lift z = x := by
    have hr₁T : (r₁ : T) ≠ 0 := fun h => hr₁ (Subtype.ext h)
    rw [map_div₀, hlift, hlift]
    field_simp
    rw [← hx, mul_comm]

  have hzint : IsIntegral R z := by
    obtain ⟨p, hp, hpx⟩ := hint
    refine ⟨p, hp, ?_⟩
    apply hliftinj
    rw [Polynomial.hom_eval₂, hz, map_zero]
    have : lift.comp (algebraMap R K) = algebraMap R T := RingHom.ext hlift
    rw [this]
    exact hpx
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hzint
  have : (r : T) = x := by rw [← hlift r, hr, hz]
  rw [← this]
  exact r.2

end FibreIsoAux

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme modularFunctionFieldFull jqModC modularFunctionFieldC jqModC_mem coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange CharPModel.FibreModel IgusaScheme.exists_algHom_tensor_chartAlg_injective_isIntegrallyClosed IgusaScheme.chartRing_le_span_coeffEmb_chartAlg"
namespace IgusaScheme
p2m_export "ModularCurve.IgusaScheme" "chartAlgFin jChartFin exists_algHom_tensor_chartAlg_injective_isIntegrallyClosed chartRing_le_span_coeffEmb_chartAlg"
namespace FibreIsoK
p2m_open "ModularCurve.IgusaScheme ModularCurve"

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
variable (A : ValuationSubring (AlgebraicClosure ℚ)) [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) ↥A]

set_option quotPrecheck false in
local notation "ℤℓ" => ↥(GaloisRep.ratLocalizedAt ℓ)
set_option quotPrecheck false in
local notation "Qb" => AlgebraicClosure ℚ
set_option quotPrecheck false in
local notation "FN" => ↥(modularFunctionFieldFull N)
set_option quotPrecheck false in
local notation "TT" => ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
set_option quotPrecheck false in
local notation "kA" => ResidueField ↥A

section Generic

variable (S : Subalgebra ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N))

def AS : Type := ↥A ⊗[ℤℓ] S

scoped instance : CommRing (AS N ℓ A S) := Algebra.TensorProduct.instCommRing
scoped instance : Algebra ↥A (AS N ℓ A S) := Algebra.TensorProduct.leftAlgebra

def asEquiv : (↥A ⊗[ℤℓ] S) ≃ₐ[↥A] AS N ℓ A S := AlgEquiv.refl

variable [Algebra ↥A ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))]

omit [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) ↥A] in

theorem exists_denom (s : Finset Qb) : ∃ d : ↥A, d ≠ 0 ∧ ∀ q ∈ s, (d : Qb) * q ∈ A := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, fun q hq => absurd hq (by simp)⟩
  | insert q s hqs ih =>
    obtain ⟨d, hd0, hd⟩ := ih
    rcases A.mem_or_inv_mem q with hq | hq
    · refine ⟨d, hd0, fun r hr => ?_⟩
      rcases Finset.mem_insert.mp hr with rfl | hr
      · exact A.mul_mem _ _ d.2 hq
      · exact hd r hr
    · by_cases hq0 : q = 0
      · refine ⟨d, hd0, fun r hr => ?_⟩
        rcases Finset.mem_insert.mp hr with rfl | hr
        · rw [hq0, mul_zero]; exact A.zero_mem
        · exact hd r hr
      · refine ⟨⟨(d : Qb) * q⁻¹, A.mul_mem _ _ d.2 hq⟩, ?_, fun r hr => ?_⟩
        · intro h
          have h' : (d : Qb) * q⁻¹ = 0 := congrArg Subtype.val h
          rcases mul_eq_zero.mp h' with h1 | h1
          · exact hd0 (Subtype.ext h1)
          · exact hq0 (inv_eq_zero.mp h1)
        · rcases Finset.mem_insert.mp hr with rfl | hr
          · change (d : Qb) * r⁻¹ * r ∈ A
            rw [inv_mul_cancel_right₀ hq0]
            exact d.2
          · change (d : Qb) * q⁻¹ * r ∈ A
            rw [mul_assoc, mul_comm q⁻¹, ← mul_assoc]
            exact A.mul_mem _ _ (hd r hr) hq

def embS (b : S) : TT :=
  ⟨coeffEmb Qb ((b : FN) : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange Qb (b : FN).2⟩

omit [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) ↥A] in
@[scoped simp] theorem coe_embS (b : S) :
    (embS N ℓ S b : LaurentSeries Qb) = coeffEmb Qb ((b : FN) : LaurentSeries ℚ) := rfl

theorem b1 (ψ : AS N ℓ A S →ₐ[↥A] TT) (hIC : IsIntegrallyClosed ↥ψ.range)
    (hψ : ∀ (a : ↥A) (b : S), ψ (asEquiv N ℓ A S (a ⊗ₜ b)) = algebraMap ↥A TT a * embS N ℓ S b)
    (hcT : ∀ a : ↥A, algebraMap ↥A TT a = constantsHom N A a)
    (g : TT)
    (base : Subring TT) (hbase : base ≤ (Algebra.adjoin Qb ({g} : Set TT)).toSubring)
    (hbase' : ∀ x ∈ base, ∃ t, ψ t = x)
    (B : Subring TT)
    (hBint : ∀ b : ↥B, ∃ p : Polynomial ↥base, p.Monic ∧ Polynomial.eval₂ base.subtype (b : TT) p = 0)
    (hSB : ∀ b : S, embS N ℓ S b ∈ B) (hconstB : ∀ a : ↥A, constantsHom N A a ∈ B)
    (hspan : (CurveModel.chartRing Qb ({g} : Set TT)).toSubmodule ≤
      Submodule.span Qb (Set.range (embS N ℓ S))) :
    ∀ x : TT, x ∈ B ↔ ∃ t, ψ t = x := by
  classical
  have hconst : ∀ a : ↥A, algebraMap ↥A TT a = algebraMap Qb TT (a : Qb) := fun a => by
    rw [hcT]; rfl
  intro x
  constructor
  · intro hxB

    obtain ⟨p, hp, hpx⟩ := hBint ⟨x, hxB⟩
    let incl : ↥base →+* ↥(Algebra.adjoin Qb ({g} : Set TT)) :=
      { toFun := fun y => ⟨y, hbase y.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
        map_zero' := rfl, map_add' := fun _ _ => rfl }
    have hint : IsIntegral (Algebra.adjoin Qb ({g} : Set TT)) x := by
      refine ⟨p.map incl, hp.map incl, ?_⟩
      rw [Polynomial.eval₂_map]
      exact hpx
    have hxchart : x ∈ CurveModel.chartRing Qb ({g} : Set TT) := hint

    have hxspan : x ∈ Submodule.span Qb (Set.range (embS N ℓ S)) := hspan hxchart
    obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp hxspan

    obtain ⟨d, hd0, hd⟩ := exists_denom A (c.support.image c)
    have hdc : ∀ b ∈ c.support, (d : Qb) * c b ∈ A := fun b hb => hd _ (Finset.mem_image_of_mem c hb)

    have hy : ∃ t, ψ t = algebraMap ↥A TT d * x := by
      refine ⟨asEquiv N ℓ A S (∑ b ∈ c.support.attach,
        (⟨(d : Qb) * c b.1, hdc b.1 b.2⟩ : ↥A) ⊗ₜ (b.1 : S)), ?_⟩
      have e1 : ψ (asEquiv N ℓ A S (∑ b ∈ c.support.attach,
          (⟨(d : Qb) * c b.1, hdc b.1 b.2⟩ : ↥A) ⊗ₜ (b.1 : S))) =
          ∑ b ∈ c.support.attach, algebraMap ↥A TT d * (c b.1 • embS N ℓ S b.1) := by
        rw [map_sum, map_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [hψ, Algebra.smul_def, ← mul_assoc, hconst, hconst]
        congr 1
        change algebraMap Qb TT ((d : Qb) * c b.1) = _
        rw [map_mul]
      have e2 : algebraMap ↥A TT d * x =
          ∑ b ∈ c.support.attach, algebraMap ↥A TT d * (c b.1 • embS N ℓ S b.1) := by
        rw [← hc, Finsupp.sum, Finset.mul_sum]
        exact (Finset.sum_attach c.support (fun b => algebraMap ↥A TT d * (c b • embS N ℓ S b))).symm
      exact e1.trans e2.symm

    let R : Subring TT := ψ.range.toSubring
    haveI : IsIntegrallyClosed ↥R := hIC
    have hd_mem : algebraMap ↥A TT d ∈ R := ⟨algebraMap ↥A _ d, ψ.commutes d⟩
    obtain ⟨t, ht⟩ := hy
    have hy_mem : algebraMap ↥A TT d * x ∈ R := ⟨t, ht⟩
    have hr₁ : (⟨algebraMap ↥A TT d, hd_mem⟩ : ↥R) ≠ 0 := by
      intro h
      have h' : algebraMap ↥A TT d = 0 := congrArg Subtype.val h
      rw [hconst] at h'
      exact hd0 (Subtype.ext ((algebraMap Qb TT).injective (h'.trans (map_zero _).symm)))
    let incl' : ↥base →+* ↥R :=
      { toFun := fun y => ⟨y, by obtain ⟨t, ht⟩ := hbase' y y.2; exact ⟨t, ht⟩⟩,
        map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }
    have hintR : IsIntegral ↥R x := by
      refine ⟨p.map incl', hp.map incl', ?_⟩
      rw [Polynomial.eval₂_map]
      exact hpx
    have hxR : x ∈ R := FibreIsoAux.mem_of_isIntegral_of_mul_mem R x ⟨algebraMap ↥A TT d, hd_mem⟩
      ⟨algebraMap ↥A TT d * x, hy_mem⟩ hr₁ rfl hintR
    exact hxR
  · rintro ⟨t, rfl⟩
    change ψ t ∈ B
    induction t using TensorProduct.induction_on with
    | zero =>
      convert B.zero_mem
      exact map_zero ψ
    | tmul a b =>
      have := hψ a b
      change ψ (a ⊗ₜ b) = _ at this
      rw [this, hcT]
      exact B.mul_mem (hconstB a) (hSB b)
    | add x y hx hy =>
      convert B.add_mem hx hy using 1
      exact map_add ψ x y

theorem b4 (B base : Subring TT) (hbaseB : base ≤ B) (g : TT)
    (hbase_le : base ≤ Subring.closure (Set.range (constantsHom N A) ∪ {g}))
    (hgen : Set.range (constantsHom N A) ∪ {g} ⊆ (base : Set TT))
    (hBint : ∀ b : ↥B, ∃ p : Polynomial ↥base, p.Monic ∧ Polynomial.eval₂ base.subtype (b : TT) p = 0)
    (Lk : Type) [Field Lk] [Algebra kA Lk] (π : ↥B →+* Lk) (h : Lk)
    (hgB : g ∈ B) (hπg : π ⟨g, hgB⟩ = h)
    (hcB : ∀ a : ↥A, constantsHom N A a ∈ B)
    (hπc : ∀ a : ↥A, π ⟨constantsHom N A a, hcB a⟩ = algebraMap kA Lk (residue ↥A a))
    (hIC : ∀ y : Lk, (∃ p : Polynomial ↥π.range, p.Monic ∧ Polynomial.eval₂ π.range.subtype y p = 0) →
      y ∈ π.range) :
    ∀ y : Lk, y ∈ π.range ↔ IsIntegral (Algebra.adjoin kA ({h} : Set Lk)) y := by
  classical
  set R₀ := Algebra.adjoin kA ({h} : Set Lk) with hR₀
  have hsB : ∀ y ∈ Subring.closure (Set.range (constantsHom N A) ∪ {g}), y ∈ B :=
    fun y hy => hbaseB (Subring.closure_le.mpr hgen hy)

  have hland : ∀ (y : TT) (hy : y ∈ Subring.closure (Set.range (constantsHom N A) ∪ {g}))
      (hyB : y ∈ B), π ⟨y, hyB⟩ ∈ R₀ := by
    intro y hy
    induction hy using Subring.closure_induction with
    | mem y hy =>
      intro hyB
      rcases hy with ⟨a, rfl⟩ | hy
      · rw [show π ⟨constantsHom N A a, hyB⟩ = π ⟨constantsHom N A a, hcB a⟩ from rfl, hπc]
        exact Subalgebra.algebraMap_mem _ _
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        rw [show π ⟨y, hyB⟩ = π ⟨y, hgB⟩ from rfl, hπg]
        exact Algebra.subset_adjoin rfl
    | zero => intro hyB; rw [show (⟨0, hyB⟩ : ↥B) = 0 from rfl, map_zero]; exact zero_mem _
    | one => intro hyB; rw [show (⟨1, hyB⟩ : ↥B) = 1 from rfl, map_one]; exact one_mem _
    | add x z hx hz ihx ihz =>
      intro hB
      rw [show (⟨x + z, hB⟩ : ↥B) = ⟨x, hsB x hx⟩ + ⟨z, hsB z hz⟩ from rfl, map_add]
      exact add_mem (ihx _) (ihz _)
    | neg x hx ihx =>
      intro hB
      rw [show (⟨-x, hB⟩ : ↥B) = -⟨x, hsB x hx⟩ from rfl, map_neg]
      exact neg_mem (ihx _)
    | mul x z hx hz ihx ihz =>
      intro hB
      rw [show (⟨x * z, hB⟩ : ↥B) = ⟨x, hsB x hx⟩ * ⟨z, hsB z hz⟩ from rfl, map_mul]
      exact mul_mem (ihx _) (ihz _)

  let inclB : ↥base →+* ↥B :=
    { toFun := fun x => ⟨x, hbaseB x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  let φ : ↥base →+* ↥R₀ :=
    (π.comp inclB).codRestrict R₀ (fun x => hland x (hbase_le x.2) (hbaseB x.2))
  intro y
  constructor
  · rintro ⟨b, rfl⟩
    obtain ⟨p, hp, hpb⟩ := hBint b
    have hrelB : Polynomial.eval₂ inclB b p = 0 := by
      apply Subtype.val_injective
      change B.subtype (Polynomial.eval₂ inclB b p) = ((0 : ↥B) : TT)
      rw [Polynomial.hom_eval₂]
      exact hpb
    refine ⟨p.map φ, hp.map φ, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap ↥R₀ Lk).comp φ = π.comp inclB := RingHom.ext fun _ => rfl
    rw [hcomp, ← Polynomial.hom_eval₂, hrelB, map_zero]
  · intro hy

    have hconst : ∀ x : kA, algebraMap kA Lk x ∈ π.range := by
      intro x
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
      exact ⟨⟨constantsHom N A a, hcB a⟩, hπc a⟩
    let πS : Subalgebra kA Lk :=
      { π.range with algebraMap_mem' := hconst }
    have hle : R₀ ≤ πS := Algebra.adjoin_le (by rintro _ rfl; exact ⟨⟨g, hgB⟩, hπg⟩)
    let ι : ↥R₀ →+* ↥π.range :=
      { toFun := fun x => ⟨x, hle x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
        map_zero' := rfl, map_add' := fun _ _ => rfl }
    obtain ⟨p, hp, hpy⟩ := hy
    refine hIC y ⟨p.map ι, hp.map ι, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : π.range.subtype.comp ι = algebraMap ↥R₀ Lk := RingHom.ext fun _ => rfl
    rw [hcomp]
    exact hpy

end Generic

def rhoPlace (hA : A.LiesOverPrime ℓ) : ℤℓ →+* ↥A :=
  ((algebraMap ℚ Qb).comp (algebraMap ℤℓ ℚ)).codRestrict A (fun x => by
    refine ValuationSubring.algebraMap_rat_mem_of_not_dvd_den (q := ℓ) Fact.out hA (fun hd => ?_)
    have hcop : (x : ℚ).den.Coprime ℓ := x.2
    exact (Fact.out : ℓ.Prime).one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop.symm hd))

omit [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) ↥A] in
theorem subtype_comp_rhoPlace (hA : A.LiesOverPrime ℓ) :
    A.subtype.comp (rhoPlace ℓ A hA) = algebraMap ℤℓ Qb :=
  RingHom.ext fun _ => rfl

omit [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) ↥A] in
theorem liesOverPrime_of_charP [CharP kA ℓ] : A.LiesOverPrime ℓ := by
  change ((ℓ : ℕ) : Qb) ∈ A.nonunits
  have h1 : ((ℓ : ℕ) : Qb) = (((ℓ : ℕ) : ↥A) : Qb) := by push_cast; rfl
  rw [h1, ValuationSubring.coe_mem_nonunits_iff, ← IsLocalRing.residue_eq_zero_iff, map_natCast]
  exact CharP.cast_eq_zero kA ℓ

omit [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) ↥A] in

theorem pifin_main (hℓN : ¬ ℓ ∣ N) [CharP kA ℓ]
    (fm : CharPModel.FibreModel N A ℓ kA (residue ↥A))
    (hsubF : ∀ b : ↥(chartAlgFin N ℓ),
      (⟨coeffEmb Qb ((b : FN) : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange Qb (b : FN).2⟩ : TT) ∈ fm.BFin) :
    ∀ z : ↥(modularFunctionFieldC kA N),
      z ∈ AlgebraicCurve.CurveModel.chartRing kA
        ({⟨jqModC kA, jqModC_mem kA N⟩} : Set ↥(modularFunctionFieldC kA N)) →
      ∃ (n : ℕ) (c : Fin n → kA) (b : Fin n → ↥(chartAlgFin N ℓ)),
        z = ∑ i, algebraMap kA ↥(modularFunctionFieldC kA N) (c i) * fm.piFin ⟨_, hsubF (b i)⟩ := by
  classical
  have hA : A.LiesOverPrime ℓ := liesOverPrime_of_charP ℓ A
  let ρ := rhoPlace ℓ A hA
  letI i1 : Algebra ℤℓ ↥A := ρ.toAlgebra
  letI i2 : Algebra ↥A TT := (constantsHom N A).toAlgebra
  obtain ⟨⟨ψ, hψ, hinj, -, hIC⟩, -⟩ :=
    ModularCurve.IgusaScheme.exists_algHom_tensor_chartAlg_injective_isIntegrallyClosed N ℓ hℓN A hA ρ
      (subtype_comp_rhoPlace ℓ A hA)
  obtain ⟨hspan, -⟩ := ModularCurve.IgusaScheme.chartRing_le_span_coeffEmb_chartAlg N ℓ
  have hcT : ∀ a : ↥A, algebraMap ↥A TT a = constantsHom N A a := fun a => rfl
  have hψ' : ∀ (a : ↥A) (b : ↥(chartAlgFin N ℓ)),
      ψ (asEquiv N ℓ A (chartAlgFin N ℓ) (a ⊗ₜ b)) = algebraMap ↥A TT a * embS N ℓ (chartAlgFin N ℓ) b := by
    intro a b
    apply Subtype.ext
    exact hψ a b

  have hbaseB : affineBaseFin N A ≤ fm.BFin := by
    rw [affineBaseFin, Subring.closure_le]
    rintro y (⟨a, rfl⟩ | hy)
    · exact fm.constFin_mem a
    · rw [Set.mem_singleton_iff] at hy; subst hy; exact fm.jBar_mem
  have hbase_adj : affineBaseFin N A ≤ (Algebra.adjoin Qb ({jBar N} : Set TT)).toSubring := by
    rw [affineBaseFin, Subring.closure_le]
    rintro y (⟨a, rfl⟩ | hy)
    · exact Subalgebra.algebraMap_mem _ (a : Qb)
    · rw [Set.mem_singleton_iff] at hy; subst hy
      exact Algebra.subset_adjoin rfl
  have hg : ψ (asEquiv N ℓ A (chartAlgFin N ℓ) ((1 : ↥A) ⊗ₜ jChartFin N ℓ)) = jBar N := by
    rw [hψ', map_one, one_mul]
    exact Subtype.ext rfl
  have hbase' : ∀ x ∈ affineBaseFin N A, ∃ t, ψ t = x := by
    intro x hx
    have hcl : affineBaseFin N A ≤ ψ.range.toSubring := by
      rw [affineBaseFin, Subring.closure_le]
      rintro y (⟨a, rfl⟩ | hy)
      · exact ⟨algebraMap ↥A _ a, by change ψ (algebraMap ↥A _ a) = _; rw [ψ.commutes, hcT]⟩
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact ⟨_, hg⟩
    exact hcl hx

  have hB : ∀ x : TT, x ∈ fm.BFin ↔ ∃ t, ψ t = x :=
    b1 N ℓ A (chartAlgFin N ℓ) ψ hIC hψ' hcT (jBar N) (affineBaseFin N A) hbase_adj hbase' fm.BFin
      fm.integralFin hsubF fm.constFin_mem hspan

  have hR := b4 (N := N) (A := A) (B := fm.BFin) (base := affineBaseFin N A) (hbaseB := hbaseB) (g := jBar N)
    (hbase_le := le_rfl) (hgen := Subring.subset_closure) (hBint := fm.integralFin)
    (Lk := ↥(modularFunctionFieldC kA N)) (π := fm.piFin) (h := ⟨jqModC kA, jqModC_mem kA N⟩)
    (hgB := fm.jBar_mem) (hπg := fm.piFin_j) (hcB := fm.constFin_mem) (hπc := fm.piFin_const)
    (hIC := fm.intClosed_piFin)

  let Pr : AS N ℓ A (chartAlgFin N ℓ) →+* ↥(modularFunctionFieldC kA N) :=
    fm.piFin.comp (ψ.toRingHom.codRestrict fm.BFin (fun t => (hB _).mpr ⟨t, rfl⟩))
  have hPr : ∀ (a : ↥A) (b : ↥(chartAlgFin N ℓ)),
      Pr (asEquiv N ℓ A (chartAlgFin N ℓ) (a ⊗ₜ b)) =
        algebraMap kA ↥(modularFunctionFieldC kA N) (residue ↥A a) * fm.piFin ⟨_, hsubF b⟩ := by
    intro a b
    have h1 : (ψ.toRingHom.codRestrict fm.BFin (fun t => (hB _).mpr ⟨t, rfl⟩))
        (asEquiv N ℓ A (chartAlgFin N ℓ) (a ⊗ₜ b)) =
        (⟨constantsHom N A a, fm.constFin_mem a⟩ : ↥fm.BFin) * ⟨_, hsubF b⟩ := by
      apply Subtype.ext
      change ψ (asEquiv N ℓ A (chartAlgFin N ℓ) (a ⊗ₜ b)) = constantsHom N A a * embS N ℓ (chartAlgFin N ℓ) b
      rw [hψ', hcT]
    change fm.piFin _ = _
    refine (congrArg fm.piFin h1).trans ?_
    rw [map_mul, fm.piFin_const]
  intro z hz
  rw [CurveModel.mem_chartRing_iff] at hz
  obtain ⟨⟨x, hxB⟩, rfl⟩ := (hR z).mpr hz
  obtain ⟨t, ht⟩ := (hB x).mp hxB
  have hzt : fm.piFin ⟨x, hxB⟩ = Pr t := by
    change _ = fm.piFin _
    congr 1
    exact Subtype.ext ht.symm

  obtain ⟨s, hs⟩ := TensorProduct.exists_finset ((asEquiv N ℓ A (chartAlgFin N ℓ)).symm t)
  have ht' : t = ∑ i ∈ s, asEquiv N ℓ A (chartAlgFin N ℓ) (i.1 ⊗ₜ i.2) := by
    rw [← map_sum, ← hs, AlgEquiv.apply_symm_apply]
  refine ⟨s.card, fun i => residue ↥A (s.equivFin.symm i).1.1, fun i => (s.equivFin.symm i).1.2, ?_⟩
  rw [hzt, ht', map_sum]
  rw [← Finset.sum_coe_sort s, ← Equiv.sum_comp s.equivFin.symm]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact hPr _ _

end ModularCurve.IgusaScheme.FibreIsoK
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_piFin_image_spans_chartAlg.ModularCurve P2MW.S_ModularCurve_IgusaScheme_piFin_image_spans_chartAlg.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_piFin_image_spans_chartAlg.ModularCurve.IgusaScheme.FibreIsoK"
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_piFin_image_spans_chartAlg.ModularCurve P2MW.S_ModularCurve_IgusaScheme_piFin_image_spans_chartAlg.ModularCurve.IgusaScheme"
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_piFin_image_spans_chartAlg.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_piFin_image_spans_chartAlg.ModularCurve P2MW.S_ModularCurve_IgusaScheme_piFin_image_spans_chartAlg.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_piFin_image_spans_chartAlg.ModularCurve.IgusaScheme.FibreIsoK"

open IsLocalRing _root_.ModularCurve _root_.P2MW.S_ModularCurve_IgusaScheme_piFin_image_spans_chartAlg.ModularCurve _root_.ModularCurve.IgusaScheme _root_.P2MW.S_ModularCurve_IgusaScheme_piFin_image_spans_chartAlg.ModularCurve.IgusaScheme ModularCurve.CharPModel AlgebraicCurve in
theorem solution (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓp : ¬ ℓ ∣ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) ℓ]
    (fm : CharPModel.FibreModel p A ℓ (ResidueField ↥A) (residue ↥A))
    (hsubF : ∀ b : ↥(chartAlgFin p ℓ),
      (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (b : ↥(modularFunctionFieldFull p)).2⟩ :
        laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) ∈ fm.BFin) :
    ∀ z : modularFunctionFieldC (ResidueField ↥A) p,
      z ∈ AlgebraicCurve.CurveModel.chartRing (ResidueField ↥A)
        ({⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) p⟩} :
          Set (modularFunctionFieldC (ResidueField ↥A) p)) →
      ∃ (n : ℕ) (c : Fin n → ResidueField ↥A) (b : Fin n → ↥(chartAlgFin p ℓ)),
        z = ∑ i, algebraMap (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) p) (c i) *
          fm.piFin ⟨_, hsubF (b i)⟩ :=
  ModularCurve.IgusaScheme.FibreIsoK.pifin_main p ℓ A hℓp fm hsubF

end S_ModularCurve_IgusaScheme_piFin_image_spans_chartAlg
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_piFin_image_spans_chartAlg (solution)
