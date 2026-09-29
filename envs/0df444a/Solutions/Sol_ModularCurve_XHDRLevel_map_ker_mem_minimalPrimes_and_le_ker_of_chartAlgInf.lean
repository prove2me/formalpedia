-- Prove2me | solution 1 for ModularCurve.XHDRLevel.map_ker_mem_minimalPrimes_and_le_ker_of_chartAlgInf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/32061e1b-1706-587a-bef1-24da82777d30

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRLevel_map_ker_mem_minimalPrimes_and_le_ker_of_chartAlgInf

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve P2MW.S_ModularCurve_XHDRLevel_map_ker_mem_minimalPrimes_and_le_ker_of_chartAlgInf.ModularCurve ModularCurve.XHDRLevel"
p2m_open_scoped "MatrixGroups TensorProduct P2MW.S_ModularCurve_XHDRLevel_map_ker_mem_minimalPrimes_and_le_ker_of_chartAlgInf.TensorProduct"

noncomputable section

p2m_attr_erase "instance" "HahnSeries.powerSeriesAlgebra"

namespace TensorProduct p2m_export "TensorProduct" "map_tmul smul_tmul zero_tmul lift mk ext tmul map ext' Algebra.smul_def add_tmul mk_surjective tmul_sum" end TensorProduct
p2m_open_scoped "TensorProduct" in

theorem TensorProduct.mem_map_includeRight_of_map_mk_eq_zero
    {R A κ : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing κ] [Algebra R κ]
    (I : Ideal A) (t : κ ⊗[R] A)
    (ht : Algebra.TensorProduct.map (AlgHom.id κ κ) (Ideal.Quotient.mkₐ R I) t = 0) :
    t ∈ I.map (Algebra.TensorProduct.includeRight : A →ₐ[R] κ ⊗[R] A) := by
  let g : A →ₗ[R] A ⧸ I := (Ideal.Quotient.mkₐ R I).toLinearMap
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective
  have hex := lTensor_exact κ (LinearMap.exact_subtype_ker_map g) hg
  have hagree : ∀ s, Algebra.TensorProduct.map (AlgHom.id κ κ) (Ideal.Quotient.mkₐ R I) s = LinearMap.lTensor κ g s := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul c b => rw [Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have ht' : LinearMap.lTensor κ g t = 0 := by rw [← hagree, ht]
  obtain ⟨s, hs⟩ := (hex t).mp ht'
  rw [← hs]
  clear hs ht ht'
  induction s using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Ideal.zero_mem _
  | tmul c i =>
    rw [LinearMap.lTensor_tmul]
    have : (c ⊗ₜ[R] ((LinearMap.ker g).subtype i) : κ ⊗[R] A) = (c ⊗ₜ 1) * (1 ⊗ₜ (i : A)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]; rfl
    rw [this]
    have hi : (i : A) ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp (LinearMap.mem_ker.mp i.2)
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hi)
  | add x y hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy

namespace LaurentSeries
p2m_export "LaurentSeries" "algebraMap_apply linearIndependent_coeffMap"
namespace LDKappa
p2m_open "LaurentSeries"

variable {k κ : Type*} [Field k] [Field κ] [Algebra k κ]

theorem coeff_sum_smul_coeffMap {ι : Type*} (s : Finset ι) (c : ι → κ) (f : ι → LaurentSeries k) (n : ℤ) :
    (∑ i ∈ s, c i • coeffMap (algebraMap k κ) (f i)).coeff n = ∑ i ∈ s, c i * algebraMap k κ ((f i).coeff n) := by
  rw [HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [HahnSeries.coeff_smul, coeffMap_coeff, smul_eq_mul]

theorem eq_zero_of_sum_smul_coeffMap_eq_zero {ι : Type*} (f : ι → LaurentSeries k) (hf : LinearIndependent k f)
    (s : Finset ι) (c : ι → κ) (h : ∑ i ∈ s, c i • coeffMap (algebraMap k κ) (f i) = 0) :
    ∀ i ∈ s, c i = 0 := by
  classical

  let E := Module.Basis.ofVectorSpace k κ

  have hrel : ∀ b, ∑ i ∈ s, (E.repr (c i)) b • f i = 0 := by
    intro b
    ext n
    rw [HahnSeries.coeff_sum, HahnSeries.coeff_zero]
    simp only [HahnSeries.coeff_smul, smul_eq_mul]

    have hn := congrArg (fun x => HahnSeries.coeff x n) h
    simp only [coeff_sum_smul_coeffMap, HahnSeries.coeff_zero] at hn

    have hn' : ∑ i ∈ s, ((f i).coeff n) • c i = 0 := by
      rw [← hn]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, mul_comm]
    have := congrArg (fun x => E.repr x b) hn'
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => mul_comm _ _

  have hcoord : ∀ b, ∀ i ∈ s, (E.repr (c i)) b = 0 := fun b =>
    linearIndependent_iff'.mp hf s (fun i => (E.repr (c i)) b) (hrel b)
  intro i hi
  have : E.repr (c i) = 0 := by
    ext b
    exact hcoord b i hi
  exact E.repr.map_eq_zero_iff.mp this

private theorem _root_.LaurentSeries.linearIndependent_coeffMap {ι : Type*} (f : ι → LaurentSeries k)
    (hf : LinearIndependent k f) :
    LinearIndependent κ (fun i => coeffMap (algebraMap k κ) (f i)) := by
  rw [linearIndependent_iff']
  intro s c h
  exact eq_zero_of_sum_smul_coeffMap_eq_zero f hf s c h

p2m_alias "P2MW.S_ModularCurve_XHDRLevel_map_ker_mem_minimalPrimes_and_le_ker_of_chartAlgInf.LaurentSeries.linearIndependent_coeffMap" "LaurentSeries.linearIndependent_coeffMap"
end LaurentSeries.LDKappa

namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC jNum constantCoeff_jNum jNumQ constantCoeff_jNumQ ofPowerSeries_coeff_of_neg coeffMap coeffMap_coeff coeffMap_single coeffMap_ofPowerSeries jqModC coeff_jqModC_neg_one exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC"
namespace QPrime
p2m_open "ModularCurve"

scoped instance (p : ℕ) [hp : Fact p.Prime] : IsDiscreteValuationRing (R p) :=
  GaloisRep.isDiscreteValuationRing_ratLocalizedAt p hp.out

theorem maximalIdeal_eq (p : ℕ) [hp : Fact p.Prime] :
    IsLocalRing.maximalIdeal (R p) = Ideal.span {(p : R p)} :=
  GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast p hp.out

theorem residue_eq_zero_of_mem (p : ℕ) [hp : Fact p.Prime] {r : R p} (hr : r ∈ IsLocalRing.maximalIdeal (R p)) :
    GaloisRep.ratLocalizedAtResidue p r = 0 := by
  rw [maximalIdeal_eq, Ideal.mem_span_singleton] at hr
  obtain ⟨s, rfl⟩ := hr
  rw [map_mul, map_natCast, ZMod.natCast_self, zero_mul]

theorem isUnit_of_residue_ne_zero (p : ℕ) [hp : Fact p.Prime] {r : R p}
    (hr : GaloisRep.ratLocalizedAtResidue p r ≠ 0) : IsUnit r := by
  by_contra h
  exact hr (residue_eq_zero_of_mem p ((IsLocalRing.mem_maximalIdeal _).mpr h))

theorem exists_eq_mul_of_residue_eq_zero (p : ℕ) [hp : Fact p.Prime] {r : R p}
    (hr : GaloisRep.ratLocalizedAtResidue p r = 0) : ∃ s : R p, r = p * s := by
  have h : ¬ IsUnit r := fun hu => (hu.map (GaloisRep.ratLocalizedAtResidue p)).ne_zero hr
  have hm : r ∈ IsLocalRing.maximalIdeal (R p) := (IsLocalRing.mem_maximalIdeal _).mpr h
  rw [maximalIdeal_eq, Ideal.mem_span_singleton] at hm
  exact hm

abbrev psQ (p : ℕ) (x : PowerSeries (R p)) : LaurentSeries ℚ :=
  HahnSeries.ofPowerSeries ℤ ℚ (x.map (GaloisRep.ratLocalizedAt p).subtype)

theorem psQ_injective (p : ℕ) : Function.Injective (psQ p) := fun x y h =>
  PowerSeries.map_injective _ Subtype.coe_injective (HahnSeries.ofPowerSeries_injective h)

theorem subtype_comp_intCast (p : ℕ) :
    (GaloisRep.ratLocalizedAt p).subtype.comp (Int.castRingHom (R p)) = Int.castRingHom ℚ :=
  RingHom.ext_int _ _

theorem residue_comp_intCast (p : ℕ) [Fact p.Prime] :
    (GaloisRep.ratLocalizedAtResidue p).comp (Int.castRingHom (R p)) = Int.castRingHom (ZMod p) :=
  RingHom.ext_int _ _

theorem jqModC_rat_ne_zero : jqModC ℚ ≠ 0 := by
  intro h
  have := congrArg (fun s : LaurentSeries ℚ => s.coeff (-1)) h
  simp only [coeff_jqModC_neg_one, HahnSeries.coeff_zero] at this
  exact one_ne_zero this

theorem single_one_mul_jqModC :
    HahnSeries.single (1 : ℤ) (1 : ℚ) * jqModC ℚ = HahnSeries.ofPowerSeries ℤ ℚ (jNum.map (Int.castRingHom ℚ)) := by
  rw [jqModC, ← mul_assoc, HahnSeries.single_mul_single, add_neg_cancel, one_mul]
  exact one_mul _

theorem map_map_ps {A B C : Type*} [CommSemiring A] [CommSemiring B] [CommSemiring C] (f : A →+* B) (g : B →+* C)
    (x : PowerSeries A) : (x.map f).map g = x.map (g.comp f) := by
  ext n
  simp only [PowerSeries.coeff_map, RingHom.comp_apply]

theorem psQ_jNum (p : ℕ) : psQ p (jNum.map (Int.castRingHom (R p))) = HahnSeries.ofPowerSeries ℤ ℚ (jNum.map (Int.castRingHom ℚ)) := by
  rw [psQ, map_map_ps, subtype_comp_intCast]

theorem psQ_X (p : ℕ) : psQ p PowerSeries.X = HahnSeries.single (1 : ℤ) (1 : ℚ) := by
  rw [psQ, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]

theorem jNum_map_residue_ne_zero (p : ℕ) [Fact p.Prime] :
    (jNum.map (Int.castRingHom (R p))).map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 := by
  rw [map_map_ps, residue_comp_intCast]
  intro h
  have := congrArg PowerSeries.constantCoeff h
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
    constantCoeff_jNum, map_one, map_zero] at this
  exact one_ne_zero this

theorem coeff_zero_inv_jqModC : ((jqModC ℚ)⁻¹).coeff 0 = 0 := by
  have hu : jNumQ * jNumQ.invOfUnit 1 = 1 := PowerSeries.mul_invOfUnit _ _ (by rw [constantCoeff_jNumQ]; rfl)
  have hj : jqModC ℚ = HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℚ jNumQ := rfl
  have hinv : (jqModC ℚ)⁻¹ = HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.X * jNumQ.invOfUnit 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [hj, map_mul, HahnSeries.ofPowerSeries_X, mul_mul_mul_comm, HahnSeries.single_mul_single, neg_add_cancel, one_mul,
      ← map_mul, hu, map_one (HahnSeries.ofPowerSeries ℤ ℚ), mul_one]
    rfl
  rw [hinv, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_zero_X_mul]

theorem ringHom_ext_R (p : ℕ) [hp : Fact p.Prime] {T : Type*} [Semiring T] (f g : R p →+* T) : f = g := by
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := p) hp.out
  exact IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl (RingHom.ext_int _ _)

section Frame

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (p : ℕ) [hp : Fact p.Prime]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [Algebra (R p) κ]
    (red : ↥(chartAlgInf p Γ hj) →+* LaurentSeries κ)
    (hred : ∀ (b : ↥(chartAlgInf p Γ hj)) (y : LaurentSeries (R p)),
      coeffMap (algebraMap (R p) ℚ) y = ((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) →
        red b = coeffMap (algebraMap (R p) κ) y)
    (ev : κ ⊗[R p] ↥(chartAlgInf p Γ hj) →ₐ[κ] κ)
    (hev : ∀ b : ↥(chartAlgInf p Γ hj), ev (1 ⊗ₜ b) = (red b).coeff 0)

local instance instZModAlg : Algebra (ZMod p) κ := ZMod.algebra κ p

theorem algebraMap_R_eq : algebraMap (R p) κ = (algebraMap (ZMod p) κ).comp (GaloisRep.ratLocalizedAtResidue p) :=
  ringHom_ext_R p _ _

private def _root_.ModularCurve.QPrime.lift (b : ↥(chartAlgInf p Γ hj)) : LaurentSeries (R p) :=
  ((_root_.ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC (Γ := Γ) (p := p) (j := jAt Γ hj) (coe_jAt Γ hj)).2 b).choose

p2m_export "ModularCurve.QPrime" "lift"
theorem coeffMap_lift (b : ↥(chartAlgInf p Γ hj)) :
    coeffMap (algebraMap (R p) ℚ) (lift Γ p hj b) = ((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) :=
  ((_root_.ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC (Γ := Γ) (p := p) (j := jAt Γ hj) (coe_jAt Γ hj)).2 b).choose_spec

omit hp in
theorem coeffMap_R_injective : Function.Injective (coeffMap (algebraMap (R p) ℚ)) := by
  intro x y h
  ext k
  have := congrArg (fun s => HahnSeries.coeff s k) h
  simp only [coeffMap_coeff] at this
  exact this

theorem lift_unique (b : ↥(chartAlgInf p Γ hj)) (y : LaurentSeries (R p))
    (hy : coeffMap (algebraMap (R p) ℚ) y = ((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ)) :
    y = lift Γ p hj b :=
  coeffMap_R_injective p ((hy.trans (coeffMap_lift Γ p hj b).symm))

def liftHom : ↥(chartAlgInf p Γ hj) →+* LaurentSeries (R p) where
  toFun := lift Γ p hj
  map_one' := (lift_unique Γ p hj 1 1 (by rw [map_one]; rfl)).symm
  map_mul' x y := (lift_unique Γ p hj (x * y) _ (by rw [map_mul, coeffMap_lift, coeffMap_lift]; rfl)).symm
  map_zero' := (lift_unique Γ p hj 0 0 (by rw [map_zero]; rfl)).symm
  map_add' x y := (lift_unique Γ p hj (x + y) _ (by rw [map_add, coeffMap_lift, coeffMap_lift]; rfl)).symm

def ρ : ↥(chartAlgInf p Γ hj) →+* LaurentSeries (ZMod p) :=
  (coeffMap (GaloisRep.ratLocalizedAtResidue p)).comp (liftHom Γ p hj)

omit hp in
theorem coeffMap_comp {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) (x : LaurentSeries A) :
    coeffMap g (coeffMap f x) = coeffMap (g.comp f) x := by
  ext k; simp only [coeffMap_coeff, RingHom.comp_apply]

include hred in
theorem red_eq (b : ↥(chartAlgInf p Γ hj)) : red b = coeffMap (algebraMap (ZMod p) κ) (ρ Γ p hj b) := by
  rw [hred b (lift Γ p hj b) (coeffMap_lift Γ p hj b), algebraMap_R_eq, ρ, RingHom.comp_apply, coeffMap_comp]
  rfl

omit hp in
theorem coeffMap_field_injective {k K : Type*} [Field k] [Field K] (f : k →+* K) : Function.Injective (coeffMap f) := by
  intro x y h
  ext n
  have := congrArg (fun s => HahnSeries.coeff s n) h
  simp only [coeffMap_coeff] at this
  exact f.injective this

include hred in
theorem mem_ker_red_iff (b : ↥(chartAlgInf p Γ hj)) : b ∈ RingHom.ker red ↔ ρ Γ p hj b = 0 := by
  rw [RingHom.mem_ker, red_eq Γ p hj κ red hred]
  constructor
  · intro h; exact coeffMap_field_injective _ (h.trans (map_zero _).symm)
  · intro h; rw [h, map_zero]

scoped instance instTowerRLS : IsScalarTower (R p) κ (LaurentSeries κ) :=
  ⟨fun r c x => HahnSeries.ext (funext fun n => by
    simp only [HahnSeries.coeff_smul]
    exact smul_assoc r c (x.coeff n))⟩

omit hp [CharP κ p] [IsAlgClosed κ] in
theorem algebraMap_LS (r : R p) : algebraMap (R p) (LaurentSeries κ) r = HahnSeries.single 0 (algebraMap (R p) κ r) :=
  (HahnSeries.algebraMap_apply (Γ := ℤ) (R := R p) (A := κ) (r := r)).trans (HahnSeries.C_apply _)

scoped instance instTowerRLS' : @IsScalarTower (R p) κ (LaurentSeries κ) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  ⟨fun r c x => HahnSeries.ext (funext fun n => by
    simp only [HahnSeries.coeff_smul]
    exact smul_assoc r c (x.coeff n))⟩

include hred in

theorem red_algebraMap (r : R p) : red (algebraMap (R p) _ r) = algebraMap (R p) (LaurentSeries κ) r := by
  have hy : coeffMap (algebraMap (R p) ℚ) (HahnSeries.C r) =
      (((algebraMap (R p) ↥(chartAlgInf p Γ hj) r : ↥(chartAlgInf p Γ hj)) : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) := by
    rw [show (HahnSeries.C r : LaurentSeries (R p)) = HahnSeries.single 0 r from rfl, coeffMap_single]
    rfl
  rw [hred _ _ hy, show (HahnSeries.C r : LaurentSeries (R p)) = HahnSeries.single 0 r from rfl, coeffMap_single,
    algebraMap_LS]

def redₐ : ↥(chartAlgInf p Γ hj) →ₐ[R p] LaurentSeries κ :=
  { red with commutes' := red_algebraMap Γ p hj κ red hred }

def Φ : κ ⊗[R p] ↥(chartAlgInf p Γ hj) →ₐ[κ] LaurentSeries κ :=
  Algebra.TensorProduct.lift (Algebra.ofId κ (LaurentSeries κ)) (redₐ Γ p hj κ red hred) (fun _ _ => Commute.all _ _)

include hred in
theorem Φ_tmul (c : κ) (b : ↥(chartAlgInf p Γ hj)) : Φ Γ p hj κ red hred (c ⊗ₜ b) = algebraMap κ _ c * red b :=
  Algebra.TensorProduct.lift_tmul _ _ _ c b

def P0 : Ideal (κ ⊗[R p] ↥(chartAlgInf p Γ hj)) :=
  Ideal.map (Algebra.TensorProduct.includeRight : ↥(chartAlgInf p Γ hj) →ₐ[R p] κ ⊗[R p] ↥(chartAlgInf p Γ hj))
    (RingHom.ker red)

include hred in
theorem P0_le_kerΦ : P0 Γ p hj κ red ≤ RingHom.ker (Φ Γ p hj κ red hred) := by
  unfold P0
  rw [Ideal.map_le_iff_le_comap]
  intro b hb
  rw [Ideal.mem_comap, RingHom.mem_ker, Algebra.TensorProduct.includeRight_apply]
  show Φ Γ p hj κ red hred ((1 : κ) ⊗ₜ b) = 0
  rw [Φ_tmul, RingHom.mem_ker.mp hb, mul_zero]

include hev in

theorem P0_le_ker : P0 Γ p hj κ red ≤ RingHom.ker ev := by
  unfold P0
  rw [Ideal.map_le_iff_le_comap]
  intro b hb
  rw [Ideal.mem_comap, RingHom.mem_ker]
  show ev (1 ⊗ₜ b) = 0
  rw [hev, RingHom.mem_ker.mp hb, HahnSeries.coeff_zero]

include hred in

theorem comap_P0_le : (P0 Γ p hj κ red).comap
    (Algebra.TensorProduct.includeRight : ↥(chartAlgInf p Γ hj) →ₐ[R p] κ ⊗[R p] ↥(chartAlgInf p Γ hj)) ≤ RingHom.ker red := by
  intro b hb
  have h := P0_le_kerΦ Γ p hj κ red hred hb
  rw [RingHom.mem_ker, Algebra.TensorProduct.includeRight_apply, Φ_tmul, map_one, one_mul] at h
  exact h

def U : PowerSeries (R p) := PowerSeries.X * (jNum.map (Int.castRingHom (R p))).invOfUnit 1

theorem constantCoeff_jNum_map : PowerSeries.constantCoeff (jNum.map (Int.castRingHom (R p))) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
    constantCoeff_jNum, map_one]

theorem jNum_map_mul_invOfUnit : (jNum.map (Int.castRingHom (R p))) * (jNum.map (Int.castRingHom (R p))).invOfUnit 1 = 1 :=
  PowerSeries.mul_invOfUnit _ _ (by rw [constantCoeff_jNum_map]; rfl)

theorem coeff_U_zero : PowerSeries.coeff 0 (U p) = 0 := by
  rw [U, PowerSeries.coeff_zero_X_mul]

theorem coeff_U_one : PowerSeries.coeff 1 (U p) = 1 := by
  rw [U, show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have h := congrArg PowerSeries.constantCoeff (jNum_map_mul_invOfUnit p)
  rw [map_mul, constantCoeff_jNum_map, one_mul, map_one] at h
  exact h

theorem coeff_pow_of_coeff_zero_eq_zero {k : Type*} [CommRing k] (V : PowerSeries k) (hV0 : PowerSeries.coeff 0 V = 0)
    (i m : ℕ) : PowerSeries.coeff m (V ^ i) = if i ≤ m then PowerSeries.coeff (m - i) ((PowerSeries.mk fun n => PowerSeries.coeff (n + 1) V) ^ i) else 0 := by
  have hV : V = PowerSeries.X * PowerSeries.mk fun n => PowerSeries.coeff (n + 1) V := by
    have h := PowerSeries.eq_X_mul_shift_add_const V
    rw [show PowerSeries.constantCoeff V = 0 from by rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hV0], map_zero,
      add_zero] at h
    exact h
  conv_lhs => rw [hV, mul_pow]
  rw [PowerSeries.coeff_X_pow_mul']

theorem coeff_natTrailingDegree_eval₂ {k : Type*} [CommRing k] (Q : Polynomial k) (V : PowerSeries k)
    (hV0 : PowerSeries.coeff 0 V = 0) (hV1 : PowerSeries.coeff 1 V = 1) :
    PowerSeries.coeff Q.natTrailingDegree (Q.eval₂ (PowerSeries.C) V) = Q.trailingCoeff := by
  rcases eq_or_ne Q 0 with rfl | hQ
  · simp
  rw [Polynomial.eval₂_eq_sum_range, map_sum]
  rw [Finset.sum_eq_single Q.natTrailingDegree]
  · rw [PowerSeries.coeff_C_mul, coeff_pow_of_coeff_zero_eq_zero V hV0, if_pos le_rfl, Nat.sub_self,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow]
    rw [show PowerSeries.constantCoeff (PowerSeries.mk fun n => PowerSeries.coeff (n + 1) V) = 1 from by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, zero_add, hV1], one_pow, mul_one]
    rfl
  · intro i _ hi
    rcases lt_or_gt_of_ne hi with hlt | hgt
    · rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hlt, map_zero, zero_mul, map_zero]
    · rw [PowerSeries.coeff_C_mul, coeff_pow_of_coeff_zero_eq_zero V hV0, if_neg (not_le.mpr hgt), mul_zero]
  · intro h
    exfalso
    exact h (Finset.mem_range.mpr (Nat.lt_succ_of_le (Polynomial.natTrailingDegree_le_natDegree Q)))

theorem eval₂_ne_zero_of_map_ne_zero {k : Type*} [CommRing k] (Q : Polynomial k) (hQ : Q ≠ 0) (V : PowerSeries k)
    (hV0 : PowerSeries.coeff 0 V = 0) (hV1 : PowerSeries.coeff 1 V = 1) : Q.eval₂ (PowerSeries.C) V ≠ 0 := by
  intro h
  have := coeff_natTrailingDegree_eval₂ Q V hV0 hV1
  rw [h, map_zero] at this
  exact (Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hQ) this.symm

abbrev u : ↥(chartAlgInf p Γ hj) := TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)

theorem psQ_U' : psQ p (U p) = (((u Γ p hj : ↥(chartAlgInf p Γ hj)) : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) := by
  rw [TwoChartIntegralModel.coe_jInvChartInf]
  push_cast
  rw [coe_jAt]
  symm
  apply inv_eq_of_mul_eq_one_right
  have h1 : jqModC ℚ = HahnSeries.single (-1 : ℤ) 1 * psQ p (jNum.map (Int.castRingHom (R p))) := by
    rw [psQ_jNum]; rfl
  rw [h1, U, show psQ p (PowerSeries.X * (jNum.map (Int.castRingHom (R p))).invOfUnit 1) =
      psQ p PowerSeries.X * psQ p ((jNum.map (Int.castRingHom (R p))).invOfUnit 1) from by simp [psQ],
    psQ_X, mul_mul_mul_comm, HahnSeries.single_mul_single, neg_add_cancel, one_mul,
    show psQ p (jNum.map (Int.castRingHom (R p))) * psQ p ((jNum.map (Int.castRingHom (R p))).invOfUnit 1) =
      psQ p ((jNum.map (Int.castRingHom (R p))) * (jNum.map (Int.castRingHom (R p))).invOfUnit 1) from by simp [psQ],
    jNum_map_mul_invOfUnit]
  simp [psQ]

omit hp in
theorem coeffMap_ofPowerSeries {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (Y : PowerSeries A) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ A Y) = HahnSeries.ofPowerSeries ℤ B (Y.map f) := by
  ext k
  rw [coeffMap_coeff]
  rcases lt_or_ge k 0 with hk | hk
  · rw [ofPowerSeries_coeff_of_neg Y hk, ofPowerSeries_coeff_of_neg (Y.map f) hk, map_zero]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]

theorem lift_u : lift Γ p hj (u Γ p hj) = HahnSeries.ofPowerSeries ℤ (R p) (U p) :=
  (lift_unique Γ p hj _ _ (by rw [coeffMap_ofPowerSeries, ← psQ_U']; rfl)).symm

theorem ρ_u : ρ Γ p hj (u Γ p hj) = HahnSeries.ofPowerSeries ℤ (ZMod p) ((U p).map (GaloisRep.ratLocalizedAtResidue p)) := by
  rw [ρ, RingHom.comp_apply, show liftHom Γ p hj (u Γ p hj) = lift Γ p hj (u Γ p hj) from rfl, lift_u, coeffMap_ofPowerSeries]

theorem lift_algebraMap (r : R p) : lift Γ p hj (algebraMap (R p) _ r) = HahnSeries.C r :=
  (lift_unique Γ p hj _ _ (by
    rw [show (HahnSeries.C r : LaurentSeries (R p)) = HahnSeries.single 0 r from rfl, coeffMap_single]; rfl)).symm

theorem ρ_algebraMap (r : R p) : ρ Γ p hj (algebraMap (R p) _ r) = HahnSeries.C (GaloisRep.ratLocalizedAtResidue p r) := by
  rw [ρ, RingHom.comp_apply, show liftHom Γ p hj (algebraMap (R p) _ r) = lift Γ p hj (algebraMap (R p) _ r) from rfl,
    lift_algebraMap, show (HahnSeries.C r : LaurentSeries (R p)) = HahnSeries.single 0 r from rfl, coeffMap_single]
  rfl

theorem ρ_aeval (P : Polynomial (R p)) :
    ρ Γ p hj (Polynomial.aeval (u Γ p hj) P) =
      HahnSeries.ofPowerSeries ℤ (ZMod p)
        ((P.map (GaloisRep.ratLocalizedAtResidue p)).eval₂ PowerSeries.C ((U p).map (GaloisRep.ratLocalizedAtResidue p))) := by
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, ρ_u]
  have h1 : (ρ Γ p hj).comp (algebraMap (R p) ↥(chartAlgInf p Γ hj)) =
      ((HahnSeries.ofPowerSeries ℤ (ZMod p)).comp PowerSeries.C).comp (GaloisRep.ratLocalizedAtResidue p) := by
    refine RingHom.ext fun r => ?_
    rw [RingHom.comp_apply, ρ_algebraMap, RingHom.comp_apply, RingHom.comp_apply, HahnSeries.ofPowerSeries_C]
  rw [h1, ← Polynomial.eval₂_map, ← Polynomial.hom_eval₂]

include hred in

theorem aeval_not_mem_ker (P : Polynomial (R p)) (hP : P.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0) :
    Polynomial.aeval (u Γ p hj) P ∉ RingHom.ker red := by
  rw [mem_ker_red_iff Γ p hj κ red hred, ρ_aeval]
  intro h
  refine eval₂_ne_zero_of_map_ne_zero _ hP _ ?_ ?_ (HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm))
  · rw [PowerSeries.coeff_map, coeff_U_zero, map_zero]
  · rw [PowerSeries.coeff_map, coeff_U_one, map_one]

include hred in

theorem mem_span_of_mem_adjoin_of_mem_ker (g : ↥(chartAlgInf p Γ hj))
    (hgA : g ∈ Algebra.adjoin (R p) ({u Γ p hj} : Set ↥(chartAlgInf p Γ hj))) (hg : g ∈ RingHom.ker red) :
    g ∈ Ideal.span {(p : ↥(chartAlgInf p Γ hj))} := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hgA
  obtain ⟨P, hPg⟩ := hgA
  have hPbar : P.map (GaloisRep.ratLocalizedAtResidue p) = 0 := by
    by_contra hne
    exact aeval_not_mem_ker Γ p hj κ red hred P hne (by rw [show Polynomial.aeval (u Γ p hj) P = g from hPg]; exact hg)
  have hcoeff : ∀ n : ℕ, P.coeff n ∈ Ideal.span {(p : R p)} := fun n => by
    have h := congrArg (fun Q : Polynomial (ZMod p) => Q.coeff n) hPbar
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h
    obtain ⟨s, hs⟩ := exists_eq_mul_of_residue_eq_zero p h
    exact Ideal.mem_span_singleton.mpr ⟨s, hs⟩
  have hPmem : P ∈ Ideal.map Polynomial.C (Ideal.span {(p : R p)}) := Ideal.mem_map_C_iff.mpr hcoeff
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at hPmem
  obtain ⟨P₂, hP₂⟩ := hPmem
  refine Ideal.mem_span_singleton.mpr ⟨Polynomial.aeval (u Γ p hj) P₂, ?_⟩
  rw [← hPg, show (Polynomial.aeval (u Γ p hj) : Polynomial (R p) →ₐ[R p] _).toRingHom P = Polynomial.aeval (u Γ p hj) P from rfl,
    hP₂, map_mul, Polynomial.aeval_C, map_natCast]

include hred in

theorem ker_red_mem_minimalPrimes :
    RingHom.ker red ∈ (Ideal.span {(p : ↥(chartAlgInf p Γ hj))}).minimalPrimes := by
  haveI hprime : (RingHom.ker red).IsPrime := RingHom.ker_isPrime red
  have hpmem : (p : ↥(chartAlgInf p Γ hj)) ∈ RingHom.ker red := by
    rw [RingHom.mem_ker, map_natCast, ← map_natCast (algebraMap κ (LaurentSeries κ)) p, CharP.cast_eq_zero, map_zero]

  let A : Subalgebra (R p) ↥(chartAlgInf p Γ hj) := Algebra.adjoin (R p) ({u Γ p hj} : Set ↥(chartAlgInf p Γ hj))
  letI inst : Algebra ↥A ↥(chartAlgInf p Γ hj) := A.toAlgebra
  refine ⟨⟨hprime, (Ideal.span_singleton_le_iff_mem _).mpr hpmem⟩, ?_⟩
  rintro q' ⟨hq', hpq'⟩ hle
  by_contra hne
  obtain ⟨x, hxc, hxq⟩ := SetLike.not_le_iff_exists.mp hne

  have hint : IsIntegral ↥A x := by

    let val : ↥(chartAlgInf p Γ hj) →ₐ[R p] ↥(qExpFunctionFieldC ℚ Γ) := (chartAlgInf p Γ hj).val
    have hval : Function.Injective val := Subtype.coe_injective
    let e : ↥A ≃ₐ[R p] ↥(A.map val) := Subalgebra.equivMapOfInjective A val hval
    have hAF : A.map val = Algebra.adjoin (R p) ({((jAt Γ hj : ↥(qExpFunctionFieldC ℚ Γ)))⁻¹} : Set ↥(qExpFunctionFieldC ℚ Γ)) := by
      show Subalgebra.map val (Algebra.adjoin (R p) {u Γ p hj}) = _
      rw [AlgHom.map_adjoin, Set.image_singleton]
      rfl

    have hx : IsIntegral ↥(A.map val) (x : ↥(qExpFunctionFieldC ℚ Γ)) := by
      rw [hAF]; exact x.2
    obtain ⟨P, hPm, hP0⟩ := hx
    refine ⟨P.map (e.symm : ↥(A.map val) ≃ₐ[R p] ↥A).toAlgHom.toRingHom, hPm.map _, hval ?_⟩
    rw [map_zero, Polynomial.eval₂_map]
    have h := Polynomial.hom_eval₂ P ((algebraMap ↥A ↥(chartAlgInf p Γ hj)).comp
      (e.symm : ↥(A.map val) ≃ₐ[R p] ↥A).toAlgHom.toRingHom) val.toRingHom x
    have hcomp : val.toRingHom.comp ((algebraMap ↥A ↥(chartAlgInf p Γ hj)).comp
        (e.symm : ↥(A.map val) ≃ₐ[R p] ↥A).toAlgHom.toRingHom) = algebraMap ↥(A.map val) ↥(qExpFunctionFieldC ℚ Γ) := by
      refine RingHom.ext fun a => ?_
      obtain ⟨y, rfl⟩ := e.surjective a
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgEquiv.toAlgHom_eq_coe,
        AlgEquiv.coe_algHom, AlgEquiv.symm_apply_apply]
      rfl
    rw [hcomp] at h
    exact h.trans hP0
  haveI := hq'
  have key := Ideal.comap_lt_comap_of_integral_mem_sdiff (R := ↥A) hle ⟨hxc, hxq⟩ hint
  refine key.2 ?_
  intro g hg
  exact hpq' (mem_span_of_mem_adjoin_of_mem_ker Γ p hj κ red hred _ g.2 hg)

include hred in
theorem P0_le_of_prime_le (Q : Ideal (κ ⊗[R p] ↥(chartAlgInf p Γ hj))) [hQ : Q.IsPrime]
    (hle : Q ≤ P0 Γ p hj κ red) : P0 Γ p hj κ red ≤ Q := by

  set Qc := Q.comap (Algebra.TensorProduct.includeRight : ↥(chartAlgInf p Γ hj) →ₐ[R p] κ ⊗[R p] ↥(chartAlgInf p Γ hj))
    with hQc
  have hQc_prime : Qc.IsPrime := Ideal.comap_isPrime _ _
  have hp_mem : (p : ↥(chartAlgInf p Γ hj)) ∈ Qc := by
    rw [hQc, Ideal.mem_comap, map_natCast]
    have : ((p : ℕ) : κ ⊗[R p] ↥(chartAlgInf p Γ hj)) = 0 := by
      rw [← map_natCast (algebraMap κ (κ ⊗[R p] ↥(chartAlgInf p Γ hj))) p, CharP.cast_eq_zero, map_zero]
    rw [this]; exact Q.zero_mem
  have hQc_le : Qc ≤ RingHom.ker red := (Ideal.comap_mono hle).trans (comap_P0_le Γ p hj κ red hred)
  obtain ⟨hmin, hmin'⟩ := ker_red_mem_minimalPrimes Γ p hj κ red hred
  have heq : RingHom.ker red ≤ Qc := hmin' ⟨hQc_prime, (Ideal.span_singleton_le_iff_mem _).mpr hp_mem⟩ hQc_le

  unfold P0
  rw [Ideal.map_le_iff_le_comap]
  exact heq

abbrev Sbar : Type := ↥(chartAlgInf p Γ hj) ⧸ RingHom.ker red

def redbar : Sbar Γ p hj κ red →ₐ[R p] LaurentSeries κ :=
  Ideal.Quotient.liftₐ (RingHom.ker red) (redₐ Γ p hj κ red hred) (fun a ha => ha)

theorem redbar_mk (b : ↥(chartAlgInf p Γ hj)) :
    redbar Γ p hj κ red hred (Ideal.Quotient.mk (RingHom.ker red) b) = red b := rfl

def Φbar : κ ⊗[R p] Sbar Γ p hj κ red →ₐ[κ] LaurentSeries κ :=
  Algebra.TensorProduct.lift (Algebra.ofId κ (LaurentSeries κ)) (redbar Γ p hj κ red hred) (fun _ _ => Commute.all _ _)

theorem Φbar_tmul (c : κ) (s : Sbar Γ p hj κ red) :
    Φbar Γ p hj κ red hred (c ⊗ₜ s) = algebraMap κ _ c * redbar Γ p hj κ red hred s :=
  Algebra.TensorProduct.lift_tmul _ _ _ c s

def idmk : κ ⊗[R p] ↥(chartAlgInf p Γ hj) →ₐ[κ] κ ⊗[R p] Sbar Γ p hj κ red :=
  Algebra.TensorProduct.map (AlgHom.id κ κ) (Ideal.Quotient.mkₐ (R p) (RingHom.ker red))

include hred in
theorem Φ_eq_comp : Φ Γ p hj κ red hred = (Φbar Γ p hj κ red hred).comp (idmk Γ p hj κ red) := by
  refine Algebra.TensorProduct.ext' fun a b => ?_
  rw [Φ_tmul, AlgHom.comp_apply, idmk, Algebra.TensorProduct.map_tmul, Φbar_tmul]
  rfl

theorem mem_P0_of_idmk_eq_zero (t : κ ⊗[R p] ↥(chartAlgInf p Γ hj)) (ht : idmk Γ p hj κ red t = 0) :
    t ∈ P0 Γ p hj κ red :=
  TensorProduct.mem_map_includeRight_of_map_mk_eq_zero (RingHom.ker red) t ht

def ρbar : Sbar Γ p hj κ red →+* LaurentSeries (ZMod p) :=
  Ideal.Quotient.lift (RingHom.ker red) (ρ Γ p hj) (fun a ha => (mem_ker_red_iff Γ p hj κ red hred a).mp ha)

theorem ρbar_mk (b : ↥(chartAlgInf p Γ hj)) : ρbar Γ p hj κ red hred (Ideal.Quotient.mk _ b) = ρ Γ p hj b := rfl

theorem ρbar_injective : Function.Injective (ρbar Γ p hj κ red hred) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [ρbar_mk] at hx
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ((mem_ker_red_iff Γ p hj κ red hred b).mpr hx)

theorem redbar_eq (s : Sbar Γ p hj κ red) :
    redbar Γ p hj κ red hred s = coeffMap (algebraMap (ZMod p) κ) (ρbar Γ p hj κ red hred s) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective s
  rw [redbar_mk, ρbar_mk, red_eq Γ p hj κ red hred]

theorem ρbar_smul (r : R p) (s : Sbar Γ p hj κ red) :
    ρbar Γ p hj κ red hred (r • s) = (GaloisRep.ratLocalizedAtResidue p r) • ρbar Γ p hj κ red hred s := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective s
  rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul, ρbar_mk, ρbar_mk, map_mul,
    ρ_algebraMap, HahnSeries.C_mul_eq_smul]

def V : Submodule (ZMod p) (LaurentSeries (ZMod p)) where
  carrier := Set.range (ρbar Γ p hj κ red hred)
  add_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x + y, map_add _ _ _⟩
  zero_mem' := ⟨0, map_zero _⟩
  smul_mem' := by
    rintro a _ ⟨x, rfl⟩
    refine ⟨((a.val : ℕ) : R p) • x, ?_⟩
    rw [ρbar_smul, map_natCast, ZMod.natCast_zmod_val]

abbrev ι : Type := Module.Basis.ofVectorSpaceIndex (ZMod p) ↥(V Γ p hj κ red hred)

def w : Module.Basis (ι Γ p hj κ red hred) (ZMod p) ↥(V Γ p hj κ red hred) := Module.Basis.ofVectorSpace _ _

def Bv (i : ι Γ p hj κ red hred) : Sbar Γ p hj κ red := ((w Γ p hj κ red hred i).2).choose

theorem ρbar_Bv (i : ι Γ p hj κ red hred) :
    ρbar Γ p hj κ red hred (Bv Γ p hj κ red hred i) = ((w Γ p hj κ red hred i : ↥(V Γ p hj κ red hred)) : LaurentSeries (ZMod p)) :=
  ((w Γ p hj κ red hred i).2).choose_spec

theorem linearIndependent_ρbar_Bv :
    LinearIndependent (ZMod p) (fun i => ρbar Γ p hj κ red hred (Bv Γ p hj κ red hred i)) := by
  have h := (w Γ p hj κ red hred).linearIndependent.map' (V Γ p hj κ red hred).subtype
    (Submodule.ker_subtype _)
  convert h using 1 <;> try with_reducible_and_instances rfl
  funext i
  exact ρbar_Bv Γ p hj κ red hred i

theorem eq_sum_smul_Bv (s : Sbar Γ p hj κ red) :
    s = ∑ i ∈ ((w Γ p hj κ red hred).repr ⟨ρbar Γ p hj κ red hred s, ⟨s, rfl⟩⟩).support,
      ((((w Γ p hj κ red hred).repr ⟨ρbar Γ p hj κ red hred s, ⟨s, rfl⟩⟩) i).val : R p) • Bv Γ p hj κ red hred i := by
  set v : ↥(V Γ p hj κ red hred) := ⟨ρbar Γ p hj κ red hred s, ⟨s, rfl⟩⟩ with hv
  set l := (w Γ p hj κ red hred).repr v with hl
  apply ρbar_injective Γ p hj κ red hred
  rw [map_sum]
  have hrepr := (w Γ p hj κ red hred).linearCombination_repr v
  rw [Finsupp.linearCombination_apply, Finsupp.sum, ← hl] at hrepr
  have hcoe := congrArg (fun v : ↥(V Γ p hj κ red hred) => (v : LaurentSeries (ZMod p))) hrepr
  simp only [Submodule.coe_sum, Submodule.coe_smul] at hcoe
  rw [show ρbar Γ p hj κ red hred s = (v : LaurentSeries (ZMod p)) from rfl, ← hcoe]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ρbar_smul, map_natCast, ZMod.natCast_zmod_val, ρbar_Bv]

def Θ (g : ι Γ p hj κ red hred →₀ κ) : κ ⊗[R p] Sbar Γ p hj κ red := g.sum fun i c => c ⊗ₜ Bv Γ p hj κ red hred i

theorem Θ_add (g₁ g₂ : ι Γ p hj κ red hred →₀ κ) :
    Θ Γ p hj κ red hred (g₁ + g₂) = Θ Γ p hj κ red hred g₁ + Θ Γ p hj κ red hred g₂ :=
  Finsupp.sum_add_index' (fun i => TensorProduct.zero_tmul _ _) (fun i c₁ c₂ => TensorProduct.add_tmul _ _ _)

theorem Θ_surjective (t : κ ⊗[R p] Sbar Γ p hj κ red) : ∃ g, Θ Γ p hj κ red hred g = t := by
  classical
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, Finsupp.sum_zero_index⟩
  | tmul c s =>
    set l := (w Γ p hj κ red hred).repr ⟨ρbar Γ p hj κ red hred s, ⟨s, rfl⟩⟩ with hl
    refine ⟨Finsupp.onFinset l.support (fun i => if i ∈ l.support then ((l i).val : R p) • c else 0)
      (fun i hi => by by_contra h; exact hi (if_neg h)), ?_⟩
    rw [Θ, Finsupp.onFinset_sum (g := fun i c => c ⊗ₜ[R p] Bv Γ p hj κ red hred i) _ (fun i => TensorProduct.zero_tmul _ _)]
    conv_rhs => rw [eq_sum_smul_Bv Γ p hj κ red hred s, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [if_pos hi, TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨g₁, rfl⟩ := hx
    obtain ⟨g₂, rfl⟩ := hy
    exact ⟨g₁ + g₂, Θ_add Γ p hj κ red hred g₁ g₂⟩

theorem Φbar_Θ (g : ι Γ p hj κ red hred →₀ κ) :
    Φbar Γ p hj κ red hred (Θ Γ p hj κ red hred g) =
      ∑ i ∈ g.support, g i • coeffMap (algebraMap (ZMod p) κ) (ρbar Γ p hj κ red hred (Bv Γ p hj κ red hred i)) := by
  rw [Θ, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Φbar_tmul, redbar_eq, Algebra.smul_def]

theorem Φbar_injective : Function.Injective (Φbar Γ p hj κ red hred) := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨g, rfl⟩ := Θ_surjective Γ p hj κ red hred t
  rw [Φbar_Θ] at ht
  have hg : ∀ i ∈ g.support, g i = 0 :=
    LaurentSeries.LDKappa.eq_zero_of_sum_smul_coeffMap_eq_zero _ (linearIndependent_ρbar_Bv Γ p hj κ red hred)
      g.support g ht
  have hg0 : g = 0 := by
    ext i
    by_cases hi : i ∈ g.support
    · exact hg i hi
    · exact Finsupp.notMem_support_iff.mp hi
  rw [hg0, Θ, Finsupp.sum_zero_index]

include hred in

theorem kerΦ_le_P0 : RingHom.ker (Φ Γ p hj κ red hred) ≤ P0 Γ p hj κ red := by
  intro t ht
  rw [RingHom.mem_ker, Φ_eq_comp, AlgHom.comp_apply] at ht
  exact mem_P0_of_idmk_eq_zero Γ p hj κ red t (Φbar_injective Γ p hj κ red hred (ht.trans (map_zero _).symm))

include hred in
theorem P0_isPrime : (P0 Γ p hj κ red).IsPrime := by
  have h : P0 Γ p hj κ red = RingHom.ker (Φ Γ p hj κ red hred) :=
    le_antisymm (P0_le_kerΦ Γ p hj κ red hred) (kerΦ_le_P0 Γ p hj κ red hred)
  rw [h]
  exact RingHom.ker_isPrime _

end Frame

end ModularCurve.QPrime
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_map_ker_mem_minimalPrimes_and_le_ker_of_chartAlgInf.ModularCurve P2MW.S_ModularCurve_XHDRLevel_map_ker_mem_minimalPrimes_and_le_ker_of_chartAlgInf.ModularCurve.QPrime"
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_map_ker_mem_minimalPrimes_and_le_ker_of_chartAlgInf.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_map_ker_mem_minimalPrimes_and_le_ker_of_chartAlgInf.ModularCurve P2MW.S_ModularCurve_XHDRLevel_map_ker_mem_minimalPrimes_and_le_ker_of_chartAlgInf.ModularCurve.QPrime"

open ModularCurve.QPrime in
theorem solution
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (p : ℕ) [Fact p.Prime]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [Algebra (R p) κ]
    (red : ↥(chartAlgInf p Γ hj) →+* LaurentSeries κ)
    (hred : ∀ (b : ↥(chartAlgInf p Γ hj)) (y : LaurentSeries (R p)),
      coeffMap (algebraMap (R p) ℚ) y = ((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) →
        red b = coeffMap (algebraMap (R p) κ) y)
    (ev : κ ⊗[R p] ↥(chartAlgInf p Γ hj) →ₐ[κ] κ)
    (hev : ∀ b : ↥(chartAlgInf p Γ hj), ev (1 ⊗ₜ b) = (red b).coeff 0) :
    Ideal.map (Algebra.TensorProduct.includeRight :
        ↥(chartAlgInf p Γ hj) →ₐ[R p] κ ⊗[R p] ↥(chartAlgInf p Γ hj)) (RingHom.ker red) ∈
      minimalPrimes (κ ⊗[R p] ↥(chartAlgInf p Γ hj)) ∧
    Ideal.map (Algebra.TensorProduct.includeRight :
        ↥(chartAlgInf p Γ hj) →ₐ[R p] κ ⊗[R p] ↥(chartAlgInf p Γ hj)) (RingHom.ker red) ≤ RingHom.ker ev :=
  ⟨⟨⟨ModularCurve.QPrime.P0_isPrime Γ p hj κ red hred, bot_le⟩,
    fun Q hQ hle => by
      haveI := hQ.1
      exact ModularCurve.QPrime.P0_le_of_prime_le Γ p hj κ red hred Q hle⟩,
   ModularCurve.QPrime.P0_le_ker Γ p hj κ red ev hev⟩

end S_ModularCurve_XHDRLevel_map_ker_mem_minimalPrimes_and_le_ker_of_chartAlgInf
end P2MW
export P2MW.S_ModularCurve_XHDRLevel_map_ker_mem_minimalPrimes_and_le_ker_of_chartAlgInf (solution)
