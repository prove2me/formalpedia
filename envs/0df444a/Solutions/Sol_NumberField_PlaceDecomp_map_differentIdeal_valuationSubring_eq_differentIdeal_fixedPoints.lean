-- Prove2me | solution 1 for NumberField.PlaceDecomp.map_differentIdeal_valuationSubring_eq_differentIdeal_fixedPoints
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/edd9347a-451c-58d5-a670-5f0ae8818396

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import Theorems.Thm_FixedPoints_isDiscreteValuationRing_subring
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_stabilizer_asIdeal_eq_decompositionSubgroup_valuationSubring
import Theorems.Thm_NumberField_PlaceDecomp_natCard_decomp_eq_ramificationIdx_mul_inertiaDeg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_map_differentIdeal_valuationSubring_eq_differentIdeal_fixedPoints

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3

p2m_open "NumberField P2MW.S_NumberField_PlaceDecomp_map_differentIdeal_valuationSubring_eq_differentIdeal_fixedPoints.NumberField IsDedekindDomain"
p2m_open_scoped "NumberField.PlaceDecomp P2MW.S_NumberField_PlaceDecomp_map_differentIdeal_valuationSubring_eq_differentIdeal_fixedPoints.NumberField.PlaceDecomp Pointwise"

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

noncomputable section

namespace NumberField
p2m_export "NumberField" "RingOfIntegers RingOfIntegers.isIntegral_coe PlaceDecomp.decomp PlaceDecomp.natCard_decomp_eq_ramificationIdx_mul_inertiaDeg"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "decomp smul_def natCard_decomp_eq_ramificationIdx_mul_inertiaDeg"
namespace LocDiff
p2m_open "NumberField.PlaceDecomp NumberField"

variable (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F] [IsGalois K F]
variable (P : HeightOneSpectrum (𝓞 F))

abbrev AP : Type := ↥((P.valuation F).valuationSubring)

noncomputable abbrev DD : Type := ↥(NumberField.PlaceDecomp.decomp K F P)

noncomputable abbrev AD : Type := ↥(FixedPoints.subring (AP F P) (DD K F P))

abbrev ZZ : IntermediateField K F := IntermediateField.fixedField (NumberField.PlaceDecomp.decomp K F P)

theorem coe_smul_AP (σ : DD K F P) (x : AP F P) : ((σ • x : AP F P) : F) = (σ : F ≃ₐ[K] F) (x : F) := rfl

theorem coe_mem_ZZ (x : AD K F P) : ((x : AP F P) : F) ∈ ZZ K F P := by
  rw [IntermediateField.mem_fixedField_iff]
  intro σ hσ
  have h := x.2 ⟨σ, hσ⟩
  have := congrArg (fun y : AP F P => (y : F)) h
  simpa [coe_smul_AP] using this

noncomputable def toZZ : AD K F P →+* ↥(ZZ K F P) where
  toFun x := ⟨((x : AP F P) : F), coe_mem_ZZ K F P x⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable scoped instance algebraADZZ : Algebra (AD K F P) ↥(ZZ K F P) := (toZZ K F P).toAlgebra

theorem algebraMap_AD_ZZ_apply (x : AD K F P) : ((algebraMap (AD K F P) ↥(ZZ K F P) x : ↥(ZZ K F P)) : F) = ((x : AP F P) : F) := rfl

noncomputable scoped instance algebraADF : Algebra (AD K F P) F :=
  ((algebraMap (AP F P) F).comp (algebraMap (AD K F P) (AP F P))).toAlgebra

theorem algebraMap_AD_F_apply (x : AD K F P) : algebraMap (AD K F P) F x = ((x : AP F P) : F) := rfl

scoped instance isScalarTower_AD_AP_F : IsScalarTower (AD K F P) (AP F P) F :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

scoped instance isScalarTower_AD_ZZ_F : IsScalarTower (AD K F P) ↥(ZZ K F P) F :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem algebraMap_AD_ZZ_injective : Function.Injective (algebraMap (AD K F P) ↥(ZZ K F P)) := by
  intro x y h
  have := congrArg (fun z : ↥(ZZ K F P) => (z : F)) h
  simp only [algebraMap_AD_ZZ_apply] at this
  exact Subtype.ext (Subtype.ext this)

theorem mem_range_algebraMap_AD_ZZ {z : ↥(ZZ K F P)} (hz : (z : F) ∈ (P.valuation F).valuationSubring) :
    z ∈ (algebraMap (AD K F P) ↥(ZZ K F P)).range := by
  refine ⟨⟨⟨(z : F), hz⟩, fun σ => ?_⟩, Subtype.ext rfl⟩
  apply Subtype.ext
  rw [coe_smul_AP]
  exact (IntermediateField.mem_fixedField_iff _ _).mp z.2 σ σ.2

noncomputable scoped instance isFractionRing_AD_ZZ : IsFractionRing (AD K F P) ↥(ZZ K F P) where
  map_units y := by
    apply IsUnit.mk0
    intro h
    have h0 : (y : AD K F P) = 0 := algebraMap_AD_ZZ_injective K F P (by rw [h, map_zero])
    exact nonZeroDivisors.coe_ne_zero y h0
  surj z := by
    by_cases hz : (z : F) ∈ (P.valuation F).valuationSubring
    · obtain ⟨x, hx⟩ := mem_range_algebraMap_AD_ZZ K F P hz
      exact ⟨(x, 1), by simp [hx]⟩
    · have hz0 : (z : F) ≠ 0 := by rintro h; exact hz (h ▸ zero_mem _)
      have hinv : (z : F)⁻¹ ∈ (P.valuation F).valuationSubring :=
        ((P.valuation F).valuationSubring.mem_or_inv_mem (z : F)).resolve_left hz
      have hinv' : ((z⁻¹ : ↥(ZZ K F P)) : F) ∈ (P.valuation F).valuationSubring := by simpa using hinv
      obtain ⟨s, hs⟩ := mem_range_algebraMap_AD_ZZ K F P hinv'
      have hs0 : s ∈ nonZeroDivisors (AD K F P) := by
        apply mem_nonZeroDivisors_of_ne_zero
        rintro rfl
        rw [map_zero] at hs
        have hz' : ((z : ↥(ZZ K F P))⁻¹ : ↥(ZZ K F P)) = 0 := hs.symm
        exact hz0 (by simpa using congrArg (fun t : ↥(ZZ K F P) => (t : F)) hz')
      refine ⟨(1, ⟨s, hs0⟩), ?_⟩
      simp only [map_one]
      rw [hs, mul_inv_cancel₀]
      exact fun h => hz0 (congrArg Subtype.val h)
  exists_of_eq {x y} h := ⟨1, by rw [algebraMap_AD_ZZ_injective K F P h]⟩

theorem smul_asIdeal_eq (τ : DD K F P) : (τ : F ≃ₐ[K] F) • P.asIdeal = P.asIdeal := by
  have hτ : (τ : F ≃ₐ[K] F) ∈ MulAction.stabilizer (F ≃ₐ[K] F) P.asIdeal := by
    rw [IsDedekindDomain.HeightOneSpectrum.stabilizer_asIdeal_eq_decompositionSubgroup_valuationSubring K F P]
    exact τ.2
  exact hτ

theorem smul_notMem (τ : DD K F P) {b : 𝓞 F} (hb : b ∉ P.asIdeal) : (τ : F ≃ₐ[K] F) • b ∉ P.asIdeal := by
  intro h
  apply hb
  have h1 : (τ : F ≃ₐ[K] F)⁻¹ • ((τ : F ≃ₐ[K] F) • b) ∈ (τ : F ≃ₐ[K] F)⁻¹ • ((τ : F ≃ₐ[K] F) • P.asIdeal) := by
    rw [smul_asIdeal_eq]
    exact Ideal.smul_mem_pointwise_smul _ _ _ h
  rwa [inv_smul_smul, inv_smul_smul] at h1

open scoped algebraMap in

theorem exists_mul_algebraMap_eq {u : F} (hu : u ∈ (P.valuation F).valuationSubring) :
    ∃ a b : 𝓞 F, b ∉ P.asIdeal ∧ u * algebraMap (𝓞 F) F b = algebraMap (𝓞 F) F a := by
  have hu' : u ∈ HeightOneSpectrum.valuationSubringAtPrime F P := by
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]; exact hu
  obtain ⟨a, s, hs, rfl⟩ := hu'
  refine ⟨a, s, hs, ?_⟩
  have hs0 : (algebraMap (𝓞 F) F s) ≠ 0 := by
    intro h0
    apply hs
    rw [show s = 0 from (FaithfulSMul.algebraMap_injective (𝓞 F) F) (by rw [h0, map_zero])]
    exact Submodule.zero_mem _
  show (a : F) * ((s : F))⁻¹ * algebraMap (𝓞 F) F s = algebraMap (𝓞 F) F a
  rw [inv_mul_cancel_right₀ hs0]

theorem valuation_algebraMap_eq_one_iff (b : 𝓞 F) : P.valuation F (algebraMap (𝓞 F) F b) = 1 ↔ b ∉ P.asIdeal := by
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl]
  rfl

theorem exists_den {u : F} (hu : u ∈ (P.valuation F).valuationSubring) :
    ∃ t : 𝓞 F, (algebraMap (𝓞 F) F t) ∈ ZZ K F P ∧ P.valuation F (algebraMap (𝓞 F) F t) = 1 ∧
      ∃ c : 𝓞 F, algebraMap (𝓞 F) F t * u = algebraMap (𝓞 F) F c := by
  classical
  haveI : Fintype (DD K F P) := Fintype.ofFinite _
  obtain ⟨a, b, hb, hab⟩ := exists_mul_algebraMap_eq F P hu

  refine ⟨∏ τ : DD K F P, (τ : F ≃ₐ[K] F) • b, ?_, ?_, ?_⟩
  ·
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    rw [map_prod, map_prod]

    have : ∀ τ : DD K F P, σ (algebraMap (𝓞 F) F ((τ : F ≃ₐ[K] F) • b)) =
        algebraMap (𝓞 F) F (((⟨σ, hσ⟩ * τ : DD K F P) : F ≃ₐ[K] F) • b) := fun τ => by
      rw [Subgroup.coe_mul, mul_smul]
      rfl
    simp_rw [this]
    exact Fintype.prod_equiv (Equiv.mulLeft (⟨σ, hσ⟩ : DD K F P)) _ _ fun τ => rfl
  ·
    rw [valuation_algebraMap_eq_one_iff]
    intro hmem
    haveI := P.isPrime
    obtain ⟨τ, -, hτ⟩ := (Ideal.IsPrime.prod_mem_iff (p := P.asIdeal)).mp hmem
    exact smul_notMem K F P τ hb hτ
  · refine ⟨(∏ τ ∈ Finset.univ.erase (1 : DD K F P), (τ : F ≃ₐ[K] F) • b) * a, ?_⟩
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (1 : DD K F P))]
    simp only [Subgroup.coe_one, one_smul, map_mul]
    rw [mul_assoc, mul_comm (algebraMap (𝓞 F) F b) u, hab]

theorem inv_mem_of_den {t : 𝓞 F} (htZ : (algebraMap (𝓞 F) F t) ∈ ZZ K F P) (ht1 : P.valuation F (algebraMap (𝓞 F) F t) = 1) :
    (algebraMap (𝓞 F) F t)⁻¹ ∈ (P.valuation F).valuationSubring ∧ (algebraMap (𝓞 F) F t)⁻¹ ∈ ZZ K F P := by
  constructor
  · rw [Valuation.mem_valuationSubring_iff, map_inv₀, ht1, inv_one]
  · exact inv_mem htZ

theorem exists_AD_algebraMap_eq_inv {t : 𝓞 F} (htZ : (algebraMap (𝓞 F) F t) ∈ ZZ K F P)
    (ht1 : P.valuation F (algebraMap (𝓞 F) F t) = 1) :
    ∃ s : AD K F P, algebraMap (AD K F P) F s = (algebraMap (𝓞 F) F t)⁻¹ := by
  obtain ⟨hA, hZ⟩ := inv_mem_of_den K F P htZ ht1
  obtain ⟨s, hs⟩ := mem_range_algebraMap_AD_ZZ K F P (z := ⟨_, hZ⟩) hA
  exact ⟨s, by rw [algebraMap_AD_F_apply, ← algebraMap_AD_ZZ_apply, hs]⟩

scoped instance isIntegralClosure_AP : IsIntegralClosure (AP F P) (AD K F P) F where
  algebraMap_injective := fun x y h => Subtype.ext h
  isIntegral_iff {x} := by
    constructor
    · intro hx
      have hx' : IsIntegral (AP F P) x := hx.tower_top
      exact (IsIntegrallyClosed.isIntegral_iff (R := AP F P) (K := F)).mp hx'
    · rintro ⟨y, rfl⟩
      obtain ⟨t, htZ, ht1, c, hc⟩ := exists_den K F P y.2
      obtain ⟨s, hs⟩ := exists_AD_algebraMap_eq_inv K F P htZ ht1
      have ht0 : algebraMap (𝓞 F) F t ≠ 0 := by
        intro h; rw [h, map_zero] at ht1; exact zero_ne_one ht1
      have hy : algebraMap (AP F P) F y = algebraMap (AD K F P) F s * algebraMap (𝓞 F) F c := by
        rw [hs, ← hc, ← mul_assoc, inv_mul_cancel₀ ht0, one_mul]
        rfl
      rw [hy]
      exact isIntegral_algebraMap.mul ((RingOfIntegers.isIntegral_coe c).tower_top)

abbrev RZ : Type := 𝓞 ↥(ZZ K F P)

abbrev Tg : Submodule (𝓞 F) F := Submodule.traceDual (RZ K F P) ↥(ZZ K F P) (1 : Submodule (𝓞 F) F)

abbrev Tl : Submodule (AP F P) F := Submodule.traceDual (AD K F P) ↥(ZZ K F P) (1 : Submodule (AP F P) F)

theorem mem_range_RZ_iff (c : ↥(ZZ K F P)) : c ∈ (algebraMap (RZ K F P) ↥(ZZ K F P)).range ↔ IsIntegral ℤ c := by
  constructor
  · rintro ⟨y, rfl⟩; exact RingOfIntegers.isIntegral_coe y
  · intro h; exact ⟨⟨c, h⟩, rfl⟩

theorem isIntegral_ZZ_iff (c : ↥(ZZ K F P)) : IsIntegral ℤ c ↔ IsIntegral ℤ (c : F) :=
  (isIntegral_algebraMap_iff (algebraMap ↥(ZZ K F P) F).injective).symm

theorem mem_range_AD_iff (c : ↥(ZZ K F P)) : c ∈ (algebraMap (AD K F P) ↥(ZZ K F P)).range ↔ (c : F) ∈ (P.valuation F).valuationSubring := by
  constructor
  · rintro ⟨y, rfl⟩; exact (y : AP F P).2
  · exact mem_range_algebraMap_AD_ZZ K F P

theorem mem_one_iff_isIntegral (u : F) : u ∈ (1 : Submodule (𝓞 F) F) ↔ IsIntegral ℤ u := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨y, rfl⟩; exact RingOfIntegers.isIntegral_coe y
  · intro h; exact ⟨⟨u, h⟩, rfl⟩

theorem mem_one_AP_iff (u : F) : u ∈ (1 : Submodule (AP F P) F) ↔ u ∈ (P.valuation F).valuationSubring := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨y, rfl⟩; exact y.2
  · intro h; exact ⟨⟨u, h⟩, rfl⟩

theorem algebraMap_mem_AP (c : 𝓞 F) : algebraMap (𝓞 F) F c ∈ (P.valuation F).valuationSubring :=
  (Valuation.mem_valuationSubring_iff _ _).2 (P.valuation_le_one c)

theorem mem_AP_of_isIntegral {u : F} (hu : IsIntegral ℤ u) : u ∈ (P.valuation F).valuationSubring :=
  algebraMap_mem_AP F P ⟨u, hu⟩

theorem traceForm_smul_right (q : ↥(ZZ K F P)) (x y : F) :
    Algebra.traceForm ↥(ZZ K F P) F x ((q : F) * y) = q • Algebra.traceForm ↥(ZZ K F P) F x y := by
  rw [show (q : F) * y = q • y from rfl, LinearMap.map_smul]

theorem traceForm_smul_left (q : ↥(ZZ K F P)) (x y : F) :
    Algebra.traceForm ↥(ZZ K F P) F ((q : F) * x) y = q • Algebra.traceForm ↥(ZZ K F P) F x y := by
  rw [show (q : F) * x = q • x from rfl, LinearMap.map_smul, LinearMap.smul_apply]

theorem coe_smul_ZZ (q r : ↥(ZZ K F P)) : ((q • r : ↥(ZZ K F P)) : F) = (q : F) * (r : F) := rfl

theorem Tg_le_Tl : ∀ x ∈ Tg K F P, x ∈ Tl K F P := by
  intro x hx
  rw [Submodule.mem_traceDual] at hx ⊢
  intro a ha
  rw [mem_one_AP_iff] at ha
  obtain ⟨t, htZ, ht1, c, hc⟩ := exists_den K F P ha
  have ht0 : algebraMap (𝓞 F) F t ≠ 0 := by
    intro h; rw [h, map_zero] at ht1; exact zero_ne_one ht1
  obtain ⟨hinvA, hinvZ⟩ := inv_mem_of_den K F P htZ ht1
  have ha' : a = ((⟨_, hinvZ⟩ : ↥(ZZ K F P)) : F) * algebraMap (𝓞 F) F c := by
    show a = (algebraMap (𝓞 F) F t)⁻¹ * algebraMap (𝓞 F) F c
    rw [← hc, ← mul_assoc, inv_mul_cancel₀ ht0, one_mul]
  obtain ⟨r, hr⟩ := hx (algebraMap (𝓞 F) F c) ((mem_one_iff_isIntegral F _).mpr (RingOfIntegers.isIntegral_coe c))
  rw [ha', traceForm_smul_right K F P, mem_range_AD_iff, coe_smul_ZZ, ← hr]
  refine mul_mem hinvA (mem_AP_of_isIntegral F P ?_)
  rw [← isIntegral_ZZ_iff]
  exact RingOfIntegers.isIntegral_coe r

theorem exists_den_mul_mem_Tg {x : F} (hx : x ∈ Tl K F P) :
    ∃ t : 𝓞 F, (algebraMap (𝓞 F) F t) ∈ ZZ K F P ∧ P.valuation F (algebraMap (𝓞 F) F t) = 1 ∧
      algebraMap (𝓞 F) F t * x ∈ Tg K F P := by
  classical
  obtain ⟨S, hS⟩ := Module.finite_def.mp (inferInstance : Module.Finite (RZ K F P) (𝓞 F))
  rw [Submodule.mem_traceDual] at hx

  have hden : ∀ y : 𝓞 F, ∃ t : 𝓞 F, ∃ ht : (algebraMap (𝓞 F) F t) ∈ ZZ K F P, P.valuation F (algebraMap (𝓞 F) F t) = 1 ∧
      IsIntegral ℤ ((⟨_, ht⟩ : ↥(ZZ K F P)) • Algebra.traceForm ↥(ZZ K F P) F x (algebraMap (𝓞 F) F y)) := by
    intro y
    have h := hx (algebraMap (𝓞 F) F y) ((mem_one_AP_iff F P _).mpr (algebraMap_mem_AP F P y))
    rw [mem_range_AD_iff] at h
    obtain ⟨t, htZ, ht1, c, hc⟩ := exists_den K F P h
    refine ⟨t, htZ, ht1, ?_⟩
    rw [isIntegral_ZZ_iff, coe_smul_ZZ, hc]
    exact RingOfIntegers.isIntegral_coe c
  choose tf htfZ htf1 htfi using hden
  have hprodZ : ∀ S' : Finset (𝓞 F), algebraMap (𝓞 F) F (∏ y ∈ S', tf y) ∈ ZZ K F P := fun S' => by
    rw [map_prod]; exact prod_mem fun y _ => htfZ y
  refine ⟨∏ y ∈ S, tf y, hprodZ S, ?_, ?_⟩
  · rw [map_prod, map_prod]; exact Finset.prod_eq_one fun y _ => htf1 y
  · rw [Submodule.mem_traceDual]
    intro a ha
    rw [Submodule.mem_one] at ha
    obtain ⟨a, rfl⟩ := ha
    have haS : a ∈ Submodule.span (RZ K F P) (S : Set (𝓞 F)) := by rw [hS]; exact Submodule.mem_top
    rw [mem_range_RZ_iff]

    rw [show algebraMap (𝓞 F) F (∏ y ∈ S, tf y) * x = ((⟨_, hprodZ S⟩ : ↥(ZZ K F P)) : F) * x from rfl,
      traceForm_smul_left K F P]
    induction haS using Submodule.span_induction with
    | mem y hy =>

      have hsplit : (⟨_, hprodZ S⟩ : ↥(ZZ K F P)) = (⟨_, hprodZ (S.erase y)⟩ : ↥(ZZ K F P)) * ⟨_, htfZ y⟩ := by
        apply Subtype.ext
        show algebraMap (𝓞 F) F (∏ y ∈ S, tf y) = algebraMap (𝓞 F) F (∏ z ∈ S.erase y, tf z) * algebraMap (𝓞 F) F (tf y)
        rw [← map_mul, Finset.prod_erase_mul _ _ hy]
      rw [hsplit, mul_smul, smul_eq_mul]
      refine IsIntegral.mul ?_ (htfi y)
      rw [isIntegral_ZZ_iff]
      exact RingOfIntegers.isIntegral_coe _
    | zero => rw [map_zero, LinearMap.map_zero, smul_zero]; exact isIntegral_zero
    | add y z _ _ hy hz => rw [map_add, LinearMap.map_add, smul_add]; exact hy.add hz
    | smul r y _ hy =>
      have hr : algebraMap (𝓞 F) F (r • y) = ((algebraMap (RZ K F P) ↥(ZZ K F P) r : ↥(ZZ K F P)) : F) * algebraMap (𝓞 F) F y := by
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply (RZ K F P) (𝓞 F) F,
          IsScalarTower.algebraMap_apply (RZ K F P) ↥(ZZ K F P) F]
        rfl
      rw [hr, traceForm_smul_right K F P, smul_eq_mul, smul_eq_mul, mul_left_comm]
      rw [smul_eq_mul] at hy
      exact (RingOfIntegers.isIntegral_coe r).mul hy

theorem Tg_fg : (Tg K F P).FG := by
  have h : Tg K F P = ((FractionalIdeal.dual (RZ K F P) ↥(ZZ K F P) (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :
      FractionalIdeal (nonZeroDivisors (𝓞 F)) F) : Submodule (𝓞 F) F) := by
    rw [FractionalIdeal.coe_dual_one]
  rw [h]
  exact FractionalIdeal.fg_of_isUnit _ (isUnit_iff_ne_zero.mpr (FractionalIdeal.dual_ne_zero _ _ one_ne_zero))

abbrev invTg : Submodule (𝓞 F) F := 1 / Tg K F P

theorem mem_invTg_iff (z : F) : z ∈ invTg K F P ↔ ∀ y ∈ Tg K F P, z * y ∈ (1 : Submodule (𝓞 F) F) :=
  Submodule.mem_div_iff_forall_mul_mem

theorem mul_mem_one_of_mem_span {z : F} (hz : z ∈ Submodule.span (AP F P) (invTg K F P : Set F)) :
    ∀ y ∈ Tl K F P, z * y ∈ (1 : Submodule (AP F P) F) := by
  induction hz using Submodule.span_induction with
  | mem m hm =>
    intro y hy
    obtain ⟨t, htZ, ht1, hty⟩ := exists_den_mul_mem_Tg K F P hy
    have ht0 : algebraMap (𝓞 F) F t ≠ 0 := by
      intro h; rw [h, map_zero] at ht1; exact zero_ne_one ht1
    have h1 : m * (algebraMap (𝓞 F) F t * y) ∈ (1 : Submodule (𝓞 F) F) := (mem_invTg_iff K F P m).mp hm _ hty
    rw [mem_one_iff_isIntegral] at h1
    rw [mem_one_AP_iff]
    have : m * y = (algebraMap (𝓞 F) F t)⁻¹ * (m * (algebraMap (𝓞 F) F t * y)) := by
      field_simp
    rw [this]
    exact mul_mem (inv_mem_of_den K F P htZ ht1).1 (mem_AP_of_isIntegral F P h1)
  | zero => intro y _; rw [zero_mul]; exact Submodule.zero_mem _
  | add z w _ _ hz hw => intro y hy; rw [add_mul]; exact Submodule.add_mem _ (hz y hy) (hw y hy)
  | smul a z _ hz =>
    intro y hy
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ a (hz y hy)

theorem mem_span_of_mul_mem_one {z : F} (hz : ∀ y ∈ Tl K F P, z * y ∈ (1 : Submodule (AP F P) F)) :
    z ∈ Submodule.span (AP F P) (invTg K F P : Set F) := by
  classical
  obtain ⟨G, hG⟩ := Tg_fg K F P

  have hden : ∀ g : F, g ∈ G → ∃ t : 𝓞 F, P.valuation F (algebraMap (𝓞 F) F t) = 1 ∧ IsIntegral ℤ (algebraMap (𝓞 F) F t * (z * g)) := by
    intro g hg
    have hgT : g ∈ Tg K F P := by rw [← hG]; exact Submodule.subset_span hg
    have h := hz g (Tg_le_Tl K F P g hgT)
    rw [mem_one_AP_iff] at h
    obtain ⟨t, -, ht1, c, hc⟩ := exists_den K F P h
    exact ⟨t, ht1, hc ▸ RingOfIntegers.isIntegral_coe c⟩
  choose! tf htf1 htfi using hden
  set t : 𝓞 F := ∏ g ∈ G, tf g with htdef
  have ht1 : P.valuation F (algebraMap (𝓞 F) F t) = 1 := by
    rw [htdef, map_prod, map_prod]; exact Finset.prod_eq_one fun g hg => htf1 g hg
  have ht0 : algebraMap (𝓞 F) F t ≠ 0 := by
    intro h; rw [h, map_zero] at ht1; exact zero_ne_one ht1

  have htz : algebraMap (𝓞 F) F t * z ∈ invTg K F P := by
    rw [mem_invTg_iff]
    intro y hy
    rw [← hG] at hy
    induction hy using Submodule.span_induction with
    | mem g hg =>
      rw [mem_one_iff_isIntegral, htdef, ← Finset.prod_erase_mul _ _ hg, map_mul, mul_assoc, mul_assoc]
      refine (RingOfIntegers.isIntegral_coe _).mul ?_
      exact htfi g hg
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add y w _ _ hy hw => rw [mul_add]; exact Submodule.add_mem _ hy hw
    | smul r y _ hy =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ r hy

  have hz' : z = (⟨(algebraMap (𝓞 F) F t)⁻¹, by
      rw [Valuation.mem_valuationSubring_iff, map_inv₀, ht1, inv_one]⟩ : AP F P) • (algebraMap (𝓞 F) F t * z) := by
    show z = (algebraMap (𝓞 F) F t)⁻¹ * (algebraMap (𝓞 F) F t * z)
    rw [← mul_assoc, inv_mul_cancel₀ ht0, one_mul]
  rw [hz']
  exact Submodule.smul_mem _ _ (Submodule.subset_span htz)

abbrev pZ : Ideal (RZ K F P) := P.asIdeal.under (RZ K F P)
abbrev pK : Ideal (𝓞 K) := P.asIdeal.under (𝓞 K)

theorem decomp_ZZ_eq_top : NumberField.PlaceDecomp.decomp ↥(ZZ K F P) F P = ⊤ := by
  rw [eq_top_iff]
  intro σ _

  have hσD : σ.restrictScalars K ∈ NumberField.PlaceDecomp.decomp K F P := by
    rw [← IntermediateField.fixingSubgroup_fixedField (NumberField.PlaceDecomp.decomp K F P)]
    intro z
    exact σ.commutes z

  show σ • (P.valuation F).valuationSubring = (P.valuation F).valuationSubring
  have hD : (σ.restrictScalars K) • (P.valuation F).valuationSubring = (P.valuation F).valuationSubring := hσD
  apply SetLike.coe_injective
  have := congrArg (fun S : ValuationSubring F => (S : Set F)) hD
  simp only [ValuationSubring.coe_pointwise_smul] at this ⊢
  exact this

theorem natCard_decomp_eq : Nat.card ↥(NumberField.PlaceDecomp.decomp ↥(ZZ K F P) F P) = Nat.card (DD K F P) := by
  classical
  rw [decomp_ZZ_eq_top, Subgroup.card_top]
  have h1 := IsGalois.card_aut_eq_finrank ↥(ZZ K F P) F
  have h2 := IntermediateField.finrank_fixedField_eq_card (NumberField.PlaceDecomp.decomp K F P)
  rw [h1]
  exact_mod_cast h2

theorem ramificationIdx_pZ_eq_one :
    Ideal.ramificationIdx' (pK K F P) (pZ K F P) = 1 := by
  haveI : P.asIdeal.IsMaximal := P.isMaximal
  haveI : (pZ K F P).IsMaximal := Ideal.IsMaximal.under _ _
  haveI : (pK K F P).IsMaximal := Ideal.IsMaximal.under _ _
  haveI : P.asIdeal.LiesOver (pZ K F P) := ⟨rfl⟩
  haveI : (pZ K F P).LiesOver (pK K F P) := ⟨by
    rw [Ideal.under_under]⟩
  haveI : P.asIdeal.LiesOver (pK K F P) := ⟨rfl⟩

  have h1 := NumberField.PlaceDecomp.natCard_decomp_eq_ramificationIdx_mul_inertiaDeg K F P
  have h2 := NumberField.PlaceDecomp.natCard_decomp_eq_ramificationIdx_mul_inertiaDeg ↥(ZZ K F P) F P
  rw [natCard_decomp_eq] at h2

  have hu1 : (HeightOneSpectrum.under (𝓞 K) P).asIdeal = pK K F P := rfl
  have hu2 : (HeightOneSpectrum.under (RZ K F P) P).asIdeal = pZ K F P := rfl
  rw [hu1] at h1
  rw [hu2] at h2
  rw [Ideal.ramificationIdx_algebra_tower' (pK K F P) (pZ K F P) P.asIdeal,
    Ideal.inertiaDeg_algebra_tower (pK K F P) (pZ K F P) P.asIdeal] at h1

  have hpos : 0 < Nat.card (DD K F P) := Nat.card_pos
  have hprod : Ideal.ramificationIdx' (pK K F P) (pZ K F P) *
      (pK K F P).inertiaDeg' (pZ K F P) = 1 := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [one_mul]
    conv_rhs => rw [h1]
    rw [h2]
    ring
  exact Nat.eq_one_of_mul_eq_one_right hprod

theorem exists_mem_differentIdeal_notMem :
    ∃ d ∈ differentIdeal (𝓞 K) (RZ K F P), d ∉ pZ K F P := by
  haveI : P.asIdeal.IsMaximal := P.isMaximal
  haveI : (pZ K F P).IsMaximal := Ideal.IsMaximal.under _ _
  have hne : pZ K F P ≠ ⊥ := Ideal.under_ne_bot (A := RZ K F P) P.ne_bot
  haveI : (pZ K F P).LiesOver (pK K F P) := ⟨by rw [Ideal.under_under]⟩
  have hpK : pK K F P ≠ ⊥ := Ideal.under_ne_bot (A := 𝓞 K) P.ne_bot
  have hunr : Algebra.IsUnramifiedAt (𝓞 K) (pZ K F P) :=
    (Algebra.isUnramifiedAt_iff_of_isDedekindDomain (R := 𝓞 K)).mpr
      ((Ideal.ramificationIdx'_eq_ramificationIdx (pK K F P) (pZ K F P) hpK).symm.trans
        (ramificationIdx_pZ_eq_one K F P))
  have hndvd : ¬ pZ K F P ∣ differentIdeal (𝓞 K) (RZ K F P) := not_dvd_differentIdeal_iff.mpr hunr
  by_contra h
  push Not at h
  exact hndvd (Ideal.dvd_iff_le.mpr h)

abbrev φ : 𝓞 F →+* ↥((P.valuation F).valuationSubring).toSubring :=
  (algebraMap (𝓞 F) F).codRestrict ((P.valuation F).valuationSubring).toSubring
    (fun x => (Valuation.mem_valuationSubring_iff _ _).2 (P.valuation_le_one x))

theorem coeSubmodule_map (I : Ideal (𝓞 F)) :
    IsLocalization.coeSubmodule F ((I.map (φ F P) : Ideal (AP F P))) =
      Submodule.span (AP F P) ((algebraMap (𝓞 F) F) '' (I : Set (𝓞 F))) := by
  rw [IsLocalization.coeSubmodule, Ideal.map, Submodule.map_span, ← Set.image_comp]
  rfl

theorem coe_coeSubmodule (I : Ideal (𝓞 F)) :
    ((IsLocalization.coeSubmodule F I : Submodule (𝓞 F) F) : Set F) = (algebraMap (𝓞 F) F) '' (I : Set (𝓞 F)) := by
  rw [IsLocalization.coeSubmodule, Submodule.map_coe]; rfl

theorem map_differentIdeal_eq_map :
    (differentIdeal (𝓞 K) (𝓞 F)).map (φ F P) = (differentIdeal (RZ K F P) (𝓞 F)).map (φ F P) := by
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal (𝓞 K) (RZ K F P) (𝓞 F), Ideal.map_mul, Ideal.map_map]
  suffices h : (differentIdeal (𝓞 K) (RZ K F P)).map ((φ F P).comp (algebraMap (RZ K F P) (𝓞 F))) = ⊤ by
    rw [h, Ideal.mul_top]
  obtain ⟨d, hd, hdP⟩ := exists_mem_differentIdeal_notMem K F P
  apply Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hd)

  have hdP' : algebraMap (RZ K F P) (𝓞 F) d ∉ P.asIdeal := hdP
  have hv : P.valuation F (algebraMap (𝓞 F) F (algebraMap (RZ K F P) (𝓞 F) d)) = 1 :=
    (valuation_algebraMap_eq_one_iff F P _).mpr hdP'
  have hmem : (algebraMap (𝓞 F) F (algebraMap (RZ K F P) (𝓞 F) d))⁻¹ ∈ (P.valuation F).valuationSubring := by
    rw [Valuation.mem_valuationSubring_iff, map_inv₀, hv, inv_one]
  have h0 : algebraMap (𝓞 F) F (algebraMap (RZ K F P) (𝓞 F) d) ≠ 0 := by
    intro h; rw [h, map_zero] at hv; exact zero_ne_one hv
  refine isUnit_iff_exists_inv.mpr ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
  exact mul_inv_cancel₀ h0

end NumberField.PlaceDecomp.LocDiff
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_map_differentIdeal_valuationSubring_eq_differentIdeal_fixedPoints.NumberField P2MW.S_NumberField_PlaceDecomp_map_differentIdeal_valuationSubring_eq_differentIdeal_fixedPoints.NumberField.PlaceDecomp P2MW.S_NumberField_PlaceDecomp_map_differentIdeal_valuationSubring_eq_differentIdeal_fixedPoints.NumberField.PlaceDecomp.LocDiff"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_map_differentIdeal_valuationSubring_eq_differentIdeal_fixedPoints.NumberField P2MW.S_NumberField_PlaceDecomp_map_differentIdeal_valuationSubring_eq_differentIdeal_fixedPoints.NumberField.PlaceDecomp"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_map_differentIdeal_valuationSubring_eq_differentIdeal_fixedPoints.NumberField"

open NumberField.PlaceDecomp.LocDiff in

theorem solution
    (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F] [IsGalois K F]
    (P : HeightOneSpectrum (𝓞 F)) :
    (differentIdeal (𝓞 K) (𝓞 F)).map
        (algebraMap (𝓞 F) F |>.codRestrict ((P.valuation F).valuationSubring).toSubring
          (fun x => (Valuation.mem_valuationSubring_iff _ _).2 (P.valuation_le_one x))) =
      (differentIdeal (FixedPoints.subring ↥((P.valuation F).valuationSubring) ↥(NumberField.PlaceDecomp.decomp K F P))
        ↥((P.valuation F).valuationSubring)) := by

  show (differentIdeal (𝓞 K) (𝓞 F)).map (φ F P) = differentIdeal (AD K F P) (AP F P)
  rw [map_differentIdeal_eq_map K F P]

  haveI : IsDiscreteValuationRing (AD K F P) := FixedPoints.isDiscreteValuationRing_subring

  apply IsLocalization.coeSubmodule_injective F (le_refl (nonZeroDivisors (AP F P)))
  rw [coeSubmodule_map, coeSubmodule_differentIdeal (AD K F P) ↥(ZZ K F P),
    ← coe_coeSubmodule F (differentIdeal (RZ K F P) (𝓞 F)), coeSubmodule_differentIdeal (RZ K F P) ↥(ZZ K F P)]

  ext z
  rw [Submodule.mem_div_iff_forall_mul_mem]
  exact ⟨mul_mem_one_of_mem_span K F P, mem_span_of_mul_mem_one K F P⟩

end
end S_NumberField_PlaceDecomp_map_differentIdeal_valuationSubring_eq_differentIdeal_fixedPoints
end P2MW
export P2MW.S_NumberField_PlaceDecomp_map_differentIdeal_valuationSubring_eq_differentIdeal_fixedPoints (solution)
