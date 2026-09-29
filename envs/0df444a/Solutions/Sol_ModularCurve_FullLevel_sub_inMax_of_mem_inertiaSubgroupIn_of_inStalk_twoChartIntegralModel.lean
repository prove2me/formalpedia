-- Prove2me | solution 1 for ModularCurve.FullLevel.sub_inMax_of_mem_inertiaSubgroupIn_of_inStalk_twoChartIntegralModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/0ac3e629-64a1-5eeb-b03a-61714c782bff

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_LaurentCoeff
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.RamificationGroup
import Theorems.Thm_ValuationSubring_mem_and_sub_mem_maximalIdeal_of_gaussPresentation_of_coe_eq_of_coeffMap_residue_comp_eq
import Theorems.Thm_ModularCurve_FullLevel_exists_ringEquiv_laurentBaseChange_levelField_coe_eq_coeffMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_sub_inMax_of_mem_inertiaSubgroupIn_of_inStalk_twoChartIntegralModel

set_option autoImplicit false

namespace E143TI

open AlgebraicCurve ModularCurve

universe u

theorem chartAlg_le_comap {R T E : Type u} [CommRing R] [Field T] [Field E] [Algebra R T]
    (ι : T →+* E) (O : ValuationSubring E) (S : Set T)
    (hS : ∀ s ∈ S, ι s ∈ O) (hR : ∀ r : R, ι (algebraMap R T r) ∈ O)
    {x : T} (hx : x ∈ TwoChartIntegralModel.chartAlg R T S) : ι x ∈ O := by
  let O' : ValuationSubring T := O.comap ι
  have hadj : ∀ b ∈ Algebra.adjoin R S, b ∈ O' := by
    intro b hb
    rw [Algebra.mem_adjoin_iff] at hb
    refine (Subring.closure_le (t := O'.toSubring)).mpr ?_ hb
    rintro z (⟨r, rfl⟩ | hz)
    · exact (ValuationSubring.mem_comap).mpr (hR r)
    · exact (ValuationSubring.mem_comap).mpr (hS z hz)
  rw [TwoChartIntegralModel.mem_chartAlg_iff] at hx
  let φ : ↥(Algebra.adjoin R S) →+* ↥O' :=
    (algebraMap ↥(Algebra.adjoin R S) T).codRestrict O' (fun b => hadj b b.2)
  have hx' : IsIntegral ↥O' x :=
    hx.map_of_comp_eq φ (RingHom.id T) (RingHom.ext fun _ => rfl)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := ↥O') (K := T) hx'
  rw [← hy]
  exact (ValuationSubring.mem_comap).mp y.2

theorem chartAlg_map_mem {R T : Type u} [CommRing R] [Field T] [Algebra R T]
    (σ : T →+* T) (ρ : R →+* R) (hσ : ∀ r : R, σ (algebraMap R T r) = algebraMap R T (ρ r))
    (S : Set T) (hS : ∀ s ∈ S, σ s ∈ Algebra.adjoin R S)
    {x : T} (hx : x ∈ TwoChartIntegralModel.chartAlg R T S) : σ x ∈ TwoChartIntegralModel.chartAlg R T S := by
  rw [TwoChartIntegralModel.mem_chartAlg_iff] at hx ⊢
  have hmap : ∀ b ∈ Algebra.adjoin R S, σ b ∈ Algebra.adjoin R S := by
    intro b hb
    rw [Algebra.mem_adjoin_iff] at hb
    have : σ b ∈ (Subring.closure (Set.range (algebraMap R T) ∪ S)).map σ := ⟨b, hb, rfl⟩
    rw [RingHom.map_closure] at this
    refine (Subring.closure_le (t := (Algebra.adjoin R S).toSubring)).mpr ?_ this
    rintro z ⟨w, hw, rfl⟩
    rcases hw with ⟨r, rfl⟩ | hw
    · rw [hσ]; exact (Algebra.adjoin R S).algebraMap_mem _
    · exact hS w hw
  let φ : ↥(Algebra.adjoin R S) →+* ↥(Algebra.adjoin R S) :=
    (σ.comp (algebraMap ↥(Algebra.adjoin R S) T)).codRestrict (Algebra.adjoin R S) (fun b => hmap b b.2)
  exact hx.map_of_comp_eq φ σ (RingHom.ext fun _ => rfl)

theorem chart_step {R T E : Type u} [CommRing R] [Field T] [Field E] [Algebra R T]
    (ι : T →+* E) (O : ValuationSubring E)
    (σ : T →+* T) (ρ : R →+* R) (hσ : ∀ r : R, σ (algebraMap R T r) = algebraMap R T (ρ r))
    (S : Set T) (hS : ∀ s ∈ S, σ s ∈ Algebra.adjoin R S)
    (hSO : ∀ s ∈ S, ι s ∈ O) (hRO : ∀ r : R, ι (algebraMap R T r) ∈ O)
    (hσO : ∀ t : T, ι t ∈ O → ι (σ t) - ι t ∈ O.nonunits)
    (I : Ideal ↥(TwoChartIntegralModel.chartAlg R T S)) [I.IsPrime]
    (hI : ∀ b : ↥(TwoChartIntegralModel.chartAlg R T S), ι (b : T) ∈ O.nonunits → b ∈ I)
    (f : T) (g h : ↥(TwoChartIntegralModel.chartAlg R T S)) (hh : h ∉ I) (hfg : f * (h : T) = (g : T)) :
    ∃ g' h' : ↥(TwoChartIntegralModel.chartAlg R T S), h' ∉ I ∧ g' ∈ I ∧ (σ f - f) * (h' : T) = (g' : T) := by
  have hmemO : ∀ b : ↥(TwoChartIntegralModel.chartAlg R T S), ι (b : T) ∈ O :=
    fun b => chartAlg_le_comap ι O S hSO hRO b.2
  let σg : ↥(TwoChartIntegralModel.chartAlg R T S) := ⟨σ g, chartAlg_map_mem σ ρ hσ S hS g.2⟩
  let σh : ↥(TwoChartIntegralModel.chartAlg R T S) := ⟨σ h, chartAlg_map_mem σ ρ hσ S hS h.2⟩
  have hdiff : ∀ (b b' : ↥(TwoChartIntegralModel.chartAlg R T S)), (b' : T) = σ b → b' - b ∈ I := by
    intro b b' hb'
    apply hI
    rw [Subalgebra.coe_sub, map_sub, hb']
    exact hσO b (hmemO b)
  have hdg : σg - g ∈ I := hdiff g σg rfl
  have hdh : σh - h ∈ I := hdiff h σh rfl
  have hσh : σh ∉ I := by
    intro hmem
    apply hh
    have := I.sub_mem hmem hdh
    rwa [sub_sub_cancel] at this
  refine ⟨σg * h - g * σh, h * σh, ?_, ?_, ?_⟩
  · exact fun hmem => (Ideal.IsPrime.mem_or_mem ‹_› hmem).elim hh hσh
  · have : σg * h - g * σh = (σg - g) * h - g * (σh - h) := by ring
    rw [this]
    exact I.sub_mem (I.mul_mem_right _ hdg) (I.mul_mem_left _ hdh)
  · have hσfg : σ f * σ (h : T) = σ (g : T) := by rw [← map_mul, hfg]
    rw [Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_mul]
    change (σ f - f) * ((h : T) * σ (h : T)) = σ (g : T) * (h : T) - (g : T) * σ (h : T)
    linear_combination (h : T) * hσfg - (σ (h : T)) * hfg

section Inertia

open scoped Pointwise

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem mem_inertiaSubgroupIn_iff {A : ValuationSubring L} {σ : L ≃ₐ[K] L} :
    σ ∈ A.inertiaSubgroupIn K ↔
      ∃ h : σ ∈ A.decompositionSubgroup K, (⟨σ, h⟩ : A.decompositionSubgroup K) ∈ A.inertiaSubgroup K := by
  constructor
  · rintro ⟨⟨τ, hτ⟩, hτI, rfl⟩
    exact ⟨hτ, hτI⟩
  · rintro ⟨h, hI⟩
    exact ⟨⟨σ, h⟩, hI, rfl⟩

theorem apply_mem_iff {A : ValuationSubring L} {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.decompositionSubgroup K) (x : L) : σ x ∈ A ↔ x ∈ A := by
  have hσ' : σ⁻¹ • A = A :=
    MulAction.mem_stabilizer_iff.mp ((A.decompositionSubgroup K).inv_mem hσ)
  calc σ x ∈ A ↔ σ • x ∈ A := Iff.rfl
    _ ↔ x ∈ σ⁻¹ • A := by rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_inv]
    _ ↔ x ∈ A := by rw [hσ']

theorem residue_apply_eq {A : ValuationSubring L} {σ : L ≃ₐ[K] L} (hσ : σ ∈ A.inertiaSubgroupIn K)
    {x : L} (hx : x ∈ A) :
    IsLocalRing.residue A ⟨σ x, (apply_mem_iff (mem_inertiaSubgroupIn_iff.mp hσ).1 x).mpr hx⟩ =
      IsLocalRing.residue A ⟨x, hx⟩ := by
  obtain ⟨hd, hI⟩ := mem_inertiaSubgroupIn_iff.mp hσ
  set a : A := ⟨x, hx⟩
  set g : A.decompositionSubgroup K := ⟨σ, hd⟩
  have hker : (MulSemiringAction.toRingAut (A.decompositionSubgroup K) (IsLocalRing.ResidueField A)) g = 1 :=
    (MonoidHom.mem_ker).mp hI
  have happ : (MulSemiringAction.toRingAut (A.decompositionSubgroup K)
      (IsLocalRing.ResidueField A) g) (IsLocalRing.residue A a)
      = g • (IsLocalRing.residue A a) := rfl
  have hres : IsLocalRing.residue A (g • a) = IsLocalRing.residue A a := by
    rw [IsLocalRing.ResidueField.residue_smul, ← happ, hker]
    rfl
  have hcoe : (g • a : A) = ⟨σ x, (apply_mem_iff hd x).mpr hx⟩ := Subtype.ext rfl
  rw [← hcoe]
  exact hres

def restrictAut (A : ValuationSubring L) (σ : L ≃ₐ[K] L) (hσ : σ ∈ A.decompositionSubgroup K) : A →+* A where
  toFun x := ⟨σ x, (apply_mem_iff hσ x).mpr x.2⟩
  map_one' := Subtype.ext (map_one σ)
  map_mul' x y := Subtype.ext (map_mul σ (x : L) (y : L))
  map_zero' := Subtype.ext (map_zero σ)
  map_add' x y := Subtype.ext (map_add σ (x : L) (y : L))

@[scoped simp] theorem coe_restrictAut_apply (A : ValuationSubring L) (σ : L ≃ₐ[K] L) (hσ : σ ∈ A.decompositionSubgroup K)
    (x : A) : ((restrictAut A σ hσ x : A) : L) = σ x := rfl

end Inertia

open ModularCurve.FullLevel in
theorem smul_sub_mem_nonunits {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
    (O : ValuationSubring ↥(fieldBar q M'))
    (hO : ∀ f : ↥(fieldBar q M'), f ∈ O ↔
      ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : τ ∈ A.inertiaSubgroupIn ℚ)
    (t : ↥(fieldBar q M')) (ht : t ∈ O) :
    arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • t ∈ O ∧
    (arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • t) - t ∈ O.nonunits := by
  have hd : τ ∈ A.decompositionSubgroup ℚ := (mem_inertiaSubgroupIn_iff.mp hτ).1
  let Tτ : ↥(fieldBar q M') →+* ↥(fieldBar q M') :=
    (SemilinearAut.toRingAut (arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ) :
      ↥(fieldBar q M') ≃+* ↥(fieldBar q M')).toRingHom
  have hT : ∀ f, Tτ f = arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • f := fun f => rfl
  obtain ⟨hTf, hmax⟩ :=
    ValuationSubring.mem_and_sub_mem_maximalIdeal_of_gaussPresentation_of_coe_eq_of_coeffMap_residue_comp_eq
      A (fieldBar q M') O hO
      (coeffMap (τ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) (coeffMap (restrictAut A τ hd))
      (fun y => by
        rw [coeffMap_coeffMap, coeffMap_coeffMap]
        exact coeffMap_congr (RingHom.ext fun x => rfl) y)
      (fun y => by
        rw [coeffMap_coeffMap]
        exact coeffMap_congr (RingHom.ext fun x => residue_apply_eq hτ x.2) y)
      Tτ (fun f => rfl) t ht
  refine ⟨hTf, ?_⟩
  rw [← hT]
  exact (ValuationSubring.coe_mem_nonunits_iff).mpr hmax

theorem coeffMap_mem_laurentBaseChange_ringHom {L : Type*} [Field L] [Algebra ℚ L]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (φ : L →+* L) {x : LaurentSeries L}
    (hx : x ∈ laurentBaseChange L F₀) : coeffMap φ x ∈ laurentBaseChange L F₀ := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [coeffMap_algebraMap]
        exact (laurentBaseChange L F₀).algebraMap_mem _
      · have : coeffMap φ (coeffEmb L z) = coeffEmb L z := by
          unfold coeffEmb
          rw [coeffMap_coeffMap]
          exact coeffMap_congr (Subsingleton.elim _ _) z
        rw [this]
        exact coeffEmb_mem_laurentBaseChange L hz
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

theorem coeffMap_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (x : PowerSeries R) :
    coeffMap φ (HahnSeries.ofPowerSeries ℤ R x) = HahnSeries.ofPowerSeries ℤ S (x.map φ) := by
  ext k
  rw [coeffMap_coeff]
  rcases le_or_gt 0 k with hk | hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
  · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]

theorem jq_gauss (A : ValuationSubring (AlgebraicClosure ℚ)) :
    coeffMap A.subtype (HahnSeries.ofPowerSeries ℤ ↥A (jNum.map (Int.castRingHom ↥A))) =
      coeffEmb (AlgebraicClosure ℚ) jq * HahnSeries.single (1 : ℤ) 1 ∧
    coeffMap A.subtype (HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ↥A (jNum.map (Int.castRingHom ↥A))) =
      coeffEmb (AlgebraicClosure ℚ) jq ∧
    (coeffMap (IsLocalRing.residue ↥A)
      (HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ↥A (jNum.map (Int.castRingHom ↥A)))).coeff (-1) = 1 := by
  have hmm : ∀ {X Y Z : Type} [CommRing X] [CommRing Y] [CommRing Z] (f : X →+* Y) (g : Y →+* Z)
      (p : PowerSeries X), (p.map f).map g = p.map (g.comp f) := by
    intro X Y Z _ _ _ f g p
    rw [PowerSeries.map_comp]
    rfl
  have hP : coeffMap A.subtype (HahnSeries.ofPowerSeries ℤ ↥A (jNum.map (Int.castRingHom ↥A))) =
      HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (jNumQ.map (algebraMap ℚ (AlgebraicClosure ℚ))) := by
    rw [coeffMap_ofPowerSeries, hmm, jNumQ, hmm]
    congr 2
  have hJ : coeffEmb (AlgebraicClosure ℚ) jq =
      HahnSeries.single (-1 : ℤ) (1 : AlgebraicClosure ℚ) *
        HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (jNumQ.map (algebraMap ℚ (AlgebraicClosure ℚ))) := by
    unfold coeffEmb
    rw [jq, map_mul, coeffMap_single, map_one, coeffMap_ofPowerSeries]
  refine ⟨?_, ?_, ?_⟩
  · rw [hP, hJ, mul_comm (HahnSeries.single (-1 : ℤ) (1 : AlgebraicClosure ℚ)), mul_assoc,
      HahnSeries.single_mul_single, mul_one]
    norm_num
  · rw [map_mul, coeffMap_single, map_one, hP, hJ]
  · rw [map_mul, coeffMap_single, map_one, HahnSeries.coeff_single_mul, one_mul,
      show (-1 : ℤ) - (-1) = ((0 : ℕ) : ℤ) by norm_num, coeffMap_ofPowerSeries,
      HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_jNum]
    simp

end E143TI
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_sub_inMax_of_mem_inertiaSubgroupIn_of_inStalk_twoChartIntegralModel.E143TI"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace E143TI

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing

set_option hygiene false in
local notation "𝕂" => (ModularCurve.laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M')))
set_option hygiene false in
local notation "𝔛" => (AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥T j₁)

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem assembledTI (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (O : ValuationSubring ↥(fieldBar q M'))
    (hO : ∀ f : ↥(fieldBar q M'), f ∈ O ↔
      ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hOA : ∀ x : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') x ∈ O ↔ x ∈ A)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ))
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : AlgebraicClosure ℚ) ∈ A)
    [Algebra ↥k₀ ↥(fieldBar q M')]
    (T : IntermediateField ↥k₀ ↥(fieldBar q M'))
    (e : ↥𝕂 ≃+* ↥T)
    (he : ∀ f : ↥𝕂, (((e f : ↥T) : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffMap (algebraMap ↥K₁ (AlgebraicClosure ℚ)) (f : LaurentSeries ↥K₁))
    [Algebra ↥A₁ ↥T]
    (hcompat : ∀ a : ↥A₁, ((algebraMap ↥A₁ ↥T a : ↥T) : ↥(fieldBar q M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥K₁) : AlgebraicClosure ℚ))
    (j₁ : ↥T)
    (hj₁ : (j₁ : ↥(fieldBar q M')) = IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')))
    [Fact (j₁ ≠ 0)]
    (InStalk InMax : ↥𝔛 → ↥T → Prop) (GoodPt : ↥𝔛 → Prop)
    (hSt : ∀ (x : ↥𝔛) (f : ↥T), InStalk x f →
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥T j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥T j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥T j₁), h ∉ y.asIdeal ∧ f * (h : ↥T) = (g : ↥T)) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥T j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥T j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥T j₁), h ∉ y.asIdeal ∧ f * (h : ↥T) = (g : ↥T)))
    (hMx : ∀ (x : ↥𝔛) (f : ↥T),
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥T j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥T j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥T j₁), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : ↥T) = (g : ↥T)) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥T j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥T j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥T j₁), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : ↥T) = (g : ↥T)) →
      InMax x f)
    (hGd : ∀ x : ↥𝔛, GoodPt x →
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥T j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥T j₁).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥T j₁), ((b : ↥T) : ↥(fieldBar q M')) ∈ O.nonunits → b ∈ y.asIdeal) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥T j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥T j₁).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥T j₁), ((b : ↥T) : ↥(fieldBar q M')) ∈ O.nonunits → b ∈ y.asIdeal))
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : τ ∈ A.inertiaSubgroupIn ℚ)
    (hτK : ∀ a : AlgebraicClosure ℚ, a ∈ K₁ → τ a ∈ K₁) :
    (∀ f : ↥(fieldBar q M'), f ∈ T →
        ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • f ∈ T) ∧
      ∀ x : ↥𝔛, GoodPt x →
        ∀ (f : ↥T) (hτf : ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • (f : ↥(fieldBar q M')) ∈ T),
          InStalk x f → InMax x (⟨_, hτf⟩ - f) := by

  have hd : τ ∈ A.decompositionSubgroup ℚ := (mem_inertiaSubgroupIn_iff.mp hτ).1
  have hinjF : ∀ x y : ↥(fieldBar q M'),
      (x : LaurentSeries (AlgebraicClosure ℚ)) = (y : LaurentSeries (AlgebraicClosure ℚ)) → x = y :=
    fun x y h => Subtype.ext h

  let Tτ : ↥(fieldBar q M') →+* ↥(fieldBar q M') :=
    (SemilinearAut.toRingAut (arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ) :
      ↥(fieldBar q M') ≃+* ↥(fieldBar q M')).toRingHom
  have hTτ : ∀ f, Tτ f = arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • f := fun f => rfl
  have hTτL : ∀ f : ↥(fieldBar q M'), ((Tτ f : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffMap (τ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) (f : LaurentSeries (AlgebraicClosure ℚ)) := fun f => rfl

  let τ₁ : ↥K₁ →+* ↥K₁ :=
    ((τ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp (algebraMap ↥K₁ (AlgebraicClosure ℚ))).codRestrict K₁
      (fun x => hτK _ x.2)
  have hcomm : (τ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp (algebraMap ↥K₁ (AlgebraicClosure ℚ)) =
      (algebraMap ↥K₁ (AlgebraicClosure ℚ)).comp τ₁ := RingHom.ext fun _ => rfl

  have part1 : ∀ f : ↥(fieldBar q M'), f ∈ T →
      arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • f ∈ T := by
    intro f hf
    have hf' : (f : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffMap (algebraMap ↥K₁ (AlgebraicClosure ℚ)) ((e.symm ⟨f, hf⟩ : ↥𝕂) : LaurentSeries ↥K₁) := by
      rw [← he, e.apply_symm_apply]
    have hmem : coeffMap τ₁ ((e.symm ⟨f, hf⟩ : ↥𝕂) : LaurentSeries ↥K₁) ∈ 𝕂 :=
      coeffMap_mem_laurentBaseChange_ringHom _ τ₁ (e.symm ⟨f, hf⟩).2
    have key : arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • f =
        ((e ⟨_, hmem⟩ : ↥T) : ↥(fieldBar q M')) := by
      apply hinjF
      rw [he, ← hTτ, hTτL, hf', coeffMap_coeffMap, coeffMap_coeffMap, hcomm]
    rw [key]
    exact (e ⟨_, hmem⟩).2
  refine ⟨part1, ?_⟩

  let τT : ↥T →+* ↥T := (Tτ.comp (algebraMap ↥T ↥(fieldBar q M'))).codRestrict T (fun f => part1 _ f.2)
  have hτT : ∀ f : ↥T, ((τT f : ↥T) : ↥(fieldBar q M')) =
      arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • (f : ↥(fieldBar q M')) := fun f => rfl
  have hτTL : ∀ f : ↥T, (((τT f : ↥T) : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffMap (τ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) ((f : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) :=
    fun f => rfl
  let ρ : ↥A₁ →+* ↥A₁ := (τ₁.comp (algebraMap ↥A₁ ↥K₁)).codRestrict A₁ (fun a =>
    (hA₁ _).mpr ((apply_mem_iff hd _).mpr ((hA₁ _).mp a.2)))
  have hρ : ∀ a : ↥A₁, (((ρ a : ↥A₁) : ↥K₁) : AlgebraicClosure ℚ) = τ ((a : ↥K₁) : AlgebraicClosure ℚ) :=
    fun a => rfl
  have hσ : ∀ a : ↥A₁, τT (algebraMap ↥A₁ ↥T a) = algebraMap ↥A₁ ↥T (ρ a) := by
    intro a
    apply Subtype.ext
    apply hinjF
    have hconst : ∀ c : AlgebraicClosure ℚ,
        ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) =
          algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c := fun c => rfl
    rw [hτTL, hcompat, hcompat, hρ, hconst, hconst, coeffMap_algebraMap]
    rfl
  have hjL : ((j₁ : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) jq := by
    rw [hj₁]
    rfl
  have hτTj : τT j₁ = j₁ := by
    apply Subtype.ext
    apply hinjF
    rw [hτTL, hjL, coeffMap_coeffEmb]

  have hιT : ∀ t : ↥T, algebraMap ↥T ↥(fieldBar q M') t = (t : ↥(fieldBar q M')) := fun t => rfl
  have hRO : ∀ a : ↥A₁, algebraMap ↥T ↥(fieldBar q M') (algebraMap ↥A₁ ↥T a) ∈ O := by
    intro a
    rw [hιT, hcompat]
    exact (hOA _).mpr ((hA₁ _).mp a.2)
  obtain ⟨hJ1, hJ2, hJ3⟩ := jq_gauss A
  have hres_ne : coeffMap (IsLocalRing.residue ↥A)
      (HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ↥A (jNum.map (Int.castRingHom ↥A))) ≠ 0 := by
    intro h
    have h1 : (coeffMap (IsLocalRing.residue ↥A)
        (HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ↥A (jNum.map (Int.castRingHom ↥A)))).coeff (-1) =
        (0 : LaurentSeries (IsLocalRing.ResidueField ↥A)).coeff (-1) := by rw [h]
    rw [hJ3, HahnSeries.coeff_zero] at h1
    exact one_ne_zero h1
  have hjO : algebraMap ↥T ↥(fieldBar q M') j₁ ∈ O := by
    rw [hιT, hO]
    refine ⟨HahnSeries.ofPowerSeries ℤ ↥A (jNum.map (Int.castRingHom ↥A)), HahnSeries.single (1 : ℤ) 1, ?_, ?_⟩
    · rw [coeffMap_single, map_one]
      exact HahnSeries.single_ne_zero one_ne_zero
    · rw [hjL, coeffMap_single, map_one, hJ1]
  have hJne : coeffEmb (AlgebraicClosure ℚ) jq ≠ 0 := by
    intro h0
    apply (Fact.out : j₁ ≠ 0)
    apply Subtype.ext
    apply hinjF
    rw [hjL, h0]
    rfl
  have hjinvO : algebraMap ↥T ↥(fieldBar q M') j₁⁻¹ ∈ O := by
    rw [hιT, hO]
    refine ⟨1, HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ↥A (jNum.map (Int.castRingHom ↥A)), hres_ne, ?_⟩
    rw [hJ2, map_one, IntermediateField.coe_inv, IntermediateField.coe_inv, hjL, inv_mul_cancel₀ hJne]
  have hσO : ∀ t : ↥T, algebraMap ↥T ↥(fieldBar q M') t ∈ O →
      algebraMap ↥T ↥(fieldBar q M') (τT t) - algebraMap ↥T ↥(fieldBar q M') t ∈ O.nonunits := by
    intro t ht
    rw [hιT] at ht ⊢
    rw [hιT, hτT]
    exact (smul_sub_mem_nonunits O hO hτ _ ht).2

  intro x hx f hτf hst
  obtain ⟨hx3, hx4⟩ := hGd x hx
  obtain ⟨hsF, hsI⟩ := hSt x f hst
  have hτTf : (⟨_, hτf⟩ : ↥T) = τT f := rfl
  rw [hτTf]
  apply hMx
  constructor
  · intro y hy
    obtain ⟨g, h, hh, hfg⟩ := hsF y hy
    haveI : y.asIdeal.IsPrime := y.isPrime
    exact chart_step (algebraMap ↥T ↥(fieldBar q M')) O τT ρ hσ {j₁}
      (fun s hs => by
        rw [Set.mem_singleton_iff] at hs
        subst hs
        rw [hτTj]
        exact Algebra.self_mem_adjoin_singleton _ _)
      (fun s hs => by
        rw [Set.mem_singleton_iff] at hs
        subst hs
        exact hjO)
      hRO hσO y.asIdeal (fun b hb => hx3 y hy b hb) f g h hh hfg
  · intro y hy
    obtain ⟨g, h, hh, hfg⟩ := hsI y hy
    haveI : y.asIdeal.IsPrime := y.isPrime
    exact chart_step (algebraMap ↥T ↥(fieldBar q M')) O τT ρ hσ {j₁⁻¹}
      (fun s hs => by
        rw [Set.mem_singleton_iff] at hs
        subst hs
        rw [map_inv₀, hτTj]
        exact Algebra.self_mem_adjoin_singleton _ _)
      (fun s hs => by
        rw [Set.mem_singleton_iff] at hs
        subst hs
        exact hjinvO)
      hRO hσO y.asIdeal (fun b hb => hx4 y hy b hb) f g h hh hfg

end E143TI
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_sub_inMax_of_mem_inertiaSubgroupIn_of_inStalk_twoChartIntegralModel.E143TI"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s))
    (R : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) (hR : R.integers = OIg (lineInfty q))
    (hR₀O : ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers ↔
      (IntermediateField.inclusion hle f : fieldBar q M') ∈ OIg (lineInfty q))

    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ₀ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ₀⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (ζ₀ : ↥k₀) (hζ₀ : IsPrimitiveRoot ((ζ₀ : ↥k₀) : AlgebraicClosure ℚ) (q * ℓ))
    (ϖt : ↥k₀) (hϖtA : (ϖt : AlgebraicClosure ℚ) ∈ A)
    (hϖt : ∃ u : ↥A, IsUnit u ∧ (ϖt : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ))

    (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hK₁ : FiniteDimensional ↥k₀ ↥K₁)
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : AlgebraicClosure ℚ) ∈ A)
    [IsDiscreteValuationRing ↥A₁] [HenselianLocalRing ↥A₁] :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra

    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),
      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →
      (∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ F₀ → levelAutBar q M' ζ' γ f ∈ F₀) →
      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → AlgebraicClosure ℚ) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
      (∀ f : ↥(fieldBar q M'), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ Set.range ⇑(coeffEmb (AlgebraicClosure ℚ)) → f ∈ F₀) →

    ∀ [Algebra ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)],
      (∀ a : ↥A₁, ((algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) a : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) =
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥K₁) : AlgebraicClosure ℚ)) →
    ∀ (j₁ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      ((j₁ : ↥(fieldBar q M')) = IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M'))) →
    ∀ [Fact (j₁ ≠ 0)],

    let InStalk : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) → Prop := fun x f =>
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)))
    let InMax : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) → Prop := fun x f =>
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)))
    let Centred : Place (AlgebraicClosure ℚ) ↥(fieldBar q M') → ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Prop := fun P x =>
      P.IsRational ∧ ∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), InStalk x f →
        (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A ∧
          (A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ InMax x f)

    let GoodPt : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Prop := fun x =>
      (AlgebraicCurve.TwoChartIntegralModel.toBase ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base x = closedPoint ↥A₁ ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), x ⤳ y → y = x) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ R.integers.nonunits → b ∈ y.asIdeal) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ R.integers.nonunits → b ∈ y.asIdeal) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) →+* Ω), RingHom.ker φ = y.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) ∉ ModularCurve.ssJSet q Ω)

    let Reads : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → Prop := fun x Q =>
      ∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), InStalk x f →
        ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring ∧
          (R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring.nonunits ↔ InMax x f)

    ∀ τ ∈ A.inertiaSubgroupIn ℚ, (∀ a : AlgebraicClosure ℚ, a ∈ K₁ → τ a ∈ K₁) →
      (∀ f : ↥(fieldBar q M'), f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀ →
        ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • f ∈
          IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) ∧
      ∀ x : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), GoodPt x →
        ∀ (f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) (hτf : ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • (f : ↥(fieldBar q M')) ∈
            IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀),
          InStalk x f → InMax x (⟨_, hτf⟩ - f) := by
  letI instk₀ : Algebra ↥k₀ ↥(fieldBar q M') :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
  intro F₀ hF₀1 hF₀2 hF₀3 hF₀4 instAlg hcompat j₁ hj₁ instFact InStalk InMax Centred GoodPt Reads τ hτ hτK
  have hFT :=
    ModularCurve.FullLevel.exists_ringEquiv_laurentBaseChange_levelField_coe_eq_coeffMap
      q M' k₀ K₁ hK₁ F₀ hF₀1 (hF₀3 K₁ hK₁) hF₀4
  obtain ⟨e, he⟩ := hFT
  have hO : ∀ f : ↥(fieldBar q M'), f ∈ R.integers ↔
      ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x := by
    rw [hR]; exact hIg_inf
  exact E143TI.assembledTI q M' A hle R.integers hO R.algebraMap_mem_iff k₀ K₁ A₁ hA₁ _ e he hcompat j₁ hj₁
    InStalk InMax GoodPt (fun x f h => h) (fun x f h => h) (fun x hx => ⟨hx.2.2.1, hx.2.2.2.1⟩) τ hτ hτK

end S_ModularCurve_FullLevel_sub_inMax_of_mem_inertiaSubgroupIn_of_inStalk_twoChartIntegralModel
end P2MW
export P2MW.S_ModularCurve_FullLevel_sub_inMax_of_mem_inertiaSubgroupIn_of_inStalk_twoChartIntegralModel (solution)
