-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_constantTerm_chartAlgInf_twoChartIntegralModel_levelField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/6b77f045-2aa4-51d7-a8ef-33ea594501bb

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_mem_chartAlg_iff_mem_chartAlg_image_of_ringEquiv
import Theorems.Thm_ModularCurve_exists_ringHom_chartAlgInf_algebraMap_eq_coeff_zero_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_mem_maximalIdeal_apply_of_coe_mem_nonunits_gauss_of_mem_chartAlgInf_laurentBaseChange
import Definitions.Def_ModularCurve_XH
import Theorems.Thm_ModularCurve_FullLevel_exists_ringEquiv_laurentBaseChange_levelField_coe_eq_coeffMap
import Theorems.Thm_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_constantTerm_chartAlgInf_twoChartIntegralModel_levelField

set_option autoImplicit false

open scoped MatrixGroups

namespace E143

open AlgebraicCurve ModularCurve

universe u

theorem exists_ringEquiv_chartAlgInf_of_ringEquiv {R : Type u} [CommRing R] {F F' : Type u}
    [Field F] [Field F'] [Algebra R F] [Algebra R F']
    (e : F ≃+* F') (he : ∀ r : R, e (algebraMap R F r) = algebraMap R F' r)
    (j : F) (j₁ : F') (hj : e j = j₁) [Fact (j ≠ 0)] [Fact (j₁ ≠ 0)] :
    ∃ ε : ↥(TwoChartIntegralModel.chartAlgInf R F j) ≃+* ↥(TwoChartIntegralModel.chartAlgInf R F' j₁),
      (∀ b, ((ε b : ↥(TwoChartIntegralModel.chartAlgInf R F' j₁)) : F') = e (b : F)) ∧
      ∀ r : R, ε (algebraMap R _ r) = algebraMap R _ r := by
  subst hj
  exact ((TwoChartIntegralModel.mem_chartAlg_iff_mem_chartAlg_image_of_ringEquiv e he).2 j).1

theorem chartAlgInf_eq (A K : Type u) [CommRing A] [Field K] [Algebra A K] (j : K) [Fact (j ≠ 0)] :
    TwoChartIntegralModel.chartAlgInf A K j = TwoChart.chartAlgInf A K j := rfl

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) : Function.Injective (coeffMap φ) := by
  intro x y h
  ext k
  apply hφ
  rw [← coeffMap_coeff, ← coeffMap_coeff, h]

theorem coeffMap_algebraMap' {R S : Type*} [Field R] [Field S] (φ : R →+* S) (c : R) :
    coeffMap φ (algebraMap R (LaurentSeries R) c) = algebraMap S (LaurentSeries S) (φ c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem coeffMap_coeffEmb' {R S : Type*} [Field R] [Field S] [Algebra ℚ R] [Algebra ℚ S]
    (φ : R →+* S) (x : LaurentSeries ℚ) : coeffMap φ (coeffEmb R x) = coeffEmb S x := by
  unfold coeffEmb
  rw [coeffMap_coeffMap]
  exact coeffMap_congr (Subsingleton.elim _ _) x

theorem coeffMap_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (x : PowerSeries R) :
    coeffMap φ (HahnSeries.ofPowerSeries ℤ R x) = HahnSeries.ofPowerSeries ℤ S (x.map φ) := by
  ext k
  rw [coeffMap_coeff]
  rcases le_or_gt 0 k with hk | hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
  · have hk' : k ∉ Set.range (Nat.castOrderEmbedding : ℕ ↪o ℤ) := by
      rintro ⟨n, hn⟩
      simp only [Nat.castOrderEmbedding_apply] at hn
      omega
    rw [HahnSeries.ofPowerSeries_apply, HahnSeries.ofPowerSeries_apply,
      HahnSeries.embDomain_notin_range hk', HahnSeries.embDomain_notin_range hk', map_zero]

theorem core (Γ : Subgroup SL(2, ℤ)) (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = laurentBaseChange L (qExpFunctionFieldC ℚ Γ))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L]
    [IsFractionRing A L] [Algebra A ↥K] [IsScalarTower A L ↥K]
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (T : Type) [Field T] [Algebra A T] (e : ↥K ≃+* T)
    (he : ∀ a : A, e (algebraMap A ↥K a) = algebraMap A T a)
    (j₁ : T) [Fact (j₁ ≠ 0)]
    (hj : ((e.symm j₁ : ↥K) : LaurentSeries L) = coeffEmb L jq) :
    ∃ ψ : ↥(TwoChartIntegralModel.chartAlgInf A T j₁) →+* A,
      (∀ a : A, ψ (algebraMap A _ a) = a) ∧
      ψ (TwoChartIntegralModel.jInvChartInf A T j₁) = 0 ∧
      (∀ b : ↥(TwoChartIntegralModel.chartAlgInf A T j₁), ∀ k : ℤ, k < 0 →
        ((e.symm (b : T) : ↥K) : LaurentSeries L).coeff k = 0) ∧
      (∀ b : ↥(TwoChartIntegralModel.chartAlgInf A T j₁),
        algebraMap A L (ψ b) = ((e.symm (b : T) : ↥K) : LaurentSeries L).coeff 0) ∧
      (∀ b : ↥(TwoChartIntegralModel.chartAlgInf A T j₁), e.symm (b : T) ∈ W₀) ∧
      (∀ b : ↥(TwoChartIntegralModel.chartAlgInf A T j₁), e.symm (b : T) ∈ W₀.nonunits →
        ψ b ∈ IsLocalRing.maximalIdeal A) := by
  have hej : e (e.symm j₁) = j₁ := e.apply_symm_apply j₁
  haveI : Fact (e.symm j₁ ≠ 0) :=
    ⟨fun h => (Fact.out : j₁ ≠ 0) (by rw [← hej, h, map_zero])⟩
  obtain ⟨ε, hε, hεA⟩ := exists_ringEquiv_chartAlgInf_of_ringEquiv e he (e.symm j₁) j₁ hej
  obtain ⟨ψ₀, h1, hord, h0, hjinv⟩ :=
    ModularCurve.exists_ringHom_chartAlgInf_algebraMap_eq_coeff_zero_of_coe_eq_coeffEmb_jq
      L K A (e.symm j₁) hj
  obtain ⟨hW, hmax⟩ :=
    ModularCurve.mem_maximalIdeal_apply_of_coe_mem_nonunits_gauss_of_mem_chartAlgInf_laurentBaseChange
      Γ L K hK A (e.symm j₁) hj W₀ hW₀ ψ₀ h0 hord

  let ι₀ : ↥(TwoChartIntegralModel.chartAlgInf A (↥K) (e.symm j₁)) ≃ₐ[A]
      ↥(TwoChart.chartAlgInf A (↥K) (e.symm j₁)) :=
    Subalgebra.equivOfEq _ _ (chartAlgInf_eq A (↥K) (e.symm j₁))
  have hεs : ∀ x : ↥(TwoChartIntegralModel.chartAlgInf A T j₁),
      ((ε.symm x : ↥(TwoChartIntegralModel.chartAlgInf A (↥K) (e.symm j₁))) : ↥K) = e.symm (x : T) := by
    intro x
    apply e.injective
    rw [e.apply_symm_apply, ← hε, RingEquiv.apply_symm_apply]
  let θ : ↥(TwoChartIntegralModel.chartAlgInf A T j₁) →+* ↥(TwoChart.chartAlgInf A (↥K) (e.symm j₁)) :=
    ι₀.toRingEquiv.toRingHom.comp ε.symm.toRingHom
  have hθ : ∀ x, ((θ x : ↥(TwoChart.chartAlgInf A (↥K) (e.symm j₁))) : ↥K) = e.symm (x : T) := by
    intro x
    rw [← hεs]
    rfl
  refine ⟨ψ₀.comp θ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    have hθa : θ (algebraMap A _ a) = algebraMap A _ a := by
      apply Subtype.ext
      rw [hθ, Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap, ← he, e.symm_apply_apply]
    rw [RingHom.comp_apply, hθa, h1]
  · have hθj : θ (TwoChartIntegralModel.jInvChartInf A T j₁) = TwoChart.jInvChartInf A (↥K) (e.symm j₁) := by
      apply Subtype.ext
      rw [hθ, TwoChartIntegralModel.coe_jInvChartInf, TwoChart.coe_jInvChartInf, map_inv₀]
    rw [RingHom.comp_apply, hθj, hjinv]
  · intro b k hk
    rw [← hθ]
    exact hord (θ b) k hk
  · intro b
    rw [RingHom.comp_apply, h0, hθ]
  · intro b
    rw [← hθ]
    exact hW (θ b)
  · intro b hb
    rw [RingHom.comp_apply]
    exact hmax (θ b) (by rw [hθ]; exact hb)

theorem bridge {K₁ Ω : Type} [Field K₁] [Field Ω] (ι : K₁ →+* Ω)
    (A : ValuationSubring Ω) (A₁ : ValuationSubring K₁) (hA₁ : ∀ x : K₁, x ∈ A₁ ↔ ι x ∈ A)
    (K : IntermediateField K₁ (LaurentSeries K₁)) (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries ↥A₁, y.map (IsLocalRing.residue ↥A₁) ≠ 0 ∧
      (f : LaurentSeries K₁) * HahnSeries.ofPowerSeries ℤ K₁ (y.map (algebraMap ↥A₁ K₁))
        = HahnSeries.ofPowerSeries ℤ K₁ (x.map (algebraMap ↥A₁ K₁)))
    (hW₀' : ∀ (f : ↥K) (x y : PowerSeries ↥A₁), y.map (IsLocalRing.residue ↥A₁) ≠ 0 →
        (f : LaurentSeries K₁) * HahnSeries.ofPowerSeries ℤ K₁ (y.map (algebraMap ↥A₁ K₁))
          = HahnSeries.ofPowerSeries ℤ K₁ (x.map (algebraMap ↥A₁ K₁)) →
        (f ∈ W₀.nonunits ↔ x.map (IsLocalRing.residue ↥A₁) = 0))
    (E : IntermediateField Ω (LaurentSeries Ω)) (O : ValuationSubring ↥E)
    (hO : ∀ g : ↥E, g ∈ O ↔ ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
        (g : LaurentSeries Ω) * coeffMap A.subtype y = coeffMap A.subtype x)
    (f : ↥K) (g : ↥E) (hfg : (g : LaurentSeries Ω) = coeffMap ι (f : LaurentSeries K₁))
    (hf : f ∈ W₀) (hg : (g : ↥E) ∈ O.nonunits) : f ∈ W₀.nonunits := by
  obtain ⟨x, y, hy, hxy⟩ := (hW₀ f).mp hf
  rw [hW₀' f x y hy hxy]
  by_contra hx

  let κ : ↥A₁ →+* ↥A := (ι.comp A₁.subtype).codRestrict A.toSubring (fun a => (hA₁ a).mp a.2)
  have hAκ : A.subtype.comp κ = ι.comp (algebraMap ↥A₁ K₁) := RingHom.ext fun _ => rfl
  have hmapA : ∀ z : PowerSeries ↥A₁,
      coeffMap A.subtype (coeffMap κ (HahnSeries.ofPowerSeries ℤ ↥A₁ z)) =
        coeffMap ι (HahnSeries.ofPowerSeries ℤ K₁ (z.map (algebraMap ↥A₁ K₁))) := by
    intro z
    rw [coeffMap_coeffMap, hAκ, ← coeffMap_coeffMap, coeffMap_ofPowerSeries]
  have hres : ∀ z : PowerSeries ↥A₁, z.map (IsLocalRing.residue ↥A₁) ≠ 0 →
      coeffMap (IsLocalRing.residue ↥A) (coeffMap κ (HahnSeries.ofPowerSeries ℤ ↥A₁ z)) ≠ 0 := by
    intro z hz h
    apply hz
    ext n
    have hn := congrArg (fun s => s.coeff (n : ℤ)) h
    simp only [coeffMap_coeff, HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.coeff_zero] at hn
    rw [PowerSeries.coeff_map, map_zero]
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hn ⊢
    exact fun hu => hn (hu.map κ)
  set X : LaurentSeries ↥A := coeffMap κ (HahnSeries.ofPowerSeries ℤ ↥A₁ x) with hX
  set Y : LaurentSeries ↥A := coeffMap κ (HahnSeries.ofPowerSeries ℤ ↥A₁ y) with hY
  have hgY : (g : LaurentSeries Ω) * coeffMap A.subtype Y = coeffMap A.subtype X := by
    rw [hX, hY, hmapA, hmapA, hfg, ← map_mul, hxy]
  have hXne : coeffMap (IsLocalRing.residue ↥A) X ≠ 0 := hres x hx
  have hYne : coeffMap (IsLocalRing.residue ↥A) Y ≠ 0 := hres y hy
  have hX0 : coeffMap A.subtype X ≠ 0 := by
    intro h
    apply hXne
    have : X = 0 := coeffMap_injective A.subtype Subtype.val_injective (by rw [h, map_zero])
    rw [this, map_zero]
  have hg0 : (g : LaurentSeries Ω) ≠ 0 := by
    intro h
    apply hX0
    rw [← hgY, h, zero_mul]
  have hgO : (g : ↥E)⁻¹ ∈ O := (hO _).mpr ⟨Y, X, hXne, by
    rw [IntermediateField.coe_inv, inv_mul_eq_iff_eq_mul₀ hg0, hgY]⟩
  rcases (ValuationSubring.mem_nonunits_iff_or (A := O)).mp hg with h | h
  · exact hg0 (by rw [h]; rfl)
  · exact h hgO

end E143

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace E143

open AlgebraicCurve ModularCurve ModularCurve.FullLevel

set_option hygiene false in
local notation "𝕂" => (ModularCurve.laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M')))

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem assembled (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (O : ValuationSubring ↥(fieldBar q M'))
    (hO : ∀ f : ↥(fieldBar q M'), f ∈ O ↔
      ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ))
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : AlgebraicClosure ℚ) ∈ A)
    [IsDiscreteValuationRing ↥A₁]
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
    [Fact (j₁ ≠ 0)] :
    ∃ ψ : ↥(TwoChartIntegralModel.chartAlgInf ↥A₁ ↥T j₁) →+* ↥A₁,
      (∀ a : ↥A₁, ψ (algebraMap ↥A₁ ↥(TwoChartIntegralModel.chartAlgInf ↥A₁ ↥T j₁) a) = a) ∧
      ψ (TwoChartIntegralModel.jInvChartInf ↥A₁ ↥T j₁) = 0 ∧
      (∀ b : ↥(TwoChartIntegralModel.chartAlgInf ↥A₁ ↥T j₁),
        ((b : ↥T) : ↥(fieldBar q M')) ∈ qIntegersBar (AlgebraicClosure ℚ) (fieldBar q M')) ∧
      (∀ b : ↥(TwoChartIntegralModel.chartAlgInf ↥A₁ ↥T j₁),
        (((b : ↥T) : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)).coeff 0 =
          (((ψ b : ↥A₁) : ↥K₁) : AlgebraicClosure ℚ)) ∧
      (∀ b : ↥(TwoChartIntegralModel.chartAlgInf ↥A₁ ↥T j₁),
        ((b : ↥T) : ↥(fieldBar q M')) ∈ O.nonunits → ψ b ∈ IsLocalRing.maximalIdeal ↥A₁) := by

  letI instAK : Algebra ↥A₁ ↥𝕂 := ((algebraMap ↥K₁ ↥𝕂).comp (algebraMap ↥A₁ ↥K₁)).toAlgebra
  haveI instST := IsScalarTower.of_algebraMap_eq' (R := ↥A₁) (S := ↥K₁) (A := ↥𝕂) rfl
  have hinjT : ∀ x y : ↥T,
      ((x : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) =
        ((y : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) → x = y :=
    fun x y h => Subtype.ext (Subtype.ext h)
  have he' : ∀ a : ↥A₁, e (algebraMap ↥A₁ ↥𝕂 a) = algebraMap ↥A₁ ↥T a := by
    intro a
    apply hinjT
    rw [he, hcompat]
    change coeffMap (algebraMap ↥K₁ (AlgebraicClosure ℚ)) (algebraMap ↥K₁ (LaurentSeries ↥K₁) (a : ↥K₁)) =
      algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) ((a : ↥K₁) : AlgebraicClosure ℚ)
    rw [E143.coeffMap_algebraMap']
    rfl
  have hsymm : ∀ y : ↥T, ((y : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffMap (algebraMap ↥K₁ (AlgebraicClosure ℚ)) ((e.symm y : ↥𝕂) : LaurentSeries ↥K₁) := by
    intro y
    rw [← he, e.apply_symm_apply]
  have hj : ((e.symm j₁ : ↥𝕂) : LaurentSeries ↥K₁) = coeffEmb ↥K₁ ModularCurve.jq := by
    apply E143.coeffMap_injective (algebraMap ↥K₁ (AlgebraicClosure ℚ))
      (algebraMap ↥K₁ (AlgebraicClosure ℚ)).injective
    rw [← hsymm, hj₁, E143.coeffMap_coeffEmb']
    rfl
  haveI hj0 : Fact ((e.symm j₁ : ↥𝕂) ≠ 0) :=
    ⟨fun h => (Fact.out : j₁ ≠ 0) (by rw [← e.apply_symm_apply j₁, h, map_zero])⟩

  have hW0 :=
    ModularCurve.exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC
      (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')) ↥K₁ 𝕂 rfl ↥A₁ (e.symm j₁) hj
  obtain ⟨W₀, hW₀, -, -, -, hW₀'⟩ := hW0

  have hcore :=
    E143.core (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')) ↥K₁ 𝕂 rfl ↥A₁ W₀ hW₀ ↥T e he' j₁ hj
  obtain ⟨ψ, hψA, hψj, hord, hψ0, hW, hmax⟩ := hcore
  refine ⟨ψ, hψA, hψj, fun b => ?_, fun b => ?_, fun b hb => ?_⟩
  ·
    rw [ModularCurve.mem_qIntegersBar_iff]
    by_contra hlt
    push Not at hlt
    have hq : ∀ f : ↥(fieldBar q M'), ModularCurve.qSeriesBar (AlgebraicClosure ℚ) (fieldBar q M') f =
        (f : LaurentSeries (AlgebraicClosure ℚ)) := fun f => rfl
    rw [hq, hsymm] at hlt
    have hne : coeffMap (algebraMap ↥K₁ (AlgebraicClosure ℚ))
        ((e.symm (b : ↥T) : ↥𝕂) : LaurentSeries ↥K₁) ≠ 0 := by
      intro h0
      rw [h0, HahnSeries.order_zero] at hlt
      exact lt_irrefl _ hlt
    have hk := fun h => hne (HahnSeries.coeff_order_eq_zero.mp h)
    rw [coeffMap_coeff, hord b _ hlt, map_zero] at hk
    exact hk rfl
  ·
    rw [hsymm, coeffMap_coeff, ← hψ0 b, IntermediateField.algebraMap_apply]
    rfl
  ·
    have hA₁' : ∀ x : ↥K₁, x ∈ A₁ ↔ algebraMap ↥K₁ (AlgebraicClosure ℚ) x ∈ A := fun x => by
      rw [IntermediateField.algebraMap_apply]; exact hA₁ x
    exact hmax b (E143.bridge (algebraMap ↥K₁ (AlgebraicClosure ℚ)) A A₁ hA₁' 𝕂 W₀ hW₀ hW₀'
      (fieldBar q M') O hO (e.symm (b : ↥T)) ((b : ↥T) : ↥(fieldBar q M'))
      (hsymm (b : ↥T)) (hW b) hb)

end E143

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
    ∃ ψ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) →+* ↥A₁,
      (∀ a : ↥A₁, ψ (algebraMap ↥A₁ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) a) = a) ∧
      ψ (AlgebraicCurve.TwoChartIntegralModel.jInvChartInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) = 0 ∧
      (∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁),
        ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ qIntegersBar (AlgebraicClosure ℚ) (fieldBar q M')) ∧
      (∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁),
        ((((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ))).coeff 0 =
          (((ψ b : ↥A₁) : ↥K₁) : AlgebraicClosure ℚ)) ∧
      (∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁),
        ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ R.integers.nonunits → ψ b ∈ maximalIdeal ↥A₁) := by
  letI instk₀ : Algebra ↥k₀ ↥(fieldBar q M') :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
  intro F₀ hF₀1 hF₀2 hF₀3 hF₀4 instAlg hcompat j₁ hj₁ instFact
  have hFT :=
    ModularCurve.FullLevel.exists_ringEquiv_laurentBaseChange_levelField_coe_eq_coeffMap
      q M' k₀ K₁ hK₁ F₀ hF₀1 (hF₀3 K₁ hK₁) hF₀4
  obtain ⟨e, he⟩ := hFT
  have hO : ∀ f : ↥(fieldBar q M'), f ∈ R.integers ↔
      ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x := by
    rw [hR]; exact hIg_inf
  exact E143.assembled q M' A hle R.integers hO k₀ K₁ A₁ hA₁ _ e he hcompat j₁ hj₁

end S_ModularCurve_FullLevel_exists_constantTerm_chartAlgInf_twoChartIntegralModel_levelField
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_constantTerm_chartAlgInf_twoChartIntegralModel_levelField (solution)
