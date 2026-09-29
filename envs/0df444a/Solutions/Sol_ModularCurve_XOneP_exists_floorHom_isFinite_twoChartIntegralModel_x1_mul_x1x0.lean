-- Prove2me | solution 1 for ModularCurve.XOneP.exists_floorHom_isFinite_twoChartIntegralModel_x1_mul_x1x0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/9d00f3b9-c995-59c2-b4fc-57d08d9709c9

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_hom_isFinite_surjective_chartMap_finite_of_algHom
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_floorHom_isFinite_twoChartIntegralModel_x1_mul_x1x0
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

namespace CoverLoc44

theorem ringHom_finite_of_comp_eq {E K₁ K : Type*} [CommRing E] [CommRing K₁] [CommRing K]
    [Algebra E K] [Module.Finite E K] (g : E →+* K₁) (f : K₁ →+* K)
    (hcomp : f.comp g = algebraMap E K) : f.Finite := by
  letI : Algebra E K₁ := g.toAlgebra
  letI : Algebra K₁ K := f.toAlgebra
  haveI : IsScalarTower E K₁ K := IsScalarTower.of_algebraMap_eq fun e => by
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, ← RingHom.comp_apply, hcomp]
  exact Module.Finite.of_restrictScalars_finite E K₁ K

theorem finite_inclusion_of_finiteDimensional_adjoin
    {L : Type*} [Field L] {E : Type*} [Field E] [Algebra L E]
    (K₁ K : IntermediateField L E) (hle : K₁ ≤ K)
    (A : Type*) [CommSemiring A] [Algebra A L] [Algebra A ↥K] [IsScalarTower A L ↥K]
    [Algebra A ↥K₁] [IsScalarTower A L ↥K₁]
    (j : ↥K) (hjK₁ : (j : E) ∈ K₁)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K) :
    ((IntermediateField.inclusion hle).restrictScalars A).toRingHom.Finite := by
  set ι : ↥K₁ →ₐ[L] ↥K := IntermediateField.inclusion hle with hιdef
  set E₀ : IntermediateField L ↥K := IntermediateField.adjoin L ({j} : Set ↥K) with hE₀

  have hE₀le : E₀ ≤ ι.fieldRange := by
    rw [hE₀, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact (AlgHom.mem_fieldRange).mpr ⟨⟨(j : E), hjK₁⟩, Subtype.ext rfl⟩
  have hmem : ∀ e : ↥E₀, (((e : ↥K) : E)) ∈ K₁ := fun e => by
    obtain ⟨y, hy⟩ := (AlgHom.mem_fieldRange).mp (hE₀le e.2)
    rw [← hy]
    exact y.2

  let g : ↥E₀ →+* ↥K₁ :=
    { toFun := fun e => ⟨((e : ↥K) : E), hmem e⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  haveI : Module.Finite (↥E₀) (↥K) := hFD
  refine ringHom_finite_of_comp_eq (E := ↥E₀) (K₁ := ↥K₁) (K := ↥K) g _ (RingHom.ext fun e => ?_)
  exact Subtype.ext rfl

theorem isNoetherianRing_and_isFractionRing_charts
    (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [UniqueFactorizationMonoid A]
    (L : Type) [Field L] [CharZero L] [Algebra A L] [IsFractionRing A L]
    (F : Type) [Field F] [Algebra A F] [Algebra L F] [IsScalarTower A L F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental A j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set F)) F) :
    (IsNoetherianRing ↥(chartAlgFin A F j) ∧ IsFractionRing ↥(chartAlgFin A F j) F) ∧
    (IsNoetherianRing ↥(chartAlgInf A F j) ∧ IsFractionRing ↥(chartAlgInf A F j) F) := by
  haveI := hFD
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap L F).injective
  haveI : CharZero ↥(IntermediateField.adjoin L ({j} : Set F)) :=
    (algebraMap ↥(IntermediateField.adjoin L ({j} : Set F)) F).charZero
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j} : Set F)) F :=
    Algebra.IsAlgebraic.of_finite _ F
  haveI hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set F)) F := inferInstance
  obtain ⟨hF, hI⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L F j htj hFD hsep

  have hadj : IntermediateField.adjoin L ({j⁻¹} : Set F) = IntermediateField.adjoin L ({j} : Set F) := by
    apply le_antisymm
    · exact IntermediateField.adjoin_simple_le_iff.mpr
        (inv_mem (IntermediateField.mem_adjoin_simple_self L j))
    · refine IntermediateField.adjoin_simple_le_iff.mpr ?_
      have := inv_mem (IntermediateField.mem_adjoin_simple_self L j⁻¹)
      rwa [inv_inv] at this
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j⁻¹} : Set F)) F := by
    rw [hadj]; infer_instance
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · haveI := hF; exact Algebra.FiniteType.isNoetherianRing A _
  · exact AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg A L F {j}
  · haveI := hI; exact Algebra.FiniteType.isNoetherianRing A _
  · exact AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg A L F {j⁻¹}

theorem T_mem_Gamma1_inf_Gamma0 (M t : ℕ) :
    ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 t := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.T]
  · rw [CongruenceSubgroup.Gamma0_mem]
    simp [ModularGroup.T]

theorem T_mem_Gamma1 (M : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M := by
  rw [CongruenceSubgroup.Gamma1_mem]
  simp [ModularGroup.T]

end CoverLoc44

open CoverLoc44 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))

    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))
    (hle : K₁ ≤ K)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    [Algebra A ↥K₁] [IsScalarTower A L ↥K₁]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (j₁ : ↥K₁) (hj₁ : ((j₁ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₁ ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ}) :
    ∃ (m : AlgebraicCurve.TwoChartIntegralModel A (↥K) j ⟶ AlgebraicCurve.TwoChartIntegralModel A (↥K₁) j₁)
      (ιF : ↥(chartAlgFin A (↥K₁) j₁) →ₐ[A] ↥(chartAlgFin A (↥K) j))
      (ιI : ↥(chartAlgInf A (↥K₁) j₁) →ₐ[A] ↥(chartAlgInf A (↥K) j)),
      (∀ x, (((ιF x : ↥K) : LaurentSeries L)) = ((x : ↥K₁) : LaurentSeries L)) ∧
      (∀ x, (((ιI x : ↥K) : LaurentSeries L)) = ((x : ↥K₁) : LaurentSeries L)) ∧
      m ≫ toBase A (↥K₁) j₁ = toBase A (↥K) j ∧
      Spec.map (CommRingCat.ofHom ιF.toRingHom) ≫ ιFin A (↥K₁) j₁ = ιFin A (↥K) j ≫ m ∧
      Spec.map (CommRingCat.ofHom ιI.toRingHom) ≫ ιInf A (↥K₁) j₁ = ιInf A (↥K) j ≫ m ∧
      m ⁻¹ᵁ (ιFin A (↥K₁) j₁).opensRange = (ιFin A (↥K) j).opensRange ∧
      m ⁻¹ᵁ (ιInf A (↥K₁) j₁).opensRange = (ιInf A (↥K) j).opensRange ∧
      IsFinite m ∧ Function.Surjective m.base ∧
      ιF.toRingHom.Finite ∧ ιI.toRingHom.Finite ∧
      (∀ x : ↥K, x ∈ chartAlgFin A (↥K) j ↔
        IsIntegral ↥((ιF.range).map (chartAlgFin A (↥K) j).val) x) ∧
      (∀ x : ↥K, x ∈ chartAlgInf A (↥K) j ↔
        IsIntegral ↥((ιI.range).map (chartAlgInf A (↥K) j).val) x) := by
  classical

  let φ : ↥K₁ →ₐ[A] ↥K := (IntermediateField.inclusion hle).restrictScalars A
  have hφapply : ∀ x : ↥K₁, ((φ x : ↥K) : LaurentSeries L) = (x : LaurentSeries L) := fun x => rfl
  have hφj : φ j₁ = j := Subtype.ext (by rw [hφapply, hj₁, hj])

  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) (Nat.Prime.ne_zero Fact.out)⟩
  have hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma1 (M * p)) (T_mem_Gamma1 (M * p)) L K hK j hj
  have hjK₁ : (j : LaurentSeries L) ∈ K₁ := by rw [hj, ← hj₁]; exact j₁.2
  have hφfin : φ.toRingHom.Finite := finite_inclusion_of_finiteDimensional_adjoin K₁ K hle A j hjK₁ hFD

  have htj₁ : Transcendental A j₁ := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K₁ A j₁ hj₁
  have hFD₁ : FiniteDimensional ↥(IntermediateField.adjoin L ({j₁} : Set ↥K₁)) ↥K₁ :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p) (T_mem_Gamma1_inf_Gamma0 M p) L K₁
      (by rw [hK₁]; rfl) j₁ hj₁
  obtain ⟨hFfin, hFinf⟩ := isNoetherianRing_and_isFractionRing_charts A L (↥K₁) j₁ htj₁ hFD₁

  obtain ⟨m, ιF, ιI, hιF, hιI, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_hom_isFinite_surjective_chartMap_finite_of_algHom
      A (↥K₁) (↥K) φ hφfin j₁ j hφj hFfin hFinf
  exact ⟨m, ιF, ιI, fun x => by rw [hιF, hφapply], fun x => by rw [hιI, hφapply],
    h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

end S_ModularCurve_XOneP_exists_floorHom_isFinite_twoChartIntegralModel_x1_mul_x1x0
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_floorHom_isFinite_twoChartIntegralModel_x1_mul_x1x0 (solution)
