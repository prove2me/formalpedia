-- Prove2me | solution 1 for ModularCurve.exists_chartAlg_residue_mul_eq_residue_of_coe_eq_coeffMap_of_residue_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/16deb69a-dfb3-5fb2-bd1b-f4ab1c0650bb

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_mem_iff_map_mem_and_mem_nonunits_iff_of_gaussPresentation_of_coe_eq_coeffMap
import Theorems.Thm_ModularCurve_exists_map_mem_and_sub_mem_nonunits_gauss_of_coe_eq_coeffMap_of_residue_surjective
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_chartAlg_residue_mul_eq_residue_of_coe_eq_coeffMap_of_residue_surjective

set_option autoImplicit false

open ModularCurve AlgebraicCurve IsLocalRing

namespace E148H1

theorem mem_nonunits_comap_iff {K L : Type*} [Field K] [Field L] (O : ValuationSubring L) (f : K →+* L) (x : K) :
    x ∈ (O.comap f).nonunits ↔ f x ∈ O.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap,
    map_inv₀, map_eq_zero_iff f f.injective]

theorem map_reverse_ne_zero {A k : Type*} [CommRing A] [CommRing k] (r : A →+* k) (P : Polynomial A)
    (hP : P.map r ≠ 0) : P.reverse.map r ≠ 0 := by
  intro h
  apply hP
  ext n
  rw [Polynomial.coeff_map, Polynomial.coeff_zero]
  by_cases hn : n ≤ P.natDegree
  · have := congrArg (fun Q => Q.coeff (Polynomial.revAt P.natDegree n)) h
    simp only [Polynomial.coeff_map, Polynomial.coeff_reverse, Polynomial.revAt_invol, Polynomial.coeff_zero] at this
    exact this
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hn), map_zero]

end E148H1

open E148H1

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hT : ModularGroup.T ∈ Γ)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ))
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : AlgebraicClosure ℚ) ∈ A)
    [IsDiscreteValuationRing ↥A₁]

    (hκ₁ : Function.Surjective
      (fun a : ↥A₁ => IsLocalRing.residue ↥A ⟨((a : ↥K₁) : AlgebraicClosure ℚ), (hA₁ (a : ↥K₁)).mp a.2⟩))
    (K : IntermediateField ↥K₁ (LaurentSeries ↥K₁))
    (hK : K = ModularCurve.laurentBaseChange ↥K₁ (ModularCurve.qExpFunctionFieldC ℚ Γ))
    [Algebra ↥A₁ ↥K] [IsScalarTower ↥A₁ ↥K₁ ↥K]
    (E : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)))
    (hE : E = ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))

    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : RegularProlongation A ↥E Fbar)
    (hO : ∀ f : ↥E, f ∈ R.integers ↔ ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
      (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)

    (T : Type) [Field T] [Algebra ↥A₁ T] [Algebra ↥K₁ T] [IsScalarTower ↥A₁ ↥K₁ T]
    (jT : T) [Fact (jT ≠ 0)] (htj : Transcendental ↥K₁ jT)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin ↥K₁ ({jT} : Set T)) T)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin ↥K₁ ({jT} : Set T)) T)
    (e : ↥K ≃+* T) (hcomm : ∀ a : ↥A₁, e (algebraMap ↥A₁ ↥K a) = algebraMap ↥A₁ T a)
    (hj : (((e.symm jT : ↥K)) : LaurentSeries ↥K₁) = coeffEmb ↥K₁ jq)
    (ψ : T →+* ↥E)
    (hψ : ∀ w : ↥K, ((ψ (e w) : ↥E) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffMap (algebraMap ↥K₁ (AlgebraicClosure ℚ)) ((w : ↥K) : LaurentSeries ↥K₁)) :
    (∀ g : Fbar, ∃ a b : ↥(TwoChartIntegralModel.chartAlgFin ↥A₁ T jT),
      ∃ (ha : ψ (a : T) ∈ R.integers) (hb : ψ (b : T) ∈ R.integers),
        R.residue ⟨ψ (b : T), hb⟩ ≠ 0 ∧ g * R.residue ⟨ψ (b : T), hb⟩ = R.residue ⟨ψ (a : T), ha⟩) ∧
    (∀ g : Fbar, ∃ a b : ↥(TwoChartIntegralModel.chartAlgInf ↥A₁ T jT),
      ∃ (ha : ψ (a : T) ∈ R.integers) (hb : ψ (b : T) ∈ R.integers),
        R.residue ⟨ψ (b : T), hb⟩ ≠ 0 ∧ g * R.residue ⟨ψ (b : T), hb⟩ = R.residue ⟨ψ (a : T), ha⟩) := by
  classical

  haveI hjK : Fact (e.symm jT ≠ 0) := ⟨fun h => (Fact.out : jT ≠ 0) (by rw [← e.apply_symm_apply jT, h, map_zero])⟩
  have hej : e (e.symm jT) = jT := e.apply_symm_apply jT
  let σ : ↥K ≃ₐ[↥A₁] T := AlgEquiv.ofRingEquiv (f := e) hcomm
  have hσ : ∀ w, σ w = e w := fun _ => rfl

  obtain ⟨W₀, hW₀, hW₀A, hW₀m, hW₀j, -⟩ :=
    ModularCurve.exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC Γ ↥K₁ K hK ↥A₁ (e.symm jT) hj

  let φ' : ↥K →+* ↥E := ψ.comp e.toRingHom
  have hφ' : ∀ f : ↥K, ((φ' f : ↥E) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffMap (algebraMap ↥K₁ (AlgebraicClosure ℚ)) ((f : ↥K) : LaurentSeries ↥K₁) := fun f => hψ f

  obtain ⟨hbr1, hbr2⟩ := ModularCurve.mem_iff_map_mem_and_mem_nonunits_iff_of_gaussPresentation_of_coe_eq_coeffMap
    k₀ K₁ A A₁ hA₁ K W₀ hW₀ E R.integers hO φ' hφ'
  have hdense := ModularCurve.exists_map_mem_and_sub_mem_nonunits_gauss_of_coe_eq_coeffMap_of_residue_surjective
    Γ hT k₀ K₁ A A₁ hA₁ hκ₁ K hK E hE R.integers hO φ' hφ'

  let OT : ValuationSubring T := R.integers.comap ψ
  have hOT : ∀ t : T, t ∈ OT ↔ ψ t ∈ R.integers := fun _ => ValuationSubring.mem_comap
  have hOTe : ∀ w : ↥K, e w ∈ OT ↔ w ∈ W₀ := fun w => (hOT _).trans (hbr1 w).symm
  have hOTe' : ∀ w : ↥K, e w ∈ OT.nonunits ↔ w ∈ W₀.nonunits := fun w =>
    (mem_nonunits_comap_iff R.integers ψ (e w)).trans (hbr2 w).symm

  have hVA : ∀ a : ↥A₁, algebraMap ↥A₁ T a ∈ OT := fun a => by
    rw [← hcomm, hOTe]; exact hW₀A a
  have hVm : ∀ a ∈ IsLocalRing.maximalIdeal ↥A₁, algebraMap ↥A₁ T a ∈ OT.nonunits := fun a ha => by
    rw [← hcomm, hOTe']; exact hW₀m a ha
  have haeval : ∀ P : Polynomial ↥A₁, Polynomial.aeval jT P = e (Polynomial.aeval (e.symm jT) P) := fun P => by
    rw [← hσ, ← Polynomial.aeval_algHom_apply σ, hσ, hej]
  have hVj : ∀ P : Polynomial ↥A₁, P.map (IsLocalRing.residue ↥A₁) ≠ 0 →
      Polynomial.aeval jT P ∈ OT ∧ (Polynomial.aeval jT P)⁻¹ ∈ OT := fun P hP => by
    obtain ⟨h1, h2⟩ := hW₀j P hP
    rw [haeval, ← map_inv₀, hOTe, hOTe]
    exact ⟨h1, h2⟩
  have hjOT : jT ∈ OT ∧ jT⁻¹ ∈ OT := by
    have := hVj Polynomial.X (by rw [Polynomial.map_X]; exact Polynomial.X_ne_zero)
    rwa [Polynomial.aeval_X] at this
  have hVj' : ∀ P : Polynomial ↥A₁, P.map (IsLocalRing.residue ↥A₁) ≠ 0 →
      Polynomial.aeval jT⁻¹ P ∈ OT ∧ (Polynomial.aeval jT⁻¹ P)⁻¹ ∈ OT := fun P hP => by
    letI : Invertible (jT⁻¹) := invertibleOfNonzero (inv_ne_zero (Fact.out : jT ≠ 0))
    have hinv : (⅟(jT⁻¹) : T) = jT := by rw [invOf_eq_inv, inv_inv]
    have key : Polynomial.aeval jT⁻¹ P = Polynomial.aeval jT P.reverse * (jT⁻¹) ^ P.natDegree := by
      rw [Polynomial.aeval_def, Polynomial.aeval_def, ← Polynomial.eval₂_reverse_mul_pow (algebraMap ↥A₁ T) jT⁻¹ P, hinv]
    obtain ⟨h1, h2⟩ := hVj P.reverse (map_reverse_ne_zero _ P hP)
    refine ⟨?_, ?_⟩
    · rw [key]; exact mul_mem h1 (pow_mem hjOT.2 _)
    · rw [key, mul_inv, ← inv_pow, inv_inv]; exact mul_mem h2 (pow_mem hjOT.1 _)

  have finish : ∀ (B : Subalgebra ↥A₁ T) (𝔓 : Ideal ↥B),
      (∀ b : ↥B, (b : T) ∈ OT) →
      (∀ b : ↥B, b ∈ 𝔓 ↔ (b : T) ∈ OT.nonunits) →
      (∀ f : T, f ∈ OT ↔ ∃ a b : ↥B, b ∉ 𝔓 ∧ f * (b : T) = (a : T)) →
      ∀ g : Fbar, ∃ a b : ↥B, ∃ (ha : ψ (a : T) ∈ R.integers) (hb : ψ (b : T) ∈ R.integers),
        R.residue ⟨ψ (b : T), hb⟩ ≠ 0 ∧ g * R.residue ⟨ψ (b : T), hb⟩ = R.residue ⟨ψ (a : T), ha⟩ := by
    intro B 𝔓 hB h𝔓 hloc g
    obtain ⟨⟨f, hf⟩, rfl⟩ := R.residue_surjective g
    obtain ⟨w, hwO, hfw⟩ := hdense f hf
    have ht : e w ∈ OT := (hOT _).mpr hwO
    obtain ⟨a, b, hb𝔓, hab⟩ := (hloc (e w)).mp ht
    have haR : ψ (a : T) ∈ R.integers := (hOT _).mp (hB a)
    have hbR : ψ (b : T) ∈ R.integers := (hOT _).mp (hB b)
    have hbunit : R.residue ⟨ψ (b : T), hbR⟩ ≠ 0 := by
      apply R.residue_ne_zero_of_isUnit
      have hnn : ψ (b : T) ∉ R.integers.nonunits := fun h =>
        hb𝔓 ((h𝔓 b).mpr ((mem_nonunits_comap_iff R.integers ψ _).mpr h))
      by_contra hu
      exact hnn ((ValuationSubring.coe_mem_nonunits_iff (a := ⟨ψ (b : T), hbR⟩)).mpr
        ((IsLocalRing.mem_maximalIdeal _).mpr hu))
    refine ⟨a, b, haR, hbR, hbunit, ?_⟩
    have hres_fw : R.residue ⟨f, hf⟩ = R.residue ⟨φ' w, hwO⟩ := by
      rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, R.ker_residue]
      exact (ValuationSubring.coe_mem_nonunits_iff (a := (⟨f, hf⟩ - ⟨φ' w, hwO⟩ : ↥R.integers))).mp hfw
    rw [hres_fw, ← map_mul]
    congr 1
    apply Subtype.ext
    change ψ (e w) * ψ (b : T) = ψ (a : T)
    rw [← map_mul, hab]

  have htjA : Transcendental ↥A₁ jT := fun h => htj (h.extendScalars (IsFractionRing.injective ↥A₁ ↥K₁))
  obtain ⟨hchart, ⟨𝔓, -, -, h𝔓mem, -, hloc⟩, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
      ↥A₁ ↥K₁ T jT htjA hFD hsep OT hVA hVm hVj
  haveI : Fact (jT⁻¹ ≠ 0) := ⟨inv_ne_zero (Fact.out : jT ≠ 0)⟩
  have htjA' : Transcendental ↥A₁ jT⁻¹ := fun h => htjA (IsAlgebraic.inv_iff.mp h)
  have hadj : IntermediateField.adjoin ↥K₁ ({jT⁻¹} : Set T) = IntermediateField.adjoin ↥K₁ ({jT} : Set T) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact inv_mem (IntermediateField.mem_adjoin_simple_self _ _)
    · rw [IntermediateField.adjoin_simple_le_iff]
      have := inv_mem (IntermediateField.mem_adjoin_simple_self ↥K₁ jT⁻¹)
      rwa [inv_inv] at this
  have hFD' : FiniteDimensional ↥(IntermediateField.adjoin ↥K₁ ({jT⁻¹} : Set T)) T := by rw [hadj]; exact hFD
  have hsep' : Algebra.IsSeparable ↥(IntermediateField.adjoin ↥K₁ ({jT⁻¹} : Set T)) T := by rw [hadj]; exact hsep
  obtain ⟨hchart', ⟨𝔓', -, -, h𝔓mem', -, hloc'⟩, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
      ↥A₁ ↥K₁ T jT⁻¹ htjA' hFD' hsep' OT hVA hVm hVj'
  exact ⟨finish _ 𝔓 hchart h𝔓mem hloc, finish _ 𝔓' hchart' h𝔓mem' hloc'⟩

end S_ModularCurve_exists_chartAlg_residue_mul_eq_residue_of_coe_eq_coeffMap_of_residue_surjective
end P2MW
export P2MW.S_ModularCurve_exists_chartAlg_residue_mul_eq_residue_of_coe_eq_coeffMap_of_residue_surjective (solution)
