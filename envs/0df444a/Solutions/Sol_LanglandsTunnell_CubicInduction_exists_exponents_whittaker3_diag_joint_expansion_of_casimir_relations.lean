-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_exponents_whittaker3_diag_joint_expansion_of_casimir_relations
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/41283380-8bc4-58ce-a61d-a8f810b07fb0

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmoothSpace3
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le
import Theorems.Thm_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_whittaker3_diag_mul_transport_of_isCompact
import Theorems.Thm_RegularSingular_exists_twoLevel_expansion_of_commuting_systems
import Theorems.Thm_RegularSingular_exists_twoLevel_coeff_of_transport_of_slice_expansion
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_exponents_whittaker3_diag_joint_expansion_of_casimir_relations
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions WhittakerBlock.sigmaCompactSpace_adelicGL3 M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply"
p2m_attr_erase "simp" "IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul"

set_option autoImplicit false
set_option maxHeartbeats 6400000

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell LanglandsTunnell.CubicInduction

private theorem family_of_polys (q q' : Polynomial ℂ) (hq : q ≠ 0) (hq' : q' ≠ 0) (ρ : ℝ) :
    ∃ (n : ℕ) (e : Fin n → ℂ) (δ : ℝ), 0 < δ ∧ Function.Injective e ∧ (∀ i, (e i).re ≤ ρ) ∧
      (∀ μ : ℂ, ((∃ e₀ : ℂ, q.IsRoot e₀ ∧ ∃ m : ℕ, μ = e₀ + m) ∨ (∃ e₀ : ℂ, q'.IsRoot e₀ ∧ ∃ m : ℕ, μ = e₀ + m)) →
        μ.re ≤ ρ → ∃ i, e i = μ) ∧
      (∀ e₀ : ℂ, q.IsRoot e₀ → ∀ m : ℕ, ρ < (e₀ + m).re → ρ + 2 * δ ≤ (e₀ + m).re) ∧
      (∀ e₀ : ℂ, q'.IsRoot e₀ → ∀ m : ℕ, ρ < (e₀ + m).re → ρ + 2 * δ ≤ (e₀ + m).re) ∧
      (∀ i, ∃ e₀ : ℂ, (q.IsRoot e₀ ∨ q'.IsRoot e₀) ∧ ∃ m : ℕ, e i = e₀ + m) := by
  classical

  set R : Finset ℂ := q.roots.toFinset ∪ q'.roots.toFinset with hR
  have hmemR : ∀ e₀ : ℂ, (q.IsRoot e₀ ∨ q'.IsRoot e₀) → e₀ ∈ R := by
    intro e₀ h
    rcases h with h | h
    · exact Finset.mem_union_left _ ((Multiset.mem_toFinset).2 ((Polynomial.mem_roots hq).2 h))
    · exact Finset.mem_union_right _ ((Multiset.mem_toFinset).2 ((Polynomial.mem_roots hq').2 h))

  set B : ℕ := ⌈ρ⌉₊ + R.sup (fun e₀ => ⌈|e₀.re|⌉₊) with hB
  have hre_add : ∀ (e₀ : ℂ) (m : ℕ), (e₀ + (m : ℂ)).re = e₀.re + m := by
    intro e₀ m; simp
  have hceil : ∀ e₀ ∈ R, ρ - e₀.re ≤ (⌈ρ⌉₊ : ℝ) + (⌈|e₀.re|⌉₊ : ℝ) := by
    intro e₀ _
    have h1 := Nat.le_ceil ρ
    have h2 := Nat.le_ceil |e₀.re|
    have h3 := neg_le_abs e₀.re
    linarith
  have hsup : ∀ e₀ ∈ R, ((⌈|e₀.re|⌉₊ : ℕ) : ℝ) ≤ ((R.sup (fun e₀ => ⌈|e₀.re|⌉₊) : ℕ) : ℝ) := by
    intro e₀ he
    exact_mod_cast Finset.le_sup (f := fun e₀ => ⌈|e₀.re|⌉₊) he
  have hBcast : (B : ℝ) = (⌈ρ⌉₊ : ℝ) + ((R.sup (fun e₀ => ⌈|e₀.re|⌉₊) : ℕ) : ℝ) := by
    rw [hB]; push_cast; ring
  have hBle : ∀ e₀ ∈ R, ∀ m : ℕ, (e₀ + (m : ℂ)).re ≤ ρ → m ≤ B := by
    intro e₀ he m hm
    rw [hre_add] at hm
    have h1 := hceil e₀ he
    have h2 := hsup e₀ he
    have : (m : ℝ) ≤ (B : ℝ) := by rw [hBcast]; linarith
    exact_mod_cast this

  set T : Finset ℂ :=
    ((R ×ˢ Finset.range (B + 1)).image (fun p : ℂ × ℕ => p.1 + (p.2 : ℂ))).filter (fun μ => μ.re ≤ ρ) with hT

  set G : Finset ℝ :=
    insert (1 : ℝ)
      (((R ×ˢ Finset.range (B + 2)).image (fun p : ℂ × ℕ => (p.1 + (p.2 : ℂ)).re - ρ)).filter (fun t => 0 < t))
    with hG
  have hGne : G.Nonempty := ⟨1, by rw [hG]; exact Finset.mem_insert_self _ _⟩
  have hGpos : ∀ t ∈ G, 0 < t := by
    intro t ht
    rw [hG, Finset.mem_insert] at ht
    rcases ht with rfl | ht
    · norm_num
    · exact (Finset.mem_filter.1 ht).2
  set δ : ℝ := G.min' hGne / 2 with hδ
  have hδpos : 0 < δ := by
    have := hGpos _ (Finset.min'_mem G hGne)
    rw [hδ]; linarith
  have hmin_le_one : G.min' hGne ≤ 1 := Finset.min'_le _ _ (by rw [hG]; exact Finset.mem_insert_self _ _)

  have hgap : ∀ e₀ ∈ R, ∀ m : ℕ, ρ < (e₀ + (m : ℂ)).re → ρ + 2 * δ ≤ (e₀ + (m : ℂ)).re := by
    intro e₀ he m hm
    by_cases hmB : m ≤ B + 1
    · have hmem : (e₀ + (m : ℂ)).re - ρ ∈ G := by
        rw [hG]
        apply Finset.mem_insert_of_mem
        rw [Finset.mem_filter]
        refine ⟨?_, by linarith⟩
        rw [Finset.mem_image]
        exact ⟨(e₀, m), Finset.mem_product.2 ⟨he, Finset.mem_range.2 (by omega)⟩, rfl⟩
      have h1 : G.min' hGne ≤ (e₀ + (m : ℂ)).re - ρ := Finset.min'_le _ _ hmem
      rw [hδ]; linarith
    · have h2' : B + 2 ≤ m := by omega
      have h2 : (B : ℝ) + 2 ≤ (m : ℝ) := by exact_mod_cast h2'
      have h3 := hceil e₀ he
      have h4 := hsup e₀ he
      rw [hδ, hre_add]
      rw [hBcast] at h2
      linarith

  have hRmem : ∀ e₀ ∈ R, q.IsRoot e₀ ∨ q'.IsRoot e₀ := by
    intro e₀ he
    rw [hR, Finset.mem_union, Multiset.mem_toFinset, Multiset.mem_toFinset, Polynomial.mem_roots hq,
      Polynomial.mem_roots hq'] at he
    exact he
  refine ⟨Fintype.card T, fun i => ((Fintype.equivFin T).symm i : ℂ), δ, hδpos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact (Fintype.equivFin T).symm.injective (Subtype.ext hij)
  · intro i
    exact (Finset.mem_filter.1 ((Fintype.equivFin T).symm i).2).2
  · intro μ hμ hre
    have hμT : μ ∈ T := by
      refine Finset.mem_filter.2 ⟨?_, hre⟩
      rw [Finset.mem_image]
      rcases hμ with ⟨e₀, he₀, m, rfl⟩ | ⟨e₀, he₀, m, rfl⟩
      · have heR := hmemR e₀ (Or.inl he₀)
        exact ⟨(e₀, m), Finset.mem_product.2 ⟨heR, Finset.mem_range.2 (Nat.lt_succ_of_le (hBle e₀ heR m hre))⟩,
          rfl⟩
      · have heR := hmemR e₀ (Or.inr he₀)
        exact ⟨(e₀, m), Finset.mem_product.2 ⟨heR, Finset.mem_range.2 (Nat.lt_succ_of_le (hBle e₀ heR m hre))⟩,
          rfl⟩
    exact ⟨Fintype.equivFin T ⟨μ, hμT⟩, by simp⟩
  · intro e₀ he₀ m hm
    exact hgap e₀ (hmemR e₀ (Or.inl he₀)) m hm
  · intro e₀ he₀ m hm
    exact hgap e₀ (hmemR e₀ (Or.inr he₀)) m hm
  · intro i
    have hi := (Finset.mem_filter.1 ((Fintype.equivFin T).symm i).2).1
    rw [Finset.mem_image] at hi
    obtain ⟨⟨e₀, m⟩, hp, hμ⟩ := hi
    exact ⟨e₀, hRmem e₀ (Finset.mem_product.1 hp).1, m, hμ.symm⟩

section ContinuityLemmas

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal Pointwise

private theorem continuous_upperUnipotent3_of_entries :
    Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
      (upperUnipotent3 p.1 p.2.1 p.2.2 : AdelicGL 3 (𝓞 ℚ) ℚ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    simp only [Function.comp_def, upperUnipotent3_coe]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    show Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
      (!![1, -p.1, p.1 * p.2.1 - p.2.2; 0, 1, -p.2.1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem ae_mem_adelicBox_of_productionPins :
    ∀ᵐ z ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν,
      z ∈ AdelicBox.adelicBox ℚ := by
  rw [productionPinsOf_ν]
  exact ProbabilityTheory.ae_cond_mem (AdelicBox.measurableSet_adelicBox ℚ)

private theorem isProbabilityMeasure_ν_of_productionPins_adelicBox :
    @IsProbabilityMeasure _ (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).nS
      (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν :=
  isProbabilityMeasure_productionPinsOf_ν ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)
    (AdelicBox.adelicAddHaar_adelicBox_pos ℚ).ne' (AdelicBox.adelicAddHaar_adelicBox_lt_top ℚ).ne

private theorem integrable_adelicBox_of_continuousOn {G : AdeleRing (𝓞 ℚ) ℚ → ℂ}
    (hG : ContinuousOn G (AdelicBox.adelicBox ℚ)) {M : ℝ} (hM : ∀ z ∈ AdelicBox.adelicBox ℚ, ‖G z‖ ≤ M) :
    Integrable G (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν := by
  haveI := isProbabilityMeasure_ν_of_productionPins_adelicBox
  refine Integrable.mono' (integrable_const M) ?_ (ae_mem_adelicBox_of_productionPins.mono fun z hz => hM z hz)
  rw [productionPinsOf_ν]
  letI := AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  haveI := AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  exact (hG.aestronglyMeasurable (μ := AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
    (AdelicBox.measurableSet_adelicBox ℚ)).smul_measure
      (AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ))⁻¹

private theorem integrable_of_continuous_productionPins {G : AdeleRing (𝓞 ℚ) ℚ → ℂ} (hG : Continuous G) :
    Integrable G (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν := by
  obtain ⟨L, hL, hsub⟩ := AdelicBox.exists_isCompact_adelicBox_subset ℚ
  obtain ⟨M, hM⟩ := hL.exists_bound_of_continuousOn hG.continuousOn
  exact integrable_adelicBox_of_continuousOn hG.continuousOn fun z hz => hM z (hsub hz)

private theorem continuous_integral_of_continuous_productionPins {P : Type} [TopologicalSpace P]
    {F : P → AdeleRing (𝓞 ℚ) ℚ → ℂ} (hF : Continuous fun q : P × AdeleRing (𝓞 ℚ) ℚ => F q.1 q.2) :
    Continuous fun p => ∫ z, F p z ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν := by
  haveI := isProbabilityMeasure_ν_of_productionPins_adelicBox
  obtain ⟨L, hL, hsub⟩ := AdelicBox.exists_isCompact_adelicBox_subset ℚ
  have hint : ∀ p, Integrable (F p) (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν := by
    intro p
    have hp : Continuous fun z => F p z := hF.comp (f := fun z => (p, z)) (by fun_prop)
    exact integrable_of_continuous_productionPins hp
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  have hU : TendstoUniformlyOn (fun p z => F p z) (F p₀) (nhds p₀) L :=
    ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1
      ((ContinuousMap.curry ⟨fun q : P × AdeleRing (𝓞 ℚ) ℚ => F q.1 q.2, hF⟩).continuous.tendsto p₀) L hL
  unfold ContinuousAt
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hU (ε / 2) (half_pos hε)] with p hp
  rw [dist_eq_norm, ← integral_sub (hint p) (hint p₀)]
  refine lt_of_le_of_lt (norm_integral_le_of_norm_le_const (C := ε / 2) ?_) ?_
  · filter_upwards [ae_mem_adelicBox_of_productionPins] with z hz
    rw [← dist_eq_norm, dist_comm]
    exact (hp z (hsub hz)).le
  · rw [probReal_univ, mul_one]
    exact half_lt_self hε

private noncomputable def archOfRealHom : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun v : NumberField.InfinitePlace ℚ =>
    ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
      (NumberField.IsTotallyReal.isReal v)).symm : ℝ →+* v.Completion)

private theorem archRealMat3_eq_mapMatrix (e : Fin 3 → Fin 3 → ℝ) :
    WhittakerBlock.archRealMat3 e =
      AutomorphicForm.archMatrixInclN (Fin 3) ℚ (archOfRealHom.mapMatrix (Matrix.of e)) := by
  unfold WhittakerBlock.archRealMat3
  congr 1

private theorem archRealMat3_of_mul (e d : Fin 3 → Fin 3 → ℝ) :
    WhittakerBlock.archRealMat3 (Matrix.of e * Matrix.of d : Matrix (Fin 3) (Fin 3) ℝ) =
      WhittakerBlock.archRealMat3 e * WhittakerBlock.archRealMat3 d := by
  rw [archRealMat3_eq_mapMatrix, archRealMat3_eq_mapMatrix, archRealMat3_eq_mapMatrix,
    ← AutomorphicForm.archMatrixInclN_mul, ← map_mul archOfRealHom.mapMatrix]
  rfl

private theorem isUnit_archRealMat3_of_det_ne_zero {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    IsUnit (WhittakerBlock.archRealMat3 e) := by
  rw [archRealMat3_eq_mapMatrix]
  have h1 : IsUnit (Matrix.of e) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 he)
  exact (h1.map archOfRealHom.mapMatrix).map (AutomorphicForm.archMatrixInclHomN (Fin 3) ℚ)

private theorem coe_archRealLift3_of_det_ne_zero {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    ((WhittakerBlock.archRealLift3 e : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      WhittakerBlock.archRealMat3 e := by
  unfold WhittakerBlock.archRealLift3
  rw [dif_pos (isUnit_archRealMat3_of_det_ne_zero he)]
  exact IsUnit.unit_spec _

private theorem archRealLift3_of_mul {e d : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0)
    (hd : (Matrix.of d).det ≠ 0) :
    WhittakerBlock.archRealLift3 (Matrix.of e * Matrix.of d : Matrix (Fin 3) (Fin 3) ℝ) =
      WhittakerBlock.archRealLift3 e * WhittakerBlock.archRealLift3 d := by
  have hed : (Matrix.of (Matrix.of e * Matrix.of d : Matrix (Fin 3) (Fin 3) ℝ)).det ≠ 0 := by
    show (Matrix.of e * Matrix.of d).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero he hd
  apply Units.ext
  rw [Units.val_mul, coe_archRealLift3_of_det_ne_zero he, coe_archRealLift3_of_det_ne_zero hd,
    coe_archRealLift3_of_det_ne_zero hed, archRealMat3_of_mul]

private theorem archRealLift3_one_array : WhittakerBlock.archRealLift3 (1 : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  apply Units.ext
  rw [coe_archRealLift3_of_det_ne_zero (by show (1 : Matrix (Fin 3) (Fin 3) ℝ).det ≠ 0; simp),
    archRealMat3_eq_mapMatrix, Units.val_one]
  have h1 : archOfRealHom.mapMatrix (Matrix.of (1 : Matrix (Fin 3) (Fin 3) ℝ)) = 1 := by
    rw [show Matrix.of (1 : Matrix (Fin 3) (Fin 3) ℝ) = (1 : Matrix (Fin 3) (Fin 3) ℝ) from rfl, map_one]
  rw [h1, AutomorphicForm.archMatrixInclN_one]

private theorem isOpen_detSet : IsOpen {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  have h : Continuous fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e).det :=
    (continuous_id (X := Matrix (Fin 3) (Fin 3) ℝ)).matrix_det
  exact isOpen_compl_singleton.preimage h

private theorem exists_closedBall_subset_detSet {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall e r ⊆ {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 isOpen_detSet e he
  exact ⟨r / 2, half_pos hr, (Metric.closedBall_subset_ball (half_lt_self hr)).trans hsub⟩

private theorem contDiff_det_of : ContDiff ℝ (⊤ : ℕ∞) fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e).det := by
  simp only [Matrix.det_fin_three, Matrix.of_apply]
  fun_prop

private theorem contDiff_adjugate_of (k l : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e).adjugate k l := by
  fin_cases k <;> fin_cases l <;>
    simp only [Matrix.adjugate_fin_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    fun_prop

private theorem contDiffOn_inv_entry (k l : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e)⁻¹ k l)
      {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  have h : ∀ e : Fin 3 → Fin 3 → ℝ, (Matrix.of e)⁻¹ k l = ((Matrix.of e).det)⁻¹ * (Matrix.of e).adjugate k l := by
    intro e
    rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, smul_eq_mul]
  simp only [h]
  exact (contDiff_det_of.contDiffOn.inv fun e he => he).mul (contDiff_adjugate_of k l).contDiffOn

private theorem continuous_archRealMat3 : Continuous WhittakerBlock.archRealMat3 := by
  refine continuous_matrix fun i j => ?_
  unfold WhittakerBlock.archRealMat3
  simp only [AutomorphicForm.archMatrixInclN, Matrix.of_apply]
  exact (AutomorphicForm.StandardKernel.continuous_ofReal.comp
    ((continuous_apply j).comp (continuous_apply i))).prodMk continuous_const

private theorem det_of_inv_ne_zero {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    (Matrix.of ((Matrix.of e)⁻¹ : Matrix (Fin 3) (Fin 3) ℝ)).det ≠ 0 := by
  show ((Matrix.of e)⁻¹).det ≠ 0
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  exact inv_ne_zero he

private theorem archRealLift3_inv_of_det_ne_zero {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    (WhittakerBlock.archRealLift3 e)⁻¹ =
      WhittakerBlock.archRealLift3 ((Matrix.of e)⁻¹ : Matrix (Fin 3) (Fin 3) ℝ) := by
  have h1 : (Matrix.of e * Matrix.of ((Matrix.of e)⁻¹ : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
    show Matrix.of e * (Matrix.of e)⁻¹ = 1
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 he)
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← archRealLift3_of_mul he (det_of_inv_ne_zero he), h1, archRealLift3_one_array]

private theorem continuousOn_archRealLift3_detSet :
    ContinuousOn WhittakerBlock.archRealLift3 {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  rw [continuousOn_iff_continuous_restrict]
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h : ∀ e : {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0},
        ((WhittakerBlock.archRealLift3 e.1 : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
          WhittakerBlock.archRealMat3 e.1 :=
      fun e => coe_archRealLift3_of_det_ne_zero e.2
    simp only [Set.domRestrict_apply, Function.comp_def, h]
    exact continuous_archRealMat3.comp continuous_subtype_val
  · have h : ∀ e : {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0},
        (((WhittakerBlock.archRealLift3 e.1)⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
          WhittakerBlock.archRealMat3 ((Matrix.of e.1)⁻¹ : Matrix (Fin 3) (Fin 3) ℝ) := by
      intro e
      rw [archRealLift3_inv_of_det_ne_zero e.2]
      exact coe_archRealLift3_of_det_ne_zero (det_of_inv_ne_zero e.2)
    simp only [Set.domRestrict_apply, h]
    refine continuous_archRealMat3.comp ?_
    refine continuous_pi fun k => continuous_pi fun l => ?_
    exact (contDiffOn_inv_entry k l).continuousOn.comp_continuous continuous_subtype_val fun e => e.2

private theorem continuous_whittaker3_of_continuous {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : Continuous u) :
    Continuous (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ u) := by
  have hn : Continuous fun q : ((AdelicGL 3 (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ =>
      upperUnipotent3 q.1.1.2 q.1.2 q.2 :=
    continuous_upperUnipotent3_of_entries.comp
      (by fun_prop : Continuous fun q : ((AdelicGL 3 (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ) ×
          AdeleRing (𝓞 ℚ) ℚ => (q.1.1.2, q.1.2, q.2))
  have hm : Continuous fun q : ((AdelicGL 3 (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ =>
      upperUnipotent3 q.1.1.2 q.1.2 q.2 * q.1.1.1 :=
    hn.mul (by fun_prop)
  have hu' : Continuous fun q : ((AdelicGL 3 (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ =>
      u (upperUnipotent3 q.1.1.2 q.1.2 q.2 * q.1.1.1) :=
    hu.comp hm
  have hp : Continuous fun q : ((AdelicGL 3 (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ =>
      NumberField.StandardAddChar.psiQ (-(q.1.1.2 + q.1.2)) :=
    NumberField.StandardAddChar.continuous_psiQ.comp
      (by fun_prop : Continuous fun q : ((AdelicGL 3 (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ) ×
          AdeleRing (𝓞 ℚ) ℚ => -(q.1.1.2 + q.1.2))
  have hF : Continuous fun q : ((AdelicGL 3 (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ =>
      u (upperUnipotent3 q.1.1.2 q.1.2 q.2 * q.1.1.1) * NumberField.StandardAddChar.psiQ (-(q.1.1.2 + q.1.2)) :=
    hu'.mul hp
  have hA := continuous_integral_of_continuous_productionPins
    (P := (AdelicGL 3 (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ)
    (F := fun q z => u (upperUnipotent3 q.1.2 q.2 z * q.1.1) * NumberField.StandardAddChar.psiQ (-(q.1.2 + q.2))) hF
  have hB := continuous_integral_of_continuous_productionPins (P := AdelicGL 3 (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ)
    (F := fun q y => ∫ z, u (upperUnipotent3 q.2 y z * q.1) * NumberField.StandardAddChar.psiQ (-(q.2 + y))
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν) hA
  exact continuous_integral_of_continuous_productionPins (P := AdelicGL 3 (𝓞 ℚ) ℚ)
    (F := fun g x => ∫ y, ∫ z, u (upperUnipotent3 x y z * g) * NumberField.StandardAddChar.psiQ (-(x + y))
        ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν ∂(productionPinsOf ℚ ∅
            (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν) hB

end

end ContinuityLemmas

private theorem continuousOn_whittaker3_diag_mul {f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hf : Continuous f)
    (k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ContinuousOn (fun w : ℝ × ℝ × AdelicGL 3 (𝓞 ℚ) ℚ =>
        whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ f
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![w.1 * w.2.1, w.2.1, 1] i else 0) * w.2.2 * k))
      (Set.Ioi 0 ×ˢ Set.Ioi 0 ×ˢ Set.univ) := by
  have harr : Continuous fun w : ℝ × ℝ × AdelicGL 3 (𝓞 ℚ) ℚ =>
      (fun i j : Fin 3 => if i = j then ![w.1 * w.2.1, w.2.1, 1] i else 0) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    by_cases h : i = j
    · subst h
      fin_cases i <;> simp <;> fun_prop
    · simp [h]
      exact continuous_const
  have hdet : ∀ w : ℝ × ℝ × AdelicGL 3 (𝓞 ℚ) ℚ, w ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) ×ˢ Set.univ →
      (Matrix.of (fun i j : Fin 3 => if i = j then ![w.1 * w.2.1, w.2.1, 1] i else 0)).det ≠ 0 := by
    intro w hw
    have h1 : (0 : ℝ) < w.1 := (Set.mem_prod.1 hw).1
    have h2 : (0 : ℝ) < w.2.1 := (Set.mem_prod.1 (Set.mem_prod.1 hw).2).1
    have hdiag : Matrix.of (fun i j : Fin 3 => if i = j then ![w.1 * w.2.1, w.2.1, 1] i else 0) =
        Matrix.diagonal ![w.1 * w.2.1, w.2.1, 1] := by
      ext i j
      simp [Matrix.diagonal_apply]
    rw [hdiag, Matrix.det_diagonal]
    simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    have h12 : w.1 * w.2.1 * w.2.1 * 1 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero h1.ne' h2.ne') h2.ne') one_ne_zero
    simpa using h12
  have hlift : ContinuousOn (fun w : ℝ × ℝ × AdelicGL 3 (𝓞 ℚ) ℚ =>
      WhittakerBlock.archRealLift3 (fun i j => if i = j then ![w.1 * w.2.1, w.2.1, 1] i else 0))
      (Set.Ioi 0 ×ˢ Set.Ioi 0 ×ˢ Set.univ) :=
    continuousOn_archRealLift3_detSet.comp harr.continuousOn fun w hw => hdet w hw
  have hmul : ContinuousOn (fun w : ℝ × ℝ × AdelicGL 3 (𝓞 ℚ) ℚ =>
      WhittakerBlock.archRealLift3 (fun i j => if i = j then ![w.1 * w.2.1, w.2.1, 1] i else 0) * w.2.2 * k)
      (Set.Ioi 0 ×ˢ Set.Ioi 0 ×ˢ Set.univ) :=
    (hlift.mul (continuous_snd.comp continuous_snd).continuousOn).mul continuousOn_const
  exact (continuous_whittaker3_of_continuous hf).comp_continuousOn hmul

section Slice

open Finset

private theorem bound_on_strip (C : ℝ) (N : ℕ) (Z : ℝ) (hZ : 1 ≤ Z) (y z : ℝ) (hy : y ∈ Set.Ioc (0 : ℝ) 1)
    (hz : z ∈ Set.Ioc (0 : ℝ) Z) :
    C * (max y 1 * max z 1 * max y⁻¹ 1 * max z⁻¹ 1) ^ N ≤
      |C| * Z ^ (2 * N) * y ^ (-(N : ℝ)) * z ^ (-(N : ℝ)) := by
  have hy0 : 0 < y := hy.1
  have hz0 : 0 < z := hz.1
  have hZ0 : 0 < Z := lt_of_lt_of_le one_pos hZ
  have h1 : max y 1 = 1 := max_eq_right hy.2
  have h2 : max z 1 ≤ Z := max_le hz.2 hZ
  have h3 : max y⁻¹ 1 = y⁻¹ := max_eq_left (one_le_inv₀ hy0 |>.2 hy.2)
  have h4 : max z⁻¹ 1 ≤ Z * z⁻¹ := by
    refine max_le ?_ ?_
    · calc z⁻¹ = 1 * z⁻¹ := (one_mul _).symm
        _ ≤ Z * z⁻¹ := mul_le_mul_of_nonneg_right hZ (inv_pos.2 hz0).le
    · rw [← div_eq_mul_inv, le_div_iff₀ hz0, one_mul]
      exact hz.2
  have hprod : max y 1 * max z 1 * max y⁻¹ 1 * max z⁻¹ 1 ≤ Z * Z * (y⁻¹ * z⁻¹) := by
    rw [h1, h3]
    calc 1 * max z 1 * y⁻¹ * max z⁻¹ 1 ≤ 1 * Z * y⁻¹ * (Z * z⁻¹) := by gcongr
      _ = Z * Z * (y⁻¹ * z⁻¹) := by ring
  have hpow : (max y 1 * max z 1 * max y⁻¹ 1 * max z⁻¹ 1) ^ N ≤ (Z * Z * (y⁻¹ * z⁻¹)) ^ N :=
    pow_le_pow_left₀ (by positivity) hprod N
  have hry : y ^ (-(N : ℝ)) = (y⁻¹) ^ N := by rw [Real.rpow_neg hy0.le, Real.rpow_natCast, inv_pow]
  have hrz : z ^ (-(N : ℝ)) = (z⁻¹) ^ N := by rw [Real.rpow_neg hz0.le, Real.rpow_natCast, inv_pow]
  calc C * (max y 1 * max z 1 * max y⁻¹ 1 * max z⁻¹ 1) ^ N
      ≤ |C| * (max y 1 * max z 1 * max y⁻¹ 1 * max z⁻¹ 1) ^ N :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (Z * Z * (y⁻¹ * z⁻¹)) ^ N := by gcongr
    _ = |C| * Z ^ (2 * N) * y ^ (-(N : ℝ)) * z ^ (-(N : ℝ)) := by
        rw [hry, hrz, mul_pow, mul_pow, pow_mul, sq, mul_pow]; ring

private theorem slice_package
    {n J R d d₂ d' d₂' : ℕ} (e : Fin n → ℂ) (he : Function.Injective e) (ρ δ : ℝ) (hδ : 0 < δ)
    (hre : ∀ i, (e i).re ≤ ρ)
    (hcl : ∀ i (k : ℕ), (e i + k).re ≤ ρ → ∃ i', e i' = e i + k)
    (hgap : ∀ i (k : ℕ), ρ < (e i + k).re → ρ + 2 * δ ≤ (e i + k).re)
    (q q' : Polynomial ℂ) (hq : q ≠ 0) (hq' : q' ≠ 0)
    (hcov : ∀ e₀ : ℂ, q.IsRoot e₀ → ∀ k : ℕ, (e₀ + k).re ≤ ρ → ∃ i, e i = e₀ + k)
    (hcov' : ∀ e₀ : ℂ, q'.IsRoot e₀ → ∀ k : ℕ, (e₀ + k).re ≤ ρ → ∃ i, e i = e₀ + k)
    (hgq : ∀ e₀ : ℂ, q.IsRoot e₀ → ∀ k : ℕ, ρ < (e₀ + k).re → ρ + 2 * δ ≤ (e₀ + k).re)
    (hgq' : ∀ e₀ : ℂ, q'.IsRoot e₀ → ∀ k : ℕ, ρ < (e₀ + k).re → ρ + 2 * δ ≤ (e₀ + k).re)
    (hJ : q.natDegree ≤ J) (hJ' : n * q'.natDegree ≤ J)
    (Mc : AdelicGL 3 (𝓞 ℚ) ℚ → Fin (d₂ + 1) → Matrix (Fin R) (Fin R) ℂ)
    (A : AdelicGL 3 (𝓞 ℚ) ℚ → Fin d → Fin (d₂ + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ)))
    (Mc' : AdelicGL 3 (𝓞 ℚ) ℚ → Fin (d₂' + 1) → Matrix (Fin R) (Fin R) ℂ)
    (A' : AdelicGL 3 (𝓞 ℚ) ℚ → Fin d' → Fin (d₂' + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ)))
    (hMc : ∀ b, Continuous fun g => Mc g b) (hA : ∀ k b, Continuous fun g => A g k b)
    (hMc' : ∀ a, Continuous fun g => Mc' g a) (hA' : ∀ k a, Continuous fun g => A' g k a)
    (K₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hK₀ : IsCompact K₀)
    (hq0 : ∀ g ∈ K₀, ∀ z : ℝ, 0 < z → Polynomial.aeval (∑ b : Fin (d₂ + 1), ((z : ℂ) ^ (b : ℕ)) • Mc g b) q = 0)
    (hq0' : ∀ g ∈ K₀, ∀ y : ℝ, 0 < y →
      Polynomial.aeval (∑ a : Fin (d₂' + 1), ((y : ℂ) ^ (a : ℕ)) • Mc' g a) q' = 0)
    (V : ℝ → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → (Fin R → ℂ))
    (hVc : ContinuousOn (fun w : ℝ × ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => V w.1 w.2.1 w.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioi 0 ×ˢ Set.univ))
    (Vy Vz : AdelicGL 3 (𝓞 ℚ) ℚ → ℝ → ℝ → (Fin R → ℂ))
    (hsysY : ∀ g ∈ K₀, ∀ z : ℝ, 0 < z → ∀ y : ℝ, 0 < y →
      HasDerivAt (fun y => V y z g) (Vy g y z) y ∧
      (y : ℂ) • Vy g y z =
        (fun i => ∑ j, (∑ b : Fin (d₂ + 1), (z : ℂ) ^ (b : ℕ) * Mc g b i j) • V y z g j) +
          ∑ k : Fin d, ∑ b : Fin (d₂ + 1), ((y : ℂ) ^ ((k : ℕ) + 1) * (z : ℂ) ^ (b : ℕ)) • A g k b (V y z g))
    (hsysZ : ∀ g ∈ K₀, ∀ y : ℝ, 0 < y → ∀ z : ℝ, 0 < z →
      HasDerivAt (fun z => V y z g) (Vz g y z) z ∧
      (z : ℂ) • Vz g y z =
        (fun i => ∑ j, (∑ a : Fin (d₂' + 1), (y : ℂ) ^ (a : ℕ) * Mc' g a i j) • V y z g j) +
          ∑ k : Fin d', ∑ a : Fin (d₂' + 1), ((z : ℂ) ^ ((k : ℕ) + 1) * (y : ℂ) ^ (a : ℕ)) • A' g k a (V y z g))
    (N : ℕ) (CS : ℝ)
    (hVb : ∀ g ∈ K₀, ∀ y z : ℝ, 0 < y → 0 < z →
      ‖V y z g‖ ≤ CS * (max y 1 * max z 1 * max y⁻¹ 1 * max z⁻¹ 1) ^ N)
    (i₀ : Fin R) (Z : ℝ) (hZ : 2 ≤ Z) :
    ∃ (m C : ℝ) (cS : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
      (c₂ : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      (∀ k ∈ K₀, ∀ i j i' j', ‖c₂ i j i' j' k‖ ≤ C) ∧
      (∀ k ∈ K₀, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ∀ i j, ‖cS i j z k‖ ≤ C * z ^ (-m)) ∧
      (∀ k ∈ K₀, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
        ‖V y z k i₀ - ∑ i : Fin n, ∑ j : Fin J,
            cS i j z k * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤ C * z ^ (-m) * y ^ (ρ + δ)) ∧
      (∀ k ∈ K₀, ∀ i j, ∀ z ∈ Set.Ioc (0 : ℝ) 1,
        ‖cS i j z k - ∑ i' : Fin n, ∑ j' : Fin J,
            c₂ i j i' j' k * ((z : ℂ) ^ e i' * ((Real.log z : ℝ) : ℂ) ^ (j' : ℕ))‖ ≤ C * z ^ (ρ + δ)) := by
  classical
  have hZ1 : 1 ≤ Z := by linarith
  haveI hK₀cs : CompactSpace K₀ := isCompact_iff_compactSpace.1 hK₀

  have hf_cont : Continuous fun p : K₀ =>
      (∑ b : Fin (d₂ + 1), ∑ ij : Fin R × Fin R, ‖Mc p.1 b ij.1 ij.2‖) +
      (∑ k : Fin d, ∑ b : Fin (d₂ + 1), ‖A p.1 k b‖) +
      (∑ a : Fin (d₂' + 1), ∑ ij : Fin R × Fin R, ‖Mc' p.1 a ij.1 ij.2‖) +
      (∑ k : Fin d', ∑ a : Fin (d₂' + 1), ‖A' p.1 k a‖) := by
    refine ((Continuous.add ?_ ?_).add ?_).add ?_
    · exact continuous_finsetSum _ fun b _ => continuous_finsetSum _ fun ij _ =>
        (((hMc b).comp continuous_subtype_val).matrix_elem ij.1 ij.2).norm
    · exact continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun b _ =>
        ((hA k b).comp continuous_subtype_val).norm
    · exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun ij _ =>
        (((hMc' a).comp continuous_subtype_val).matrix_elem ij.1 ij.2).norm
    · exact continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun a _ =>
        ((hA' k a).comp continuous_subtype_val).norm
  obtain ⟨L, hL⟩ := isCompact_univ.exists_bound_of_continuousOn hf_cont.continuousOn
  have hL' : ∀ p : K₀,
      (∑ b : Fin (d₂ + 1), ∑ ij : Fin R × Fin R, ‖Mc p.1 b ij.1 ij.2‖) +
      (∑ k : Fin d, ∑ b : Fin (d₂ + 1), ‖A p.1 k b‖) +
      (∑ a : Fin (d₂' + 1), ∑ ij : Fin R × Fin R, ‖Mc' p.1 a ij.1 ij.2‖) +
      (∑ k : Fin d', ∑ a : Fin (d₂' + 1), ‖A' p.1 k a‖) ≤ L := by
    intro p
    have h := hL p (Set.mem_univ p)
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  have hS1 : ∀ p : K₀, 0 ≤ ∑ b : Fin (d₂ + 1), ∑ ij : Fin R × Fin R, ‖Mc p.1 b ij.1 ij.2‖ :=
    fun p => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hS2 : ∀ p : K₀, 0 ≤ ∑ k : Fin d, ∑ b : Fin (d₂ + 1), ‖A p.1 k b‖ :=
    fun p => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hS3 : ∀ p : K₀, 0 ≤ ∑ a : Fin (d₂' + 1), ∑ ij : Fin R × Fin R, ‖Mc' p.1 a ij.1 ij.2‖ :=
    fun p => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hS4 : ∀ p : K₀, 0 ≤ ∑ k : Fin d', ∑ a : Fin (d₂' + 1), ‖A' p.1 k a‖ :=
    fun p => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hMcL : ∀ (p : K₀) b i j, ‖Mc p.1 b i j‖ ≤ L := by
    intro p b i j
    have h1 : ‖Mc p.1 b i j‖ ≤ ∑ ij : Fin R × Fin R, ‖Mc p.1 b ij.1 ij.2‖ :=
      Finset.single_le_sum (f := fun ij : Fin R × Fin R => ‖Mc p.1 b ij.1 ij.2‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ (i, j))
    have h2 : ∑ ij : Fin R × Fin R, ‖Mc p.1 b ij.1 ij.2‖ ≤
        ∑ b : Fin (d₂ + 1), ∑ ij : Fin R × Fin R, ‖Mc p.1 b ij.1 ij.2‖ :=
      Finset.single_le_sum (f := fun b => ∑ ij : Fin R × Fin R, ‖Mc p.1 b ij.1 ij.2‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ b)
    linarith [hL' p, hS2 p, hS3 p, hS4 p]
  have hAL : ∀ (p : K₀) k b, ‖A p.1 k b‖ ≤ L := by
    intro p k b
    have h1 : ‖A p.1 k b‖ ≤ ∑ b : Fin (d₂ + 1), ‖A p.1 k b‖ :=
      Finset.single_le_sum (f := fun b => ‖A p.1 k b‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ b)
    have h2 : ∑ b : Fin (d₂ + 1), ‖A p.1 k b‖ ≤ ∑ k : Fin d, ∑ b : Fin (d₂ + 1), ‖A p.1 k b‖ :=
      Finset.single_le_sum (f := fun k => ∑ b : Fin (d₂ + 1), ‖A p.1 k b‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k)
    linarith [hL' p, hS1 p, hS3 p, hS4 p]
  have hMcL' : ∀ (p : K₀) a i j, ‖Mc' p.1 a i j‖ ≤ L := by
    intro p a i j
    have h1 : ‖Mc' p.1 a i j‖ ≤ ∑ ij : Fin R × Fin R, ‖Mc' p.1 a ij.1 ij.2‖ :=
      Finset.single_le_sum (f := fun ij : Fin R × Fin R => ‖Mc' p.1 a ij.1 ij.2‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ (i, j))
    have h2 : ∑ ij : Fin R × Fin R, ‖Mc' p.1 a ij.1 ij.2‖ ≤
        ∑ a : Fin (d₂' + 1), ∑ ij : Fin R × Fin R, ‖Mc' p.1 a ij.1 ij.2‖ :=
      Finset.single_le_sum (f := fun a => ∑ ij : Fin R × Fin R, ‖Mc' p.1 a ij.1 ij.2‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a)
    linarith [hL' p, hS1 p, hS2 p, hS4 p]
  have hAL' : ∀ (p : K₀) k a, ‖A' p.1 k a‖ ≤ L := by
    intro p k a
    have h1 : ‖A' p.1 k a‖ ≤ ∑ a : Fin (d₂' + 1), ‖A' p.1 k a‖ :=
      Finset.single_le_sum (f := fun a => ‖A' p.1 k a‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ a)
    have h2 : ∑ a : Fin (d₂' + 1), ‖A' p.1 k a‖ ≤ ∑ k : Fin d', ∑ a : Fin (d₂' + 1), ‖A' p.1 k a‖ :=
      Finset.single_le_sum (f := fun k => ∑ a : Fin (d₂' + 1), ‖A' p.1 k a‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k)
    linarith [hL' p, hS1 p, hS2 p, hS3 p]

  have hφ : Continuous fun w : K₀ × ℝ × ℝ => ((w.2.1, w.2.2, (w.1 : AdelicGL 3 (𝓞 ℚ) ℚ)) :
      ℝ × ℝ × AdelicGL 3 (𝓞 ℚ) ℚ) := by fun_prop
  have hF : ContinuousOn (fun w : K₀ × ℝ × ℝ => V w.2.1 w.2.2 w.1.1) (Set.univ ×ˢ Set.Ioc 0 1 ×ˢ Set.Ioc 0 Z) := by
    refine hVc.comp hφ.continuousOn ?_
    intro w hw
    have h1 : w.2.1 ∈ Set.Ioc (0 : ℝ) 1 := (Set.mem_prod.1 (Set.mem_prod.1 hw).2).1
    have h2 : w.2.2 ∈ Set.Ioc (0 : ℝ) Z := (Set.mem_prod.1 (Set.mem_prod.1 hw).2).2
    exact ⟨h1.1, h2.1, Set.mem_univ _⟩

  have hbound : ∀ (p : K₀), ∀ z ∈ Set.Ioc (0 : ℝ) Z, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      ‖V y z p.1‖ ≤ |CS| * Z ^ (2 * N) * y ^ (-(N : ℝ)) * z ^ (-(N : ℝ)) :=
    fun p z hz y hy => (hVb p.1 p.2 y z hy.1 hz.1).trans (bound_on_strip CS N Z hZ1 y z hy hz)

  obtain ⟨c, c₂, C, -, -, hc₂b, hcb, hexp1, hexp2⟩ :=
    RegularSingular.exists_twoLevel_expansion_of_commuting_systems e he ρ δ hδ hre hcl hgap q q' hq hq' hcov hcov'
      hgq hgq' hJ hJ' K₀ (fun p b => Mc p.1 b) (fun p k b => A p.1 k b) (fun p a => Mc' p.1 a)
      (fun p k a => A' p.1 k a) (fun b => (hMc b).comp continuous_subtype_val)
      (fun k b => (hA k b).comp continuous_subtype_val) (fun a => (hMc' a).comp continuous_subtype_val)
      (fun k a => (hA' k a).comp continuous_subtype_val) L hMcL hAL hMcL' hAL'
      (fun p z hz => hq0 p.1 p.2 z hz) (fun p y hy => hq0' p.1 p.2 y hy) Z hZ
      (fun p y z => V y z p.1) (fun p y z => Vy p.1 y z) (fun p y z => Vz p.1 y z) hF
      (fun p z hz y hy => hsysY p.1 p.2 z hz.1 y hy.1) (fun p y hy z hz => hsysZ p.1 p.2 y hy.1 z hz.1)
      (N : ℝ) (|CS| * Z ^ (2 * N)) hbound

  refine ⟨(N : ℝ), C, fun i j z k => if h : k ∈ K₀ then c i j ⟨k, h⟩ z i₀ else 0,
    fun i j i' j' k => if h : k ∈ K₀ then c₂ i j i' j' ⟨k, h⟩ i₀ else 0, ?_, ?_, ?_, ?_⟩
  · intro k hk i j i' j'
    simp only [dif_pos hk]
    exact (norm_le_pi_norm _ i₀).trans (hc₂b ⟨k, hk⟩ i j i' j')
  · intro k hk z hz i j
    simp only [dif_pos hk]
    exact (norm_le_pi_norm _ i₀).trans (hcb ⟨k, hk⟩ i j z hz)
  · intro k hk z hz y hy
    have h := hexp1 ⟨k, hk⟩ z hz y hy
    have h0 := norm_le_pi_norm (V y z k - ∑ i : Fin n, ∑ j : Fin J,
      ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • c i j ⟨k, hk⟩ z) i₀
    have hsum : (∑ i : Fin n, ∑ j : Fin J,
        ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • c i j ⟨k, hk⟩ z) i₀ =
        ∑ i : Fin n, ∑ j : Fin J, (if h : k ∈ K₀ then c i j ⟨k, h⟩ z i₀ else 0) *
          ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dif_pos hk]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [Pi.sub_apply, hsum] at h0
    exact h0.trans h
  · intro k hk i j z hz
    have h := hexp2 ⟨k, hk⟩ i j z hz
    have h0 := norm_le_pi_norm (c i j ⟨k, hk⟩ z - ∑ i' : Fin n, ∑ j' : Fin J,
      ((z : ℂ) ^ e i' * ((Real.log z : ℝ) : ℂ) ^ (j' : ℕ)) • c₂ i j i' j' ⟨k, hk⟩) i₀
    have hsum : (∑ i' : Fin n, ∑ j' : Fin J,
        ((z : ℂ) ^ e i' * ((Real.log z : ℝ) : ℂ) ^ (j' : ℕ)) • c₂ i j i' j' ⟨k, hk⟩) i₀ =
        ∑ i' : Fin n, ∑ j' : Fin J, c₂ i j i' j' ⟨k, hk⟩ i₀ *
          ((z : ℂ) ^ e i' * ((Real.log z : ℝ) : ℂ) ^ (j' : ℕ)) := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ => ?_
      ring
    rw [Pi.sub_apply, hsum] at h0
    simp only [dif_pos hk]
    exact h0.trans h

end Slice

section Instances

private scoped instance : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdeleRing.secondCountableTopology ℚ

private scoped instance : SecondCountableTopology (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → AdeleRing (𝓞 ℚ) ℚ))

private scoped instance : SecondCountableTopology (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

private scoped instance : SecondCountableTopology (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

end Instances

private theorem exists_bound_words (N : ℕ) (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (h1 : ∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w))
    (h8 : ∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w g‖ ≤ C * gauge3 ℚ g ^ N)
    {r : ℕ} (w : Fin (r + 1) → List (Fin 3 × Fin 3)) (κ : Fin (r + 1) → AdelicGL 3 (𝓞 ℚ) ℚ)
    (K₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hK₀ : IsCompact K₀) :
    ∃ CS : ℝ, ∀ g ∈ K₀, ∀ y z : ℝ, 0 < y → 0 < z →
      ‖(fun i : Fin (r + 1) => whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ
          (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u (w i))
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y * z, z, 1] i else 0) * g * κ i))‖ ≤
        CS * (max y 1 * max z 1 * max y⁻¹ 1 * max z⁻¹ 1) ^ N := by
  classical
  have hS3 : ∀ i : Fin (r + 1), ∃ C : ℝ, ∀ g ∈ K₀, ∀ y z : ℝ, 0 < y → 0 < z →
      ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ
          (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u (w i))
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y * z, z, 1] i else 0) * g * κ i)‖ ≤
        C * (max y 1 * max z 1 * max y⁻¹ 1 * max z⁻¹ 1) ^ N := by
    intro i
    have hcw : ∀ w' : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ)
        (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u (w i)) w') := by
      intro w'
      have h := h1 (w' ++ w i)
      rwa [List.foldr_append] at h
    have hgr : ∀ w' : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        ‖List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ)
          (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u (w i)) w' g‖ ≤ C * gauge3 ℚ g ^ N := by
      intro w'
      obtain ⟨C, hC⟩ := h8 (w' ++ w i)
      refine ⟨C, fun g => ?_⟩
      have h := hC g
      rwa [List.foldr_append] at h
    obtain ⟨C, hC⟩ := LanglandsTunnell.CubicInduction.norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact N _
      hcw hgr ((fun g => g * κ i) '' K₀) (hK₀.image (continuous_id.mul continuous_const))
    refine ⟨C, fun g hg y z hy hz => ?_⟩
    have h := hC (g * κ i) ⟨g, hg, rfl⟩ y z hy hz
    simpa only [mul_assoc] using h
  choose CS hCS using hS3
  refine ⟨∑ i : Fin (r + 1), |CS i|, fun g hg y z hy hz => ?_⟩
  have hP : 0 ≤ (max y 1 * max z 1 * max y⁻¹ 1 * max z⁻¹ 1) ^ N := by positivity
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) hP)]
  intro i
  have h1' : |CS i| ≤ ∑ i : Fin (r + 1), |CS i| :=
    Finset.single_le_sum (f := fun i => |CS i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  calc _ ≤ CS i * (max y 1 * max z 1 * max y⁻¹ 1 * max z⁻¹ 1) ^ N := hCS i g hg y z hy hz
    _ ≤ |CS i| * (max y 1 * max z 1 * max y⁻¹ 1 * max z⁻¹ 1) ^ N :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hP
    _ ≤ (∑ i : Fin (r + 1), |CS i|) * (max y 1 * max z 1 * max y⁻¹ 1 * max z⁻¹ 1) ^ N :=
        mul_le_mul_of_nonneg_right h1' hP

theorem solution
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (N₂ : ℕ) (a₂ : Fin (N₂ + 1) → ℂ) (ha₂ : a₂ (Fin.last N₂) = 1)
    (N₃ : ℕ) (a₃ : Fin (N₃ + 1) → ℂ) (ha₃ : a₃ (Fin.last N₃) = 1) :
    ∀ ρ : ℝ, ∃ (n J : ℕ) (e : Fin n → ℂ) (δ : ℝ), 0 < δ ∧ Function.Injective e ∧ (∀ i, (e i).re ≤ ρ) ∧
      ∀ (N : ℕ) (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      (∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w)) →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = u g) →
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g) →
      WhittakerBlock.IsArchSmooth3 u →
      (∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => u (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) →
      (∑ m, a₂ m • (WhittakerBlock.casimir2^[m] u) = 0) →
      (∑ m, a₃ m • (WhittakerBlock.casimir3^[m] u) = 0) →
      (∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        ‖List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w g‖ ≤ C * gauge3 ℚ g ^ N) →
      (∃ c : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
        (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => c i j p.1 p.2) {p | 0 < p.1}) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin n, ∑ j : Fin J, c i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ (ρ + δ)) ∧
        ∃ c' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
          (∀ i j i' j', Continuous (c' i j i' j')) ∧
          ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
            ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
            ‖c i j y₂ k -
                (∑ i' : Fin n, ∑ j' : Fin J,
                  c' i j i' j' k * ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤
              C * y₂ ^ (ρ + δ)) ∧
      (∃ c : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
        (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => c i j p.1 p.2) {p | 0 < p.1}) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₁ : ℝ, b⁻¹ ≤ y₁ → y₁ ≤ b → ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin n, ∑ j : Fin J, c i j y₁ k * ((y₂ : ℂ) ^ e i * ((Real.log y₂ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₂ ^ (ρ + δ)) ∧
        ∃ c' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
          (∀ i j i' j', Continuous (c' i j i' j')) ∧
          ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
            ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
            ‖c i j y₁ k -
                (∑ i' : Fin n, ∑ j' : Fin J,
                  c' i j i' j' k * ((y₁ : ℂ) ^ e i' * ((Real.log y₁ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤
              C * y₁ ^ (ρ + δ)) := by
  classical
  haveI hLC : LocallyCompactSpace (AdelicGL 3 (𝓞 ℚ) ℚ) :=
    inferInstanceAs (LocallyCompactSpace (GL (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)))
  intro ρ
  obtain ⟨d, d₂, d', d₂', hS1⟩ :=
    LanglandsTunnell.CubicInduction.exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le
      N₂ N₃
  obtain ⟨_ι, _ι', q, q', hq, hq', _hdq, _hdq', _hrq, _hrq', hsysU⟩ := hS1 ω a₂ ha₂ a₃ ha₃
  obtain ⟨n, e, δ, hδ, he_inj, hre, hcov, hgap, hgap', hmem⟩ := family_of_polys q q' hq hq' ρ

  have hcl : ∀ (i : Fin n) (k : ℕ), (e i + k).re ≤ ρ → ∃ i', e i' = e i + k := by
    intro i k hk
    obtain ⟨e₀, he₀, m, hm⟩ := hmem i
    have hshift : e i + k = e₀ + ((m + k : ℕ) : ℂ) := by rw [hm]; push_cast; ring
    refine hcov (e i + k) ?_ hk
    rcases he₀ with h | h
    · exact Or.inl ⟨e₀, h, m + k, hshift⟩
    · exact Or.inr ⟨e₀, h, m + k, hshift⟩
  have hgapF : ∀ (i : Fin n) (k : ℕ), ρ < (e i + k).re → ρ + 2 * δ ≤ (e i + k).re := by
    intro i k hk
    obtain ⟨e₀, he₀, m, hm⟩ := hmem i
    have hshift : e i + k = e₀ + ((m + k : ℕ) : ℂ) := by rw [hm]; push_cast; ring
    rw [hshift] at hk ⊢
    rcases he₀ with h | h
    · exact hgap e₀ h (m + k) hk
    · exact hgap' e₀ h (m + k) hk
  have hcovq : ∀ e₀ : ℂ, q.IsRoot e₀ → ∀ k : ℕ, (e₀ + k).re ≤ ρ → ∃ i, e i = e₀ + k :=
    fun e₀ h k hk => hcov _ (Or.inl ⟨e₀, h, k, rfl⟩) hk
  have hcovq' : ∀ e₀ : ℂ, q'.IsRoot e₀ → ∀ k : ℕ, (e₀ + k).re ≤ ρ → ∃ i, e i = e₀ + k :=
    fun e₀ h k hk => hcov _ (Or.inr ⟨e₀, h, k, rfl⟩) hk
  set J : ℕ := max (max q.natDegree q'.natDegree) (max (n * q.natDegree) (n * q'.natDegree)) with hJ
  have hJ₁ : q.natDegree ≤ J := (le_max_left _ _).trans (le_max_left _ _)
  have hJ₁' : q'.natDegree ≤ J := (le_max_right _ _).trans (le_max_left _ _)
  have hJ₂ : n * q'.natDegree ≤ J := (le_max_right _ _).trans (le_max_right _ _)
  have hJ₂' : n * q.natDegree ≤ J := (le_max_left _ _).trans (le_max_right _ _)
  refine ⟨n, J, e, δ, hδ, he_inj, hre, ?_⟩
  intro N u h1 h2 h3 h4 h5 h6 h7 h8
  obtain ⟨r, w, κ, Mc, Mc', A, A', hw0, hκ0, _hκ, hMc, hMc', hA, hA', hsysg⟩ := hsysU u h1 h2 h3 h4 h5 h6 h7
  have hu : Continuous u := by simpa using h1 []

  obtain ⟨W, hWdef⟩ : ∃ W : ℝ → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, W = fun y₁ y₂ k =>
    whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
      NumberField.StandardAddChar.psiQ u
      (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) := ⟨_, rfl⟩
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → (Fin (r + 1) → ℂ), V = fun y z g i =>
    whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
      NumberField.StandardAddChar.psiQ
      (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u (w i))
      (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y * z, z, 1] i else 0) * g * κ i) := ⟨_, rfl⟩
  have hVW : ∀ y z g, V y z g 0 = W y z g := by
    intro y z g
    simp only [hVdef, hWdef, hw0, hκ0, List.foldr_nil, mul_one]
  have hVc : ContinuousOn (fun w : ℝ × ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => V w.1 w.2.1 w.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioi 0 ×ˢ Set.univ) := by
    rw [hVdef]
    exact continuousOn_pi.2 fun i => continuousOn_whittaker3_diag_mul (h1 (w i)) (κ i)
  have hWc : ContinuousOn (fun w : ℝ × ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => W w.1 w.2.1 w.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioi 0 ×ˢ Set.univ) := by
    have h := continuousOn_whittaker3_diag_mul hu (1 : AdelicGL 3 (𝓞 ℚ) ℚ)
    simpa only [hWdef, mul_one] using h

  obtain ⟨W', hW'def⟩ : ∃ W' : ℝ → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, W' = fun a b k => W b a k := ⟨_, rfl⟩
  obtain ⟨V', hV'def⟩ : ∃ V' : ℝ → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → (Fin (r + 1) → ℂ), V' = fun a b g => V b a g :=
    ⟨_, rfl⟩
  subst hW'def hV'def
  have hswap : Continuous fun w : ℝ × ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => ((w.2.1, w.1, w.2.2) : ℝ × ℝ × AdelicGL 3 (𝓞 ℚ) ℚ) := by
    fun_prop
  have hswap_maps : Set.MapsTo (fun w : ℝ × ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => ((w.2.1, w.1, w.2.2) : ℝ × ℝ × AdelicGL 3 (𝓞 ℚ) ℚ))
      (Set.Ioi 0 ×ˢ Set.Ioi 0 ×ˢ Set.univ) (Set.Ioi 0 ×ˢ Set.Ioi 0 ×ˢ Set.univ) := by
    rintro ⟨a, b, k⟩ ⟨ha, hb, -⟩
    exact ⟨hb, ha, Set.mem_univ _⟩
  have hVc' : ContinuousOn (fun w : ℝ × ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => (fun a b g => V b a g) w.1 w.2.1 w.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioi 0 ×ˢ Set.univ) := hVc.comp hswap.continuousOn hswap_maps
  have hWc' : ContinuousOn (fun w : ℝ × ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => (fun a b k => W b a k) w.1 w.2.1 w.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioi 0 ×ˢ Set.univ) := hWc.comp hswap.continuousOn hswap_maps

  have hsysV : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, archComponent3 (𝓞 ℚ) ℚ g ∈ orth3 →
      ∃ Fy Fz : ℝ → ℝ → (Fin (r + 1) → ℂ),
      (∀ z : ℝ, 0 < z → ∀ y : ℝ, 0 < y → HasDerivAt (fun y => V y z g) (Fy y z) y ∧
        (y : ℂ) • Fy y z = (fun i => ∑ j, (∑ b : Fin (d₂ + 1), (z : ℂ) ^ (b : ℕ) * Mc g b i j) • V y z g j) +
          ∑ k : Fin d, ∑ b : Fin (d₂ + 1),
            ((y : ℂ) ^ ((k : ℕ) + 1) * (z : ℂ) ^ (b : ℕ)) • A g k b (V y z g)) ∧
      (∀ y : ℝ, 0 < y → ∀ z : ℝ, 0 < z → HasDerivAt (fun z => V y z g) (Fz y z) z ∧
        (z : ℂ) • Fz y z = (fun i => ∑ j, (∑ a : Fin (d₂' + 1), (y : ℂ) ^ (a : ℕ) * Mc' g a i j) • V y z g j) +
          ∑ k : Fin d', ∑ a : Fin (d₂' + 1),
            ((z : ℂ) ^ ((k : ℕ) + 1) * (y : ℂ) ^ (a : ℕ)) • A' g k a (V y z g)) :=
    fun g hg => ((hsysg g hg).2.2 (fun y z => V y z g) (fun y z i => by rw [hVdef])).2
  choose! Fy Fz hFy hFz using hsysV

  obtain ⟨S, hS⟩ : ∃ S : Set (AdelicGL 3 (𝓞 ℚ) ℚ), ∀ k, k ∈ S ↔ archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 :=
    ⟨{k | archComponent3 (𝓞 ℚ) ℚ k ∈ orth3}, fun _ => Iff.rfl⟩
  have hG0 := LanglandsTunnell.CubicInduction.exists_whittaker3_diag_mul_transport_of_isCompact ω u hu h2 h3
  have htrans₁ : ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ (lam₀ nB Ω : ℝ) (K₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)),
      0 < lam₀ ∧ lam₀ ≤ 1 ∧ 0 ≤ nB ∧ 0 ≤ Ω ∧ IsCompact K₀ ∧ K₀ ⊆ S ∧
      ∀ g ∈ K, ∃ (lam τ n₁ n₂ : ℝ) (κ₁ : ℂ) (k' : AdelicGL 3 (𝓞 ℚ) ℚ), k' ∈ K₀ ∧
        lam₀ ≤ lam ∧ lam ≤ lam₀⁻¹ ∧ lam₀ ≤ τ ∧ τ ≤ lam₀⁻¹ ∧ |n₁| ≤ nB ∧ |n₂| ≤ nB ∧ ‖κ₁‖ ≤ Ω ∧
        ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
          W y₁ y₂ g = κ₁ * Complex.exp (2 * Real.pi * Complex.I * ((y₁ * n₁ + y₂ * n₂ : ℝ) : ℂ)) *
            W (lam * y₁) (τ * y₂) k' := by
    intro K hK
    obtain ⟨lam₀, nB, Ω, K₀, h0, h1', hnB, hΩ, hK₀, horth, hT⟩ := hG0 K hK
    refine ⟨lam₀, nB, Ω, K₀, h0, h1', hnB, hΩ, hK₀, fun k hk => (hS k).2 (horth k hk), fun g hg => ?_⟩
    obtain ⟨lam, τ, n₁, n₂, κ₁, k', hk', hl1, hl2, ht1, ht2, hn1, hn2, hκ, hid⟩ := hT g hg
    exact ⟨lam, τ, n₁, n₂, κ₁, k', hk', hl1, hl2, ht1, ht2, hn1, hn2, hκ, fun y₁ y₂ hy₁ hy₂ => by
      simp only [hWdef]
      exact hid y₁ y₂ hy₁ hy₂⟩
  have htrans₂ : ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ (lam₀ nB Ω : ℝ) (K₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)),
      0 < lam₀ ∧ lam₀ ≤ 1 ∧ 0 ≤ nB ∧ 0 ≤ Ω ∧ IsCompact K₀ ∧ K₀ ⊆ S ∧
      ∀ g ∈ K, ∃ (lam τ n₁ n₂ : ℝ) (κ₁ : ℂ) (k' : AdelicGL 3 (𝓞 ℚ) ℚ), k' ∈ K₀ ∧
        lam₀ ≤ lam ∧ lam ≤ lam₀⁻¹ ∧ lam₀ ≤ τ ∧ τ ≤ lam₀⁻¹ ∧ |n₁| ≤ nB ∧ |n₂| ≤ nB ∧ ‖κ₁‖ ≤ Ω ∧
        ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
          (fun a b k => W b a k) y₁ y₂ g = κ₁ * Complex.exp (2 * Real.pi * Complex.I * ((y₁ * n₁ + y₂ * n₂ : ℝ) : ℂ)) *
            (fun a b k => W b a k) (lam * y₁) (τ * y₂) k' := by
    intro K hK
    obtain ⟨lam₀, nB, Ω, K₀, h0, h1', hnB, hΩ, hK₀, horth, hT⟩ := hG0 K hK
    refine ⟨lam₀, nB, Ω, K₀, h0, h1', hnB, hΩ, hK₀, fun k hk => (hS k).2 (horth k hk), fun g hg => ?_⟩
    obtain ⟨lam, τ, n₁, n₂, κ₁, k', hk', hl1, hl2, ht1, ht2, hn1, hn2, hκ, hid⟩ := hT g hg
    refine ⟨τ, lam, n₂, n₁, κ₁, k', hk', ht1, ht2, hl1, hl2, hn2, hn1, hκ, fun y₁ y₂ hy₁ hy₂ => ?_⟩
    have hre' : (y₂ * n₁ + y₁ * n₂ : ℝ) = y₁ * n₂ + y₂ * n₁ := by ring
    show W y₂ y₁ g = κ₁ * Complex.exp (2 * Real.pi * Complex.I * ((y₁ * n₂ + y₂ * n₁ : ℝ) : ℂ)) *
      W (lam * y₂) (τ * y₁) k'
    simp only [hWdef]
    rw [hid y₂ y₁ hy₂ hy₁, hre']

  have hslice₁ : ∀ K₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K₀ → K₀ ⊆ S → ∀ Z : ℝ, 2 ≤ Z →
      ∃ (m C : ℝ) (cS : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
        (c₂ : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
        (∀ k ∈ K₀, ∀ i j i' j', ‖c₂ i j i' j' k‖ ≤ C) ∧
        (∀ k ∈ K₀, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ∀ i j, ‖cS i j z k‖ ≤ C * z ^ (-m)) ∧
        (∀ k ∈ K₀, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
          ‖W y z k - ∑ i : Fin n, ∑ j : Fin J,
              cS i j z k * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤ C * z ^ (-m) * y ^ (ρ + δ)) ∧
        (∀ k ∈ K₀, ∀ i j, ∀ z ∈ Set.Ioc (0 : ℝ) 1,
          ‖cS i j z k - ∑ i' : Fin n, ∑ j' : Fin J,
              c₂ i j i' j' k * ((z : ℂ) ^ e i' * ((Real.log z : ℝ) : ℂ) ^ (j' : ℕ))‖ ≤ C * z ^ (ρ + δ)) := by
    intro K₀ hK₀ hK₀S Z hZ
    obtain ⟨CS, hCS⟩ := exists_bound_words N u h1 h8 w κ K₀ hK₀
    obtain ⟨m, C, cS, c₂, ha, hb, hc, hd⟩ := slice_package e he_inj ρ δ hδ hre hcl hgapF q q' hq hq' hcovq
      hcovq' hgap hgap' hJ₁ hJ₂ Mc A Mc' A' hMc hA hMc' hA' K₀ hK₀ (fun g hg => (hsysg g ((hS g).1 (hK₀S hg))).1)
      (fun g hg => (hsysg g ((hS g).1 (hK₀S hg))).2.1) V hVc Fy Fz (fun g hg => hFy g ((hS g).1 (hK₀S hg)))
      (fun g hg => hFz g ((hS g).1 (hK₀S hg))) N CS
      (fun g hg y z hy hz => by rw [hVdef]; exact hCS g hg y z hy hz) 0 Z hZ
    exact ⟨m, C, cS, c₂, ha, hb, fun k hk z hz y hy => by rw [← hVW]; exact hc k hk z hz y hy, hd⟩
  have hslice₂ : ∀ K₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K₀ → K₀ ⊆ S → ∀ Z : ℝ, 2 ≤ Z →
      ∃ (m C : ℝ) (cS : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
        (c₂ : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
        (∀ k ∈ K₀, ∀ i j i' j', ‖c₂ i j i' j' k‖ ≤ C) ∧
        (∀ k ∈ K₀, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ∀ i j, ‖cS i j z k‖ ≤ C * z ^ (-m)) ∧
        (∀ k ∈ K₀, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
          ‖(fun a b k => W b a k) y z k - ∑ i : Fin n, ∑ j : Fin J,
              cS i j z k * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤ C * z ^ (-m) * y ^ (ρ + δ)) ∧
        (∀ k ∈ K₀, ∀ i j, ∀ z ∈ Set.Ioc (0 : ℝ) 1,
          ‖cS i j z k - ∑ i' : Fin n, ∑ j' : Fin J,
              c₂ i j i' j' k * ((z : ℂ) ^ e i' * ((Real.log z : ℝ) : ℂ) ^ (j' : ℕ))‖ ≤ C * z ^ (ρ + δ)) := by
    intro K₀ hK₀ hK₀S Z hZ
    obtain ⟨CS, hCS⟩ := exists_bound_words N u h1 h8 w κ K₀ hK₀
    obtain ⟨m, C, cS, c₂, ha, hb, hc, hd⟩ := slice_package e he_inj ρ δ hδ hre hcl hgapF q' q hq' hq hcovq'
      hcovq hgap' hgap hJ₁' hJ₂' Mc' A' Mc A hMc' hA' hMc hA K₀ hK₀ (fun g hg => (hsysg g ((hS g).1 (hK₀S hg))).2.1)
      (fun g hg => (hsysg g ((hS g).1 (hK₀S hg))).1) (fun a b g => V b a g) hVc' (fun g a b => Fz g b a)
      (fun g a b => Fy g b a)
      (fun g hg z hz y hy => hFz g ((hS g).1 (hK₀S hg)) z hz y hy) (fun g hg y hy z hz => hFy g ((hS g).1 (hK₀S hg)) y hy z hz) N CS
      (fun g hg y z hy hz => by
        have h := hCS g hg z y hz hy
        rw [hVdef]
        refine h.trans (le_of_eq ?_)
        ring) 0 Z hZ
    refine ⟨m, C, cS, c₂, ha, hb, fun k hk z hz y hy => ?_, hd⟩
    have h := hc k hk z hz y hy
    dsimp only at h ⊢
    rw [← hVW z y k]
    exact h

  obtain ⟨c₁, hc₁c, hc₁K, c₁', hc₁'c, hc₁'K⟩ :=
    RegularSingular.exists_twoLevel_coeff_of_transport_of_slice_expansion e he_inj ρ δ hδ hre hcl hgapF S W hWc
      htrans₁ hslice₁
  obtain ⟨c₂, hc₂c, hc₂K, c₂', hc₂'c, hc₂'K⟩ :=
    RegularSingular.exists_twoLevel_coeff_of_transport_of_slice_expansion e he_inj ρ δ hδ hre hcl hgapF S
      (fun a b k => W b a k) hWc' htrans₂ hslice₂
  refine ⟨⟨c₁, hc₁c, fun K hK b hb => ?_, c₁', hc₁'c, hc₁'K⟩, ⟨c₂, hc₂c, fun K hK b hb => ?_, c₂', hc₂'c, hc₂'K⟩⟩
  · obtain ⟨C, hC⟩ := hc₁K K hK b hb
    refine ⟨C, fun k hk y₂ hy₂l hy₂u y₁ hy₁0 hy₁1 => ?_⟩
    have h := hC k hk y₂ hy₂l hy₂u y₁ hy₁0 hy₁1
    simpa only [hWdef] using h
  · obtain ⟨C, hC⟩ := hc₂K K hK b hb
    refine ⟨C, fun k hk y₁ hy₁l hy₁u y₂ hy₂0 hy₂1 => ?_⟩
    have h := hC k hk y₁ hy₁l hy₁u y₂ hy₂0 hy₂1
    simpa only [hWdef] using h

end S_LanglandsTunnell_CubicInduction_exists_exponents_whittaker3_diag_joint_expansion_of_casimir_relations
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_exponents_whittaker3_diag_joint_expansion_of_casimir_relations (solution)
