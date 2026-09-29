-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/d83e4371-6fd3-5e26-9fbc-becc0760752b

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_RepTheory_SmoothAdmissibleSchurCommutant
import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_Growth
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2
import Definitions.Def_NumberField_Completion_Finite
import Definitions.Def_Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace
import Definitions.Def_Mathlib_LinearAlgebra_Countable
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mul_eq_unipotent_mul_diagonal_mul_compact
import Theorems.Thm_RepTheory_IsometricRep_exists_forall_sum_smul_eq_zero_of_finiteDimensional_inf_fixedVectors
import Theorems.Thm_RepTheory_IsometricRep_exists_finiteDimensional_inf_fixedVectors_of_isCompactOperator
import Theorems.Thm_LanglandsTunnell_CubicInduction_smoothingOperator_mem_cuspFunctions_of_isCuspidalAlong
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isCompactOperator_cuspidalSubspace_smoothingOperator
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_TateGlobal_compactSpace_normOneIdeleClass
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_isCosetEigenfunction
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one
import Theorems.Thm_LanglandsTunnell_CubicInduction_measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace
import Theorems.Thm_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar_finThree_rat
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.GroupTheory.Complement
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Topology.Separation.Hausdorff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions WhittakerBlock.sigmaCompactSpace_adelicGL3 M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b"
p2m_attr_erase "simp" "AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level LanglandsTunnell.CubicInduction.fnTwist3_apply LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one"

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.AdelicGL CubicInduction.globalPointsGL"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "SlabL2.realCoordinate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 LocalGL3 heckeGen1 heckeGen2 cosetSum IsCosetEigenfunction IsRightInvariant archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 one_le_gauge3 one_le_archGauge3 IsModerateGrowth3 matrixFin_ext matrixAdele_ext localMatN localMatN_apply_self localMatN_apply_of_ne mapMatrix_localMatN_self mapMatrix_localMatN_of_ne localEmbedN finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN finEmbedN localToAdelic3 exists_mul_eq_unipotent_mul_diagonal_mul_compact smoothingOperator_mem_cuspFunctions_of_isCuspidalAlong exists_isCompactOperator_cuspidalSubspace_smoothingOperator exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous exists_inner_toL2_translateRight_ne_zero_of_isCosetEigenfunction measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator"
namespace Level2
namespace Twist
p2m_open "LanglandsTunnell.CubicInduction~isCompact_localMaximalCompact3~det_radicalP21~det_radicalP12 LanglandsTunnell~CubicInduction.isCompact_localMaximalCompact3"

open FLT.SmoothAdmissibleSchurCommutant Filter
p2m_open "Matrix IsDedekindDomain NumberField LanglandsTunnell.CubicInduction~isCompact_localMaximalCompact3~det_radicalP21~det_radicalP12 P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction M4aHerbrand NumberField.TateGlobal"

section TrivialLine

private theorem exists_isIrreducibleRep_isSmoothRep_isAdmissibleRep (G : Type) [Group G] [TopologicalSpace G] :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Module ℂ E) (πE : G →* Module.End ℂ E),
      IsIrreducibleRep πE ∧ IsSmoothRep πE ∧ IsAdmissibleRep πE := by
  refine ⟨ℂ, inferInstance, inferInstance, 1, ?_, ?_, ?_⟩
  · refine ⟨⟨1, one_ne_zero⟩, fun W _ => ?_⟩
    rcases eq_or_ne W ⊥ with h | h
    · exact Or.inl h
    · right
      obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
      rw [eq_top_iff]
      intro z _
      have hz : z = (z * w⁻¹) • w := by
        rw [smul_eq_mul, mul_assoc, inv_mul_cancel₀ hw0, mul_one]
      rw [hz]
      exact W.smul_mem _ hwW
  · intro v
    have h : ((repStabilizer (1 : G →* Module.End ℂ ℂ) v : Subgroup G) : Set G) = Set.univ := by
      ext g
      simp only [SetLike.mem_coe, mem_repStabilizer, MonoidHom.one_apply, Module.End.one_apply, Set.mem_univ]
    rw [h]
    exact isOpen_univ
  · intro K _ _
    infer_instance

private theorem apply_eq_one_of_compactSpace {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    (χ : G →* ℝ) (hχ : Continuous χ) (hpos : ∀ g, 0 < χ g) (g : G) : χ g = 1 := by

  obtain ⟨M, hM⟩ := (isCompact_range hχ).bddAbove
  have hbound : ∀ x : G, χ x ≤ M := fun x => hM ⟨x, rfl⟩
  have hle : ∀ x : G, χ x ≤ 1 := by
    intro x
    by_contra hx
    push Not at hx
    have ht := tendsto_pow_atTop_atTop_of_one_lt hx
    obtain ⟨n, hn⟩ := (ht.eventually_gt_atTop M).exists
    exact absurd (hbound (x ^ n)) (by rw [map_pow]; exact not_le.mpr hn)
  have h1 := hle g
  have h2 := hle g⁻¹
  rw [map_inv] at h2
  have hg := hpos g
  have h3 : 1 ≤ χ g := by
    rwa [inv_le_one₀ hg] at h2
  exact le_antisymm h1 h3

end TrivialLine

section Character

private theorem continuous_centralScalarGL : Continuous (centralScalarGL 3 (𝓞 ℚ) ℚ) := by
  have h : Continuous fun (a : AdeleRing (𝓞 ℚ) ℚ) (_ : Fin 3) => a := continuous_pi fun _ => continuous_id
  have hd : Continuous ((Matrix.scalar (Fin 3) :
      AdeleRing (𝓞 ℚ) ℚ →+* Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom) := by
    show Continuous fun a : AdeleRing (𝓞 ℚ) ℚ => Matrix.scalar (Fin 3) a
    simpa only [Matrix.scalar_apply] using h.matrix_diagonal
  exact Continuous.units_map _ hd

private theorem globalPointsGL_scalar (q : ℚˣ) :
    globalPointsGL 3 (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.scalar (Fin 3) q) =
      centralScalarGL 3 (𝓞 ℚ) ℚ (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) : ℚ →* AdeleRing (𝓞 ℚ) ℚ) q) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change ((algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)).mapMatrix (Matrix.scalar (Fin 3) (q : ℚ))) i j =
    (Matrix.scalar (Fin 3) (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (q : ℚ))) i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs with h
  · rfl
  · exact map_zero _

variable (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)

private theorem continuous_character_of_central (hc : Continuous f)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g)
    (g₀ : AdelicGL 3 (𝓞 ℚ) ℚ) (h0 : f g₀ ≠ 0) : Continuous fun z => (ω z : ℂ) := by
  have h1 : Continuous fun z => f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g₀) :=
    hc.comp ((continuous_centralScalarGL.comp continuous_id).mul continuous_const)
  have h2 : (fun z => (ω z : ℂ)) = fun z => f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g₀) / f g₀ := by
    funext z
    rw [hcen, mul_div_cancel_right₀ _ h0]
  rw [h2]
  exact h1.div_const _

private theorem character_eq_one_of_mem_principalIdeles
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g)
    (g₀ : AdelicGL 3 (𝓞 ℚ) ℚ) (h0 : f g₀ ≠ 0)
    (x : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (hx : x ∈ principalIdeles (𝓞 ℚ) ℚ) : ω x = 1 := by
  obtain ⟨q, rfl⟩ := hx
  have key := hcen (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) : ℚ →* AdeleRing (𝓞 ℚ) ℚ) q) g₀
  rw [← globalPointsGL_scalar, haut] at key

  have h1 : ((ω (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) : ℚ →* AdeleRing (𝓞 ℚ) ℚ) q) : ℂˣ) : ℂ) = 1 :=
    (mul_eq_right₀ h0).mp key.symm
  exact Units.val_eq_one.mp h1

end Character

section NormOne

private theorem ideleNorm_one : ideleNorm ℚ (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ) = 1 := by
  simp [ideleNorm]

private theorem mul_inv_mem_normOneIdeles {x y : (AdeleRing (𝓞 ℚ) ℚ)ˣ} (h : ideleNorm ℚ x = ideleNorm ℚ y) :
    x * y⁻¹ ∈ normOneIdeles ℚ := by
  rw [mem_normOneIdeles_iff]
  have hy : ideleNorm ℚ y * ideleNorm ℚ y⁻¹ = 1 := by rw [← ideleNorm_mul, mul_inv_cancel, ideleNorm_one]
  rw [ideleNorm_mul, h]
  exact hy

variable (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℝ)

private theorem character_eq_one_of_mem_normOneIdeles
    (hK : CompactSpace (↥(normOneIdeles ℚ) ⧸ (principalIdeles (𝓞 ℚ) ℚ).subgroupOf (normOneIdeles ℚ)))
    (hχc : Continuous χ) (hpos : ∀ x, 0 < χ x) (h1 : ∀ x ∈ principalIdeles (𝓞 ℚ) ℚ, χ x = 1)
    (x : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (hx : x ∈ normOneIdeles ℚ) : χ x = 1 := by
  haveI := hK
  let N : Subgroup (AdeleRing (𝓞 ℚ) ℚ)ˣ := normOneIdeles ℚ
  let P : Subgroup N := (principalIdeles (𝓞 ℚ) ℚ).subgroupOf N
  let χN : N →* ℝ := χ.comp N.subtype
  have hP : P ≤ χN.ker := by
    intro y hy
    rw [MonoidHom.mem_ker]
    exact h1 _ (Subgroup.mem_subgroupOf.mp hy)
  let χQ : N ⧸ P →* ℝ := QuotientGroup.lift P χN hP
  have hcN : Continuous χN := hχc.comp continuous_subtype_val
  have hcQ : Continuous χQ := by
    rw [(QuotientGroup.isQuotientMap_mk P).continuous_iff]
    exact hcN
  have hposQ : ∀ q : N ⧸ P, 0 < χQ q := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H y => rw [QuotientGroup.lift_mk]; exact hpos _
  have key := apply_eq_one_of_compactSpace χQ hcQ hposQ ((⟨x, hx⟩ : N) : N ⧸ P)
  rw [QuotientGroup.lift_mk] at key
  exact key

private theorem character_eq_of_ideleNorm_eq
    (hK : CompactSpace (↥(normOneIdeles ℚ) ⧸ (principalIdeles (𝓞 ℚ) ℚ).subgroupOf (normOneIdeles ℚ)))
    (hχc : Continuous χ) (hpos : ∀ x, 0 < χ x) (h1 : ∀ x ∈ principalIdeles (𝓞 ℚ) ℚ, χ x = 1)
    {x y : (AdeleRing (𝓞 ℚ) ℚ)ˣ} (h : ideleNorm ℚ x = ideleNorm ℚ y) : χ x = χ y := by
  have h1N := character_eq_one_of_mem_normOneIdeles χ hK hχc hpos h1 _ (mul_inv_mem_normOneIdeles h)
  rw [map_mul, map_inv] at h1N
  have hy0 : χ y ≠ 0 := (hpos y).ne'
  rw [mul_inv_eq_one₀ hy0] at h1N
  exact h1N

private theorem exists_character_eq_ideleNorm_rpow
    (hK : CompactSpace (↥(normOneIdeles ℚ) ⧸ (principalIdeles (𝓞 ℚ) ℚ).subgroupOf (normOneIdeles ℚ)))
    (hχc : Continuous χ) (hpos : ∀ x, 0 < χ x) (h1 : ∀ x ∈ principalIdeles (𝓞 ℚ) ℚ, χ x = 1)
    (s : ℝ → (AdeleRing (𝓞 ℚ) ℚ)ˣ) (hs : ∀ r, 0 < r → ideleNorm ℚ (s r) = r)
    (hsc : ContinuousOn (fun r => χ (s r)) (Set.Ioi 0)) :
    ∃ σ : ℝ, ∀ x, χ x = ideleNorm ℚ x ^ σ := by

  let a : ℝ → ℝ := fun t => Real.log (χ (s (Real.exp t)))
  have hadd : ∀ t u, a (t + u) = a t + a u := by
    intro t u
    have hn : ideleNorm ℚ (s (Real.exp (t + u))) = ideleNorm ℚ (s (Real.exp t) * s (Real.exp u)) := by
      rw [ideleNorm_mul, hs _ (Real.exp_pos _), hs _ (Real.exp_pos _), hs _ (Real.exp_pos _), Real.exp_add]
    show Real.log _ = Real.log _ + Real.log _
    rw [character_eq_of_ideleNorm_eq χ hK hχc hpos h1 hn, map_mul,
      Real.log_mul (hpos _).ne' (hpos _).ne']
  have hca : Continuous a := by
    have h1' : Continuous fun t => χ (s (Real.exp t)) :=
      hsc.comp_continuous Real.continuous_exp fun t => Real.exp_pos t
    exact h1'.log fun t => (hpos _).ne'
  let A : ℝ →+ ℝ := AddMonoidHom.mk' a hadd
  let L := A.toRealLinearMap hca
  have hL : ∀ t, a t = t * a 1 := by
    intro t
    have h := L.map_smul t (1 : ℝ)
    rw [smul_eq_mul, mul_one, smul_eq_mul] at h
    exact h
  refine ⟨a 1, fun x => ?_⟩
  have hr := ideleNorm_pos (F := ℚ) x
  have hx : χ x = χ (s (Real.exp (Real.log (ideleNorm ℚ x)))) := by
    refine character_eq_of_ideleNorm_eq χ hK hχc hpos h1 ?_
    rw [hs _ (Real.exp_pos _), Real.exp_log hr]
  have hlog : Real.log (χ x) = Real.log (ideleNorm ℚ x) * a 1 := by
    rw [hx]
    exact hL _
  rw [Real.rpow_def_of_pos hr, ← hlog, Real.exp_log (hpos x)]

end NormOne

end LanglandsTunnell.CubicInduction.Level2.Twist

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.AdelicGL CubicInduction.globalPointsGL"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "SlabL2.realCoordinate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 LocalGL3 heckeGen1 heckeGen2 cosetSum IsCosetEigenfunction IsRightInvariant archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 one_le_gauge3 one_le_archGauge3 IsModerateGrowth3 matrixFin_ext matrixAdele_ext localMatN localMatN_apply_self localMatN_apply_of_ne mapMatrix_localMatN_self mapMatrix_localMatN_of_ne localEmbedN finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN finEmbedN localToAdelic3 exists_mul_eq_unipotent_mul_diagonal_mul_compact smoothingOperator_mem_cuspFunctions_of_isCuspidalAlong exists_isCompactOperator_cuspidalSubspace_smoothingOperator exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous exists_inner_toL2_translateRight_ne_zero_of_isCosetEigenfunction measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator"
namespace Level2
namespace Twist
p2m_open "LanglandsTunnell.CubicInduction~isCompact_localMaximalCompact3~det_radicalP21~det_radicalP12 LanglandsTunnell~CubicInduction.isCompact_localMaximalCompact3"

open FLT.SmoothAdmissibleSchurCommutant

variable {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E]

private def twistRep (c : G →* ℂˣ) (π : G →* Module.End ℂ E) : G →* Module.End ℂ E where
  toFun h := ((c h : ℂˣ) : ℂ) • π h
  map_one' := by simp only [map_one, Units.val_one, one_smul]
  map_mul' h h' := by
    refine LinearMap.ext fun x => ?_
    simp only [map_mul, Units.val_mul, LinearMap.smul_apply, Module.End.mul_apply, map_smul, smul_smul]
    rw [mul_comm]

private theorem twistRep_apply (c : G →* ℂˣ) (π : G →* Module.End ℂ E) (h : G) (x : E) :
    twistRep c π h x = ((c h : ℂˣ) : ℂ) • π h x := rfl

private theorem isIrreducibleRep_twistRep (c : G →* ℂˣ) {π : G →* Module.End ℂ E} (hπ : IsIrreducibleRep π) :
    IsIrreducibleRep (twistRep c π) := by
  refine ⟨hπ.1, fun W hW => hπ.2 W fun g v hv => ?_⟩
  have h := hW g v hv
  rw [twistRep_apply] at h
  exact (Submodule.smul_mem_iff W (c g).ne_zero).mp h

variable [TopologicalSpace G] [IsTopologicalGroup G]

private theorem
    isSmoothRep_twistRep (c : G →* ℂˣ) (hc : IsOpen ((c.ker : Subgroup G) : Set G)) {π : G →* Module.End ℂ E}
    (hπ : IsSmoothRep π) : IsSmoothRep (twistRep c π) := by
  intro v
  refine Subgroup.isOpen_mono (H₁ := repStabilizer π v ⊓ c.ker) (fun x hx => ?_) ?_
  · rw [Subgroup.mem_inf, mem_repStabilizer, MonoidHom.mem_ker] at hx
    rw [mem_repStabilizer, twistRep_apply, hx.1, hx.2, Units.val_one, one_smul]
  · rw [Subgroup.coe_inf]
    exact (hπ v).inter hc

omit [IsTopologicalGroup G] in
private theorem
    isAdmissibleRep_twistRep (c : G →* ℂˣ) (hcK : ∀ K : Subgroup G, IsCompact (K : Set G) → ∀ k ∈ K, c k = 1)
    {π : G →* Module.End ℂ E} (hπ : IsAdmissibleRep π) : IsAdmissibleRep (twistRep c π) := by
  intro K hK hKo
  have h : fixedVectors (twistRep c π) K = fixedVectors π K := by
    ext v
    simp only [mem_fixedVectors]
    refine forall₂_congr fun u hu => ?_
    rw [twistRep_apply, hcK K hK u hu, Units.val_one, one_smul]
  rw [h]
  exact hπ K hK hKo

omit [TopologicalSpace G] [IsTopologicalGroup G] in

private theorem exists_finsupp_mul (c : G →* ℂˣ) (μ : G →₀ ℂ) :
    ∃ ν : G →₀ ℂ, ν.support ⊆ μ.support ∧ ∀ h, ν h = μ h * ((c h : ℂˣ) : ℂ) := by
  refine ⟨Finsupp.onFinset μ.support (fun h => μ h * ((c h : ℂˣ) : ℂ)) fun h hh => ?_,
    Finsupp.support_onFinset_subset, fun h => Finsupp.onFinset_apply⟩
  rw [Finsupp.mem_support_iff]
  exact fun h0 => hh (by simp only [h0, zero_mul])

omit [TopologicalSpace G] [IsTopologicalGroup G] in

private theorem finsupp_sum_smul_eq {V : Type} [AddCommGroup V] [Module ℂ V] (c : G →* ℂˣ) (μ ν : G →₀ ℂ)
    (hνs : ν.support ⊆ μ.support) (hν : ∀ h, ν h = μ h * ((c h : ℂˣ) : ℂ)) (Φ : G → V) :
    (μ.sum fun h a => a • (((c h : ℂˣ) : ℂ) • Φ h)) = ν.sum fun h a => a • Φ h := by
  rw [Finsupp.sum, Finsupp.sum_of_support_subset ν hνs _ fun h _ => zero_smul ℂ (Φ h)]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [smul_smul, hν]

omit [TopologicalSpace G] [IsTopologicalGroup G] in

private theorem finsupp_sum_translate_eq_zero {X : Type} (act : X → G → X) (n : X → ℂ) (nv : G →* ℂˣ) (F F' : X → ℂ)
    (hF' : ∀ y, F' y = n y * F y) (hn : ∀ x h, n (act x h) = n x * ((nv h : ℂˣ) : ℂ)) (hn0 : ∀ x, n x ≠ 0)
    (μ ν : G →₀ ℂ) (hνs : ν.support ⊆ μ.support) (hν : ∀ h, ν h = μ h * (((nv h)⁻¹ : ℂˣ) : ℂ))
    (hzero : (ν.sum fun h a => a • fun x => F' (act x h)) = 0) :
    (μ.sum fun h a => a • fun x => F (act x h)) = 0 := by
  funext x
  have hx := congrFun hzero x
  rw [Finsupp.sum_of_support_subset ν hνs (fun h a => a • fun x => F' (act x h)) fun h _ => zero_smul ℂ _,
    Finset.sum_apply] at hx
  rw [Finsupp.sum, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hx ⊢
  have hrw : ∀ h ∈ μ.support, ν h * F' (act x h) = n x * (μ h * F (act x h)) := by
    intro h _
    rw [hν, hF', hn]
    have hu : (((nv h)⁻¹ : ℂˣ) : ℂ) * ((nv h : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    linear_combination (μ h * n x * F (act x h)) * hu
  rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum] at hx
  exact (mul_eq_zero.mp hx).resolve_left (hn0 x)

end LanglandsTunnell.CubicInduction.Level2.Twist

section DeterminantGaugeBlock

open IsDedekindDomain NumberField NumberField.TateGlobal Matrix
open scoped NNReal

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.AdelicGL CubicInduction.globalPointsGL"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "SlabL2.realCoordinate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 LocalGL3 heckeGen1 heckeGen2 cosetSum IsCosetEigenfunction IsRightInvariant archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 one_le_gauge3 one_le_archGauge3 IsModerateGrowth3 matrixFin_ext matrixAdele_ext localMatN localMatN_apply_self localMatN_apply_of_ne mapMatrix_localMatN_self mapMatrix_localMatN_of_ne localEmbedN finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN finEmbedN localToAdelic3 exists_mul_eq_unipotent_mul_diagonal_mul_compact smoothingOperator_mem_cuspFunctions_of_isCuspidalAlong exists_isCompactOperator_cuspidalSubspace_smoothingOperator exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous exists_inner_toL2_translateRight_ne_zero_of_isCosetEigenfunction measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator"
p2m_open "LanglandsTunnell.CubicInduction~isCompact_localMaximalCompact3~det_radicalP21~det_radicalP12 LanglandsTunnell~CubicInduction.isCompact_localMaximalCompact3"

namespace DeterminantGauge

section NormedField

variable {L : Type*} [NormedField L]

private theorem nnnorm_apply_le_matrixSupSize (k : GL (Fin 3) L) (i j : Fin 3) :
    ‖(k : Matrix (Fin 3) (Fin 3) L) i j‖₊ ≤ matrixSupSize k := by
  unfold matrixSupSize
  exact le_trans (le_max_left _ _)
    (Finset.le_sup (f := fun ij : Fin 3 × Fin 3 => max ‖(k : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊
        ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊) (Finset.mem_univ (i, j)))

private theorem nnnorm_inv_apply_le_matrixSupSize (k : GL (Fin 3) L) (i j : Fin 3) :
    ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖₊ ≤ matrixSupSize k := by
  unfold matrixSupSize
  exact le_trans (le_max_right _ _)
    (Finset.le_sup (f := fun ij : Fin 3 × Fin 3 => max ‖(k : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊
        ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊) (Finset.mem_univ (i, j)))

private theorem norm_apply_le_matrixSize (k : GL (Fin 3) L) (i j : Fin 3) :
    ‖(k : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ matrixSize k := by
  unfold matrixSize
  have h1 : ‖(k : Matrix (Fin 3) (Fin 3) L) i j‖ ≤
      ‖(k : Matrix (Fin 3) (Fin 3) L) i j‖ + ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ :=
    le_add_of_nonneg_right (norm_nonneg _)
  refine h1.trans ?_
  refine le_trans ?_ (Finset.single_le_sum (f := fun i' : Fin 3 => ∑ j' : Fin 3,
    (‖(k : Matrix (Fin 3) (Fin 3) L) i' j'‖ + ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i' j'‖))
    (fun _ _ => Finset.sum_nonneg fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j' : Fin 3 =>
    ‖(k : Matrix (Fin 3) (Fin 3) L) i j'‖ + ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j'‖)
    (fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ j)

private theorem norm_inv_apply_le_matrixSize (k : GL (Fin 3) L) (i j : Fin 3) :
    ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ matrixSize k := by
  unfold matrixSize
  have h1 : ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ ≤
      ‖(k : Matrix (Fin 3) (Fin 3) L) i j‖ + ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ :=
    le_add_of_nonneg_left (norm_nonneg _)
  refine h1.trans ?_
  refine le_trans ?_ (Finset.single_le_sum (f := fun i' : Fin 3 => ∑ j' : Fin 3,
    (‖(k : Matrix (Fin 3) (Fin 3) L) i' j'‖ + ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i' j'‖))
    (fun _ _ => Finset.sum_nonneg fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j' : Fin 3 =>
    ‖(k : Matrix (Fin 3) (Fin 3) L) i j'‖ + ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j'‖)
    (fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ j)

private theorem norm_det_le_of_forall_le {A : Matrix (Fin 3) (Fin 3) L} {S : ℝ} (hS : 0 ≤ S)
    (h : ∀ i j, ‖A i j‖ ≤ S) : ‖A.det‖ ≤ 6 * S ^ 3 := by
  have hterm : ∀ i₁ j₁ i₂ j₂ i₃ j₃ : Fin 3, ‖A i₁ j₁ * A i₂ j₂ * A i₃ j₃‖ ≤ S ^ 3 := by
    intro i₁ j₁ i₂ j₂ i₃ j₃
    rw [norm_mul, norm_mul, pow_succ, pow_two]
    exact mul_le_mul (mul_le_mul (h _ _) (h _ _) (norm_nonneg _) hS) (h _ _) (norm_nonneg _)
      (mul_nonneg hS hS)
  rw [Matrix.det_fin_three]
  have e1 := hterm 0 0 1 1 2 2
  have e2 := hterm 0 0 1 2 2 1
  have e3 := hterm 0 1 1 0 2 2
  have e4 := hterm 0 1 1 2 2 0
  have e5 := hterm 0 2 1 0 2 1
  have e6 := hterm 0 2 1 1 2 0
  have t1 := norm_sub_le (A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1 - A 0 1 * A 1 0 * A 2 2
    + A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1) (A 0 2 * A 1 1 * A 2 0)
  have t2 := norm_add_le (A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1 - A 0 1 * A 1 0 * A 2 2
    + A 0 1 * A 1 2 * A 2 0) (A 0 2 * A 1 0 * A 2 1)
  have t3 := norm_add_le (A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1 - A 0 1 * A 1 0 * A 2 2)
    (A 0 1 * A 1 2 * A 2 0)
  have t4 := norm_sub_le (A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1) (A 0 1 * A 1 0 * A 2 2)
  have t5 := norm_sub_le (A 0 0 * A 1 1 * A 2 2) (A 0 0 * A 1 2 * A 2 1)
  linarith

private theorem nnnorm_det_le_of_forall_le [IsUltrametricDist L] {A : Matrix (Fin 3) (Fin 3) L} {s : ℝ≥0}
    (h : ∀ i j, ‖A i j‖₊ ≤ s) : ‖A.det‖₊ ≤ s ^ 3 := by
  have hterm : ∀ i₁ j₁ i₂ j₂ i₃ j₃ : Fin 3, ‖A i₁ j₁ * A i₂ j₂ * A i₃ j₃‖₊ ≤ s ^ 3 := by
    intro i₁ j₁ i₂ j₂ i₃ j₃
    rw [nnnorm_mul, nnnorm_mul, pow_succ, pow_two]
    exact mul_le_mul' (mul_le_mul' (h _ _) (h _ _)) (h _ _)
  have hadd : ∀ x y : L, ‖x‖₊ ≤ s ^ 3 → ‖y‖₊ ≤ s ^ 3 → ‖x + y‖₊ ≤ s ^ 3 := fun x y hx hy =>
    (IsUltrametricDist.nnnorm_add_le_max x y).trans (max_le hx hy)
  have hsub : ∀ x y : L, ‖x‖₊ ≤ s ^ 3 → ‖y‖₊ ≤ s ^ 3 → ‖x - y‖₊ ≤ s ^ 3 := fun x y hx hy => by
    rw [sub_eq_add_neg]
    exact hadd x (-y) hx (by rwa [nnnorm_neg])
  rw [Matrix.det_fin_three]
  exact hsub _ _ (hadd _ _ (hadd _ _ (hsub _ _ (hsub _ _ (hterm _ _ _ _ _ _) (hterm _ _ _ _ _ _))
    (hterm _ _ _ _ _ _)) (hterm _ _ _ _ _ _)) (hterm _ _ _ _ _ _)) (hterm _ _ _ _ _ _)

private theorem det_mul_det_inv (k : GL (Fin 3) L) :
    (k : Matrix (Fin 3) (Fin 3) L).det * ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).det = 1 := by
  rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]

private theorem norm_det_le_of_gl (k : GL (Fin 3) L) :
    ‖(k : Matrix (Fin 3) (Fin 3) L).det‖ ≤ 6 * matrixSize k ^ 3 :=
  norm_det_le_of_forall_le (matrixSize_nonneg k) (norm_apply_le_matrixSize k)

private theorem norm_det_inv_le_of_gl (k : GL (Fin 3) L) :
    ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).det‖ ≤ 6 * matrixSize k ^ 3 :=
  norm_det_le_of_forall_le (matrixSize_nonneg k) (norm_inv_apply_le_matrixSize k)

private theorem nnnorm_det_le_of_gl [IsUltrametricDist L] (k : GL (Fin 3) L) :
    ‖(k : Matrix (Fin 3) (Fin 3) L).det‖₊ ≤ matrixSupSize k ^ 3 :=
  nnnorm_det_le_of_forall_le (nnnorm_apply_le_matrixSupSize k)

private theorem nnnorm_det_inv_le_of_gl [IsUltrametricDist L] (k : GL (Fin 3) L) :
    ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).det‖₊ ≤ matrixSupSize k ^ 3 :=
  nnnorm_det_le_of_forall_le (nnnorm_inv_apply_le_matrixSupSize k)

private theorem one_le_matrixSupSize [IsUltrametricDist L] (k : GL (Fin 3) L) : 1 ≤ matrixSupSize k := by
  have h : (1 : ℝ≥0) ≤ matrixSupSize k ^ (3 + 3) := by
    rw [pow_add]
    have h1 : (1 : ℝ≥0) =
        ‖(k : Matrix (Fin 3) (Fin 3) L).det‖₊ * ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).det‖₊ := by
      rw [← nnnorm_mul, det_mul_det_inv, nnnorm_one]
    rw [h1]
    exact mul_le_mul' (nnnorm_det_le_of_gl k) (nnnorm_det_inv_le_of_gl k)
  exact (one_le_pow_iff_of_nonneg zero_le (by norm_num)).mp h

private theorem matrixSupSize_eq_one [IsUltrametricDist L] {k : GL (Fin 3) L}
    (h₁ : ∀ i j, ‖(k : Matrix (Fin 3) (Fin 3) L) i j‖₊ ≤ 1)
    (h₂ : ∀ i j, ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖₊ ≤ 1) : matrixSupSize k = 1 := by
  refine le_antisymm ?_ (one_le_matrixSupSize k)
  unfold matrixSupSize
  exact Finset.sup_le fun ij _ => max_le (h₁ ij.1 ij.2) (h₂ ij.1 ij.2)

private theorem nnnorm_det_eq_one_of_matrixSupSize_eq_one [IsUltrametricDist L] {k : GL (Fin 3) L}
    (hk : matrixSupSize k = 1) : ‖(k : Matrix (Fin 3) (Fin 3) L).det‖₊ = 1 := by
  have h1 : ‖(k : Matrix (Fin 3) (Fin 3) L).det‖₊ ≤ 1 := by simpa [hk] using nnnorm_det_le_of_gl k
  have h2 : ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).det‖₊ ≤ 1 := by
    simpa [hk] using nnnorm_det_inv_le_of_gl k
  refine le_antisymm h1 ?_
  have h3 : (1 : ℝ≥0) =
      ‖(k : Matrix (Fin 3) (Fin 3) L).det‖₊ * ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).det‖₊ := by
    rw [← nnnorm_mul, det_mul_det_inv, nnnorm_one]
  rw [h3]
  exact (mul_le_mul_right h2 _).trans (mul_one _).le

private theorem matrixSize_inv (k : GL (Fin 3) L) : matrixSize k⁻¹ = matrixSize k := by
  unfold matrixSize
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [inv_inv, add_comm]

private theorem matrixSupSize_inv (k : GL (Fin 3) L) : matrixSupSize k⁻¹ = matrixSupSize k := by
  unfold matrixSupSize
  refine Finset.sup_congr rfl fun ij _ => ?_
  rw [inv_inv, max_comm]

end NormedField

section Adelic

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "GA" => AdelicGL 3 (𝓞 ℚ) ℚ

private theorem coe_componentAt3_apply (v : HeightOneSpectrum (𝓞 ℚ)) (g : GA) (i j : Fin 3) :
    (componentAt3 (𝓞 ℚ) ℚ v g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j =
      ((g : Matrix (Fin 3) (Fin 3) 𝔸) i j).2 v := rfl

private theorem coe_det_componentAt3 (v : HeightOneSpectrum (𝓞 ℚ)) (g : GA) :
    (GeneralLinearGroup.det (componentAt3 (𝓞 ℚ) ℚ v g) : v.adicCompletion ℚ) =
      ((GeneralLinearGroup.det g : 𝔸ˣ) : 𝔸).2 v := by
  unfold componentAt3 componentAtN
  rw [GeneralLinearGroup.map_det]
  rfl

private theorem coe_det_archPlaceComponent3 (w : InfinitePlace ℚ) (g : GA) :
    (GeneralLinearGroup.det (archPlaceComponent3 ℚ w g) : w.Completion) =
      ((GeneralLinearGroup.det g : 𝔸ˣ) : 𝔸).1 w := by
  unfold archPlaceComponent3 archComponent3 archComponentN
  rw [MonoidHom.comp_apply, GeneralLinearGroup.map_det, GeneralLinearGroup.map_det]
  rfl

private theorem norm_det_fst_le (w : InfinitePlace ℚ) (g : GA) :
    ‖((GeneralLinearGroup.det g : 𝔸ˣ) : 𝔸).1 w‖ ≤ 6 * archGauge3 ℚ g ^ 3 := by
  rw [← coe_det_archPlaceComponent3, GeneralLinearGroup.val_det_apply]
  refine (norm_det_le_of_gl _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (matrixSize_nonneg _) ?_ 3)
    (by norm_num))
  unfold archGauge3
  have h : matrixSize (archPlaceComponent3 ℚ w g) ≤ ∑ w' : InfinitePlace ℚ, matrixSize (archPlaceComponent3 ℚ w' g) :=
    Finset.single_le_sum (f := fun w' : InfinitePlace ℚ => matrixSize (archPlaceComponent3 ℚ w' g))
      (fun _ _ => matrixSize_nonneg _) (Finset.mem_univ w)
  linarith

private def archDegree : ℕ := ∑ w : InfinitePlace ℚ, w.mult

private theorem prod_norm_det_fst_pow_mult_le (g : GA) :
    (∏ w : InfinitePlace ℚ, ‖((GeneralLinearGroup.det g : 𝔸ˣ) : 𝔸).1 w‖ ^ w.mult) ≤
      (6 * archGauge3 ℚ g ^ 3) ^ archDegree := by
  unfold archDegree
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun w _ => pow_nonneg (norm_nonneg _) _)
    (fun w _ => pow_le_pow_left₀ (norm_nonneg _) (norm_det_fst_le w g) _)

private theorem nnnorm_det_snd_le (v : HeightOneSpectrum (𝓞 ℚ)) (g : GA) :
    ‖((GeneralLinearGroup.det g : 𝔸ˣ) : 𝔸).2 v‖₊ ≤ matrixSupSize (componentAt3 (𝓞 ℚ) ℚ v g) ^ 3 := by
  haveI : IsUltrametricDist (v.adicCompletion ℚ) := inferInstance
  rw [← coe_det_componentAt3, GeneralLinearGroup.val_det_apply]
  exact nnnorm_det_le_of_gl _

private theorem norm_det_snd_le (v : HeightOneSpectrum (𝓞 ℚ)) (g : GA) :
    ‖((GeneralLinearGroup.det g : 𝔸ˣ) : 𝔸).2 v‖ ≤ ((matrixSupSize (componentAt3 (𝓞 ℚ) ℚ v g) : ℝ≥0) : ℝ) ^ 3 := by
  have h := nnnorm_det_snd_le v g
  exact_mod_cast h

private theorem eventually_componentAt3_mem_localMaximalCompact3 (g : GA) :
    ∀ᶠ v in Filter.cofinite, componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  have h1 : ∀ᶠ v in Filter.cofinite, ∀ i j : Fin 3,
      ((g : Matrix (Fin 3) (Fin 3) 𝔸) i j).2 v ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j =>
      RestrictedProduct.eventually _ _ ((g : Matrix (Fin 3) (Fin 3) 𝔸) i j).2
  have h2 : ∀ᶠ v in Filter.cofinite, ∀ i j : Fin 3,
      (((g⁻¹ : GA) : Matrix (Fin 3) (Fin 3) 𝔸) i j).2 v ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j =>
      RestrictedProduct.eventually _ _ (((g⁻¹ : GA) : Matrix (Fin 3) (Fin 3) 𝔸) i j).2
  filter_upwards [h1, h2] with v hv1 hv2
  refine (mem_localMaximalCompact3_iff (R := 𝓞 ℚ) (K := ℚ) (v := v)).mpr ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [coe_componentAt3_apply]
    exact hv1 i j
  · rw [← map_inv, coe_componentAt3_apply]
    exact hv2 i j

private theorem matrixSupSize_componentAt3_eq_one {v : HeightOneSpectrum (𝓞 ℚ)} {g : GA}
    (h : componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    matrixSupSize (componentAt3 (𝓞 ℚ) ℚ v g) = 1 := by
  haveI : IsUltrametricDist (v.adicCompletion ℚ) := inferInstance
  obtain ⟨h₁, h₂⟩ := (mem_localMaximalCompact3_iff (R := 𝓞 ℚ) (K := ℚ) (v := v)).mp h
  refine matrixSupSize_eq_one (fun i j => ?_) (fun i j => ?_)
  · have h' : ‖(componentAt3 (𝓞 ℚ) ℚ v g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j‖ ≤ 1 :=
      Valued.toNormedField.norm_le_one_iff.mpr (h₁ i j)
    exact_mod_cast h'
  · have h' : ‖(((componentAt3 (𝓞 ℚ) ℚ v g)⁻¹ : GL (Fin 3) (v.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j‖ ≤ 1 :=
      Valued.toNormedField.norm_le_one_iff.mpr (h₂ i j)
    exact_mod_cast h'

private def
    supFactor (g : GA) (v : HeightOneSpectrum (𝓞 ℚ)) : ℝ := ((matrixSupSize (componentAt3 (𝓞 ℚ) ℚ v g) : ℝ≥0) : ℝ)

private theorem finGauge3_eq_finprod_supFactor (g : GA) : finGauge3 ℚ g = ∏ᶠ v, supFactor g v := rfl

private theorem one_le_supFactor (g : GA) (v : HeightOneSpectrum (𝓞 ℚ)) : 1 ≤ supFactor g v := by
  haveI : IsUltrametricDist (v.adicCompletion ℚ) := inferInstance
  have h := one_le_matrixSupSize (componentAt3 (𝓞 ℚ) ℚ v g)
  unfold supFactor
  exact_mod_cast h

private theorem mulSupport_supFactor_finite (g : GA) : (Function.mulSupport (supFactor g)).Finite := by
  refine (Filter.eventually_cofinite.mp (eventually_componentAt3_mem_localMaximalCompact3 g)).subset
    fun v hv hmem => hv ?_
  unfold supFactor
  rw [matrixSupSize_componentAt3_eq_one hmem, NNReal.coe_one]

private theorem
    norm_det_snd_eq_one_of_supFactor_eq_one {g : GA} {v : HeightOneSpectrum (𝓞 ℚ)} (hv : supFactor g v = 1) :
    ‖((GeneralLinearGroup.det g : 𝔸ˣ) : 𝔸).2 v‖ = 1 := by
  haveI : IsUltrametricDist (v.adicCompletion ℚ) := inferInstance
  have h1 : matrixSupSize (componentAt3 (𝓞 ℚ) ℚ v g) = 1 := by
    unfold supFactor at hv
    exact_mod_cast hv
  have h2 := nnnorm_det_eq_one_of_matrixSupSize_eq_one h1
  rw [← GeneralLinearGroup.val_det_apply, coe_det_componentAt3] at h2
  rw [← coe_nnnorm, h2, NNReal.coe_one]

private theorem mulSupport_norm_det_snd_subset (g : GA) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 ℚ) => ‖((GeneralLinearGroup.det g : 𝔸ˣ) : 𝔸).2 v‖) ⊆
      Function.mulSupport (supFactor g) := by
  intro v hv
  rw [Function.mem_mulSupport] at hv ⊢
  intro h1
  exact hv (norm_det_snd_eq_one_of_supFactor_eq_one h1)

private theorem one_le_finGauge3 (g : GA) : 1 ≤ finGauge3 ℚ g := by
  have hfin := mulSupport_supFactor_finite g
  rw [finGauge3_eq_finprod_supFactor,
    finprod_eq_prod_of_mulSupport_subset _ (s := hfin.toFinset) fun v hv => hfin.mem_toFinset.mpr hv]
  refine le_trans (le_of_eq (Finset.prod_const_one (s := hfin.toFinset)).symm) ?_
  exact Finset.prod_le_prod (fun _ _ => zero_le_one) (fun v _ => one_le_supFactor g v)

private theorem finprod_norm_det_snd_le (g : GA) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), ‖((GeneralLinearGroup.det g : 𝔸ˣ) : 𝔸).2 v‖) ≤ finGauge3 ℚ g ^ 3 := by
  have hfin := mulSupport_supFactor_finite g
  rw [finGauge3_eq_finprod_supFactor, finprod_pow hfin,
    finprod_eq_prod_of_mulSupport_subset _ (s := hfin.toFinset)
      (fun v hv => hfin.mem_toFinset.mpr (mulSupport_norm_det_snd_subset g hv)),
    finprod_eq_prod_of_mulSupport_subset _ (s := hfin.toFinset)
      (fun v hv => hfin.mem_toFinset.mpr (Function.mulSupport_pow (supFactor g) 3 hv))]
  exact Finset.prod_le_prod (fun v _ => norm_nonneg _) (fun v _ => norm_det_snd_le v g)

private theorem ideleNorm_det_le (g : GA) :
    ideleNorm ℚ (GeneralLinearGroup.det g) ≤ 6 ^ archDegree * gauge3 ℚ g ^ (3 * archDegree + 3) := by
  have hfac := NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm ℚ
    (GeneralLinearGroup.det g)
  have hA1 : 1 ≤ archGauge3 ℚ g := one_le_archGauge3 ℚ g
  have hA0 : 0 ≤ archGauge3 ℚ g := zero_le_one.trans hA1
  have hF1 : 1 ≤ finGauge3 ℚ g := one_le_finGauge3 g
  have hF0 : 0 ≤ finGauge3 ℚ g := zero_le_one.trans hF1
  have hG : archGauge3 ℚ g * finGauge3 ℚ g ≤ gauge3 ℚ g := le_max_right _ _
  have hAG : archGauge3 ℚ g ≤ gauge3 ℚ g := (le_mul_of_one_le_right hA0 hF1).trans hG
  have hFG : finGauge3 ℚ g ≤ gauge3 ℚ g := (le_mul_of_one_le_left hF0 hA1).trans hG
  have hG0 : 0 ≤ gauge3 ℚ g := zero_le_one.trans (one_le_gauge3 ℚ g)
  have h6A : 0 ≤ 6 * archGauge3 ℚ g ^ 3 := mul_nonneg (by norm_num) (pow_nonneg hA0 3)
  have h6G : 0 ≤ 6 * gauge3 ℚ g ^ 3 := mul_nonneg (by norm_num) (pow_nonneg hG0 3)
  calc ideleNorm ℚ (GeneralLinearGroup.det g)
      = (∏ w : InfinitePlace ℚ, ‖((GeneralLinearGroup.det g : 𝔸ˣ) : 𝔸).1 w‖ ^ w.mult) *
          ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), ‖((GeneralLinearGroup.det g : 𝔸ˣ) : 𝔸).2 v‖ := hfac
    _ ≤ (6 * archGauge3 ℚ g ^ 3) ^ archDegree * finGauge3 ℚ g ^ 3 :=
        mul_le_mul (prod_norm_det_fst_pow_mult_le g) (finprod_norm_det_snd_le g)
          (finprod_nonneg fun _ => norm_nonneg _) (pow_nonneg h6A _)
    _ ≤ (6 * gauge3 ℚ g ^ 3) ^ archDegree * gauge3 ℚ g ^ 3 :=
        mul_le_mul
          (pow_le_pow_left₀ h6A (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA0 hAG 3) (by norm_num)) _)
          (pow_le_pow_left₀ hF0 hFG 3) (pow_nonneg hF0 3) (pow_nonneg h6G _)
    _ = 6 ^ archDegree * gauge3 ℚ g ^ (3 * archDegree + 3) := by ring1

private theorem ideleNorm_one' : ideleNorm ℚ (1 : 𝔸ˣ) = 1 := by
  unfold ideleNorm
  rw [map_one, NNReal.coe_one]

private theorem ideleNorm_inv (x : 𝔸ˣ) : ideleNorm ℚ x⁻¹ = (ideleNorm ℚ x)⁻¹ := by
  refine (inv_eq_of_mul_eq_one_right ?_).symm
  rw [← ideleNorm_mul, mul_inv_cancel, ideleNorm_one']

private theorem ideleNorm_det_inv (g : GA) :
    ideleNorm ℚ (GeneralLinearGroup.det g⁻¹) = (ideleNorm ℚ (GeneralLinearGroup.det g))⁻¹ := by
  rw [map_inv, ideleNorm_inv]

private theorem gauge3_inv (g : GA) : gauge3 ℚ g⁻¹ = gauge3 ℚ g := by
  simp only [gauge3, archGauge3, finGauge3, map_inv, matrixSize_inv, matrixSupSize_inv]

private theorem rpow_le_of_le_mul_pow {n C H : ℝ} {N : ℕ} (hn : 0 ≤ n) (hC : 0 ≤ C) (hH : 1 ≤ H) (h : n ≤ C * H ^ N)
    {t : ℝ} (ht : 0 ≤ t) : n ^ t ≤ C ^ t * H ^ ⌈(N : ℝ) * t⌉₊ := by
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  calc n ^ t ≤ (C * H ^ N) ^ t := Real.rpow_le_rpow hn h ht
    _ = C ^ t * (H ^ N) ^ t := Real.mul_rpow hC (pow_nonneg hH0 N)
    _ = C ^ t * H ^ ((N : ℝ) * t) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hH0]
    _ ≤ C ^ t * H ^ ((⌈(N : ℝ) * t⌉₊ : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hH (Nat.le_ceil _)) (Real.rpow_nonneg hC t)
    _ = C ^ t * H ^ ⌈(N : ℝ) * t⌉₊ := by rw [Real.rpow_natCast]

private theorem exists_forall_ideleNorm_det_rpow_le (t : ℝ) :
    ∃ (D : ℝ) (M : ℕ), 0 ≤ D ∧ ∀ g : GA, ideleNorm ℚ (GeneralLinearGroup.det g) ^ t ≤ D * gauge3 ℚ g ^ M := by
  have h6 : (0 : ℝ) ≤ 6 ^ archDegree := pow_nonneg (by norm_num) _
  rcases le_or_gt 0 t with ht | ht
  · refine ⟨((6 : ℝ) ^ archDegree) ^ t, ⌈((3 * archDegree + 3 : ℕ) : ℝ) * t⌉₊, Real.rpow_nonneg h6 t,
      fun g => ?_⟩
    exact rpow_le_of_le_mul_pow (ideleNorm_pos _).le h6 (one_le_gauge3 ℚ g) (ideleNorm_det_le g) ht
  · refine ⟨((6 : ℝ) ^ archDegree) ^ (-t), ⌈((3 * archDegree + 3 : ℕ) : ℝ) * (-t)⌉₊, Real.rpow_nonneg h6 _,
      fun g => ?_⟩
    have h1 : ideleNorm ℚ (GeneralLinearGroup.det g) ^ t = ideleNorm ℚ (GeneralLinearGroup.det g⁻¹) ^ (-t) := by
      rw [ideleNorm_det_inv, Real.inv_rpow (ideleNorm_pos _).le, ← Real.rpow_neg (ideleNorm_pos _).le, neg_neg]
    have h2 := rpow_le_of_le_mul_pow (ideleNorm_pos _).le h6 (one_le_gauge3 ℚ g⁻¹) (ideleNorm_det_le g⁻¹)
      (neg_nonneg.mpr ht.le)
    rw [h1, ← gauge3_inv g]
    exact h2

end Adelic

section Growth

private theorem exists_nonneg_of_isModerateGrowth3 {Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hΦ : IsModerateGrowth3 ℚ Φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ g, ‖Φ g‖ ≤ C * gauge3 ℚ g ^ N := by
  obtain ⟨C, N, hb⟩ := hΦ
  refine ⟨max C 0, le_max_right _ _, N, fun g => (hb g (Set.mem_univ g)).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (zero_le_one.trans (one_le_gauge3 ℚ g)) N)

private theorem isModerateGrowth3_of_bound {Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} {C : ℝ} {N : ℕ}
    (hb : ∀ g, ‖Φ g‖ ≤ C * gauge3 ℚ g ^ N) : IsModerateGrowth3 ℚ Φ :=
  ⟨C, N, fun g _ => hb g⟩

private theorem isModerateGrowth3_ideleNorm_det_rpow_mul {f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hf : IsModerateGrowth3 ℚ f)
    (t : ℝ) : IsModerateGrowth3 ℚ fun g =>
      ((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ t : ℝ) : ℂ) * f g := by
  obtain ⟨C, hC0, N, hC⟩ := exists_nonneg_of_isModerateGrowth3 hf
  obtain ⟨D, M, hD0, hD⟩ := exists_forall_ideleNorm_det_rpow_le t
  refine isModerateGrowth3_of_bound (C := D * C) (N := M + N) fun g => ?_
  have hG0 : 0 ≤ gauge3 ℚ g := zero_le_one.trans (one_le_gauge3 ℚ g)
  show ‖((ideleNorm ℚ (GeneralLinearGroup.det g) ^ t : ℝ) : ℂ) * f g‖ ≤ D * C * gauge3 ℚ g ^ (M + N)
  rw [norm_mul, Complex.norm_of_nonneg (Real.rpow_pos_of_pos (ideleNorm_pos _) t).le, pow_add]
  calc ideleNorm ℚ (GeneralLinearGroup.det g) ^ t * ‖f g‖ ≤ (D * gauge3 ℚ g ^ M) * (C * gauge3 ℚ g ^ N) :=
        mul_le_mul (hD g) (hC g) (norm_nonneg _) (mul_nonneg hD0 (pow_nonneg hG0 M))
    _ = D * C * (gauge3 ℚ g ^ M * gauge3 ℚ g ^ N) := by ring1

end Growth

section Embedded

local notation "GA" => AdelicGL 3 (𝓞 ℚ) ℚ
local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

private theorem mapMatrix_comp_apply {R S T : Type*} [Semiring R] [Semiring S] [Semiring T] (f : S →+* T) (g : R →+* S)
    (M : Matrix (Fin 3) (Fin 3) R) : (f.comp g).mapMatrix M = f.mapMatrix (g.mapMatrix M) := by
  ext i j
  rfl

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem coe_localToAdelic3 (k : LocalGL3 v) :
    ((localToAdelic3 v k : GA) : Matrix (Fin 3) (Fin 3) 𝔸) =
      finMatN (Fin 3) (𝓞 ℚ) ℚ
        (localMatN (Fin 3) (𝓞 ℚ) ℚ v (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) := rfl

private theorem
    _root_.LanglandsTunnell.CubicInduction.DeterminantGauge.componentAt3_localToAdelic3_self (k : LocalGL3 v) : componentAt3 (𝓞 ℚ) ℚ v (localToAdelic3 v k) = k := by
  apply Units.ext
  show ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)).mapMatrix
      ((localToAdelic3 v k : GA) : Matrix (Fin 3) (Fin 3) 𝔸) = (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
  rw [coe_localToAdelic3, mapMatrix_comp_apply, mapMatrix_fin_finMatN, mapMatrix_localMatN_self]

p2m_export "LanglandsTunnell.CubicInduction.DeterminantGauge" "componentAt3_localToAdelic3_self"
private theorem _root_.LanglandsTunnell.CubicInduction.DeterminantGauge.componentAt3_localToAdelic3_of_ne (k : LocalGL3 v) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) :
    componentAt3 (𝓞 ℚ) ℚ w (localToAdelic3 v k) = 1 := by
  apply Units.ext
  rw [Units.val_one]
  show ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)).mapMatrix
      ((localToAdelic3 v k : GA) : Matrix (Fin 3) (Fin 3) 𝔸) = 1
  rw [coe_localToAdelic3, mapMatrix_comp_apply, mapMatrix_fin_finMatN,
    mapMatrix_localMatN_of_ne (Fin 3) (𝓞 ℚ) ℚ v _ hw]

p2m_export "LanglandsTunnell.CubicInduction.DeterminantGauge" "componentAt3_localToAdelic3_of_ne"
private theorem _root_.LanglandsTunnell.CubicInduction.DeterminantGauge.archComponent3_localToAdelic3 (k : LocalGL3 v) : archComponent3 (𝓞 ℚ) ℚ (localToAdelic3 v k) = 1 := by
  apply Units.ext
  rw [Units.val_one]
  show (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix ((localToAdelic3 v k : GA) : Matrix (Fin 3) (Fin 3) 𝔸) = 1
  rw [coe_localToAdelic3, mapMatrix_arch_finMatN]

p2m_export "LanglandsTunnell.CubicInduction.DeterminantGauge" "archComponent3_localToAdelic3"
private theorem archPlaceComponent3_localToAdelic3 (w : InfinitePlace ℚ) (k : LocalGL3 v) :
    archPlaceComponent3 ℚ w (localToAdelic3 v k) = 1 := by
  show GeneralLinearGroup.map (AdelicLevel.archEval ℚ w) (archComponent3 (𝓞 ℚ) ℚ (localToAdelic3 v k)) = 1
  rw [archComponent3_localToAdelic3]
  exact (GeneralLinearGroup.map (AdelicLevel.archEval ℚ w)).map_one

private theorem ideleNorm_det_localToAdelic3_eq (k : LocalGL3 v) :
    ideleNorm ℚ (GeneralLinearGroup.det (localToAdelic3 v k)) =
      ‖((GeneralLinearGroup.det (localToAdelic3 v k) : 𝔸ˣ) : 𝔸).2 v‖ := by
  have h1 : ∀ w : InfinitePlace ℚ,
      ‖((GeneralLinearGroup.det (localToAdelic3 v k) : 𝔸ˣ) : 𝔸).1 w‖ ^ w.mult = 1 := fun w => by
    rw [← coe_det_archPlaceComponent3, archPlaceComponent3_localToAdelic3, map_one, Units.val_one, norm_one, one_pow]
  have h2 : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      ‖((GeneralLinearGroup.det (localToAdelic3 v k) : 𝔸ˣ) : 𝔸).2 w‖ = 1 := fun w hw => by
    rw [← coe_det_componentAt3, componentAt3_localToAdelic3_of_ne v k hw, map_one, Units.val_one, norm_one]
  unfold ideleNorm
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm ℚ, Fintype.prod_eq_one _ h1,
    finprod_eq_single _ v h2, one_mul]

private theorem ideleNorm_det_localToAdelic3_le_one {k : LocalGL3 v} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    ideleNorm ℚ (GeneralLinearGroup.det (localToAdelic3 v k)) ≤ 1 := by
  have hmem : componentAt3 (𝓞 ℚ) ℚ v (localToAdelic3 v k) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
    rw [componentAt3_localToAdelic3_self]
    exact hk
  have h := norm_det_snd_le v (localToAdelic3 v k)
  rw [matrixSupSize_componentAt3_eq_one hmem, NNReal.coe_one, one_pow] at h
  rw [ideleNorm_det_localToAdelic3_eq]
  exact h

private theorem ideleNorm_det_localToAdelic3_of_mem {k : LocalGL3 v} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    ideleNorm ℚ (GeneralLinearGroup.det (localToAdelic3 v k)) = 1 := by
  have h1 := ideleNorm_det_localToAdelic3_le_one v hk
  have h2 := ideleNorm_det_localToAdelic3_le_one v ((localMaximalCompact3 (𝓞 ℚ) ℚ v).inv_mem hk)
  rw [map_inv, ideleNorm_det_inv] at h2
  exact le_antisymm h1 ((inv_le_one₀ (ideleNorm_pos _)).mp h2)

private theorem isOpen_localMaximalCompact3 :
    IsOpen ((localMaximalCompact3 (𝓞 ℚ) ℚ v : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) := by
  have hO : IsOpen {x : v.adicCompletion ℚ | Valued.v x ≤ 1} := Valued.isOpen_integer (v.adicCompletion ℚ)
  show IsOpen {k : LocalGL3 v | (∀ i j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ 1) ∧
    (∀ i j, Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ 1)}
  simp only [Set.setOf_and, Set.setOf_forall]
  refine IsOpen.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
  · exact hO.preimage (Units.continuous_val.matrix_elem i j)
  · exact hO.preimage (Units.continuous_coe_inv.matrix_elem i j)

private theorem continuous_det3 : Continuous fun g : GA => GeneralLinearGroup.det g := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun g : GA => Matrix.det (g : Matrix (Fin 3) (Fin 3) 𝔸)
    exact Units.continuous_val.matrix_det
  · show Continuous fun g : GA => Matrix.det ((g⁻¹ : GA) : Matrix (Fin 3) (Fin 3) 𝔸)
    exact Units.continuous_coe_inv.matrix_det

private theorem continuous_ideleNorm_det3 : Continuous fun g : GA => ideleNorm ℚ (GeneralLinearGroup.det g) :=
  (NumberField.TateGlobal.continuous_ideleNorm ℚ).comp continuous_det3

private theorem det_radicalP21 (x : Fin 2 → 𝔸) : GeneralLinearGroup.det (radicalP21 x) = 1 :=
  Units.ext (by simp [radicalP21, Matrix.det_fin_three])

private theorem det_radicalP12 (x : Fin 2 → 𝔸) : GeneralLinearGroup.det (radicalP12 x) = 1 :=
  Units.ext (by simp [radicalP12, Matrix.det_fin_three])

end Embedded

section Twist

local notation "GA" => AdelicGL 3 (𝓞 ℚ) ℚ
local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

private theorem twist_mul {t : ℝ} (g h : GA) :
    ((ideleNorm ℚ (GeneralLinearGroup.det (g * h)) ^ t : ℝ) : ℂ) =
      ((ideleNorm ℚ (GeneralLinearGroup.det g) ^ t : ℝ) : ℂ) *
        ((ideleNorm ℚ (GeneralLinearGroup.det h) ^ t : ℝ) : ℂ) := by
  rw [map_mul, ideleNorm_mul, Real.mul_rpow (ideleNorm_pos _).le (ideleNorm_pos _).le, Complex.ofReal_mul]

private theorem twist_eq_one {t : ℝ} {u : GA} (hu : ideleNorm ℚ (GeneralLinearGroup.det u) = 1) :
    ((ideleNorm ℚ (GeneralLinearGroup.det u) ^ t : ℝ) : ℂ) = 1 := by
  rw [hu, Real.one_rpow, Complex.ofReal_one]

private theorem twist_localToAdelic3 {t : ℝ} (p : HeightOneSpectrum (𝓞 ℚ)) {k : LocalGL3 p}
    (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    ((ideleNorm ℚ (GeneralLinearGroup.det (localToAdelic3 p k)) ^ t : ℝ) : ℂ) = 1 :=
  twist_eq_one (ideleNorm_det_localToAdelic3_of_mem p hk)

private theorem twist_of_mem_map {t : ℝ} (p : HeightOneSpectrum (𝓞 ℚ)) {u : GA}
    (hu : u ∈ (localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) :
    ((ideleNorm ℚ (GeneralLinearGroup.det u) ^ t : ℝ) : ℂ) = 1 := by
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hu
  exact twist_localToAdelic3 p hk

private theorem twist_radicalP21 {t : ℝ} (x : Fin 2 → 𝔸) :
    ((ideleNorm ℚ (GeneralLinearGroup.det (radicalP21 x)) ^ t : ℝ) : ℂ) = 1 :=
  twist_eq_one (by rw [det_radicalP21, ideleNorm_one'])

private theorem twist_radicalP12 {t : ℝ} (x : Fin 2 → 𝔸) :
    ((ideleNorm ℚ (GeneralLinearGroup.det (radicalP12 x)) ^ t : ℝ) : ℂ) = 1 :=
  twist_eq_one (by rw [det_radicalP12, ideleNorm_one'])

section Generic

variable {G : Type*} [Group G]

private theorem isRightInvariant_mul_of_forall_eq_one {U : Subgroup G} {W : G → ℂ} (χ : G → ℂ)
    (hχ : ∀ a b, χ (a * b) = χ a * χ b) (hU : ∀ u ∈ U, χ u = 1) (hW : IsRightInvariant U W) :
    IsRightInvariant U fun g => χ g * W g := by
  intro g u hu
  show χ (g * u) * W (g * u) = χ g * W g
  rw [hχ, hU u hu, mul_one, hW g u hu]

private theorem isCosetEigenfunction_mul_of_forall_eq_one {U : Subgroup G} {gen : G} {W : G → ℂ} {lam : ℂ} (χ : G → ℂ)
    (hχ : ∀ a b, χ (a * b) = χ a * χ b) (hU : ∀ u ∈ U, χ u = 1) (hW : IsCosetEigenfunction U gen W lam) :
    IsCosetEigenfunction U gen (fun g => χ g * W g) (χ gen * lam) := by
  intro ι _ reps hreps g
  have hrep : ∀ i, χ (reps i) = χ gen := fun i => by
    obtain ⟨u, hu, u', hu', huu'⟩ := HeckePair.mem_doubleCoset_iff.mp (hreps.mem_doubleCoset i)
    rw [← huu', hχ, hχ, hU u hu, hU u' hu', one_mul, mul_one]
  have hsum : (∑ i, W (g * reps i)) = lam * W g := hW ι reps hreps g
  show (∑ i, χ (g * reps i) * W (g * reps i)) = χ gen * lam * (χ g * W g)
  simp only [hχ, hrep]
  rw [← Finset.mul_sum, hsum]
  ring1

end Generic

variable {f : GA → ℂ}

private theorem continuous_twist_mul (t : ℝ) (hf : Continuous f) :
    Continuous fun g : GA => ((ideleNorm ℚ (GeneralLinearGroup.det g) ^ t : ℝ) : ℂ) * f g :=
  (Complex.continuous_ofReal.comp
    (continuous_ideleNorm_det3.rpow_const fun g => Or.inl (ideleNorm_pos (GeneralLinearGroup.det g)).ne')).mul hf

private theorem
    isCuspidalAlongP21_twist_mul (t : ℝ) (pins : AutomorphicForm.CarrierPins ℚ) (hf : IsCuspidalAlongP21 pins f) :
    IsCuspidalAlongP21 pins fun g => ((ideleNorm ℚ (GeneralLinearGroup.det g) ^ t : ℝ) : ℂ) * f g := by
  intro g
  have hg := hf g
  simp only [twist_mul, twist_radicalP21, one_mul, MeasureTheory.integral_const_mul]
  rw [hg, mul_zero]

private theorem
    isCuspidalAlongP12_twist_mul (t : ℝ) (pins : AutomorphicForm.CarrierPins ℚ) (hf : IsCuspidalAlongP12 pins f) :
    IsCuspidalAlongP12 pins fun g => ((ideleNorm ℚ (GeneralLinearGroup.det g) ^ t : ℝ) : ℂ) * f g := by
  intro g
  have hg := hf g
  simp only [twist_mul, twist_radicalP12, one_mul, MeasureTheory.integral_const_mul]
  rw [hg, mul_zero]

private theorem isRightInvariant_twist_mul (t : ℝ) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hf : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f) :
    ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      fun g => ((ideleNorm ℚ (GeneralLinearGroup.det g) ^ t : ℝ) : ℂ) * f g :=
  fun p hp => isRightInvariant_mul_of_forall_eq_one (fun g => ((ideleNorm ℚ (GeneralLinearGroup.det g) ^ t : ℝ) : ℂ))
    (fun a b => twist_mul a b) (fun _ hu => twist_of_mem_map p hu) (hf p hp)

private theorem isCosetEigenfunction_twist_mul (t : ℝ) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (gen : (p : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 p) (lam : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (hf : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (gen p)) f (lam p)) :
    ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (gen p)) (fun g => ((ideleNorm ℚ (GeneralLinearGroup.det g) ^ t : ℝ) : ℂ) * f g)
      (((ideleNorm ℚ (GeneralLinearGroup.det (localToAdelic3 p (gen p))) ^ t : ℝ) : ℂ) * lam p) :=
  fun p hp => isCosetEigenfunction_mul_of_forall_eq_one
    (fun g => ((ideleNorm ℚ (GeneralLinearGroup.det g) ^ t : ℝ) : ℂ)) (fun a b => twist_mul a b)
    (fun _ hu => twist_of_mem_map p hu) (hf p hp)

private theorem exists_isOpen_twist_mul (t : ℝ) (v : HeightOneSpectrum (𝓞 ℚ))
    (hf : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : GA, f (g * localToAdelic3 v k) = f g) :
    ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : GA,
      ((ideleNorm ℚ (GeneralLinearGroup.det (g * localToAdelic3 v k)) ^ t : ℝ) : ℂ) * f (g * localToAdelic3 v k) =
        ((ideleNorm ℚ (GeneralLinearGroup.det g) ^ t : ℝ) : ℂ) * f g := by
  obtain ⟨Uv, hU, hinv⟩ := hf
  refine ⟨Uv ⊓ localMaximalCompact3 (𝓞 ℚ) ℚ v, ?_, fun k hk g => ?_⟩
  · rw [Subgroup.coe_inf]
    exact hU.inter (isOpen_localMaximalCompact3 v)
  · obtain ⟨hkU, hkK⟩ := Subgroup.mem_inf.mp hk
    rw [twist_mul, twist_localToAdelic3 v hkK, mul_one, hinv k hkU g]

end Twist

end DeterminantGauge

end LanglandsTunnell.CubicInduction

end

end DeterminantGaugeBlock

noncomputable section

open NumberField NumberField.TateGlobal IsDedekindDomain
open scoped NNReal

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.AdelicGL CubicInduction.globalPointsGL"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "SlabL2.realCoordinate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 LocalGL3 heckeGen1 heckeGen2 cosetSum IsCosetEigenfunction IsRightInvariant archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 one_le_gauge3 one_le_archGauge3 IsModerateGrowth3 matrixFin_ext matrixAdele_ext localMatN localMatN_apply_self localMatN_apply_of_ne mapMatrix_localMatN_self mapMatrix_localMatN_of_ne localEmbedN finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN finEmbedN localToAdelic3 exists_mul_eq_unipotent_mul_diagonal_mul_compact smoothingOperator_mem_cuspFunctions_of_isCuspidalAlong exists_isCompactOperator_cuspidalSubspace_smoothingOperator exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous exists_inner_toL2_translateRight_ne_zero_of_isCosetEigenfunction measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator"
p2m_open "LanglandsTunnell.CubicInduction~isCompact_localMaximalCompact3~det_radicalP21~det_radicalP12 LanglandsTunnell~CubicInduction.isCompact_localMaximalCompact3"

namespace NormSection

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

private theorem isReal_of_rat (w : InfinitePlace ℚ) : w.IsReal := by
  rw [Subsingleton.elim w Rat.infinitePlace]
  exact Rat.isReal_infinitePlace

private def ofRealAdele (r : ℝ) : InfiniteAdeleRing ℚ :=
  show (v : InfinitePlace ℚ) → v.Completion from
    fun v => (InfinitePlace.Completion.isometryEquivRealOfIsReal (isReal_of_rat v)).symm r

private theorem continuous_ofRealAdele : Continuous ofRealAdele :=
  continuous_pi fun v => (InfinitePlace.Completion.isometryEquivRealOfIsReal (isReal_of_rat v)).symm.continuous

private theorem ofRealAdele_apply (r : ℝ) (v : InfinitePlace ℚ) :
    ofRealAdele r v = (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_of_rat v)).symm r := rfl

private theorem extensionEmbeddingOfIsReal_ofRealAdele (r : ℝ) (v : InfinitePlace ℚ) :
    InfinitePlace.Completion.extensionEmbeddingOfIsReal (isReal_of_rat v) (ofRealAdele r v) = r :=
  (InfinitePlace.Completion.isometryEquivRealOfIsReal (isReal_of_rat v)).apply_symm_apply r

private theorem norm_ofRealAdele_apply (r : ℝ) (v : InfinitePlace ℚ) : ‖ofRealAdele r v‖ = |r| := by
  rw [← dist_zero_right,
    ← (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (isReal_of_rat v)).dist_eq, map_zero,
    dist_zero_right, extensionEmbeddingOfIsReal_ofRealAdele, Real.norm_eq_abs]

private theorem ofRealAdele_mul (a b : ℝ) : ofRealAdele a * ofRealAdele b = ofRealAdele (a * b) := by
  funext v
  show ofRealAdele a v * ofRealAdele b v = ofRealAdele (a * b) v
  rw [ofRealAdele_apply, ofRealAdele_apply, ofRealAdele_apply]
  exact (RingEquiv.map_mul _ a b).symm

private theorem ofRealAdele_one : ofRealAdele 1 = 1 := by
  funext v
  show ofRealAdele 1 v = 1
  rw [ofRealAdele_apply]
  exact RingEquiv.map_one _

private def archHom : ℝ →* InfiniteAdeleRing ℚ where
  toFun := ofRealAdele
  map_one' := ofRealAdele_one
  map_mul' a b := (ofRealAdele_mul a b).symm

private def archMul : ℝ →* 𝔸 := archHom.prod 1

private theorem archMul_apply (x : ℝ) : archMul x = ((ofRealAdele x, (1 : 𝔸f)) : InfiniteAdeleRing ℚ × 𝔸f) := rfl

private theorem continuous_archMul : Continuous archMul := by
  show Continuous fun x : ℝ => ((ofRealAdele x, (1 : 𝔸f)) : InfiniteAdeleRing ℚ × 𝔸f)
  exact continuous_ofRealAdele.prodMk continuous_const

private def posPart (r : ℝ) : ℝ := Real.exp (Real.log r)

private theorem posPart_pos (r : ℝ) : 0 < posPart r := Real.exp_pos _

private theorem posPart_of_pos {r : ℝ} (hr : 0 < r) : posPart r = r := Real.exp_log hr

private theorem continuousOn_posPart : ContinuousOn posPart (Set.Ioi 0) :=
  Real.continuous_exp.comp_continuousOn (Real.continuousOn_log.mono fun _ hx => ne_of_gt hx)

private def archIdele (r : ℝ) : 𝔸ˣ := Units.map archMul (Units.mk0 (posPart r) (posPart_pos r).ne')

private theorem archIdele_val_fst (r : ℝ) : ((archIdele r : 𝔸ˣ) : 𝔸).1 = ofRealAdele (posPart r) := rfl

private theorem archIdele_val_snd (r : ℝ) : ((archIdele r : 𝔸ˣ) : 𝔸).2 = 1 := rfl

private theorem norm_one_finiteAdele_apply (v : HeightOneSpectrum (𝓞 ℚ)) : ‖(1 : 𝔸f) v‖ = 1 := by
  show ‖(1 : v.adicCompletion ℚ)‖ = 1
  exact norm_one

private theorem prod_norm_archIdele (r : ℝ) :
    (∏ w : InfinitePlace ℚ, ‖((archIdele r : 𝔸ˣ) : 𝔸).1 w‖ ^ w.mult)
      * ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), ‖((archIdele r : 𝔸ˣ) : 𝔸).2 v‖ = posPart r := by
  rw [Fintype.prod_unique, archIdele_val_fst, archIdele_val_snd, norm_ofRealAdele_apply, abs_of_pos (posPart_pos r),
    InfinitePlace.mult, if_pos (isReal_of_rat _), pow_one]
  simp only [norm_one_finiteAdele_apply, finprod_one, mul_one]

private theorem continuousOn_archIdele : ContinuousOn archIdele (Set.Ioi 0) := by
  rw [continuousOn_iff_continuous_restrict]
  have hp : Continuous fun x : Set.Ioi (0 : ℝ) => posPart x :=
    continuousOn_iff_continuous_restrict.mp continuousOn_posPart
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun x : Set.Ioi (0 : ℝ) => archMul (posPart x)
    exact continuous_archMul.comp hp
  · show Continuous fun x : Set.Ioi (0 : ℝ) => archMul (posPart x)⁻¹
    exact continuous_archMul.comp (hp.inv₀ fun x => (posPart_pos x).ne')

private theorem ideleNorm_archIdele (r : ℝ) : ideleNorm ℚ (archIdele r) = posPart r := by
  show ((MeasureTheory.distribHaarChar 𝔸 (archIdele r) : ℝ≥0) : ℝ) = posPart r
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm ℚ (archIdele r),
    prod_norm_archIdele]

private theorem exists_ideleNorm_section :
    ∃ s : ℝ → (AdeleRing (𝓞 ℚ) ℚ)ˣ, (∀ r, 0 < r → ideleNorm ℚ (s r) = r) ∧ ContinuousOn s (Set.Ioi 0) :=
  ⟨archIdele, fun _ hr => by rw [ideleNorm_archIdele, posPart_of_pos hr], continuousOn_archIdele⟩

end NormSection

end LanglandsTunnell.CubicInduction

end

section DomainsAndSlab

open MeasureTheory
open scoped Pointwise

namespace ProperlyDiscontinuousFundamentalDomain

variable {Γ X : Type*} [Group Γ] [TopologicalSpace X] [T2Space X] [MulAction Γ X] [ContinuousConstSMul Γ X]

private theorem exists_isOpen_smul_notMem [LocallyCompactSpace X] [ProperlyDiscontinuousSMul Γ X]
    (hfree : ∀ (γ : Γ) (x : X), γ • x = x → γ = 1) (x : X) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∀ γ : Γ, γ ≠ 1 → ∀ y ∈ V, γ • y ∉ V := by
  obtain ⟨K, hKc, hKx⟩ := exists_compact_mem_nhds x
  have hS : Set.Finite {γ : Γ | ((γ • ·) '' K ∩ K).Nonempty} :=
    ProperlyDiscontinuousSMul.finite_disjoint_inter_image hKc hKc
  have hA : ∀ γ : Γ, ∃ A : Set X, A ∈ nhds x ∧ (γ ≠ 1 → ∀ y ∈ A, γ • y ∉ A) := by
    intro γ
    by_cases hγ : γ = 1
    · exact ⟨Set.univ, Filter.univ_mem, fun h => absurd hγ h⟩
    · have hne : x ≠ γ • x := fun h => hγ (hfree γ x h.symm)
      obtain ⟨V, W, hV, hW, hVW⟩ := t2_separation_nhds hne
      refine ⟨V ∩ (fun z => γ • z) ⁻¹' W,
        Filter.inter_mem hV ((continuous_const_smul γ).continuousAt.preimage_mem_nhds hW), fun _ y hy hγy => ?_⟩
      exact Set.disjoint_left.mp hVW hγy.1 hy.2
  choose A hAx hAsmall using hA
  have hN : (K ∩ ⋂ γ ∈ hS.toFinset, A γ) ∈ nhds x :=
    Filter.inter_mem hKx ((Filter.biInter_finset_mem _).mpr fun γ _ => hAx γ)
  refine ⟨interior (K ∩ ⋂ γ ∈ hS.toFinset, A γ), isOpen_interior, mem_interior_iff_mem_nhds.mpr hN,
    fun γ hγ y hy hγy => ?_⟩
  have hy' := interior_subset hy
  have hγy' := interior_subset hγy
  have hγS : γ ∈ hS.toFinset := hS.mem_toFinset.mpr ⟨γ • y, ⟨y, hy'.1, rfl⟩, hγy'.1⟩
  exact hAsmall γ hγ y (Set.mem_iInter₂.mp hy'.2 γ hγS) (Set.mem_iInter₂.mp hγy'.2 γ hγS)

private theorem exists_measurableSet_isFundamentalDomain [LocallyCompactSpace X] [LindelofSpace X]
    [ProperlyDiscontinuousSMul Γ X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (hfree : ∀ (γ : Γ) (x : X), γ • x = x → γ = 1) (μ : Measure X) :
    ∃ F : Set X, MeasurableSet F ∧ IsFundamentalDomain Γ F μ := by
  classical
  choose V hVo hxV hVsmall using exists_isOpen_smul_notMem (Γ := Γ) hfree
  obtain ⟨t, htc, htU⟩ := countable_cover_nhds (U := V) fun x => (hVo x).mem_nhds (hxV x)
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨∅, MeasurableSet.empty,
      IsFundamentalDomain.mk' MeasurableSet.empty.nullMeasurableSet fun x => (hX.false x).elim⟩
  have htne : t.Nonempty := by
    obtain ⟨x₀⟩ := hX
    have hx₀ : x₀ ∈ ⋃ y ∈ t, V y := by rw [htU]; exact Set.mem_univ x₀
    obtain ⟨y, hyt, -⟩ := Set.mem_iUnion₂.mp hx₀
    exact ⟨y, hyt⟩
  obtain ⟨e, he⟩ := htc.exists_eq_range htne

  obtain ⟨O, hO⟩ : ∃ O : ℕ → Set X, O = fun j => ⋃ γ : Γ, γ • V (e j) := ⟨_, rfl⟩
  have hOmem : ∀ j y, y ∈ O j ↔ ∃ γ : Γ, y ∈ γ • V (e j) := by
    intro j y
    simp only [hO, Set.mem_iUnion]
  have hOopen : ∀ j, IsOpen (O j) := by
    intro j
    simp only [hO]
    exact isOpen_iUnion fun γ => (hVo _).smul γ
  have hsub : ∀ j y, y ∈ V (e j) → y ∈ O j := fun j y hy =>
    (hOmem j y).mpr ⟨1, Set.mem_smul_set.mpr ⟨y, hy, one_smul Γ y⟩⟩
  have hOsmul : ∀ j (γ : Γ) y, y ∈ O j → γ • y ∈ O j := by
    intro j γ y hy
    obtain ⟨δ, hδ⟩ := (hOmem j y).mp hy
    exact (hOmem j _).mpr ⟨γ * δ, smul_smul γ δ (V (e j)) ▸ Set.smul_mem_smul_set hδ⟩
  obtain ⟨P, hP⟩ : ∃ P : ℕ → Set X, P = fun i => V (e i) \ ⋃ (j : ℕ) (_ : j < i), O j := ⟨_, rfl⟩
  have hPmem_mp : ∀ i y, y ∈ P i → y ∈ V (e i) ∧ ∀ j, j < i → y ∉ O j := by
    intro i y hy
    simp only [hP] at hy
    exact ⟨hy.1, fun j hj hyj => hy.2 (Set.mem_iUnion₂.mpr ⟨j, hj, hyj⟩)⟩
  have hPmem_mpr : ∀ i y, y ∈ V (e i) → (∀ j, j < i → y ∉ O j) → y ∈ P i := by
    intro i y h1 h2
    simp only [hP]
    refine Set.mem_diff_of_mem h1 fun hy => ?_
    obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.mp hy
    exact h2 j hj hyj
  have hPmeas : ∀ i, MeasurableSet (P i) := by
    intro i
    simp only [hP]
    exact (hVo _).measurableSet.diff
      (MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => (hOopen j).measurableSet)
  obtain ⟨F, hF⟩ : ∃ F : Set X, F = ⋃ i, P i := ⟨_, rfl⟩
  have hFmem : ∀ y, y ∈ F ↔ ∃ i, y ∈ P i := by
    intro y
    rw [hF]
    exact Set.mem_iUnion
  have hFmeas : MeasurableSet F := by
    rw [hF]
    exact MeasurableSet.iUnion hPmeas

  have hkey : ∀ δ : Γ, δ ≠ 1 → ∀ y, y ∈ F → δ • y ∉ F := by
    intro δ hδ y hyF hδyF
    obtain ⟨i, hyi⟩ := (hFmem y).mp hyF
    obtain ⟨k, hδyk⟩ := (hFmem _).mp hδyF
    obtain ⟨hyV, hyO⟩ := hPmem_mp i y hyi
    obtain ⟨hδyV, hδyO⟩ := hPmem_mp k _ hδyk
    rcases lt_trichotomy i k with hik | hik | hki
    · exact hδyO i hik (hOsmul i δ y (hsub i y hyV))
    · subst hik
      exact hVsmall (e i) δ hδ y hyV hδyV
    · have h2 : y ∈ O k := by
        have h := hOsmul k δ⁻¹ _ (hsub k _ hδyV)
        rwa [inv_smul_smul] at h
      exact hyO k hki h2
  refine ⟨F, hFmeas, IsFundamentalDomain.mk' hFmeas.nullMeasurableSet fun x => ?_⟩
  have hcov : ∃ i, x ∈ O i := by
    have hx : x ∈ ⋃ y ∈ t, V y := by rw [htU]; exact Set.mem_univ x
    obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.mp hx
    rw [he] at hyt
    obtain ⟨i, rfl⟩ := Set.mem_range.mp hyt
    exact ⟨i, hsub i x hxy⟩
  obtain ⟨i, hi, hmin⟩ : ∃ i, x ∈ O i ∧ ∀ j, j < i → x ∉ O j :=
    ⟨Nat.find hcov, Nat.find_spec hcov, fun _ hj => Nat.find_min hcov hj⟩
  obtain ⟨γ, hγ⟩ := (hOmem i x).mp hi
  obtain ⟨u, huV, rfl⟩ := Set.mem_smul_set.mp hγ
  have huP : u ∈ P i := hPmem_mpr i u huV fun j hj huj => hmin j hj (hOsmul j γ u huj)
  have huF : u ∈ F := (hFmem u).mpr ⟨i, huP⟩
  refine ⟨γ⁻¹, ?_, fun g hg => ?_⟩
  · show γ⁻¹ • γ • u ∈ F
    rw [inv_smul_smul]
    exact huF
  · by_contra hne
    have hδ : g * γ ≠ 1 := fun h => hne (eq_inv_of_mul_eq_one_left h)
    exact hkey (g * γ) hδ u huF (by rw [mul_smul]; exact hg)

end ProperlyDiscontinuousFundamentalDomain

namespace AdelicSigmaCompact

section Units

variable {M : Type*} [Monoid M] [TopologicalSpace M] [T2Space M] [ContinuousMul M] [SigmaCompactSpace M]

private theorem lindelofSpace_units : LindelofSpace Mˣ := by
  have hS : IsClosed ({p : M × M | p.1 * p.2 = 1} ∩ {p : M × M | p.2 * p.1 = 1}) :=
    (isClosed_eq (continuous_fst.mul continuous_snd) continuous_const).inter
      (isClosed_eq (continuous_snd.mul continuous_fst) continuous_const)
  haveI : LindelofSpace ({p : M × M | p.1 * p.2 = 1} ∩ {p : M × M | p.2 * p.1 = 1} : Set (M × M)) :=
    isLindelof_iff_lindelofSpace.mp hS.isLindelof
  let f : ({p : M × M | p.1 * p.2 = 1} ∩ {p : M × M | p.2 * p.1 = 1} : Set (M × M)) → Mˣ :=
    fun p => ⟨p.1.1, p.1.2, p.2.1, p.2.2⟩
  have hf : Continuous f :=
    Units.continuous_iff.mpr ⟨continuous_fst.comp continuous_subtype_val, continuous_snd.comp continuous_subtype_val⟩
  have hsurj : Function.Surjective f := fun u => ⟨⟨((u : M), ((u⁻¹ : Mˣ) : M)), u.mul_inv, u.inv_mul⟩, Units.ext rfl⟩
  exact LindelofSpace.of_continuous_surjective hf hsurj

end Units

section Matrix

variable (n : Type*) [Fintype n] (R : Type*) [TopologicalSpace R]

private scoped instance sigmaCompactSpace_matrix [SigmaCompactSpace R] : SigmaCompactSpace (Matrix n n R) :=
  inferInstanceAs (SigmaCompactSpace (n → n → R))

private scoped instance lindelofSpace_generalLinearGroup [DecidableEq n] [CommRing R] [T2Space R] [IsTopologicalRing R]
    [SigmaCompactSpace R] : LindelofSpace (GL n R) :=
  lindelofSpace_units

end Matrix

section Quotient

variable {G : Type*} [Group G] [TopologicalSpace G] [LindelofSpace G] (N : Subgroup G)

private scoped instance lindelofSpace_quotient : LindelofSpace (G ⧸ N) :=
  LindelofSpace.of_continuous_surjective QuotientGroup.continuous_mk QuotientGroup.mk_surjective

end Quotient

section Adeles

open NumberField IsDedekindDomain

variable (K : Type*) [Field K] [NumberField K]

private scoped instance sigmaCompactSpace_adeleRing [Countable K] : SigmaCompactSpace (AdeleRing (𝓞 K) K) := by
  obtain ⟨C, hC, hsub⟩ := AdelicBox.exists_isCompact_adelicBox_subset K
  have huniv : (⋃ k : K, (fun y => y - algebraMap K (AdeleRing (𝓞 K) K) k) '' C)
      = (Set.univ : Set (AdeleRing (𝓞 K) K)) := by
    refine Set.eq_univ_iff_forall.mpr fun x => ?_
    obtain ⟨k, hk, -⟩ := AdelicBox.existsUnique_algebraMap_add_mem_adelicBox K x
    exact Set.mem_iUnion.mpr ⟨k, algebraMap K (AdeleRing (𝓞 K) K) k + x, hsub hk, by simp⟩
  refine ⟨?_⟩
  rw [← huniv]
  exact isSigmaCompact_iUnion_of_isCompact _ fun k => hC.image (continuous_id.sub continuous_const)

end Adeles

end AdelicSigmaCompact
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact"

section DiscreteSubgroups

p2m_open "MeasureTheory NumberField IsDedekindDomain LanglandsTunnell.CubicInduction~isCompact_localMaximalCompact3~det_radicalP21~det_radicalP12 P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction"
open AdelicSigmaCompact ProperlyDiscontinuousFundamentalDomain

namespace RationalPointsDomain

section Generic

variable {G : Type*} [Group G] [TopologicalSpace G]

private theorem discreteTopology_of_exists_isOpen [IsTopologicalGroup G] (S : Subgroup G)
    (h : ∃ U : Set G, IsOpen U ∧ ∀ x ∈ S, x ∈ U ↔ x = 1) :
    DiscreteTopology S := by
  obtain ⟨U, hUo, hU⟩ := h
  rw [discreteTopology_iff_isOpen_singleton_one]
  refine isOpen_induced_iff.mpr ⟨U, hUo, ?_⟩
  ext ⟨x, hx⟩
  exact ⟨fun h => Set.mem_singleton_iff.mpr (Subtype.ext ((hU x hx).mp h)),
    fun h => (hU x hx).mpr (congrArg Subtype.val (Set.mem_singleton_iff.mp h))⟩

private theorem exists_isOpen_of_discreteTopology (S : Subgroup G) [DiscreteTopology S] :
    ∃ U : Set G, IsOpen U ∧ ∀ x ∈ S, x ∈ U ↔ x = 1 := by
  obtain ⟨U, hUo, hU⟩ := isOpen_induced_iff.mp (discreteTopology_iff_isOpen_singleton_one.mp ‹DiscreteTopology S›)
  refine ⟨U, hUo, fun x hx => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact congrArg Subtype.val (Set.mem_singleton_iff.mp ((Set.ext_iff.mp hU ⟨x, hx⟩).mp h))
  · exact (Set.ext_iff.mp hU ⟨x, hx⟩).mpr (Set.mem_singleton_iff.mpr (Subtype.ext h))

private theorem
    discreteTopology_of_forall_eq_mul_zpow [IsTopologicalGroup G] {H : Type*} [Group H] [TopologicalSpace H]
    (S : Subgroup G) [DiscreteTopology S] (ν : G →* H) (hν : Continuous ν) (hνS : ∀ γ ∈ S, ν γ = 1) (z₀ : G)
    (hz₀ : ∃ V ∈ nhds (1 : H), ∀ n : ℤ, ν z₀ ^ n ∈ V → n = 0) (S' : Subgroup G)
    (hS' : ∀ x ∈ S', ∃ γ ∈ S, ∃ n : ℤ, x = γ * z₀ ^ n) : DiscreteTopology S' := by
  obtain ⟨U, hUo, hU⟩ := exists_isOpen_of_discreteTopology S
  obtain ⟨V, hV, hVz⟩ := hz₀
  refine discreteTopology_of_exists_isOpen S' ⟨U ∩ ν ⁻¹' interior V, hUo.inter (isOpen_interior.preimage hν),
    fun x hx => ⟨fun hxU => ?_, fun hx1 => ?_⟩⟩
  · obtain ⟨γ, hγ, n, rfl⟩ := hS' x hx
    have hn : n = 0 := by
      refine hVz n (interior_subset ?_)
      have h := hxU.2
      rwa [Set.mem_preimage, map_mul, map_zpow, hνS γ hγ, one_mul] at h
    subst hn
    rw [zpow_zero, mul_one] at hxU ⊢
    exact (hU γ hγ).mp hxU.1
  · subst hx1
    exact ⟨(hU 1 S.one_mem).mpr rfl, by simpa only [Set.mem_preimage, map_one] using mem_interior_iff_mem_nhds.mpr hV⟩

end Generic
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact"

section ProperlyDiscontinuous

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

private theorem properlyDiscontinuousSMul_of_discreteTopology (S : Subgroup G) [DiscreteTopology S] :
    ProperlyDiscontinuousSMul S G :=
  S.properlyDiscontinuousSMul_of_tendsto_cofinite
    (S.tendsto_coe_cofinite_of_discrete (isDiscrete_iff_discreteTopology.mpr ‹DiscreteTopology S›))

end ProperlyDiscontinuous
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact"

section Production

private theorem exists_mem_nhds_zero_forall_eq_zero :
    ∃ B ∈ nhds (0 : AdeleRing (𝓞 ℚ) ℚ), ∀ k : ℚ, algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) k ∈ B → k = 0 := by
  obtain ⟨V, hVo, ⟨v, hv⟩, hVsub⟩ := AdelicBox.exists_isOpen_subset_adelicBox ℚ
  refine ⟨(fun y => y + v) ⁻¹' V, (hVo.preimage (continuous_id.add continuous_const)).mem_nhds ?_, fun k hk => ?_⟩
  · show (0 : AdeleRing (𝓞 ℚ) ℚ) + v ∈ V
    rwa [zero_add]
  · obtain ⟨k₀, -, huniq⟩ := AdelicBox.existsUnique_algebraMap_add_mem_adelicBox ℚ v
    have h0 : algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (0 : ℚ) + v ∈ AdelicBox.adelicBox ℚ := by
      rw [map_zero, zero_add]
      exact hVsub hv
    exact (huniq k (hVsub (show algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) k + v ∈ V from hk))).trans (huniq 0 h0).symm

private theorem coe_globalPointsGL_apply (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ) (i j : Fin 3) :
    (globalPointsGL 3 (𝓞 ℚ) ℚ γ : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j = algebraMap ℚ _ (γ i j) :=
  Matrix.GeneralLinearGroup.map_apply (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) i j γ

private theorem discreteTopology_range_globalPointsGL : DiscreteTopology (globalPointsGL 3 (𝓞 ℚ) ℚ).range := by
  obtain ⟨B, hB, hBdisc⟩ := exists_mem_nhds_zero_forall_eq_zero
  refine discreteTopology_of_exists_isOpen _
    ⟨⋂ i : Fin 3, ⋂ j : Fin 3, (fun g : AdelicGL 3 (𝓞 ℚ) ℚ =>
      (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j - (1 : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j)
        ⁻¹' interior B, ?_, ?_⟩
  · refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_interior.preimage ?_
    exact (Units.continuous_val.matrix_elem i j).sub continuous_const
  · rintro x ⟨γ, rfl⟩
    constructor
    · intro hx
      suffices hγ : γ = 1 by rw [hγ, map_one]
      refine Units.ext (Matrix.ext fun i j => ?_)
      have h := Set.mem_iInter.mp (Set.mem_iInter.mp hx i) j
      rw [Set.mem_preimage, coe_globalPointsGL_apply] at h
      have h' : algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (γ i j - (1 : Matrix (Fin 3) (Fin 3) ℚ) i j) ∈ B := by
        rw [map_sub]
        refine interior_subset ?_
        convert h using 3
        simp only [Matrix.one_apply, apply_ite (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)), map_one, map_zero]
      exact sub_eq_zero.mp (hBdisc _ h')
    · intro hx
      rw [hx]
      refine Set.mem_iInter.mpr fun i => Set.mem_iInter.mpr fun j => ?_
      rw [Set.mem_preimage, Units.val_one, sub_self]
      exact mem_interior_iff_mem_nhds.mpr hB

private theorem exists_measurableSet_isFundamentalDomain_of_discreteTopology (S : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
    [DiscreteTopology S] :
    ∃ F : Set (AdelicGL 3 (𝓞 ℚ) ℚ), MeasurableSet[AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ] F ∧
      @IsFundamentalDomain S (AdelicGL 3 (𝓞 ℚ) ℚ) _ _ (AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ) F
        (AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
  letI := AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := properlyDiscontinuousSMul_of_discreteTopology S
  haveI : ContinuousConstSMul S (AdelicGL 3 (𝓞 ℚ) ℚ) := ⟨fun γ => by
    show Continuous fun x : AdelicGL 3 (𝓞 ℚ) ℚ => (γ : AdelicGL 3 (𝓞 ℚ) ℚ) * x
    exact continuous_const.mul continuous_id⟩
  refine exists_measurableSet_isFundamentalDomain (fun γ x h => ?_) (AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)
  change (γ : AdelicGL 3 (𝓞 ℚ) ℚ) * x = x at h
  exact OneMemClass.coe_eq_one.mp (mul_right_cancel (h.trans (one_mul x).symm))

private theorem exists_measurableSet_isFundamentalDomain_range_globalPointsGL :
    ∃ F : Set (AdelicGL 3 (𝓞 ℚ) ℚ), MeasurableSet[AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ] F ∧
      @IsFundamentalDomain (globalPointsGL 3 (𝓞 ℚ) ℚ).range (AdelicGL 3 (𝓞 ℚ) ℚ) _ _
        (AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ) F (AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
  haveI := discreteTopology_range_globalPointsGL
  exact exists_measurableSet_isFundamentalDomain_of_discreteTopology _

end Production
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact"

end RationalPointsDomain
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact"

end DiscreteSubgroups
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact"

section Slab

p2m_open "MeasureTheory NumberField NumberField.TateGlobal LanglandsTunnell.CubicInduction~isCompact_localMaximalCompact3~det_radicalP21~det_radicalP12 P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction"
p2m_open "LanglandsTunnell.CubicInduction.SlabL2~exists_isSlabDomain P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.RationalPointsDomain"

namespace SlabDomain

section Generic

variable {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α] {μ : Measure α}

private theorem isFundamentalDomain_inter_restrict {s : Set α} (h : IsFundamentalDomain G s μ) {T : Set α}
    (hT : MeasurableSet T) (hTinv : ∀ (g : G) (x : α), g • x ∈ T ↔ x ∈ T) :
    IsFundamentalDomain G (s ∩ T) (μ.restrict T) := by
  have hac : μ.restrict T ≪ μ := Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  have h' : IsFundamentalDomain G s (μ.restrict T) := h.mono hac
  refine ⟨h'.nullMeasurableSet.inter hT.nullMeasurableSet, ?_, fun g g' hgg' => ?_⟩
  · refine ((ae_restrict_of_ae h.ae_covers).and (ae_restrict_mem hT)).mono ?_
    rintro x ⟨⟨g, hg⟩, hx⟩
    exact ⟨g, hg, (hTinv g x).mpr hx⟩
  · exact (show AEDisjoint (μ.restrict T) (g • s) (g' • s) from h'.aedisjoint hgg').mono
      (Set.smul_set_mono Set.inter_subset_left) (Set.smul_set_mono Set.inter_subset_left)

end Generic
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact"

section Production

private theorem ideleNorm_det_globalPointsGL (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ) :
    ideleNorm ℚ (Matrix.GeneralLinearGroup.det (globalPointsGL 3 (𝓞 ℚ) ℚ γ)) = 1 := by
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdeleRing (𝓞 ℚ) ℚ) := ⟨rfl⟩
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap ℚ (Matrix.GeneralLinearGroup.det γ)
  have h2 : Matrix.GeneralLinearGroup.det (globalPointsGL 3 (𝓞 ℚ) ℚ γ) =
      Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom (Matrix.GeneralLinearGroup.det γ) :=
    Matrix.GeneralLinearGroup.map_det (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) γ
  unfold ideleNorm
  rw [h2, h]
  simp

private theorem ideleNorm_det_mul_mem_Icc_iff (γ : (globalPointsGL 3 (𝓞 ℚ) ℚ).range) (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (α β : ℝ) :
    ideleNorm ℚ (Matrix.GeneralLinearGroup.det ((γ : AdelicGL 3 (𝓞 ℚ) ℚ) * g)) ∈ Set.Icc α β ↔
      ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β := by
  obtain ⟨γ, ⟨γ₀, hγ₀⟩⟩ := γ
  subst hγ₀
  show ideleNorm ℚ (Matrix.GeneralLinearGroup.det (globalPointsGL 3 (𝓞 ℚ) ℚ γ₀ * g)) ∈ Set.Icc α β ↔ _
  rw [map_mul, ideleNorm_mul, ideleNorm_det_globalPointsGL, one_mul]

private theorem smul_ideleNormDetSlab (γ : (globalPointsGL 3 (𝓞 ℚ) ℚ).range) (α β : ℝ) :
    γ • ideleNormDetSlab α β = ideleNormDetSlab α β := by
  ext g
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  exact ideleNorm_det_mul_mem_Icc_iff γ⁻¹ g α β

private theorem continuous_ideleNorm_det_gl3 :
    Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) := by
  refine (continuous_ideleNorm ℚ).comp (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · exact Units.continuous_val.matrix_det.congr fun g => (Matrix.GeneralLinearGroup.val_det_apply g).symm
  · exact Units.continuous_coe_inv.matrix_det.congr fun g => by
      rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]

attribute [local instance] NumberField.AdelicHaar.glBorel

private theorem measurableSet_slab_gl3 (α β : ℝ) :
    MeasurableSet {g : AdelicGL 3 (𝓞 ℚ) ℚ | ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} := by
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  exact continuous_ideleNorm_det_gl3.measurable measurableSet_Icc

private theorem exists_isFundamentalDomain_globalPointsGL_range_restrict_ideleNorm_det_Icc (α β : ℝ) :
    ∃ S : Set (AdelicGL 3 (𝓞 ℚ) ℚ),
      S ⊆ {g | ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} ∧
      IsFundamentalDomain (globalPointsGL 3 (𝓞 ℚ) ℚ).range S
        ((NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).restrict
          {g | ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}) := by
  obtain ⟨F, -, hF⟩ := exists_measurableSet_isFundamentalDomain_range_globalPointsGL
  exact ⟨F ∩ _, Set.inter_subset_right,
    isFundamentalDomain_inter_restrict hF (measurableSet_slab_gl3 α β)
      fun γ g => ideleNorm_det_mul_mem_Icc_iff γ g α β⟩

end Production
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact"

end SlabDomain
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact"

end Slab
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact"

end DomainsAndSlab
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact"

section SlabDatum

p2m_open "NumberField LanglandsTunnell.CubicInduction~isCompact_localMaximalCompact3~det_radicalP21~det_radicalP12 P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2~exists_isSlabDomain P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.SlabDomain"

namespace L2Witness

private theorem exists_isSlabDomain : ∃ Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsSlabDomain 1 8 Φ₀ := by
  obtain ⟨S, -, hS⟩ := exists_isFundamentalDomain_globalPointsGL_range_restrict_ideleNorm_det_Icc 1 8
  exact ⟨S, (isSlabDomain_iff 1 8 S).mpr ⟨one_pos, by norm_num, hS⟩⟩

end L2Witness
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact"

end SlabDatum
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact"

section ClassActionBlock

noncomputable section

open Submodule
open scoped InnerProductSpace

namespace DenseUnitaryExtension

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {C : Type*} [AddCommGroup C] [Module ℂ C]
variable {Hc : Type*} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc]

private structure IsDenseIsometricAction (T : C →ₗ[ℂ] Hc) (D : Submodule ℂ Hc) (a : G →* Module.End ℂ C) : Prop where
  mem : ∀ c, T c ∈ D
  dense : (D : Set Hc) ⊆ closure (LinearMap.range T : Set Hc)
  norm_eq : ∀ g c, ‖T (a g c)‖ = ‖T c‖
  cont : ∀ c, Continuous fun g => T (a g c)

variable {T : C →ₗ[ℂ] Hc} {D : Submodule ℂ Hc} {a : G →* Module.End ℂ C}

namespace IsDenseIsometricAction

private def gen (h : IsDenseIsometricAction T D a) : C →ₗ[ℂ] D :=
  LinearMap.codRestrict D T h.mem

@[scoped simp]
private theorem coe_gen (h : IsDenseIsometricAction T D a) (c : C) : (h.gen c : Hc) = T c :=
  rfl

private theorem norm_gen (h : IsDenseIsometricAction T D a) (c : C) : ‖h.gen c‖ = ‖T c‖ :=
  rfl

private theorem denseRange_gen (h : IsDenseIsometricAction T D a) : DenseRange h.gen := by
  have h1 : (LinearMap.range T : Set Hc) ⊆ D := by
    rintro _ ⟨c, rfl⟩
    exact h.mem c
  have h2 : DenseRange (Set.inclusion h1) := (denseRange_inclusion_iff h1).2 h.dense
  have h3 : Function.Surjective fun c : C => (⟨T c, LinearMap.mem_range_self T c⟩ : LinearMap.range T) := by
    rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := LinearMap.mem_range.1 hx
    exact ⟨c, rfl⟩
  have h4 : (h.gen : C → D) =
      Set.inclusion h1 ∘ fun c : C => (⟨T c, LinearMap.mem_range_self T c⟩ : LinearMap.range T) := by
    funext c
    rfl
  rw [h4]
  exact h2.comp h3.denseRange (continuous_inclusion h1)

private theorem norm_bound (h : IsDenseIsometricAction T D a) (g : G) (c : C) :
    ‖(h.gen ∘ₗ a g) c‖ ≤ 1 * ‖h.gen c‖ := by
  rw [one_mul, LinearMap.comp_apply, norm_gen, norm_gen, h.norm_eq]

private theorem norm_bound' (h : IsDenseIsometricAction T D a) (g : G) :
    ∃ M : ℝ, ∀ c : C, ‖(h.gen ∘ₗ a g) c‖ ≤ M * ‖h.gen c‖ :=
  ⟨1, h.norm_bound g⟩

variable [CompleteSpace D]

private def U (h : IsDenseIsometricAction T D a) (g : G) : D →L[ℂ] D :=
  (h.gen ∘ₗ a g).extendOfNorm h.gen

private theorem U_gen (h : IsDenseIsometricAction T D a) (g : G) (c : C) : h.U g (h.gen c) = h.gen (a g c) :=
  LinearMap.extendOfNorm_eq h.denseRange_gen (h.norm_bound' g) c

private theorem U_one (h : IsDenseIsometricAction T D a) : h.U 1 = ContinuousLinearMap.id ℂ D := by
  refine LinearMap.extendOfNorm_unique h.denseRange_gen 1 (h.norm_bound 1) _ ?_
  ext c
  rw [map_one]
  rfl

private theorem U_mul (h : IsDenseIsometricAction T D a) (g g' : G) : h.U (g * g') = (h.U g).comp (h.U g') := by
  refine LinearMap.extendOfNorm_unique h.denseRange_gen 1 (h.norm_bound (g * g')) _ ?_
  ext c
  show ((h.U g (h.U g' (h.gen c)) : D) : Hc) = ((h.gen ∘ₗ a (g * g')) c : Hc)
  rw [U_gen, U_gen, map_mul]
  rfl

private theorem U_inv_U (h : IsDenseIsometricAction T D a) (g : G) (x : D) : h.U g⁻¹ (h.U g x) = x := by
  rw [← ContinuousLinearMap.comp_apply, ← U_mul, inv_mul_cancel, U_one]
  rfl

private theorem U_U_inv (h : IsDenseIsometricAction T D a) (g : G) (x : D) : h.U g (h.U g⁻¹ x) = x := by
  simpa using h.U_inv_U g⁻¹ x

private theorem norm_U_le (h : IsDenseIsometricAction T D a) (g : G) (x : D) : ‖h.U g x‖ ≤ ‖x‖ := by
  first | simpa using LinearMap.norm_extendOfNorm_apply_le h.denseRange_gen 1 (h.norm_bound g) x | (have h_1 := LinearMap.norm_extendOfNorm_apply_le h.denseRange_gen 1 (h.norm_bound g) x; simp at h_1; exact h_1) | (have h_1 := LinearMap.norm_extendOfNorm_apply_le h.denseRange_gen 1 (h.norm_bound g) x; simp at h_1 ⊢; exact h_1) | exact (LinearMap.norm_extendOfNorm_apply_le h.denseRange_gen 1 (h.norm_bound g) x)

private theorem norm_U (h : IsDenseIsometricAction T D a) (g : G) (x : D) : ‖h.U g x‖ = ‖x‖ :=
  le_antisymm (h.norm_U_le g x) (by simpa [U_inv_U] using h.norm_U_le g⁻¹ (h.U g x))

private def isometry (h : IsDenseIsometricAction T D a) (g : G) : D →ₗᵢ[ℂ] D :=
  { (h.U g : D →ₗ[ℂ] D) with norm_map' := h.norm_U g }

private theorem inner_U_U (h : IsDenseIsometricAction T D a) (g : G) (x y : D) :
    ⟪h.U g x, h.U g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (h.isometry g).inner_map_map x y

private theorem adjoint_U (h : IsDenseIsometricAction T D a) (g : G) :
    ContinuousLinearMap.adjoint (h.U g) = h.U g⁻¹ := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [← h.inner_U_U g (h.U g⁻¹ x) y, U_U_inv]

private def hom (h : IsDenseIsometricAction T D a) : G →* (D →L[ℂ] D) where
  toFun := h.U
  map_one' := h.U_one
  map_mul' g g' := by
    rw [ContinuousLinearMap.mul_def]
    exact h.U_mul g g'

private theorem hom_apply (h : IsDenseIsometricAction T D a) (g : G) : h.hom g = h.U g :=
  rfl

private theorem continuous_U_apply (h : IsDenseIsometricAction T D a) (x : D) : Continuous fun g => h.U g x := by
  apply continuous_of_uniform_approx_of_continuous
  intro u hu
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu
  obtain ⟨c, hc⟩ := Metric.denseRange_iff.1 h.denseRange_gen x (ε / 2) (half_pos hε)
  refine ⟨fun g => h.U g (h.gen c), ?_, fun g => hεu ?_⟩
  · simp_rw [U_gen]
    show Continuous fun g => (⟨T (a g c), h.mem (a g c)⟩ : D)
    exact (h.cont c).subtype_mk _
  · rw [dist_eq_norm, ← map_sub, norm_U, ← dist_eq_norm]
    exact hc.trans (half_lt_self hε)

end IsDenseIsometricAction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction"

end DenseUnitaryExtension
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.AdelicGL CubicInduction.globalPointsGL"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "SlabL2.realCoordinate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 LocalGL3 heckeGen1 heckeGen2 cosetSum IsCosetEigenfunction IsRightInvariant archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 one_le_gauge3 one_le_archGauge3 IsModerateGrowth3 matrixFin_ext matrixAdele_ext localMatN localMatN_apply_self localMatN_apply_of_ne mapMatrix_localMatN_self mapMatrix_localMatN_of_ne localEmbedN finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN finEmbedN localToAdelic3 exists_mul_eq_unipotent_mul_diagonal_mul_compact smoothingOperator_mem_cuspFunctions_of_isCuspidalAlong exists_isCompactOperator_cuspidalSubspace_smoothingOperator exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous exists_inner_toL2_translateRight_ne_zero_of_isCosetEigenfunction measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator"
p2m_open "LanglandsTunnell.CubicInduction~isCompact_localMaximalCompact3~det_radicalP21~det_radicalP12 LanglandsTunnell~CubicInduction.isCompact_localMaximalCompact3"

open Matrix IsDedekindDomain NumberField AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

section Unipotent

private theorem upperUnipotent3_inv_coe' (x y z : AdeleRing (𝓞 ℚ) ℚ) :
    (((upperUnipotent3 x y z)⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      !![1, -x, x * y - z; 0, 1, -y; 0, 0, 1] :=
  rfl

private theorem continuous_upperUnipotent3 :
    Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
      (upperUnipotent3 p.1 p.2.1 p.2.2 : AdelicGL 3 (𝓞 ℚ) ℚ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    simp only [Function.comp_apply, upperUnipotent3_coe]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    simp only [upperUnipotent3_inv_coe']
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem continuous_radicalP21_pair :
    Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => (radicalP21 ![p.1, p.2] : AdelicGL 3 (𝓞 ℚ) ℚ) := by
  show Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => upperUnipotent3 0 p.2 p.1
  exact continuous_upperUnipotent3.comp
    (f := fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => ((0 : AdeleRing (𝓞 ℚ) ℚ), p.2, p.1)) (by fun_prop)

private theorem continuous_radicalP12_pair :
    Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => (radicalP12 ![p.1, p.2] : AdelicGL 3 (𝓞 ℚ) ℚ) := by
  show Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => upperUnipotent3 p.1 0 p.2
  exact continuous_upperUnipotent3.comp
    (f := fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => (p.1, (0 : AdeleRing (𝓞 ℚ) ℚ), p.2)) (by fun_prop)

end Unipotent
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension"

section Box

private scoped instance secondCountable_adeleRing : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ) :=
  NumberField.AdeleRing.secondCountableTopology ℚ

private abbrev boxMeasure : MeasureTheory.Measure (AdeleRing (𝓞 ℚ) ℚ) :=
  ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ)

private scoped instance isProbabilityMeasure_boxMeasure : MeasureTheory.IsProbabilityMeasure boxMeasure :=
  AdelicBox.isProbabilityMeasure_cond_adelicBox ℚ

private theorem integrable_boxMeasure_of_continuous {f : AdeleRing (𝓞 ℚ) ℚ → ℂ} (hf : Continuous f) :
    MeasureTheory.Integrable f boxMeasure := by
  obtain ⟨C, hC, hsub⟩ := AdelicBox.exists_isCompact_adelicBox_subset ℚ
  have h1 : MeasureTheory.IntegrableOn f C (AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) :=
    hf.continuousOn.integrableOn_compact hC
  have h2 : MeasureTheory.IntegrableOn f (AdelicBox.adelicBox ℚ) (AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) :=
    h1.mono_set hsub
  exact MeasureTheory.Integrable.smul_measure h2
    (ENNReal.inv_ne_top.mpr (AdelicBox.adelicAddHaar_adelicBox_pos ℚ).ne')

private theorem continuous_integral_boxMeasure {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [LocallyCompactSpace X] {f : X → AdeleRing (𝓞 ℚ) ℚ → ℂ} (hf : Continuous (Function.uncurry f)) :
    Continuous fun x => ∫ y, f x y ∂boxMeasure := by
  obtain ⟨C, hC, hsub⟩ := AdelicBox.exists_isCompact_adelicBox_subset ℚ
  refine continuous_iff_continuousAt.mpr fun x₀ => ?_
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds x₀
  obtain ⟨M, hM⟩ := (hK.prod hC).exists_bound_of_continuousOn hf.continuousOn
  refine MeasureTheory.continuousAt_of_dominated (bound := fun _ => M) ?_ ?_ (MeasureTheory.integrable_const M) ?_
  · exact Filter.Eventually.of_forall fun x =>
      (hf.comp (f := fun y => (x, y)) (by fun_prop)).aestronglyMeasurable
  · refine Filter.mem_of_superset hKn fun x hx => ?_
    exact (ProbabilityTheory.ae_cond_mem (AdelicBox.measurableSet_adelicBox ℚ)).mono fun y hy =>
      hM (x, y) ⟨hx, hsub hy⟩
  · exact Filter.Eventually.of_forall fun y => (hf.comp (f := fun x => (x, y)) (by fun_prop)).continuousAt

private theorem integral2_boxMeasure_add {φ φ' : AdeleRing (𝓞 ℚ) ℚ → AdeleRing (𝓞 ℚ) ℚ → ℂ}
    (hφ : Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => φ p.1 p.2)
    (hφ' : Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => φ' p.1 p.2) :
    (∫ x, ∫ y, (φ x y + φ' x y) ∂boxMeasure ∂boxMeasure) =
      (∫ x, ∫ y, φ x y ∂boxMeasure ∂boxMeasure) + ∫ x, ∫ y, φ' x y ∂boxMeasure ∂boxMeasure := by
  have hy : ∀ x, Continuous fun y => φ x y := fun x => hφ.comp (f := fun y => (x, y)) (by fun_prop)
  have hy' : ∀ x, Continuous fun y => φ' x y := fun x => hφ'.comp (f := fun y => (x, y)) (by fun_prop)
  have hx : Continuous fun x => ∫ y, φ x y ∂boxMeasure := continuous_integral_boxMeasure (f := φ) hφ
  have hx' : Continuous fun x => ∫ y, φ' x y ∂boxMeasure := continuous_integral_boxMeasure (f := φ') hφ'
  have hyadd : ∀ x, (∫ y, (φ x y + φ' x y) ∂boxMeasure) =
      (∫ y, φ x y ∂boxMeasure) + ∫ y, φ' x y ∂boxMeasure := fun x =>
    MeasureTheory.integral_add (integrable_boxMeasure_of_continuous (hy x))
      (integrable_boxMeasure_of_continuous (hy' x))
  simp_rw [hyadd]
  exact MeasureTheory.integral_add (integrable_boxMeasure_of_continuous hx) (integrable_boxMeasure_of_continuous hx')

private theorem integral3_boxMeasure_add
    {φ φ' : AdeleRing (𝓞 ℚ) ℚ → AdeleRing (𝓞 ℚ) ℚ → AdeleRing (𝓞 ℚ) ℚ → ℂ}
    (hφ : Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => φ p.1 p.2.1 p.2.2)
    (hφ' : Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => φ' p.1 p.2.1 p.2.2) :
    (∫ x, ∫ y, ∫ z, (φ x y z + φ' x y z) ∂boxMeasure ∂boxMeasure ∂boxMeasure) =
      (∫ x, ∫ y, ∫ z, φ x y z ∂boxMeasure ∂boxMeasure ∂boxMeasure) +
        ∫ x, ∫ y, ∫ z, φ' x y z ∂boxMeasure ∂boxMeasure ∂boxMeasure := by
  have hz : ∀ x y, Continuous fun z => φ x y z := fun x y => hφ.comp (f := fun z => (x, y, z)) (by fun_prop)
  have hz' : ∀ x y, Continuous fun z => φ' x y z := fun x y => hφ'.comp (f := fun z => (x, y, z)) (by fun_prop)
  have hzadd : ∀ x y, (∫ z, (φ x y z + φ' x y z) ∂boxMeasure) =
      (∫ z, φ x y z ∂boxMeasure) + ∫ z, φ' x y z ∂boxMeasure := fun x y =>
    MeasureTheory.integral_add (integrable_boxMeasure_of_continuous (hz x y))
      (integrable_boxMeasure_of_continuous (hz' x y))
  simp_rw [hzadd]
  have h1 : Continuous fun q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => ∫ z, φ q.1 q.2 z ∂boxMeasure :=
    continuous_integral_boxMeasure
      (f := fun (q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) (z : AdeleRing (𝓞 ℚ) ℚ) => φ q.1 q.2 z)
      (hφ.comp (f := fun r : (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ => (r.1.1, r.1.2, r.2))
        (by fun_prop))
  have h1' : Continuous fun q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => ∫ z, φ' q.1 q.2 z ∂boxMeasure :=
    continuous_integral_boxMeasure
      (f := fun (q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) (z : AdeleRing (𝓞 ℚ) ℚ) => φ' q.1 q.2 z)
      (hφ'.comp (f := fun r : (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ => (r.1.1, r.1.2, r.2))
        (by fun_prop))
  exact integral2_boxMeasure_add (φ := fun x y => ∫ z, φ x y z ∂boxMeasure)
    (φ' := fun x y => ∫ z, φ' x y z ∂boxMeasure) h1 h1'

end Box
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension"

section Pins

variable (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
  (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)

private abbrev prodPins : CarrierPins ℚ := productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)

variable {D U gen}

section Cuspidal

variable {F F' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}

private theorem isCuspidalAlongP21_prodPins_add (hF : Continuous F) (hF' : Continuous F')
    (h1 : IsCuspidalAlongP21 (prodPins D U gen) F) (h2 : IsCuspidalAlongP21 (prodPins D U gen) F') :
    IsCuspidalAlongP21 (prodPins D U gen) (F + F') := by
  intro g
  have hc : Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => F (radicalP21 ![p.1, p.2] * g) :=
    hF.comp (continuous_radicalP21_pair.mul continuous_const)
  have hc' : Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => F' (radicalP21 ![p.1, p.2] * g) :=
    hF'.comp (continuous_radicalP21_pair.mul continuous_const)
  have h := integral2_boxMeasure_add (φ := fun x y => F (radicalP21 ![x, y] * g))
    (φ' := fun x y => F' (radicalP21 ![x, y] * g)) hc hc'
  simp only [Pi.add_apply]
  exact h.trans ((congrArg₂ (· + ·) (h1 g) (h2 g)).trans (add_zero (0 : ℂ)))

private theorem isCuspidalAlongP12_prodPins_add (hF : Continuous F) (hF' : Continuous F')
    (h1 : IsCuspidalAlongP12 (prodPins D U gen) F) (h2 : IsCuspidalAlongP12 (prodPins D U gen) F') :
    IsCuspidalAlongP12 (prodPins D U gen) (F + F') := by
  intro g
  have hc : Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => F (radicalP12 ![p.1, p.2] * g) :=
    hF.comp (continuous_radicalP12_pair.mul continuous_const)
  have hc' : Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => F' (radicalP12 ![p.1, p.2] * g) :=
    hF'.comp (continuous_radicalP12_pair.mul continuous_const)
  have h := integral2_boxMeasure_add (φ := fun x y => F (radicalP12 ![x, y] * g))
    (φ' := fun x y => F' (radicalP12 ![x, y] * g)) hc hc'
  simp only [Pi.add_apply]
  exact h.trans ((congrArg₂ (· + ·) (h1 g) (h2 g)).trans (add_zero (0 : ℂ)))

private theorem isCuspidalAlongP21_smul (pins : CarrierPins ℚ) (c : ℂ) (hF : IsCuspidalAlongP21 pins F) :
    IsCuspidalAlongP21 pins (c • F) := by
  intro g
  simp only [Pi.smul_apply, smul_eq_mul, MeasureTheory.integral_const_mul, hF g, mul_zero]

private theorem isCuspidalAlongP12_smul (pins : CarrierPins ℚ) (c : ℂ) (hF : IsCuspidalAlongP12 pins F) :
    IsCuspidalAlongP12 pins (c • F) := by
  intro g
  simp only [Pi.smul_apply, smul_eq_mul, MeasureTheory.integral_const_mul, hF g, mul_zero]

private theorem isCuspidalAlongP21_zero (pins : CarrierPins ℚ) :
    IsCuspidalAlongP21 pins (0 : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) := by
  intro g
  simp

private theorem isCuspidalAlongP12_zero (pins : CarrierPins ℚ) :
    IsCuspidalAlongP12 pins (0 : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) := by
  intro g
  simp

end Cuspidal
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension"

end Pins
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.AdelicGL CubicInduction.globalPointsGL"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "SlabL2.realCoordinate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 LocalGL3 heckeGen1 heckeGen2 cosetSum IsCosetEigenfunction IsRightInvariant archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 one_le_gauge3 one_le_archGauge3 IsModerateGrowth3 matrixFin_ext matrixAdele_ext localMatN localMatN_apply_self localMatN_apply_of_ne mapMatrix_localMatN_self mapMatrix_localMatN_of_ne localEmbedN finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN finEmbedN localToAdelic3 exists_mul_eq_unipotent_mul_diagonal_mul_compact smoothingOperator_mem_cuspFunctions_of_isCuspidalAlong exists_isCompactOperator_cuspidalSubspace_smoothingOperator exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous exists_inner_toL2_translateRight_ne_zero_of_isCosetEigenfunction measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator"
namespace CuspClassAction
p2m_open "LanglandsTunnell.CubicInduction~isCompact_localMaximalCompact3~det_radicalP21~det_radicalP12 LanglandsTunnell~CubicInduction.isCompact_localMaximalCompact3"

p2m_open "IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction.SlabL2~exists_isSlabDomain"

variable (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))

private def cuspSubmodule : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) where
  carrier := cuspFunctions ω a b Φ₀
  zero_mem' := ⟨Submodule.zero_mem _, continuous_zero, isCuspidalAlongP21_zero _, isCuspidalAlongP12_zero _⟩
  add_mem' := fun {_ _} hF hF' =>
    ⟨Submodule.add_mem _ hF.1 hF'.1, hF.2.1.add hF'.2.1,
      isCuspidalAlongP21_prodPins_add (D := ∅) (U := fun _ => ⊥) (gen := fun _ => 1) hF.2.1 hF'.2.1 hF.2.2.1
        hF'.2.2.1,
      isCuspidalAlongP12_prodPins_add (D := ∅) (U := fun _ => ⊥) (gen := fun _ => 1) hF.2.1 hF'.2.1 hF.2.2.2
        hF'.2.2.2⟩
  smul_mem' := fun c {_} hF =>
    ⟨Submodule.smul_mem _ c hF.1, hF.2.1.const_smul c, isCuspidalAlongP21_smul _ c hF.2.2.1,
      isCuspidalAlongP12_smul _ c hF.2.2.2⟩

private theorem mem_cuspSubmodule_iff (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    F ∈ cuspSubmodule ω a b Φ₀ ↔ F ∈ cuspFunctions ω a b Φ₀ :=
  Iff.rfl

private def cuspMemberSubmodule : Submodule ℂ ↥(automorphicSubmodule ω a b Φ₀) :=
  (cuspSubmodule ω a b Φ₀).comap (automorphicSubmodule ω a b Φ₀).subtype

private theorem mem_cuspMemberSubmodule_iff (f : ↥(automorphicSubmodule ω a b Φ₀)) :
    f ∈ cuspMemberSubmodule ω a b Φ₀ ↔ (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) ∈ cuspFunctions ω a b Φ₀ :=
  Iff.rfl

private theorem span_cuspMembers : Submodule.span ℂ (cuspMembers ω a b Φ₀) = cuspMemberSubmodule ω a b Φ₀ :=
  Submodule.span_eq (cuspMemberSubmodule ω a b Φ₀)

private scoped instance completeSpace_cuspidalSubspace : CompleteSpace ↥(cuspidalSubspace ω a b Φ₀) :=
  (isClosed_cuspidalSubspace ω a b Φ₀).isComplete.completeSpace_coe

private def RightTranslationLaw : Prop :=
  ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀),
    ∃ hmem : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, translateRight g F ∈ cuspFunctions ω a b Φ₀,
      (∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        ‖toL2 ω a b Φ₀ ⟨translateRight g F, (hmem g).1⟩‖ = ‖toL2 ω a b Φ₀ ⟨F, hF.1⟩‖) ∧
      Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => toL2 ω a b Φ₀ ⟨translateRight g F, (hmem g).1⟩

variable {ω a b Φ₀}

private def act (hR : RightTranslationLaw ω a b Φ₀) :
    AdelicGL 3 (𝓞 ℚ) ℚ →* Module.End ℂ ↥(cuspMemberSubmodule ω a b Φ₀) where
  toFun g :=
    { toFun := fun f =>
        ⟨⟨translateRight g (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ((hR _ f.2).fst g).1⟩, (hR _ f.2).fst g⟩
      map_add' := fun f f' => rfl
      map_smul' := fun c f => rfl }
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply Subtype.ext
    exact translateRight_one _
  map_mul' g g' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply Subtype.ext
    exact translateRight_mul g g' _

private theorem coe_coe_act (hR : RightTranslationLaw ω a b Φ₀) (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (f : ↥(cuspMemberSubmodule ω a b Φ₀)) :
    ((act hR g f : ↥(automorphicSubmodule ω a b Φ₀)) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) =
      translateRight g (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :=
  rfl

private def classOf : ↥(cuspMemberSubmodule ω a b Φ₀) →ₗ[ℂ] Carrier a b Φ₀ :=
  (toL2 ω a b Φ₀).comp (cuspMemberSubmodule ω a b Φ₀).subtype

private theorem classOf_apply (f : ↥(cuspMemberSubmodule ω a b Φ₀)) :
    classOf f = toL2 ω a b Φ₀ (f : ↥(automorphicSubmodule ω a b Φ₀)) :=
  rfl

private theorem isDenseIsometricAction (hR : RightTranslationLaw ω a b Φ₀) :
    DenseUnitaryExtension.IsDenseIsometricAction (G := AdelicGL 3 (𝓞 ℚ) ℚ) (C := ↥(cuspMemberSubmodule ω a b Φ₀))
      (Hc := Carrier a b Φ₀) classOf (cuspidalSubspace ω a b Φ₀) (act hR) where
  mem f := toL2_mem_cuspidalSubspace ω a b Φ₀ f.2
  dense := by
    rw [cuspidalSubspace_def, Submodule.topologicalClosure_coe, classOf, LinearMap.range_comp,
      Submodule.range_subtype, Submodule.span_image, span_cuspMembers]
  norm_eq g f := (hR _ f.2).snd.1 g
  cont f := (hR _ f.2).snd.2

private def rbar (hR : RightTranslationLaw ω a b Φ₀) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀) :=
  (isDenseIsometricAction hR).U g

private theorem rbar_toL2 (hR : RightTranslationLaw ω a b Φ₀) (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀) :
    (rbar hR g ⟨toL2 ω a b Φ₀ ⟨F, hF.1⟩, toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hF⟩ :
        Carrier a b Φ₀) = toL2 ω a b Φ₀ ⟨translateRight g F, ((hR F hF).fst g).1⟩ := by
  have h := (isDenseIsometricAction hR).U_gen g ⟨⟨F, hF.1⟩, hF⟩
  exact congrArg Subtype.val h

private theorem rbar_one (hR : RightTranslationLaw ω a b Φ₀) : rbar hR 1 = ContinuousLinearMap.id ℂ _ :=
  (isDenseIsometricAction hR).U_one

private theorem rbar_mul (hR : RightTranslationLaw ω a b Φ₀) (g g' : AdelicGL 3 (𝓞 ℚ) ℚ) :
    rbar hR (g * g') = (rbar hR g).comp (rbar hR g') :=
  (isDenseIsometricAction hR).U_mul g g'

private theorem norm_rbar (hR : RightTranslationLaw ω a b Φ₀) (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (x : ↥(cuspidalSubspace ω a b Φ₀)) : ‖rbar hR g x‖ = ‖x‖ :=
  (isDenseIsometricAction hR).norm_U g x

private theorem adjoint_rbar (hR : RightTranslationLaw ω a b Φ₀) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ContinuousLinearMap.adjoint (rbar hR g) = rbar hR g⁻¹ :=
  (isDenseIsometricAction hR).adjoint_U g

private theorem continuous_rbar_apply (hR : RightTranslationLaw ω a b Φ₀) (x : ↥(cuspidalSubspace ω a b Φ₀)) :
    Continuous fun g => rbar hR g x :=
  (isDenseIsometricAction hR).continuous_U_apply x

section WeakForm

open MeasureTheory

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

variable (ω a b Φ₀)
variable (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)

private def WeakInterchangeLaw : Prop :=
  ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (_hF : F ∈ cuspFunctions ω a b Φ₀)
    (hmem : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, translateRight g F ∈ cuspFunctions ω a b Φ₀)
    (hRF : smoothingOperator φ F ∈ automorphicSubmodule ω a b Φ₀) (h : Carrier a b Φ₀),
    ⟪h, toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hRF⟩⟫_ℂ =
      ∫ g, φ g * ⟪h, toL2 ω a b Φ₀ ⟨translateRight g F, (hmem g).1⟩⟫_ℂ
        ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)

private def AgreesWithSmoothing (T : ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀)) : Prop :=
  ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀),
    ∃ hRF : smoothingOperator φ F ∈ cuspFunctions ω a b Φ₀,
      (T ⟨toL2 ω a b Φ₀ ⟨F, hF.1⟩, toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hF⟩ :
          Carrier a b Φ₀) = toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hRF.1⟩

variable {ω a b Φ₀ φ}

private theorem continuous_inner_rbar (hR : RightTranslationLaw ω a b Φ₀) (h : Carrier a b Φ₀)
    (c : ↥(cuspidalSubspace ω a b Φ₀)) : Continuous fun g => ⟪h, (rbar hR g c : Carrier a b Φ₀)⟫_ℂ :=
  continuous_const.inner (continuous_subtype_val.comp (continuous_rbar_apply hR c))

private theorem norm_inner_rbar_le (hR : RightTranslationLaw ω a b Φ₀) (h : Carrier a b Φ₀)
    (c : ↥(cuspidalSubspace ω a b Φ₀)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ‖⟪h, (rbar hR g c : Carrier a b Φ₀)⟫_ℂ‖ ≤ ‖h‖ * ‖c‖ := by
  refine (norm_inner_le_norm _ _).trans (le_of_eq ?_)
  rw [norm_coe, norm_rbar]

private theorem integrable_mul_inner_rbar (hR : RightTranslationLaw ω a b Φ₀)
    (hφ : Integrable φ (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)) (h : Carrier a b Φ₀)
    (c : ↥(cuspidalSubspace ω a b Φ₀)) :
    Integrable (fun g => φ g * ⟪h, (rbar hR g c : Carrier a b Φ₀)⟫_ℂ)
      (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) :=
  hφ.mul_bdd (continuous_inner_rbar hR h c).aestronglyMeasurable
    (Filter.Eventually.of_forall fun g => norm_inner_rbar_le hR h c g)

private def weakFunctional (hR : RightTranslationLaw ω a b Φ₀)
    (hφ : Integrable φ (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)) (h : Carrier a b Φ₀) :
    ↥(cuspidalSubspace ω a b Φ₀) →ₗ[ℂ] ℂ where
  toFun c := ∫ g, φ g * ⟪h, (rbar hR g c : Carrier a b Φ₀)⟫_ℂ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)
  map_add' c c' := by
    rw [← integral_add (integrable_mul_inner_rbar hR hφ h c) (integrable_mul_inner_rbar hR hφ h c')]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [map_add, Submodule.coe_add, inner_add_right, mul_add]
  map_smul' s c := by
    rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [map_smul, Submodule.coe_smul, inner_smul_right]
    ring

private theorem weakFunctional_apply (hR : RightTranslationLaw ω a b Φ₀)
    (hφ : Integrable φ (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)) (h : Carrier a b Φ₀)
    (c : ↥(cuspidalSubspace ω a b Φ₀)) :
    weakFunctional hR hφ h c =
      ∫ g, φ g * ⟪h, (rbar hR g c : Carrier a b Φ₀)⟫_ℂ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) :=
  rfl

private theorem norm_weakFunctional_le (hR : RightTranslationLaw ω a b Φ₀)
    (hφ : Integrable φ (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)) (h : Carrier a b Φ₀)
    (c : ↥(cuspidalSubspace ω a b Φ₀)) :
    ‖weakFunctional hR hφ h c‖ ≤
      ((∫ g, ‖φ g‖ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)) * ‖h‖) * ‖c‖ := by
  rw [weakFunctional_apply, mul_assoc, ← integral_mul_const]
  refine norm_integral_le_of_norm_le (hφ.norm.mul_const _) (Filter.Eventually.of_forall fun g => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_inner_rbar_le hR h c g) (norm_nonneg _)

private theorem continuous_weakFunctional (hR : RightTranslationLaw ω a b Φ₀)
    (hφ : Integrable φ (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)) (h : Carrier a b Φ₀) :
    Continuous (weakFunctional hR hφ h) :=
  AddMonoidHomClass.continuous_of_bound (weakFunctional hR hφ h) _ (norm_weakFunctional_le hR hφ h)

private theorem inner_apply_eq_integral (hR : RightTranslationLaw ω a b Φ₀) (hX : WeakInterchangeLaw ω a b Φ₀ φ)
    (hφ : Integrable φ (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    {T : ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀)} (hT : AgreesWithSmoothing ω a b Φ₀ φ T)
    (h : Carrier a b Φ₀) (c : ↥(cuspidalSubspace ω a b Φ₀)) :
    ⟪h, (T c : Carrier a b Φ₀)⟫_ℂ =
      ∫ g, φ g * ⟪h, (rbar hR g c : Carrier a b Φ₀)⟫_ℂ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
  have hd := (isDenseIsometricAction hR).denseRange_gen
  have key : (fun c : ↥(cuspidalSubspace ω a b Φ₀) => ⟪h, (T c : Carrier a b Φ₀)⟫_ℂ) =
      fun c => weakFunctional hR hφ h c := by
    refine hd.equalizer (continuous_const.inner (continuous_subtype_val.comp T.continuous))
      (continuous_weakFunctional hR hφ h) ?_
    funext f
    obtain ⟨hRF, hTF⟩ := hT (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) f.2
    simp only [Function.comp_apply, weakFunctional_apply]
    rw [show (isDenseIsometricAction hR).gen f =
        ⟨toL2 ω a b Φ₀ ⟨(f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), f.2.1⟩,
          toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ f.2⟩ from rfl, hTF,
      hX (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) f.2 (hR _ f.2).fst hRF.1 h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    dsimp only
    rw [rbar_toL2 hR g (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) f.2]
  exact congrFun key c

private theorem
    apply_mem_of_forall_rbar_apply_mem (hR : RightTranslationLaw ω a b Φ₀) (hX : WeakInterchangeLaw ω a b Φ₀ φ)
    (hφ : Integrable φ (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    {T : ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀)} (hT : AgreesWithSmoothing ω a b Φ₀ φ T)
    {W : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀)} (hWc : IsClosed (W : Set ↥(cuspidalSubspace ω a b Φ₀)))
    (hW : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ∀ x ∈ W, rbar hR g x ∈ W) {c : ↥(cuspidalSubspace ω a b Φ₀)} (hc : c ∈ W) :
    T c ∈ W := by
  haveI : CompleteSpace W := hWc.isComplete.completeSpace_coe
  rw [← Submodule.orthogonal_orthogonal W, Submodule.mem_orthogonal]
  intro u hu
  rw [Submodule.coe_inner, inner_apply_eq_integral hR hX hφ hT]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun g => ?_)
  show φ g * ⟪(u : Carrier a b Φ₀), (rbar hR g c : Carrier a b Φ₀)⟫_ℂ = 0
  have h0 : ⟪(u : Carrier a b Φ₀), (rbar hR g c : Carrier a b Φ₀)⟫_ℂ = 0 := by
    rw [← Submodule.coe_inner]
    exact Submodule.inner_left_of_mem_orthogonal (hW g c hc) hu
  rw [h0, mul_zero]

private theorem adjoint_mem_range_rbar (hR : RightTranslationLaw ω a b Φ₀)
    {r : ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀)} (hr : r ∈ Set.range (rbar hR)) :
    ContinuousLinearMap.adjoint r ∈ Set.range (rbar hR) := by
  obtain ⟨g, rfl⟩ := hr
  exact ⟨g⁻¹, (adjoint_rbar hR g).symm⟩

end WeakForm
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction"

section NonVanishing

open MeasureTheory Filter Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

private def HasApproximateIdentity : Prop :=
  ∀ U ∈ 𝓝 (1 : AdelicGL 3 (𝓞 ℚ) ℚ), ∃ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
    IsSmoothingKernel φ ∧ (∀ g, φ g = ((φ g).re : ℂ) ∧ 0 ≤ (φ g).re) ∧ Function.support φ ⊆ U ∧
      Integrable φ (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) ∧
        0 < (∫ g, φ g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)).re

private theorem exists_isSmoothingKernel_forall_apply_ne_zero (hR : RightTranslationLaw ω a b Φ₀)
    (hS : HasApproximateIdentity) {c : ↥(cuspidalSubspace ω a b Φ₀)} (hc : c ≠ 0) :
    ∃ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ ∧
      Integrable φ (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) ∧
        ∀ T : ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀),
          AgreesWithSmoothing ω a b Φ₀ φ T → WeakInterchangeLaw ω a b Φ₀ φ → T c ≠ 0 := by
  set k : ℝ := ‖c‖ ^ 2 / 2 with hk
  set U : Set (AdelicGL 3 (𝓞 ℚ) ℚ) :=
    {g | k < (⟪(c : Carrier a b Φ₀), (rbar hR g c : Carrier a b Φ₀)⟫_ℂ).re} with hU
  have hUo : IsOpen U :=
    isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_inner_rbar hR (c : Carrier a b Φ₀) c))
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hk0 : 0 < k := by rw [hk]; positivity
  have hcc : (⟪(c : Carrier a b Φ₀), (c : Carrier a b Φ₀)⟫_ℂ).re = ‖c‖ ^ 2 := by
    rw [← RCLike.re_to_complex, inner_self_eq_norm_sq, norm_coe]
  have h1U : (1 : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ U := by
    show k < _
    rw [rbar_one, ContinuousLinearMap.id_apply, hcc, hk]
    linarith [pow_pos hcn 2]
  obtain ⟨φ, hφk, hφre, hφU, hφi, hφpos⟩ := hS U (hUo.mem_nhds h1U)
  have him : ∀ g, (φ g).im = 0 := fun g => by rw [(hφre g).1, Complex.ofReal_im]
  refine ⟨φ, hφk, hφi, fun T hT hX hTc => ?_⟩
  have key := inner_apply_eq_integral hR hX hφi hT (c : Carrier a b Φ₀) c
  rw [hTc, Submodule.coe_zero, inner_zero_right] at key

  have hint := integrable_mul_inner_rbar hR hφi (c : Carrier a b Φ₀) c
  have hpt : ∀ g, 0 ≤ (φ g * ⟪(c : Carrier a b Φ₀), (rbar hR g c : Carrier a b Φ₀)⟫_ℂ - (k : ℂ) * φ g).re := by
    intro g
    by_cases hg : φ g = 0
    · simp [hg]
    · have hgU : g ∈ U := hφU (Function.mem_support.mpr hg)
      have hlt : k < (⟪(c : Carrier a b Φ₀), (rbar hR g c : Carrier a b Φ₀)⟫_ℂ).re := hgU
      rw [Complex.sub_re, Complex.mul_re, him g, zero_mul, sub_zero, Complex.re_ofReal_mul]
      nlinarith [(hφre g).2, hlt]
  have hsplit : (∫ g, φ g * ⟪(c : Carrier a b Φ₀), (rbar hR g c : Carrier a b Φ₀)⟫_ℂ
      ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)) =
      (∫ g, (φ g * ⟪(c : Carrier a b Φ₀), (rbar hR g c : Carrier a b Φ₀)⟫_ℂ - (k : ℂ) * φ g)
        ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)) +
        (k : ℂ) * ∫ g, φ g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
    rw [integral_sub hint (hφi.const_mul _), integral_const_mul, sub_add_cancel]
  have hnonneg : 0 ≤ (∫ g, (φ g * ⟪(c : Carrier a b Φ₀), (rbar hR g c : Carrier a b Φ₀)⟫_ℂ - (k : ℂ) * φ g)
      ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)).re := by
    have h1 := integral_re (hint.sub' (hφi.const_mul (k : ℂ)))
    simp only [RCLike.re_to_complex] at h1
    rw [← h1]
    exact integral_nonneg fun g => hpt g
  have hre := congrArg Complex.re key
  rw [hsplit, Complex.add_re, Complex.re_ofReal_mul, Complex.zero_re] at hre
  nlinarith [hnonneg, mul_pos hk0 hφpos]

end NonVanishing
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction"

section ClassToFunction

open MeasureTheory NumberField.TateGlobal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

private def SlabInvarianceLaw (a b : ℝ) : Prop :=
  ∀ γ : Matrix.GeneralLinearGroup (Fin 3) ℚ,
    MeasurePreserving
      (fun g : LanglandsTunnell.CubicInduction.AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ =>
        LanglandsTunnell.CubicInduction.globalPointsGL 3 (NumberField.RingOfIntegers ℚ) ℚ γ * g)
      ((NumberField.AdelicHaar.adelicGLHaar (Fin 3) (NumberField.RingOfIntegers ℚ) ℚ).restrict
        {g | NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b})
      ((NumberField.AdelicHaar.adelicGLHaar (Fin 3) (NumberField.RingOfIntegers ℚ) ℚ).restrict
        {g | NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b})

private theorem continuous_ideleNorm_det_gl3 :
    Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) := by
  refine (continuous_ideleNorm ℚ).comp (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · exact Units.continuous_val.matrix_det.congr fun g => (Matrix.GeneralLinearGroup.val_det_apply g).symm
  · exact Units.continuous_coe_inv.matrix_det.congr fun g => by
      rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]

private theorem ideleNorm_det_scalar (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ideleNorm ℚ (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 3) z : AdelicGL 3 (𝓞 ℚ) ℚ))
      = ideleNorm ℚ z ^ 3 := by
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, pow_three' z, ideleNorm_mul, ideleNorm_mul,
    pow_three' (ideleNorm ℚ z)]

private theorem apply_subgroup_smul_of_mem_automorphicSubmodule {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hF : F ∈ automorphicSubmodule ω a b Φ₀) (γ : (globalPointsGL 3 (𝓞 ℚ) ℚ).range) (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    F (γ • x) = F x := by
  obtain ⟨q, hq⟩ := MonoidHom.mem_range.mp γ.2
  show F ((γ : AdelicGL 3 (𝓞 ℚ) ℚ) * x) = F x
  rw [← hq]
  exact hF.1 q x

private theorem slabMeasure_setOf_ne_eq_zero (hΦ₀ : IsSlabDomain a b Φ₀) (hI : SlabInvarianceLaw a b)
    {F F' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : F ∈ automorphicSubmodule ω a b Φ₀) (hF' : F' ∈ automorphicSubmodule ω a b Φ₀)
    (h : toL2 ω a b Φ₀ ⟨F, hF⟩ = toL2 ω a b Φ₀ ⟨F', hF'⟩) : slabMeasure a b {x | F x ≠ F' x} = 0 := by
  haveI : Countable (Matrix (Fin 3) (Fin 3) ℚ) := inferInstanceAs (Countable (Fin 3 → Fin 3 → ℚ))
  haveI : Countable (Matrix.GeneralLinearGroup (Fin 3) ℚ) := Units.val_injective.countable
  haveI : Countable (globalPointsGL 3 (𝓞 ℚ) ℚ).range := (Set.countable_range _).to_subtype
  haveI : MeasurableConstSMul (globalPointsGL 3 (𝓞 ℚ) ℚ).range (AdelicGL 3 (𝓞 ℚ) ℚ) :=
    ⟨fun γ => (continuous_const.mul continuous_id :
      Continuous fun x : AdelicGL 3 (𝓞 ℚ) ℚ => (γ : AdelicGL 3 (𝓞 ℚ) ℚ) * x).measurable⟩
  haveI : SMulInvariantMeasure (globalPointsGL 3 (𝓞 ℚ) ℚ).range (AdelicGL 3 (𝓞 ℚ) ℚ) (slabMeasure a b) :=
    ⟨fun γ s hs => by
      obtain ⟨q, hq⟩ := MonoidHom.mem_range.mp γ.2
      change slabMeasure a b ((fun x : AdelicGL 3 (𝓞 ℚ) ℚ => (γ : AdelicGL 3 (𝓞 ℚ) ℚ) * x) ⁻¹' s) = slabMeasure a b s
      rw [← hq]
      exact (hI q).measure_preimage hs.nullMeasurableSet⟩
  have hae : F =ᵐ[domainMeasure a b Φ₀] F' := by
    rw [toL2_apply, toL2_apply] at h
    exact (MemLp.toLp_eq_toLp_iff hF.2.2 hF'.2.2).mp h
  have h0 : (slabMeasure a b).restrict Φ₀ {x | F x ≠ F' x} = 0 := by
    rw [domainMeasure_def] at hae
    exact ae_iff.mp hae
  rw [Measure.restrict_apply₀' hΦ₀.isFundamentalDomain.nullMeasurableSet] at h0
  refine hΦ₀.isFundamentalDomain.measure_zero_of_invariant _ (fun γ => ?_) h0
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_setOf_eq, Set.mem_setOf_eq,
    apply_subgroup_smul_of_mem_automorphicSubmodule hF, apply_subgroup_smul_of_mem_automorphicSubmodule hF']

private theorem eq_of_toL2_eq (hΦ₀ : IsSlabDomain a b Φ₀) (hI : SlabInvarianceLaw a b) {F F' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hF : F ∈ cuspFunctions ω a b Φ₀) (hF' : F' ∈ cuspFunctions ω a b Φ₀)
    (h : toL2 ω a b Φ₀ ⟨F, hF.1⟩ = toL2 ω a b Φ₀ ⟨F', hF'.1⟩) : F = F' := by
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  have hT := slabMeasure_setOf_ne_eq_zero hΦ₀ hI hF.1 hF'.1 h

  set O : Set (AdelicGL 3 (𝓞 ℚ) ℚ) := {g | ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Ioo a b} with hO
  have hOo : IsOpen O := isOpen_Ioo.preimage continuous_ideleNorm_det_gl3
  have hOsub : O ⊆ ideleNormDetSlab a b := fun g hg => Set.Ioo_subset_Icc_self hg
  have hopen : IsOpen ({x | F x ≠ F' x} ∩ O) := (isOpen_ne_fun hF.2.1 hF'.2.1).inter hOo
  have hzero : NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ ({x | F x ≠ F' x} ∩ O) = 0 := by
    refine le_antisymm ?_ zero_le
    have hslab : MeasurableSet (ideleNormDetSlab a b) :=
      measurableSet_Icc.preimage continuous_ideleNorm_det_gl3.measurable
    calc NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ ({x | F x ≠ F' x} ∩ O)
        = NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ (({x | F x ≠ F' x} ∩ O) ∩ ideleNormDetSlab a b) := by
          rw [Set.inter_eq_left.mpr (Set.inter_subset_right.trans hOsub)]
      _ = slabMeasure a b ({x | F x ≠ F' x} ∩ O) := by
          rw [slabMeasure_def, Measure.restrict_apply' hslab]
      _ ≤ slabMeasure a b {x | F x ≠ F' x} := measure_mono Set.inter_subset_left
      _ = 0 := hT
  have hempty := (hopen.measure_eq_zero_iff _).mp hzero
  have hOeq : ∀ g ∈ O, F g = F' g := fun g hg => by
    by_contra hne
    have hmem : g ∈ ({x | F x ≠ F' x} ∩ O) := ⟨hne, hg⟩
    rw [hempty] at hmem
    exact hmem

  funext g
  have hd := ideleNorm_pos (Matrix.GeneralLinearGroup.det g)
  have ha := hΦ₀.pos
  have hab := hΦ₀.lt
  have hc₀ : 0 < (a + b) / 2 := by linarith
  set t : ℝ := (((a + b) / 2) / ideleNorm ℚ (Matrix.GeneralLinearGroup.det g)) ^ (((3 : ℕ) : ℝ)⁻¹) with htdef
  have ht : 0 < t := Real.rpow_pos_of_pos (div_pos hc₀ hd) _
  have ht3 : t ^ 3 = ((a + b) / 2) / ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) :=
    Real.rpow_inv_natCast_pow (div_pos hc₀ hd).le (by norm_num)
  obtain ⟨z, -, hz⟩ := exists_ideleNorm_eq_and_snd_eq_one ℚ t ht
  have hzg : centralScalarGL 3 (𝓞 ℚ) ℚ z * g ∈ O := by
    show ideleNorm ℚ (Matrix.GeneralLinearGroup.det (centralScalarGL 3 (𝓞 ℚ) ℚ z * g)) ∈ Set.Ioo a b
    rw [map_mul, ideleNorm_mul,
      show centralScalarGL 3 (𝓞 ℚ) ℚ z = Matrix.GeneralLinearGroup.scalar (Fin 3) z from rfl, ideleNorm_det_scalar,
      hz, ht3, div_mul_cancel₀ _ hd.ne']
    exact ⟨by linarith, by linarith⟩
  have key := hOeq _ hzg
  rw [hF.1.2.1 z g, hF'.1.2.1 z g] at key
  exact mul_left_cancel₀ (Units.ne_zero _) key

private theorem toL2_ne_zero_of_ne_zero (hΦ₀ : IsSlabDomain a b Φ₀) (hI : SlabInvarianceLaw a b)
    {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : F ∈ cuspFunctions ω a b Φ₀) (h0 : F ≠ 0) : toL2 ω a b Φ₀ ⟨F, hF.1⟩ ≠ 0 := by
  intro h
  have hz : (0 : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) ∈ cuspFunctions ω a b Φ₀ := (cuspSubmodule ω a b Φ₀).zero_mem
  refine h0 (eq_of_toL2_eq hΦ₀ hI hF hz ?_)
  rw [h, ← (toL2 ω a b Φ₀).map_zero]
  rfl

end ClassToFunction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction"

section EntryNonVanishing

open MeasureTheory Filter Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

local notation "μGL" => NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ

private def SmoothingKernelLaw : Prop :=
  ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → Continuous φ ∧ HasCompactSupport φ

private theorem exists_isSmoothingKernel_smoothingOperator_apply_ne_zero (hS : HasApproximateIdentity)
    (hSK : SmoothingKernelLaw) {f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hf : Continuous f) {g₀ : AdelicGL 3 (𝓞 ℚ) ℚ}
    (h0 : f g₀ ≠ 0) : ∃ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ ∧ smoothingOperator φ f g₀ ≠ 0 := by
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  set k : ℝ := ‖f g₀‖ / 2 with hk
  have hn : 0 < ‖f g₀‖ := norm_pos_iff.mpr h0
  have hk0 : 0 < k := by rw [hk]; exact half_pos hn
  set U : Set (AdelicGL 3 (𝓞 ℚ) ℚ) := {g | ‖f (g₀ * g) - f g₀‖ < k} with hU
  have hfc : Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => f (g₀ * g) := hf.comp (continuous_const.mul continuous_id)
  have hUo : IsOpen U := isOpen_lt (hfc.sub continuous_const).norm continuous_const
  have h1U : (1 : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ U := by
    show ‖f (g₀ * 1) - f g₀‖ < k
    rw [mul_one, sub_self, norm_zero]
    exact hk0
  obtain ⟨φ, hφk, hφre, hφU, hφi, hφpos⟩ := hS U (hUo.mem_nhds h1U)
  obtain ⟨hφc, hφcs⟩ := hSK φ hφk
  refine ⟨φ, hφk, fun hzero => ?_⟩
  have hFi : Integrable (fun g => φ g * f (g₀ * g)) μGL :=
    (hφc.mul hfc).integrable_of_hasCompactSupport (hφcs.mul_right (f' := fun g => f (g₀ * g)))
  have hsplit : (∫ g, φ g * f (g₀ * g) ∂μGL) =
      (∫ g, φ g * (f (g₀ * g) - f g₀) ∂μGL) + (∫ g, φ g ∂μGL) * f g₀ := by
    have hfun : (fun g => φ g * (f (g₀ * g) - f g₀)) = fun g => φ g * f (g₀ * g) - φ g * f g₀ := by
      funext g
      ring
    rw [hfun, integral_sub hFi (hφi.mul_const _), integral_mul_const]
    ring
  have hre_int : (∫ g, φ g ∂μGL).re = ∫ g, ‖φ g‖ ∂μGL := by
    rw [← RCLike.re_to_complex, ← integral_re hφi]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    simp only [RCLike.re_to_complex]
    rw [(hφre g).1, Complex.ofReal_re, Complex.norm_of_nonneg (hφre g).2]
  have hbound : ‖∫ g, φ g * (f (g₀ * g) - f g₀) ∂μGL‖ ≤ (∫ g, φ g ∂μGL).re * k := by
    rw [hre_int, ← integral_mul_const]
    refine norm_integral_le_of_norm_le (hφi.norm.mul_const _) (Eventually.of_forall fun g => ?_)
    rw [norm_mul]
    by_cases hg : φ g = 0
    · simp [hg]
    · exact mul_le_mul_of_nonneg_left
        (le_of_lt (hφU (Function.mem_support.mpr hg) : ‖f (g₀ * g) - f g₀‖ < k)) (norm_nonneg _)
  have hm : 0 < (∫ g, φ g ∂μGL).re := hφpos
  rw [smoothingOperator_apply, hsplit] at hzero
  have hE : (∫ g, φ g ∂μGL) * f g₀ = -∫ g, φ g * (f (g₀ * g) - f g₀) ∂μGL :=
    eq_neg_of_add_eq_zero_right hzero
  have h1 : ‖(∫ g, φ g ∂μGL) * f g₀‖ ≤ (∫ g, φ g ∂μGL).re * k := by
    rw [hE, norm_neg]
    exact hbound
  have h2 : (∫ g, φ g ∂μGL).re * ‖f g₀‖ ≤ ‖(∫ g, φ g ∂μGL) * f g₀‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (Complex.re_le_norm _) (norm_nonneg _)
  have h3 : (∫ g, φ g ∂μGL).re * k = (∫ g, φ g ∂μGL).re * ‖f g₀‖ / 2 := by
    rw [hk]
    ring
  nlinarith [h1, h2, h3, mul_pos hm hn]

end EntryNonVanishing
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction"

section ClassToData

open MeasureTheory Filter Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

private def cuspClass {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : F ∈ cuspFunctions ω a b Φ₀) : ↥(cuspidalSubspace ω a b Φ₀) :=
  ⟨toL2 ω a b Φ₀ ⟨F, hF.1⟩, toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hF⟩

private theorem coe_cuspClass {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : F ∈ cuspFunctions ω a b Φ₀) :
    (cuspClass hF : Carrier a b Φ₀) = toL2 ω a b Φ₀ ⟨F, hF.1⟩ :=
  rfl

private theorem isRightInvariant_of_forall_rbar_eq (hΦ₀ : IsSlabDomain a b Φ₀) (hI : SlabInvarianceLaw a b)
    (hR : RightTranslationLaw ω a b Φ₀) {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : F ∈ cuspFunctions ω a b Φ₀)
    (U : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ)) (hU : ∀ u ∈ U, rbar hR u (cuspClass hF) = cuspClass hF) :
    IsRightInvariant U F := by
  intro g u hu
  have hcls : toL2 ω a b Φ₀ ⟨translateRight u F, ((hR F hF).fst u).1⟩ = toL2 ω a b Φ₀ ⟨F, hF.1⟩ := by
    rw [← rbar_toL2 hR u F hF]
    exact congrArg Subtype.val (hU u hu)
  exact congrFun (eq_of_toL2_eq hΦ₀ hI ((hR F hF).fst u) hF hcls) g

private theorem cosetSum_eq_of_sum_rbar_eq (hΦ₀ : IsSlabDomain a b Φ₀) (hI : SlabInvarianceLaw a b)
    (hR : RightTranslationLaw ω a b Φ₀) {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : F ∈ cuspFunctions ω a b Φ₀)
    {ι : Type} [Fintype ι] (reps : ι → AdelicGL 3 (𝓞 ℚ) ℚ) (lam : ℂ)
    (h : ∑ i, rbar hR (reps i) (cuspClass hF) = lam • cuspClass hF) :
    cosetSum reps F = fun g => lam * F g := by
  have hfun : cosetSum reps F = ∑ i, translateRight (reps i) F := by
    funext g
    simp only [cosetSum, Finset.sum_apply, translateRight_apply]
  have hmemi : ∀ i, translateRight (reps i) F ∈ cuspFunctions ω a b Φ₀ := fun i => (hR F hF).fst (reps i)
  have hsum_mem : (∑ i, translateRight (reps i) F) ∈ cuspFunctions ω a b Φ₀ :=
    (cuspSubmodule ω a b Φ₀).sum_mem fun i _ => hmemi i
  have hlam_mem : (fun g => lam * F g) ∈ cuspFunctions ω a b Φ₀ := (cuspSubmodule ω a b Φ₀).smul_mem lam hF
  rw [hfun]
  refine eq_of_toL2_eq hΦ₀ hI hsum_mem hlam_mem ?_
  have hL : (⟨∑ i, translateRight (reps i) F, hsum_mem.1⟩ : ↥(automorphicSubmodule ω a b Φ₀)) =
      ∑ i, ⟨translateRight (reps i) F, (hmemi i).1⟩ := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
  have hRHS : (⟨fun g => lam * F g, hlam_mem.1⟩ : ↥(automorphicSubmodule ω a b Φ₀)) = lam • ⟨F, hF.1⟩ :=
    Subtype.ext rfl
  rw [hL, hRHS, map_sum, map_smul]
  have h' := congrArg Subtype.val h
  rw [Submodule.coe_sum, Submodule.coe_smul] at h'
  simp_rw [cuspClass, rbar_toL2 hR _ F hF] at h'
  exact h'

private theorem apply_comm_of_forall_rbar_comm (hR : RightTranslationLaw ω a b Φ₀) {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hX : WeakInterchangeLaw ω a b Φ₀ φ) (hφ : Integrable φ (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    {T : ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀)} (hT : AgreesWithSmoothing ω a b Φ₀ φ T)
    (P : ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀))
    (hPadj : ∀ x y : ↥(cuspidalSubspace ω a b Φ₀), ⟪P x, y⟫_ℂ = ⟪x, P y⟫_ℂ)
    (hP : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (x : ↥(cuspidalSubspace ω a b Φ₀)), P (rbar hR g x) = rbar hR g (P x))
    (c : ↥(cuspidalSubspace ω a b Φ₀)) : P (T c) = T (P c) := by
  refine ext_inner_left ℂ fun v => ?_
  rw [← hPadj, Submodule.coe_inner, Submodule.coe_inner, inner_apply_eq_integral hR hX hφ hT,
    inner_apply_eq_integral hR hX hφ hT]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  show φ g * _ = φ g * _
  rw [← Submodule.coe_inner, ← Submodule.coe_inner, hPadj, hP]

end ClassToData
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction"

end LanglandsTunnell.CubicInduction.CuspClassAction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction"

end ClassActionBlock
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction"

section HilbertConstituentBlock

noncomputable section

open Submodule Module.End ContinuousLinearMap
open scoped InnerProductSpace

namespace HilbertConstituent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private def IsInvariant (R : Set (H →L[ℂ] H)) (W : Submodule ℂ H) : Prop :=
  ∀ r ∈ R, ∀ x ∈ W, r x ∈ W

private def IsAdjointClosed (R : Set (H →L[ℂ] H)) : Prop :=
  ∀ r ∈ R, ContinuousLinearMap.adjoint r ∈ R

private def IsIrreducible (R : Set (H →L[ℂ] H)) (V : Submodule ℂ H) : Prop :=
  IsClosed (V : Set H) ∧ IsInvariant R V ∧ V ≠ ⊥ ∧
    ∀ W : Submodule ℂ H, IsClosed (W : Set H) → IsInvariant R W → W ≤ V → W = ⊥ ∨ W = V

variable {R : Set (H →L[ℂ] H)}

private theorem isInvariant_orthogonal (hR : IsAdjointClosed R) {W : Submodule ℂ H} (hW : IsInvariant R W) :
    IsInvariant R Wᗮ := by
  intro r hr x hx
  rw [mem_orthogonal] at hx ⊢
  intro u hu
  rw [← adjoint_inner_left]
  exact hx _ (hW _ (hR r hr) u hu)

omit [CompleteSpace H] in
private theorem isInvariant_inf {W W' : Submodule ℂ H} (hW : IsInvariant R W) (hW' : IsInvariant R W') :
    IsInvariant R (W ⊓ W') :=
  fun r hr x hx => mem_inf.2 ⟨hW r hr x (mem_inf.1 hx).1, hW' r hr x (mem_inf.1 hx).2⟩

private theorem starProjection_apply_comm (hR : IsAdjointClosed R) {V : Submodule ℂ H} [V.HasOrthogonalProjection]
    (hV : IsInvariant R V) {r : H →L[ℂ] H} (hr : r ∈ R) (x : H) :
    V.starProjection (r x) = r (V.starProjection x) := by
  apply eq_starProjection_of_mem_orthogonal (hV r hr _ (starProjection_apply_mem V x))
  rw [← map_sub]
  exact isInvariant_orthogonal hR hV r hr _ (sub_starProjection_mem_orthogonal x)

private def generated (R : Set (H →L[ℂ] H)) (x : H) : Submodule ℂ H :=
  sInf {W | IsClosed (W : Set H) ∧ IsInvariant R W ∧ x ∈ W}

omit [CompleteSpace H] in
private theorem mem_generated (x : H) : x ∈ generated R x := by
  rw [generated, mem_sInf]
  exact fun W hW => hW.2.2

omit [CompleteSpace H] in
private theorem generated_le {x : H} {W : Submodule ℂ H} (hWc : IsClosed (W : Set H)) (hWi : IsInvariant R W)
    (hx : x ∈ W) : generated R x ≤ W :=
  sInf_le ⟨hWc, hWi, hx⟩

omit [CompleteSpace H] in
private theorem isClosed_generated (x : H) : IsClosed (generated R x : Set H) := by
  rw [generated, coe_sInf]
  exact isClosed_biInter fun W hW => hW.1

omit [CompleteSpace H] in
private theorem isInvariant_generated (x : H) : IsInvariant R (generated R x) := by
  intro r hr y hy
  rw [generated, mem_sInf] at hy ⊢
  exact fun W hW => hW.2.1 r hr y (hy W hW)

private theorem isSymmetric_adjoint_comp (A : H →L[ℂ] H) : ((adjoint A).comp A : H →ₗ[ℂ] H).IsSymmetric := by
  intro x y
  simp only [coe_coe, comp_apply, adjoint_inner_left, adjoint_inner_right]

private theorem adjoint_comp_apply_eq_zero_iff (A : H →L[ℂ] H) (x : H) : (adjoint A).comp A x = 0 ↔ A x = 0 := by
  constructor
  · intro h
    have h' : ⟪adjoint A (A x), x⟫_ℂ = 0 := by rw [← comp_apply, h, inner_zero_left]
    rwa [adjoint_inner_left, inner_self_eq_zero] at h'
  · intro h
    rw [comp_apply, h, map_zero]

private theorem adjoint_apply_mem (hR : IsAdjointClosed R) (A : H →L[ℂ] H)
    (hA : ∀ W : Submodule ℂ H, IsClosed (W : Set H) → IsInvariant R W → ∀ x ∈ W, A x ∈ W)
    {W : Submodule ℂ H} (hWc : IsClosed (W : Set H)) (hWi : IsInvariant R W) {y : H} (hy : y ∈ W) :
    adjoint A y ∈ W := by
  haveI : CompleteSpace W := hWc.isComplete.completeSpace_coe
  rw [← orthogonal_orthogonal W, mem_orthogonal]
  intro u hu
  rw [adjoint_inner_right]
  exact inner_left_of_mem_orthogonal hy (hA Wᗮ (isClosed_orthogonal W) (isInvariant_orthogonal hR hWi) u hu)

private theorem exists_isIrreducible_le (hR : IsAdjointClosed R) (A : H →L[ℂ] H) (hAc : IsCompactOperator A)
    (hA : ∀ W : Submodule ℂ H, IsClosed (W : Set H) → IsInvariant R W → ∀ x ∈ W, A x ∈ W)
    {W : Submodule ℂ H} (hWc : IsClosed (W : Set H)) (hWi : IsInvariant R W) (hAW : ∃ x ∈ W, A x ≠ 0) :
    ∃ V ≤ W, IsIrreducible R V := by
  classical
  haveI : CompleteSpace W := hWc.isComplete.completeSpace_coe

  have hTc : IsCompactOperator ((adjoint A).comp A) := hAc.clm_comp (adjoint A)
  have hTinv : ∀ W' : Submodule ℂ H, IsClosed (W' : Set H) → IsInvariant R W' →
      ∀ x ∈ W', (adjoint A).comp A x ∈ W' :=
    fun W' h1 h2 x hx => adjoint_apply_mem hR A hA h1 h2 (hA W' h1 h2 x hx)
  set T : H →L[ℂ] H := (adjoint A).comp A with hTdef
  have hTW : ∀ x ∈ W, T x ∈ W := hTinv W hWc hWi
  set S : W →L[ℂ] W := T.restrict hTW with hSdef
  have hSc : IsCompactOperator S := hTc.restrict' hTW
  have hSs : (S : W →ₗ[ℂ] W).IsSymmetric := by
    have h := (isSymmetric_adjoint_comp A).restrict_invariant hTW
    exact h

  have hS0 : S ≠ 0 := by
    obtain ⟨x, hxW, hx⟩ := hAW
    intro h0
    have h1 : ((S ⟨x, hxW⟩ : W) : H) = 0 := by simp [h0]
    have h2 : T x = 0 := by simpa [hSdef, coe_restrict_apply] using h1
    rw [hTdef, adjoint_comp_apply_eq_zero_iff] at h2
    exact hx h2
  obtain ⟨μ, hμ, hμ0⟩ : ∃ μ, HasEigenvalue (S : Module.End ℂ W) μ ∧ μ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hS0 ((eq_zero_of_forall_hasEigenvalue_eq_zero hSc hSs).1 hcon)
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  have hw0 : (w : H) ≠ 0 := fun h => (hasEigenvector_iff.1 hw).2 (Subtype.ext h)
  have hTw : T w = μ • (w : H) := by
    have h := congrArg Subtype.val (hasEigenvector_iff.1 hw |>.1 |> mem_eigenspace_iff.1)
    simpa [hSdef, coe_restrict_apply] using h

  set E : Submodule ℂ H := eigenspace (T : Module.End ℂ H) μ with hEdef
  haveI hEfin : FiniteDimensional ℂ E := finite_dimensional_eigenspace hTc μ hμ0
  have hwE : (w : H) ∈ E := by
    rw [hEdef, mem_eigenspace_iff]
    simpa using hTw
  have hWE : W ⊓ E ≠ ⊥ := (Submodule.ne_bot_iff _).2 ⟨w, mem_inf.2 ⟨w.2, hwE⟩, hw0⟩

  have hP : ∃ n, ∃ W' : Submodule ℂ H, IsClosed (W' : Set H) ∧ IsInvariant R W' ∧ W' ≤ W ∧ W' ⊓ E ≠ ⊥ ∧
      Module.finrank ℂ ↥(W' ⊓ E) = n :=
    ⟨_, W, hWc, hWi, le_rfl, hWE, rfl⟩
  obtain ⟨W₀, hW₀c, hW₀i, hW₀W, hW₀E, hW₀n⟩ := Nat.find_spec hP
  have hmin : ∀ W' : Submodule ℂ H, IsClosed (W' : Set H) → IsInvariant R W' → W' ≤ W → W' ⊓ E ≠ ⊥ →
      Module.finrank ℂ ↥(W₀ ⊓ E) ≤ Module.finrank ℂ ↥(W' ⊓ E) := by
    intro W' h1 h2 h3 h4
    rw [hW₀n]
    exact Nat.find_min' hP ⟨W', h1, h2, h3, h4, rfl⟩
  obtain ⟨x₀, hx₀, hx₀0⟩ := (Submodule.ne_bot_iff _).1 hW₀E
  have hx₀W₀ : x₀ ∈ W₀ := (mem_inf.1 hx₀).1
  have hTx₀ : T x₀ = μ • x₀ := by
    have h := mem_eigenspace_iff.1 (hEdef ▸ (mem_inf.1 hx₀).2 : x₀ ∈ eigenspace (T : Module.End ℂ H) μ)
    simpa using h

  refine ⟨generated R x₀, (generated_le hW₀c hW₀i hx₀W₀).trans hW₀W, isClosed_generated x₀,
    isInvariant_generated x₀, ?_, ?_⟩
  · exact fun h => hx₀0 ((Submodule.eq_bot_iff _).1 h x₀ (mem_generated x₀))
  · intro V₁ hV₁c hV₁i hV₁V
    haveI : CompleteSpace V₁ := hV₁c.isComplete.completeSpace_coe
    have hVc : IsClosed (generated R x₀ : Set H) := isClosed_generated x₀
    have hVi : IsInvariant R (generated R x₀) := isInvariant_generated x₀

    set x₁ : H := V₁.starProjection x₀ with hx₁def
    have hx₁V₁ : x₁ ∈ V₁ := starProjection_apply_mem V₁ x₀
    have hx₂ : x₀ - x₁ ∈ V₁ᗮ := sub_starProjection_mem_orthogonal x₀
    have hV₂c : IsClosed ((generated R x₀ ⊓ V₁ᗮ : Submodule ℂ H) : Set H) := by
      rw [coe_inf]
      exact hVc.inter (isClosed_orthogonal V₁)
    have hV₂i : IsInvariant R (generated R x₀ ⊓ V₁ᗮ) := isInvariant_inf hVi (isInvariant_orthogonal hR hV₁i)
    have hx₂V₂ : x₀ - x₁ ∈ generated R x₀ ⊓ V₁ᗮ :=
      mem_inf.2 ⟨sub_mem (mem_generated x₀) (hV₁V hx₁V₁), hx₂⟩
    have hTx₁ : T x₁ ∈ V₁ := hTinv V₁ hV₁c hV₁i x₁ hx₁V₁
    have hTx₂ : T (x₀ - x₁) ∈ generated R x₀ ⊓ V₁ᗮ := hTinv _ hV₂c hV₂i _ hx₂V₂
    have key : T x₁ - μ • x₁ = 0 := by
      have h1 : T x₁ - μ • x₁ ∈ V₁ := sub_mem hTx₁ (smul_mem _ _ hx₁V₁)
      have h2 : T x₁ - μ • x₁ ∈ V₁ᗮ := by
        have h3 : T x₁ - μ • x₁ = -(T (x₀ - x₁) - μ • (x₀ - x₁)) := by
          rw [map_sub, smul_sub, hTx₀]
          abel
        rw [h3]
        exact neg_mem (sub_mem (mem_inf.1 hTx₂).2 (smul_mem _ _ hx₂))
      exact (disjoint_def.1 (orthogonal_disjoint V₁)) _ h1 h2
    by_cases h0 : x₁ = 0
    · left
      have hx₀V₂ : x₀ ∈ generated R x₀ ⊓ V₁ᗮ := by simpa [h0] using hx₂V₂
      have hle : generated R x₀ ≤ V₁ᗮ := (generated_le hV₂c hV₂i hx₀V₂).trans inf_le_right
      rw [eq_bot_iff]
      intro y hy
      exact (Submodule.mem_bot ℂ).2 ((disjoint_def.1 (orthogonal_disjoint V₁)) y hy (hle (hV₁V hy)))
    · right
      have hx₁E : x₁ ∈ E := by
        rw [hEdef, mem_eigenspace_iff]
        simpa using (sub_eq_zero.1 key)
      have h1 : V₁ ⊓ E ≠ ⊥ := (Submodule.ne_bot_iff _).2 ⟨x₁, mem_inf.2 ⟨hx₁V₁, hx₁E⟩, h0⟩
      have hV₁W₀ : V₁ ≤ W₀ := hV₁V.trans (generated_le hW₀c hW₀i hx₀W₀)
      have h2 : V₁ ⊓ E ≤ W₀ ⊓ E := inf_le_inf_right E hV₁W₀
      have h3 : Module.finrank ℂ ↥(W₀ ⊓ E) ≤ Module.finrank ℂ ↥(V₁ ⊓ E) :=
        hmin V₁ hV₁c hV₁i (hV₁W₀.trans hW₀W) h1
      have h4 : V₁ ⊓ E = W₀ ⊓ E :=
        Submodule.eq_of_le_of_finrank_eq h2 (le_antisymm (Submodule.finrank_mono h2) h3)
      have hx₀V₁ : x₀ ∈ V₁ := by
        have h5 : x₀ ∈ V₁ ⊓ E := by
          rw [h4]
          exact hx₀
        exact (mem_inf.1 h5).1
      exact le_antisymm hV₁V (generated_le hV₁c hV₁i hx₀V₁)

private theorem exists_isIrreducible_not_mem_orthogonal (hR : IsAdjointClosed R)
    (hA : ∀ W : Submodule ℂ H, IsClosed (W : Set H) → IsInvariant R W → W ≠ ⊥ →
      ∃ A : H →L[ℂ] H, IsCompactOperator A ∧
        (∀ W' : Submodule ℂ H, IsClosed (W' : Set H) → IsInvariant R W' → ∀ x ∈ W', A x ∈ W') ∧
          ∃ x ∈ W, A x ≠ 0)
    {c : H} (hc : c ≠ 0) : ∃ V : Submodule ℂ H, IsIrreducible R V ∧ c ∉ Vᗮ := by
  by_contra hcon
  push Not at hcon
  set W : Submodule ℂ H := ⨅ V : {V : Submodule ℂ H // IsIrreducible R V}, (V : Submodule ℂ H)ᗮ with hWdef
  have hcW : c ∈ W := by
    rw [hWdef, mem_iInf]
    exact fun V => hcon V V.2
  have hWc : IsClosed (W : Set H) := by
    rw [hWdef, coe_iInf]
    exact isClosed_iInter fun V => isClosed_orthogonal (V : Submodule ℂ H)
  have hWi : IsInvariant R W := by
    intro r hr x hx
    rw [hWdef, mem_iInf] at hx ⊢
    exact fun V => isInvariant_orthogonal hR V.2.2.1 r hr x (hx V)
  have hW0 : W ≠ ⊥ := fun h => hc ((Submodule.mem_bot ℂ).1 (h ▸ hcW))
  obtain ⟨A, hAc, hAinv, hAW⟩ := hA W hWc hWi hW0
  obtain ⟨V, hVW, hV⟩ := exists_isIrreducible_le hR A hAc hAinv hWc hWi hAW
  have hVle : V ≤ Vᗮ :=
    hVW.trans (hWdef ▸ iInf_le (fun V' : {V' : Submodule ℂ H // IsIrreducible R V'} => (V' : Submodule ℂ H)ᗮ)
      ⟨V, hV⟩)
  apply hV.2.2.1
  rw [eq_bot_iff]
  intro y hy
  exact (Submodule.mem_bot ℂ).2 ((disjoint_def.1 (orthogonal_disjoint V)) y hy (hVle hy))

end HilbertConstituent
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction"

end HilbertConstituentBlock
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction"

section SmoothingKernelBlock

section Countability

open NumberField IsDedekindDomain TopologicalSpace Topology
open scoped MatrixGroups

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.AdelicGL CubicInduction.globalPointsGL"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "SlabL2.realCoordinate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 LocalGL3 heckeGen1 heckeGen2 cosetSum IsCosetEigenfunction IsRightInvariant archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 one_le_gauge3 one_le_archGauge3 IsModerateGrowth3 matrixFin_ext matrixAdele_ext localMatN localMatN_apply_self localMatN_apply_of_ne mapMatrix_localMatN_self mapMatrix_localMatN_of_ne localEmbedN finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN finEmbedN localToAdelic3 exists_mul_eq_unipotent_mul_diagonal_mul_compact smoothingOperator_mem_cuspFunctions_of_isCuspidalAlong exists_isCompactOperator_cuspidalSubspace_smoothingOperator exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous exists_inner_toL2_translateRight_ne_zero_of_isCosetEigenfunction measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator"
namespace AdelicCountability
p2m_open "LanglandsTunnell.CubicInduction~isCompact_localMaximalCompact3~det_radicalP21~det_radicalP12 LanglandsTunnell~CubicInduction.isCompact_localMaximalCompact3"

private theorem countable_ideal (R : Type*) [CommRing R] [IsNoetherianRing R] [Countable R] : Countable (Ideal R) := by
  have hfg : ∀ I : Ideal R, ∃ s : Finset R, Ideal.span (s : Set R) = I := fun I => IsNoetherian.noetherian I
  choose gen hgen using hfg
  have hinj : Function.Injective gen := fun I J h => by rw [← hgen I, ← hgen J, h]
  exact hinj.countable

private scoped instance countable_ringOfIntegers_rat : Countable (𝓞 ℚ) :=
  Countable.of_module_finite ℤ (𝓞 ℚ)

private scoped instance countable_heightOneSpectrum_rat : Countable (HeightOneSpectrum (𝓞 ℚ)) := by
  haveI := countable_ideal (𝓞 ℚ)
  have hinj : Function.Injective fun v : HeightOneSpectrum (𝓞 ℚ) => v.asIdeal := fun v w h =>
    HeightOneSpectrum.ext h
  exact hinj.countable

private scoped instance secondCountableTopology_finiteAdeleRing_rat : SecondCountableTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  RestrictedProduct.secondCountableTopology (X := fun v : HeightOneSpectrum (𝓞 ℚ) => v.adicCompletion ℚ)
    (C := fun v => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)))
    fun v => NumberField.isOpenAdicCompletionIntegers ℚ v

private theorem isReal_of_rat' (w : InfinitePlace ℚ) : w.IsReal := by
  rw [Subsingleton.elim w Rat.infinitePlace]
  exact Rat.isReal_infinitePlace

private scoped instance secondCountableTopology_completion_rat (w : InfinitePlace ℚ) : SecondCountableTopology w.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (isReal_of_rat' w)).isEmbedding.secondCountableTopology

private scoped instance secondCountableTopology_infiniteAdeleRing_rat : SecondCountableTopology (InfiniteAdeleRing ℚ) :=
  inferInstanceAs (SecondCountableTopology ((w : InfinitePlace ℚ) → w.Completion))

private scoped instance secondCountableTopology_adeleRing_rat : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ) :=
  NumberField.AdeleRing.secondCountableTopology ℚ

private theorem secondCountableTopology_matrix3 (A : Type*) [TopologicalSpace A] [SecondCountableTopology A] :
    SecondCountableTopology (Matrix (Fin 3) (Fin 3) A) :=
  inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → A))

private theorem secondCountableTopology_units (M : Type*) [Monoid M] [TopologicalSpace M] [SecondCountableTopology M] :
    SecondCountableTopology Mˣ :=
  haveI : SecondCountableTopology Mᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  Units.isEmbedding_embedProduct.secondCountableTopology

private scoped instance secondCountableTopology_adelicGL : SecondCountableTopology (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  haveI := secondCountableTopology_matrix3 (AdeleRing (𝓞 ℚ) ℚ)
  secondCountableTopology_units (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))

private scoped instance secondCountableTopology_archGL : SecondCountableTopology (GL (Fin 3) (InfiniteAdeleRing ℚ)) :=
  haveI := secondCountableTopology_matrix3 (InfiniteAdeleRing ℚ)
  secondCountableTopology_units (Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))

private scoped instance secondCountableTopology_finGL : SecondCountableTopology (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  haveI := secondCountableTopology_matrix3 (FiniteAdeleRing (𝓞 ℚ) ℚ)
  secondCountableTopology_units (Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))

private theorem firstCountableTopology_adelicGL : FirstCountableTopology (AdelicGL 3 (𝓞 ℚ) ℚ) := inferInstance

private theorem
    firstCountableTopology_archGL : FirstCountableTopology (GL (Fin 3) (InfiniteAdeleRing ℚ)) := inferInstance

private theorem firstCountableTopology_finGL : FirstCountableTopology (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  inferInstance

end LanglandsTunnell.CubicInduction.AdelicCountability
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction"

end Countability
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

section LevelSet

open Matrix IsDedekindDomain NumberField AutomorphicForm

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.AdelicGL CubicInduction.globalPointsGL"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "SlabL2.realCoordinate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 LocalGL3 heckeGen1 heckeGen2 cosetSum IsCosetEigenfunction IsRightInvariant archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 one_le_gauge3 one_le_archGauge3 IsModerateGrowth3 matrixFin_ext matrixAdele_ext localMatN localMatN_apply_self localMatN_apply_of_ne mapMatrix_localMatN_self mapMatrix_localMatN_of_ne localEmbedN finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN finEmbedN localToAdelic3 exists_mul_eq_unipotent_mul_diagonal_mul_compact smoothingOperator_mem_cuspFunctions_of_isCuspidalAlong exists_isCompactOperator_cuspidalSubspace_smoothingOperator exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous exists_inner_toL2_translateRight_ne_zero_of_isCosetEigenfunction measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator"
p2m_open "LanglandsTunnell.CubicInduction~isCompact_localMaximalCompact3~det_radicalP21~det_radicalP12 LanglandsTunnell~CubicInduction.isCompact_localMaximalCompact3"

section Components

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem coe_componentAt3 (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ((componentAt3 (𝓞 ℚ) ℚ v g : GL (Fin 3) (v.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)).mapMatrix
        (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  rfl

private theorem coe_archComponent3 (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ((archComponent3 (𝓞 ℚ) ℚ g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
        Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) =
      (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  rfl

private theorem coe_localToAdelic3 (h : LocalGL3 v) :
    ((localToAdelic3 v h : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      finMatN (Fin 3) (𝓞 ℚ) ℚ
        (localMatN (Fin 3) (𝓞 ℚ) ℚ v (h : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) :=
  rfl

private theorem _root_.LanglandsTunnell.CubicInduction.componentAt3_localToAdelic3_self (h : LocalGL3 v) :
    componentAt3 (𝓞 ℚ) ℚ v (localToAdelic3 v h) = h := by
  apply Units.ext
  rw [coe_componentAt3, coe_localToAdelic3, ← RingHom.mapMatrix_comp, RingHom.comp_apply,
    mapMatrix_fin_finMatN, mapMatrix_localMatN_self]

p2m_export "LanglandsTunnell.CubicInduction" "componentAt3_localToAdelic3_self"

private theorem _root_.LanglandsTunnell.CubicInduction.componentAt3_localToAdelic3_of_ne {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) (h : LocalGL3 v) :
    componentAt3 (𝓞 ℚ) ℚ w (localToAdelic3 v h) = 1 := by
  apply Units.ext
  rw [coe_componentAt3, coe_localToAdelic3, ← RingHom.mapMatrix_comp, RingHom.comp_apply,
    mapMatrix_fin_finMatN, mapMatrix_localMatN_of_ne (Fin 3) (𝓞 ℚ) ℚ v _ hw, Units.val_one]

p2m_export "LanglandsTunnell.CubicInduction" "componentAt3_localToAdelic3_of_ne"

private theorem _root_.LanglandsTunnell.CubicInduction.archComponent3_localToAdelic3 (h : LocalGL3 v) :
    archComponent3 (𝓞 ℚ) ℚ (localToAdelic3 v h) = 1 := by
  apply Units.ext
  rw [coe_archComponent3, coe_localToAdelic3, mapMatrix_arch_finMatN, Units.val_one]

p2m_export "LanglandsTunnell.CubicInduction" "archComponent3_localToAdelic3"
end Components
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

section OpenMaximal

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem isOpen_setOf_forall_entry_mem {B : Set (v.adicCompletion ℚ)} (hB : IsOpen B) :
    IsOpen {M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ) | ∀ i j, M i j ∈ B} := by
  simp_rw [Set.setOf_forall]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact (continuous_id.matrix_elem i j).isOpen_preimage B hB

private theorem _root_.LanglandsTunnell.CubicInduction.isOpen_localMaximalCompact3 :
    IsOpen ((localMaximalCompact3 (𝓞 ℚ) ℚ v : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) := by
  have hI : IsOpen {M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ) |
      ∀ i j, M i j ∈ {z : v.adicCompletion ℚ | Valued.v z ≤ 1}} :=
    isOpen_setOf_forall_entry_mem v
      (by simpa using AdelicLevel.isOpen_setOf_valued_le v (1 : v.adicCompletion ℚ) one_ne_zero)
  have hset : ((localMaximalCompact3 (𝓞 ℚ) ℚ v : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) =
      (Units.val ⁻¹' {M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ) |
          ∀ i j, M i j ∈ {z : v.adicCompletion ℚ | Valued.v z ≤ 1}}) ∩
        ((fun k : LocalGL3 v => ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) ⁻¹'
          {M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ) |
            ∀ i j, M i j ∈ {z : v.adicCompletion ℚ | Valued.v z ≤ 1}}) :=
    rfl
  rw [hset]
  exact (Units.continuous_val.isOpen_preimage _ hI).inter (Units.continuous_coe_inv.isOpen_preimage _ hI)

p2m_export "LanglandsTunnell.CubicInduction" "isOpen_localMaximalCompact3"
end OpenMaximal
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

section LevelCompact

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "Gf" => GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)

private scoped instance t2Space_matrixFin3_finiteAdeleRing : T2Space (Matrix (Fin 3) (Fin 3) 𝔸f) :=
  inferInstanceAs (T2Space (Fin 3 → Fin 3 → 𝔸f))

private def finComponent3 (p : HeightOneSpectrum (𝓞 ℚ)) : Gf →* LocalGL3 p :=
  (componentAt3 (𝓞 ℚ) ℚ p).comp (finEmbedN (Fin 3) (𝓞 ℚ) ℚ)

private theorem finComponent3_apply (p : HeightOneSpectrum (𝓞 ℚ)) (k : Gf) :
    finComponent3 p k = componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) := rfl

private theorem finComponent3_localEmbedN_self (p : HeightOneSpectrum (𝓞 ℚ)) (τ : LocalGL3 p) :
    finComponent3 p (localEmbedN (Fin 3) (𝓞 ℚ) ℚ p τ) = τ :=
  componentAt3_localToAdelic3_self p τ

private theorem finComponent3_localEmbedN_of_ne {p q : HeightOneSpectrum (𝓞 ℚ)} (hq : q ≠ p) (τ : LocalGL3 p) :
    finComponent3 q (localEmbedN (Fin 3) (𝓞 ℚ) ℚ p τ) = 1 :=
  componentAt3_localToAdelic3_of_ne p hq τ

private theorem coe_finComponent3_apply (p : HeightOneSpectrum (𝓞 ℚ)) (k : Gf) (i j : Fin 3) :
    ((finComponent3 p k : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j =
      ((k : Matrix (Fin 3) (Fin 3) 𝔸f) i j) p :=
  rfl

private def integralMatrices : Set (Matrix (Fin 3) (Fin 3) 𝔸f) :=
  {m | ∀ i j, m i j ∈ AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ}

private theorem isCompact_integralMatrices : IsCompact integralMatrices := by
  have hset : integralMatrices =
      (Set.pi Set.univ fun _ : Fin 3 => Set.pi Set.univ fun _ : Fin 3 => AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ :
        Set (Matrix (Fin 3) (Fin 3) 𝔸f)) := by
    exact Set.ext fun m =>
      ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ i) j (Set.mem_univ j)⟩
  rw [hset]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => AdelicBox.isCompact_integralFiniteAdeles ℚ

private theorem isClosed_range_embedProduct_matrix :
    IsClosed (Set.range (Units.embedProduct (Matrix (Fin 3) (Fin 3) 𝔸f))) := by
  have h : Set.range (Units.embedProduct (Matrix (Fin 3) (Fin 3) 𝔸f)) =
      {q : Matrix (Fin 3) (Fin 3) 𝔸f × (Matrix (Fin 3) (Fin 3) 𝔸f)ᵐᵒᵖ |
        q.1 * MulOpposite.unop q.2 = 1 ∧ MulOpposite.unop q.2 * q.1 = 1} := by
    ext q
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u.mul_inv, u.inv_mul⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨q.1, MulOpposite.unop q.2, h1, h2⟩, Prod.ext rfl (MulOpposite.op_unop q.2)⟩
  rw [h]
  exact (isClosed_eq (continuous_fst.mul (MulOpposite.continuous_unop.comp continuous_snd)) continuous_const).inter
    (isClosed_eq ((MulOpposite.continuous_unop.comp continuous_snd).mul continuous_fst) continuous_const)

private def integralPoints : Set Gf :=
  Units.embedProduct (Matrix (Fin 3) (Fin 3) 𝔸f) ⁻¹' (integralMatrices ×ˢ (MulOpposite.op '' integralMatrices))

private theorem isCompact_integralPoints : IsCompact integralPoints :=
  (Units.isInducing_embedProduct (M := Matrix (Fin 3) (Fin 3) 𝔸f)).isCompact_preimage
    isClosed_range_embedProduct_matrix
    (isCompact_integralMatrices.prod (isCompact_integralMatrices.image MulOpposite.continuous_op))

private theorem mem_integralPoints_of_forall_mem_localMaximalCompact3 {k : Gf}
    (hk : ∀ p : HeightOneSpectrum (𝓞 ℚ), finComponent3 p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    k ∈ integralPoints := by
  show (k : Matrix (Fin 3) (Fin 3) 𝔸f) ∈ integralMatrices ∧
    MulOpposite.op ((k⁻¹ : Gf) : Matrix (Fin 3) (Fin 3) 𝔸f) ∈ MulOpposite.op '' integralMatrices
  refine ⟨fun i j p => ?_, Set.mem_image_of_mem _ fun i j p => ?_⟩
  · rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, ← coe_finComponent3_apply]
    exact (hk p).1 i j
  · rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, ← coe_finComponent3_apply, map_inv]
    exact (hk p).2 i j

open scoped Classical in

private theorem exists_isCompact_superset_of_finset (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    ∀ K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p),
      (∀ p ∈ S, IsCompact (K' p : Set (LocalGL3 p))) → (∀ p ∉ S, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) →
      ∃ C : Set Gf, IsCompact C ∧ {k : Gf | ∀ p, finComponent3 p k ∈ K' p} ⊆ C := by
  refine Finset.induction_on S ?_ ?_
  · intro K' _ hmax
    refine ⟨integralPoints, isCompact_integralPoints, fun k hk => ?_⟩
    exact mem_integralPoints_of_forall_mem_localMaximalCompact3 fun p => by
      rw [← hmax p (by simp)]
      exact hk p
  · intro p S hpS ih K' hcpt hmax
    obtain ⟨C', hC', hsub'⟩ := ih (Function.update K' p (localMaximalCompact3 (𝓞 ℚ) ℚ p))
      (fun q hq => by
        have hqp : q ≠ p := fun h => hpS (h ▸ hq)
        rw [Function.update_of_ne hqp]
        exact hcpt q (Finset.mem_insert_of_mem hq))
      (fun q hq => by
        by_cases hqp : q = p
        · subst hqp
          exact Function.update_self ..
        · rw [Function.update_of_ne hqp]
          exact hmax q fun h => hq ((Finset.mem_insert.mp h).elim (fun h' => absurd h' hqp) id))
    have hKp : IsCompact (K' p : Set (LocalGL3 p)) := hcpt p (Finset.mem_insert_self p S)
    obtain ⟨T, hT⟩ := hKp.elim_finite_subcover
      (fun τ : LocalGL3 p => {x : LocalGL3 p | τ⁻¹ * x ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p})
      (fun τ => (continuous_const.mul continuous_id).isOpen_preimage _ (isOpen_localMaximalCompact3 p))
      (fun x _ => Set.mem_iUnion.mpr ⟨x, by simp only [Set.mem_setOf_eq, inv_mul_cancel]; exact one_mem _⟩)
    refine ⟨⋃ τ ∈ T, (fun k : Gf => localEmbedN (Fin 3) (𝓞 ℚ) ℚ p τ * k) '' C',
      T.finite_toSet.isCompact_biUnion fun τ _ => hC'.image (continuous_const.mul continuous_id), fun k hk => ?_⟩
    obtain ⟨τ, hτT, hτ⟩ := Set.mem_iUnion₂.mp (hT (hk p))
    refine Set.mem_biUnion hτT ⟨(localEmbedN (Fin 3) (𝓞 ℚ) ℚ p τ)⁻¹ * k, hsub' fun q => ?_, mul_inv_cancel_left _ _⟩
    rw [map_mul, map_inv]
    by_cases hqp : q = p
    · subst hqp
      rw [Function.update_self, finComponent3_localEmbedN_self]
      exact hτ
    · rw [Function.update_of_ne hqp, finComponent3_localEmbedN_of_ne hqp, inv_one, one_mul]
      exact hk q

private theorem exists_isCompact_forall_componentAt3_finEmbedN_mem_subset
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p))
    (hcpt : ∀ p, IsCompact (K' p : Set (LocalGL3 p)))
    (hcof : ∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    ∃ C : Set Gf, IsCompact C ∧
      {k : Gf | ∀ p, componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ∈ K' p} ⊆ C := by
  have hfin := Filter.eventually_cofinite.mp hcof
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_superset_of_finset hfin.toFinset K' (fun p _ => hcpt p)
    (fun p hp => by simpa using hp)
  exact ⟨C, hC, fun k hk => hsub fun p => hk p⟩

private theorem continuous_finComponent3 (p : HeightOneSpectrum (𝓞 ℚ)) : Continuous (finComponent3 p) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact continuous_matrix fun i j =>
      (AdelicLevel.continuous_finAdeleEval (𝓞 ℚ) ℚ p).comp (Units.continuous_val.matrix_elem i j)
  · simp only [← map_inv]
    exact continuous_matrix fun i j =>
      (AdelicLevel.continuous_finAdeleEval (𝓞 ℚ) ℚ p).comp (Units.continuous_coe_inv.matrix_elem i j)

private def levelSubgroup (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p)) : Subgroup Gf where
  carrier := {k | ∀ p, finComponent3 p k ∈ K' p}
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    intro p
    rw [map_one]
    exact one_mem _
  mul_mem' := by
    intro a b ha hb p
    rw [map_mul]
    exact mul_mem (ha p) (hb p)
  inv_mem' := by
    intro a ha p
    rw [map_inv]
    exact inv_mem (ha p)

private theorem mem_levelSubgroup_iff (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p)) (k : Gf) :
    k ∈ levelSubgroup K' ↔ ∀ p, finComponent3 p k ∈ K' p := Iff.rfl

private theorem coe_levelSubgroup (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p)) :
    (levelSubgroup K' : Set Gf) =
      {k : Gf | ∀ p, componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ∈ K' p} := rfl

private theorem isOpen_integralMatrices : IsOpen integralMatrices := by
  have hset : integralMatrices =
      (Set.pi Set.univ fun _ : Fin 3 => Set.pi Set.univ fun _ : Fin 3 => AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ :
        Set (Matrix (Fin 3) (Fin 3) 𝔸f)) := by
    exact Set.ext fun m =>
      ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ i) j (Set.mem_univ j)⟩
  rw [hset]
  exact isOpen_set_pi Set.finite_univ fun _ _ =>
    isOpen_set_pi Set.finite_univ fun _ _ => AdelicBox.isOpen_integralFiniteAdeles ℚ

private theorem isOpen_integralPoints : IsOpen integralPoints :=
  Units.continuous_embedProduct.isOpen_preimage _
    (isOpen_integralMatrices.prod (MulOpposite.opHomeomorph.isOpenMap _ isOpen_integralMatrices))

private theorem finComponent3_mem_localMaximalCompact3_of_mem_integralPoints {k : Gf} (hk : k ∈ integralPoints)
    (p : HeightOneSpectrum (𝓞 ℚ)) : finComponent3 p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p := by
  obtain ⟨h1, h2⟩ := hk
  obtain ⟨m, hm, hmk⟩ := h2
  have hmk' : MulOpposite.op m = MulOpposite.op ((k⁻¹ : Gf) : Matrix (Fin 3) (Fin 3) 𝔸f) := hmk
  have hm' : m = ((k⁻¹ : Gf) : Matrix (Fin 3) (Fin 3) 𝔸f) := MulOpposite.op_injective hmk'
  subst hm'
  change _ ∧ _
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [coe_finComponent3_apply, ← IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    exact h1 i j p
  · rw [← map_inv, coe_finComponent3_apply, ← IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hm i j p

private theorem one_mem_integralPoints : (1 : Gf) ∈ integralPoints :=
  mem_integralPoints_of_forall_mem_localMaximalCompact3 fun p => by
    rw [map_one]
    exact one_mem _

open scoped Classical in

private theorem isOpen_setOf_forall_componentAt3_finEmbedN_mem
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p))
    (hopen : ∀ p, IsOpen (K' p : Set (LocalGL3 p)))
    (hcof : ∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    IsOpen {k : Gf | ∀ p, componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ∈ K' p} := by
  rw [← coe_levelSubgroup]
  refine Subgroup.isOpen_of_mem_nhds (levelSubgroup K') (g := 1) ?_
  have hfin := Filter.eventually_cofinite.mp hcof
  have hW : IsOpen (integralPoints ∩ ⋂ p ∈ hfin.toFinset, finComponent3 p ⁻¹' (K' p : Set (LocalGL3 p))) :=
    isOpen_integralPoints.inter
      (isOpen_biInter_finset fun p _ => (continuous_finComponent3 p).isOpen_preimage _ (hopen p))
  refine Filter.mem_of_superset (hW.mem_nhds ⟨one_mem_integralPoints, ?_⟩) ?_
  · exact Set.mem_iInter₂.mpr fun p _ => by
      show finComponent3 p 1 ∈ K' p
      rw [map_one]
      exact one_mem _
  · intro k hk
    obtain ⟨hint, hS⟩ := hk
    rw [SetLike.mem_coe, mem_levelSubgroup_iff]
    intro p
    by_cases hp : p ∈ hfin.toFinset
    · exact Set.mem_iInter₂.mp hS p hp
    · have hmax : K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p := by simpa using hp
      rw [hmax]
      exact finComponent3_mem_localMaximalCompact3_of_mem_integralPoints hint p

private theorem isCompact_setOf_forall_componentAt3_finEmbedN_mem
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p))
    (hopen : ∀ p, IsOpen (K' p : Set (LocalGL3 p))) (hcpt : ∀ p, IsCompact (K' p : Set (LocalGL3 p)))
    (hcof : ∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    IsCompact {k : Gf | ∀ p, componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ∈ K' p} := by
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_forall_componentAt3_finEmbedN_mem_subset K' hcpt hcof
  have hclosed : IsClosed {k : Gf | ∀ p, componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ∈ K' p} := by
    rw [← coe_levelSubgroup]
    exact Subgroup.isClosed_of_isOpen _ (isOpen_setOf_forall_componentAt3_finEmbedN_mem K' hopen hcof)
  exact hC.of_isClosed_subset hclosed hsub

end LevelCompact
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

end LevelSet
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

section MaximalCompactCarried

open Matrix IsDedekindDomain NumberField AutomorphicForm

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.AdelicGL CubicInduction.globalPointsGL"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "SlabL2.realCoordinate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 LocalGL3 heckeGen1 heckeGen2 cosetSum IsCosetEigenfunction IsRightInvariant archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 one_le_gauge3 one_le_archGauge3 IsModerateGrowth3 matrixFin_ext matrixAdele_ext localMatN localMatN_apply_self localMatN_apply_of_ne mapMatrix_localMatN_self mapMatrix_localMatN_of_ne localEmbedN finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN finEmbedN localToAdelic3 exists_mul_eq_unipotent_mul_diagonal_mul_compact smoothingOperator_mem_cuspFunctions_of_isCuspidalAlong exists_isCompactOperator_cuspidalSubspace_smoothingOperator exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous exists_inner_toL2_translateRight_ne_zero_of_isCosetEigenfunction measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator"
p2m_open "LanglandsTunnell.CubicInduction~isCompact_localMaximalCompact3~det_radicalP21~det_radicalP12 LanglandsTunnell~CubicInduction.isCompact_localMaximalCompact3"

section Compact

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem isCompact_adicCompletionIntegers :
    IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) :=
  isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace (v.adicCompletionIntegers ℚ)))

private def integralMatrices3 : Submonoid (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) where
  carrier := {a | ∀ i j, Valued.v (a i j) ≤ 1}
  one_mem' := by
    intro i j
    exact valued_one_entry_le3 (𝓞 ℚ) ℚ v i j
  mul_mem' := by
    intro a b ha hb i j
    exact valued_mul_apply_le3 (𝓞 ℚ) ℚ v (fun l => ha i l) (fun l => hb l j)

private theorem mem_integralMatrices3 {a : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} :
    a ∈ integralMatrices3 v ↔ ∀ i j, Valued.v (a i j) ≤ 1 :=
  Iff.rfl

private theorem isCompact_integralMatrices3 :
    IsCompact (integralMatrices3 v : Set (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) := by
  have hpi : IsCompact (Set.pi Set.univ fun _ : Fin 3 =>
      Set.pi Set.univ fun _ : Fin 3 => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_adicCompletionIntegers v
  have hset : (integralMatrices3 v : Set (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) =
      (Set.pi Set.univ fun _ : Fin 3 =>
        Set.pi Set.univ fun _ : Fin 3 => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) := by
    ext a
    rw [SetLike.mem_coe, mem_integralMatrices3]
    constructor
    · intro h i _ j _
      exact h i j
    · intro h i j
      exact h i (Set.mem_univ i) j (Set.mem_univ j)
  rw [hset]
  exact hpi

private theorem localMaximalCompact3_eq_units :
    localMaximalCompact3 (𝓞 ℚ) ℚ v = (integralMatrices3 v).units := by
  ext k
  simp only [mem_localMaximalCompact3_iff, Submonoid.mem_units_iff, mem_integralMatrices3]

private theorem isCompact_localMaximalCompact3 :
    IsCompact ((localMaximalCompact3 (𝓞 ℚ) ℚ v : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) := by
  rw [localMaximalCompact3_eq_units]
  exact Submonoid.units_isCompact (isCompact_integralMatrices3 v)

end Compact
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

end MaximalCompactCarried
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

section ArchEmbeddingCarried

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.AdelicGL CubicInduction.globalPointsGL"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "SlabL2.realCoordinate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 LocalGL3 heckeGen1 heckeGen2 cosetSum IsCosetEigenfunction IsRightInvariant archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 one_le_gauge3 one_le_archGauge3 IsModerateGrowth3 matrixFin_ext matrixAdele_ext localMatN localMatN_apply_self localMatN_apply_of_ne mapMatrix_localMatN_self mapMatrix_localMatN_of_ne localEmbedN finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN finEmbedN localToAdelic3 exists_mul_eq_unipotent_mul_diagonal_mul_compact smoothingOperator_mem_cuspFunctions_of_isCuspidalAlong exists_isCompactOperator_cuspidalSubspace_smoothingOperator exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous exists_inner_toL2_translateRight_ne_zero_of_isCosetEigenfunction measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator"
p2m_open "LanglandsTunnell.CubicInduction~isCompact_localMaximalCompact3~det_radicalP21~det_radicalP12 LanglandsTunnell~CubicInduction.isCompact_localMaximalCompact3"

section ArchEmbedding

private def archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ) :=
  Matrix.of fun i j =>
    ((g i j, (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : AdeleRing (𝓞 ℚ) ℚ)

private theorem mapMatrix_arch_archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (archMat3 g) = g := by
  ext i j
  simp [archMat3, RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleArch_apply]

private theorem mapMatrix_fin_archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (archMat3 g) = 1 := by
  ext i j
  simp [archMat3, RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleFin_apply]

private theorem archMat3_one : archMat3 1 = 1 :=
  matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ (by rw [mapMatrix_arch_archMat3, map_one])
    (by rw [mapMatrix_fin_archMat3, map_one])

private theorem archMat3_mul (g h : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    archMat3 (g * h) = archMat3 g * archMat3 h :=
  matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ
    (by rw [map_mul, mapMatrix_arch_archMat3, mapMatrix_arch_archMat3, mapMatrix_arch_archMat3])
    (by rw [map_mul, mapMatrix_fin_archMat3, mapMatrix_fin_archMat3, mapMatrix_fin_archMat3, mul_one])

private def archToAdelic3 : GL (Fin 3) (InfiniteAdeleRing ℚ) →* AdelicGL 3 (𝓞 ℚ) ℚ where
  toFun g :=
    { val := archMat3 g
      inv := archMat3 ((g⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))
      val_inv := by rw [← archMat3_mul, Units.mul_inv, archMat3_one]
      inv_val := by rw [← archMat3_mul, Units.inv_mul, archMat3_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; exact archMat3_one)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; exact archMat3_mul _ _)

private theorem coe_archToAdelic3 (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    ((archToAdelic3 g : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :=
  rfl

private theorem archComponent3_archToAdelic3 (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    archComponent3 (𝓞 ℚ) ℚ (archToAdelic3 g) = g := by
  apply Units.ext
  rw [coe_archComponent3, coe_archToAdelic3, mapMatrix_arch_archMat3]

private theorem componentAt3_archToAdelic3 (v : HeightOneSpectrum (𝓞 ℚ)) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    componentAt3 (𝓞 ℚ) ℚ v (archToAdelic3 g) = 1 := by
  apply Units.ext
  rw [coe_componentAt3, coe_archToAdelic3, ← RingHom.mapMatrix_comp, RingHom.comp_apply,
    mapMatrix_fin_archMat3, map_one, Units.val_one]

end ArchEmbedding
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

end ArchEmbeddingCarried
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

section ComponentGlueCarried

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory
open scoped MatrixGroups

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.AdelicGL CubicInduction.globalPointsGL"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "SlabL2.realCoordinate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 LocalGL3 heckeGen1 heckeGen2 cosetSum IsCosetEigenfunction IsRightInvariant archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 one_le_gauge3 one_le_archGauge3 IsModerateGrowth3 matrixFin_ext matrixAdele_ext localMatN localMatN_apply_self localMatN_apply_of_ne mapMatrix_localMatN_self mapMatrix_localMatN_of_ne localEmbedN finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN finEmbedN localToAdelic3 exists_mul_eq_unipotent_mul_diagonal_mul_compact smoothingOperator_mem_cuspFunctions_of_isCuspidalAlong exists_isCompactOperator_cuspidalSubspace_smoothingOperator exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous exists_inner_toL2_translateRight_ne_zero_of_isCosetEigenfunction measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator"
p2m_open "LanglandsTunnell.CubicInduction~isCompact_localMaximalCompact3~det_radicalP21~det_radicalP12 LanglandsTunnell~CubicInduction.isCompact_localMaximalCompact3"

private theorem adelicGL3_ext {g g' : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hfin : ∀ u : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ u g = componentAt3 (𝓞 ℚ) ℚ u g')
    (harch : archComponent3 (𝓞 ℚ) ℚ g = archComponent3 (𝓞 ℚ) ℚ g') : g = g' := by
  apply Units.ext
  refine matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ ?_ ?_
  · exact congrArg Units.val harch
  · refine matrixFin_ext (Fin 3) (𝓞 ℚ) ℚ fun u => ?_
    exact congrArg Units.val (hfin u)

private theorem continuous_finEmbedN3 : Continuous (finEmbedN (Fin 3) (𝓞 ℚ) ℚ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    show Continuous fun k : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
      (((1 : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j,
        (k : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : AdeleRing (𝓞 ℚ) ℚ)
    exact continuous_const.prodMk (Units.continuous_val.matrix_elem i j)
  · refine continuous_matrix fun i j => ?_
    show Continuous fun k : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
      (((1 : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j,
        ((k⁻¹ : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) :
        AdeleRing (𝓞 ℚ) ℚ)
    exact continuous_const.prodMk (Units.continuous_coe_inv.matrix_elem i j)

private theorem continuous_archToAdelic3 : Continuous archToAdelic3 := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    show Continuous fun a : GL (Fin 3) (InfiniteAdeleRing ℚ) =>
      (((a : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j,
        (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : AdeleRing (𝓞 ℚ) ℚ)
    exact (Units.continuous_val.matrix_elem i j).prodMk continuous_const
  · refine continuous_matrix fun i j => ?_
    show Continuous fun a : GL (Fin 3) (InfiniteAdeleRing ℚ) =>
      ((((a⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j,
        (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : AdeleRing (𝓞 ℚ) ℚ)
    exact (Units.continuous_coe_inv.matrix_elem i j).prodMk continuous_const

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

end ComponentGlueCarried
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

section SplittingCarried

open Matrix IsDedekindDomain NumberField NumberField.AdelicHaar MeasureTheory MeasureTheory.Measure
open scoped MatrixGroups

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.AdelicGL CubicInduction.globalPointsGL"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "SlabL2.realCoordinate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 LocalGL3 heckeGen1 heckeGen2 cosetSum IsCosetEigenfunction IsRightInvariant archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 one_le_gauge3 one_le_archGauge3 IsModerateGrowth3 matrixFin_ext matrixAdele_ext localMatN localMatN_apply_self localMatN_apply_of_ne mapMatrix_localMatN_self mapMatrix_localMatN_of_ne localEmbedN finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN finEmbedN localToAdelic3 exists_mul_eq_unipotent_mul_diagonal_mul_compact smoothingOperator_mem_cuspFunctions_of_isCuspidalAlong exists_isCompactOperator_cuspidalSubspace_smoothingOperator exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous exists_inner_toL2_translateRight_ne_zero_of_isCosetEigenfunction measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator"
p2m_open "LanglandsTunnell.CubicInduction~isCompact_localMaximalCompact3~det_radicalP21~det_radicalP12 LanglandsTunnell~CubicInduction.isCompact_localMaximalCompact3"

local notation "Ginf" => GL (Fin 3) (InfiniteAdeleRing ℚ)
local notation "Gf" => GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)

private theorem continuous_generalLinearGroup_map {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A]
    [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B] (f : A →+* B) (hf : Continuous f) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin 3) f) :=
  Continuous.units_map _ ((continuous_id.matrix_map hf : Continuous fun m : Matrix (Fin 3) (Fin 3) A => m.map f))

private def finPart3 : AdelicGL 3 (𝓞 ℚ) ℚ →* Gf :=
  Matrix.GeneralLinearGroup.map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)

private theorem coe_finPart3 (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ((finPart3 g : Gf) : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) =
      (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  rfl

private theorem continuous_finPart3 : Continuous finPart3 :=
  continuous_generalLinearGroup_map _ (AdelicLevel.continuous_adeleFin (𝓞 ℚ) ℚ)

private theorem continuous_archComponent3 : Continuous (archComponent3 (𝓞 ℚ) ℚ) :=
  continuous_generalLinearGroup_map _ (AdelicLevel.continuous_adeleArch (𝓞 ℚ) ℚ)

private theorem coe_finEmbedN3 (k : Gf) :
    ((finEmbedN (Fin 3) (𝓞 ℚ) ℚ k : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      finMatN (Fin 3) (𝓞 ℚ) ℚ (k : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  rfl

private theorem archComponent3_finEmbedN (k : Gf) : archComponent3 (𝓞 ℚ) ℚ (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) = 1 := by
  apply Units.ext
  rw [coe_archComponent3, coe_finEmbedN3, mapMatrix_arch_finMatN, Units.val_one]

private theorem finPart3_finEmbedN (k : Gf) : finPart3 (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) = k := by
  apply Units.ext
  rw [coe_finPart3, coe_finEmbedN3, mapMatrix_fin_finMatN]

private theorem finPart3_archToAdelic3 (a : Ginf) : finPart3 (archToAdelic3 a) = 1 := by
  apply Units.ext
  rw [coe_finPart3, coe_archToAdelic3, mapMatrix_fin_archMat3, Units.val_one]

private theorem componentAt3_finEmbedN_finPart3 (u : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    componentAt3 (𝓞 ℚ) ℚ u (finEmbedN (Fin 3) (𝓞 ℚ) ℚ (finPart3 g)) = componentAt3 (𝓞 ℚ) ℚ u g := by
  apply Units.ext
  rw [coe_componentAt3, coe_componentAt3, coe_finEmbedN3, coe_finPart3, ← RingHom.mapMatrix_comp,
    RingHom.comp_apply, RingHom.comp_apply, mapMatrix_fin_finMatN]

private def archFinMul (p : Ginf × Gf) : AdelicGL 3 (𝓞 ℚ) ℚ :=
  archToAdelic3 p.1 * finEmbedN (Fin 3) (𝓞 ℚ) ℚ p.2

private theorem continuous_archFinMul : Continuous archFinMul :=
  (continuous_archToAdelic3.comp continuous_fst).mul (continuous_finEmbedN3.comp continuous_snd)

private theorem archComponent3_archFinMul (p : Ginf × Gf) : archComponent3 (𝓞 ℚ) ℚ (archFinMul p) = p.1 := by
  rw [archFinMul, map_mul, archComponent3_archToAdelic3, archComponent3_finEmbedN, mul_one]

private theorem finPart3_archFinMul (p : Ginf × Gf) : finPart3 (archFinMul p) = p.2 := by
  rw [archFinMul, map_mul, finPart3_archToAdelic3, finPart3_finEmbedN, one_mul]

private theorem archFinMul_archComponent3_finPart3 (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    archFinMul (archComponent3 (𝓞 ℚ) ℚ g, finPart3 g) = g := by
  refine adelicGL3_ext (fun u => ?_) ?_
  · simp only [archFinMul, map_mul, componentAt3_archToAdelic3, one_mul, componentAt3_finEmbedN_finPart3]
  · rw [archComponent3_archFinMul]

private def archFinHomeomorph : Ginf × Gf ≃ₜ AdelicGL 3 (𝓞 ℚ) ℚ where
  toFun := archFinMul
  invFun g := (archComponent3 (𝓞 ℚ) ℚ g, finPart3 g)
  left_inv p := by simp only [archComponent3_archFinMul, finPart3_archFinMul]
  right_inv g := archFinMul_archComponent3_finPart3 g
  continuous_toFun := continuous_archFinMul
  continuous_invFun := continuous_archComponent3.prodMk continuous_finPart3

private theorem archFinHomeomorph_apply (p : Ginf × Gf) : archFinHomeomorph p = archFinMul p := rfl

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

end SplittingCarried
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

section ArchHalfCarried

open NumberField Matrix
open scoped MatrixGroups

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.AdelicGL CubicInduction.globalPointsGL"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "SlabL2.realCoordinate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 LocalGL3 heckeGen1 heckeGen2 cosetSum IsCosetEigenfunction IsRightInvariant archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 one_le_gauge3 one_le_archGauge3 IsModerateGrowth3 matrixFin_ext matrixAdele_ext localMatN localMatN_apply_self localMatN_apply_of_ne mapMatrix_localMatN_self mapMatrix_localMatN_of_ne localEmbedN finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN finEmbedN localToAdelic3 exists_mul_eq_unipotent_mul_diagonal_mul_compact smoothingOperator_mem_cuspFunctions_of_isCuspidalAlong exists_isCompactOperator_cuspidalSubspace_smoothingOperator exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous exists_inner_toL2_translateRight_ne_zero_of_isCosetEigenfunction measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator"
p2m_open "LanglandsTunnell.CubicInduction~isCompact_localMaximalCompact3~det_radicalP21~det_radicalP12 LanglandsTunnell~CubicInduction.isCompact_localMaximalCompact3"

section ArchHalf

p2m_open "LanglandsTunnell.CubicInduction.SlabL2~exists_isSlabDomain"

private theorem isReal_of_rat (w : InfinitePlace ℚ) : w.IsReal := by
  rw [Subsingleton.elim w Rat.infinitePlace]
  exact Rat.isReal_infinitePlace

private theorem continuous_realCoordinate : Continuous realCoordinate :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).continuous.comp
    (continuous_apply Rat.infinitePlace)

private def ofRealAdele (r : ℝ) : InfiniteAdeleRing ℚ :=
  show (v : InfinitePlace ℚ) → v.Completion from
    fun v => (InfinitePlace.Completion.isometryEquivRealOfIsReal (isReal_of_rat v)).symm r

private theorem continuous_ofRealAdele : Continuous ofRealAdele :=
  continuous_pi fun v => (InfinitePlace.Completion.isometryEquivRealOfIsReal (isReal_of_rat v)).symm.continuous

private theorem realCoordinate_ofRealAdele (r : ℝ) : realCoordinate (ofRealAdele r) = r :=
  (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply r

private theorem ofRealAdele_realCoordinate (x : InfiniteAdeleRing ℚ) : ofRealAdele (realCoordinate x) = x := by
  funext v
  obtain rfl : v = Rat.infinitePlace := Subsingleton.elim _ _
  exact (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).symm_apply_apply
    (x Rat.infinitePlace)

private def realCoordinateRingEquiv : InfiniteAdeleRing ℚ ≃+* ℝ where
  toFun := realCoordinate
  invFun := ofRealAdele
  left_inv := ofRealAdele_realCoordinate
  right_inv := realCoordinate_ofRealAdele
  map_mul' := map_mul realCoordinate
  map_add' := map_add realCoordinate

private def realCoordinateHomeomorph : InfiniteAdeleRing ℚ ≃ₜ ℝ where
  toFun := realCoordinate
  invFun := ofRealAdele
  left_inv := ofRealAdele_realCoordinate
  right_inv := realCoordinate_ofRealAdele
  continuous_toFun := continuous_realCoordinate
  continuous_invFun := continuous_ofRealAdele

private theorem
    realCoordinateHomeomorph_apply (x : InfiniteAdeleRing ℚ) : realCoordinateHomeomorph x = realCoordinate x :=
  rfl

private theorem realCoordinateHomeomorph_symm_apply (r : ℝ) : realCoordinateHomeomorph.symm r = ofRealAdele r :=
  rfl

private theorem realCoordinateRingEquiv_symm_apply (r : ℝ) : realCoordinateRingEquiv.symm r = ofRealAdele r :=
  rfl

private def archEntries3 (a : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Fin 3 → Fin 3 → ℝ :=
  fun i j => SlabL2.realCoordinate ((a : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j)

private theorem continuous_archEntries3 : Continuous archEntries3 :=
  continuous_pi fun i => continuous_pi fun j =>
    continuous_realCoordinate.comp (Units.continuous_val.matrix_elem i j)

private theorem isCompact_preimage_archEntries3 {T : Set (Fin 3 → Fin 3 → ℝ)} (hT : IsCompact T)
    (hTloc : T ⊆ {m | (Matrix.of m).det ≠ 0}) : IsCompact (archEntries3 ⁻¹' T) := by
  haveI : CompactSpace T := isCompact_iff_compactSpace.mp hT
  have hdet : ∀ x : T, IsUnit (Matrix.of x.1).det := fun x => isUnit_iff_ne_zero.mpr (hTloc x.2)
  let φ : ℝ →+* InfiniteAdeleRing ℚ := realCoordinateRingEquiv.symm
  let u : T → GL (Fin 3) ℝ := fun x =>
    ⟨Matrix.of x.1, (Matrix.of x.1)⁻¹, Matrix.mul_nonsing_inv _ (hdet x), Matrix.nonsing_inv_mul _ (hdet x)⟩
  let j : T → GL (Fin 3) (InfiniteAdeleRing ℚ) := fun x => Units.map (RingHom.mapMatrix φ).toMonoidHom (u x)
  have hof : Continuous fun x : T => Matrix.of x.1 := continuous_subtype_val
  have hinv : Continuous fun x : T => (Matrix.of x.1)⁻¹ := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    have hc : ContinuousAt Ring.inverse (Matrix.of x.1).det := by
      simpa using NormedRing.inverse_continuousAt (hdet x).unit
    exact (continuousAt_matrix_inv (Matrix.of x.1) hc).comp (f := fun x : T => Matrix.of x.1) hof.continuousAt
  have hj : Continuous j := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · refine continuous_matrix fun i k => ?_
      exact continuous_ofRealAdele.comp (hof.matrix_elem i k)
    · refine continuous_matrix fun i k => ?_
      exact continuous_ofRealAdele.comp (hinv.matrix_elem i k)
  have hsub : archEntries3 ⁻¹' T ⊆ Set.range j := by
    intro a ha
    refine ⟨⟨archEntries3 a, ha⟩, Units.ext (Matrix.ext fun i k => ?_)⟩
    show ofRealAdele (realCoordinate ((a : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i k)) = _
    exact ofRealAdele_realCoordinate _
  exact (isCompact_range hj).of_isClosed_subset (hT.isClosed.preimage continuous_archEntries3) hsub

private theorem hasCompactSupport_comp_archEntries3 {α : (Fin 3 → Fin 3 → ℝ) → ℂ} (hα : IsSmoothArchFactor α) :
    HasCompactSupport fun a => α (archEntries3 a) :=
  (isCompact_preimage_archEntries3 hα.2.1 hα.2.2).of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal (fun _ ha => subset_closure ha) ((isClosed_tsupport α).preimage continuous_archEntries3))

private theorem continuous_comp_archEntries3 {α : (Fin 3 → Fin 3 → ℝ) → ℂ} (hα : IsSmoothArchFactor α) :
    Continuous fun a => α (archEntries3 a) :=
  (hα.1.continuous).comp continuous_archEntries3

end ArchHalf
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

end ArchHalfCarried
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

section ParametricKernelCarried

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory Metric
p2m_open "LanglandsTunnell.CubicInduction~isCompact_localMaximalCompact3~det_radicalP21~det_radicalP12 P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2~exists_isSlabDomain"

noncomputable section

namespace SmoothingKernels

private theorem isOpen_setOf_det_ne_zero : IsOpen {m : Fin 3 → Fin 3 → ℝ | (Matrix.of m).det ≠ 0} := by
  have hc : Continuous fun m : Fin 3 → Fin 3 → ℝ => (Matrix.of m).det :=
    (continuous_id (X := Matrix (Fin 3) (Fin 3) ℝ)).matrix_det
  exact isOpen_ne.preimage hc

private theorem of_archEntries_one : Matrix.of (archEntries 1) = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [archEntries]
    exact map_one realCoordinate
  · simp [archEntries, hij]
    exact map_zero realCoordinate

private theorem det_of_archEntries_one_ne_zero : (Matrix.of (archEntries 1)).det ≠ 0 := by
  rw [of_archEntries_one, Matrix.det_one]
  exact one_ne_zero

private theorem exists_isSmoothArchFactor : ∃ α : (Fin 3 → Fin 3 → ℝ) → ℂ, IsSmoothArchFactor α := by
  have h₀ : archEntries 1 ∈ {m : Fin 3 → Fin 3 → ℝ | (Matrix.of m).det ≠ 0} := det_of_archEntries_one_ne_zero
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_setOf_det_ne_zero _ h₀
  let f : ContDiffBump (archEntries 1) := ⟨ε / 2, 3 * ε / 4, by positivity, by linarith⟩
  refine ⟨fun m => ((f m : ℝ) : ℂ), Complex.ofRealCLM.contDiff.comp f.contDiff,
    f.hasCompactSupport.comp_left Complex.ofReal_zero, ?_⟩
  intro m hm
  have hm' : m ∈ tsupport f := tsupport_comp_subset Complex.ofReal_zero (f : _ → ℝ) hm
  rw [f.tsupport_eq] at hm'
  exact hball (closedBall_subset_ball (by show 3 * ε / 4 < ε; linarith) hm')

private theorem exists_isSmoothingKernel_support_subset {r : ℝ} (hr : 0 < r)
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ)))
    (hopen : ∀ p, IsOpen (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))))
    (hcpt : ∀ p, IsCompact (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))))
    (hcof : ∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    ∃ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ ∧
      (∀ g, φ g = (((φ g).re : ℝ) : ℂ) ∧ 0 ≤ (φ g).re) ∧
      Function.support φ ⊆
        {g | archEntries g ∈ ball (archEntries 1) r} ∩ {g | ∀ p, componentAt3 (𝓞 ℚ) ℚ p g ∈ K' p} ∧
      φ 1 ≠ 0 := by
  have h₀ : archEntries 1 ∈ {m : Fin 3 → Fin 3 → ℝ | (Matrix.of m).det ≠ 0} := det_of_archEntries_one_ne_zero
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_setOf_det_ne_zero _ h₀
  set ρ : ℝ := min ε r
  have hρ : 0 < ρ := lt_min hε hr
  have hρε : ρ ≤ ε := min_le_left ε r
  have hρr : ρ ≤ r := min_le_right ε r
  let f : ContDiffBump (archEntries 1) := ⟨ρ / 2, 3 * ρ / 4, by positivity, by linarith⟩

  have hsupp : ∀ m, f m ≠ 0 → m ∈ ball (archEntries 1) ρ := by
    intro m hm
    have hm' : m ∈ tsupport (f : (Fin 3 → Fin 3 → ℝ) → ℝ) := subset_tsupport _ hm
    rw [f.tsupport_eq] at hm'
    exact closedBall_subset_ball (by show 3 * ρ / 4 < ρ; linarith) hm'
  let α : (Fin 3 → Fin 3 → ℝ) → ℂ := fun m => ((f m : ℝ) : ℂ)
  have hα : IsSmoothArchFactor α := by
    refine ⟨Complex.ofRealCLM.contDiff.comp f.contDiff, f.hasCompactSupport.comp_left Complex.ofReal_zero, ?_⟩
    intro m hm
    have hm' : m ∈ tsupport f := tsupport_comp_subset Complex.ofReal_zero (f : _ → ℝ) hm
    rw [f.tsupport_eq] at hm'
    exact hball (ball_subset_ball hρε (closedBall_subset_ball (by show 3 * ρ / 4 < ρ; linarith) hm'))
  let S : Set (AdelicGL 3 (𝓞 ℚ) ℚ) := {x | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p}
  refine ⟨fun g => α (archEntries g) * S.indicator (fun _ => (1 : ℂ)) g, ?_, ?_, ?_, ?_⟩
  · exact ⟨α, K', hα, fun p => ⟨hopen p, hcpt p⟩, hcof, fun g => rfl⟩
  · intro g
    by_cases hg : g ∈ S
    · refine ⟨?_, ?_⟩
      · simp only [Set.indicator_of_mem hg, mul_one, α, Complex.ofReal_re]
      · simp only [Set.indicator_of_mem hg, mul_one, α, Complex.ofReal_re]
        exact f.nonneg
    · simp [Set.indicator_of_notMem hg]
  · intro g hg
    have hg' : α (archEntries g) ≠ 0 ∧ S.indicator (fun _ => (1 : ℂ)) g ≠ 0 := mul_ne_zero_iff.1 hg
    refine ⟨?_, ?_⟩
    · have hf : f (archEntries g) ≠ 0 := fun h => hg'.1 (by simp [α, h])
      exact ball_subset_ball hρr (hsupp _ hf)
    · by_contra hgS
      exact hg'.2 (Set.indicator_of_notMem hgS _)
  · have h1 : (1 : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ S := fun p => by
      show componentAt3 (𝓞 ℚ) ℚ p 1 ∈ K' p
      rw [map_one]
      exact one_mem _
    have hf1 : f (archEntries 1) = 1 := f.one_of_mem_closedBall (mem_closedBall_self f.rIn_pos.le)
    simp only [Set.indicator_of_mem h1, mul_one]
    show ((f (archEntries 1) : ℝ) : ℂ) ≠ 0
    rw [hf1]
    exact one_ne_zero

end SmoothingKernels
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

end ParametricKernelCarried
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

section ApproximateIdentity

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory Filter Topology Metric
open scoped MatrixGroups
p2m_open "LanglandsTunnell.CubicInduction.SlabL2~exists_isSlabDomain"

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.AdelicGL CubicInduction.globalPointsGL"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "SlabL2.realCoordinate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 LocalGL3 heckeGen1 heckeGen2 cosetSum IsCosetEigenfunction IsRightInvariant archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 one_le_gauge3 one_le_archGauge3 IsModerateGrowth3 matrixFin_ext matrixAdele_ext localMatN localMatN_apply_self localMatN_apply_of_ne mapMatrix_localMatN_self mapMatrix_localMatN_of_ne localEmbedN finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN finEmbedN localToAdelic3 exists_mul_eq_unipotent_mul_diagonal_mul_compact smoothingOperator_mem_cuspFunctions_of_isCuspidalAlong exists_isCompactOperator_cuspidalSubspace_smoothingOperator exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous exists_inner_toL2_translateRight_ne_zero_of_isCosetEigenfunction measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator"
p2m_open "LanglandsTunnell.CubicInduction~isCompact_localMaximalCompact3~det_radicalP21~det_radicalP12 LanglandsTunnell~CubicInduction.isCompact_localMaximalCompact3"

section Congruence

variable (p : HeightOneSpectrum (𝓞 ℚ))

private theorem valued_mul_le_of_le_of_le_one {x y : p.adicCompletion ℚ} {γ : WithZero (Multiplicative ℤ)}
    (hx : Valued.v x ≤ γ) (hy : Valued.v y ≤ 1) : Valued.v (x * y) ≤ γ := by
  rw [Valuation.map_mul]
  exact mul_le_of_le_of_le_one hx hy

private theorem valued_mul_le_of_le_one_of_le {x y : p.adicCompletion ℚ} {γ : WithZero (Multiplicative ℤ)}
    (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ γ) : Valued.v (x * y) ≤ γ := by
  rw [Valuation.map_mul]
  exact mul_le_of_le_one_of_le hx hy

private theorem
    valued_entries_le_one_of_mem_localMaximalCompact3 {k : LocalGL3 p} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    (∀ i j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ 1) ∧
      ∀ i j, Valued.v (((k⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ 1 :=
  hk

private def congruenceLevel (n : ℕ) : Subgroup (LocalGL3 p) where
  carrier := {k | k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p ∧
    ∀ i j, Valued.v (((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) - 1) i j) ≤ WithZero.exp (-(n : ℤ))}
  one_mem' := ⟨one_mem _, fun i j => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun i j => ?_⟩
    have hbint := (valued_entries_le_one_of_mem_localMaximalCompact3 p hb).1
    have hid : ((a * b : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) - 1 =
        ((a : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) - 1) * (b : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) +
          ((b : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) - 1) := by
      rw [Units.val_mul, sub_mul, one_mul, sub_add_sub_cancel]
    rw [hid, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_three]
    refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (hb' i j))
    refine le_trans (Valuation.map_add _ _ _) (max_le (le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)) ?_)
    · exact valued_mul_le_of_le_of_le_one p (ha' i 0) (hbint 0 j)
    · exact valued_mul_le_of_le_of_le_one p (ha' i 1) (hbint 1 j)
    · exact valued_mul_le_of_le_of_le_one p (ha' i 2) (hbint 2 j)
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun i j => ?_⟩
    have hainv := (valued_entries_le_one_of_mem_localMaximalCompact3 p ha).2
    have hid : ((a⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) - 1 =
        -(((a⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) *
          ((a : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) - 1)) := by
      rw [Matrix.mul_sub, Matrix.mul_one, Units.inv_mul, neg_sub]
    rw [hid, Matrix.neg_apply, Valuation.map_neg, Matrix.mul_apply, Fin.sum_univ_three]
    refine le_trans (Valuation.map_add _ _ _) (max_le (le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)) ?_)
    · exact valued_mul_le_of_le_one_of_le p (hainv i 0) (ha' 0 j)
    · exact valued_mul_le_of_le_one_of_le p (hainv i 1) (ha' 1 j)
    · exact valued_mul_le_of_le_one_of_le p (hainv i 2) (ha' 2 j)

private theorem congruenceLevel_le (n : ℕ) : congruenceLevel p n ≤ localMaximalCompact3 (𝓞 ℚ) ℚ p := fun _ hk => hk.1

private theorem
    congruenceLevel_antitone {m n : ℕ} (h : m ≤ n) : congruenceLevel p n ≤ congruenceLevel p m := fun _ hk =>
  ⟨hk.1, fun i j => (hk.2 i j).trans (WithZero.exp_le_exp.mpr (by omega))⟩

private theorem isClosed_setOf_forall_entry_mem {B : Set (p.adicCompletion ℚ)} (hB : IsClosed B) :
    IsClosed {M : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ) | ∀ i j, M i j ∈ B} := by
  simp_rw [Set.setOf_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j => hB.preimage (continuous_id.matrix_elem i j)

private theorem congruenceLevel_coe_eq (n : ℕ) :
    (congruenceLevel p n : Set (LocalGL3 p)) = (localMaximalCompact3 (𝓞 ℚ) ℚ p : Set (LocalGL3 p)) ∩
      (fun k : LocalGL3 p => (k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) - 1) ⁻¹'
        {M | ∀ i j, M i j ∈ {z : p.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (-(n : ℤ))}} :=
  Set.ext fun _ => Iff.rfl

private theorem isOpen_congruenceLevel (n : ℕ) : IsOpen (congruenceLevel p n : Set (LocalGL3 p)) := by
  obtain ⟨t, ht, hvt⟩ := AdelicLevel.exists_valued_eq_exp_neg (K := ℚ) p n
  have hB : IsOpen {z : p.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (-(n : ℤ))} := by
    rw [← hvt]
    exact AdelicLevel.isOpen_setOf_valued_le p t ht
  rw [congruenceLevel_coe_eq]
  exact (isOpen_localMaximalCompact3 p).inter
    ((Units.continuous_val.sub continuous_const).isOpen_preimage _ (isOpen_setOf_forall_entry_mem p hB))

private theorem isClosed_congruenceLevel (n : ℕ) : IsClosed (congruenceLevel p n : Set (LocalGL3 p)) := by
  obtain ⟨t, ht, hvt⟩ := AdelicLevel.exists_valued_eq_exp_neg (K := ℚ) p n
  have hB : IsClosed {z : p.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (-(n : ℤ))} := by
    rw [← hvt, AdelicLevel.setOf_valued_le_eq_preimage p t ht]
    exact (AdelicLevel.isClosed_adicCompletionIntegers (K := ℚ) p).preimage (continuous_id.mul continuous_const)
  rw [congruenceLevel_coe_eq]
  exact (isCompact_localMaximalCompact3 p).isClosed.inter
    ((isClosed_setOf_forall_entry_mem p hB).preimage (Units.continuous_val.sub continuous_const))

private theorem isCompact_congruenceLevel (n : ℕ) : IsCompact (congruenceLevel p n : Set (LocalGL3 p)) :=
  (isCompact_localMaximalCompact3 p).of_isClosed_subset (isClosed_congruenceLevel p n) (congruenceLevel_le p n)

private theorem
    eq_one_of_forall_mem_congruenceLevel {k : LocalGL3 p} (hk : ∀ n : ℕ, k ∈ congruenceLevel p n) : k = 1 := by
  apply Units.ext
  rw [Units.val_one, ← sub_eq_zero]
  ext i j
  rw [Matrix.zero_apply]
  by_contra hx
  have hne : Valued.v (((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) - 1) i j) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr hx
  obtain ⟨m, hm⟩ :
      ∃ m : ℤ, Valued.v (((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) - 1) i j) = WithZero.exp m :=
    ⟨_, (WithZero.exp_log hne).symm⟩
  have h := (hk ((-m).toNat + 1)).2 i j
  rw [hm, WithZero.exp_le_exp] at h
  have := Int.self_le_toNat (-m)
  push_cast at h
  omega

end Congruence
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

private def placeIndex : HeightOneSpectrum (𝓞 ℚ) → ℕ :=
  Classical.choose (Countable.exists_injective_nat (HeightOneSpectrum (𝓞 ℚ)))

private theorem placeIndex_injective : Function.Injective placeIndex :=
  Classical.choose_spec (Countable.exists_injective_nat (HeightOneSpectrum (𝓞 ℚ)))

private def shrinkingLevel (n : ℕ) (p : HeightOneSpectrum (𝓞 ℚ)) : Subgroup (LocalGL3 p) :=
  if placeIndex p < n then congruenceLevel p n else localMaximalCompact3 (𝓞 ℚ) ℚ p

private theorem isOpen_shrinkingLevel (n : ℕ) (p : HeightOneSpectrum (𝓞 ℚ)) :
    IsOpen (shrinkingLevel n p : Set (LocalGL3 p)) := by
  unfold shrinkingLevel
  split_ifs
  · exact isOpen_congruenceLevel p n
  · exact isOpen_localMaximalCompact3 p

private theorem isCompact_shrinkingLevel (n : ℕ) (p : HeightOneSpectrum (𝓞 ℚ)) :
    IsCompact (shrinkingLevel n p : Set (LocalGL3 p)) := by
  unfold shrinkingLevel
  split_ifs
  · exact isCompact_congruenceLevel p n
  · exact isCompact_localMaximalCompact3 p

private theorem eventually_shrinkingLevel_eq (n : ℕ) :
    ∀ᶠ p in Filter.cofinite, shrinkingLevel n p = localMaximalCompact3 (𝓞 ℚ) ℚ p := by
  rw [Filter.eventually_cofinite]
  refine (Set.Finite.preimage placeIndex_injective.injOn (Set.finite_lt_nat n)).subset fun p hp => ?_
  by_contra h
  exact hp (if_neg h)

private theorem shrinkingLevel_antitone {m n : ℕ} (h : m ≤ n) (p : HeightOneSpectrum (𝓞 ℚ)) :
    shrinkingLevel n p ≤ shrinkingLevel m p := by
  unfold shrinkingLevel
  by_cases hm : placeIndex p < m
  · rw [if_pos hm, if_pos (lt_of_lt_of_le hm h)]
    exact congruenceLevel_antitone p h
  · rw [if_neg hm]
    split_ifs
    · exact congruenceLevel_le p n
    · exact le_rfl

private theorem eq_one_of_forall_mem_shrinkingLevel {p : HeightOneSpectrum (𝓞 ℚ)} {k : LocalGL3 p}
    (hk : ∀ n, k ∈ shrinkingLevel n p) : k = 1 := by
  refine eq_one_of_forall_mem_congruenceLevel p fun n => ?_
  have hN := hk (max n (placeIndex p + 1))
  have hidx : placeIndex p < max n (placeIndex p + 1) :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  rw [shrinkingLevel, if_pos hidx] at hN
  exact congruenceLevel_antitone p (le_max_left _ _) hN

private theorem exists_radius_det_ne_zero :
    ∃ ε : ℝ, 0 < ε ∧ closedBall (archEntries 1) ε ⊆ {m : Fin 3 → Fin 3 → ℝ | (Matrix.of m).det ≠ 0} := by
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.isOpen_iff.mp SmoothingKernels.isOpen_setOf_det_ne_zero _ SmoothingKernels.det_of_archEntries_one_ne_zero
  exact ⟨δ / 2, half_pos hδ, (closedBall_subset_ball (half_lt_self hδ)).trans hball⟩

private def detRadius : ℝ := Classical.choose exists_radius_det_ne_zero

private theorem detRadius_pos : 0 < detRadius := (Classical.choose_spec exists_radius_det_ne_zero).1

private theorem closedBall_detRadius_subset :
    closedBall (archEntries 1) detRadius ⊆ {m : Fin 3 → Fin 3 → ℝ | (Matrix.of m).det ≠ 0} :=
  (Classical.choose_spec exists_radius_det_ne_zero).2

private def stageRadius (n : ℕ) : ℝ := detRadius / (n + 1)

private theorem stageRadius_pos (n : ℕ) : 0 < stageRadius n := div_pos detRadius_pos (by positivity)

private theorem stageRadius_le (n : ℕ) : stageRadius n ≤ detRadius :=
  div_le_self detRadius_pos.le (by simp)

private theorem stageRadius_antitone {m n : ℕ} (h : m ≤ n) : stageRadius n ≤ stageRadius m :=
  div_le_div_of_nonneg_left detRadius_pos.le (by positivity) (by exact_mod_cast Nat.succ_le_succ h)

private theorem eq_of_forall_dist_le_stageRadius {x y : Fin 3 → Fin 3 → ℝ} (h : ∀ n : ℕ, dist x y ≤ stageRadius n) :
    x = y := by
  by_contra hxy
  have hd : 0 < dist x y := dist_pos.mpr hxy
  obtain ⟨n, hn⟩ := exists_nat_gt (detRadius / dist x y)
  have h1 := (div_lt_iff₀ hd).mp hn
  have h2 := h n
  rw [stageRadius, le_div_iff₀ (by positivity)] at h2
  nlinarith

private theorem archEntries_eq_archEntries3 (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    archEntries g = archEntries3 (archComponent3 (𝓞 ℚ) ℚ g) :=
  rfl

private theorem continuous_archEntries : Continuous archEntries :=
  continuous_archEntries3.comp continuous_archComponent3

private theorem archEntries3_injective : Function.Injective archEntries3 := fun _ _ h =>
  Units.ext (Matrix.ext fun i j =>
    (Function.LeftInverse.injective ofRealAdele_realCoordinate) (congrFun (congrFun h i) j))

private theorem continuous_componentAt3 (p : HeightOneSpectrum (𝓞 ℚ)) : Continuous (componentAt3 (𝓞 ℚ) ℚ p) :=
  continuous_generalLinearGroup_map _
    ((AdelicLevel.continuous_finAdeleEval (𝓞 ℚ) ℚ p).comp (AdelicLevel.continuous_adeleFin (𝓞 ℚ) ℚ))

private theorem setOf_forall_componentAt3_mem_eq (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p)) :
    {g : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p g ∈ K' p} =
      finPart3 ⁻¹' {k | ∀ p, componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ∈ K' p} := by
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_preimage, componentAt3_finEmbedN_finPart3]

private theorem isOpen_setOf_forall_componentAt3_mem (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p))
    (hopen : ∀ p, IsOpen (K' p : Set (LocalGL3 p)))
    (hcof : ∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    IsOpen {g : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p g ∈ K' p} := by
  rw [setOf_forall_componentAt3_mem_eq]
  exact (isOpen_setOf_forall_componentAt3_finEmbedN_mem K' hopen hcof).preimage continuous_finPart3

private theorem isClosed_setOf_forall_componentAt3_mem (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p))
    (hcpt : ∀ p, IsCompact (K' p : Set (LocalGL3 p))) :
    IsClosed {g : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p g ∈ K' p} := by
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun p => (hcpt p).isClosed.preimage (continuous_componentAt3 p)

private def stageSet (n : ℕ) : Set (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  {g | archEntries g ∈ closedBall (archEntries 1) (stageRadius n)} ∩
    {g | ∀ p, componentAt3 (𝓞 ℚ) ℚ p g ∈ shrinkingLevel n p}

private theorem isClosed_stageSet (n : ℕ) : IsClosed (stageSet n) :=
  (isClosed_closedBall.preimage continuous_archEntries).inter
    (isClosed_setOf_forall_componentAt3_mem (shrinkingLevel n) (isCompact_shrinkingLevel n))

private theorem stageSet_subset_image (n : ℕ) :
    stageSet n ⊆ archFinMul '' ((archEntries3 ⁻¹' closedBall (archEntries 1) (stageRadius n)) ×ˢ
      {k | ∀ p, componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ∈ shrinkingLevel n p}) := by
  rintro g ⟨hg1, hg2⟩
  refine ⟨(archComponent3 (𝓞 ℚ) ℚ g, finPart3 g), ⟨hg1, fun p => ?_⟩, archFinMul_archComponent3_finPart3 g⟩
  rw [componentAt3_finEmbedN_finPart3]
  exact hg2 p

private theorem isCompact_stageSet (n : ℕ) : IsCompact (stageSet n) :=
  (((isCompact_preimage_archEntries3 (isCompact_closedBall _ _)
      ((closedBall_subset_closedBall (stageRadius_le n)).trans closedBall_detRadius_subset)).prod
    (isCompact_setOf_forall_componentAt3_finEmbedN_mem (shrinkingLevel n) (isOpen_shrinkingLevel n)
      (isCompact_shrinkingLevel n) (eventually_shrinkingLevel_eq n))).image continuous_archFinMul).of_isClosed_subset
    (isClosed_stageSet n) (stageSet_subset_image n)

private theorem stageSet_antitone {m n : ℕ} (h : m ≤ n) : stageSet n ⊆ stageSet m := fun _ hg =>
  ⟨closedBall_subset_closedBall (stageRadius_antitone h) hg.1, fun p => shrinkingLevel_antitone h p (hg.2 p)⟩

private theorem eq_one_of_forall_mem_stageSet {g : AdelicGL 3 (𝓞 ℚ) ℚ} (hg : ∀ n, g ∈ stageSet n) : g = 1 := by
  refine adelicGL3_ext (fun p => ?_) ?_
  · rw [map_one]
    exact eq_one_of_forall_mem_shrinkingLevel fun n => (hg n).2 p
  · rw [map_one]
    have h0 : archEntries g = archEntries 1 := eq_of_forall_dist_le_stageRadius fun n => mem_closedBall.mp (hg n).1
    have h1 : archEntries3 (archComponent3 (𝓞 ℚ) ℚ g) =
        archEntries3 (archComponent3 (𝓞 ℚ) ℚ (1 : AdelicGL 3 (𝓞 ℚ) ℚ)) :=
      h0
    have h2 := archEntries3_injective h1
    rwa [map_one] at h2

private theorem
    continuous_of_isSmoothingKernel {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hφ : IsSmoothingKernel φ) : Continuous φ := by
  obtain ⟨α, K', hα, hK, hcof, hφeq⟩ := hφ
  have hfun : φ = fun g => α (archEntries g) *
      Set.indicator {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} (fun _ => (1 : ℂ)) g :=
    funext hφeq
  rw [hfun]
  have hclopen : IsClopen {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} :=
    ⟨isClosed_setOf_forall_componentAt3_mem K' fun p => (hK p).2,
      isOpen_setOf_forall_componentAt3_mem K' (fun p => (hK p).1) hcof⟩
  refine (hα.1.continuous.comp continuous_archEntries).mul (continuous_const.indicator ?_)
  rw [hclopen.frontier_eq]
  simp

private def _root_.LanglandsTunnell.CubicInduction.HasApproximateIdentity : Prop :=
  ∀ U ∈ 𝓝 (1 : AdelicGL 3 (𝓞 ℚ) ℚ), ∃ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
    IsSmoothingKernel φ ∧ (∀ g, φ g = ((φ g).re : ℂ) ∧ 0 ≤ (φ g).re) ∧ Function.support φ ⊆ U ∧
      Integrable φ (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) ∧
        0 < (∫ g, φ g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)).re

p2m_export "LanglandsTunnell.CubicInduction" "HasApproximateIdentity"

private theorem hasApproximateIdentity : HasApproximateIdentity := by
  intro U hU
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  obtain ⟨n, hn⟩ : ∃ n, stageSet n ⊆ U := by
    refine exists_subset_nhds_of_isCompact'
      (fun m n => ⟨max m n, stageSet_antitone (le_max_left m n), stageSet_antitone (le_max_right m n)⟩)
      isCompact_stageSet isClosed_stageSet fun g hg => ?_
    rw [Set.mem_iInter] at hg
    rw [eq_one_of_forall_mem_stageSet hg]
    exact hU
  obtain ⟨φ, hφ, hreal, hsupp, h1⟩ := SmoothingKernels.exists_isSmoothingKernel_support_subset (stageRadius_pos n)
    (shrinkingLevel n) (isOpen_shrinkingLevel n) (isCompact_shrinkingLevel n) (eventually_shrinkingLevel_eq n)
  have hsuppV : Function.support φ ⊆ stageSet n :=
    hsupp.trans (Set.inter_subset_inter (fun _ hg => ball_subset_closedBall hg) subset_rfl)
  have hcont : Continuous φ := continuous_of_isSmoothingKernel hφ
  have hcs : HasCompactSupport φ :=
    (isCompact_stageSet n).of_isClosed_subset (isClosed_tsupport φ) (closure_minimal hsuppV (isClosed_stageSet n))
  have hint : Integrable φ (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) :=
    hcont.integrable_of_hasCompactSupport hcs
  refine ⟨φ, hφ, hreal, hsuppV.trans hn, hint, ?_⟩
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  rw [← hre]
  have hnn : (0 : AdelicGL 3 (𝓞 ℚ) ℚ → ℝ) ≤ fun g => (φ g).re := fun g => (hreal g).2
  rw [integral_pos_iff_support_of_nonneg hnn hint.re]
  have hO : IsOpen {g : AdelicGL 3 (𝓞 ℚ) ℚ | 0 < (φ g).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp hcont)
  have h1' : (1 : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ {g : AdelicGL 3 (𝓞 ℚ) ℚ | 0 < (φ g).re} := by
    obtain ⟨hre1, hnonneg⟩ := hreal 1
    refine lt_of_le_of_ne hnonneg fun h0 => h1 ?_
    rw [hre1, ← h0]
    simp
  exact (hO.measure_pos _ ⟨1, h1'⟩).trans_le (measure_mono fun g hg => ne_of_gt hg)

private theorem hasCompactSupport_of_isSmoothingKernel {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hφ : IsSmoothingKernel φ) :
    HasCompactSupport φ := by
  obtain ⟨α, K', hα, hK, hcof, hφeq⟩ := hφ
  have hT := isCompact_preimage_archEntries3 hα.2.1 hα.2.2
  have hF := isCompact_setOf_forall_componentAt3_finEmbedN_mem K' (fun p => (hK p).1) (fun p => (hK p).2) hcof
  have hC := (hT.prod hF).image continuous_archFinMul
  refine hC.of_isClosed_subset (isClosed_tsupport φ) (closure_minimal ?_ hC.isClosed)
  intro g hg
  rw [Function.mem_support, hφeq] at hg
  have hg' := mul_ne_zero_iff.1 hg
  refine ⟨(archComponent3 (𝓞 ℚ) ℚ g, finPart3 g), ⟨subset_tsupport _ hg'.1, fun p => ?_⟩,
    archFinMul_archComponent3_finPart3 g⟩
  rw [componentAt3_finEmbedN_finPart3]
  have hgS : g ∈ {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} := by
    by_contra hS
    exact hg'.2 (Set.indicator_of_notMem hS _)
  exact hgS p

private theorem integrable_of_isSmoothingKernel {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hφ : IsSmoothingKernel φ) :
    Integrable φ (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  exact (continuous_of_isSmoothingKernel hφ).integrable_of_hasCompactSupport
    (hasCompactSupport_of_isSmoothingKernel hφ)

private theorem exists_isSmoothArchFactor_support_subset {r : ℝ} (hr : 0 < r) :
    ∃ α : (Fin 3 → Fin 3 → ℝ) → ℂ, IsSmoothArchFactor α ∧ (∀ m, α m = ((α m).re : ℂ) ∧ 0 ≤ (α m).re) ∧
      (∀ m, α m ≠ 0 → m ∈ ball (archEntries 1) r) ∧ α (archEntries 1) ≠ 0 := by
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.1 SmoothingKernels.isOpen_setOf_det_ne_zero _ SmoothingKernels.det_of_archEntries_one_ne_zero
  set ρ : ℝ := min ε r
  have hρ : 0 < ρ := lt_min hε hr
  have hρε : ρ ≤ ε := min_le_left ε r
  have hρr : ρ ≤ r := min_le_right ε r
  let f : ContDiffBump (archEntries 1) := ⟨ρ / 2, 3 * ρ / 4, by positivity, by linarith⟩
  have hsupp : ∀ m, f m ≠ 0 → m ∈ ball (archEntries 1) ρ := by
    intro m hm
    have hm' : m ∈ tsupport (f : (Fin 3 → Fin 3 → ℝ) → ℝ) := subset_tsupport _ hm
    rw [f.tsupport_eq] at hm'
    exact closedBall_subset_ball (by show 3 * ρ / 4 < ρ; linarith) hm'
  refine ⟨fun m => ((f m : ℝ) : ℂ), ?_, fun m => ⟨by simp, by simpa using f.nonneg⟩, fun m hm => ?_, ?_⟩
  · refine ⟨Complex.ofRealCLM.contDiff.comp f.contDiff, f.hasCompactSupport.comp_left Complex.ofReal_zero, ?_⟩
    intro m hm
    have hm' : m ∈ tsupport f := tsupport_comp_subset Complex.ofReal_zero (f : _ → ℝ) hm
    rw [f.tsupport_eq] at hm'
    exact hball (ball_subset_ball hρε (closedBall_subset_ball (by show 3 * ρ / 4 < ρ; linarith) hm'))
  · exact ball_subset_ball hρr (hsupp m fun h => hm (by simp [h]))
  · have hf1 : f (archEntries 1) = 1 := f.one_of_mem_closedBall (mem_closedBall_self f.rIn_pos.le)
    simp [hf1]

private theorem exists_isSmoothArchFactor_and_level_eq_of_mem_nhds (v : HeightOneSpectrum (𝓞 ℚ))
    (Kf : Subgroup (LocalGL3 v)) (hKo : IsOpen (Kf : Set (LocalGL3 v))) (hKc : IsCompact (Kf : Set (LocalGL3 v)))
    (N : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hN : N ∈ 𝓝 (1 : AdelicGL 3 (𝓞 ℚ) ℚ)) :
    ∃ (α : (Fin 3 → Fin 3 → ℝ) → ℂ)
      (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))),
      IsSmoothArchFactor α ∧
      (∀ p, IsOpen (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))) ∧
        IsCompact (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ)))) ∧
      (∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) ∧
      K' v = Kf ∧
      (∀ m, α m = ((α m).re : ℂ) ∧ 0 ≤ (α m).re) ∧
      (0 < ∫ g, (α (archEntries g) *
          Set.indicator {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} (fun _ => (1 : ℂ)) g).re
            ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)) ∧
      ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        α (archEntries g) *
            Set.indicator {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} (fun _ => (1 : ℂ)) g ≠ 0 →
          g * (localToAdelic3 v (componentAt3 (𝓞 ℚ) ℚ v g))⁻¹ ∈ N := by
  classical
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  obtain ⟨n, hn⟩ : ∃ n, stageSet n ⊆ N := by
    refine exists_subset_nhds_of_isCompact'
      (fun m n => ⟨max m n, stageSet_antitone (le_max_left m n), stageSet_antitone (le_max_right m n)⟩)
      isCompact_stageSet isClosed_stageSet fun g hg => ?_
    rw [Set.mem_iInter] at hg
    rw [eq_one_of_forall_mem_stageSet hg]
    exact hN
  obtain ⟨α, hα, hreal, hsupp, h1⟩ := exists_isSmoothArchFactor_support_subset (stageRadius_pos n)
  set K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p) := Function.update (shrinkingLevel n) v Kf with hK'
  have hKv : K' v = Kf := Function.update_self v Kf (shrinkingLevel n)
  have hKne : ∀ p, p ≠ v → K' p = shrinkingLevel n p := fun p hp => Function.update_of_ne hp Kf (shrinkingLevel n)
  have hKopen : ∀ p, IsOpen (K' p : Set (LocalGL3 p)) := by
    intro p
    rcases eq_or_ne p v with rfl | hp
    · rw [hKv]
      exact hKo
    · rw [hKne p hp]
      exact isOpen_shrinkingLevel n p
  have hKcpt : ∀ p, IsCompact (K' p : Set (LocalGL3 p)) := by
    intro p
    rcases eq_or_ne p v with rfl | hp
    · rw [hKv]
      exact hKc
    · rw [hKne p hp]
      exact isCompact_shrinkingLevel n p
  have hKcof : ∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p :=
    ((eventually_shrinkingLevel_eq n).and (Filter.eventually_cofinite_ne v)).mono fun p hp => by
      rw [hKne p hp.2]
      exact hp.1
  set S : Set (AdelicGL 3 (𝓞 ℚ) ℚ) := {x | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} with hS
  set φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ := fun g => α (archEntries g) * S.indicator (fun _ => (1 : ℂ)) g with hφdef
  have hsk : IsSmoothingKernel φ := ⟨α, K', hα, fun p => ⟨hKopen p, hKcpt p⟩, hKcof, fun g => rfl⟩
  have hφreal : ∀ g, φ g = ((φ g).re : ℂ) ∧ 0 ≤ (φ g).re := by
    intro g
    by_cases hg : g ∈ S
    · have hφg : φ g = α (archEntries g) := by simp only [φ, Set.indicator_of_mem hg, mul_one]
      rw [hφg]
      exact hreal _
    · have hφg : φ g = 0 := by simp only [φ, Set.indicator_of_notMem hg, mul_zero]
      rw [hφg]
      simp
  have h1S : (1 : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ S := fun p => by
    show componentAt3 (𝓞 ℚ) ℚ p 1 ∈ K' p
    rw [map_one]
    exact one_mem _
  have hφ1 : φ 1 ≠ 0 := by
    have hφg : φ 1 = α (archEntries 1) := by simp only [φ, Set.indicator_of_mem h1S, mul_one]
    rw [hφg]
    exact h1
  have hcont : Continuous φ := continuous_of_isSmoothingKernel hsk
  have hint : Integrable φ (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := integrable_of_isSmoothingKernel hsk
  refine ⟨α, K', hα, fun p => ⟨hKopen p, hKcpt p⟩, hKcof, hKv, hreal, ?_, ?_⟩
  · show 0 < ∫ g, (φ g).re ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)
    have hnn : (0 : AdelicGL 3 (𝓞 ℚ) ℚ → ℝ) ≤ fun g => (φ g).re := fun g => (hφreal g).2
    rw [integral_pos_iff_support_of_nonneg hnn hint.re]
    have hO : IsOpen {g : AdelicGL 3 (𝓞 ℚ) ℚ | 0 < (φ g).re} :=
      isOpen_lt continuous_const (Complex.continuous_re.comp hcont)
    have h1' : (1 : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ {g : AdelicGL 3 (𝓞 ℚ) ℚ | 0 < (φ g).re} := by
      obtain ⟨hre1, hnonneg⟩ := hφreal 1
      refine lt_of_le_of_ne hnonneg fun h0 => hφ1 ?_
      rw [hre1, ← h0]
      simp
    exact (hO.measure_pos _ ⟨1, h1'⟩).trans_le (measure_mono fun g hg => ne_of_gt hg)
  · intro g hg
    have hg' : α (archEntries g) ≠ 0 ∧ S.indicator (fun _ => (1 : ℂ)) g ≠ 0 := mul_ne_zero_iff.1 hg
    have hgS : g ∈ S := by
      by_contra h
      exact hg'.2 (Set.indicator_of_notMem h _)
    set k : LocalGL3 v := componentAt3 (𝓞 ℚ) ℚ v g with hk
    have hcomp : ∀ (w : HeightOneSpectrum (𝓞 ℚ)) (M : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)),
        ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)).mapMatrix M =
          (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix M) :=
      fun w M => by
        ext i j
        rfl
    have harchι : archComponent3 (𝓞 ℚ) ℚ (localToAdelic3 v k) = 1 := by
      apply Units.ext
      rw [Units.val_one]
      show (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (finMatN (Fin 3) (𝓞 ℚ) ℚ
        (localMatN (Fin 3) (𝓞 ℚ) ℚ v (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))) = 1
      rw [mapMatrix_arch_finMatN]
    have hselfι : componentAt3 (𝓞 ℚ) ℚ v (localToAdelic3 v k) = k := by
      apply Units.ext
      show ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)).mapMatrix
        (finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ v (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))) =
          (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
      rw [hcomp, mapMatrix_fin_finMatN, mapMatrix_localMatN_self]
    have hneι : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → componentAt3 (𝓞 ℚ) ℚ w (localToAdelic3 v k) = 1 := by
      intro w hw
      apply Units.ext
      rw [Units.val_one]
      show ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)).mapMatrix
        (finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ v (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))) = 1
      rw [hcomp, mapMatrix_fin_finMatN, mapMatrix_localMatN_of_ne (Fin 3) (𝓞 ℚ) ℚ v _ hw]
    apply hn
    refine ⟨?_, fun p => ?_⟩
    · have harch : archEntries (g * (localToAdelic3 v k)⁻¹) = archEntries g := by
        show archEntries3 (archComponent3 (𝓞 ℚ) ℚ (g * (localToAdelic3 v k)⁻¹)) =
          archEntries3 (archComponent3 (𝓞 ℚ) ℚ g)
        rw [map_mul, map_inv, harchι, inv_one, mul_one]
      show archEntries (g * (localToAdelic3 v k)⁻¹) ∈ closedBall (archEntries 1) (stageRadius n)
      rw [harch]
      exact ball_subset_closedBall (hsupp _ hg'.1)
    · show componentAt3 (𝓞 ℚ) ℚ p (g * (localToAdelic3 v k)⁻¹) ∈ shrinkingLevel n p
      rcases eq_or_ne p v with rfl | hp
      · rw [map_mul, map_inv, hselfι, mul_inv_cancel]
        exact one_mem _
      · rw [map_mul, map_inv, hneι p hp, inv_one, mul_one, ← hKne p hp]
        exact hgS p

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

end ApproximateIdentity
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

end SmoothingKernelBlock
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

section WeakInterchangeBlock

section WeakInterchange

p2m_open "NumberField MeasureTheory LanglandsTunnell.CubicInduction.SlabL2~exists_isSlabDomain"
open scoped InnerProductSpace ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.AdelicGL CubicInduction.globalPointsGL"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "SlabL2.realCoordinate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 LocalGL3 heckeGen1 heckeGen2 cosetSum IsCosetEigenfunction IsRightInvariant archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 one_le_gauge3 one_le_archGauge3 IsModerateGrowth3 matrixFin_ext matrixAdele_ext localMatN localMatN_apply_self localMatN_apply_of_ne mapMatrix_localMatN_self mapMatrix_localMatN_of_ne localEmbedN finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN finEmbedN localToAdelic3 exists_mul_eq_unipotent_mul_diagonal_mul_compact smoothingOperator_mem_cuspFunctions_of_isCuspidalAlong exists_isCompactOperator_cuspidalSubspace_smoothingOperator exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous exists_inner_toL2_translateRight_ne_zero_of_isCosetEigenfunction measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator"
p2m_open "LanglandsTunnell.CubicInduction~isCompact_localMaximalCompact3~det_radicalP21~det_radicalP12 LanglandsTunnell~CubicInduction.isCompact_localMaximalCompact3"

private theorem norm_toL2_eq (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (f : ↥(automorphicSubmodule ω a b Φ₀)) :
    ‖toL2 ω a b Φ₀ f‖ =
      (∫ x, ‖(f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) x‖ ^ (2 : ℝ) ∂domainMeasure a b Φ₀) ^ (1 / (2 : ℝ)) := by
  rw [toL2_apply, Lp.norm_toLp, MemLp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofReal (by positivity)]
  simp only [ENNReal.toReal_ofNat, one_div]
  exact f.2.2.2

private theorem inner_toL2_smoothingOperator_eq_integral_of_norm_eq
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (_hΦ₀ : IsSlabDomain a b Φ₀)
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (_hφ : IsSmoothingKernel φ) (hφc : Continuous φ)
    (hφi : Integrable φ (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀)
    (hmem : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, translateRight g F ∈ cuspFunctions ω a b Φ₀)
    (hiso : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖toL2 ω a b Φ₀ ⟨translateRight g F, (hmem g).1⟩‖ = ‖toL2 ω a b Φ₀ ⟨F, hF.1⟩‖)
    (hRF : smoothingOperator φ F ∈ automorphicSubmodule ω a b Φ₀)
    (h : Carrier a b Φ₀) :
    ⟪h, toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hRF⟩⟫_ℂ =
      ∫ g, φ g * ⟪h, toL2 ω a b Φ₀ ⟨translateRight g F, (hmem g).1⟩⟫_ℂ
        ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  haveI : SigmaFinite (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := sigmaFinite_of_locallyFinite
  haveI : SigmaFinite (domainMeasure a b Φ₀) := by
    unfold domainMeasure slabMeasure
    infer_instance

  set f : AdelicGL 3 (𝓞 ℚ) ℚ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ := fun g x => φ g * (conj (h x) * F (x * g)) with hf_def
  have hf_meas : AEStronglyMeasurable (Function.uncurry f)
      ((NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).prod (domainMeasure a b Φ₀)) := by
    have h1 : AEStronglyMeasurable (fun p : AdelicGL 3 (𝓞 ℚ) ℚ × AdelicGL 3 (𝓞 ℚ) ℚ => φ p.1)
        ((NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).prod (domainMeasure a b Φ₀)) :=
      (hφc.comp continuous_fst).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun p : AdelicGL 3 (𝓞 ℚ) ℚ × AdelicGL 3 (𝓞 ℚ) ℚ => conj (h p.2))
        ((NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).prod (domainMeasure a b Φ₀)) :=
      Complex.continuous_conj.comp_aestronglyMeasurable
        ((Lp.aestronglyMeasurable h).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
    have h3 : AEStronglyMeasurable (fun p : AdelicGL 3 (𝓞 ℚ) ℚ × AdelicGL 3 (𝓞 ℚ) ℚ => F (p.2 * p.1))
        ((NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).prod (domainMeasure a b Φ₀)) :=
      (hF.2.1.comp (continuous_snd.mul continuous_fst)).aestronglyMeasurable
    exact h1.mul (h2.mul h3)

  have hint_x : ∀ g, Integrable (fun x => f g x) (domainMeasure a b Φ₀) := by
    intro g
    have hI := L2.integrable_inner (𝕜 := ℂ) h (toL2 ω a b Φ₀ ⟨translateRight g F, (hmem g).1⟩)
    have hae : (fun x => ⟪h x, (toL2 ω a b Φ₀ ⟨translateRight g F, (hmem g).1⟩ : Carrier a b Φ₀) x⟫_ℂ)
        =ᵐ[domainMeasure a b Φ₀] fun x => conj (h x) * F (x * g) := by
      rw [toL2_apply]
      filter_upwards [MemLp.coeFn_toLp (hmem g).1.2.2] with x hx
      rw [hx, RCLike.inner_apply', translateRight_apply]
    exact (hI.congr hae).const_mul (φ g)

  have hnorm : ∀ g, ∫ x, ‖f g x‖ ∂domainMeasure a b Φ₀ ≤
      ‖φ g‖ * ((∫ x, ‖h x‖ ^ (2 : ℝ) ∂domainMeasure a b Φ₀) ^ (1 / (2 : ℝ)) * ‖toL2 ω a b Φ₀ ⟨F, hF.1⟩‖) := by
    intro g
    have hholder : ∫ x, ‖h x‖ * ‖F (x * g)‖ ∂domainMeasure a b Φ₀ ≤
        (∫ x, ‖h x‖ ^ (2 : ℝ) ∂domainMeasure a b Φ₀) ^ (1 / (2 : ℝ)) *
          (∫ x, ‖F (x * g)‖ ^ (2 : ℝ) ∂domainMeasure a b Φ₀) ^ (1 / (2 : ℝ)) :=
      integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
        (Filter.Eventually.of_forall fun x => norm_nonneg (h x))
        (Filter.Eventually.of_forall fun x => norm_nonneg (F (x * g)))
        (by simpa using (Lp.memLp h).norm) (by simpa [translateRight_apply] using (hmem g).1.2.2.norm)
    have hF2 : (∫ x, ‖F (x * g)‖ ^ (2 : ℝ) ∂domainMeasure a b Φ₀) ^ (1 / (2 : ℝ)) =
        ‖toL2 ω a b Φ₀ ⟨F, hF.1⟩‖ := by
      rw [← hiso g, norm_toL2_eq]
      rfl
    calc ∫ x, ‖f g x‖ ∂domainMeasure a b Φ₀
        = ‖φ g‖ * ∫ x, ‖h x‖ * ‖F (x * g)‖ ∂domainMeasure a b Φ₀ := by
          simp only [hf_def, norm_mul, RCLike.norm_conj]
          rw [integral_const_mul]
      _ ≤ ‖φ g‖ * ((∫ x, ‖h x‖ ^ (2 : ℝ) ∂domainMeasure a b Φ₀) ^ (1 / (2 : ℝ)) *
            (∫ x, ‖F (x * g)‖ ^ (2 : ℝ) ∂domainMeasure a b Φ₀) ^ (1 / (2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hholder (norm_nonneg _)
      _ = _ := by rw [hF2]

  have hf_int : Integrable (Function.uncurry f)
      ((NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).prod (domainMeasure a b Φ₀)) := by
    refine (integrable_prod_iff hf_meas).mpr ⟨Filter.Eventually.of_forall hint_x, ?_⟩
    refine Integrable.mono' (hφi.norm.mul_const
        ((∫ x, ‖h x‖ ^ (2 : ℝ) ∂domainMeasure a b Φ₀) ^ (1 / (2 : ℝ)) * ‖toL2 ω a b Φ₀ ⟨F, hF.1⟩‖))
      hf_meas.norm.integral_prod_right' (Filter.Eventually.of_forall fun g => ?_)
    exact (Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)).le.trans (hnorm g)

  calc ⟪h, toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hRF⟩⟫_ℂ
      = ∫ x, conj (h x) * smoothingOperator φ F x ∂domainMeasure a b Φ₀ := by
        rw [L2.inner_def, toL2_apply]
        refine integral_congr_ae ?_
        filter_upwards [MemLp.coeFn_toLp hRF.2.2] with x hx
        rw [hx, RCLike.inner_apply']
    _ = ∫ x, ∫ g, f g x ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) ∂domainMeasure a b Φ₀ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [hf_def, smoothingOperator_apply]
        rw [← integral_const_mul]
        simp_rw [mul_left_comm (conj (h x))]
    _ = ∫ g, ∫ x, f g x ∂domainMeasure a b Φ₀ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) :=
        (integral_integral_swap hf_int).symm
    _ = ∫ g, φ g * ⟪h, toL2 ω a b Φ₀ ⟨translateRight g F, (hmem g).1⟩⟫_ℂ
          ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        simp only [hf_def]
        rw [integral_const_mul, L2.inner_def, toL2_apply]
        congr 1
        refine integral_congr_ae ?_
        filter_upwards [MemLp.coeFn_toLp (hmem g).1.2.2] with x hx
        rw [hx, RCLike.inner_apply', translateRight_apply]

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

end WeakInterchange
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

end WeakInterchangeBlock
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

section Interfaces

p2m_open "Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory LanglandsTunnell.CubicInduction.SlabL2~exists_isSlabDomain"
open scoped InnerProductSpace

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.AdelicGL CubicInduction.globalPointsGL"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "SlabL2.realCoordinate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 LocalGL3 heckeGen1 heckeGen2 cosetSum IsCosetEigenfunction IsRightInvariant archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 one_le_gauge3 one_le_archGauge3 IsModerateGrowth3 matrixFin_ext matrixAdele_ext localMatN localMatN_apply_self localMatN_apply_of_ne mapMatrix_localMatN_self mapMatrix_localMatN_of_ne localEmbedN finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN finEmbedN localToAdelic3 exists_mul_eq_unipotent_mul_diagonal_mul_compact smoothingOperator_mem_cuspFunctions_of_isCuspidalAlong exists_isCompactOperator_cuspidalSubspace_smoothingOperator exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous exists_inner_toL2_translateRight_ne_zero_of_isCosetEigenfunction measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator"
namespace LocalConstituent
p2m_open "LanglandsTunnell.CubicInduction~isCompact_localMaximalCompact3~det_radicalP21~det_radicalP12 LanglandsTunnell~CubicInduction.isCompact_localMaximalCompact3"

namespace LevelFamilyUnit

private noncomputable def levelKernelAt (α : (Fin 3 → Fin 3 → ℝ) → ℂ)
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ)))
    (v : HeightOneSpectrum (𝓞 ℚ)) (K : Subgroup (LocalGL3 v)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) : ℂ :=
  α (archEntries g) *
    Set.indicator {x : AdelicGL 3 (𝓞 ℚ) ℚ | componentAt3 (𝓞 ℚ) ℚ v x ∈ K ∧
      ∀ p, p ≠ v → componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} (fun _ => (1 : ℂ)) g

private def smoothVectors {Hc : Type} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc]
    (R : AdelicGL 3 (𝓞 ℚ) ℚ →* (Hc →L[ℂ] Hc)) (v : HeightOneSpectrum (𝓞 ℚ)) (V : Submodule ℂ Hc) : Set Hc :=
  {y : Hc | y ∈ V ∧ ∃ K : Subgroup (LocalGL3 v), IsCompact (K : Set (LocalGL3 v)) ∧ IsOpen (K : Set (LocalGL3 v)) ∧
    ∀ k ∈ K, R (localToAdelic3 v k) y = y}

private theorem coe_localToAdelic3 (v : HeightOneSpectrum (𝓞 ℚ)) (k : LocalGL3 v) :
    ((localToAdelic3 v k : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      finMatN (Fin 3) (𝓞 ℚ) ℚ
        (localMatN (Fin 3) (𝓞 ℚ) ℚ v (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) := rfl

private theorem coe_componentAt3 (p : HeightOneSpectrum (𝓞 ℚ)) (u : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ((componentAt3 (𝓞 ℚ) ℚ p u : GL (Fin 3) (p.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) =
      ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)).mapMatrix
        (u : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) := rfl

private theorem mapMatrix_comp_apply' (p : HeightOneSpectrum (𝓞 ℚ))
    (M : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :
    ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)).mapMatrix M =
      (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p).mapMatrix ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix M) := by
  ext i j
  rfl

private theorem _root_.LanglandsTunnell.CubicInduction.LocalConstituent.LevelFamilyUnit.componentAt3_localToAdelic3_self (v : HeightOneSpectrum (𝓞 ℚ)) (k : LocalGL3 v) :
    componentAt3 (𝓞 ℚ) ℚ v (localToAdelic3 v k) = k := by
  apply Units.ext
  rw [coe_componentAt3, coe_localToAdelic3, mapMatrix_comp_apply', mapMatrix_fin_finMatN,
    mapMatrix_localMatN_self]

p2m_export "LanglandsTunnell.CubicInduction.LocalConstituent.LevelFamilyUnit" "componentAt3_localToAdelic3_self"
private theorem _root_.LanglandsTunnell.CubicInduction.LocalConstituent.LevelFamilyUnit.componentAt3_localToAdelic3_of_ne {v p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ≠ v)
    (k : LocalGL3 v) : componentAt3 (𝓞 ℚ) ℚ p (localToAdelic3 v k) = 1 := by
  apply Units.ext
  rw [coe_componentAt3, coe_localToAdelic3, mapMatrix_comp_apply', mapMatrix_fin_finMatN,
    mapMatrix_localMatN_of_ne (Fin 3) (𝓞 ℚ) ℚ v _ hp, Units.val_one]

p2m_export "LanglandsTunnell.CubicInduction.LocalConstituent.LevelFamilyUnit" "componentAt3_localToAdelic3_of_ne"
private theorem componentAt3_mul_localToAdelic3_self (v : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (k : LocalGL3 v) :
    componentAt3 (𝓞 ℚ) ℚ v (g * localToAdelic3 v k) = componentAt3 (𝓞 ℚ) ℚ v g * k := by
  rw [map_mul, componentAt3_localToAdelic3_self]

private theorem componentAt3_mul_localToAdelic3_of_ne {v p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ≠ v)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (k : LocalGL3 v) :
    componentAt3 (𝓞 ℚ) ℚ p (g * localToAdelic3 v k) = componentAt3 (𝓞 ℚ) ℚ p g := by
  rw [map_mul, componentAt3_localToAdelic3_of_ne hp, mul_one]

private theorem componentAt3_localToAdelic3_mul_self (v : HeightOneSpectrum (𝓞 ℚ)) (k : LocalGL3 v)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    componentAt3 (𝓞 ℚ) ℚ v (localToAdelic3 v k * g) = k * componentAt3 (𝓞 ℚ) ℚ v g := by
  rw [map_mul, componentAt3_localToAdelic3_self]

private theorem componentAt3_localToAdelic3_mul_of_ne {v p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ≠ v)
    (k : LocalGL3 v) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    componentAt3 (𝓞 ℚ) ℚ p (localToAdelic3 v k * g) = componentAt3 (𝓞 ℚ) ℚ p g := by
  rw [map_mul, componentAt3_localToAdelic3_of_ne hp, one_mul]

private theorem fst_apply_mul_finMatN (A : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))
    (X : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) (i j : Fin 3) :
    ((A * finMatN (Fin 3) (𝓞 ℚ) ℚ X) i j).1 = (A i j).1 := by
  have h : (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (A * finMatN (Fin 3) (𝓞 ℚ) ℚ X) =
      (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix A := by
    rw [map_mul, mapMatrix_arch_finMatN, mul_one]
  have h' := congrFun (congrFun h i) j
  simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleArch_apply] using h'

private theorem fst_finMatN_mul_apply (X : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))
    (A : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) (i j : Fin 3) :
    ((finMatN (Fin 3) (𝓞 ℚ) ℚ X * A) i j).1 = (A i j).1 := by
  have h : (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (finMatN (Fin 3) (𝓞 ℚ) ℚ X * A) =
      (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix A := by
    rw [map_mul, mapMatrix_arch_finMatN, one_mul]
  have h' := congrFun (congrFun h i) j
  simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleArch_apply] using h'

private theorem archEntries_mul_localToAdelic3 (v : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (k : LocalGL3 v) : archEntries (g * localToAdelic3 v k) = archEntries g := by
  funext i j
  simp only [archEntries, Units.val_mul, coe_localToAdelic3, fst_apply_mul_finMatN]

private theorem archEntries_localToAdelic3_mul (v : HeightOneSpectrum (𝓞 ℚ)) (k : LocalGL3 v)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) : archEntries (localToAdelic3 v k * g) = archEntries g := by
  funext i j
  simp only [archEntries, Units.val_mul, coe_localToAdelic3, fst_finMatN_mul_apply]

private def InLevel (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ)))
    (v : HeightOneSpectrum (𝓞 ℚ)) (K : Subgroup (LocalGL3 v)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) : Prop :=
  componentAt3 (𝓞 ℚ) ℚ v g ∈ K ∧ ∀ p, p ≠ v → componentAt3 (𝓞 ℚ) ℚ p g ∈ K' p

private theorem levelKernelAt_of_inLevel (α : (Fin 3 → Fin 3 → ℝ) → ℂ)
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ)))
    (v : HeightOneSpectrum (𝓞 ℚ)) (K : Subgroup (LocalGL3 v)) {g : AdelicGL 3 (𝓞 ℚ) ℚ} (hg : InLevel K' v K g) :
    levelKernelAt α K' v K g = α (archEntries g) := by
  unfold levelKernelAt
  rw [Set.indicator_of_mem (show g ∈ {x : AdelicGL 3 (𝓞 ℚ) ℚ | componentAt3 (𝓞 ℚ) ℚ v x ∈ K ∧
    ∀ p, p ≠ v → componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} from hg), mul_one]

private theorem levelKernelAt_of_not_inLevel (α : (Fin 3 → Fin 3 → ℝ) → ℂ)
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ)))
    (v : HeightOneSpectrum (𝓞 ℚ)) (K : Subgroup (LocalGL3 v)) {g : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hg : ¬ InLevel K' v K g) : levelKernelAt α K' v K g = 0 := by
  unfold levelKernelAt
  rw [Set.indicator_of_notMem (show g ∉ {x : AdelicGL 3 (𝓞 ℚ) ℚ | componentAt3 (𝓞 ℚ) ℚ v x ∈ K ∧
    ∀ p, p ≠ v → componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} from hg), mul_zero]

private theorem levelKernelAt_congr (α : (Fin 3 → Fin 3 → ℝ) → ℂ)
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ)))
    (v : HeightOneSpectrum (𝓞 ℚ)) {K₁ K₂ : Subgroup (LocalGL3 v)} {g₁ g₂ : AdelicGL 3 (𝓞 ℚ) ℚ}
    (harch : archEntries g₂ = archEntries g₁) (hmem : InLevel K' v K₂ g₂ ↔ InLevel K' v K₁ g₁) :
    levelKernelAt α K' v K₂ g₂ = levelKernelAt α K' v K₁ g₁ := by
  by_cases h : InLevel K' v K₁ g₁
  · rw [levelKernelAt_of_inLevel α K' v K₂ (hmem.mpr h), levelKernelAt_of_inLevel α K' v K₁ h, harch]
  · rw [levelKernelAt_of_not_inLevel α K' v K₂ (fun h' => h (hmem.mp h')),
      levelKernelAt_of_not_inLevel α K' v K₁ h]

private theorem isSmoothingKernel_levelKernelAt {α : (Fin 3 → Fin 3 → ℝ) → ℂ} (hα : IsSmoothArchFactor α)
    {K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))}
    (hK' : ∀ p, IsOpen (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))) ∧
      IsCompact (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))))
    (hK'e : ∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p)
    {v : HeightOneSpectrum (𝓞 ℚ)} {K : Subgroup (LocalGL3 v)} (hKc : IsCompact (K : Set (LocalGL3 v)))
    (hKo : IsOpen (K : Set (LocalGL3 v))) : IsSmoothingKernel (levelKernelAt α K' v K) := by
  classical
  refine ⟨α, Function.update K' v K, hα, ?_, ?_, fun g => ?_⟩
  · intro p
    by_cases hp : p = v
    · subst hp
      rw [Function.update_self]
      exact ⟨hKo, hKc⟩
    · rw [Function.update_of_ne hp]
      exact hK' p
  · refine (hK'e.and (Filter.eventually_cofinite_ne v)).mono ?_
    rintro p ⟨hp, hpv⟩
    rw [Function.update_of_ne hpv]
    exact hp
  · have hset : {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ Function.update K' v K p} =
        {x : AdelicGL 3 (𝓞 ℚ) ℚ | componentAt3 (𝓞 ℚ) ℚ v x ∈ K ∧
          ∀ p, p ≠ v → componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} := by
      ext x
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h
        refine ⟨?_, fun p hp => ?_⟩
        · have hv := h v
          rwa [Function.update_self] at hv
        · have hp' := h p
          rwa [Function.update_of_ne hp] at hp'
      · rintro ⟨h₁, h₂⟩ p
        by_cases hp : p = v
        · subst hp
          rw [Function.update_self]
          exact h₁
        · rw [Function.update_of_ne hp]
          exact h₂ p hp
    rw [hset]
    rfl

private theorem levelKernelAt_eq_re_and_nonneg {α : (Fin 3 → Fin 3 → ℝ) → ℂ}
    (hαr : ∀ m, α m = ((α m).re : ℂ) ∧ 0 ≤ (α m).re)
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ)))
    (v : HeightOneSpectrum (𝓞 ℚ)) (K : Subgroup (LocalGL3 v)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    levelKernelAt α K' v K g = ((levelKernelAt α K' v K g).re : ℂ) ∧ 0 ≤ (levelKernelAt α K' v K g).re := by
  by_cases hg : InLevel K' v K g
  · rw [levelKernelAt_of_inLevel α K' v K hg]
    exact hαr _
  · rw [levelKernelAt_of_not_inLevel α K' v K hg]
    simp

private theorem levelKernelAt_localToAdelic3_mul (α : (Fin 3 → Fin 3 → ℝ) → ℂ)
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ)))
    (v : HeightOneSpectrum (𝓞 ℚ)) (K : Subgroup (LocalGL3 v)) {k : LocalGL3 v} (hk : k ∈ K)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) : levelKernelAt α K' v K (localToAdelic3 v k * g) = levelKernelAt α K' v K g := by
  refine levelKernelAt_congr α K' v (archEntries_localToAdelic3_mul v k g) ?_
  unfold InLevel
  rw [componentAt3_localToAdelic3_mul_self, Subgroup.mul_mem_cancel_left _ hk]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, fun p hp => by simpa only [componentAt3_localToAdelic3_mul_of_ne hp] using h₂ p hp⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, fun p hp => by rw [componentAt3_localToAdelic3_mul_of_ne hp]; exact h₂ p hp⟩

private theorem levelKernelAt_inv_mul_eq_map_conj (α : (Fin 3 → Fin 3 → ℝ) → ℂ)
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ)))
    (v : HeightOneSpectrum (𝓞 ℚ)) (K : Subgroup (LocalGL3 v)) (h : LocalGL3 v) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    levelKernelAt α K' v K ((localToAdelic3 v h)⁻¹ * g) =
      levelKernelAt α K' v (K.map (MulAut.conj h).toMonoidHom) (g * (localToAdelic3 v h)⁻¹) := by
  rw [← map_inv]
  refine levelKernelAt_congr α K' v ?_ ?_
  · rw [archEntries_mul_localToAdelic3, archEntries_localToAdelic3_mul]
  · unfold InLevel
    rw [componentAt3_mul_localToAdelic3_self, componentAt3_localToAdelic3_mul_self, Subgroup.mem_map_equiv,
      MulAut.conj_symm_apply]
    have hconj : h⁻¹ * (componentAt3 (𝓞 ℚ) ℚ v g * h⁻¹) * h = h⁻¹ * componentAt3 (𝓞 ℚ) ℚ v g := by
      rw [mul_assoc, mul_assoc, inv_mul_cancel, mul_one]
    rw [hconj]
    constructor
    · rintro ⟨h₁, h₂⟩
      refine ⟨h₁, fun p hp => ?_⟩
      simpa only [componentAt3_mul_localToAdelic3_of_ne hp, componentAt3_localToAdelic3_mul_of_ne hp] using h₂ p hp
    · rintro ⟨h₁, h₂⟩
      refine ⟨h₁, fun p hp => ?_⟩
      simpa only [componentAt3_mul_localToAdelic3_of_ne hp, componentAt3_localToAdelic3_mul_of_ne hp] using h₂ p hp

private theorem levelKernelAt_map_conj_of_mem (α : (Fin 3 → Fin 3 → ℝ) → ℂ)
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ)))
    (v : HeightOneSpectrum (𝓞 ℚ)) (K : Subgroup (LocalGL3 v)) {k : LocalGL3 v} (hk : k ∈ K) :
    levelKernelAt α K' v (K.map (MulAut.conj k).toMonoidHom) = levelKernelAt α K' v K := by
  funext g
  refine levelKernelAt_congr α K' v rfl ?_
  unfold InLevel
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, Subgroup.mul_mem_cancel_right _ hk,
    Subgroup.mul_mem_cancel_left _ (K.inv_mem hk)]

private theorem isCompact_isOpen_map_conj {v : HeightOneSpectrum (𝓞 ℚ)} {K : Subgroup (LocalGL3 v)}
    (hKc : IsCompact (K : Set (LocalGL3 v))) (hKo : IsOpen (K : Set (LocalGL3 v))) (h : LocalGL3 v) :
    IsCompact ((K.map (MulAut.conj h).toMonoidHom : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) ∧
      IsOpen ((K.map (MulAut.conj h).toMonoidHom : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) := by
  have himage : ((K.map (MulAut.conj h).toMonoidHom : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) =
      (Homeomorph.mulRight h⁻¹) '' ((Homeomorph.mulLeft h) '' (K : Set (LocalGL3 v))) := by
    rw [Subgroup.coe_map, Set.image_image]
    rfl
  rw [himage]
  exact ⟨((hKc.image (Homeomorph.mulLeft h).continuous).image (Homeomorph.mulRight h⁻¹).continuous),
    (Homeomorph.mulRight h⁻¹).isOpen_image.2 ((Homeomorph.mulLeft h).isOpen_image.2 hKo)⟩

private theorem levelKernelAt_eq_sum_of_transversal (α : (Fin 3 → Fin 3 → ℝ) → ℂ)
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ)))
    (v : HeightOneSpectrum (𝓞 ℚ)) {K₀ K : Subgroup (LocalGL3 v)} (hle : K₀ ≤ K) (s : Finset (LocalGL3 v))
    (hs : ∀ t ∈ s, t ∈ K) (huniq : ∀ x ∈ K, ∃! t, t ∈ s ∧ x * t⁻¹ ∈ K₀) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    levelKernelAt α K' v K g = ∑ t ∈ s, levelKernelAt α K' v K₀ (g * (localToAdelic3 v t)⁻¹) := by
  have hlevel : ∀ t : LocalGL3 v, InLevel K' v K₀ (g * (localToAdelic3 v t)⁻¹) ↔
      (componentAt3 (𝓞 ℚ) ℚ v g * t⁻¹ ∈ K₀ ∧ ∀ p, p ≠ v → componentAt3 (𝓞 ℚ) ℚ p g ∈ K' p) := by
    intro t
    unfold InLevel
    rw [← map_inv, componentAt3_mul_localToAdelic3_self]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨h₁, fun p hp => by simpa only [componentAt3_mul_localToAdelic3_of_ne hp] using h₂ p hp⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨h₁, fun p hp => by rw [componentAt3_mul_localToAdelic3_of_ne hp]; exact h₂ p hp⟩
  by_cases hrest : ∀ p, p ≠ v → componentAt3 (𝓞 ℚ) ℚ p g ∈ K' p
  · by_cases hv : componentAt3 (𝓞 ℚ) ℚ v g ∈ K
    · obtain ⟨t₀, ⟨ht₀s, ht₀⟩, ht₀u⟩ := huniq _ hv
      rw [levelKernelAt_of_inLevel α K' v K ⟨hv, hrest⟩, Finset.sum_eq_single t₀]
      · rw [← map_inv, levelKernelAt_of_inLevel α K' v K₀ (by
          rw [map_inv]; exact (hlevel t₀).2 ⟨ht₀, hrest⟩), archEntries_mul_localToAdelic3]
      · intro t hts htne
        refine levelKernelAt_of_not_inLevel α K' v K₀ fun ht => htne ?_
        exact ht₀u t ⟨hts, ((hlevel t).1 ht).1⟩
      · intro ht₀s'
        exact absurd ht₀s ht₀s'
    · rw [levelKernelAt_of_not_inLevel α K' v K fun hg => hv hg.1]
      symm
      refine Finset.sum_eq_zero fun t hts => ?_
      refine levelKernelAt_of_not_inLevel α K' v K₀ fun ht => hv ?_
      have hmem : componentAt3 (𝓞 ℚ) ℚ v g * t⁻¹ ∈ K := hle ((hlevel t).1 ht).1
      simpa using K.mul_mem hmem (hs t hts)
  · rw [levelKernelAt_of_not_inLevel α K' v K fun hg => hrest hg.2]
    symm
    refine Finset.sum_eq_zero fun t _ => ?_
    exact levelKernelAt_of_not_inLevel α K' v K₀ fun ht => hrest ((hlevel t).1 ht).2

section WeakFormTransport

open MeasureTheory
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {A : Type*} [Group A]

private theorem inner_apply_eq_inner_inv_apply (R : A →* (E →L[ℂ] E))
    (hRn : ∀ (g : A) (x : E), ‖R g x‖ = ‖x‖) (g : A) (h y : E) : ⟪h, R g y⟫_ℂ = ⟪R g⁻¹ h, y⟫_ℂ := by
  have hiso : ∀ (a : A) (x z : E), ⟪R a x, R a z⟫_ℂ = ⟪x, z⟫_ℂ := fun a x z =>
    (⟨(R a : E →ₗ[ℂ] E), hRn a⟩ : E →ₗᵢ[ℂ] E).inner_map_map x z
  have hh : R g (R g⁻¹ h) = h := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]
  calc ⟪h, R g y⟫_ℂ = ⟪R g (R g⁻¹ h), R g y⟫_ℂ := by rw [hh]
    _ = ⟪R g⁻¹ h, y⟫_ℂ := hiso g _ y

private theorem apply_mem_of_inner_eq_integral [CompleteSpace E] [MeasurableSpace A] {μ : Measure A}
    (R : A →* (E →L[ℂ] E)) (φ : A → ℂ) (T : E →L[ℂ] E)
    (hTw : ∀ h c : E, ⟪h, T c⟫_ℂ = ∫ g, φ g * ⟪h, R g c⟫_ℂ ∂μ)
    (V : Submodule ℂ E) (hVc : IsClosed (V : Set E)) (hVR : ∀ (g : A) (x : E), x ∈ V → R g x ∈ V)
    {c : E} (hc : c ∈ V) : T c ∈ V := by
  haveI : CompleteSpace V := hVc.completeSpace_coe
  rw [← Submodule.orthogonal_orthogonal (K := V)]
  refine (Submodule.mem_orthogonal _ _).2 fun u hu => ?_
  have h0 : ∀ g : A, ⟪u, R g c⟫_ℂ = 0 := fun g => Submodule.inner_left_of_mem_orthogonal (hVR g c hc) hu
  rw [hTw]
  simp only [h0, mul_zero, integral_zero]

private theorem apply_apply_eq_of_forall_inv_mul_eq [MeasurableSpace A] [MeasurableMul A] {μ : Measure A}
    [μ.IsMulLeftInvariant] (R : A →* (E →L[ℂ] E)) (hRn : ∀ (g : A) (x : E), ‖R g x‖ = ‖x‖) (φ : A → ℂ)
    (T : E →L[ℂ] E) (hTw : ∀ h c : E, ⟪h, T c⟫_ℂ = ∫ g, φ g * ⟪h, R g c⟫_ℂ ∂μ) {a : A}
    (hφ : ∀ u, φ (a⁻¹ * u) = φ u) (c : E) : R a (T c) = T c := by
  refine ext_inner_left ℂ fun h => ?_
  rw [inner_apply_eq_inner_inv_apply R hRn, hTw, hTw]
  have hL : (fun g => φ g * ⟪R a⁻¹ h, R g c⟫_ℂ) = fun g => φ (a⁻¹ * (a * g)) * ⟪h, R (a * g) c⟫_ℂ := by
    funext g
    rw [inv_mul_cancel_left, map_mul, ContinuousLinearMap.mul_apply, inner_apply_eq_inner_inv_apply R hRn a h (R g c)]
  rw [hL, integral_mul_left_eq_self (fun u => φ (a⁻¹ * u) * ⟪h, R u c⟫_ℂ) a]
  simp only [hφ]

private theorem apply_apply_eq_apply_apply_of_forall_inv_mul_eq_mul_inv [MeasurableSpace A] [MeasurableMul A]
    {μ : Measure A} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (R : A →* (E →L[ℂ] E))
    (hRn : ∀ (g : A) (x : E), ‖R g x‖ = ‖x‖) (φ₁ φ₂ : A → ℂ) (T₁ T₂ : E →L[ℂ] E)
    (h₁ : ∀ h c : E, ⟪h, T₁ c⟫_ℂ = ∫ g, φ₁ g * ⟪h, R g c⟫_ℂ ∂μ)
    (h₂ : ∀ h c : E, ⟪h, T₂ c⟫_ℂ = ∫ g, φ₂ g * ⟪h, R g c⟫_ℂ ∂μ) {a : A}
    (hφ : ∀ u, φ₁ (a⁻¹ * u) = φ₂ (u * a⁻¹)) (c : E) : R a (T₁ c) = T₂ (R a c) := by
  refine ext_inner_left ℂ fun h => ?_
  rw [inner_apply_eq_inner_inv_apply R hRn, h₁, h₂]
  have hL : (fun g => φ₁ g * ⟪R a⁻¹ h, R g c⟫_ℂ) = fun g => φ₁ (a⁻¹ * (a * g)) * ⟪h, R (a * g) c⟫_ℂ := by
    funext g
    rw [inv_mul_cancel_left, map_mul, ContinuousLinearMap.mul_apply, inner_apply_eq_inner_inv_apply R hRn a h (R g c)]
  have hR : (fun w => φ₂ w * ⟪h, R w (R a c)⟫_ℂ) = fun w => φ₁ (a⁻¹ * (w * a)) * ⟪h, R (w * a) c⟫_ℂ := by
    funext w
    rw [hφ, mul_inv_cancel_right, map_mul, ContinuousLinearMap.mul_apply]
  rw [hL, integral_mul_left_eq_self (fun u => φ₁ (a⁻¹ * u) * ⟪h, R u c⟫_ℂ) a, hR,
    integral_mul_right_eq_self (fun u => φ₁ (a⁻¹ * u) * ⟪h, R u c⟫_ℂ) a]

private theorem integral_eq_integral_of_forall_inv_mul_eq_mul_inv [MeasurableSpace A] [MeasurableMul A]
    {μ : Measure A} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (φ₁ φ₂ : A → ℂ) {a : A}
    (hφ : ∀ u, φ₁ (a⁻¹ * u) = φ₂ (u * a⁻¹)) : ∫ u, φ₂ u ∂μ = ∫ u, φ₁ u ∂μ := by
  calc ∫ u, φ₂ u ∂μ = ∫ u, φ₂ (u * a⁻¹) ∂μ := (integral_mul_right_eq_self φ₂ a⁻¹).symm
    _ = ∫ u, φ₁ (a⁻¹ * u) ∂μ := by simp only [hφ]
    _ = ∫ u, φ₁ u ∂μ := integral_mul_left_eq_self φ₁ a⁻¹

end WeakFormTransport
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

section LocalTransport

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

private theorem smoothing_apply_mem {Hc : Type} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
    (R : AdelicGL 3 (𝓞 ℚ) ℚ →* (Hc →L[ℂ] Hc)) (T : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (Hc →L[ℂ] Hc))
    (hTw : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → ∀ h c : Hc,
      ⟪h, T φ c⟫_ℂ = ∫ g, φ g * ⟪h, R g c⟫_ℂ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (V : Submodule ℂ Hc) (hVc : IsClosed (V : Set Hc)) (hVR : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (x : Hc), x ∈ V → R g x ∈ V)
    {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hφ : IsSmoothingKernel φ) {x : Hc} (hx : x ∈ V) : T φ x ∈ V :=
  apply_mem_of_inner_eq_integral R φ (T φ) (hTw φ hφ) V hVc hVR hx

private theorem localToAdelic3_smoothing_levelKernelAt {Hc : Type} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc]
    (R : AdelicGL 3 (𝓞 ℚ) ℚ →* (Hc →L[ℂ] Hc)) (hRn : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (x : Hc), ‖R g x‖ = ‖x‖)
    (T : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (Hc →L[ℂ] Hc))
    (hTw : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → ∀ h c : Hc,
      ⟪h, T φ c⟫_ℂ = ∫ g, φ g * ⟪h, R g c⟫_ℂ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (v : HeightOneSpectrum (𝓞 ℚ)) {α : (Fin 3 → Fin 3 → ℝ) → ℂ} (hα : IsSmoothArchFactor α)
    {K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))}
    (hK' : ∀ p, IsOpen (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))) ∧
      IsCompact (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))))
    (hK'e : ∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p)
    {K : Subgroup (LocalGL3 v)} (hKc : IsCompact (K : Set (LocalGL3 v))) (hKo : IsOpen (K : Set (LocalGL3 v)))
    {k : LocalGL3 v} (hk : k ∈ K) (x : Hc) :
    R (localToAdelic3 v k) (T (levelKernelAt α K' v K) x) = T (levelKernelAt α K' v K) x := by
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  refine apply_apply_eq_of_forall_inv_mul_eq R hRn (levelKernelAt α K' v K) (T (levelKernelAt α K' v K))
    (hTw _ (isSmoothingKernel_levelKernelAt hα hK' hK'e hKc hKo)) (a := localToAdelic3 v k) (fun u => ?_) x
  rw [← map_inv, levelKernelAt_localToAdelic3_mul α K' v K (K.inv_mem hk) u]

private theorem localToAdelic3_smoothing_levelKernelAt_eq_map_conj {Hc : Type} [NormedAddCommGroup Hc]
    [InnerProductSpace ℂ Hc] (R : AdelicGL 3 (𝓞 ℚ) ℚ →* (Hc →L[ℂ] Hc))
    (hRn : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (x : Hc), ‖R g x‖ = ‖x‖) (T : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (Hc →L[ℂ] Hc))
    (hTw : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → ∀ h c : Hc,
      ⟪h, T φ c⟫_ℂ = ∫ g, φ g * ⟪h, R g c⟫_ℂ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (v : HeightOneSpectrum (𝓞 ℚ)) {α : (Fin 3 → Fin 3 → ℝ) → ℂ} (hα : IsSmoothArchFactor α)
    {K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))}
    (hK' : ∀ p, IsOpen (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))) ∧
      IsCompact (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))))
    (hK'e : ∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p)
    {K : Subgroup (LocalGL3 v)} (hKc : IsCompact (K : Set (LocalGL3 v))) (hKo : IsOpen (K : Set (LocalGL3 v)))
    (h : LocalGL3 v) (x : Hc) :
    R (localToAdelic3 v h) (T (levelKernelAt α K' v K) x) =
      T (levelKernelAt α K' v (K.map (MulAut.conj h).toMonoidHom)) (R (localToAdelic3 v h) x) := by
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar_finThree_rat
  obtain ⟨hKc', hKo'⟩ := isCompact_isOpen_map_conj hKc hKo h
  exact apply_apply_eq_apply_apply_of_forall_inv_mul_eq_mul_inv R hRn _ _ _ _
    (hTw _ (isSmoothingKernel_levelKernelAt hα hK' hK'e hKc hKo))
    (hTw _ (isSmoothingKernel_levelKernelAt hα hK' hK'e hKc' hKo'))
    (levelKernelAt_inv_mul_eq_map_conj α K' v K h) x

private theorem integral_levelKernelAt_map_conj (α : (Fin 3 → Fin 3 → ℝ) → ℂ)
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ)))
    (v : HeightOneSpectrum (𝓞 ℚ)) (K : Subgroup (LocalGL3 v)) (h : LocalGL3 v) :
    ∫ g, levelKernelAt α K' v (K.map (MulAut.conj h).toMonoidHom) g
        ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) =
      ∫ g, levelKernelAt α K' v K g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar_finThree_rat
  exact integral_eq_integral_of_forall_inv_mul_eq_mul_inv _ _ (levelKernelAt_inv_mul_eq_map_conj α K' v K h)

end LocalTransport
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

section WeakFormAverages

open MeasureTheory
open scoped InnerProductSpace

private theorem opNorm_le_integral_norm_of_inner_eq_integral
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {G : Type*} [MeasurableSpace G] {ν : Measure G}
    (T : E →L[ℂ] E) (r : G → E → E) (φ : G → ℂ)
    (hr : ∀ (g : G) (x : E), ‖r g x‖ ≤ ‖x‖) (hφ : Integrable φ ν)
    (hTw : ∀ x y : E, ⟪y, T x⟫_ℂ = ∫ g, φ g * ⟪y, r g x⟫_ℂ ∂ν) :
    ‖T‖ ≤ ∫ g, ‖φ g‖ ∂ν := by
  have hM : 0 ≤ ∫ g, ‖φ g‖ ∂ν := integral_nonneg fun _ => norm_nonneg _
  refine ContinuousLinearMap.opNorm_le_bound _ hM fun x => ?_

  have hsq : ‖T x‖ * ‖T x‖ ≤ (∫ g, ‖φ g‖ ∂ν) * (‖T x‖ * ‖x‖) := by
    have h1 : ‖T x‖ * ‖T x‖ ≤ ‖⟪T x, T x⟫_ℂ‖ := by
      rw [← inner_self_eq_norm_mul_norm (𝕜 := ℂ) (T x)]
      exact RCLike.re_le_norm _
    refine h1.trans ?_
    rw [hTw x (T x), ← integral_mul_const]
    refine norm_integral_le_of_norm_le (hφ.norm.mul_const _) (Filter.Eventually.of_forall fun g => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hr g x) (norm_nonneg _))) (norm_nonneg _)
  rcases (norm_nonneg (T x)).eq_or_lt with h0 | hpos
  · rw [← h0]; exact mul_nonneg hM (norm_nonneg _)
  · exact le_of_mul_le_mul_left (hsq.trans_eq (mul_left_comm _ _ _)) hpos

private theorem norm_inv_integral_smul_le_one
    {F : Type*} [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    {G : Type*} [MeasurableSpace G] {ν : Measure G}
    (S : F) (φ : G → ℂ) (hφr : ∀ g : G, φ g = ((φ g).re : ℂ) ∧ 0 ≤ (φ g).re) (hφ : Integrable φ ν)
    (hS : ‖S‖ ≤ ∫ g, ‖φ g‖ ∂ν) :
    ‖(∫ g, φ g ∂ν)⁻¹ • S‖ ≤ 1 := by

  have hnorm : ∀ g : G, ‖φ g‖ = (φ g).re := fun g => by
    rw [(hφr g).1, Complex.norm_real, Real.norm_of_nonneg (hφr g).2, Complex.ofReal_re]
  have hre : (∫ g, φ g ∂ν).re = ∫ g, ‖φ g‖ ∂ν := by
    rw [show (∫ g, φ g ∂ν).re = RCLike.re (∫ g, φ g ∂ν) from rfl, ← integral_re hφ]
    exact integral_congr_ae (Filter.Eventually.of_forall fun g => (hnorm g).symm)
  have him : (∫ g, φ g ∂ν).im = 0 := by
    rw [show (∫ g, φ g ∂ν).im = RCLike.im (∫ g, φ g ∂ν) from rfl, ← integral_im hφ]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun g => ?_)
    show RCLike.im (φ g) = 0
    rw [RCLike.im_to_complex, (hφr g).1]
    exact Complex.ofReal_im _
  have hint : ∫ g, φ g ∂ν = ((∫ g, ‖φ g‖ ∂ν : ℝ) : ℂ) := by
    rw [← hre]; exact Complex.ext (by simp) (by simp [him])
  have hM : 0 ≤ ∫ g, ‖φ g‖ ∂ν := integral_nonneg fun _ => norm_nonneg _
  rw [hint, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hM]
  rcases hM.eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · rw [inv_mul_le_iff₀ hpos, mul_one]; exact hS

private theorem Subgroup.exists_finset_forall_existsUnique_mul_inv_mem
    {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    {K K₀ : Subgroup L} (hle : K₀ ≤ K) (hK : IsCompact (K : Set L)) (hK₀ : IsOpen (K₀ : Set L)) :
    ∃ S : Finset L, (∀ s ∈ S, s ∈ K) ∧ ∀ k ∈ K, ∃! s, s ∈ S ∧ k * s⁻¹ ∈ K₀ := by
  classical
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let H : Subgroup K := K₀.subgroupOf K
  have hH : IsOpen (H : Set K) := hK₀.preimage continuous_subtype_val
  haveI : Finite (K ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨T, hT, -⟩ := H.exists_isComplement_right 1
  have hTf : T.Finite := hT.finite_right
  have huniq := Subgroup.isComplement_iff_existsUnique_mul_inv_mem.mp hT
  have _ := hle
  refine ⟨(hTf.image fun t : K => (t : L)).toFinset, ?_, ?_⟩
  · intro s hs
    rw [Set.Finite.mem_toFinset] at hs
    obtain ⟨t, -, rfl⟩ := hs
    exact t.2
  · intro k hk
    obtain ⟨t, ht, htu⟩ := huniq ⟨k, hk⟩
    refine ⟨((t : K) : L), ⟨?_, ?_⟩, ?_⟩
    · rw [Set.Finite.mem_toFinset]
      exact ⟨(t : K), t.2, rfl⟩
    · have ht' : (⟨k, hk⟩ : K) * ((t : K))⁻¹ ∈ H := ht
      rw [Subgroup.mem_subgroupOf] at ht'
      simpa using ht'
    · rintro s ⟨hs, hs'⟩
      rw [Set.Finite.mem_toFinset] at hs
      obtain ⟨t', ht'T, rfl⟩ := hs
      have hmem : (⟨k, hk⟩ : K) * ((⟨t', ht'T⟩ : T) : K)⁻¹ ∈ (H : Set K) := by
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
        simpa using hs'
      rw [← htu ⟨t', ht'T⟩ hmem]

private theorem integral_finset_sum_comp_mul_inv
    {A : Type*} [Group A] [MeasurableSpace A] [MeasurableMul A] {μ : Measure A} [μ.IsMulRightInvariant]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type*} (S : Finset ι) (a : ι → A) (f : A → F) (hf : Integrable f μ) :
    ∫ g, ∑ s ∈ S, f (g * (a s)⁻¹) ∂μ = S.card • ∫ g, f g ∂μ := by
  rw [integral_finsetSum _ fun s _ => hf.comp_mul_right (a s)⁻¹]
  simp_rw [integral_mul_right_eq_self f]
  rw [Finset.sum_const]

private theorem eq_card_smul_of_inner_eq_integral_sum
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {A : Type*} [Group A] [MeasurableSpace A] [MeasurableMul A] {μ : Measure A} [μ.IsMulRightInvariant]
    (R : A →* (E →L[ℂ] E)) (hRn : ∀ (g : A) (x : E), ‖R g x‖ ≤ ‖x‖)
    (hRm : ∀ h x : E, AEStronglyMeasurable (fun g => ⟪h, R g x⟫_ℂ) μ)
    {ι : Type*} (S : Finset ι) (a : ι → A) (φ₀ φ₁ : A → ℂ) (hφ₀ : Integrable φ₀ μ)
    (hsum : ∀ g, φ₁ g = ∑ s ∈ S, φ₀ (g * (a s)⁻¹))
    (T₀ T₁ : E →L[ℂ] E) (x : E) (hx : ∀ s ∈ S, R (a s) x = x)
    (h₀ : ∀ h : E, ⟪h, T₀ x⟫_ℂ = ∫ g, φ₀ g * ⟪h, R g x⟫_ℂ ∂μ)
    (h₁ : ∀ h : E, ⟪h, T₁ x⟫_ℂ = ∫ g, φ₁ g * ⟪h, R g x⟫_ℂ ∂μ) :
    T₁ x = (S.card : ℂ) • T₀ x := by
  refine ext_inner_left ℂ fun h => ?_
  have hbdd : ∀ g, ‖⟪h, R g x⟫_ℂ‖ ≤ ‖h‖ * ‖x‖ := fun g =>
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hRn g x) (norm_nonneg _))
  have hint : ∀ s, Integrable (fun g => φ₀ (g * (a s)⁻¹) * ⟪h, R g x⟫_ℂ) μ := fun s =>
    (hφ₀.comp_mul_right (a s)⁻¹).mul_bdd (hRm h x) (Filter.Eventually.of_forall hbdd)
  have hterm : ∀ s ∈ S,
      ∫ g, φ₀ (g * (a s)⁻¹) * ⟪h, R g x⟫_ℂ ∂μ = ∫ g, φ₀ g * ⟪h, R g x⟫_ℂ ∂μ := by
    intro s hs
    rw [← integral_mul_right_eq_self (fun g => φ₀ (g * (a s)⁻¹) * ⟪h, R g x⟫_ℂ) (a s)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [mul_inv_cancel_right, map_mul, ContinuousLinearMap.mul_apply, hx s hs]
  rw [h₁ h, inner_smul_right, h₀ h]
  simp_rw [hsum, Finset.sum_mul]
  rw [integral_finsetSum _ fun s _ => hint s, Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]

private theorem inv_smul_eq_inv_smul_of_eq_mul_of_eq_smul
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    {m₀ m₁ : ℂ} {n : ℕ} (hn : n ≠ 0) (hm : m₁ = n * m₀) {y₀ y₁ : E} (hy : y₁ = (n : ℂ) • y₀) :
    m₁⁻¹ • y₁ = m₀⁻¹ • y₀ := by
  subst hm hy
  rw [smul_smul, mul_inv, mul_right_comm, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn : (n : ℂ) ≠ 0), one_mul]

end WeakFormAverages
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

noncomputable section

namespace DirectedSubmoduleFamily

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable (V : ι → Submodule ℂ E) (T : ι → E →L[ℂ] E)

private def index [Nonempty ι] (hdir : Directed (· ≤ ·) V) (x : ↥(iSup V)) : ι :=
  ((Submodule.mem_iSup_of_directed V hdir).1 x.2).choose

private theorem mem_index [Nonempty ι] (hdir : Directed (· ≤ ·) V) (x : ↥(iSup V)) :
    (x : E) ∈ V (index V hdir x) :=
  ((Submodule.mem_iSup_of_directed V hdir).1 x.2).choose_spec

private def glue [Nonempty ι] (hdir : Directed (· ≤ ·) V)
    (hcons : ∀ i j, ∀ x ∈ V i, x ∈ V j → T i x = T j x) : ↥(iSup V) →ₗ[ℂ] E where
  toFun x := T (index V hdir x) x
  map_add' x y := by
    obtain ⟨k, hxk, hyk⟩ := hdir (index V hdir x) (index V hdir y)
    have hx : (x : E) ∈ V k := hxk (mem_index V hdir x)
    have hy : (y : E) ∈ V k := hyk (mem_index V hdir y)
    have hxy : ((x + y : ↥(iSup V)) : E) ∈ V k := by
      rw [Submodule.coe_add]
      exact (V k).add_mem hx hy
    show T _ ((x + y : ↥(iSup V)) : E) = T _ (x : E) + T _ (y : E)
    rw [hcons _ _ _ (mem_index V hdir (x + y)) hxy, hcons _ _ _ (mem_index V hdir x) hx,
      hcons _ _ _ (mem_index V hdir y) hy, Submodule.coe_add, map_add]
  map_smul' c x := by
    have hcx : ((c • x : ↥(iSup V)) : E) ∈ V (index V hdir x) := by
      rw [Submodule.coe_smul]
      exact (V _).smul_mem c (mem_index V hdir x)
    show T _ ((c • x : ↥(iSup V)) : E) = c • T _ (x : E)
    rw [hcons _ _ _ (mem_index V hdir (c • x)) hcx, Submodule.coe_smul, map_smul]

private theorem glue_apply_of_mem [Nonempty ι] (hdir : Directed (· ≤ ·) V)
    (hcons : ∀ i j, ∀ x ∈ V i, x ∈ V j → T i x = T j x) {i : ι} (x : ↥(iSup V)) (hx : (x : E) ∈ V i) :
    glue V T hdir hcons x = T i x :=
  hcons _ _ _ (mem_index V hdir x) hx

private theorem denseRange_inclusion_topologicalClosure :
    DenseRange (Submodule.inclusion (iSup V).le_topologicalClosure) := by
  refine Subtype.dense_iff.2 fun y hy => ?_
  refine closure_mono ?_ ((Submodule.topologicalClosure_coe (iSup V)).subset hy)
  rintro z hz
  exact ⟨Submodule.inclusion (iSup V).le_topologicalClosure ⟨z, hz⟩, Set.mem_range_self _, rfl⟩

private theorem exists_opNorm_le_and_forall_mem_eq_and_mem_closure [CompleteSpace E] [Nonempty ι]
    (hdir : Directed (· ≤ ·) V) (hcons : ∀ i j, ∀ x ∈ V i, x ∈ V j → T i x = T j x) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ i, ∀ x ∈ V i, ‖T i x‖ ≤ C * ‖x‖)
    (hmem : ∀ i, ∀ x ∈ V i, T i x ∈ closure (⋃ j, (V j : Set E))) :
    ∃ A : E →L[ℂ] E, ‖A‖ ≤ C ∧ (∀ i, ∀ x ∈ V i, A x = T i x) ∧
      ∀ x : E, A x ∈ closure (⋃ j, (V j : Set E)) := by
  set H : Submodule ℂ E := (iSup V).topologicalClosure with hH
  set e : ↥(iSup V) →ₗ[ℂ] H := Submodule.inclusion (iSup V).le_topologicalClosure with he
  have hdr : DenseRange e := denseRange_inclusion_topologicalClosure V
  have hnorm : ∀ x : ↥(iSup V), ‖glue V T hdir hcons x‖ ≤ C * ‖e x‖ := fun x =>
    hbound _ x (mem_index V hdir x)
  set S : H →L[ℂ] E := (glue V T hdir hcons).extendOfNorm e with hSdef
  have hSe : ∀ x : ↥(iSup V), S (e x) = glue V T hdir hcons x := fun x =>
    LinearMap.extendOfNorm_eq hdr ⟨C, hnorm⟩ x
  have hSH : ∀ y : H, S y ∈ closure (⋃ j, (V j : Set E)) := by
    intro y
    refine hdr.induction_on y (isClosed_closure.preimage S.continuous) fun x => ?_
    rw [hSe x, glue_apply_of_mem V T hdir hcons x (mem_index V hdir x)]
    exact hmem _ x (mem_index V hdir x)
  refine ⟨S.comp H.orthogonalProjection, ?_, fun i x hx => ?_, fun x => hSH _⟩
  · calc ‖S.comp H.orthogonalProjection‖ ≤ ‖S‖ * ‖H.orthogonalProjection‖ :=
          ContinuousLinearMap.opNorm_comp_le S H.orthogonalProjection
      _ ≤ C * 1 := mul_le_mul (LinearMap.opNorm_extendOfNorm_le hdr hC hnorm)
          H.orthogonalProjection_norm_le (ContinuousLinearMap.opNorm_nonneg _) hC
      _ = C := mul_one C
  · have hxS : x ∈ iSup V := Submodule.mem_iSup_of_mem i hx
    have hxH : x ∈ H := (iSup V).le_topologicalClosure hxS
    have h1 : H.orthogonalProjection x = e ⟨x, hxS⟩ :=
      H.orthogonalProjection_mem_subspace_eq_self (⟨x, hxH⟩ : H)
    rw [ContinuousLinearMap.comp_apply, h1, hSe, glue_apply_of_mem V T hdir hcons ⟨x, hxS⟩ hx]

private theorem apply_comm_of_mem_closure {A : E →L[ℂ] E} {ρ : E → E} (hρc : Continuous ρ) (σ : ι → ι)
    (hA : ∀ i, ∀ x ∈ V i, A x = T i x) (hρ : ∀ i, ∀ x ∈ V i, ρ x ∈ V (σ i))
    (hcomm : ∀ i, ∀ x ∈ V i, ρ (T i x) = T (σ i) (ρ x)) {x : E} (hx : x ∈ closure (⋃ j, (V j : Set E))) :
    A (ρ x) = ρ (A x) := by
  have h : Set.EqOn (fun y : E => A (ρ y)) (fun y : E => ρ (A y)) (⋃ j, (V j : Set E)) := by
    intro y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
    show A (ρ y) = ρ (A y)
    rw [hA (σ i) (ρ y) (hρ i y hi), ← hcomm i y hi, hA i y hi]
  exact h.closure (A.continuous.comp hρc) (hρc.comp A.continuous) hx

end DirectedSubmoduleFamily
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

section LevelConsistency

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

private theorem exists_smoothing_apply_eq_smul_and_integral_eq_mul_of_le
    {Hc : Type} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc]
    (R : AdelicGL 3 (𝓞 ℚ) ℚ →* (Hc →L[ℂ] Hc)) (hRn : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (x : Hc), ‖R g x‖ = ‖x‖)
    (hRc : ∀ x : Hc, Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => R g x)
    (T : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (Hc →L[ℂ] Hc))
    (hTw : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → ∀ h c : Hc,
      ⟪h, T φ c⟫_ℂ = ∫ g, φ g * ⟪h, R g c⟫_ℂ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (hφi : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ →
      Continuous φ ∧ HasCompactSupport φ ∧ Integrable φ (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (v : HeightOneSpectrum (𝓞 ℚ))
    {α : (Fin 3 → Fin 3 → ℝ) → ℂ} (hα : IsSmoothArchFactor α)
    {K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))}
    (hK' : ∀ p, IsOpen (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))) ∧
      IsCompact (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))))
    (hK'e : ∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p)
    {K₀ K : Subgroup (LocalGL3 v)} (hle : K₀ ≤ K)
    (hK₀c : IsCompact (K₀ : Set (LocalGL3 v))) (hK₀o : IsOpen (K₀ : Set (LocalGL3 v)))
    (hKc : IsCompact (K : Set (LocalGL3 v))) (hKo : IsOpen (K : Set (LocalGL3 v)))
    (x : Hc) (hx : ∀ k ∈ K, R (localToAdelic3 v k) x = x) :
    ∃ n : ℕ, n ≠ 0 ∧
      T (levelKernelAt α K' v K) x = (n : ℂ) • T (levelKernelAt α K' v K₀) x ∧
      ∫ g, levelKernelAt α K' v K g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) =
        n * ∫ g, levelKernelAt α K' v K₀ g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar_finThree_rat
  obtain ⟨S, hS, huniq⟩ := Subgroup.exists_finset_forall_existsUnique_mul_inv_mem hle hKc hK₀o
  have hsum := levelKernelAt_eq_sum_of_transversal α K' v hle S hS huniq
  have hk₀ := isSmoothingKernel_levelKernelAt hα hK' hK'e hK₀c hK₀o
  have hk := isSmoothingKernel_levelKernelAt hα hK' hK'e hKc hKo
  have hne : S.card ≠ 0 := by
    obtain ⟨t, ⟨ht, -⟩, -⟩ := huniq 1 K.one_mem
    exact (Finset.card_pos.mpr ⟨t, ht⟩).ne'
  refine ⟨S.card, hne, ?_, ?_⟩
  · refine eq_card_smul_of_inner_eq_integral_sum R (fun g y => (hRn g y).le)
      (fun h y => (continuous_const.inner (hRc y)).aestronglyMeasurable) S (localToAdelic3 v)
      (levelKernelAt α K' v K₀) (levelKernelAt α K' v K) (hφi _ hk₀).2.2 hsum
      (T (levelKernelAt α K' v K₀)) (T (levelKernelAt α K' v K)) x (fun t ht => hx t (hS t ht))
      (fun h => hTw _ hk₀ h x) (fun h => hTw _ hk h x)
  · rw [← nsmul_eq_mul, ← integral_finset_sum_comp_mul_inv S (localToAdelic3 v)
      (levelKernelAt α K' v K₀) (hφi _ hk₀).2.2]
    exact integral_congr_ae (Filter.Eventually.of_forall hsum)

private theorem inv_integral_smul_smoothing_apply_eq_of_le
    {Hc : Type} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc]
    (R : AdelicGL 3 (𝓞 ℚ) ℚ →* (Hc →L[ℂ] Hc)) (hRn : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (x : Hc), ‖R g x‖ = ‖x‖)
    (hRc : ∀ x : Hc, Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => R g x)
    (T : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (Hc →L[ℂ] Hc))
    (hTw : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → ∀ h c : Hc,
      ⟪h, T φ c⟫_ℂ = ∫ g, φ g * ⟪h, R g c⟫_ℂ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (hφi : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ →
      Continuous φ ∧ HasCompactSupport φ ∧ Integrable φ (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (v : HeightOneSpectrum (𝓞 ℚ))
    {α : (Fin 3 → Fin 3 → ℝ) → ℂ} (hα : IsSmoothArchFactor α)
    {K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))}
    (hK' : ∀ p, IsOpen (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))) ∧
      IsCompact (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))))
    (hK'e : ∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p)
    {K₀ K : Subgroup (LocalGL3 v)} (hle : K₀ ≤ K)
    (hK₀c : IsCompact (K₀ : Set (LocalGL3 v))) (hK₀o : IsOpen (K₀ : Set (LocalGL3 v)))
    (hKc : IsCompact (K : Set (LocalGL3 v))) (hKo : IsOpen (K : Set (LocalGL3 v)))
    (x : Hc) (hx : ∀ k ∈ K, R (localToAdelic3 v k) x = x) :
    (∫ g, levelKernelAt α K' v K g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))⁻¹ •
        T (levelKernelAt α K' v K) x =
      (∫ g, levelKernelAt α K' v K₀ g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))⁻¹ •
        T (levelKernelAt α K' v K₀) x := by
  obtain ⟨n, hn, hT, hm⟩ := exists_smoothing_apply_eq_smul_and_integral_eq_mul_of_le R hRn hRc T hTw hφi v hα
    hK' hK'e hle hK₀c hK₀o hKc hKo x hx
  exact inv_smul_eq_inv_smul_of_eq_mul_of_eq_smul hn hm hT

private theorem inv_integral_smul_smoothing_apply_eq
    {Hc : Type} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc]
    (R : AdelicGL 3 (𝓞 ℚ) ℚ →* (Hc →L[ℂ] Hc)) (hRn : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (x : Hc), ‖R g x‖ = ‖x‖)
    (hRc : ∀ x : Hc, Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => R g x)
    (T : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (Hc →L[ℂ] Hc))
    (hTw : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → ∀ h c : Hc,
      ⟪h, T φ c⟫_ℂ = ∫ g, φ g * ⟪h, R g c⟫_ℂ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (hφi : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ →
      Continuous φ ∧ HasCompactSupport φ ∧ Integrable φ (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (v : HeightOneSpectrum (𝓞 ℚ))
    {α : (Fin 3 → Fin 3 → ℝ) → ℂ} (hα : IsSmoothArchFactor α)
    {K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))}
    (hK' : ∀ p, IsOpen (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))) ∧
      IsCompact (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))))
    (hK'e : ∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p)
    {K K₀ : Subgroup (LocalGL3 v)}
    (hKc : IsCompact (K : Set (LocalGL3 v))) (hKo : IsOpen (K : Set (LocalGL3 v)))
    (hK₀c : IsCompact (K₀ : Set (LocalGL3 v))) (hK₀o : IsOpen (K₀ : Set (LocalGL3 v)))
    (x : Hc) (hx : ∀ k ∈ K, R (localToAdelic3 v k) x = x) (hx₀ : ∀ k ∈ K₀, R (localToAdelic3 v k) x = x) :
    (∫ g, levelKernelAt α K' v K g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))⁻¹ •
        T (levelKernelAt α K' v K) x =
      (∫ g, levelKernelAt α K' v K₀ g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))⁻¹ •
        T (levelKernelAt α K' v K₀) x := by
  have hIc : IsCompact ((K ⊓ K₀ : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) := by
    rw [Subgroup.coe_inf]
    exact hKc.inter_right (Subgroup.isClosed_of_isOpen K₀ hK₀o)
  have hIo : IsOpen ((K ⊓ K₀ : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) := by
    rw [Subgroup.coe_inf]
    exact hKo.inter hK₀o
  exact (inv_integral_smul_smoothing_apply_eq_of_le R hRn hRc T hTw hφi v hα hK' hK'e inf_le_left hIc hIo hKc hKo
      x hx).trans
    (inv_integral_smul_smoothing_apply_eq_of_le R hRn hRc T hTw hφi v hα hK' hK'e inf_le_right hIc hIo hK₀c hK₀o
      x hx₀).symm

end LevelConsistency
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

private abbrev CompactOpenLevel (v : HeightOneSpectrum (𝓞 ℚ)) : Type :=
  {K : Subgroup (LocalGL3 v) // IsCompact (K : Set (LocalGL3 v)) ∧ IsOpen (K : Set (LocalGL3 v))}

private noncomputable def conjLevel {v : HeightOneSpectrum (𝓞 ℚ)} (h : LocalGL3 v) (i : CompactOpenLevel v) :
    CompactOpenLevel v :=
  ⟨i.1.map (MulAut.conj h).toMonoidHom, isCompact_isOpen_map_conj i.2.1 i.2.2 h⟩

private noncomputable def infLevel {v : HeightOneSpectrum (𝓞 ℚ)} (i j : CompactOpenLevel v) : CompactOpenLevel v :=
  ⟨i.1 ⊓ j.1, by
    constructor
    · rw [Subgroup.coe_inf]
      exact i.2.1.inter_right (Subgroup.isClosed_of_isOpen j.1 j.2.2)
    · rw [Subgroup.coe_inf]
      exact i.2.2.inter j.2.2⟩

private def fixedIn {Hc : Type} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc]
    (R : AdelicGL 3 (𝓞 ℚ) ℚ →* (Hc →L[ℂ] Hc)) (v : HeightOneSpectrum (𝓞 ℚ)) (V : Submodule ℂ Hc)
    (K : Subgroup (LocalGL3 v)) : Submodule ℂ Hc where
  carrier := {x : Hc | x ∈ V ∧ ∀ k ∈ K, R (localToAdelic3 v k) x = x}
  add_mem' := by
    rintro x y ⟨hxV, hx⟩ ⟨hyV, hy⟩
    exact ⟨V.add_mem hxV hyV, fun k hk => by rw [map_add, hx k hk, hy k hk]⟩
  zero_mem' := ⟨V.zero_mem, fun k _ => map_zero _⟩
  smul_mem' := by
    rintro c x ⟨hxV, hx⟩
    exact ⟨V.smul_mem c hxV, fun k hk => by rw [map_smul, hx k hk]⟩

private theorem mem_fixedIn_iff {Hc : Type} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc]
    (R : AdelicGL 3 (𝓞 ℚ) ℚ →* (Hc →L[ℂ] Hc)) (v : HeightOneSpectrum (𝓞 ℚ)) (V : Submodule ℂ Hc)
    (K : Subgroup (LocalGL3 v)) (x : Hc) :
    x ∈ fixedIn R v V K ↔ x ∈ V ∧ ∀ k ∈ K, R (localToAdelic3 v k) x = x := Iff.rfl

private theorem smoothVectors_eq_iUnion {Hc : Type} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc]
    (R : AdelicGL 3 (𝓞 ℚ) ℚ →* (Hc →L[ℂ] Hc)) (v : HeightOneSpectrum (𝓞 ℚ)) (V : Submodule ℂ Hc) :
    smoothVectors R v V = ⋃ i : CompactOpenLevel v, ((fixedIn R v V i.1 : Submodule ℂ Hc) : Set Hc) := by
  ext y
  simp only [smoothVectors, Set.mem_setOf_eq, Set.mem_iUnion, SetLike.mem_coe, mem_fixedIn_iff]
  constructor
  · rintro ⟨hyV, K, hKc, hKo, hfix⟩
    exact ⟨⟨K, hKc, hKo⟩, hyV, hfix⟩
  · rintro ⟨⟨K, hKc, hKo⟩, hyV, hfix⟩
    exact ⟨hyV, K, hKc, hKo, hfix⟩

private noncomputable def normalizedSmoothing {Hc : Type} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc]
    (T : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (Hc →L[ℂ] Hc)) (α : (Fin 3 → Fin 3 → ℝ) → ℂ)
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ)))
    (v : HeightOneSpectrum (𝓞 ℚ)) (K : Subgroup (LocalGL3 v)) : Hc →L[ℂ] Hc :=
  (∫ g, levelKernelAt α K' v K g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))⁻¹ •
    T (levelKernelAt α K' v K)

private theorem normalizedSmoothing_apply {Hc : Type} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc]
    (T : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (Hc →L[ℂ] Hc)) (α : (Fin 3 → Fin 3 → ℝ) → ℂ)
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ)))
    (v : HeightOneSpectrum (𝓞 ℚ)) (K : Subgroup (LocalGL3 v)) (x : Hc) :
    normalizedSmoothing T α K' v K x =
      (∫ g, levelKernelAt α K' v K g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))⁻¹ •
        T (levelKernelAt α K' v K) x := rfl

section Bound

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

private theorem norm_normalizedSmoothing_apply_le {Hc : Type} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc]
    (R : AdelicGL 3 (𝓞 ℚ) ℚ →* (Hc →L[ℂ] Hc)) (hRn : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (x : Hc), ‖R g x‖ = ‖x‖)
    (T : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (Hc →L[ℂ] Hc))
    (hTw : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → ∀ h c : Hc,
      ⟪h, T φ c⟫_ℂ = ∫ g, φ g * ⟪h, R g c⟫_ℂ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (hφi : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ →
      Continuous φ ∧ HasCompactSupport φ ∧ Integrable φ (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    {α : (Fin 3 → Fin 3 → ℝ) → ℂ} (hα : IsSmoothArchFactor α) (hαr : ∀ m, α m = ((α m).re : ℂ) ∧ 0 ≤ (α m).re)
    {K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))}
    (hK' : ∀ p, IsOpen (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))) ∧
      IsCompact (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))))
    (hK'e : ∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p)
    {v : HeightOneSpectrum (𝓞 ℚ)} (i : CompactOpenLevel v) (x : Hc) :
    ‖normalizedSmoothing T α K' v i.1 x‖ ≤ 1 * ‖x‖ := by
  have hsk : IsSmoothingKernel (levelKernelAt α K' v i.1) := isSmoothingKernel_levelKernelAt hα hK' hK'e i.2.1 i.2.2
  have hop : ‖T (levelKernelAt α K' v i.1)‖ ≤
      ∫ g, ‖levelKernelAt α K' v i.1 g‖ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) :=
    opNorm_le_integral_norm_of_inner_eq_integral (T (levelKernelAt α K' v i.1)) (fun g y => R g y)
      (levelKernelAt α K' v i.1) (fun g y => (hRn g y).le) (hφi _ hsk).2.2 (fun c h => hTw _ hsk h c)
  have hN : ‖normalizedSmoothing T α K' v i.1‖ ≤ 1 :=
    norm_inv_integral_smul_le_one (T (levelKernelAt α K' v i.1)) (levelKernelAt α K' v i.1)
      (levelKernelAt_eq_re_and_nonneg hαr K' v i.1) (hφi _ hsk).2.2 hop
  exact ((normalizedSmoothing T α K' v i.1).le_opNorm x).trans (mul_le_mul_of_nonneg_right hN (norm_nonneg x))

end Bound
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

private theorem fixedIn_le_of_le {Hc : Type} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc]
    (R : AdelicGL 3 (𝓞 ℚ) ℚ →* (Hc →L[ℂ] Hc)) (v : HeightOneSpectrum (𝓞 ℚ)) (V : Submodule ℂ Hc)
    {K₀ K : Subgroup (LocalGL3 v)} (hle : K₀ ≤ K) : fixedIn R v V K ≤ fixedIn R v V K₀ := by
  intro x hx
  rw [mem_fixedIn_iff] at hx ⊢
  exact ⟨hx.1, fun k hk => hx.2 k (hle hk)⟩

private theorem apply_mem_fixedIn_map_conj {Hc : Type} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc]
    (R : AdelicGL 3 (𝓞 ℚ) ℚ →* (Hc →L[ℂ] Hc)) (v : HeightOneSpectrum (𝓞 ℚ)) (V : Submodule ℂ Hc)
    (hVR : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (x : Hc), x ∈ V → R g x ∈ V) (K : Subgroup (LocalGL3 v)) (h : LocalGL3 v)
    {x : Hc} (hx : x ∈ fixedIn R v V K) :
    R (localToAdelic3 v h) x ∈ fixedIn R v V (K.map (MulAut.conj h).toMonoidHom) := by
  rw [mem_fixedIn_iff] at hx ⊢
  refine ⟨hVR _ x hx.1, fun k' hk' => ?_⟩
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hk'
  have hkey : (MulAut.conj h).toMonoidHom k * h = h * k := by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_mul_cancel_right]
  rw [← ContinuousLinearMap.mul_apply, ← map_mul, ← map_mul, hkey, map_mul, map_mul, ContinuousLinearMap.mul_apply,
    hx.2 k hk]

private theorem smoothing_apply_mem_fixedIn {Hc : Type} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc]
    [CompleteSpace Hc] (R : AdelicGL 3 (𝓞 ℚ) ℚ →* (Hc →L[ℂ] Hc))
    (hRn : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (x : Hc), ‖R g x‖ = ‖x‖) (T : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (Hc →L[ℂ] Hc))
    (hTw : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → ∀ h c : Hc,
      ⟪h, T φ c⟫_ℂ = ∫ g, φ g * ⟪h, R g c⟫_ℂ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (v : HeightOneSpectrum (𝓞 ℚ)) (V : Submodule ℂ Hc) (hVc : IsClosed (V : Set Hc))
    (hVR : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (x : Hc), x ∈ V → R g x ∈ V) {α : (Fin 3 → Fin 3 → ℝ) → ℂ}
    (hα : IsSmoothArchFactor α) {K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))}
    (hK' : ∀ p, IsOpen (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))) ∧
      IsCompact (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))))
    (hK'e : ∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) (i : CompactOpenLevel v) {x : Hc}
    (hx : x ∈ V) : T (levelKernelAt α K' v i.1) x ∈ fixedIn R v V i.1 := by
  rw [mem_fixedIn_iff]
  exact ⟨smoothing_apply_mem R T hTw V hVc hVR (isSmoothingKernel_levelKernelAt hα hK' hK'e i.2.1 i.2.2) hx,
    fun k hk => localToAdelic3_smoothing_levelKernelAt R hRn T hTw v hα hK' hK'e i.2.1 i.2.2 hk x⟩

private theorem apply_normalizedSmoothing_comm {Hc : Type} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc]
    (R : AdelicGL 3 (𝓞 ℚ) ℚ →* (Hc →L[ℂ] Hc)) (hRn : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (x : Hc), ‖R g x‖ = ‖x‖)
    (T : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (Hc →L[ℂ] Hc))
    (hTw : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → ∀ h c : Hc,
      ⟪h, T φ c⟫_ℂ = ∫ g, φ g * ⟪h, R g c⟫_ℂ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (v : HeightOneSpectrum (𝓞 ℚ)) {α : (Fin 3 → Fin 3 → ℝ) → ℂ} (hα : IsSmoothArchFactor α)
    {K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))}
    (hK' : ∀ p, IsOpen (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))) ∧
      IsCompact (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))))
    (hK'e : ∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) (i : CompactOpenLevel v)
    (h : LocalGL3 v) (x : Hc) :
    R (localToAdelic3 v h) (normalizedSmoothing T α K' v i.1 x) =
      normalizedSmoothing T α K' v (i.1.map (MulAut.conj h).toMonoidHom) (R (localToAdelic3 v h) x) := by
  rw [normalizedSmoothing_apply, normalizedSmoothing_apply, map_smul,
    localToAdelic3_smoothing_levelKernelAt_eq_map_conj R hRn T hTw v hα hK' hK'e i.2.1 i.2.2 h x,
    integral_levelKernelAt_map_conj]

private theorem exists_clm_forall_eq_smul_smoothing_and_comm_localToAdelic3
    {Hc : Type} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
    (R : AdelicGL 3 (𝓞 ℚ) ℚ →* (Hc →L[ℂ] Hc)) (_hRn : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (x : Hc), ‖R g x‖ = ‖x‖)
    (_hRc : ∀ x : Hc, Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => R g x)
    (T : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (Hc →L[ℂ] Hc))
    (_hTw : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → ∀ h c : Hc,
      ⟪h, T φ c⟫_ℂ = ∫ g, φ g * ⟪h, R g c⟫_ℂ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (_hφi : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ →
      Continuous φ ∧ HasCompactSupport φ ∧ Integrable φ (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (v : HeightOneSpectrum (𝓞 ℚ))
    (V : Submodule ℂ Hc) (_hVc : IsClosed (V : Set Hc))
    (_hVR : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (x : Hc), x ∈ V → R g x ∈ V)
    (α : (Fin 3 → Fin 3 → ℝ) → ℂ) (_hα : IsSmoothArchFactor α) (_hαr : ∀ m, α m = ((α m).re : ℂ) ∧ 0 ≤ (α m).re)
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ)))
    (_hK' : ∀ p, IsOpen (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))) ∧
      IsCompact (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))))
    (_hK'e : ∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    ∃ A : Hc →L[ℂ] Hc,
      (∀ K : Subgroup (LocalGL3 v), IsCompact (K : Set (LocalGL3 v)) → IsOpen (K : Set (LocalGL3 v)) →
        ∀ x : Hc, x ∈ V → (∀ k ∈ K, R (localToAdelic3 v k) x = x) →
          A x = (∫ g, levelKernelAt α K' v K g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))⁻¹ •
            T (levelKernelAt α K' v K) x) ∧
      (∀ x : Hc, x ∈ closure (smoothVectors R v V) → A x ∈ closure (smoothVectors R v V)) ∧
      ∀ (h : LocalGL3 v) (x : Hc), x ∈ closure (smoothVectors R v V) →
        A (R (localToAdelic3 v h) x) = R (localToAdelic3 v h) (A x) := by
  haveI : Nonempty (CompactOpenLevel v) := ⟨⟨K' v, (_hK' v).2, (_hK' v).1⟩⟩
  have hdir : Directed (· ≤ ·) fun i : CompactOpenLevel v => fixedIn R v V i.1 := fun i j =>
    ⟨infLevel i j, fixedIn_le_of_le R v V inf_le_left, fixedIn_le_of_le R v V inf_le_right⟩
  have hcons : ∀ i j : CompactOpenLevel v, ∀ x ∈ fixedIn R v V i.1, x ∈ fixedIn R v V j.1 →
      normalizedSmoothing T α K' v i.1 x = normalizedSmoothing T α K' v j.1 x := by
    intro i j x hxi hxj
    rw [normalizedSmoothing_apply, normalizedSmoothing_apply]
    exact inv_integral_smul_smoothing_apply_eq R _hRn _hRc T _hTw _hφi v _hα _hK' _hK'e i.2.1 i.2.2 j.2.1 j.2.2 x
      ((mem_fixedIn_iff R v V i.1 x).1 hxi).2 ((mem_fixedIn_iff R v V j.1 x).1 hxj).2
  have hbound : ∀ i : CompactOpenLevel v, ∀ x ∈ fixedIn R v V i.1,
      ‖normalizedSmoothing T α K' v i.1 x‖ ≤ (1 : ℝ) * ‖x‖ := fun i x _ =>
    norm_normalizedSmoothing_apply_le R _hRn T _hTw _hφi _hα _hαr _hK' _hK'e i x
  have hmemfix : ∀ i : CompactOpenLevel v, ∀ x ∈ fixedIn R v V i.1,
      normalizedSmoothing T α K' v i.1 x ∈ fixedIn R v V i.1 := fun i x hx => by
    rw [normalizedSmoothing_apply]
    exact (fixedIn R v V i.1).smul_mem _ (smoothing_apply_mem_fixedIn R _hRn T _hTw v V _hVc _hVR _hα _hK' _hK'e i
      ((mem_fixedIn_iff R v V i.1 x).1 hx).1)
  have hmem : ∀ i : CompactOpenLevel v, ∀ x ∈ fixedIn R v V i.1, normalizedSmoothing T α K' v i.1 x ∈
      closure (⋃ j : CompactOpenLevel v, ((fixedIn R v V j.1 : Submodule ℂ Hc) : Set Hc)) := fun i x hx =>
    subset_closure (Set.mem_iUnion.2 ⟨i, hmemfix i x hx⟩)
  obtain ⟨A, -, hagree, hrange⟩ := DirectedSubmoduleFamily.exists_opNorm_le_and_forall_mem_eq_and_mem_closure
    (fun i : CompactOpenLevel v => fixedIn R v V i.1) (fun i => normalizedSmoothing T α K' v i.1) hdir hcons
    zero_le_one hbound hmem
  have hsets : smoothVectors R v V = ⋃ j : CompactOpenLevel v, ((fixedIn R v V j.1 : Submodule ℂ Hc) : Set Hc) :=
    smoothVectors_eq_iUnion R v V
  refine ⟨A, ?_, ?_, ?_⟩
  · intro K hKc hKo x hxV hxfix
    rw [hagree ⟨K, hKc, hKo⟩ x ((mem_fixedIn_iff R v V K x).2 ⟨hxV, hxfix⟩)]
    rfl
  · intro x _
    rw [hsets]
    exact hrange x
  · intro h x hx
    rw [hsets] at hx
    exact DirectedSubmoduleFamily.apply_comm_of_mem_closure (fun i : CompactOpenLevel v => fixedIn R v V i.1)
      (fun i => normalizedSmoothing T α K' v i.1) (R (localToAdelic3 v h)).continuous (conjLevel h) hagree
      (fun i y hy => apply_mem_fixedIn_map_conj R v V _hVR i.1 h hy)
      (fun i y _ => apply_normalizedSmoothing_comm R _hRn T _hTw v _hα _hK' _hK'e i h y) hx

end LevelFamilyUnit
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

namespace LocalStepUnit

open LevelFamilyUnit

section Generic

variable {Γ : Type*} [Group Γ] {Gv : Type*} [Group Gv]
variable {Hc : Type*} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc]

private def restrictOp (V : Submodule ℂ Hc) (f : Hc →L[ℂ] Hc) (hf : ∀ x : Hc, x ∈ V → f x ∈ V) :
    ↥V →L[ℂ] ↥V :=
  (f.comp V.subtypeL).codRestrict V fun x => hf x x.2

@[scoped simp] private theorem restrictOp_apply_coe (V : Submodule ℂ Hc) (f : Hc →L[ℂ] Hc)
    (hf : ∀ x : Hc, x ∈ V → f x ∈ V) (x : ↥V) : ((restrictOp V f hf x : ↥V) : Hc) = f x := rfl

private def restrictRep (R : Γ →* (Hc →L[ℂ] Hc)) (V : Submodule ℂ Hc)
    (hVR : ∀ (g : Γ) (x : Hc), x ∈ V → R g x ∈ V) (ι : Gv →* Γ) : Gv →* Module.End ℂ ↥V where
  toFun h := (restrictOp V (R (ι h)) (hVR (ι h))).toLinearMap
  map_one' := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp only [map_one, ContinuousLinearMap.coe_coe, restrictOp_apply_coe, ContinuousLinearMap.one_apply,
      Module.End.one_apply]
  map_mul' a b := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp only [map_mul, ContinuousLinearMap.coe_coe, restrictOp_apply_coe, ContinuousLinearMap.mul_apply,
      Module.End.mul_apply]

@[scoped simp] private theorem restrictRep_apply_coe (R : Γ →* (Hc →L[ℂ] Hc)) (V : Submodule ℂ Hc)
    (hVR : ∀ (g : Γ) (x : Hc), x ∈ V → R g x ∈ V) (ι : Gv →* Γ) (h : Gv) (x : ↥V) :
    ((restrictRep R V hVR ι h x : ↥V) : Hc) = R (ι h) x := rfl

private theorem inner_map_map_of_norm_map (R : Γ →* (Hc →L[ℂ] Hc))
    (hRn : ∀ (g : Γ) (x : Hc), ‖R g x‖ = ‖x‖) (g : Γ) (x y : Hc) : ⟪R g x, R g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  ({ toLinearMap := (R g).toLinearMap, norm_map' := hRn g } : Hc →ₗᵢ[ℂ] Hc).inner_map_map x y

private theorem restrictRep_inner (R : Γ →* (Hc →L[ℂ] Hc))
    (hRn : ∀ (g : Γ) (x : Hc), ‖R g x‖ = ‖x‖) (V : Submodule ℂ Hc)
    (hVR : ∀ (g : Γ) (x : Hc), x ∈ V → R g x ∈ V) (ι : Gv →* Γ) (h : Gv) (x y : ↥V) :
    ⟪restrictRep R V hVR ι h x, restrictRep R V hVR ι h y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [Submodule.coe_inner, Submodule.coe_inner, restrictRep_apply_coe, restrictRep_apply_coe]
  exact inner_map_map_of_norm_map R hRn _ _ _

private theorem mem_orthogonal_of_norm_map (R : Γ →* (Hc →L[ℂ] Hc))
    (hRn : ∀ (g : Γ) (x : Hc), ‖R g x‖ = ‖x‖) (V : Submodule ℂ Hc)
    (hVR : ∀ (g : Γ) (x : Hc), x ∈ V → R g x ∈ V) (g : Γ) (y : Hc) (hy : y ∈ Vᗮ) :
    R g y ∈ Vᗮ := by
  rw [Submodule.mem_orthogonal'] at hy ⊢
  intro u hu
  have hu' : R g (R g⁻¹ u) = u := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]
  rw [← hu', inner_map_map_of_norm_map R hRn]
  exact hy _ (hVR _ _ hu)

private def translationOps (R : Γ →* (Hc →L[ℂ] Hc)) (V : Submodule ℂ Hc)
    (hVR : ∀ (g : Γ) (x : Hc), x ∈ V → R g x ∈ V) (C : Set Γ) : Set (↥V →L[ℂ] ↥V) :=
  (fun c => restrictOp V (R c) (hVR c)) '' C

private theorem mem_translationOps (R : Γ →* (Hc →L[ℂ] Hc)) (V : Submodule ℂ Hc)
    (hVR : ∀ (g : Γ) (x : Hc), x ∈ V → R g x ∈ V) {C : Set Γ} {c : Γ} (hc : c ∈ C) :
    restrictOp V (R c) (hVR c) ∈ translationOps R V hVR C :=
  Set.mem_image_of_mem (fun c => restrictOp V (R c) (hVR c)) hc

private theorem translationOps_comm (R : Γ →* (Hc →L[ℂ] Hc)) (V : Submodule ℂ Hc)
    (hVR : ∀ (g : Γ) (x : Hc), x ∈ V → R g x ∈ V) (ι : Gv →* Γ) (C : Set Γ)
    (hC : ∀ c ∈ C, ∀ h : Gv, c * ι h = ι h * c) :
    ∀ s ∈ translationOps R V hVR C, ∀ (h : Gv) (x : ↥V),
      s (restrictRep R V hVR ι h x) = restrictRep R V hVR ι h (s x) := by
  rintro _ ⟨c, hc, rfl⟩ h x
  refine Subtype.ext ?_
  change R c (R (ι h) (x : Hc)) = R (ι h) (R c (x : Hc))
  rw [← ContinuousLinearMap.mul_apply, ← map_mul, hC c hc h, map_mul, ContinuousLinearMap.mul_apply]

private theorem eq_bot_or_eq_top_of_stable (R : Γ →* (Hc →L[ℂ] Hc)) (V : Submodule ℂ Hc)
    (hVc : IsClosed (V : Set Hc)) (hVR : ∀ (g : Γ) (x : Hc), x ∈ V → R g x ∈ V)
    (hVirr : ∀ W : Submodule ℂ Hc, IsClosed (W : Set Hc) →
      (∀ (g : Γ) (x : Hc), x ∈ W → R g x ∈ W) → W ≤ V → W = ⊥ ∨ W = V)
    (ι : Gv →* Γ) (C : Set Γ) (hfac : ∀ g : Γ, ∃ (h : Gv) (c : Γ), c ∈ C ∧ g = ι h * c)
    (W : Submodule ℂ ↥V) (hW : IsClosed (W : Set ↥V))
    (hWρ : ∀ (h : Gv) (x : ↥V), x ∈ W → restrictRep R V hVR ι h x ∈ W)
    (hWS : ∀ s ∈ translationOps R V hVR C, ∀ x : ↥V, x ∈ W → s x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  have hW'V : W.map V.subtype ≤ V := Submodule.map_subtype_le V W
  have hW'c : IsClosed ((W.map V.subtype : Submodule ℂ Hc) : Set Hc) := by
    rw [Submodule.map_coe, Submodule.coe_subtype]
    exact hVc.isClosedMap_subtype_val _ hW
  have hW'R : ∀ (g : Γ) (x : Hc), x ∈ W.map V.subtype → R g x ∈ W.map V.subtype := by
    rintro g _ ⟨x, hx, rfl⟩
    obtain ⟨h, c, hc, rfl⟩ := hfac g
    have h1 : restrictOp V (R c) (hVR c) x ∈ W := hWS _ (mem_translationOps R V hVR hc) x hx
    exact Submodule.mem_map.2 ⟨_, hWρ h _ h1, by simp [ContinuousLinearMap.mul_apply]⟩
  rcases hVirr _ hW'c hW'R hW'V with h0 | h1
  · left
    rw [eq_bot_iff]
    intro x hx
    have hx' : (x : Hc) ∈ W.map V.subtype := Submodule.mem_map.2 ⟨x, hx, rfl⟩
    rw [h0, Submodule.mem_bot] at hx'
    rw [Submodule.mem_bot]
    exact Subtype.ext hx'
  · right
    rw [eq_top_iff]
    intro x _
    have hx' : (x : Hc) ∈ W.map V.subtype := by
      rw [h1]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hx'
    have hyx' : y = x := Subtype.ext hyx
    exact hyx' ▸ hy

private theorem orthogonalProjection_map (R : Γ →* (Hc →L[ℂ] Hc))
    (hRn : ∀ (g : Γ) (x : Hc), ‖R g x‖ = ‖x‖) (V : Submodule ℂ Hc) [V.HasOrthogonalProjection]
    (hVR : ∀ (g : Γ) (x : Hc), x ∈ V → R g x ∈ V) (g : Γ)
    (x : Hc) : V.orthogonalProjection (R g x) = restrictOp V (R g) (hVR g) (V.orthogonalProjection x) := by
  refine Subtype.ext ?_
  rw [restrictOp_apply_coe, ← Submodule.starProjection_apply, ← Submodule.starProjection_apply]
  refine Submodule.eq_starProjection_of_mem_orthogonal (hVR g _ (Submodule.starProjection_apply_mem V x)) ?_
  rw [← map_sub]
  exact mem_orthogonal_of_norm_map R hRn V hVR g _ (Submodule.sub_starProjection_mem_orthogonal x)

private theorem sum_smul_mem_orthogonal (R : Γ →* (Hc →L[ℂ] Hc))
    (hRn : ∀ (g : Γ) (x : Hc), ‖R g x‖ = ‖x‖) (V : Submodule ℂ Hc) [V.HasOrthogonalProjection]
    (hVR : ∀ (g : Γ) (x : Hc), x ∈ V → R g x ∈ V)
    (ι : Gv →* Γ) (K : Subgroup Gv) (μ : Gv →₀ ℂ)
    (hkill : ∀ x : ↥V, (∀ k ∈ K, restrictRep R V hVR ι k x = x) →
      (μ.sum fun (h : Gv) (c : ℂ) => c • restrictRep R V hVR ι h x) = 0)
    (x : Hc) (hx : ∀ k ∈ K, R (ι k) x = x) :
    (μ.sum fun (h : Gv) (c : ℂ) => c • R (ι h) x) ∈ Vᗮ := by
  have hPx : ∀ k ∈ K, restrictRep R V hVR ι k (V.orthogonalProjection x) = V.orthogonalProjection x := by
    intro k hk
    refine Subtype.ext ?_
    rw [restrictRep_apply_coe, ← restrictOp_apply_coe V (R (ι k)) (hVR (ι k)),
      ← orthogonalProjection_map R hRn V hVR, hx k hk]
  have h0 := hkill _ hPx
  rw [← Submodule.orthogonalProjection_eq_zero_iff, map_finsuppSum]
  rw [← h0]
  refine Finsupp.sum_congr fun h _ => ?_
  rw [map_smul]
  congr 1
  refine Subtype.ext ?_
  rw [orthogonalProjection_map R hRn V hVR, restrictOp_apply_coe, restrictRep_apply_coe]

end Generic
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

section Adelic

variable (v : HeightOneSpectrum (𝓞 ℚ))

noncomputable section SharedComponents

private abbrev evalHom (q : HeightOneSpectrum (𝓞 ℚ)) : AdeleRing (𝓞 ℚ) ℚ →+* q.adicCompletion ℚ :=
  (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ q).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)

private theorem coe_localToAdelic3 (p : HeightOneSpectrum (𝓞 ℚ)) (x : LocalGL3 p) :
    ((localToAdelic3 p x : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ p (x : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) :=
  rfl

private theorem coe_componentAt3 (q : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ((componentAt3 (𝓞 ℚ) ℚ q g : GL (Fin 3) (q.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (q.adicCompletion ℚ)) =
      (evalHom q).mapMatrix (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  rfl

private theorem coe_archComponent3 (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ((archComponent3 (𝓞 ℚ) ℚ g : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) =
      (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  rfl

private theorem componentAt3_localToAdelic3 (p : HeightOneSpectrum (𝓞 ℚ)) (x : LocalGL3 p) :
    componentAt3 (𝓞 ℚ) ℚ p (localToAdelic3 p x) = x := by
  apply Units.ext
  rw [coe_componentAt3, coe_localToAdelic3]
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, finMatN, AdelicLevel.adeleFin_apply, AdelicLevel.finAdeleEval_apply,
    localMatN_apply_self]

private theorem _root_.LanglandsTunnell.CubicInduction.LocalConstituent.LocalStepUnit.componentAt3_localToAdelic3_of_ne {p q : HeightOneSpectrum (𝓞 ℚ)} (hq : q ≠ p) (x : LocalGL3 p) :
    componentAt3 (𝓞 ℚ) ℚ q (localToAdelic3 p x) = 1 := by
  apply Units.ext
  rw [coe_componentAt3, coe_localToAdelic3, Units.val_one]
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, finMatN, AdelicLevel.adeleFin_apply, AdelicLevel.finAdeleEval_apply,
    localMatN_apply_of_ne (Fin 3) (𝓞 ℚ) ℚ p _ i j hq]

p2m_export "LanglandsTunnell.CubicInduction.LocalConstituent.LocalStepUnit" "componentAt3_localToAdelic3_of_ne"

private theorem _root_.LanglandsTunnell.CubicInduction.LocalConstituent.LocalStepUnit.archComponent3_localToAdelic3 (p : HeightOneSpectrum (𝓞 ℚ)) (x : LocalGL3 p) :
    archComponent3 (𝓞 ℚ) ℚ (localToAdelic3 p x) = 1 := by
  apply Units.ext
  rw [coe_archComponent3, coe_localToAdelic3, mapMatrix_arch_finMatN, Units.val_one]

p2m_export "LanglandsTunnell.CubicInduction.LocalConstituent.LocalStepUnit" "archComponent3_localToAdelic3"

private theorem ext_of_components {g h : AdelicGL 3 (𝓞 ℚ) ℚ}
    (harch : archComponent3 (𝓞 ℚ) ℚ g = archComponent3 (𝓞 ℚ) ℚ h)
    (hfin : ∀ q : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ q g = componentAt3 (𝓞 ℚ) ℚ q h) : g = h := by
  apply Units.ext
  refine matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ ?_ ?_
  · have h₁ := congrArg Units.val harch
    rwa [coe_archComponent3, coe_archComponent3] at h₁
  · refine matrixFin_ext (Fin 3) (𝓞 ℚ) ℚ fun w => ?_
    have h₂ := congrArg Units.val (hfin w)
    rw [coe_componentAt3, coe_componentAt3] at h₂
    ext i j
    first | simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using congrFun (congrFun h₂ i) j | (have h_1 := congrFun (congrFun h₂ i) j; simp [RingHom.mapMatrix_apply, Matrix.map_apply] at h_1; exact h_1) | (have h_1 := congrFun (congrFun h₂ i) j; simp [RingHom.mapMatrix_apply, Matrix.map_apply] at h_1 ⊢; exact h_1) | exact (congrFun (congrFun h₂ i) j)

private theorem commute_localToAdelic3 {p : HeightOneSpectrum (𝓞 ℚ)} {g : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hg : componentAt3 (𝓞 ℚ) ℚ p g = 1) (x : LocalGL3 p) :
    g * localToAdelic3 p x = localToAdelic3 p x * g := by
  refine ext_of_components ?_ fun q => ?_
  · rw [map_mul, map_mul, archComponent3_localToAdelic3, mul_one, one_mul]
  · by_cases hq : q = p
    · subst hq
      rw [map_mul, map_mul, hg, one_mul, mul_one]
    · rw [map_mul, map_mul, componentAt3_localToAdelic3_of_ne hq, mul_one, one_mul]

end SharedComponents
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

private theorem exists_eq_localToAdelic3_mul (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∃ c : AdelicGL 3 (𝓞 ℚ) ℚ, componentAt3 (𝓞 ℚ) ℚ v c = 1 ∧
      g = localToAdelic3 v (componentAt3 (𝓞 ℚ) ℚ v g) * c :=
  ⟨(localToAdelic3 v (componentAt3 (𝓞 ℚ) ℚ v g))⁻¹ * g,
    by rw [map_mul, map_inv, componentAt3_localToAdelic3, inv_mul_cancel],
    (mul_inv_cancel_left _ _).symm⟩

private theorem continuous_componentAt3 (p : HeightOneSpectrum (𝓞 ℚ)) :
    Continuous (componentAt3 (𝓞 ℚ) ℚ p) :=
  Continuous.units_map _ ((continuous_id.matrix_map
    ((AdelicLevel.continuous_finAdeleEval (𝓞 ℚ) ℚ p).comp (AdelicLevel.continuous_adeleFin (𝓞 ℚ) ℚ))) :
      Continuous fun m : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ) =>
        m.map ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)))

private theorem isCompact_isOpen_inf {K₁ K₂ : Subgroup (LocalGL3 v)} (h₁c : IsCompact (K₁ : Set (LocalGL3 v)))
    (h₁o : IsOpen (K₁ : Set (LocalGL3 v))) (h₂o : IsOpen (K₂ : Set (LocalGL3 v))) :
    IsCompact ((K₁ ⊓ K₂ : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) ∧
      IsOpen ((K₁ ⊓ K₂ : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) := by
  rw [Subgroup.coe_inf]
  exact ⟨h₁c.inter_right (K₂.isClosed_of_isOpen h₂o), h₁o.inter h₂o⟩

private theorem isCompact_isOpen_conj (g : LocalGL3 v) {K : Subgroup (LocalGL3 v)}
    (hc : IsCompact (K : Set (LocalGL3 v))) (ho : IsOpen (K : Set (LocalGL3 v))) :
    IsCompact ((K.map (MulAut.conj g).toMonoidHom : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) ∧
      IsOpen ((K.map (MulAut.conj g).toMonoidHom : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) := by
  have hset : ((K.map (MulAut.conj g).toMonoidHom : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) =
      (fun k => k * g⁻¹) '' ((fun k => g * k) '' (K : Set (LocalGL3 v))) := by
    rw [Subgroup.coe_map, Set.image_image]
    rfl
  rw [hset]
  exact ⟨(hc.image (continuous_const_mul g)).image (continuous_mul_const g⁻¹),
    (Homeomorph.mulRight g⁻¹).isOpenMap _ ((Homeomorph.mulLeft g).isOpenMap _ ho)⟩

private theorem mem_map_conj {g k' : LocalGL3 v} {K : Subgroup (LocalGL3 v)}
    (hk' : k' ∈ K.map (MulAut.conj g).toMonoidHom) : ∃ k ∈ K, g * k * g⁻¹ = k' := by
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hk'
  exact ⟨k, hk, rfl⟩

section Smooth

variable {Hc : Type} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc]

private theorem apply_translate_eq_of_mem_map_conj (R : AdelicGL 3 (𝓞 ℚ) ℚ →* (Hc →L[ℂ] Hc))
    {K : Subgroup (LocalGL3 v)} {y : Hc} (hy : ∀ k ∈ K, R (localToAdelic3 v k) y = y)
    (gv : LocalGL3 v) {c : AdelicGL 3 (𝓞 ℚ) ℚ} (hc : componentAt3 (𝓞 ℚ) ℚ v c = 1) {k' : LocalGL3 v}
    (hk' : k' ∈ K.map (MulAut.conj gv).toMonoidHom) :
    R (localToAdelic3 v k') (R (localToAdelic3 v gv * c) y) = R (localToAdelic3 v gv * c) y := by
  obtain ⟨k, hk, rfl⟩ := mem_map_conj v hk'
  have hkey : localToAdelic3 v (gv * k * gv⁻¹) * (localToAdelic3 v gv * c) =
      localToAdelic3 v gv * c * localToAdelic3 v k := by
    rw [map_mul, map_mul, map_inv, mul_assoc (localToAdelic3 v gv * localToAdelic3 v k),
      inv_mul_cancel_left, mul_assoc, mul_assoc, commute_localToAdelic3 hc k]
  rw [← ContinuousLinearMap.mul_apply, ← map_mul, hkey, map_mul, ContinuousLinearMap.mul_apply, hy k hk]

private def smoothSubmodule (R : AdelicGL 3 (𝓞 ℚ) ℚ →* (Hc →L[ℂ] Hc)) (V : Submodule ℂ Hc)
    (K₀ : Subgroup (LocalGL3 v)) (hK₀c : IsCompact (K₀ : Set (LocalGL3 v))) (hK₀o : IsOpen (K₀ : Set (LocalGL3 v))) :
    Submodule ℂ Hc where
  carrier := smoothVectors R v V
  add_mem' := by
    rintro a b ⟨haV, Ka, haKc, haKo, ha⟩ ⟨hbV, Kb, hbKc, hbKo, hb⟩
    refine ⟨V.add_mem haV hbV, Ka ⊓ Kb, (isCompact_isOpen_inf v haKc haKo hbKo).1,
      (isCompact_isOpen_inf v haKc haKo hbKo).2, fun k hk => ?_⟩
    rw [map_add, ha k (Subgroup.mem_inf.1 hk).1, hb k (Subgroup.mem_inf.1 hk).2]
  zero_mem' := ⟨V.zero_mem, K₀, hK₀c, hK₀o, fun k _ => map_zero _⟩
  smul_mem' := by
    rintro c y ⟨hyV, K, hKc, hKo, hy⟩
    refine ⟨V.smul_mem c hyV, K, hKc, hKo, fun k hk => ?_⟩
    rw [map_smul, hy k hk]

private theorem coe_smoothSubmodule (R : AdelicGL 3 (𝓞 ℚ) ℚ →* (Hc →L[ℂ] Hc)) (V : Submodule ℂ Hc)
    (K₀ : Subgroup (LocalGL3 v)) (hK₀c : IsCompact (K₀ : Set (LocalGL3 v)))
    (hK₀o : IsOpen (K₀ : Set (LocalGL3 v))) :
    (smoothSubmodule v R V K₀ hK₀c hK₀o : Set Hc) = smoothVectors R v V := rfl

private theorem translate_mem_smoothVectors (R : AdelicGL 3 (𝓞 ℚ) ℚ →* (Hc →L[ℂ] Hc)) (V : Submodule ℂ Hc)
    (hVR : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (x : Hc), x ∈ V → R g x ∈ V) (g : AdelicGL 3 (𝓞 ℚ) ℚ) {y : Hc}
    (hy : y ∈ smoothVectors R v V) : R g y ∈ smoothVectors R v V := by
  obtain ⟨hyV, K, hKc, hKo, hyK⟩ := hy
  obtain ⟨c, hc, hg⟩ := exists_eq_localToAdelic3_mul v g
  refine ⟨hVR _ _ hyV, K.map (MulAut.conj (componentAt3 (𝓞 ℚ) ℚ v g)).toMonoidHom,
    (isCompact_isOpen_conj v _ hKc hKo).1, (isCompact_isOpen_conj v _ hKc hKo).2, fun k' hk' => ?_⟩
  rw [hg]
  exact apply_translate_eq_of_mem_map_conj v R hyK _ hc hk'

private theorem closure_smoothVectors_eq (R : AdelicGL 3 (𝓞 ℚ) ℚ →* (Hc →L[ℂ] Hc)) (V : Submodule ℂ Hc)
    (hVc : IsClosed (V : Set Hc)) (hVR : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (x : Hc), x ∈ V → R g x ∈ V)
    (hVirr : ∀ W : Submodule ℂ Hc, IsClosed (W : Set Hc) →
      (∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (x : Hc), x ∈ W → R g x ∈ W) → W ≤ V → W = ⊥ ∨ W = V)
    {x₀ : Hc} (hx₀0 : x₀ ≠ 0) (K₀ : Subgroup (LocalGL3 v)) (hK₀c : IsCompact (K₀ : Set (LocalGL3 v)))
    (hK₀o : IsOpen (K₀ : Set (LocalGL3 v))) (hx₀s : x₀ ∈ smoothVectors R v V) :
    closure (smoothVectors R v V) = (V : Set Hc) := by
  set W := (smoothSubmodule v R V K₀ hK₀c hK₀o).topologicalClosure with hWdef
  have hWcoe : (W : Set Hc) = closure (smoothVectors R v V) := by
    rw [hWdef, Submodule.topologicalClosure_coe, coe_smoothSubmodule]
  have hle : smoothVectors R v V ⊆ (V : Set Hc) := fun y hy => hy.1
  have hWV : W ≤ V := by
    intro y hy
    have hy' : y ∈ closure (smoothVectors R v V) := by rwa [← hWcoe]
    exact hVc.closure_subset_iff.2 hle hy'
  have hWR : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (x : Hc), x ∈ W → R g x ∈ W := by
    intro g x hx
    have hx' : x ∈ closure (smoothVectors R v V) := by rwa [← SetLike.mem_coe, hWcoe] at hx
    have himg : R g x ∈ closure (R g '' smoothVectors R v V) :=
      map_mem_closure (R g).continuous hx' fun y hy => Set.mem_image_of_mem _ hy
    have hsub : R g '' smoothVectors R v V ⊆ smoothVectors R v V := by
      rintro _ ⟨y, hy, rfl⟩
      exact translate_mem_smoothVectors v R V hVR g hy
    rw [← SetLike.mem_coe, hWcoe]
    exact closure_mono hsub himg
  rcases hVirr W (Submodule.isClosed_topologicalClosure _) hWR hWV with h0 | h1
  · exfalso
    have hx₀W : x₀ ∈ W := by
      rw [← SetLike.mem_coe, hWcoe]
      exact subset_closure hx₀s
    rw [h0, Submodule.mem_bot] at hx₀W
    exact hx₀0 hx₀W
  · rw [← hWcoe, h1]

end Smooth
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

end Adelic
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

section NonVanishing

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem isSmoothArchFactor_sq {α : (Fin 3 → Fin 3 → ℝ) → ℂ} (hα : IsSmoothArchFactor α) :
    IsSmoothArchFactor fun m => (((α m).re ^ 2 : ℝ) : ℂ) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp ((Complex.reCLM.contDiff.comp hα.1).pow 2)
  · exact hα.2.1.comp_left (g := fun z : ℂ => (((z.re) ^ 2 : ℝ) : ℂ)) (by simp)
  · refine Set.Subset.trans (closure_mono fun m hm => ?_) hα.2.2
    simp only [Function.mem_support, ne_eq] at hm ⊢
    intro h0
    apply hm
    rw [h0, Complex.zero_re, zero_pow two_ne_zero, Complex.ofReal_zero]

private theorem isSmoothingKernel_levelKernelAt {α : (Fin 3 → Fin 3 → ℝ) → ℂ} (hα : IsSmoothArchFactor α)
    {K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))}
    (hK' : ∀ p, IsOpen (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))) ∧
      IsCompact (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))))
    (hK'e : ∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p)
    {K : Subgroup (LocalGL3 v)} (hKc : IsCompact (K : Set (LocalGL3 v))) (hKo : IsOpen (K : Set (LocalGL3 v))) :
    IsSmoothingKernel (levelKernelAt α K' v K) := by
  classical
  refine ⟨α, Function.update K' v K, hα, fun p => ?_, ?_, fun g => ?_⟩
  · rcases eq_or_ne p v with rfl | hp
    · rw [Function.update_self]
      exact ⟨hKo, hKc⟩
    · rw [Function.update_of_ne hp]
      exact hK' p
  · refine (hK'e.and (Set.finite_singleton v).compl_mem_cofinite).mono fun p hp => ?_
    have hpv : p ≠ v := fun h => hp.2 (h ▸ Set.mem_singleton v)
    rw [Function.update_of_ne hpv]
    exact hp.1
  · simp only [levelKernelAt]
    congr 2
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hxv, hx⟩ p
      rcases eq_or_ne p v with rfl | hp
      · rwa [Function.update_self]
      · rw [Function.update_of_ne hp]
        exact hx p hp
    · intro hx
      refine ⟨?_, fun p hp => ?_⟩
      · have := hx v
        rwa [Function.update_self] at this
      · have := hx p
        rwa [Function.update_of_ne hp] at this

section WithSpace

variable {Hc : Type} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc]

private theorem exists_nhds_one (R : AdelicGL 3 (𝓞 ℚ) ℚ →* (Hc →L[ℂ] Hc))
    (hRc : ∀ x : Hc, Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => R g x) {x₀ : Hc} (hx₀0 : x₀ ≠ 0)
    {K₀ : Subgroup (LocalGL3 v)} (hK₀o : IsOpen (K₀ : Set (LocalGL3 v))) :
    ∃ U ∈ nhds (1 : AdelicGL 3 (𝓞 ℚ) ℚ), (∀ g ∈ U, ‖x₀‖ ^ 2 / 2 < (⟪x₀, R g x₀⟫_ℂ).re) ∧
      ∀ g ∈ U, componentAt3 (𝓞 ℚ) ℚ v g ∈ K₀ := by
  refine ⟨{g | ‖x₀‖ ^ 2 / 2 < (⟪x₀, R g x₀⟫_ℂ).re} ∩ {g | componentAt3 (𝓞 ℚ) ℚ v g ∈ K₀},
    Filter.inter_mem ?_ ?_, fun g hg => hg.1, fun g hg => hg.2⟩
  · have hcont : Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => (⟪x₀, R g x₀⟫_ℂ).re :=
      Complex.continuous_re.comp (continuous_const.inner (hRc x₀))
    refine (isOpen_lt continuous_const hcont).mem_nhds ?_
    show ‖x₀‖ ^ 2 / 2 < (⟪x₀, R 1 x₀⟫_ℂ).re
    have h := inner_self_eq_norm_sq (𝕜 := ℂ) x₀
    rw [RCLike.re_to_complex] at h
    rw [map_one, ContinuousLinearMap.one_apply, h]
    exact half_lt_self (pow_pos (norm_pos_iff.2 hx₀0) 2)
  · exact ((continuous_componentAt3 v).isOpen_preimage _ hK₀o).mem_nhds (by
      show componentAt3 (𝓞 ℚ) ℚ v 1 ∈ K₀
      rw [map_one]
      exact K₀.one_mem)

private theorem levelKernelAt_sq_eq {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} {α : (Fin 3 → Fin 3 → ℝ) → ℂ}
    {K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))}
    (hφeq : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, φ g = α (archEntries g) *
      Set.indicator {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} (fun _ => (1 : ℂ)) g)
    {K₀ : Subgroup (LocalGL3 v)} (hφK₀ : ∀ g, φ g ≠ 0 → componentAt3 (𝓞 ℚ) ℚ v g ∈ K₀)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    levelKernelAt (fun m => (((α m).re ^ 2 : ℝ) : ℂ)) K' v (K' v ⊓ K₀) g = (((φ g).re ^ 2 : ℝ) : ℂ) := by
  classical
  simp only [levelKernelAt, Set.indicator_apply, Set.mem_setOf_eq]
  by_cases hA : componentAt3 (𝓞 ℚ) ℚ v g ∈ K' v ⊓ K₀ ∧ ∀ p, p ≠ v → componentAt3 (𝓞 ℚ) ℚ p g ∈ K' p
  · have hall : ∀ p, componentAt3 (𝓞 ℚ) ℚ p g ∈ K' p := fun p => by
      rcases eq_or_ne p v with rfl | hp
      · exact (Subgroup.mem_inf.1 hA.1).1
      · exact hA.2 p hp
    have hmem : g ∈ {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} := hall
    rw [if_pos hA, mul_one, hφeq g]
    simp only [Set.indicator_of_mem hmem, mul_one]
  · rw [if_neg hA, mul_zero]
    have hφ0 : φ g = 0 := by
      by_contra hne
      have hind : ∀ p, componentAt3 (𝓞 ℚ) ℚ p g ∈ K' p := by
        by_contra hnot
        have hnot' : g ∉ {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} := hnot
        exact hne (by rw [hφeq g, Set.indicator_of_notMem hnot', mul_zero])
      exact hA ⟨Subgroup.mem_inf.2 ⟨hind v, hφK₀ g hne⟩, fun p _ => hind p⟩
    rw [hφ0, Complex.zero_re, zero_pow two_ne_zero, Complex.ofReal_zero]

private theorem integral_sq_re_pos {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hφc : Continuous φ) (hφcs : HasCompactSupport φ)
    (hφi : Integrable φ (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (hφpos : 0 < (∫ g, φ g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)).re) :
    0 < ∫ g, (φ g).re ^ 2 ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  set μ := NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ with hμ
  have hre : Integrable (fun g => (φ g).re) μ := hφi.re
  obtain ⟨C, hC⟩ := (hφcs.comp_left (g := Complex.re) Complex.zero_re).exists_bound_of_continuous
    (Complex.continuous_re.comp hφc)
  have hsq : Integrable (fun g => (φ g).re ^ 2) μ := by
    have h := hre.mul_bdd hre.aestronglyMeasurable (Filter.Eventually.of_forall hC)
    refine h.congr (Filter.Eventually.of_forall fun g => ?_)
    simp only [pow_two]
  have hnn : 0 ≤ fun g => (φ g).re ^ 2 := fun g => sq_nonneg _
  rcases (integral_nonneg (μ := μ) hnn).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    have hae : (fun g => (φ g).re ^ 2) =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg hnn hsq).1 heq.symm
    have hae' : (fun g => (φ g).re) =ᵐ[μ] 0 :=
      hae.mono fun g hg => by simpa [pow_eq_zero_iff, two_ne_zero] using hg
    have h0 : ∫ g, (φ g).re ∂μ = 0 := by
      rw [integral_congr_ae hae']
      simp
    have h1 : (∫ g, φ g ∂μ).re = ∫ g, (φ g).re ∂μ := by
      have h := Complex.reCLM.integral_comp_comm hφi
      simp only [Complex.reCLM_apply] at h
      exact h.symm
    rw [h1, h0] at hφpos
    exact lt_irrefl _ hφpos

private theorem smoothing_apply_ne_zero (R : AdelicGL 3 (𝓞 ℚ) ℚ →* (Hc →L[ℂ] Hc))
    (hRn : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (x : Hc), ‖R g x‖ = ‖x‖)
    (hRc : ∀ x : Hc, Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => R g x) {S : Hc →L[ℂ] Hc}
    {ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hSw : ∀ h c : Hc, ⟪h, S c⟫_ℂ = ∫ g, ψ g * ⟪h, R g c⟫_ℂ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (hψi : Integrable ψ (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (hψr : ∀ g, ψ g = ((ψ g).re : ℂ) ∧ 0 ≤ (ψ g).re)
    (hψpos : 0 < ∫ g, (ψ g).re ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    {x₀ : Hc} {b : ℝ} (hb : 0 < b) (hbψ : ∀ g, ψ g ≠ 0 → b < (⟪x₀, R g x₀⟫_ℂ).re) : S x₀ ≠ 0 := by
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  set μ := NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ with hμ
  intro hS0
  have hinner : ⟪x₀, S x₀⟫_ℂ = 0 := by rw [hS0, inner_zero_right]

  have hmeas : AEStronglyMeasurable (fun g : AdelicGL 3 (𝓞 ℚ) ℚ => ⟪x₀, R g x₀⟫_ℂ) μ :=
    (continuous_const.inner (hRc x₀)).aestronglyMeasurable
  have hbdd : ∀ᵐ g ∂μ, ‖⟪x₀, R g x₀⟫_ℂ‖ ≤ ‖x₀‖ * ‖x₀‖ :=
    Filter.Eventually.of_forall fun g => (norm_inner_le_norm x₀ _).trans (by rw [hRn])
  have hint : Integrable (fun g => ψ g * ⟪x₀, R g x₀⟫_ℂ) μ := hψi.mul_bdd hmeas hbdd
  have hlow : ∀ g, b * (ψ g).re ≤ (ψ g * ⟪x₀, R g x₀⟫_ℂ).re := fun g => by
    by_cases h0 : ψ g = 0
    · rw [h0, zero_mul, Complex.zero_re, mul_zero]
    · rw [(hψr g).1, Complex.re_ofReal_mul, Complex.ofReal_re, mul_comm b]
      exact mul_le_mul_of_nonneg_left (hbψ g h0).le (hψr g).2
  have hle : ∫ g, b * (ψ g).re ∂μ ≤ ∫ g, (ψ g * ⟪x₀, R g x₀⟫_ℂ).re ∂μ :=
    integral_mono (hψi.re.const_mul b) hint.re hlow
  have hre : (∫ g, ψ g * ⟪x₀, R g x₀⟫_ℂ ∂μ).re = ∫ g, (ψ g * ⟪x₀, R g x₀⟫_ℂ).re ∂μ := by
    have h := Complex.reCLM.integral_comp_comm hint
    simp only [Complex.reCLM_apply] at h
    exact h.symm
  have hpos : 0 < (∫ g, ψ g * ⟪x₀, R g x₀⟫_ℂ ∂μ).re := by
    rw [hre]
    refine lt_of_lt_of_le ?_ hle
    rw [integral_const_mul]
    exact mul_pos hb hψpos
  rw [← hSw, hinner, Complex.zero_re] at hpos
  exact lt_irrefl _ hpos

private theorem isCompactOperator_restrict {Γ Gv : Type*} [Group Γ] [Group Gv]
    (R : Γ →* (Hc →L[ℂ] Hc)) (V : Submodule ℂ Hc) (hVc : IsClosed (V : Set Hc))
    (hVR : ∀ (g : Γ) (x : Hc), x ∈ V → R g x ∈ V) (ι : Gv →* Γ) (A S : Hc →L[ℂ] Hc) (c : ℂ)
    (hAV : ∀ x : Hc, x ∈ V → A x ∈ V) (hS : IsCompactOperator S) (K : Subgroup Gv)
    (hAS : ∀ x : Hc, x ∈ V → (∀ k ∈ K, R (ι k) x = x) → A x = c • S x) :
    IsCompactOperator fun x : ↥(FLT.SmoothAdmissibleSchurCommutant.fixedVectors (restrictRep R V hVR ι) K) =>
      restrictOp V A hAV x := by
  obtain ⟨U₀, hU₀, hU₀c⟩ := (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image _).1 (hS.smul c)
  set F := FLT.SmoothAdmissibleSchurCommutant.fixedVectors (restrictRep R V hVR ι) K with hF
  have hval : Continuous fun x : ↥F => ((x : ↥V) : Hc) := continuous_subtype_val.comp continuous_subtype_val
  refine (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image _).2
    ⟨(fun x : ↥F => ((x : ↥V) : Hc)) ⁻¹' U₀, hval.continuousAt.preimage_mem_nhds (by exact hU₀), ?_⟩
  have hemb := hVc.isClosedEmbedding_subtypeVal
  have hsub : (fun x : ↥F => restrictOp V A hAV x) '' ((fun x : ↥F => ((x : ↥V) : Hc)) ⁻¹' U₀) ⊆
      ((↑) : ↥V → Hc) ⁻¹' closure ((c • (S : Hc → Hc)) '' U₀) := by
    rintro _ ⟨x, hx, rfl⟩
    refine subset_closure ⟨_, hx, ?_⟩
    rw [restrictOp_apply_coe]
    exact (hAS _ (x : ↥V).2 fun k hk => by
      have := congrArg Subtype.val
        ((FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors (restrictRep R V hVR ι)).1 x.2 k hk)
      rwa [restrictRep_apply_coe] at this).symm
  exact (hemb.isCompact_preimage hU₀c).of_isClosed_subset isClosed_closure
    (closure_minimal hsub (isClosed_closure.preimage continuous_subtype_val))

end WithSpace
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

end NonVanishing
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability"

private theorem exists_isIrreducibleRep_forall_sum_smul_mem_orthogonal
    {Hc : Type} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
    (R : AdelicGL 3 (𝓞 ℚ) ℚ →* (Hc →L[ℂ] Hc)) (_hRn : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (x : Hc), ‖R g x‖ = ‖x‖)
    (_hRc : ∀ x : Hc, Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => R g x)
    (T : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (Hc →L[ℂ] Hc))
    (_hTw : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → ∀ h c : Hc,
      ⟪h, T φ c⟫_ℂ = ∫ g, φ g * ⟪h, R g c⟫_ℂ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (_hTk : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → IsCompactOperator (T φ))
    (_hφi : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ →
      Continuous φ ∧ HasCompactSupport φ ∧ Integrable φ (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (_hsup : ∀ U ∈ nhds (1 : AdelicGL 3 (𝓞 ℚ) ℚ), ∃ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ ∧
      (∀ g, φ g = ((φ g).re : ℂ) ∧ 0 ≤ (φ g).re) ∧ Function.support φ ⊆ U ∧
      Integrable φ (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) ∧
      0 < (∫ g, φ g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)).re)
    (v : HeightOneSpectrum (𝓞 ℚ))
    (V : Submodule ℂ Hc) (_hVc : IsClosed (V : Set Hc))
    (_hVR : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (x : Hc), x ∈ V → R g x ∈ V)
    (_hVirr : ∀ W : Submodule ℂ Hc, IsClosed (W : Set Hc) →
      (∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (x : Hc), x ∈ W → R g x ∈ W) → W ≤ V → W = ⊥ ∨ W = V)
    (x₀ : Hc) (_hx₀ : x₀ ∈ V) (_hx₀0 : x₀ ≠ 0)
    (K₀ : Subgroup (LocalGL3 v)) (_hK₀c : IsCompact (K₀ : Set (LocalGL3 v))) (_hK₀o : IsOpen (K₀ : Set (LocalGL3 v)))
    (_hx₀K : ∀ k ∈ K₀, R (localToAdelic3 v k) x₀ = x₀) :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Module ℂ E) (πE : LocalGL3 v →* Module.End ℂ E),
      FLT.SmoothAdmissibleSchurCommutant.IsIrreducibleRep πE ∧
      FLT.SmoothAdmissibleSchurCommutant.IsSmoothRep πE ∧
      FLT.SmoothAdmissibleSchurCommutant.IsAdmissibleRep πE ∧
      ∀ K : Subgroup (LocalGL3 v), IsCompact (K : Set (LocalGL3 v)) → IsOpen (K : Set (LocalGL3 v)) →
        ∃ (d : ℕ) (e : Fin d → E), ∀ μ : LocalGL3 v →₀ ℂ,
          (∀ j : Fin d, (μ.sum fun h c => c • πE h (e j)) = 0) →
            ∀ x : Hc, (∀ k ∈ K, R (localToAdelic3 v k) x = x) →
              (μ.sum fun h c => c • R (localToAdelic3 v h) x) ∈ Vᗮ := by
  classical
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI : CompleteSpace ↥V := _hVc.completeSpace_coe

  have hx₀s : x₀ ∈ smoothVectors R v V := ⟨_hx₀, K₀, _hK₀c, _hK₀o, _hx₀K⟩
  have hcl : closure (smoothVectors R v V) = (V : Set Hc) :=
    closure_smoothVectors_eq v R V _hVc _hVR _hVirr _hx₀0 K₀ _hK₀c _hK₀o hx₀s

  obtain ⟨U, hU1, hUre, hUK⟩ := exists_nhds_one v R _hRc _hx₀0 _hK₀o
  obtain ⟨φ, hφk, -, hφU, -, hφpos⟩ := _hsup U hU1
  obtain ⟨hφc, hφcs, hφi⟩ := _hφi φ hφk
  obtain ⟨α, K', hα, hK', hK'e, hφeq⟩ := hφk
  have hφne : ∀ g, φ g ≠ 0 → g ∈ U := fun g hg => hφU (Function.mem_support.2 hg)

  obtain ⟨hK₁c, hK₁o⟩ := isCompact_isOpen_inf v (hK' v).2 (hK' v).1 _hK₀o
  have hα₂ : IsSmoothArchFactor fun m => (((α m).re ^ 2 : ℝ) : ℂ) := isSmoothArchFactor_sq hα
  have hα₂r : ∀ m : Fin 3 → Fin 3 → ℝ,
      (fun m => (((α m).re ^ 2 : ℝ) : ℂ)) m = (((fun m => (((α m).re ^ 2 : ℝ) : ℂ)) m).re : ℂ) ∧
        0 ≤ ((fun m => (((α m).re ^ 2 : ℝ) : ℂ)) m).re := fun m =>
    ⟨by simp only [Complex.ofReal_re], by simp only [Complex.ofReal_re]; exact sq_nonneg _⟩
  obtain ⟨A, hA1, hA2, hA3⟩ := exists_clm_forall_eq_smul_smoothing_and_comm_localToAdelic3 R _hRn _hRc T _hTw _hφi
    v V _hVc _hVR (fun m => (((α m).re ^ 2 : ℝ) : ℂ)) hα₂ hα₂r K' hK' hK'e

  set ψ := levelKernelAt (fun m => (((α m).re ^ 2 : ℝ) : ℂ)) K' v (K' v ⊓ K₀) with hψdef
  have hψ : ∀ g, ψ g = (((φ g).re ^ 2 : ℝ) : ℂ) := fun g =>
    levelKernelAt_sq_eq v hφeq (fun g hg => hUK g (hφne g hg)) g
  have hψk : IsSmoothingKernel ψ := isSmoothingKernel_levelKernelAt v hα₂ hK' hK'e hK₁c hK₁o
  have hψi : Integrable ψ (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := (_hφi ψ hψk).2.2
  have hψr : ∀ g, ψ g = ((ψ g).re : ℂ) ∧ 0 ≤ (ψ g).re := fun g => by
    rw [hψ g, Complex.ofReal_re]
    exact ⟨rfl, sq_nonneg _⟩
  have hψre : ∀ g, (ψ g).re = (φ g).re ^ 2 := fun g => by rw [hψ g, Complex.ofReal_re]
  have hψpos : 0 < ∫ g, (ψ g).re ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
    simp only [hψre]
    exact integral_sq_re_pos hφc hφcs hφi hφpos
  have hψmass : (∫ g, ψ g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)) ≠ 0 := by
    intro h0
    have h4 : (∫ g, ψ g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)) =
        ((∫ g, (ψ g).re ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) : ℝ) : ℂ) :=
      (integral_congr_ae (Filter.Eventually.of_forall fun g => (hψr g).1)).trans integral_ofReal
    rw [h4] at h0
    exact hψpos.ne' (Complex.ofReal_eq_zero.1 h0)
  have hTx₀ : T ψ x₀ ≠ 0 :=
    smoothing_apply_ne_zero R _hRn _hRc (S := T ψ) (_hTw ψ hψk) hψi hψr hψpos
      (half_pos (pow_pos (norm_pos_iff.2 _hx₀0) 2)) fun g hg => hUre g (hφne g (by
        intro h0
        exact hg (by rw [hψ g, h0, Complex.zero_re, zero_pow two_ne_zero, Complex.ofReal_zero])))
  have hAx₀ : A x₀ ≠ 0 := by
    rw [hA1 (K' v ⊓ K₀) hK₁c hK₁o x₀ _hx₀ fun k hk => _hx₀K k (Subgroup.mem_inf.1 hk).2]
    exact smul_ne_zero (inv_ne_zero hψmass) hTx₀

  have hAV : ∀ x : Hc, x ∈ V → A x ∈ V := fun x hx => by
    have h := hA2 x (by rw [hcl]; exact hx)
    rwa [hcl] at h

  set ρ : LocalGL3 v →* Module.End ℂ ↥V := restrictRep R V _hVR (localToAdelic3 v) with hρdef
  have hρ : ∀ (g : LocalGL3 v) (x y : ↥V), ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ :=
    restrictRep_inner R _hRn V _hVR (localToAdelic3 v)
  set TV : ↥V →L[ℂ] ↥V := restrictOp V A hAV with hTVdef
  have hT : ∀ (g : LocalGL3 v) (x : ↥V), TV (ρ g x) = ρ g (TV x) := fun g x =>
    Subtype.ext (hA3 g x (by rw [hcl]; exact x.2))
  have hTc : ∀ K : Subgroup (LocalGL3 v), IsCompact (K : Set (LocalGL3 v)) → IsOpen (K : Set (LocalGL3 v)) →
      IsCompactOperator (fun x : ↥(FLT.SmoothAdmissibleSchurCommutant.fixedVectors ρ K) => TV x) := by
    intro K hKc hKo
    have hKk : IsSmoothingKernel (levelKernelAt (fun m => (((α m).re ^ 2 : ℝ) : ℂ)) K' v K) :=
      isSmoothingKernel_levelKernelAt v hα₂ hK' hK'e hKc hKo
    exact isCompactOperator_restrict R V _hVc _hVR (localToAdelic3 v) A _
      (∫ g, levelKernelAt (fun m => (((α m).re ^ 2 : ℝ) : ℂ)) K' v K g
        ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))⁻¹ hAV (_hTk _ hKk) K
      fun x hx hxK => hA1 K hKc hKo x hx hxK
  have hTx : ∃ x : ↥V, (∃ K : Subgroup (LocalGL3 v), IsCompact (K : Set (LocalGL3 v)) ∧
      IsOpen (K : Set (LocalGL3 v)) ∧ x ∈ FLT.SmoothAdmissibleSchurCommutant.fixedVectors ρ K) ∧ TV x ≠ 0 :=
    ⟨⟨x₀, _hx₀⟩, ⟨K₀, _hK₀c, _hK₀o, (FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors ρ).2 fun k hk =>
      Subtype.ext (_hx₀K k hk)⟩, fun h0 => hAx₀ (congrArg Subtype.val h0)⟩

  have hX :=
    RepTheory.IsometricRep.exists_finiteDimensional_inf_fixedVectors_of_isCompactOperator ρ hρ TV hT hTc hTx
  have hfac : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ (h : LocalGL3 v) (c : AdelicGL 3 (𝓞 ℚ) ℚ),
      c ∈ {c : AdelicGL 3 (𝓞 ℚ) ℚ | componentAt3 (𝓞 ℚ) ℚ v c = 1} ∧ g = localToAdelic3 v h * c := fun g => by
    obtain ⟨c, hc, hg⟩ := exists_eq_localToAdelic3_mul v g
    exact ⟨_, c, hc, hg⟩
  obtain ⟨E, instE₁, instE₂, πE, hirrE, hsmE, hadmE, hkill⟩ :=
    RepTheory.IsometricRep.exists_forall_sum_smul_eq_zero_of_finiteDimensional_inf_fixedVectors ρ hρ
      (translationOps R V _hVR {c : AdelicGL 3 (𝓞 ℚ) ℚ | componentAt3 (𝓞 ℚ) ℚ v c = 1})
      (translationOps_comm R V _hVR (localToAdelic3 v) _ fun c hc h => commute_localToAdelic3 hc h)
      (fun W hW hWρ hWS => eq_bot_or_eq_top_of_stable R V _hVc _hVR _hVirr (localToAdelic3 v) _ hfac W hW hWρ hWS)
      hX
  refine ⟨E, instE₁, instE₂, πE, hirrE, hsmE, hadmE, fun K hKc hKo => ?_⟩
  obtain ⟨d, e, he⟩ := hkill K hKc hKo
  refine ⟨d, e, fun μ hμ x hx => ?_⟩
  exact sum_smul_mem_orthogonal R _hRn V _hVR (localToAdelic3 v) K μ (fun y hy => he y hy μ hμ) x hx

end LocalStepUnit
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.LocalConstituent.LocalStepUnit"

namespace TransportUnit

section Linearity

variable {G : Type*} [Group G] {α : Type*}

private theorem isRightInvariant_sum (U : Subgroup G) (μ : α →₀ ℂ) (W : α → G → ℂ)
    (hW : ∀ a ∈ μ.support, IsRightInvariant U (W a)) :
    IsRightInvariant U (fun x => μ.sum fun a c => c * W a x) := by
  intro g u hu
  simp only [Finsupp.sum]
  exact Finset.sum_congr rfl fun a ha => by rw [hW a ha g u hu]

private theorem isCosetEigenfunction_sum (U : Subgroup G) (gen : G) (lam : ℂ) (μ : α →₀ ℂ) (W : α → G → ℂ)
    (hW : ∀ a ∈ μ.support, IsCosetEigenfunction U gen (W a) lam) :
    IsCosetEigenfunction U gen (fun x => μ.sum fun a c => c * W a x) lam := by
  intro ι _ reps hreps g
  simp only [cosetSum, Finsupp.sum]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have h := hW a ha ι reps hreps g
  simp only [cosetSum] at h
  rw [← Finset.mul_sum, h]
  ring

end Linearity
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.LocalConstituent.LocalStepUnit"

private theorem _root_.LanglandsTunnell.CubicInduction.LocalConstituent.TransportUnit.componentAt3_localToAdelic3_of_ne {p v : HeightOneSpectrum (𝓞 ℚ)} (hpv : p ≠ v) (h : LocalGL3 v) :
    componentAt3 (𝓞 ℚ) ℚ p (localToAdelic3 v h) = 1 := by
  apply Units.ext
  show ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)).mapMatrix
      (finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ v (h : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))) = 1
  have hcomp : ∀ M : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ),
      ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)).mapMatrix M =
        (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p).mapMatrix ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix M) := by
    intro M
    ext i j
    simp [RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [hcomp, mapMatrix_fin_finMatN, mapMatrix_localMatN_of_ne (Fin 3) (𝓞 ℚ) ℚ v _ hpv]

p2m_export "LanglandsTunnell.CubicInduction.LocalConstituent.TransportUnit" "componentAt3_localToAdelic3_of_ne"

private theorem isRightInvariant_and_isCosetEigenfunction_sum_translateRight_smoothingOperator
    (p v : HeightOneSpectrum (𝓞 ℚ)) (_hpv : p ≠ v) (lam1 lam2 : ℂ)
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (_hφ : IsSmoothingKernel φ)
    (_hφp : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, φ g ≠ 0 → componentAt3 (𝓞 ℚ) ℚ p g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (_hc : Continuous f)
    (_hK : IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f)
    (_hT1 : IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen1 p)) f lam1)
    (_hT2 : IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen2 p)) f lam2)
    (μ : LocalGL3 v →₀ ℂ) :
    IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
        (fun x => μ.sum fun h c => c * translateRight (localToAdelic3 v h) (smoothingOperator φ f) x) ∧
      IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) (localToAdelic3 p (heckeGen1 p))
        (fun x => μ.sum fun h c => c * translateRight (localToAdelic3 v h) (smoothingOperator φ f) x) lam1 ∧
      IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) (localToAdelic3 p (heckeGen2 p))
        (fun x => μ.sum fun h c => c * translateRight (localToAdelic3 v h) (smoothingOperator φ f) x) lam2 := by
  have hterm : ∀ h : LocalGL3 v,
      IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
        (translateRight (localToAdelic3 v h) (smoothingOperator φ f)) ∧
      IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) (localToAdelic3 p (heckeGen1 p))
        (translateRight (localToAdelic3 v h) (smoothingOperator φ f)) lam1 ∧
      IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) (localToAdelic3 p (heckeGen2 p))
        (translateRight (localToAdelic3 v h) (smoothingOperator φ f)) lam2 :=
    fun h => isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator p lam1 lam2 φ _hφ _hφp
      (localToAdelic3 v h) (componentAt3_localToAdelic3_of_ne _hpv h) f _hc _hK _hT1 _hT2
  exact ⟨isRightInvariant_sum _ μ (fun h => translateRight (localToAdelic3 v h) (smoothingOperator φ f))
      fun h _ => (hterm h).1,
    isCosetEigenfunction_sum _ _ _ μ (fun h => translateRight (localToAdelic3 v h) (smoothingOperator φ f))
      fun h _ => (hterm h).2.1,
    isCosetEigenfunction_sum _ _ _ μ (fun h => translateRight (localToAdelic3 v h) (smoothingOperator φ f))
      fun h _ => (hterm h).2.2⟩

end TransportUnit
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.LocalConstituent.LocalStepUnit"

end LanglandsTunnell.CubicInduction.LocalConstituent
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.LocalConstituent.LocalStepUnit P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.LocalConstituent"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.LocalConstituent.LocalStepUnit"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.LocalConstituent.LocalStepUnit"

end Interfaces
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.LocalConstituent.LocalStepUnit P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.LocalConstituent"

section LocalDescent

p2m_open "Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory LanglandsTunnell.CubicInduction.SlabL2~exists_isSlabDomain"
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.AdelicGL CubicInduction.globalPointsGL"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "SlabL2.realCoordinate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 LocalGL3 heckeGen1 heckeGen2 cosetSum IsCosetEigenfunction IsRightInvariant archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 one_le_gauge3 one_le_archGauge3 IsModerateGrowth3 matrixFin_ext matrixAdele_ext localMatN localMatN_apply_self localMatN_apply_of_ne mapMatrix_localMatN_self mapMatrix_localMatN_of_ne localEmbedN finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN finEmbedN localToAdelic3 exists_mul_eq_unipotent_mul_diagonal_mul_compact smoothingOperator_mem_cuspFunctions_of_isCuspidalAlong exists_isCompactOperator_cuspidalSubspace_smoothingOperator exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous exists_inner_toL2_translateRight_ne_zero_of_isCosetEigenfunction measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator"
namespace LocalConstituent
p2m_open "LanglandsTunnell.CubicInduction~isCompact_localMaximalCompact3~det_radicalP21~det_radicalP12 LanglandsTunnell~CubicInduction.isCompact_localMaximalCompact3"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private noncomputable def kernelOf (α : (Fin 3 → Fin 3 → ℝ) → ℂ)
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ℂ :=
  α (archEntries g) *
    Set.indicator {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} (fun _ => (1 : ℂ)) g

variable {v}

private theorem componentAt3_mem_of_kernelOf_ne_zero {α : (Fin 3 → Fin 3 → ℝ) → ℂ}
    {K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))} {g : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hg : kernelOf α K' g ≠ 0) (p : HeightOneSpectrum (𝓞 ℚ)) : componentAt3 (𝓞 ℚ) ℚ p g ∈ K' p := by
  by_contra hp
  apply hg
  rw [kernelOf, Set.indicator_of_notMem (fun h : ∀ q, componentAt3 (𝓞 ℚ) ℚ q g ∈ K' q => hp (h p)), mul_zero]

private theorem kernelOf_eq_re_and_nonneg {α : (Fin 3 → Fin 3 → ℝ) → ℂ}
    {K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))}
    (hαr : ∀ m, α m = ((α m).re : ℂ) ∧ 0 ≤ (α m).re) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    kernelOf α K' g = ((kernelOf α K' g).re : ℂ) ∧ 0 ≤ (kernelOf α K' g).re := by
  by_cases hg : g ∈ {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p}
  · rw [kernelOf, Set.indicator_of_mem hg, mul_one]
    exact hαr _
  · rw [kernelOf, Set.indicator_of_notMem hg, mul_zero, Complex.zero_re, Complex.ofReal_zero]
    exact ⟨rfl, le_rfl⟩

private theorem kernelOf_localToAdelic3_mul {α : (Fin 3 → Fin 3 → ℝ) → ℂ}
    {K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))}
    {k : LocalGL3 v} (hk : k ∈ K' v) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    kernelOf α K' (localToAdelic3 v k * g) = kernelOf α K' g := by
  have harch : archEntries (localToAdelic3 v k * g) = archEntries g := by
    show (fun i j => realCoordinate (((archComponent3 (𝓞 ℚ) ℚ (localToAdelic3 v k * g) :
        GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j)) =
      fun i j => realCoordinate (((archComponent3 (𝓞 ℚ) ℚ g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
        Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j)
    rw [map_mul, _root_.LanglandsTunnell.CubicInduction.archComponent3_localToAdelic3 v k, one_mul]
  have hmem : (localToAdelic3 v k * g) ∈ {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} ↔
      g ∈ {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} := by
    simp only [Set.mem_setOf_eq, map_mul]
    refine forall_congr' fun p => ?_
    by_cases hp : p = v
    · subst hp
      rw [_root_.LanglandsTunnell.CubicInduction.componentAt3_localToAdelic3_self]
      exact mul_mem_cancel_left hk
    · rw [_root_.LanglandsTunnell.CubicInduction.componentAt3_localToAdelic3_of_ne v hp k, one_mul]
  rw [kernelOf, kernelOf, harch]
  by_cases hg : g ∈ {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p}
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hmem.2 hg)]
  · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hmem.1 h))]

private theorem smoothingOperator_kernelOf_apply_mul_localToAdelic3 {α : (Fin 3 → Fin 3 → ℝ) → ℂ}
    {K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))}
    {k : LocalGL3 v} (hk : k ∈ K' v) (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    smoothingOperator (kernelOf α K') F (y * localToAdelic3 v k) = smoothingOperator (kernelOf α K') F y := by
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  rw [smoothingOperator_apply, smoothingOperator_apply]
  have h := integral_mul_left_eq_self (μ := NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)
    (fun g => kernelOf α K' ((localToAdelic3 v k)⁻¹ * g) * F (y * g)) (localToAdelic3 v k)
  have h1 : (fun g => kernelOf α K' ((localToAdelic3 v k)⁻¹ * (localToAdelic3 v k * g)) *
      F (y * (localToAdelic3 v k * g))) = fun g => kernelOf α K' g * F (y * localToAdelic3 v k * g) := by
    funext g
    rw [inv_mul_cancel_left, mul_assoc]
  have h2 : (fun g => kernelOf α K' ((localToAdelic3 v k)⁻¹ * g) * F (y * g)) =
      fun g => kernelOf α K' g * F (y * g) := by
    funext g
    rw [← map_inv, kernelOf_localToAdelic3_mul (inv_mem hk)]
  rw [h1, h2] at h
  exact h

private theorem norm_integral_mul_sub_mul_le {X : Type*} [MeasurableSpace X] (μ : Measure X) (φ G : X → ℂ) (c : ℂ)
    (ε : ℝ) (_hε : 0 ≤ ε) (hφr : ∀ x, φ x = ((φ x).re : ℂ) ∧ 0 ≤ (φ x).re) (hφ : Integrable φ μ)
    (hG : Integrable (fun x => φ x * G x) μ) (hb : ∀ x, φ x ≠ 0 → ‖G x - c‖ ≤ ε) :
    ‖(∫ x, φ x * G x ∂μ) - (∫ x, φ x ∂μ) * c‖ ≤ ε * (∫ x, φ x ∂μ).re := by
  have hφc : Integrable (fun x => φ x * c) μ := hφ.mul_const c
  have h1 : (∫ x, φ x * G x ∂μ) - (∫ x, φ x ∂μ) * c = ∫ x, φ x * (G x - c) ∂μ := by
    have hmc : ∫ x, φ x * c ∂μ = (∫ x, φ x ∂μ) * c := integral_mul_const c φ
    rw [← hmc, ← integral_sub hG hφc]
    congr 1
    funext x
    ring
  have hre : Integrable (fun x => ε * (φ x).re) μ := by
    have := hφ.re.const_mul ε
    simpa only [RCLike.re_to_complex] using this
  have h2 : ∫ x, (φ x).re ∂μ = (∫ x, φ x ∂μ).re := by
    have := integral_re (𝕜 := ℂ) hφ
    simpa only [RCLike.re_to_complex] using this
  rw [h1]
  refine (norm_integral_le_of_norm_le hre (Filter.Eventually.of_forall fun x => ?_)).trans ?_
  · rw [norm_mul]
    by_cases h0 : φ x = 0
    · simp [h0]
    · have hn : ‖φ x‖ = (φ x).re := by
        conv_lhs => rw [(hφr x).1]
        rw [Complex.norm_real, Real.norm_of_nonneg (hφr x).2]
      rw [hn, mul_comm ε]
      exact mul_le_mul_of_nonneg_left (hb x h0) (hφr x).2
  · have hcm : ∫ x, ε * (φ x).re ∂μ = ε * ∫ x, (φ x).re ∂μ := integral_const_mul ε fun x => (φ x).re
    rw [hcm, h2]

private theorem norm_smoothingOperator_sub_mul_le {α : (Fin 3 → Fin 3 → ℝ) → ℂ}
    {K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))}
    (hα : IsSmoothArchFactor α)
    (hK' : ∀ p, IsOpen (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))) ∧
      IsCompact (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))))
    (hK'e : ∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p)
    (hαr : ∀ m, α m = ((α m).re : ℂ) ∧ 0 ≤ (α m).re)
    {f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hf : Continuous f) (hfix : ∀ k ∈ K' v, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      f (g * localToAdelic3 v k) = f g)
    (x : AdelicGL 3 (𝓞 ℚ) ℚ) {ε : ℝ} (hε : 0 ≤ ε)
    (hN : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, kernelOf α K' g ≠ 0 →
      ‖f (x * (g * (localToAdelic3 v (componentAt3 (𝓞 ℚ) ℚ v g))⁻¹)) - f x‖ ≤ ε) :
    ‖smoothingOperator (kernelOf α K') f x -
        (∫ g, kernelOf α K' g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)) * f x‖ ≤
      ε * (∫ g, kernelOf α K' g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)).re := by
  have hφ : IsSmoothingKernel (kernelOf α K') := ⟨α, K', hα, hK', hK'e, fun _ => rfl⟩
  rw [smoothingOperator_apply]
  refine norm_integral_mul_sub_mul_le _ (kernelOf α K') (fun g => f (x * g)) (f x) ε hε
    (kernelOf_eq_re_and_nonneg hαr) (integrable_of_isSmoothingKernel hφ) ?_ fun g hg => ?_
  · haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
    exact ((continuous_of_isSmoothingKernel hφ).mul (hf.comp (continuous_const.mul continuous_id))
      ).integrable_of_hasCompactSupport ((hasCompactSupport_of_isSmoothingKernel hφ).mul_right)
  · have hgv : componentAt3 (𝓞 ℚ) ℚ v g ∈ K' v := componentAt3_mem_of_kernelOf_ne_zero hg v
    have hxg : f (x * g) = f (x * (g * (localToAdelic3 v (componentAt3 (𝓞 ℚ) ℚ v g))⁻¹)) := by
      rw [← hfix _ hgv (x * (g * (localToAdelic3 v (componentAt3 (𝓞 ℚ) ℚ v g))⁻¹)), mul_assoc,
        inv_mul_cancel_right]
    show ‖f (x * g) - f x‖ ≤ ε
    rw [hxg]
    exact hN g hg

private theorem sum_mul_apply_mul_localToAdelic3_eq_zero {f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hc : Continuous f)
    {Kf : Subgroup (LocalGL3 v)} (hKfo : IsOpen (Kf : Set (LocalGL3 v))) (hKfc : IsCompact (Kf : Set (LocalGL3 v)))
    (hKfU : ∀ k ∈ Kf, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, f (g * localToAdelic3 v k) = f g) (μ : LocalGL3 v →₀ ℂ)
    (hvan : ∀ (α : (Fin 3 → Fin 3 → ℝ) → ℂ)
      (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))),
      IsSmoothArchFactor α →
      (∀ p, IsOpen (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))) ∧
        IsCompact (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ)))) →
      (∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) → K' v = Kf →
      (fun x => ∑ h ∈ μ.support, μ h * smoothingOperator (kernelOf α K') f (x * localToAdelic3 v h)) = 0)
    (x : AdelicGL 3 (𝓞 ℚ) ℚ) : (∑ h ∈ μ.support, μ h * f (x * localToAdelic3 v h)) = 0 := by

  have hbound : ∀ ε : ℝ, 0 < ε → ‖∑ h ∈ μ.support, μ h * f (x * localToAdelic3 v h)‖ ≤ ε * ∑ h ∈ μ.support, ‖μ h‖ := by
    intro ε hε

    obtain ⟨N, hNdef⟩ : ∃ N : Set (AdelicGL 3 (𝓞 ℚ) ℚ),
        N = ⋂ h ∈ μ.support, {y | ‖f (x * localToAdelic3 v h * y) - f (x * localToAdelic3 v h)‖ < ε} := ⟨_, rfl⟩
    have hN : N ∈ nhds (1 : AdelicGL 3 (𝓞 ℚ) ℚ) := by
      rw [hNdef, Filter.biInter_finset_mem]
      intro h _
      refine IsOpen.mem_nhds (isOpen_lt ?_ continuous_const) ?_
      · exact continuous_norm.comp ((hc.comp (continuous_const.mul continuous_id)).sub continuous_const)
      · simp only [Set.mem_setOf_eq, mul_one, sub_self, norm_zero]
        exact hε
    obtain ⟨α, K', hα, hK', hK'e, hK'v, hαr, hmass, hsupp⟩ :=
      exists_isSmoothArchFactor_and_level_eq_of_mem_nhds v Kf hKfo hKfc N hN
    have hφK : IsSmoothingKernel (kernelOf α K') := ⟨α, K', hα, hK', hK'e, fun _ => rfl⟩
    obtain ⟨m, hmdef⟩ : ∃ m : ℂ, (∫ g, kernelOf α K' g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)) = m :=
      ⟨_, rfl⟩
    have hre :
        (∫ g, ((kernelOf α K' g).re : ℝ) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)) =
          (∫ g, kernelOf α K' g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)).re := by
      have := integral_re (𝕜 := ℂ) (integrable_of_isSmoothingKernel hφK)
      simpa only [RCLike.re_to_complex] using this
    have hm : 0 < m.re := by
      rw [← hmdef, ← hre]
      exact hmass

    have hz : (∑ h ∈ μ.support, μ h * smoothingOperator (kernelOf α K') f (x * localToAdelic3 v h)) =
        0 := by
      have := congrFun (hvan α K' hα hK' hK'e hK'v) x
      rwa [Pi.zero_apply] at this

    have hest : ∀ h ∈ μ.support,
        ‖smoothingOperator (kernelOf α K') f (x * localToAdelic3 v h) - m * f (x * localToAdelic3 v h)‖ ≤ ε * m.re := by
      intro h hh
      rw [← hmdef]
      refine norm_smoothingOperator_sub_mul_le hα hK' hK'e hαr hc
        (fun k hk g => hKfU k (by rw [← hK'v]; exact hk) g) _ hε.le fun g hg => le_of_lt ?_
      have hgN := hsupp g hg
      rw [hNdef] at hgN
      exact Set.mem_iInter₂.1 hgN h hh

    have hsum : m * ∑ h ∈ μ.support, μ h * f (x * localToAdelic3 v h) =
        ∑ h ∈ μ.support, μ h * (m * f (x * localToAdelic3 v h) -
          smoothingOperator (kernelOf α K') f (x * localToAdelic3 v h)) := by
      rw [Finset.mul_sum]
      have : ∑ h ∈ μ.support, μ h * (m * f (x * localToAdelic3 v h) -
          smoothingOperator (kernelOf α K') f (x * localToAdelic3 v h)) =
          ∑ h ∈ μ.support, m * (μ h * f (x * localToAdelic3 v h)) -
            ∑ h ∈ μ.support, μ h * smoothingOperator (kernelOf α K') f (x * localToAdelic3 v h) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun h _ => by ring
      rw [this, hz, sub_zero]
    have hnorm : ‖m * ∑ h ∈ μ.support, μ h * f (x * localToAdelic3 v h)‖ ≤ (∑ h ∈ μ.support, ‖μ h‖) * (ε * m.re) := by
      rw [hsum, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h hh => ?_)
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [← norm_neg, neg_sub]
      exact hest h hh
    have hmn : m.re ≤ ‖m‖ := Complex.re_le_norm m
    have hm0 : 0 < ‖m‖ := hm.trans_le hmn
    have hC : 0 ≤ ∑ h ∈ μ.support, ‖μ h‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have h2 : (∑ h ∈ μ.support, ‖μ h‖) * (ε * m.re) ≤ ‖m‖ * (ε * ∑ h ∈ μ.support, ‖μ h‖) :=
      calc (∑ h ∈ μ.support, ‖μ h‖) * (ε * m.re) = ε * (∑ h ∈ μ.support, ‖μ h‖) * m.re := by ring
        _ ≤ ε * (∑ h ∈ μ.support, ‖μ h‖) * ‖m‖ := mul_le_mul_of_nonneg_left hmn (mul_nonneg hε.le hC)
        _ = ‖m‖ * (ε * ∑ h ∈ μ.support, ‖μ h‖) := by ring
    rw [norm_mul] at hnorm
    exact le_of_mul_le_mul_left (hnorm.trans h2) hm0

  by_contra hne0
  have hpos : 0 < ‖∑ h ∈ μ.support, μ h * f (x * localToAdelic3 v h)‖ := norm_pos_iff.2 hne0
  have hC : 0 ≤ ∑ h ∈ μ.support, ‖μ h‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h := hbound (‖∑ h ∈ μ.support, μ h * f (x * localToAdelic3 v h)‖ / (2 * (∑ h ∈ μ.support, ‖μ h‖ + 1)))
    (div_pos hpos (by positivity))
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at h
  nlinarith [mul_nonneg hpos.le hC]

section ClassIdentities

variable {ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ} {a b : ℝ} {Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)}

private theorem rbar_cuspClass_eq_self (hR : CuspClassAction.RightTranslationLaw ω a b Φ₀) {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hF : F ∈ cuspFunctions ω a b Φ₀) {g : AdelicGL 3 (𝓞 ℚ) ℚ} (h : ∀ y, F (y * g) = F y) :
    CuspClassAction.rbar hR g (CuspClassAction.cuspClass hF) = CuspClassAction.cuspClass hF := by
  apply Subtype.ext
  show ((CuspClassAction.rbar hR g ⟨toL2 ω a b Φ₀ ⟨F, hF.1⟩,
      toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hF⟩ : ↥(cuspidalSubspace ω a b Φ₀)) : Carrier a b Φ₀) =
    toL2 ω a b Φ₀ ⟨F, hF.1⟩
  rw [CuspClassAction.rbar_toL2 hR g F hF]
  congr 1
  apply Subtype.ext
  funext y
  exact h y

private theorem
    sum_rbar_cuspClass_eq_smul (hR : CuspClassAction.RightTranslationLaw ω a b Φ₀) {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hF : F ∈ cuspFunctions ω a b Φ₀) {ι : Type} [Fintype ι] (reps : ι → AdelicGL 3 (𝓞 ℚ) ℚ) (lam : ℂ)
    (h : ∀ y, cosetSum reps F y = lam * F y) :
    ∑ i, CuspClassAction.rbar hR (reps i) (CuspClassAction.cuspClass hF) = lam • CuspClassAction.cuspClass hF := by
  have hlam : (fun y => lam * F y) ∈ cuspFunctions ω a b Φ₀ := (CuspClassAction.cuspSubmodule ω a b Φ₀).smul_mem lam hF
  have hL : (∑ i, (⟨translateRight (reps i) F, ((hR F hF).fst (reps i)).1⟩ : ↥(automorphicSubmodule ω a b Φ₀))) =
      ⟨fun y => lam * F y, hlam.1⟩ := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    funext y
    show (∑ i, ((⟨translateRight (reps i) F, ((hR F hF).fst (reps i)).1⟩ : ↥(automorphicSubmodule ω a b Φ₀)) :
        AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) y = lam * F y
    rw [Finset.sum_apply, ← h y]
    rfl
  have hRHS : (⟨fun y => lam * F y, hlam.1⟩ : ↥(automorphicSubmodule ω a b Φ₀)) = lam • ⟨F, hF.1⟩ :=
    Subtype.ext rfl
  apply Subtype.ext
  rw [Submodule.coe_sum, Submodule.coe_smul, CuspClassAction.coe_cuspClass hF]
  simp_rw [CuspClassAction.cuspClass, CuspClassAction.rbar_toL2 hR _ F hF]
  rw [← map_sum, hL, hRHS, map_smul]

private theorem
    sum_smul_rbar_cuspClass_eq (hR : CuspClassAction.RightTranslationLaw ω a b Φ₀) {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hF : F ∈ cuspFunctions ω a b Φ₀) {ι : Type} (s : Finset ι) (c : ι → ℂ) (g : ι → AdelicGL 3 (𝓞 ℚ) ℚ)
    (hG : (fun x => ∑ i ∈ s, c i * F (x * g i)) ∈ cuspFunctions ω a b Φ₀) :
    ∑ i ∈ s, c i • CuspClassAction.rbar hR (g i) (CuspClassAction.cuspClass hF) = CuspClassAction.cuspClass hG := by
  have hL : (⟨fun x => ∑ i ∈ s, c i * F (x * g i), hG.1⟩ : ↥(automorphicSubmodule ω a b Φ₀)) =
      ∑ i ∈ s, c i • ⟨translateRight (g i) F, ((hR F hF).fst (g i)).1⟩ := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    funext x
    show (∑ i ∈ s, c i * F (x * g i)) = (∑ i ∈ s, ((c i • ⟨translateRight (g i) F, ((hR F hF).fst (g i)).1⟩ :
        ↥(automorphicSubmodule ω a b Φ₀)) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) x
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => rfl
  apply Subtype.ext
  rw [Submodule.coe_sum, CuspClassAction.coe_cuspClass hG]
  simp_rw [Submodule.coe_smul, CuspClassAction.cuspClass, CuspClassAction.rbar_toL2 hR _ F hF]
  rw [hL, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]

private theorem sum_mul_apply_mul_mem_cuspFunctions (hR : CuspClassAction.RightTranslationLaw ω a b Φ₀)
    {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : F ∈ cuspFunctions ω a b Φ₀) {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (g : ι → AdelicGL 3 (𝓞 ℚ) ℚ) : (fun x => ∑ i ∈ s, c i * F (x * g i)) ∈ cuspFunctions ω a b Φ₀ := by
  have heq : (fun x => ∑ i ∈ s, c i * F (x * g i)) = ∑ i ∈ s, c i • translateRight (g i) F := by
    funext x
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => rfl
  rw [heq]
  exact (CuspClassAction.cuspSubmodule ω a b Φ₀).sum_mem fun i _ =>
    (CuspClassAction.cuspSubmodule ω a b Φ₀).smul_mem _ ((hR F hF).fst (g i))

end ClassIdentities
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.LocalConstituent.LocalStepUnit P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.LocalConstituent"

end LanglandsTunnell.CubicInduction.LocalConstituent
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.LocalConstituent.LocalStepUnit P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.LocalConstituent"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.LocalConstituent.LocalStepUnit P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.LocalConstituent"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.LocalConstituent.LocalStepUnit P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.LocalConstituent"

end LocalDescent
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.AdelicSigmaCompact P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.AdelicCountability P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.LocalConstituent.LocalStepUnit P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction.LocalConstituent"

p2m_open "Matrix IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction.SlabL2~exists_isSlabDomain"
open FLT.SmoothAdmissibleSchurCommutant
open scoped InnerProductSpace

universe v w

namespace LanglandsTunnell p2m_export "LanglandsTunnell" "CubicInduction.AdelicGL CubicInduction.globalPointsGL" namespace CubicInduction p2m_export "LanglandsTunnell.CubicInduction" "SlabL2.realCoordinate AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 LocalGL3 heckeGen1 heckeGen2 cosetSum IsCosetEigenfunction IsRightInvariant archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 one_le_gauge3 one_le_archGauge3 IsModerateGrowth3 matrixFin_ext matrixAdele_ext localMatN localMatN_apply_self localMatN_apply_of_ne mapMatrix_localMatN_self mapMatrix_localMatN_of_ne localEmbedN finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN finEmbedN localToAdelic3 exists_mul_eq_unipotent_mul_diagonal_mul_compact smoothingOperator_mem_cuspFunctions_of_isCuspidalAlong exists_isCompactOperator_cuspidalSubspace_smoothingOperator exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous exists_inner_toL2_translateRight_ne_zero_of_isCosetEigenfunction measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator" namespace Level2 end LanglandsTunnell.CubicInduction.Level2
p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.Level2.standinSolution_of_norm_eq_one
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (lam1 lam2 : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (_hc : Continuous f)
    (_haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g)
    (_hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g)
    (_hmg : IsModerateGrowth3 ℚ f)
    (_hP21 : IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f)
    (_hP12 : IsCuspidalAlongP12 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f)
    (_hK : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f)
    (_hT1 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen1 p)) f (lam1 p))
    (_hT2 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen2 p)) f (lam2 p))
    (v : HeightOneSpectrum (𝓞 ℚ))
    (_hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, f (g * localToAdelic3 v k) = f g)
    (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1) :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Module ℂ E) (πE : LocalGL3 v →* Module.End ℂ E),
      IsIrreducibleRep πE ∧ IsSmoothRep πE ∧ IsAdmissibleRep πE ∧
        ∃ (d : ℕ) (e : Fin d → E), ∀ μ : LocalGL3 v →₀ ℂ,
          (∀ j : Fin d, (μ.sum fun (h : LocalGL3 v) (c : ℂ) => c • πE h (e j)) = 0) →
            (μ.sum fun (h : LocalGL3 v) (c : ℂ) =>
              c • fun g : AdelicGL 3 (𝓞 ℚ) ℚ => f (g * localToAdelic3 v h)) = 0 := by
  classical

  obtain ⟨Φ₀, hΦ₀⟩ : ∃ Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsSlabDomain 1 8 Φ₀ := L2Witness.exists_isSlabDomain

  have hW1 : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ →
      smoothingOperator φ f ∈ cuspFunctions ω 1 8 Φ₀ := fun φ hφ =>
    smoothingOperator_mem_cuspFunctions_of_isCuspidalAlong ω 1 8 Φ₀ hΦ₀
      exists_mul_eq_unipotent_mul_diagonal_mul_compact f _hc _haut _hcen _hmg _hP21 _hP12 φ hφ

  have hW2 := fun (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : IsSmoothingKernel φ) =>
    exists_isCompactOperator_cuspidalSubspace_smoothingOperator ω 1 8 Φ₀ hΦ₀
      exists_mul_eq_unipotent_mul_diagonal_mul_compact φ hφ

  have hIso := fun (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω 1 8 Φ₀) =>
    exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous ω hω 1 8 Φ₀ hΦ₀ F hF

  have hR : CuspClassAction.RightTranslationLaw ω 1 8 Φ₀ := fun F hF => hIso F hF
  have hS : CuspClassAction.HasApproximateIdentity := fun U hU => hasApproximateIdentity U hU
  have hI : CuspClassAction.SlabInvarianceLaw 1 8 := fun γ =>
    measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc 1 8 γ
  have hSK : CuspClassAction.SmoothingKernelLaw := fun φ hφ =>
    ⟨continuous_of_isSmoothingKernel hφ, hasCompactSupport_of_isSmoothingKernel hφ⟩
  have hφi : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → Continuous φ ∧ HasCompactSupport φ ∧
      MeasureTheory.Integrable φ (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := fun φ hφ =>
    ⟨continuous_of_isSmoothingKernel hφ, hasCompactSupport_of_isSmoothingKernel hφ, integrable_of_isSmoothingKernel hφ⟩
  have hXw : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → CuspClassAction.WeakInterchangeLaw ω 1 8 Φ₀ φ := by
    intro φ hφ F hF hmem hRF h
    obtain ⟨hmem', hiso, -⟩ := hIso F hF
    exact inner_toL2_smoothingOperator_eq_integral_of_norm_eq ω 1 8 Φ₀ hΦ₀ φ hφ (continuous_of_isSmoothingKernel hφ)
      (integrable_of_isSmoothingKernel hφ) F hF hmem (fun g => hiso g) hRF h

  have hT : ∃ T : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (↥(cuspidalSubspace ω 1 8 Φ₀) →L[ℂ] ↥(cuspidalSubspace ω 1 8 Φ₀)),
      ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ →
        IsCompactOperator (T φ) ∧ CuspClassAction.AgreesWithSmoothing ω 1 8 Φ₀ φ (T φ) := by
    refine ⟨fun φ => if hφ : IsSmoothingKernel φ then (hW2 φ hφ).choose else 0, fun φ hφ => ?_⟩
    simp only [dif_pos hφ]
    exact (hW2 φ hφ).choose_spec
  obtain ⟨T, hT⟩ := hT
  set R : AdelicGL 3 (𝓞 ℚ) ℚ →* (↥(cuspidalSubspace ω 1 8 Φ₀) →L[ℂ] ↥(cuspidalSubspace ω 1 8 Φ₀)) :=
    (CuspClassAction.isDenseIsometricAction hR).hom
  have hRr : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (x : ↥(cuspidalSubspace ω 1 8 Φ₀)), R g x = CuspClassAction.rbar hR g x :=
    fun _ _ => rfl
  have hRn : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (x : ↥(cuspidalSubspace ω 1 8 Φ₀)), ‖R g x‖ = ‖x‖ := fun g x =>
    CuspClassAction.norm_rbar hR g x
  have hRc : ∀ x : ↥(cuspidalSubspace ω 1 8 Φ₀), Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => R g x := fun x =>
    CuspClassAction.continuous_rbar_apply hR x
  have hTw : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → ∀ h c : ↥(cuspidalSubspace ω 1 8 Φ₀),
      ⟪h, T φ c⟫_ℂ = ∫ g, φ g * ⟪h, R g c⟫_ℂ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
    intro φ hφ h c
    rw [Submodule.coe_inner, CuspClassAction.inner_apply_eq_integral hR (hXw φ hφ) (hφi φ hφ).2.2 (hT φ hφ).2]
    simp only [hRr, Submodule.coe_inner]
  have hTk : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → IsCompactOperator (T φ) := fun φ hφ => (hT φ hφ).1

  have hTmem : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → ∀ W : Submodule ℂ ↥(cuspidalSubspace ω 1 8 Φ₀),
      IsClosed (W : Set ↥(cuspidalSubspace ω 1 8 Φ₀)) →
      (∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (x : ↥(cuspidalSubspace ω 1 8 Φ₀)), x ∈ W → CuspClassAction.rbar hR g x ∈ W) →
      ∀ x ∈ W, T φ x ∈ W := fun φ hφ W hWc hWi x hx =>
    CuspClassAction.apply_mem_of_forall_rbar_apply_mem hR (hXw φ hφ) (hφi φ hφ).2.2 (hT φ hφ).2 hWc hWi hx
  have hRadj : HilbertConstituent.IsAdjointClosed (Set.range (CuspClassAction.rbar hR)) := fun r hr =>
    CuspClassAction.adjoint_mem_range_rbar hR hr

  by_cases hf0 : f = 0
  · obtain ⟨E, iE, mE, πE, hirr, hsmE, hadm⟩ :=
      Twist.exists_isIrreducibleRep_isSmoothRep_isAdmissibleRep (LocalGL3 v)
    refine ⟨E, iE, mE, πE, hirr, hsmE, hadm, 0, Fin.elim0, fun μ _ => ?_⟩
    subst hf0
    rw [Finsupp.sum]
    refine Finset.sum_eq_zero fun h _ => ?_
    funext g
    simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_zero]
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, f g₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hf0 (funext h)

  obtain ⟨φ₀, hφ₀, hne⟩ := CuspClassAction.exists_isSmoothingKernel_smoothingOperator_apply_ne_zero hS hSK _hc hg₀
  obtain ⟨α₀, K₀', hα₀, hK₀', hK₀'e, hφ₀eq⟩ := id hφ₀
  have hF₀ : smoothingOperator φ₀ f ∈ cuspFunctions ω 1 8 Φ₀ := hW1 φ₀ hφ₀
  have hc₀ : CuspClassAction.cuspClass hF₀ ≠ 0 := fun h0 =>
    CuspClassAction.toL2_ne_zero_of_ne_zero hΦ₀ hI hF₀ (fun h => hne (by rw [h, Pi.zero_apply]))
      (by rw [← CuspClassAction.coe_cuspClass hF₀, h0, Submodule.coe_zero])

  have hA : ∀ W : Submodule ℂ ↥(cuspidalSubspace ω 1 8 Φ₀), IsClosed (W : Set ↥(cuspidalSubspace ω 1 8 Φ₀)) →
      HilbertConstituent.IsInvariant (Set.range (CuspClassAction.rbar hR)) W → W ≠ ⊥ →
      ∃ A : ↥(cuspidalSubspace ω 1 8 Φ₀) →L[ℂ] ↥(cuspidalSubspace ω 1 8 Φ₀), IsCompactOperator A ∧
        (∀ W' : Submodule ℂ ↥(cuspidalSubspace ω 1 8 Φ₀), IsClosed (W' : Set ↥(cuspidalSubspace ω 1 8 Φ₀)) →
          HilbertConstituent.IsInvariant (Set.range (CuspClassAction.rbar hR)) W' → ∀ x ∈ W', A x ∈ W') ∧
        ∃ x ∈ W, A x ≠ 0 := by
    intro W _ _ hW0
    obtain ⟨x, hxW, hx0⟩ := (Submodule.ne_bot_iff W).1 hW0
    obtain ⟨φ, hφ, -, hφT⟩ := CuspClassAction.exists_isSmoothingKernel_forall_apply_ne_zero hR hS hx0
    exact ⟨T φ, hTk φ hφ, fun W' hW'c hW'i y hy => hTmem φ hφ W' hW'c (fun g z hz => hW'i _ ⟨g, rfl⟩ z hz) y hy,
      x, hxW, hφT (T φ) (hT φ hφ).2 (hXw φ hφ)⟩
  obtain ⟨V, hV, hc₀V⟩ := HilbertConstituent.exists_isIrreducible_not_mem_orthogonal hRadj hA hc₀
  haveI : CompleteSpace V := hV.1.isComplete.completeSpace_coe
  have hVR : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (x : ↥(cuspidalSubspace ω 1 8 Φ₀)), x ∈ V → R g x ∈ V :=
    fun g x hx => hV.2.1 _ ⟨g, rfl⟩ x hx
  have hVirr : ∀ W : Submodule ℂ ↥(cuspidalSubspace ω 1 8 Φ₀), IsClosed (W : Set ↥(cuspidalSubspace ω 1 8 Φ₀)) →
      (∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (x : ↥(cuspidalSubspace ω 1 8 Φ₀)), x ∈ W → R g x ∈ W) → W ≤ V →
      W = ⊥ ∨ W = V := fun W hWc hWR hWV =>
    hV.2.2.2 W hWc (fun r hr x hx => by obtain ⟨g, rfl⟩ := hr; exact hWR g x hx) hWV
  have hPcomm : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (y : ↥(cuspidalSubspace ω 1 8 Φ₀)),
      V.starProjection (CuspClassAction.rbar hR g y) = CuspClassAction.rbar hR g (V.starProjection y) :=
    fun g y => HilbertConstituent.starProjection_apply_comm hRadj hV.2.1 ⟨g, rfl⟩ y
  have hPT : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → ∀ y : ↥(cuspidalSubspace ω 1 8 Φ₀),
      V.starProjection (T φ y) = T φ (V.starProjection y) := fun φ hφ y =>
    CuspClassAction.apply_comm_of_forall_rbar_comm hR (hXw φ hφ) (hφi φ hφ).2.2 (hT φ hφ).2 V.starProjection
      (fun a b => Submodule.inner_starProjection_left_eq_right V a b) hPcomm y
  set x₀ : ↥(cuspidalSubspace ω 1 8 Φ₀) := V.starProjection (CuspClassAction.cuspClass hF₀) with hx₀def
  have hx₀V : x₀ ∈ V := Submodule.starProjection_apply_mem V _
  have hx₀0 : x₀ ≠ 0 := fun h0 => hc₀V (by
    have h := Submodule.sub_starProjection_mem_orthogonal (K := V) (CuspClassAction.cuspClass hF₀)
    rwa [← hx₀def, h0, sub_zero] at h)

  have hfixed : ∀ (α : (Fin 3 → Fin 3 → ℝ) → ℂ)
      (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ)))
      (hRF : smoothingOperator (LocalConstituent.kernelOf α K') f ∈ cuspFunctions ω 1 8 Φ₀),
      ∀ k ∈ K' v, CuspClassAction.rbar hR (localToAdelic3 v k) (CuspClassAction.cuspClass hRF) =
        CuspClassAction.cuspClass hRF := fun α K' hRF k hk =>
    LocalConstituent.rbar_cuspClass_eq_self hR hRF fun y =>
      LocalConstituent.smoothingOperator_kernelOf_apply_mul_localToAdelic3 hk f y
  have hx₀K : ∀ k ∈ K₀' v, R (localToAdelic3 v k) x₀ = x₀ := by
    intro k hk
    have hF₀' : smoothingOperator (LocalConstituent.kernelOf α₀ K₀') f ∈ cuspFunctions ω 1 8 Φ₀ := by
      have : LocalConstituent.kernelOf α₀ K₀' = φ₀ := funext fun g => (hφ₀eq g).symm
      rw [this]
      exact hF₀
    have hcl : CuspClassAction.cuspClass hF₀ = CuspClassAction.cuspClass hF₀' := by
      apply Subtype.ext
      rw [CuspClassAction.coe_cuspClass, CuspClassAction.coe_cuspClass]
      congr 1
      apply Subtype.ext
      exact congrArg (fun φ => smoothingOperator φ f) (funext hφ₀eq)
    rw [hRr, hx₀def, ← hPcomm, hcl, hfixed α₀ K₀' hF₀' k hk]

  obtain ⟨E, iE, mE, πE, hirr, hsmE, hadm, hloc⟩ :=
    LocalConstituent.LocalStepUnit.exists_isIrreducibleRep_forall_sum_smul_mem_orthogonal R hRn hRc T hTw hTk hφi hS v
      V hV.1
      hVR hVirr x₀ hx₀V hx₀0 (K₀' v) (hK₀' v).2 (hK₀' v).1 hx₀K

  obtain ⟨Uv, hUo, hUf⟩ := _hsm
  set Kf : Subgroup (LocalGL3 v) := Uv ⊓ localMaximalCompact3 (𝓞 ℚ) ℚ v with hKf
  have hKfo : IsOpen (Kf : Set (LocalGL3 v)) := by
    rw [hKf, Subgroup.coe_inf]
    exact hUo.inter (isOpen_localMaximalCompact3 v)
  have hKfc : IsCompact (Kf : Set (LocalGL3 v)) := by
    rw [hKf, Subgroup.coe_inf]
    exact (isCompact_localMaximalCompact3 v).inter_left (Subgroup.isClosed_of_isOpen Uv hUo)
  have hKfU : ∀ k ∈ Kf, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, f (g * localToAdelic3 v k) = f g := fun k hk g =>
    hUf k (Subgroup.mem_inf.1 hk).1 g
  obtain ⟨d, e, hde⟩ := hloc Kf hKfc hKfo
  refine ⟨E, iE, mE, πE, hirr, hsmE, hadm, d, e, fun μ hμ => ?_⟩

  obtain ⟨θ, hθ, -, hθT⟩ := CuspClassAction.exists_isSmoothingKernel_forall_apply_ne_zero hR hS hx₀0
  obtain ⟨αθ, Kθ', hαθ, hKθ', hKθ'e, hθeq⟩ := id hθ
  have hu0 : T θ x₀ ≠ 0 := hθT (T θ) (hT θ hθ).2 (hXw θ hθ)
  have huV : T θ x₀ ∈ V := hTmem θ hθ V hV.1 (fun g x hx => hVR g x hx) x₀ hx₀V
  obtain ⟨hF₂, hTc₀⟩ := (hT θ hθ).2 (smoothingOperator φ₀ f) hF₀
  have hu : T θ x₀ = V.starProjection (CuspClassAction.cuspClass hF₂) := by
    rw [hx₀def, ← hPT θ hθ]
    congr 1
    exact Subtype.ext hTc₀
  obtain ⟨CN, hRD⟩ := exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace ω hω 1 8 Φ₀ hΦ₀ θ hθ
    (T θ) (hT θ hθ).2
  obtain ⟨F', hF', hF'eq, -⟩ := hRD x₀
  have huF' : T θ x₀ = CuspClassAction.cuspClass hF' := Subtype.ext hF'eq

  have hmax : ∀ (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (α : (Fin 3 → Fin 3 → ℝ) → ℂ)
      (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))),
      (∀ g, φ g = α (archEntries g) *
        Set.indicator {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} (fun _ => (1 : ℂ)) g) →
      ∀ p, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p →
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, φ g ≠ 0 → componentAt3 (𝓞 ℚ) ℚ p g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p := by
    intro φ α K' hφeq p hp g hg
    rw [← hp]
    rw [hφeq] at hg
    exact LocalConstituent.componentAt3_mem_of_kernelOf_ne_zero (α := α) (K' := K') (g := g) hg p
  have hdata₂ : ∀ p, p ∉ S → K₀' p = localMaximalCompact3 (𝓞 ℚ) ℚ p → Kθ' p = localMaximalCompact3 (𝓞 ℚ) ℚ p →
      IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
          (smoothingOperator θ (smoothingOperator φ₀ f)) ∧
        IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
          (localToAdelic3 p (heckeGen1 p)) (smoothingOperator θ (smoothingOperator φ₀ f)) (lam1 p) ∧
        IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
          (localToAdelic3 p (heckeGen2 p)) (smoothingOperator θ (smoothingOperator φ₀ f)) (lam2 p) := by
    intro p hp h0 hθp
    have h1 := isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator p (lam1 p) (lam2 p) φ₀ hφ₀
      (hmax φ₀ α₀ K₀' hφ₀eq p h0) 1 (map_one _) f _hc (_hK p hp) (_hT1 p hp) (_hT2 p hp)
    rw [translateRight_one] at h1
    have h2 := isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator p (lam1 p) (lam2 p) θ hθ
      (hmax θ αθ Kθ' hθeq p hθp) 1 (map_one _) (smoothingOperator φ₀ f) hF₀.2.1 h1.1 h1.2.1 h1.2.2
    rwa [translateRight_one] at h2

  have hdata' : ∀ p, p ∉ S → K₀' p = localMaximalCompact3 (𝓞 ℚ) ℚ p → Kθ' p = localMaximalCompact3 (𝓞 ℚ) ℚ p →
      IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) F' ∧
        IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
          (localToAdelic3 p (heckeGen1 p)) F' (lam1 p) ∧
        IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
          (localToAdelic3 p (heckeGen2 p)) F' (lam2 p) := by
    intro p hp h0 hθp
    obtain ⟨hK₂, hT₂1, hT₂2⟩ := hdata₂ p hp h0 hθp

    have hinv : ∀ k ∈ (localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p),
        CuspClassAction.rbar hR k (CuspClassAction.cuspClass hF') = CuspClassAction.cuspClass hF' := by
      intro k hk
      rw [← huF', hu, ← hPcomm, LocalConstituent.rbar_cuspClass_eq_self hR hF₂ fun y => hK₂ y k hk]
    have heig : ∀ {ι : Type} [Fintype ι] (reps : ι → AdelicGL 3 (𝓞 ℚ) ℚ) (lam : ℂ),
        (∀ g, cosetSum reps (smoothingOperator θ (smoothingOperator φ₀ f)) g =
          lam * smoothingOperator θ (smoothingOperator φ₀ f) g) →
        ∑ i, CuspClassAction.rbar hR (reps i) (CuspClassAction.cuspClass hF') =
          lam • CuspClassAction.cuspClass hF' := by
      intro ι _ reps lam hfun
      rw [← huF', hu]
      simp only [← hPcomm]
      rw [← map_sum, LocalConstituent.sum_rbar_cuspClass_eq_smul hR hF₂ reps lam hfun, map_smul]
    refine ⟨CuspClassAction.isRightInvariant_of_forall_rbar_eq hΦ₀ hI hR hF' _ hinv, ?_, ?_⟩
    · intro ι _ reps hreps g
      exact congrFun (CuspClassAction.cosetSum_eq_of_sum_rbar_eq hΦ₀ hI hR hF' reps (lam1 p)
        (heig reps (lam1 p) (hT₂1 ι reps hreps))) g
    · intro ι _ reps hreps g
      exact congrFun (CuspClassAction.cosetSum_eq_of_sum_rbar_eq hΦ₀ hI hR hF' reps (lam2 p)
        (heig reps (lam2 p) (hT₂2 ι reps hreps))) g

  have hvan : ∀ (α : (Fin 3 → Fin 3 → ℝ) → ℂ)
      (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))),
      IsSmoothArchFactor α →
      (∀ p, IsOpen (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))) ∧
        IsCompact (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ)))) →
      (∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) → K' v = Kf →
      (fun x => ∑ h ∈ μ.support, μ h * smoothingOperator (LocalConstituent.kernelOf α K') f (x * localToAdelic3 v h)) =
        0 := by
    intro α K' hα hK' hK'e hK'v
    have hφ : IsSmoothingKernel (LocalConstituent.kernelOf α K') := ⟨α, K', hα, hK', hK'e, fun _ => rfl⟩
    have hRF : smoothingOperator (LocalConstituent.kernelOf α K') f ∈ cuspFunctions ω 1 8 Φ₀ := hW1 _ hφ

    have hG := LocalConstituent.sum_mul_apply_mul_mem_cuspFunctions hR hRF μ.support μ (localToAdelic3 v)
    have hcl := LocalConstituent.sum_smul_rbar_cuspClass_eq hR hRF μ.support μ (localToAdelic3 v) hG
    have hperp : CuspClassAction.cuspClass hG ∈ Vᗮ := by
      rw [← hcl]
      have h := hde μ hμ (CuspClassAction.cuspClass hRF) fun k hk => hfixed α K' hRF k (by rw [hK'v]; exact hk)
      rw [Finsupp.sum] at h
      exact h

    by_contra hG0
    have hcls0 : toL2 ω 1 8 Φ₀ ⟨_, hG.1⟩ ≠ 0 := CuspClassAction.toL2_ne_zero_of_ne_zero hΦ₀ hI hG hG0
    have huF'0 : toL2 ω 1 8 Φ₀ ⟨F', hF'.1⟩ ≠ 0 := fun h0 => hu0 (by
      rw [huF']
      exact Subtype.ext h0)

    have hGt : (fun x => μ.sum fun h c => c * translateRight (localToAdelic3 v h)
        (smoothingOperator (LocalConstituent.kernelOf α K') f) x) ∈ cuspFunctions ω 1 8 Φ₀ := hG
    have hclst : toL2 ω 1 8 Φ₀ ⟨(fun x => μ.sum fun h c => c * translateRight (localToAdelic3 v h)
        (smoothingOperator (LocalConstituent.kernelOf α K') f) x), hGt.1⟩ ≠ 0 := hcls0

    obtain ⟨S', hS'⟩ : ∃ S' : Finset (HeightOneSpectrum (𝓞 ℚ)), S' = S ∪ {v} ∪
        (Filter.eventually_cofinite.1 hK'e).toFinset ∪ (Filter.eventually_cofinite.1 hK₀'e).toFinset ∪
          (Filter.eventually_cofinite.1 hKθ'e).toFinset := ⟨_, rfl⟩
    have hS'S : ∀ p, p ∉ S' → p ∉ S ∧ p ≠ v ∧ K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p ∧
        K₀' p = localMaximalCompact3 (𝓞 ℚ) ℚ p ∧ Kθ' p = localMaximalCompact3 (𝓞 ℚ) ℚ p := by
      intro p hp
      rw [hS'] at hp
      simp only [Finset.mem_union, Finset.mem_singleton, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or,
        not_not] at hp
      exact ⟨hp.1.1.1.1, hp.1.1.1.2, hp.1.1.2, hp.1.2, hp.2⟩
    have htr := fun (p : HeightOneSpectrum (𝓞 ℚ)) (hp : p ∉ S') =>
      LocalConstituent.TransportUnit.isRightInvariant_and_isCosetEigenfunction_sum_translateRight_smoothingOperator p v
        (hS'S p hp).2.1 (lam1 p)
        (lam2 p) _ hφ (hmax _ α K' (fun _ => rfl) p (hS'S p hp).2.2.1) f _hc (_hK p (hS'S p hp).1)
        (_hT1 p (hS'S p hp).1) (_hT2 p (hS'S p hp).1) μ
    obtain ⟨g, hg, hinner⟩ := exists_inner_toL2_translateRight_ne_zero_of_isCosetEigenfunction S' ω hω lam1 lam2 1 8
      Φ₀ hΦ₀ _ hGt hclst (fun p hp => (htr p hp).1) (fun p hp => (htr p hp).2.1) (fun p hp => (htr p hp).2.2)
      F' hF' huF'0 (fun p hp => (hdata' p (hS'S p hp).1 (hS'S p hp).2.2.2.1 (hS'S p hp).2.2.2.2).1)
      (fun p hp => (hdata' p (hS'S p hp).1 (hS'S p hp).2.2.2.1 (hS'S p hp).2.2.2.2).2.1)
      (fun p hp => (hdata' p (hS'S p hp).1 (hS'S p hp).2.2.2.1 (hS'S p hp).2.2.2.2).2.2)
    apply hinner
    rw [← CuspClassAction.rbar_toL2 hR g _ hGt, ← CuspClassAction.coe_cuspClass hF', ← Submodule.coe_inner]
    refine Submodule.inner_left_of_mem_orthogonal (K := V) (by rw [← huF']; exact huV) ?_
    exact HilbertConstituent.isInvariant_orthogonal hRadj hV.2.1 _ ⟨g, rfl⟩ _ hperp

  suffices hpt : ∀ x : AdelicGL 3 (𝓞 ℚ) ℚ, (∑ h ∈ μ.support, μ h * f (x * localToAdelic3 v h)) = 0 by
    rw [Finsupp.sum]
    funext x
    rw [Finset.sum_apply, Pi.zero_apply]
    exact (Finset.sum_congr rfl fun h _ => rfl).trans (hpt x)
  exact fun x => LocalConstituent.sum_mul_apply_mul_localToAdelic3_eq_zero _hc hKfo hKfc hKfU μ hvan x

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.Level2.standinSolution
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (lam1 lam2 : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (_hc : Continuous f)
    (_haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g)
    (_hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g)
    (_hmg : IsModerateGrowth3 ℚ f)
    (_hP21 : IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f)
    (_hP12 : IsCuspidalAlongP12 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f)
    (_hK : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f)
    (_hT1 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen1 p)) f (lam1 p))
    (_hT2 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen2 p)) f (lam2 p))
    (v : HeightOneSpectrum (𝓞 ℚ))
    (_hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, f (g * localToAdelic3 v k) = f g) :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Module ℂ E) (πE : LocalGL3 v →* Module.End ℂ E),
      IsIrreducibleRep πE ∧ IsSmoothRep πE ∧ IsAdmissibleRep πE ∧
        ∃ (d : ℕ) (e : Fin d → E), ∀ μ : LocalGL3 v →₀ ℂ,
          (∀ j : Fin d, (μ.sum fun (h : LocalGL3 v) (c : ℂ) => c • πE h (e j)) = 0) →
            (μ.sum fun (h : LocalGL3 v) (c : ℂ) =>
              c • fun g : AdelicGL 3 (𝓞 ℚ) ℚ => f (g * localToAdelic3 v h)) = 0 := by
  classical

  wlog hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1 generalizing ω lam1 lam2 f with H
  ·
    by_cases hf0 : f = 0
    · obtain ⟨E, iE, mE, πE, hirr, hsmE, hadm⟩ :=
        Twist.exists_isIrreducibleRep_isSmoothRep_isAdmissibleRep (LocalGL3 v)
      refine ⟨E, iE, mE, πE, hirr, hsmE, hadm, 0, Fin.elim0, fun μ _ => ?_⟩
      subst hf0
      rw [Finsupp.sum]
      refine Finset.sum_eq_zero fun h _ => ?_
      funext g
      simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_zero]

    obtain ⟨g₀, hg₀⟩ : ∃ g₀, f g₀ ≠ 0 := by
      by_contra h
      push Not at h
      exact hf0 (funext h)
    have hωc : Continuous fun z => (ω z : ℂ) := Twist.continuous_character_of_central ω f _hc _hcen g₀ hg₀
    have hω1 : ∀ x ∈ M4aHerbrand.principalIdeles (𝓞 ℚ) ℚ, ω x = 1 :=
      Twist.character_eq_one_of_mem_principalIdeles ω f _haut _hcen g₀ hg₀
    let χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℝ :=
      { toFun := fun z => ‖(ω z : ℂ)‖
        map_one' := by rw [map_one, Units.val_one, norm_one]
        map_mul' := fun a b => by rw [map_mul, Units.val_mul, norm_mul] }
    have hχ : ∀ z, χ z = ‖(ω z : ℂ)‖ := fun _ => rfl
    have hχc : Continuous χ := continuous_norm.comp hωc
    have hχpos : ∀ x, 0 < χ x := fun x => norm_pos_iff.mpr (ω x).ne_zero
    have hχ1 : ∀ x ∈ M4aHerbrand.principalIdeles (𝓞 ℚ) ℚ, χ x = 1 := fun x hx => by
      rw [hχ, hω1 x hx, Units.val_one, norm_one]
    obtain ⟨s, hs, hsc⟩ := NormSection.exists_ideleNorm_section
    obtain ⟨σ, hσ⟩ := Twist.exists_character_eq_ideleNorm_rpow χ
      (NumberField.TateGlobal.compactSpace_normOneIdeleClass ℚ) hχc hχpos hχ1 s hs (hχc.comp_continuousOn hsc)

    set t : ℝ := -σ / 3 with ht
    have hn0 : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ((NumberField.TateGlobal.ideleNorm ℚ z ^ (3 * t) : ℝ) : ℂ) ≠ 0 := fun z =>
      Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (NumberField.TateGlobal.ideleNorm_pos z) _).ne'
    let ω' : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ :=
      { toFun := fun z => ω z * Units.mk0 _ (hn0 z)
        map_one' := Units.ext (by
          rw [Units.val_mul, Units.val_mk0, map_one, Units.val_one, one_mul, Twist.ideleNorm_one,
            Real.one_rpow, Complex.ofReal_one])
        map_mul' := fun a b => Units.ext (by
          simp only [Units.val_mul, Units.val_mk0, map_mul, NumberField.TateGlobal.ideleNorm_mul,
            Real.mul_rpow (NumberField.TateGlobal.ideleNorm_pos a).le (NumberField.TateGlobal.ideleNorm_pos b).le,
            Complex.ofReal_mul]
          ring) }
    have hω' : ∀ z, (ω' z : ℂ) = (ω z : ℂ) * ((NumberField.TateGlobal.ideleNorm ℚ z ^ (3 * t) : ℝ) : ℂ) :=
      fun _ => rfl

    have hγ1 : ∀ γ : GL (Fin 3) ℚ,
        NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (globalPointsGL 3 (𝓞 ℚ) ℚ γ)) = 1 := by
      intro γ
      letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := borel _
      haveI : BorelSpace (AdeleRing (𝓞 ℚ) ℚ) := ⟨rfl⟩
      have h := NumberField.AdeleRing.distribHaarChar_algebraMap ℚ (Matrix.GeneralLinearGroup.det γ)
      try rw [RingHom.toMonoidHom_eq_coe] at h
      show NumberField.TateGlobal.ideleNorm ℚ
        (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map _ γ)) = 1
      rw [Matrix.GeneralLinearGroup.map_det]
      unfold NumberField.TateGlobal.ideleNorm
      rw [h, NNReal.coe_one]
    have hz3 : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
        NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (centralScalarGL 3 (𝓞 ℚ) ℚ z)) =
          NumberField.TateGlobal.ideleNorm ℚ z ^ 3 := by
      intro z
      have hdet : Matrix.GeneralLinearGroup.det (centralScalarGL 3 (𝓞 ℚ) ℚ z) = z ^ 3 := by
        show Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 3) z) = z ^ 3
        rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]
      rw [hdet]
      simp only [pow_succ, pow_zero, NumberField.TateGlobal.ideleNorm_mul, one_mul]
    have key := H ω'
      (fun p => ((NumberField.TateGlobal.ideleNorm ℚ
        (Matrix.GeneralLinearGroup.det (localToAdelic3 p (heckeGen1 p))) ^ t : ℝ) : ℂ) * lam1 p)
      (fun p => ((NumberField.TateGlobal.ideleNorm ℚ
        (Matrix.GeneralLinearGroup.det (localToAdelic3 p (heckeGen2 p))) ^ t : ℝ) : ℂ) * lam2 p)
      (fun g => ((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ t : ℝ) : ℂ) * f g)
      (DeterminantGauge.continuous_twist_mul t _hc)
      (fun γ g => by
        show ((NumberField.TateGlobal.ideleNorm ℚ
            (Matrix.GeneralLinearGroup.det (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g)) ^ t : ℝ) : ℂ) * _ = _
        rw [DeterminantGauge.twist_mul, DeterminantGauge.twist_eq_one (hγ1 γ), one_mul,
          _haut γ g])
      (fun z g => by
        show ((NumberField.TateGlobal.ideleNorm ℚ
            (Matrix.GeneralLinearGroup.det (centralScalarGL 3 (𝓞 ℚ) ℚ z * g)) ^ t : ℝ) : ℂ) * _ = _
        rw [DeterminantGauge.twist_mul, _hcen z g, hω', hz3,
          ← Real.rpow_natCast_mul (NumberField.TateGlobal.ideleNorm_pos z).le, Nat.cast_ofNat]
        ring)
      (DeterminantGauge.isModerateGrowth3_ideleNorm_det_rpow_mul _hmg t)
      (DeterminantGauge.isCuspidalAlongP21_twist_mul t _ _hP21)
      (DeterminantGauge.isCuspidalAlongP12_twist_mul t _ _hP12)
      (DeterminantGauge.isRightInvariant_twist_mul t S _hK)
      (DeterminantGauge.isCosetEigenfunction_twist_mul t S (fun p => heckeGen1 p) lam1 _hT1)
      (DeterminantGauge.isCosetEigenfunction_twist_mul t S (fun p => heckeGen2 p) lam2 _hT2)
      (DeterminantGauge.exists_isOpen_twist_mul t v _hsm)
      (fun z => by
        rw [hω', norm_mul,
          Complex.norm_of_nonneg (Real.rpow_nonneg (NumberField.TateGlobal.ideleNorm_pos z).le _), ← hχ, hσ z,
          ← Real.rpow_add (NumberField.TateGlobal.ideleNorm_pos z), ht,
          show σ + 3 * (-σ / 3) = 0 by ring, Real.rpow_zero])

    obtain ⟨E, iE, mE, πE, hirr, hsmE, hadm, d, e, hann⟩ := key
    have hn0' : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        ((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ t : ℝ) : ℂ) ≠ 0 := fun g =>
      Complex.ofReal_ne_zero.mpr
        (Real.rpow_pos_of_pos (NumberField.TateGlobal.ideleNorm_pos (Matrix.GeneralLinearGroup.det g)) _).ne'
    let nv : LocalGL3 v →* ℂˣ :=
      { toFun := fun h => Units.mk0 _ (hn0' (localToAdelic3 v h))
        map_one' := Units.ext (by
          rw [Units.val_mk0, Units.val_one, map_one]
          exact DeterminantGauge.twist_eq_one (by
            rw [map_one, Twist.ideleNorm_one]))
        map_mul' := fun a b => Units.ext (by
          rw [Units.val_mk0, Units.val_mul, Units.val_mk0, Units.val_mk0, map_mul,
            DeterminantGauge.twist_mul]) }
    have hnv : ∀ h, (nv h : ℂ) =
        ((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (localToAdelic3 v h)) ^ t : ℝ) : ℂ) :=
      fun _ => rfl

    have hcpt : ∀ K : Subgroup (LocalGL3 v), IsCompact (K : Set (LocalGL3 v)) → ∀ k ∈ K, nv⁻¹ k = 1 := by
      intro K hK k hk
      haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
      let ρ : K →* ℝ :=
        { toFun := fun k =>
            NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (localToAdelic3 v (k : LocalGL3 v)))
          map_one' := by
            rw [OneMemClass.coe_one, map_one, map_one, Twist.ideleNorm_one]
          map_mul' := fun a b => by
            rw [Subgroup.coe_mul, map_mul, map_mul, NumberField.TateGlobal.ideleNorm_mul] }
      have hρ : ∀ k : K, ρ k =
          NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (localToAdelic3 v (k : LocalGL3 v))) :=
        fun _ => rfl
      have hρc : Continuous ρ := by
        have hfun : (fun k : K => ρ k) =
            fun k : K => ‖(((k : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))).det‖ := by
          funext k
          rw [hρ, DeterminantGauge.ideleNorm_det_localToAdelic3_eq,
            ← DeterminantGauge.coe_det_componentAt3, DeterminantGauge.componentAt3_localToAdelic3_self,
            Matrix.GeneralLinearGroup.val_det_apply]
        show Continuous fun k : K => ρ k
        rw [hfun]
        exact continuous_norm.comp ((Units.continuous_val.comp continuous_subtype_val).matrix_det)
      have h1 : NumberField.TateGlobal.ideleNorm ℚ
          (Matrix.GeneralLinearGroup.det (localToAdelic3 v k)) = 1 :=
        Twist.apply_eq_one_of_compactSpace ρ hρc (fun k => NumberField.TateGlobal.ideleNorm_pos _) ⟨k, hk⟩
      rw [MonoidHom.inv_apply, inv_eq_one]
      exact Units.ext (DeterminantGauge.twist_eq_one h1)
    have hker : IsOpen (((nv⁻¹ : LocalGL3 v →* ℂˣ).ker : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) := by
      refine Subgroup.isOpen_mono (H₁ := localMaximalCompact3 (𝓞 ℚ) ℚ v) (fun k hk => ?_)
        (DeterminantGauge.isOpen_localMaximalCompact3 v)
      rw [MonoidHom.mem_ker, MonoidHom.inv_apply, inv_eq_one]
      exact Units.ext (DeterminantGauge.twist_localToAdelic3 v hk)
    refine ⟨E, iE, mE, Twist.twistRep nv⁻¹ πE, Twist.isIrreducibleRep_twistRep _ hirr,
      Twist.isSmoothRep_twistRep _ hker hsmE, Twist.isAdmissibleRep_twistRep _ hcpt hadm, d, e, fun μ hμ => ?_⟩
    obtain ⟨ν, hνs, hν⟩ := Twist.exists_finsupp_mul nv⁻¹ μ
    have hν' : ∀ h, ν h = μ h * (((nv h)⁻¹ : ℂˣ) : ℂ) := fun h => by rw [hν h, MonoidHom.inv_apply]
    have hνann : ∀ j : Fin d, (ν.sum fun (h : LocalGL3 v) (c : ℂ) => c • πE h (e j)) = 0 := fun j => by
      rw [← Twist.finsupp_sum_smul_eq nv⁻¹ μ ν hνs hν fun h => πE h (e j), ← hμ j]
      simp only [Twist.twistRep_apply]
    exact Twist.finsupp_sum_translate_eq_zero
      (fun (g : AdelicGL 3 (𝓞 ℚ) ℚ) (h : LocalGL3 v) => g * localToAdelic3 v h)
      (fun g => ((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ t : ℝ) : ℂ)) nv f
      (fun g => ((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ t : ℝ) : ℂ) * f g)
      (fun _ => rfl) (fun g h => DeterminantGauge.twist_mul g (localToAdelic3 v h)) hn0' μ ν hνs hν' (hann ν hνann)
  exact LanglandsTunnell.CubicInduction.Level2.standinSolution_of_norm_eq_one S ω lam1 lam2 f _hc _haut _hcen
    _hmg _hP21 _hP12 _hK _hT1 _hT2 v _hsm hω

p2m_open "LanglandsTunnell.CubicInduction~isCompact_localMaximalCompact3~det_radicalP21~det_radicalP12" in open _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong.LanglandsTunnell.CubicInduction in
open Matrix IsDedekindDomain NumberField AutomorphicForm FLT.SmoothAdmissibleSchurCommutant in
theorem solution
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (lam1 lam2 : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (_hc : Continuous f)
    (_haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g)
    (_hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g)
    (_hmg : IsModerateGrowth3 ℚ f)
    (_hP21 : IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f)
    (_hP12 : IsCuspidalAlongP12 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f)
    (_hK : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f)
    (_hT1 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen1 p)) f (lam1 p))
    (_hT2 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen2 p)) f (lam2 p))
    (v : HeightOneSpectrum (𝓞 ℚ))
    (_hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, f (g * localToAdelic3 v k) = f g) :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Module ℂ E) (πE : LocalGL3 v →* Module.End ℂ E),
      IsIrreducibleRep πE ∧ IsSmoothRep πE ∧ IsAdmissibleRep πE ∧
        ∃ (d : ℕ) (e : Fin d → E), ∀ μ : LocalGL3 v →₀ ℂ,
          (∀ j : Fin d, (μ.sum fun (h : LocalGL3 v) (c : ℂ) => c • πE h (e j)) = 0) →
            (μ.sum fun (h : LocalGL3 v) (c : ℂ) =>
              c • fun g : AdelicGL 3 (𝓞 ℚ) ℚ => f (g * localToAdelic3 v h)) = 0
:=
  LanglandsTunnell.CubicInduction.Level2.standinSolution S ω lam1 lam2 f _hc _haut _hcen _hmg _hP21
    _hP12 _hK _hT1 _hT2 v _hsm

end S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_sum_smul_translate_eq_zero_of_isCuspidalAlong (solution)
