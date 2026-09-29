-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_hasProd_rsFinIntegral_eq_rsFinIntegral_indicator_mul_of_torus_law
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/acfab362-d71a-53e2-bb63-804670075414

import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_UnramifiedWhittaker_apply_mul_placeEmbed_diagZ_eq_mul_torusFactor
import Theorems.Thm_LanglandsTunnell_RankinSelberg_mk_twoRowCauchySum_mul_coe_rsEulerPoly_eq_one
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_uniformizerIdele
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
import Theorems.Thm_HaarQuotient_lintegral_density_mul_eq_one
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_isHaarMeasure_map_eq_prod_localAt
import Theorems.Thm_MeasureTheory_Measure_exists_isHaarMeasure_map_continuousMulEquiv_eq_prod
import Theorems.Thm_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral

import Theorems.Thm_LanglandsTunnell_RankinSelberg_mk_heckeRecursionSeq_mul_heckeRecursionSeq_mul_coe_rsEulerPoly_eq_and_hasSum
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_hasProd_rsFinIntegral_eq_rsFinIntegral_indicator_mul_of_torus_law
p2m_attr_erase "instance" "instCountableOfNumberField_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel

open MeasureTheory NumberField AutomorphicForm IsDedekindDomain UnramifiedWhittaker AdelicDock Topology

universe u₁ u₂ u₃

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RankinSelberg.mk_twoRowCauchySum_mul_coe_rsEulerPoly_eq_one RankinSelberg.mk_heckeRecursionSeq_mul_heckeRecursionSeq_mul_coe_rsEulerPoly_eq_and_hasSum RankinSelberg.exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow"
namespace RankinSelberg
p2m_export "LanglandsTunnell.RankinSelberg" "rsEulerPoly mk_twoRowCauchySum_mul_coe_rsEulerPoly_eq_one exists_isHaarMeasure_map_eq_prod_localAt hasSum_cell_terms_rsLocalIntegral mk_heckeRecursionSeq_mul_heckeRecursionSeq_mul_coe_rsEulerPoly_eq_and_hasSum exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow"
namespace VSplitInhabitant
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

section Continuity

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

private theorem continuous_splice (a : FiniteAdeleRing R K)
    (ha : ∀ w : HeightOneSpectrum R, a w ∈ w.adicCompletionIntegers K) :
    Continuous (splice R K v a) := by
  have hS : (Filter.cofinite : Filter (HeightOneSpectrum R)) ≤ Filter.principal {w | w ≠ v} := by
    rw [Filter.le_principal_iff]
    exact (Set.finite_singleton v).compl_mem_cofinite
  let g : v.adicCompletion K →
      RestrictedProduct (fun w : HeightOneSpectrum R => w.adicCompletion K)
        (fun w => (w.adicCompletionIntegers K : Set (w.adicCompletion K))) (Filter.principal {w | w ≠ v}) :=
    fun t => ⟨fun w => splice R K v a t w, by
      rw [Filter.eventually_principal]
      intro w hw
      show splice R K v a t w ∈ (w.adicCompletionIntegers K : Set (w.adicCompletion K))
      rw [splice_apply_of_ne R K v a t hw]
      exact ha w⟩
  have hg : Continuous g := by
    rw [RestrictedProduct.continuous_rng_of_principal_iff_forall]
    intro w
    by_cases hw : w = v
    · subst hw
      have : ((fun x => x w) ∘ g) = id := by
        funext t
        exact splice_apply_self R K w a t
      rw [this]
      exact continuous_id
    · have : ((fun x => x w) ∘ g) = fun _ => a w := by
        funext t
        exact splice_apply_of_ne R K v a t hw
      rw [this]
      exact continuous_const
  exact (RestrictedProduct.continuous_inclusion hS).comp hg

private theorem one_entry_mem (i j : Fin 2) (w : HeightOneSpectrum R) :
    (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j w ∈ w.adicCompletionIntegers K := by
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

private theorem continuous_localMat : Continuous (localMat R K v) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (continuous_splice R K v _ (one_entry_mem R K i j)).comp
    ((continuous_apply j).comp (continuous_apply i))

private theorem continuous_localEmbed : Continuous (localEmbed R K v) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_localMat R K v).comp Units.continuous_val
  · exact (continuous_localMat R K v).comp Units.continuous_coe_inv

private theorem continuous_finMat : Continuous (finMat R K) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact continuous_const.prodMk ((continuous_apply j).comp (continuous_apply i))

private theorem continuous_finEmbed : Continuous (finEmbed R K) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_finMat R K).comp Units.continuous_val
  · exact (continuous_finMat R K).comp Units.continuous_coe_inv

end Continuity

section Section

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem placeEmbed_mem (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    UnramifiedWhittaker.placeEmbed ℚ v x ∈ finiteAdelicGL2Subgroup ℚ := by
  rw [mem_finiteAdelicGL2Subgroup_iff]
  exact glArch_finEmbed (𝓞 ℚ) ℚ _

private def sectionAt : GL (Fin 2) (v.adicCompletion ℚ) →* finiteAdelicGL2Subgroup ℚ :=
  (UnramifiedWhittaker.placeEmbed ℚ v).codRestrict _ (placeEmbed_mem v)

private theorem coe_sectionAt (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    ((sectionAt v x : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) =
      finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ v x) :=
  rfl

private theorem continuous_sectionAt : Continuous (sectionAt v) :=
  ((continuous_finEmbed (𝓞 ℚ) ℚ).comp (continuous_localEmbed (𝓞 ℚ) ℚ v)).subtype_mk _

private theorem localAt_sectionAt (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    localAt ℚ v (sectionAt v x : AdelicGL2 (𝓞 ℚ) ℚ) = x := by
  rw [coe_sectionAt]
  show AdelicLevel.finComponent (𝓞 ℚ) ℚ v (AdelicLevel.glFin (𝓞 ℚ) ℚ (finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ v x))) = x
  rw [glFin_finEmbed, finComponent_localEmbed_self]

private theorem finAdeleEval_mapMatrix_adeleFin_mapMatrix (w : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix
        ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))) =
      (localAt ℚ w g : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) :=
  rfl

private theorem finAdeleEval_mapMatrix_sectionAt (w : HeightOneSpectrum (𝓞 ℚ)) (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix
        ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix
          ((sectionAt v x : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))) =
      (AdelicLevel.finComponent (𝓞 ℚ) ℚ w (localEmbed (𝓞 ℚ) ℚ v x) :
        Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) := by
  rw [coe_sectionAt]
  show (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix (finMat (𝓞 ℚ) ℚ (localMat (𝓞 ℚ) ℚ v x) |>
    (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix) = _
  rw [mapMatrix_fin_finMat]
  rfl

private theorem arch_mapMatrix_eq_one_of_mem (g : AdelicGL2 (𝓞 ℚ) ℚ) (hg : g ∈ finiteAdelicGL2Subgroup ℚ) :
    (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) = 1 := by
  have h := congrArg Units.val ((mem_finiteAdelicGL2Subgroup_iff ℚ g).mp hg)
  rw [Units.val_one] at h
  ext i j
  have hij := congrFun (congrFun h i) j
  rw [AdelicLevel.glArch_apply] at hij
  simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleArch_apply] using hij

private theorem sectionAt_mul_comm (x : GL (Fin 2) (v.adicCompletion ℚ)) (k : finiteAdelicGL2Subgroup ℚ)
    (hk : localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1) : sectionAt v x * k = k * sectionAt v x := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  refine matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 ℚ) ℚ ?_ ?_
  ·
    have hx := arch_mapMatrix_eq_one_of_mem _ (sectionAt v x).2
    have hk' := arch_mapMatrix_eq_one_of_mem _ k.2
    rw [map_mul, map_mul, hx, hk', one_mul]
  ·
    rw [map_mul, map_mul]
    refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 ℚ) ℚ fun w => ?_
    rw [map_mul, map_mul, finAdeleEval_mapMatrix_sectionAt]
    by_cases hw : w = v
    · subst hw
      rw [finComponent_localEmbed_self, finAdeleEval_mapMatrix_adeleFin_mapMatrix, hk, Units.val_one, one_mul,
        mul_one]
    · rw [finComponent_localEmbed_of_ne (𝓞 ℚ) ℚ v x hw, Units.val_one, one_mul, mul_one]

end Section

section Inhabitant

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem exists_section :
    ∃ ι : GL (Fin 2) (v.adicCompletion ℚ) →* finiteAdelicGL2Subgroup ℚ, Continuous ι ∧
      (∀ x : GL (Fin 2) (v.adicCompletion ℚ), localAt ℚ v (ι x : AdelicGL2 (𝓞 ℚ) ℚ) = x) ∧
        ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (k : finiteAdelicGL2Subgroup ℚ),
          localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1 → ι x * k = k * ι x :=
  ⟨sectionAt v, continuous_sectionAt v, localAt_sectionAt v, sectionAt_mul_comm v⟩

private theorem locallyCompactSpace_finiteAdelicGL2Subgroup : LocallyCompactSpace (finiteAdelicGL2Subgroup ℚ) :=
  (isClosed_finiteAdelicGL2Subgroup ℚ).locallyCompactSpace

private theorem exists_isHaarMeasure : ∃ μ : Measure (finiteAdelicGL2Subgroup ℚ), μ.IsHaarMeasure :=
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 ℚ) ℚ
  haveI := locallyCompactSpace_finiteAdelicGL2Subgroup
  ⟨Measure.haar, inferInstance⟩

end Inhabitant

end LanglandsTunnell.RankinSelberg.VSplitInhabitant

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RankinSelberg.mk_twoRowCauchySum_mul_coe_rsEulerPoly_eq_one RankinSelberg.mk_heckeRecursionSeq_mul_heckeRecursionSeq_mul_coe_rsEulerPoly_eq_and_hasSum RankinSelberg.exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow"
namespace RankinSelberg
p2m_export "LanglandsTunnell.RankinSelberg" "rsEulerPoly mk_twoRowCauchySum_mul_coe_rsEulerPoly_eq_one exists_isHaarMeasure_map_eq_prod_localAt hasSum_cell_terms_rsLocalIntegral mk_heckeRecursionSeq_mul_heckeRecursionSeq_mul_coe_rsEulerPoly_eq_and_hasSum exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow"
namespace LocalCountability
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

open Topology TopologicalSpace

private theorem countable_of_numberField (K : Type) [Field K] [NumberField K] : Countable K :=
  (Module.Free.chooseBasis ℚ K).equivFun.toEquiv.injective.countable

attribute [local instance] countable_of_numberField

private theorem countable_withVal {R : Type} [Ring R] [Countable R] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀]
    (w : Valuation R Γ₀) : Countable (WithVal w) :=
  Countable.of_equiv R (WithVal.equiv w).toEquiv.symm

attribute [local instance] countable_withVal

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem secondCountableTopology_adicCompletion : SecondCountableTopology (v.adicCompletion K) :=
  inferInstance

attribute [local instance] secondCountableTopology_adicCompletion

private theorem secondCountableTopology_matrix :
    SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → v.adicCompletion K))

attribute [local instance] secondCountableTopology_matrix

private theorem secondCountableTopology_matrix_op :
    SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion K))ᵐᵒᵖ :=
  (MulOpposite.opHomeomorph (M := Matrix (Fin 2) (Fin 2) (v.adicCompletion K))).symm.isInducing
    |>.secondCountableTopology

attribute [local instance] secondCountableTopology_matrix_op

private theorem secondCountableTopology_gl : SecondCountableTopology (GL (Fin 2) (v.adicCompletion K)) :=
  Units.isInducing_embedProduct.secondCountableTopology

attribute [local instance] secondCountableTopology_gl

end LanglandsTunnell.RankinSelberg.LocalCountability

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RankinSelberg.mk_twoRowCauchySum_mul_coe_rsEulerPoly_eq_one RankinSelberg.mk_heckeRecursionSeq_mul_heckeRecursionSeq_mul_coe_rsEulerPoly_eq_and_hasSum RankinSelberg.exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow"
namespace RankinSelberg
p2m_export "LanglandsTunnell.RankinSelberg" "rsEulerPoly mk_twoRowCauchySum_mul_coe_rsEulerPoly_eq_one exists_isHaarMeasure_map_eq_prod_localAt hasSum_cell_terms_rsLocalIntegral mk_heckeRecursionSeq_mul_heckeRecursionSeq_mul_coe_rsEulerPoly_eq_and_hasSum exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow"
namespace OnePlaceSplit
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

open VSplitInhabitant HaarQuotient AdelicDock
open scoped ENNReal

attribute [local instance] LocalCountability.countable_of_numberField
attribute [local instance] LocalCountability.countable_withVal
attribute [local instance] LocalCountability.secondCountableTopology_adicCompletion
attribute [local instance] LocalCountability.secondCountableTopology_matrix
attribute [local instance] LocalCountability.secondCountableTopology_matrix_op
attribute [local instance] LocalCountability.secondCountableTopology_gl

section Data

variable (v : HeightOneSpectrum (𝓞 ℚ))

private local instance instMeasurableSpaceLocal : MeasurableSpace (GL (Fin 2) (v.adicCompletion ℚ)) :=
  borel (GL (Fin 2) (v.adicCompletion ℚ))

private local instance instBorelSpaceLocal : BorelSpace (GL (Fin 2) (v.adicCompletion ℚ)) := ⟨rfl⟩

private def kerpart (g : finiteAdelicGL2Subgroup ℚ) : finiteAdelicGL2Subgroup ℚ :=
  g * (sectionAt v (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ)))⁻¹

private def unipotentAway : Subgroup (finiteAdelicGL2Subgroup ℚ) :=
  RSCarrier.finUnipotent ⊓ ((localAt ℚ v).comp (finiteAdelicGL2Subgroup ℚ).subtype).ker

private def prodDensity (μNv : Measure (unipotentGL2Hom (R := v.adicCompletion ℚ)).range)
    (μ₄ : Measure (unipotentAway v)) (g : finiteAdelicGL2Subgroup ℚ) : ℝ≥0∞ :=
  density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μNv (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ)) *
    density (unipotentAway v) μ₄ (kerpart v g)

private def finWeight (g : finiteAdelicGL2Subgroup ℚ) : ℝ :=
  TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ))

private def localWeight (x : GL (Fin 2) (v.adicCompletion ℚ)) : ℝ := finWeight (sectionAt v x)

private def kernelIntegral (μ' : Measure (finiteAdelicGL2Subgroup ℚ)) (ρ' : finiteAdelicGL2Subgroup ℚ → ℝ≥0∞)
    (s : ℂ) (W F : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (x : GL (Fin 2) (v.adicCompletion ℚ)) : ℂ :=
  ∫ k : finiteAdelicGL2Subgroup ℚ,
    (W ((k * sectionAt v x : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) *
        F ((k * sectionAt v x : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) *
      ((finWeight k : ℝ) : ℂ) ^ (s - 1 / 2) * (((ρ' k).toReal : ℝ) : ℂ) ∂μ'

private def torusPt {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0) (p : ℤ × ℤ) :
    GL (Fin 2) (v.adicCompletion ℚ) :=
  diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (p.1 - p.2) *
    scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ p.2

private def cellValue (lam om : ℂ) (uZ : ℤ → ℤ → ℂ) (p : ℤ × ℤ) : ℂ :=
  om ^ p.2.toNat * torusFactor (Ideal.absNorm v.asIdeal) lam om (p.1 - p.2) *
    ((Ideal.absNorm v.asIdeal : ℂ)⁻¹ ^ p.1 * uZ p.1 p.2)

private def _root_.LanglandsTunnell.RankinSelberg.OnePlaceSplit.seriesTerm (s lam om : ℂ) (uZ : ℤ → ℤ → ℂ) (p : ℤ × ℤ) : ℂ :=
  (Ideal.absNorm v.asIdeal : ℂ) ^ (p.1 - p.2) * cellValue v lam om uZ p *
    (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(p.1 + p.2)) : ℝ) : ℂ) ^ (s - 1 / 2)

p2m_export "LanglandsTunnell.RankinSelberg.OnePlaceSplit" "seriesTerm"

private def localCell : Set (GL (Fin 2) (v.adicCompletion ℚ)) :=
  {g | ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range, ∃ k ∈ localLevelOne (𝓞 ℚ) ℚ v ⊤, g = n * k}

private def preCell : Set (finiteAdelicGL2Subgroup ℚ) :=
  {g | ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range, ∃ k ∈ localLevelOne (𝓞 ℚ) ℚ v ⊤,
    localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}

private def cellMass (μv : Measure (GL (Fin 2) (v.adicCompletion ℚ)))
    (μNv : Measure (unipotentGL2Hom (R := v.adicCompletion ℚ)).range) : ℂ :=
  (((μv.withDensity (density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μNv)) (localCell v)).toReal : ℂ)

end Data

section Furniture

section LevelOneOpen

namespace IntegralUnits

open Matrix NumberField

variable {F : Type*} [Field F] (O : ValuationSubring F)

private def IsIntegralUnit (k : GL (Fin 2) F) : Prop :=
  (∀ i j, (k : Matrix (Fin 2) (Fin 2) F) i j ∈ O) ∧ ∀ i j, ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j ∈ O

variable {O}

private theorem isOpen_setOf_isIntegralUnit [TopologicalSpace F] [IsTopologicalRing F] (hO : IsOpen (O : Set F)) :
    IsOpen {k : GL (Fin 2) F | IsIntegralUnit O k} := by
  have h1 : ∀ i j : Fin 2, IsOpen {k : GL (Fin 2) F | (k : Matrix (Fin 2) (Fin 2) F) i j ∈ O} := fun i j =>
    hO.preimage (Units.continuous_val.matrix_elem i j)
  have h2 : ∀ i j : Fin 2, IsOpen {k : GL (Fin 2) F | ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j ∈ O} :=
    fun i j => hO.preimage (Units.continuous_coe_inv.matrix_elem i j)
  have hset : {k : GL (Fin 2) F | IsIntegralUnit O k} =
      (⋂ i, ⋂ j, {k : GL (Fin 2) F | (k : Matrix (Fin 2) (Fin 2) F) i j ∈ O}) ∩
        ⋂ i, ⋂ j, {k : GL (Fin 2) F | ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j ∈ O} := by
    ext k
    simp only [IsIntegralUnit, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hset]
  exact (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => h1 i j).inter
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => h2 i j)

end IntegralUnits

namespace LevelOne

open IsDedekindDomain AdelicDock IntegralUnits

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem isLocalLevelOne_top_iff (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :
    IsLocalLevelOne (𝓞 ℚ) ℚ v ⊤ m ↔ ∀ i j, m i j ∈ v.adicCompletionIntegers ℚ := by
  refine ⟨fun h => h.integral, fun h => ⟨h, ?_, ?_⟩⟩
  · rw [AdelicLevel.idealBound_top]
    have := h 1 0
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at this
  · rw [AdelicLevel.idealBound_top]
    have := sub_mem (h 1 1) (one_mem (v.adicCompletionIntegers ℚ))
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at this

private theorem mem_localLevelOne_top_iff (k : GL (Fin 2) (v.adicCompletion ℚ)) :
    k ∈ localLevelOne (𝓞 ℚ) ℚ v ⊤ ↔ IsIntegralUnit (v.adicCompletionIntegers ℚ) k := by
  rw [mem_localLevelOne_iff, isLocalLevelOne_top_iff, isLocalLevelOne_top_iff]
  exact Iff.rfl

private theorem isOpen_localLevelOne_top :
    IsOpen ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) :
      Set (GL (Fin 2) (v.adicCompletion ℚ))) := by
  have hset : ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) :
      Set (GL (Fin 2) (v.adicCompletion ℚ))) =
        {k : GL (Fin 2) (v.adicCompletion ℚ) | IsIntegralUnit (v.adicCompletionIntegers ℚ) k} := by
    ext k
    exact mem_localLevelOne_top_iff v k
  rw [hset]
  exact isOpen_setOf_isIntegralUnit ((AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 ℚ) ℚ).out v)

end LevelOne

end LevelOneOpen

section Places

private theorem localAt_unipotentGL2Hom (q : HeightOneSpectrum (𝓞 ℚ)) (y : Multiplicative (AdeleRing (𝓞 ℚ) ℚ)) :
    localAt ℚ q (AutomorphicForm.unipotentGL2Hom y) =
      AutomorphicForm.unipotentGL2Hom (Multiplicative.ofAdd ((Multiplicative.toAdd y).2 q)) := by
  apply Units.ext
  ext i j
  simp only [localAt, MonoidHom.coe_comp, Function.comp_apply, AdelicLevel.finComponent_apply,
    AdelicLevel.glFin_apply, AutomorphicForm.unipotentGL2Hom, MonoidHom.coe_mk, OneHom.coe_mk,
    AutomorphicForm.unipotentGL2_coe, toAdd_ofAdd]
  fin_cases i <;> fin_cases j <;> simp <;> rfl

private theorem localAt_mem_range_of_mem_finUnipotent (q : HeightOneSpectrum (𝓞 ℚ)) (n : RSCarrier.finUnipotent) :
    localAt ℚ q ((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) ∈
      (AutomorphicForm.unipotentGL2Hom (R := q.adicCompletion ℚ)).range := by
  obtain ⟨y, hy⟩ : ((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) ∈
      (AutomorphicForm.unipotentGL2Hom (R := AdeleRing (𝓞 ℚ) ℚ)).range := Subgroup.mem_subgroupOf.mp n.2
  rw [← hy, localAt_unipotentGL2Hom]
  exact ⟨_, rfl⟩

private theorem isOpen_localCell (q : HeightOneSpectrum (𝓞 ℚ)) :
    IsOpen {y : GL (Fin 2) (q.adicCompletion ℚ) |
      ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := q.adicCompletion ℚ)).range,
        ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ q ⊤, y = n * k} := by
  have hset : {y : GL (Fin 2) (q.adicCompletion ℚ) |
      ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := q.adicCompletion ℚ)).range,
        ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ q ⊤, y = n * k} =
      ⋃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := q.adicCompletion ℚ)).range,
        (fun k => n * k) '' ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ q ⊤ : Subgroup (GL (Fin 2) (q.adicCompletion ℚ))) :
          Set (GL (Fin 2) (q.adicCompletion ℚ))) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, SetLike.mem_coe, exists_prop]
    constructor
    · rintro ⟨n, hn, k, hk, rfl⟩
      exact ⟨n, hn, k, hk, rfl⟩
    · rintro ⟨n, hn, k, hk, rfl⟩
      exact ⟨n, hn, k, hk, rfl⟩
  rw [hset]
  exact isOpen_biUnion fun n _ => (isOpenMap_mul_left n) _ (LevelOne.isOpen_localLevelOne_top q)

end Places

section GenericFurniture

private theorem sigmaCompactSpace_of_isClosed {G : Type*} [Group G] [TopologicalSpace G] [SigmaCompactSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) : SigmaCompactSpace H :=
  hH.sigmaCompactSpace

private theorem sfinite_of_isHaarMeasure {H : Type*} [Group H] [TopologicalSpace H] [SigmaCompactSpace H]
    [MeasurableSpace H] (ν : Measure H) [ν.IsHaarMeasure] : SFinite ν :=
  inferInstance

section Unipotent

variable {R : Type*} [CommRing R] [TopologicalSpace R] [T2Space R]

omit [TopologicalSpace R] [T2Space R] in

private theorem coe_range_unipotentGL2Hom :
    ((unipotentGL2Hom (R := R)).range : Set (GL (Fin 2) R)) =
      {g : GL (Fin 2) R | Units.val g 0 0 = 1 ∧ Units.val g 1 0 = 0 ∧ Units.val g 1 1 = 1} := by
  ext g
  constructor
  · rintro ⟨y, rfl⟩
    change Units.val (unipotentGL2 y.toAdd) 0 0 = 1 ∧ Units.val (unipotentGL2 y.toAdd) 1 0 = 0 ∧
      Units.val (unipotentGL2 y.toAdd) 1 1 = 1
    simp [unipotentGL2]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨Multiplicative.ofAdd (Units.val g 0 1), ?_⟩
    change unipotentGL2 (Units.val g 0 1) = g
    refine Units.ext ?_
    rw [unipotentGL2_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]

private theorem isClosed_range_unipotentGL2Hom :
    IsClosed ((unipotentGL2Hom (R := R)).range : Set (GL (Fin 2) R)) := by
  rw [coe_range_unipotentGL2Hom]
  have hc : Continuous fun g : GL (Fin 2) R => Units.val g := Units.continuous_val
  exact (isClosed_eq (hc.matrix_elem 0 0) continuous_const).inter
    ((isClosed_eq (hc.matrix_elem 1 0) continuous_const).inter
      (isClosed_eq (hc.matrix_elem 1 1) continuous_const))

end Unipotent

section Density

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]

private theorem measurable_weight (H : Subgroup G) (μH : Measure H) : Measurable (HaarQuotient.weight H μH) := by
  unfold HaarQuotient.weight
  split_ifs with h
  · refine Measurable.tsum fun n => ?_
    exact (measurable_const.indicator isOpen_interior.measurableSet).const_mul _
  · exact measurable_const

private theorem measurable_lintegral_weight_mul [BorelSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    (H : Subgroup G) (μH : Measure H) [SFinite μH] :
    Measurable fun g : G => ∫⁻ x : H, HaarQuotient.weight H μH ((x : G) * g) ∂μH := by
  have hm : Measurable fun p : H × G => HaarQuotient.weight H μH ((p.1 : G) * p.2) :=
    (measurable_weight H μH).comp ((measurable_subtype_coe.comp measurable_fst).mul measurable_snd)
  exact hm.lintegral_prod_left

private theorem measurable_density [BorelSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] (H : Subgroup G)
    (μH : Measure H) [SFinite μH] : Measurable (HaarQuotient.density H μH) := by
  unfold HaarQuotient.density
  exact (measurable_weight H μH).div (measurable_lintegral_weight_mul H μH)

end Density

end GenericFurniture

namespace Splitting

open Set Function

section Algebra

variable {G X : Type*} [Group G] [Group X] (π : G →* X) (σ : X →* G)

private def splitMap (g : G) : X × G := (π g, g * (σ (π g))⁻¹)

private theorem splitMap_fst (g : G) : (splitMap π σ g).1 = π g := rfl

private theorem splitMap_snd (g : G) : (splitMap π σ g).2 = g * (σ (π g))⁻¹ := rfl

private theorem snd_mul_section_fst (g : G) : (splitMap π σ g).2 * σ (splitMap π σ g).1 = g := by
  simp [splitMap]

private theorem range_splitMap (hσ : ∀ x, π (σ x) = x) : range (splitMap π σ) = {q : X × G | π q.2 = 1} := by
  ext ⟨x, k⟩
  constructor
  · rintro ⟨g, hg⟩
    simp only [splitMap, Prod.mk.injEq] at hg
    obtain ⟨rfl, rfl⟩ := hg
    simp [hσ]
  · intro hk
    refine ⟨k * σ x, ?_⟩
    simp only [mem_setOf_eq] at hk
    simp [splitMap, hk, hσ]

end Algebra

section Embedding

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [Group X] [TopologicalSpace X] [T1Space X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] (π : G →* X) (σ : X →* G)

omit [SecondCountableTopology X] in

private theorem measurableEmbedding_splitMap (hπ : Continuous π) (hσ_cont : Continuous σ) (hσ : ∀ x, π (σ x) = x) :
    MeasurableEmbedding (splitMap π σ) := by
  refine MeasurableEmbedding.of_measurable_inverse (g := fun q : X × G => q.2 * σ q.1) ?_ ?_ ?_ ?_
  · exact (hπ.prodMk (continuous_id.mul (hσ_cont.comp hπ).inv)).measurable
  · rw [range_splitMap π σ hσ]
    exact (isClosed_singleton.preimage (hπ.comp continuous_snd)).measurableSet
  · exact (continuous_snd.mul (hσ_cont.comp continuous_fst)).measurable
  · intro g
    exact snd_mul_section_fst π σ g

end Embedding

section Integral

variable {G X : Type*} [Group G] [MeasurableSpace G] [MeasurableSpace X]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem integral_eq_integral_integral_of_map_eq_prod
    {Θ : G → X × G} (hΘ : MeasurableEmbedding Θ) {μ : Measure G}
    {ν : Measure X} [SFinite ν] {ν' : Measure G} [SFinite ν'] (hmap : Measure.map Θ μ = ν.prod ν') {σ : X → G}
    (hrec : ∀ g, (Θ g).2 * σ (Θ g).1 = g) {f : G → E} (hf : Integrable f μ) :
    Integrable (fun x => ∫ k, f (k * σ x) ∂ν') ν ∧ ∫ g, f g ∂μ = ∫ x, ∫ k, f (k * σ x) ∂ν' ∂ν := by
  have hcomp : ∀ g, f ((Θ g).2 * σ (Θ g).1) = f g := fun g => by rw [hrec g]
  have hFi : Integrable (fun q : X × G => f (q.2 * σ q.1)) (ν.prod ν') := by
    rw [← hmap, hΘ.integrable_map_iff]
    refine hf.congr (Filter.Eventually.of_forall fun g => ?_)
    exact (hcomp g).symm
  refine ⟨hFi.integral_prod_left, ?_⟩
  calc ∫ g, f g ∂μ = ∫ g, f ((Θ g).2 * σ (Θ g).1) ∂μ := by simp only [hcomp]
    _ = ∫ q, f (q.2 * σ q.1) ∂(Measure.map Θ μ) := (hΘ.integral_map (fun q : X × G => f (q.2 * σ q.1))).symm
    _ = ∫ q, f (q.2 * σ q.1) ∂(ν.prod ν') := by rw [hmap]
    _ = ∫ x, ∫ k, f (k * σ x) ∂ν' ∂ν := integral_prod (fun q : X × G => f (q.2 * σ q.1)) hFi

omit [Group G] in

private theorem ae_mem_map_subtype_val {S : Set G} (hS : MeasurableSet S) (μ' : Measure S) :
    ∀ᵐ k ∂(Measure.map (Subtype.val : S → G) μ'), k ∈ S :=
  (ae_map_iff measurable_subtype_coe.aemeasurable hS).mpr (Filter.Eventually.of_forall fun k => k.2)

end Integral

end Splitting

namespace Unimodular

variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [LocallyCompactSpace K]
  [MeasurableSpace K] [BorelSpace K]

private theorem lintegral_inv_eq_of_comm (hcomm : ∀ a b : K, a * b = b * a) (μ : Measure K) [μ.IsHaarMeasure]
    [μ.Regular] (f : K → ℝ≥0∞) : ∫⁻ n, f n⁻¹ ∂μ = ∫⁻ n, f n ∂μ := by
  letI : CommGroup K := { (inferInstance : Group K) with mul_comm := hcomm }
  haveI : μ.IsInvInvariant := Measure.IsHaarMeasure.isInvInvariant_of_regular μ
  exact lintegral_inv_eq_self f

private theorem lintegral_inv_eq_of_comm' [SecondCountableTopology K] (hcomm : ∀ a b : K, a * b = b * a)
    (μ : Measure K) [μ.IsHaarMeasure] (f : K → ℝ≥0∞) : ∫⁻ n, f n⁻¹ ∂μ = ∫⁻ n, f n ∂μ :=
  lintegral_inv_eq_of_comm hcomm μ f

private theorem subgroup_mul_comm {G : Type*} [Group G] {A : Type*} [CommGroup A] (φ : A →* G)
    (a b : φ.range) : a * b = b * a := by
  obtain ⟨_, x, rfl⟩ := a
  obtain ⟨_, y, rfl⟩ := b
  ext
  simp only [Subgroup.coe_mul, ← map_mul, mul_comm]

end Unimodular

namespace Abelian

private theorem isMulRightInvariant_of_comm {H : Type*} [Group H] [MeasurableSpace H] (μ : Measure H)
    [μ.IsMulLeftInvariant] (hcomm : ∀ a b : H, a * b = b * a) : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have h : (fun x : H => x * g) = fun x : H => g * x := funext fun x => hcomm x g
  rw [h]
  exact map_mul_left_eq_self μ g

private theorem range_mul_comm {M G : Type*} [CommGroup M] [Group G] (φ : M →* G) (a b : φ.range) : a * b = b * a := by
  obtain ⟨x, hx⟩ := a.2
  obtain ⟨y, hy⟩ := b.2
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]

private theorem subgroupOf_mul_comm {G : Type*} [Group G] (H K : Subgroup G) (hcomm : ∀ a b : H, a * b = b * a)
    (a b : H.subgroupOf K) : a * b = b * a := by
  apply Subtype.ext
  apply Subtype.ext
  have ha : ((a : K) : G) ∈ H := Subgroup.mem_subgroupOf.mp a.2
  have hb : ((b : K) : G) ∈ H := Subgroup.mem_subgroupOf.mp b.2
  have := congrArg Subtype.val (hcomm ⟨_, ha⟩ ⟨_, hb⟩)
  simpa using this

end Abelian

namespace DensNorm

open scoped Pointwise

section Norm

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SigmaCompactSpace G] [WeaklyLocallyCompactSpace G]
  (H : Subgroup G) (μH : Measure H)

private def _root_.LanglandsTunnell.RankinSelberg.OnePlaceSplit.DensNorm.coeff (n : ℕ) : ℝ≥0∞ :=
  (2⁻¹ : ℝ≥0∞) ^ n *
    (1 + μH (((↑) : H → G) ⁻¹'
      ((CompactExhaustion.choice G (n + 1) : Set G) * (CompactExhaustion.choice G (n + 1) : Set G)⁻¹)))⁻¹

p2m_export "LanglandsTunnell.RankinSelberg.OnePlaceSplit.DensNorm" "coeff"
omit [IsTopologicalGroup G] [BorelSpace G] in
private theorem weight_eq (g : G) :
    weight H μH g = ∑' n : ℕ,
      coeff H μH n * (interior (CompactExhaustion.choice G (n + 1) : Set G)).indicator (fun _ => (1 : ℝ≥0∞)) g := by
  unfold HaarQuotient.weight
  rw [dif_pos ⟨inferInstance, inferInstance⟩]
  rfl

omit [IsTopologicalGroup G] [BorelSpace G] in
private theorem coeff_le (n : ℕ) : coeff H μH n ≤ (2⁻¹ : ℝ≥0∞) ^ n :=
  mul_le_of_le_one_right (by simp) (ENNReal.inv_le_one.mpr le_self_add)

private theorem lintegral_term_le [μH.IsMulRightInvariant] (n : ℕ) (g : G) :
    ∫⁻ x : H, coeff H μH n *
        (interior (CompactExhaustion.choice G (n + 1) : Set G)).indicator (fun _ => (1 : ℝ≥0∞)) ((x : G) * g) ∂μH ≤
      (2⁻¹ : ℝ≥0∞) ^ n := by
  set E : Set G := CompactExhaustion.choice G (n + 1) with hE
  set U : Set H := {x : H | (x : G) * g ∈ interior E} with hU
  have hUmeas : MeasurableSet U :=
    (isOpen_interior.preimage (continuous_subtype_val.mul continuous_const)).measurableSet
  have hfun : (fun x : H => coeff H μH n * (interior E).indicator (fun _ => (1 : ℝ≥0∞)) ((x : G) * g)) =
      fun x : H => U.indicator (fun _ => coeff H μH n) x := by
    funext x
    by_cases hx : x ∈ U
    · simp [Set.indicator_of_mem hx, Set.indicator_of_mem (show (x : G) * g ∈ interior E from hx)]
    · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show (x : G) * g ∉ interior E from hx)]
  rw [hfun, lintegral_indicator_const hUmeas]

  by_cases hne : U = ∅
  · simp [hne]
  obtain ⟨x₀, hx₀⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hsub : U ⊆ (fun x : H => x * x₀⁻¹) ⁻¹' (((↑) : H → G) ⁻¹' (E * E⁻¹)) := by
    intro x hx
    refine ⟨(x : G) * g, interior_subset hx, ((x₀ : G) * g)⁻¹, Set.inv_mem_inv.mpr (interior_subset hx₀), ?_⟩
    simp [mul_assoc]
  calc coeff H μH n * μH U ≤ coeff H μH n * μH ((fun x : H => x * x₀⁻¹) ⁻¹' (((↑) : H → G) ⁻¹' (E * E⁻¹))) :=
        mul_le_mul_right (measure_mono hsub) _
    _ = coeff H μH n * μH (((↑) : H → G) ⁻¹' (E * E⁻¹)) := by rw [measure_preimage_mul_right]
    _ ≤ (2⁻¹ : ℝ≥0∞) ^ n := by
        unfold coeff
        rw [mul_assoc]
        refine mul_le_of_le_one_right (by simp) ?_
        rw [← hE, ← ENNReal.div_eq_inv_mul]
        exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact le_add_self)

private theorem measurable_term (n : ℕ) (g : G) :
    Measurable fun x : H => coeff H μH n *
      (interior (CompactExhaustion.choice G (n + 1) : Set G)).indicator (fun _ => (1 : ℝ≥0∞)) ((x : G) * g) :=
  measurable_const.mul ((measurable_const.indicator isOpen_interior.measurableSet).comp
    (measurable_subtype_coe.mul_const g))

private theorem lintegral_weight_mul_ne_top [μH.IsMulRightInvariant] (g : G) :
    ∫⁻ x : H, weight H μH ((x : G) * g) ∂μH ≠ ⊤ := by
  simp_rw [weight_eq H μH]
  rw [lintegral_tsum fun n => (measurable_term H μH n g).aemeasurable]
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun n => lintegral_term_le H μH n g)
  rw [ENNReal.tsum_geometric]
  simp

private theorem lintegral_weight_mul_ne_zero [μH.IsHaarMeasure] (hH : IsClosed (H : Set G)) (g : G) :
    ∫⁻ x : H, weight H μH ((x : G) * g) ∂μH ≠ 0 := by
  obtain ⟨n, hn⟩ := (CompactExhaustion.choice G).exists_mem g
  have hg : g ∈ interior (CompactExhaustion.choice G (n + 1) : Set G) :=
    (CompactExhaustion.choice G).subset_interior_succ n hn
  set U : Set H := {x : H | (x : G) * g ∈ interior (CompactExhaustion.choice G (n + 1) : Set G)} with hU
  have hUopen : IsOpen U := isOpen_interior.preimage (continuous_subtype_val.mul continuous_const)
  have hU1 : (1 : H) ∈ U := by
    show ((1 : H) : G) * g ∈ interior (CompactExhaustion.choice G (n + 1) : Set G)
    simpa using hg

  have hcompact : IsCompact (((↑) : H → G) ⁻¹'
      ((CompactExhaustion.choice G (n + 1) : Set G) * (CompactExhaustion.choice G (n + 1) : Set G)⁻¹)) :=
    (hH.isClosedEmbedding_subtypeVal).isCompact_preimage
      (((CompactExhaustion.choice G).isCompact (n + 1)).mul ((CompactExhaustion.choice G).isCompact (n + 1)).inv)
  have hcoeff : coeff H μH n ≠ 0 := by
    unfold coeff
    refine mul_ne_zero (pow_ne_zero _ (by simp)) (ENNReal.inv_ne_zero.mpr ?_)
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hcompact.measure_lt_top.ne⟩

  have hterm : coeff H μH n * μH U ≤ ∫⁻ x : H, weight H μH ((x : G) * g) ∂μH := by
    rw [← lintegral_indicator_const hUopen.measurableSet]
    refine lintegral_mono fun x => ?_
    rw [weight_eq H μH]
    refine le_trans ?_ (ENNReal.le_tsum n)
    by_cases hx : x ∈ U
    · have hxg : (x : G) * g ∈ interior (CompactExhaustion.choice G (n + 1) : Set G) := hx
      simp [Set.indicator_of_mem hx, Set.indicator_of_mem hxg]
    · simp [Set.indicator_of_notMem hx]
  refine ne_of_gt (lt_of_lt_of_le ?_ hterm)
  exact ENNReal.mul_pos hcoeff (hUopen.measure_pos μH ⟨1, hU1⟩).ne'

omit [IsTopologicalGroup G] [BorelSpace G] in

private theorem weight_ne_top (g : G) : weight H μH g ≠ ⊤ := by
  rw [weight_eq]
  refine ne_top_of_le_ne_top (b := ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n) ?_ ?_
  · rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two]
    exact ENNReal.inv_ne_top.mpr (by simp)
  · refine ENNReal.tsum_le_tsum fun n => ?_
    refine le_trans (mul_le_of_le_one_right (by simp) ?_) (coeff_le H μH n)
    exact Set.indicator_le_self' (fun _ _ => zero_le_one) g |>.trans le_rfl

private theorem density_ne_top [μH.IsHaarMeasure] (hH : IsClosed (H : Set G)) (g : G) : density H μH g ≠ ⊤ :=
  ENNReal.div_ne_top (weight_ne_top H μH g) (lintegral_weight_mul_ne_zero H μH hH g)

end Norm

end DensNorm

section UnipotentFurniture

private theorem unipotent_mul_unipotent_neg {K : Type*} [Field K] (x : K) : unipotent x * unipotent (-x) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipotent, Matrix.mul_apply, Fin.sum_univ_two]

private theorem unipotent_inv {K : Type*} [Field K] (x : K) : (unipotent x)⁻¹ = unipotent (-x) :=
  inv_eq_of_mul_eq_one_right (unipotent_mul_unipotent_neg x)

private theorem isIntegralUnit_unipotent {K : Type*} [Field K] (O : ValuationSubring K) (r : O) :
    IntegralUnits.IsIntegralUnit O (unipotent (algebraMap O K r)) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [unipotent, one_mem, zero_mem, SetLike.coe_mem]
  · rw [unipotent_inv]
    fin_cases i <;> fin_cases j <;> simp [unipotent, one_mem, zero_mem, SetLike.coe_mem]

private theorem unipotent_integral_mem_localLevelOne_top
    (v : HeightOneSpectrum (𝓞 ℚ)) (r : v.adicCompletionIntegers ℚ) :
    unipotent (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) ∈
      AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ :=
  (LevelOne.mem_localLevelOne_top_iff v _).mpr (isIntegralUnit_unipotent _ r)

private theorem apply_mul_pow_eq_pow_mul {G : Type*} [Group G] (W : G → ℂ) (z : G) (om : ℂ)
    (hZ : ∀ g, W (g * z) = om * W g) (n : ℕ) (g : G) : W (g * z ^ n) = om ^ n * W g := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← mul_assoc, hZ, ih, pow_succ]; ring

end UnipotentFurniture

namespace Regroup

private def degreeEquiv : ℤ × ℤ ≃ ℤ × ℤ where
  toFun q := (q.1 - q.2, q.2)
  invFun p := (p.1 + p.2, p.2)
  left_inv q := by ext <;> simp
  right_inv p := by ext <;> simp

private theorem hasSum_fiber {f : ℤ × ℤ → ℂ} (hf0 : ∀ p : ℤ × ℤ, (p.2 < 0 ∨ p.1 < p.2) → f p = 0) (n : ℤ) :
    HasSum (fun p₂ : ℤ => f (n - p₂, p₂))
      (∑ p₂ ∈ Finset.range (n.toNat + 1), f (n - (p₂ : ℤ), (p₂ : ℤ))) := by
  have h : HasSum (fun p₂ : ℤ => f (n - p₂, p₂))
      (∑ p₂ ∈ (Finset.range (n.toNat + 1)).map Nat.castEmbedding, f (n - p₂, p₂)) :=
    hasSum_sum_of_ne_finset_zero ?_
  · rwa [Finset.sum_map] at h
  · intro p₂ hp₂
    apply hf0
    simp only [Finset.mem_map, Finset.mem_range, Nat.castEmbedding_apply, not_exists, not_and] at hp₂
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon

    have h3 : p₂ ≤ n := by omega
    exact hp₂ p₂.toNat (by omega) (by omega)

private theorem fiber_sum_eq_zero_of_neg {f : ℤ × ℤ → ℂ} (hf0 : ∀ p : ℤ × ℤ, (p.2 < 0 ∨ p.1 < p.2) → f p = 0)
    {n : ℤ} (hn : n < 0) : (∑ p₂ ∈ Finset.range (n.toNat + 1), f (n - (p₂ : ℤ), (p₂ : ℤ))) = 0 := by
  refine Finset.sum_eq_zero fun p₂ _ => hf0 _ ?_
  right; simp only; omega

private theorem hasSum_antidiagonal {f : ℤ × ℤ → ℂ} (hf0 : ∀ p : ℤ × ℤ, (p.2 < 0 ∨ p.1 < p.2) → f p = 0) {L : ℂ}
    (hf : HasSum f L) :
    HasSum (fun n : ℕ => ∑ p₂ ∈ Finset.range (n + 1), f ((n : ℤ) - (p₂ : ℤ), (p₂ : ℤ))) L := by

  have h1 : HasSum (fun q : ℤ × ℤ => f (degreeEquiv q)) L := (degreeEquiv.hasSum_iff).mpr hf

  have h2 : HasSum (fun n : ℤ => ∑ p₂ ∈ Finset.range (n.toNat + 1), f (n - (p₂ : ℤ), (p₂ : ℤ))) L :=
    HasSum.prod_fiberwise h1 (fun n => hasSum_fiber hf0 n)

  have h3 : HasSum ((fun n : ℤ => ∑ p₂ ∈ Finset.range (n.toNat + 1), f (n - (p₂ : ℤ), (p₂ : ℤ))) ∘
      (Nat.cast : ℕ → ℤ)) L :=
    (Nat.cast_injective.hasSum_iff ?_).mpr h2
  · refine h3.congr_fun ?_
    intro n
    simp only [Function.comp, Int.toNat_natCast]
  · intro n hn
    have hneg : n < 0 := by
      by_contra h
      push Not at h
      exact hn ⟨n.toNat, by omega⟩
    exact fiber_sum_eq_zero_of_neg hf0 hneg

private theorem summable_norm_antidiagonal {f : ℤ × ℤ → ℂ} (hf0 : ∀ p : ℤ × ℤ, (p.2 < 0 ∨ p.1 < p.2) → f p = 0)
    (hf : Summable fun p => ‖f p‖) :
    Summable (fun n : ℕ => ‖∑ p₂ ∈ Finset.range (n + 1), f ((n : ℤ) - (p₂ : ℤ), (p₂ : ℤ))‖) := by

  set g : ℤ × ℤ → ℂ := fun p => ((‖f p‖ : ℝ) : ℂ) with hg
  have hg0 : ∀ p : ℤ × ℤ, (p.2 < 0 ∨ p.1 < p.2) → g p = 0 := fun p hp => by simp [hg, hf0 p hp]
  have hgsum : HasSum g (((∑' p, ‖f p‖ : ℝ) : ℂ)) := by
    have := hf.hasSum
    exact (Complex.hasSum_ofReal).mpr this
  have hT := hasSum_antidiagonal hg0 hgsum

  refine Summable.of_norm_bounded (g := fun n : ℕ => ‖∑ p₂ ∈ Finset.range (n + 1), g ((n : ℤ) - (p₂ : ℤ), (p₂ : ℤ))‖)
    hT.summable.norm ?_
  intro n
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  calc ‖∑ p₂ ∈ Finset.range (n + 1), f ((n : ℤ) - (p₂ : ℤ), (p₂ : ℤ))‖
      ≤ ∑ p₂ ∈ Finset.range (n + 1), ‖f ((n : ℤ) - (p₂ : ℤ), (p₂ : ℤ))‖ := norm_sum_le _ _
    _ = ‖∑ p₂ ∈ Finset.range (n + 1), g ((n : ℤ) - (p₂ : ℤ), (p₂ : ℤ))‖ := by
        simp only [hg]
        rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_of_nonneg
          (Finset.sum_nonneg fun _ _ => norm_nonneg _)]

private theorem eq_inv_mul_of_hasSum_core {term : ℤ × ℤ → ℂ} (h0 : ∀ p : ℤ × ℤ, (p.2 < 0 ∨ p.1 < p.2) → term p = 0)
    {a : ℕ → ℂ} {x E : ℂ}
    (hfib : ∀ n : ℕ, ∑ p₂ ∈ Finset.range (n + 1), term ((n : ℤ) - (p₂ : ℤ), (p₂ : ℤ)) = a n * x ^ n)
    (hw2 : Summable (fun n : ℕ => ‖a n‖ * ‖x‖ ^ n) → (∑' n : ℕ, a n * x ^ n) * E = 1)
    {Y L : ℂ} (hL : HasSum (fun p => term p * Y) L) (habs : Y ≠ 0 → Summable fun p => ‖term p‖) :
    L = E⁻¹ * Y := by
  by_cases hY : Y = 0
  · subst hY
    simp only [mul_zero] at hL
    rw [hL.unique hasSum_zero, mul_zero]
  · have hT : HasSum term (L * Y⁻¹) := by
      have h := hL.mul_right Y⁻¹
      simpa only [mul_assoc, mul_inv_cancel₀ hY, mul_one] using h
    have hA := hasSum_antidiagonal h0 hT
    simp only [hfib] at hA
    have hsum : Summable fun n : ℕ => ‖a n‖ * ‖x‖ ^ n := by
      have h := summable_norm_antidiagonal h0 (habs hY)
      simpa only [hfib, norm_mul, norm_pow] using h
    have h1 : (L * Y⁻¹) * E = 1 := by rw [← hA.tsum_eq]; exact hw2 hsum
    have h2 : L * Y⁻¹ = E⁻¹ := eq_inv_of_mul_eq_one_left h1
    calc L = L * Y⁻¹ * Y := by rw [inv_mul_cancel_right₀ hY]
      _ = E⁻¹ * Y := by rw [h2]

end Regroup

namespace TermMatch

open Finset

variable {q lam om : ℂ}

private noncomputable def cellTerm (q om : ℂ) (seq : ℕ → ℂ) (u : ℕ → ℕ → ℂ) (n p₂ : ℕ) : ℂ :=
  q ^ (n - 2 * p₂) * (om ^ p₂ * seq (n - 2 * p₂)) * (q⁻¹ ^ (n - p₂) * u (n - p₂) p₂)

private theorem seq_mul_pow_eq (hq : q ≠ 0) (seq t : ℕ → ℂ) (hs0 : seq 0 = 1) (hs1 : seq 1 = lam / q)
    (hs : ∀ m, seq (m + 2) = (lam * seq (m + 1) - om * seq m) / q)
    (ht0 : t 0 = 1) (ht1 : t 1 = lam) (ht : ∀ m, t (m + 2) = lam * t (m + 1) - q * om * t m) :
    ∀ k, seq k * q ^ k = t k := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => simp [hs0, ht0]
  | one => rw [hs1, ht1, pow_one, div_mul_cancel₀ _ hq]
  | more m ih0 ih1 =>
    rw [hs, ht, ← ih0, ← ih1]
    field_simp
    ring

private theorem seq_eq_inv_pow_mul (hq : q ≠ 0) (seq t : ℕ → ℂ) (hs0 : seq 0 = 1) (hs1 : seq 1 = lam / q)
    (hs : ∀ m, seq (m + 2) = (lam * seq (m + 1) - om * seq m) / q)
    (ht0 : t 0 = 1) (ht1 : t 1 = lam) (ht : ∀ m, t (m + 2) = lam * t (m + 1) - q * om * t m) :
    ∀ k, seq k = q⁻¹ ^ k * t k := by
  intro k
  rw [← seq_mul_pow_eq hq seq t hs0 hs1 hs ht0 ht1 ht k, inv_pow]
  field_simp

private theorem sum_cellTerm_eq
    (hq : q ≠ 0) (seq t : ℕ → ℂ) (u : ℕ → ℕ → ℂ) (hseq : ∀ k, seq k = q⁻¹ ^ k * t k) (n : ℕ) :
    ∑ p₂ ∈ range (n / 2 + 1), cellTerm q om seq u n p₂ =
      (∑ k₂ ∈ range (n / 2 + 1), (q * om) ^ k₂ * t (n - 2 * k₂) * u (n - k₂) k₂) * q⁻¹ ^ n := by
  rw [sum_mul]
  refine sum_congr rfl fun p₂ hp₂ => ?_
  have h2 : 2 * p₂ ≤ n := by
    rw [mem_range] at hp₂
    omega
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 * p₂ := ⟨n - 2 * p₂, by omega⟩
  unfold cellTerm
  rw [hseq]
  have e1 : k + 2 * p₂ - 2 * p₂ = k := by omega
  have e2 : k + 2 * p₂ - p₂ = k + p₂ := by omega
  rw [e1, e2]
  simp only [inv_pow]
  field_simp
  ring

section Recursion

open UnramifiedWhittaker

variable (N : ℂ) (lam om : ℂ)

private theorem heckeRecursionSeq_zero : heckeRecursionSeq N lam om 0 = 1 := rfl

private theorem heckeRecursionSeq_one : heckeRecursionSeq N lam om 1 = lam / N := rfl

private theorem heckeRecursionSeq_add_two (m : ℕ) :
    heckeRecursionSeq N lam om (m + 2) =
      (lam * heckeRecursionSeq N lam om (m + 1) - om * heckeRecursionSeq N lam om m) / N := rfl

private theorem torusFactor_natCast (k : ℕ) : torusFactor N lam om (k : ℤ) = heckeRecursionSeq N lam om k := by
  unfold torusFactor
  rw [if_pos (Int.natCast_nonneg k), Int.toNat_natCast]

variable {N lam om}

private theorem heckeRecursionSeq_eq_inv_pow_mul (hN : N ≠ 0) (t : ℕ → ℂ) (ht0 : t 0 = 1) (ht1 : t 1 = lam)
    (ht : ∀ m, t (m + 2) = lam * t (m + 1) - N * om * t m) (k : ℕ) :
    heckeRecursionSeq N lam om k = N⁻¹ ^ k * t k :=
  seq_eq_inv_pow_mul hN (heckeRecursionSeq N lam om) t (heckeRecursionSeq_zero N lam om)
    (heckeRecursionSeq_one N lam om) (heckeRecursionSeq_add_two N lam om) ht0 ht1 ht k

private theorem sum_cellTerm_heckeRecursionSeq_eq (hN : N ≠ 0) (t : ℕ → ℂ) (ht0 : t 0 = 1) (ht1 : t 1 = lam)
    (ht : ∀ m, t (m + 2) = lam * t (m + 1) - N * om * t m) (u : ℕ → ℕ → ℂ) (n : ℕ) :
    ∑ p₂ ∈ range (n / 2 + 1), cellTerm N om (heckeRecursionSeq N lam om) u n p₂ =
      (∑ k₂ ∈ range (n / 2 + 1), (N * om) ^ k₂ * t (n - 2 * k₂) * u (n - k₂) k₂) * N⁻¹ ^ n :=
  sum_cellTerm_eq hN (heckeRecursionSeq N lam om) t u (heckeRecursionSeq_eq_inv_pow_mul hN t ht0 ht1 ht) n

end Recursion

end TermMatch

namespace Fibre

open Finset TermMatch

private noncomputable def cellValue (q om : ℂ) (tf : ℤ → ℂ) (uZ : ℤ → ℤ → ℂ) (p : ℤ × ℤ) : ℂ :=
  om ^ p.2.toNat * tf (p.1 - p.2) * (q⁻¹ ^ p.1 * uZ p.1 p.2)

private noncomputable def seriesTerm (q om : ℂ) (r : ℝ) (s : ℂ) (tf : ℤ → ℂ) (uZ : ℤ → ℤ → ℂ) (p : ℤ × ℤ) : ℂ :=
  q ^ (p.1 - p.2) * cellValue q om tf uZ p * (((r ^ (-(p.1 + p.2)) : ℝ) : ℂ) ^ (s - 1 / 2))

variable {q om : ℂ} {r : ℝ} {s : ℂ} {tf : ℤ → ℂ} {uZ : ℤ → ℤ → ℂ}

private theorem seriesTerm_eq_zero (huZ_off : ∀ m₁ m₂ : ℤ, (m₂ < 0 ∨ m₁ < m₂) → uZ m₁ m₂ = 0) (p : ℤ × ℤ)
    (hp : p.2 < 0 ∨ p.1 < p.2) : seriesTerm q om r s tf uZ p = 0 := by
  simp only [seriesTerm, cellValue, huZ_off p.1 p.2 hp, mul_zero, zero_mul]

private theorem seriesTerm_eq_cellTerm_mul {seq : ℕ → ℂ} (htf : ∀ k : ℕ, tf k = seq k) {u : ℕ → ℕ → ℂ}
    (huZ_cone : ∀ k₁ k₂ : ℕ, k₂ ≤ k₁ → uZ k₁ k₂ = u k₁ k₂) (n p₂ : ℕ) (h : 2 * p₂ ≤ n) :
    seriesTerm q om r s tf uZ ((n : ℤ) - (p₂ : ℤ), (p₂ : ℤ)) =
      cellTerm q om seq u n p₂ * (((r ^ (-(n : ℤ)) : ℝ) : ℂ) ^ (s - 1 / 2)) := by
  have h1 : ((n : ℤ) - (p₂ : ℤ)) - (p₂ : ℤ) = ((n - 2 * p₂ : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub (by omega : 2 * p₂ ≤ n)]; ring
  have h2 : (n : ℤ) - (p₂ : ℤ) = ((n - p₂ : ℕ) : ℤ) := by push_cast [Nat.cast_sub (by omega : p₂ ≤ n)]; ring
  have h3 : ((n : ℤ) - (p₂ : ℤ)) + (p₂ : ℤ) = (n : ℤ) := by ring
  unfold seriesTerm cellValue
  simp only
  rw [h3, h1, h2, Int.toNat_natCast, zpow_natCast, zpow_natCast, htf, huZ_cone (n - p₂) p₂ (by omega), cellTerm]
  ring

private theorem sum_seriesTerm_eq {seq : ℕ → ℂ} (htf : ∀ k : ℕ, tf k = seq k) {u : ℕ → ℕ → ℂ}
    (huZ_off : ∀ m₁ m₂ : ℤ, (m₂ < 0 ∨ m₁ < m₂) → uZ m₁ m₂ = 0)
    (huZ_cone : ∀ k₁ k₂ : ℕ, k₂ ≤ k₁ → uZ k₁ k₂ = u k₁ k₂) (n : ℕ) :
    ∑ p₂ ∈ range (n + 1), seriesTerm q om r s tf uZ ((n : ℤ) - (p₂ : ℤ), (p₂ : ℤ)) =
      (∑ p₂ ∈ range (n / 2 + 1), cellTerm q om seq u n p₂) * (((r ^ (-(n : ℤ)) : ℝ) : ℂ) ^ (s - 1 / 2)) := by
  rw [sum_mul, ← sum_subset (range_subset_range.mpr (by omega : n / 2 + 1 ≤ n + 1))]
  · refine sum_congr rfl fun p₂ hp₂ => ?_
    rw [mem_range] at hp₂
    exact seriesTerm_eq_cellTerm_mul htf huZ_cone n p₂ (by omega)
  · intro p₂ hp₂ hp₂'
    rw [mem_range] at hp₂ hp₂'
    apply seriesTerm_eq_zero huZ_off
    right; simp only; omega

private theorem inv_pow_mul_weight_eq (hr : 0 < r) (n : ℕ) :
    ((r : ℂ))⁻¹ ^ n * (((r ^ (-(n : ℤ)) : ℝ) : ℂ) ^ (s - 1 / 2)) = ((r : ℂ) ^ (-(s + 1 / 2))) ^ n := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  set y : ℝ := -(n : ℝ) with hy
  have hyz : (r ^ (-(n : ℤ)) : ℝ) = r ^ y := by
    rw [hy, show (-(n : ℝ)) = ((-(n : ℤ) : ℤ) : ℝ) by push_cast; ring, Real.rpow_intCast]
  have e1 : (((r ^ (-(n : ℤ)) : ℝ) : ℂ) ^ (s - 1 / 2)) = (r : ℂ) ^ (Complex.ofReal y * (s - 1 / 2)) := by
    rw [hyz, ← Complex.cpow_mul_ofReal_nonneg hr.le]
  have e2 : ((r : ℂ))⁻¹ ^ n = (r : ℂ) ^ (Complex.ofReal y) := by
    rw [show Complex.ofReal y = ((-(n : ℤ) : ℤ) : ℂ) by rw [hy]; push_cast; ring, Complex.cpow_intCast,
      zpow_neg, zpow_natCast, inv_pow]
  rw [e1, e2, ← Complex.cpow_add _ _ hr0, ← Complex.cpow_nat_mul]
  congr 1
  rw [hy]
  push_cast
  ring

end Fibre

namespace CauchyWrapper

open Polynomial Finset

private theorem eval_eq_tsum (P : ℂ[X]) (x : ℂ) : P.eval x = ∑' j, P.coeff j * x ^ j := by
  rw [eval_eq_sum_range, tsum_eq_sum (s := range (P.natDegree + 1))]
  intro j hj
  rw [mem_range, not_lt] at hj
  rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]

private theorem summable_norm_coeff_mul_pow (P : ℂ[X]) (x : ℂ) :
    Summable fun j => ‖P.coeff j * x ^ j‖ := by
  refine summable_of_ne_finset_zero (s := range (P.natDegree + 1)) fun j hj => ?_
  rw [mem_range, not_lt] at hj
  rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul, norm_zero]

private theorem tsum_mul_eval_eq_one {a : ℕ → ℂ} {P : ℂ[X]} {x : ℂ}
    (hsum : Summable fun n => ‖a n‖ * ‖x‖ ^ n)
    (hformal : ∀ n, ∑ kl ∈ antidiagonal n, a kl.1 * P.coeff kl.2 = if n = 0 then 1 else 0) :
    (∑' n, a n * x ^ n) * P.eval x = 1 := by
  have hf : Summable fun n => ‖a n * x ^ n‖ := by
    refine hsum.congr fun n => ?_
    rw [norm_mul, norm_pow]
  rw [eval_eq_tsum, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf
    (summable_norm_coeff_mul_pow P x)]
  have hterm : ∀ n, (∑ kl ∈ antidiagonal n, a kl.1 * x ^ kl.1 * (P.coeff kl.2 * x ^ kl.2)) =
      if n = 0 then (1 : ℂ) else 0 := by
    intro n
    have h1 : ∀ kl ∈ antidiagonal n, a kl.1 * x ^ kl.1 * (P.coeff kl.2 * x ^ kl.2) =
        a kl.1 * P.coeff kl.2 * x ^ n := by
      intro kl hkl
      rw [← mem_antidiagonal.mp hkl, pow_add]
      ring
    rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, hformal n]
    split_ifs with hn
    · subst hn
      simp
    · simp
  rw [tsum_congr hterm]
  exact tsum_ite_eq 0 1

private theorem formal_inverse_of_mk_mul_coe_eq_one {a : ℕ → ℂ} {P : ℂ[X]}
    (h : PowerSeries.mk a * (P : PowerSeries ℂ) = 1) (n : ℕ) :
    ∑ kl ∈ antidiagonal n, a kl.1 * P.coeff kl.2 = if n = 0 then 1 else 0 := by
  have hn := congrArg (PowerSeries.coeff n) h
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_one] at hn
  rw [← hn]
  refine Finset.sum_congr rfl fun kl _ => ?_
  rw [PowerSeries.coeff_mk, Polynomial.coeff_coe]

private theorem tsum_mul_eval_eq_one_of_mk_mul_coe_eq_one {a : ℕ → ℂ} {P : ℂ[X]} {x : ℂ}
    (h : PowerSeries.mk a * (P : PowerSeries ℂ) = 1) (hsum : Summable fun n => ‖a n‖ * ‖x‖ ^ n) :
    (∑' n, a n * x ^ n) * P.eval x = 1 :=
  tsum_mul_eval_eq_one hsum (formal_inverse_of_mk_mul_coe_eq_one h)

end CauchyWrapper

namespace GGlue

variable {N lam om : ℂ}

private theorem pow_mul_seq_zero : N ^ 0 * heckeRecursionSeq N lam om 0 = 1 := by
  simp [heckeRecursionSeq]

private theorem pow_mul_seq_one (hN : N ≠ 0) : N ^ 1 * heckeRecursionSeq N lam om 1 = lam := by
  simp only [heckeRecursionSeq, pow_one]
  field_simp

private theorem pow_mul_seq_add_two (hN : N ≠ 0) (m : ℕ) :
    N ^ (m + 2) * heckeRecursionSeq N lam om (m + 2) =
      lam * (N ^ (m + 1) * heckeRecursionSeq N lam om (m + 1)) - N * om * (N ^ m * heckeRecursionSeq N lam om m) := by
  rw [TermMatch.heckeRecursionSeq_add_two]
  field_simp
  ring

end GGlue

namespace SplitIso

section Iso

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H]
  (π : G →* H) (ι : H →* G)

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] in

private theorem mul_inv_section_mem_ker (hι : ∀ x, π (ι x) = x) (g : G) : g * (ι (π g))⁻¹ ∈ π.ker := by
  simp [MonoidHom.mem_ker, hι]

private noncomputable def sectionSplitting (hπ : Continuous π) (hι_cont : Continuous ι) (hι : ∀ x, π (ι x) = x)
    (hcomm : ∀ x (k : G), π k = 1 → ι x * k = k * ι x) : G ≃ₜ* H × π.ker where
  toFun g := (π g, ⟨g * (ι (π g))⁻¹, mul_inv_section_mem_ker π ι hι g⟩)
  invFun p := (p.2 : G) * ι p.1
  left_inv g := by simp
  right_inv p := by
    obtain ⟨x, k, hk⟩ := p
    have hk' : π k = 1 := hk
    ext
    · simp [hk', hι]
    · simp [hk', hι]
  map_mul' g g' := by
    ext
    · simp
    · simp only [map_mul, mul_inv_rev]
      have h := hcomm (π g) (g' * (ι (π g'))⁻¹) (by simp [hι])
      calc g * g' * ((ι (π g'))⁻¹ * (ι (π g))⁻¹)
          = g * ((g' * (ι (π g'))⁻¹) * (ι (π g))⁻¹) := by group
        _ = g * ((ι (π g))⁻¹ * (g' * (ι (π g'))⁻¹)) := by
            congr 1
            exact (mul_inv_eq_iff_eq_mul.mpr (by rw [mul_assoc, ← h, ← mul_assoc, inv_mul_cancel, one_mul])).trans
              rfl
        _ = g * (ι (π g))⁻¹ * (g' * (ι (π g'))⁻¹) := by group
  continuous_toFun := by
    refine hπ.prodMk (Continuous.subtype_mk ?_ _)
    exact continuous_id.mul (hι_cont.comp hπ).inv
  continuous_invFun := continuous_subtype_val.comp continuous_snd |>.mul (hι_cont.comp continuous_fst)

private theorem sectionSplitting_apply (hπ : Continuous π) (hι_cont : Continuous ι) (hι : ∀ x, π (ι x) = x)
    (hcomm : ∀ x (k : G), π k = 1 → ι x * k = k * ι x) (g : G) :
    sectionSplitting π ι hπ hι_cont hι hcomm g = (π g, ⟨g * (ι (π g))⁻¹, mul_inv_section_mem_ker π ι hι g⟩) :=
  rfl

private theorem sectionSplitting_symm_apply (hπ : Continuous π) (hι_cont : Continuous ι) (hι : ∀ x, π (ι x) = x)
    (hcomm : ∀ x (k : G), π k = 1 → ι x * k = k * ι x) (p : H × π.ker) :
    (sectionSplitting π ι hπ hι_cont hι hcomm).symm p = (p.2 : G) * ι p.1 :=
  rfl

end Iso

end SplitIso

namespace Admissible

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
variable (H : Subgroup G)

private theorem measurable_coe_mul : Measurable (fun p : H × G => (p.1 : G) * p.2) :=
  (measurable_subtype_coe.comp measurable_fst).mul measurable_snd

variable {H}

section Lintegral

variable [MeasurableInv G] (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ] (μH : Measure H) [SFinite μH]

private theorem lintegral_mul_eq_of_invariant (hinv : ∀ f : H → ℝ≥0∞, ∫⁻ n, f n⁻¹ ∂μH = ∫⁻ n, f n ∂μH)
    {ρ ρ' : G → ℝ≥0∞} (hρ : Measurable ρ) (hρ' : Measurable ρ')
    (hρ1 : ∀ g, ∫⁻ n : H, ρ ((n : G) * g) ∂μH = 1) (hρ'1 : ∀ g, ∫⁻ n : H, ρ' ((n : G) * g) ∂μH = 1)
    {φ : G → ℝ≥0∞} (hφ : AEMeasurable φ μ) (hφinv : ∀ (n : H) (g : G), φ ((n : G) * g) = φ g) :
    ∫⁻ g, φ g * ρ g ∂μ = ∫⁻ g, φ g * ρ' g ∂μ := by

  have hmeas : AEMeasurable (fun p : H × G => φ p.2 * ρ p.2 * ρ' ((p.1 : G) * p.2)) (μH.prod μ) :=
    (hφ.comp_snd.mul (hρ.comp measurable_snd).aemeasurable).mul (hρ'.comp (measurable_coe_mul H)).aemeasurable
  calc ∫⁻ g, φ g * ρ g ∂μ
      = ∫⁻ g, ∫⁻ n : H, φ g * ρ g * ρ' ((n : G) * g) ∂μH ∂μ := by
        refine lintegral_congr fun g => ?_
        rw [lintegral_const_mul (φ g * ρ g) (f := fun n : H => ρ' ((n : G) * g))
          (hρ'.comp (measurable_subtype_coe.mul_const g)), hρ'1 g, mul_one]
    _ = ∫⁻ n : H, ∫⁻ g, φ g * ρ g * ρ' ((n : G) * g) ∂μ ∂μH :=
        lintegral_lintegral_swap hmeas.prod_swap
    _ = ∫⁻ n : H, ∫⁻ g, φ g * ρ ((n : G)⁻¹ * g) * ρ' g ∂μ ∂μH := by
        refine lintegral_congr fun n => ?_

        rw [← lintegral_mul_left_eq_self (fun g => φ g * ρ ((n : G)⁻¹ * g) * ρ' g) (n : G)]
        refine lintegral_congr fun g => ?_
        simp only [inv_mul_cancel_left, hφinv n g]
    _ = ∫⁻ g, ∫⁻ n : H, φ g * ρ ((n : G)⁻¹ * g) * ρ' g ∂μH ∂μ := by
        refine (lintegral_lintegral_swap ?_).symm
        exact ((hφ.comp_snd.mul
          (hρ.comp ((measurable_subtype_coe.comp measurable_fst).inv.mul measurable_snd)).aemeasurable).mul
            (hρ'.comp measurable_snd).aemeasurable).prod_swap
    _ = ∫⁻ g, φ g * ρ' g ∂μ := by
        refine lintegral_congr fun g => ?_
        have h1 : ∫⁻ n : H, ρ ((n : G)⁻¹ * g) ∂μH = 1 := by
          rw [← hρ1 g, ← hinv (fun n : H => ρ ((n : G) * g))]
          simp only [Subgroup.coe_inv]
        calc ∫⁻ n : H, φ g * ρ ((n : G)⁻¹ * g) * ρ' g ∂μH
            = ∫⁻ n : H, (φ g * ρ' g) * ρ ((n : G)⁻¹ * g) ∂μH := by
              refine lintegral_congr fun n => ?_; ring
          _ = φ g * ρ' g := by
              rw [lintegral_const_mul (φ g * ρ' g) (f := fun n : H => ρ ((n : G)⁻¹ * g))
                (hρ.comp (measurable_subtype_coe.inv.mul_const g)), h1, mul_one]

end Lintegral

section Descent

variable (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ] (μH : Measure H) [SFinite μH]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

private theorem measurePreserving_coe_mul :
    MeasurePreserving (fun p : H × G => (p.1, (p.1 : G) * p.2)) (μH.prod μ) (μH.prod μ) :=
  (MeasurePreserving.id μH).skew_product (g := fun n : H => fun g : G => (n : G) * g) (measurable_coe_mul H)
    (ae_of_all _ fun n => map_mul_left_eq_self μ (n : G))

private theorem measurePreserving_coe_inv_mul [MeasurableInv G] :
    MeasurePreserving (fun p : H × G => (p.1, (p.1 : G)⁻¹ * p.2)) (μH.prod μ) (μH.prod μ) :=
  (MeasurePreserving.id μH).skew_product (g := fun n : H => fun g : G => (n : G)⁻¹ * g)
    ((measurable_subtype_coe.comp measurable_fst).inv.mul measurable_snd)
    (ae_of_all _ fun n => map_mul_left_eq_self μ (n : G)⁻¹)

private theorem ae_ae_mul_notMem {S : Set G} (hS : MeasurableSet S) (hS0 : μ S = 0) :
    ∀ᵐ g ∂μ, ∀ᵐ n : H ∂μH, (n : G) * g ∉ S := by
  have hT : (μH.prod μ) ((fun p : H × G => (p.1 : G) * p.2) ⁻¹' S) = 0 := by
    have h1 : (fun p : H × G => (p.1 : G) * p.2) ⁻¹' S =
        (fun p : H × G => (p.1, (p.1 : G) * p.2)) ⁻¹' (Set.univ ×ˢ S) := by
      ext p; simp
    rw [h1, (measurePreserving_coe_mul μ μH).measure_preimage (MeasurableSet.univ.prod hS).nullMeasurableSet,
      Measure.prod_prod, hS0, mul_zero]
  have hT' : (μ.prod μH) (Prod.swap ⁻¹' ((fun p : H × G => (p.1 : G) * p.2) ⁻¹' S)) = 0 := by
    rw [(Measure.measurePreserving_swap (μ := μ) (ν := μH)).measure_preimage
      (measurable_coe_mul H hS).nullMeasurableSet, hT]
  have h3 : ∀ᵐ q : G × H ∂μ.prod μH, (q.2 : G) * q.1 ∉ S := by
    rw [ae_iff]
    convert hT' using 2
    ext q; simp
  exact Measure.ae_ae_of_ae_prod h3

private theorem aestronglyMeasurable_of_invariant {ρ : G → ℝ≥0∞} (hρ : Measurable ρ)
    (hρ1 : ∀ g, ∫⁻ n : H, ρ ((n : G) * g) ∂μH = 1) (hρt : ∀ g, ρ g ≠ ∞)
    {f : G → E} (hfinv : ∀ (n : H) (g : G), f ((n : G) * g) = f g)
    (hf : AEStronglyMeasurable f (μ.withDensity ρ)) : AEStronglyMeasurable f μ := by
  set f₀ := hf.mk f with hf₀def
  have hf₀ : StronglyMeasurable f₀ := hf.stronglyMeasurable_mk
  have hae : ∀ᵐ g ∂μ, ρ g ≠ 0 → f g = f₀ g := (ae_withDensity_iff hρ).mp hf.ae_eq_mk

  set S := toMeasurable μ {g | ¬ (ρ g ≠ 0 → f g = f₀ g)} with hSdef
  have hSm : MeasurableSet S := measurableSet_toMeasurable _ _
  have hS0 : μ S = 0 := by rw [hSdef, measure_toMeasurable]; exact hae
  have hgood : ∀ g, g ∉ S → ρ g ≠ 0 → f g = f₀ g := fun g hg => by
    by_contra h; exact hg (subset_toMeasurable _ _ h)

  refine ⟨fun g => ∫ n : H, (ρ ((n : G) * g)).toReal • f₀ ((n : G) * g) ∂μH, ?_, ?_⟩
  · have : StronglyMeasurable (fun q : G × H => (ρ ((q.2 : G) * q.1)).toReal • f₀ ((q.2 : G) * q.1)) := by
      have hm : Measurable (fun q : G × H => (q.2 : G) * q.1) :=
        (measurable_subtype_coe.comp measurable_snd).mul measurable_fst
      exact ((hρ.comp hm).ennreal_toReal.stronglyMeasurable).smul (hf₀.comp_measurable hm)
    exact this.integral_prod_right'
  · filter_upwards [ae_ae_mul_notMem μ μH hSm hS0] with g hg
    have h1 : (fun n : H => (ρ ((n : G) * g)).toReal • f₀ ((n : G) * g)) =ᵐ[μH]
        fun n : H => (ρ ((n : G) * g)).toReal • f g := by
      filter_upwards [hg] with n hn
      by_cases h0 : ρ ((n : G) * g) = 0
      · simp [h0]
      · rw [← hgood _ hn h0, hfinv]
    rw [integral_congr_ae h1, integral_smul_const, integral_toReal (f := fun n : H => ρ ((n : G) * g))
      (hρ.comp (measurable_subtype_coe.mul_const g)).aemeasurable
      (ae_of_all _ fun n => lt_top_iff_ne_top.mpr (hρt _)), hρ1 g, ENNReal.toReal_one, one_smul]

end Descent

section Bochner

variable [MeasurableInv G] (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ] (μH : Measure H) [SFinite μH]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [MeasurableMul₂ G] [MeasurableInv G] [SFinite μH] in

private theorem lintegral_inv_mul_eq_one (hinv : ∀ f : H → ℝ≥0∞, ∫⁻ n, f n⁻¹ ∂μH = ∫⁻ n, f n ∂μH)
    {ρ : G → ℝ≥0∞} (hρ1 : ∀ g, ∫⁻ n : H, ρ ((n : G) * g) ∂μH = 1) (g : G) :
    ∫⁻ n : H, ρ ((n : G)⁻¹ * g) ∂μH = 1 := by
  rw [← hρ1 g, ← hinv (fun n : H => ρ ((n : G) * g))]
  simp only [Subgroup.coe_inv]

omit [Group G] [MeasurableMul₂ G] [MeasurableInv G] [μ.IsMulLeftInvariant] [SFinite μ] [CompleteSpace E] in

private theorem integrable_toReal_smul_of_integrable_withDensity {ρ : G → ℝ≥0∞} (hρ : Measurable ρ)
    (hρt : ∀ g, ρ g ≠ ∞) {f : G → E} (hfi : Integrable f (μ.withDensity ρ)) :
    Integrable (fun g => (ρ g).toReal • f g) μ :=
  (integrable_withDensity_iff_integrable_smul' hρ (ae_of_all _ fun g => lt_top_iff_ne_top.mpr (hρt g))).mp hfi

private theorem integral_withDensity_eq_of_invariant (hinv : ∀ f : H → ℝ≥0∞, ∫⁻ n, f n⁻¹ ∂μH = ∫⁻ n, f n ∂μH)
    {ρ ρ' : G → ℝ≥0∞} (hρ : Measurable ρ) (hρ' : Measurable ρ')
    (hρ1 : ∀ g, ∫⁻ n : H, ρ ((n : G) * g) ∂μH = 1) (hρ'1 : ∀ g, ∫⁻ n : H, ρ' ((n : G) * g) ∂μH = 1)
    (hρt : ∀ g, ρ g ≠ ∞) (hρ't : ∀ g, ρ' g ≠ ∞)
    {f : G → E} (hfinv : ∀ (n : H) (g : G), f ((n : G) * g) = f g)
    (hfi : Integrable f (μ.withDensity ρ)) :
    Integrable f (μ.withDensity ρ') ∧
      ∫ g, f g ∂μ.withDensity ρ' = ∫ g, f g ∂μ.withDensity ρ := by
  have hfm : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_invariant μ μH hρ hρ1 hρt hfinv hfi.aestronglyMeasurable
  have hf' : ∀ (n : H) (g : G), f ((n : G)⁻¹ * g) = f g := fun n g => by
    simpa only [Subgroup.coe_inv] using hfinv n⁻¹ g
  have hρ'lt : ∀ g, ρ' g < ∞ := fun g => lt_top_iff_ne_top.mpr (hρ't g)
  have hρlt : ∀ g, ρ g < ∞ := fun g => lt_top_iff_ne_top.mpr (hρt g)

  set A : H × G → E := fun p => (ρ p.2).toReal • ((ρ' ((p.1 : G) * p.2)).toReal • f p.2) with hAdef
  set B : H × G → E := fun p => (ρ ((p.1 : G)⁻¹ * p.2)).toReal • ((ρ' p.2).toReal • f p.2) with hBdef
  have hΨ := measurePreserving_coe_inv_mul μ μH
  have hAB : A ∘ (fun p : H × G => (p.1, (p.1 : G)⁻¹ * p.2)) = B := by
    funext p
    simp only [hAdef, hBdef, Function.comp, mul_inv_cancel_left, hf']
  have hA_meas : AEStronglyMeasurable A (μH.prod μ) := by
    have h1 : Measurable fun p : H × G => (ρ p.2).toReal := (hρ.comp measurable_snd).ennreal_toReal
    have h2 : Measurable fun p : H × G => (ρ' ((p.1 : G) * p.2)).toReal :=
      (hρ'.comp (measurable_coe_mul H)).ennreal_toReal
    exact h1.aestronglyMeasurable.smul (h2.aestronglyMeasurable.smul hfm.comp_snd)

  have hρf : Integrable (fun g => (ρ g).toReal • f g) μ :=
    integrable_toReal_smul_of_integrable_withDensity μ hρ hρt hfi
  have hA_int : Integrable A (μH.prod μ) := by
    refine (integrable_prod_iff' hA_meas).mpr ⟨ae_of_all _ fun g => ?_, ?_⟩
    · have : Integrable (fun n : H => (ρ' ((n : G) * g)).toReal) μH :=
        integrable_toReal_of_lintegral_ne_top (hρ'.comp (measurable_subtype_coe.mul_const g)).aemeasurable
          (by rw [hρ'1 g]; exact ENNReal.one_ne_top)
      exact (this.smul_const (f g)).smul ((ρ g).toReal)
    · have hnorm : (fun g => ∫ n : H, ‖A (n, g)‖ ∂μH) = fun g => ‖(ρ g).toReal • f g‖ := by
        funext g
        have h1 : ∀ n : H, ‖A (n, g)‖ = (ρ g).toReal * ((ρ' ((n : G) * g)).toReal * ‖f g‖) := fun n => by
          simp only [hAdef, norm_smul, Real.norm_of_nonneg ENNReal.toReal_nonneg]
        simp_rw [h1]
        rw [integral_const_mul, integral_mul_const, integral_toReal (f := fun n : H => ρ' ((n : G) * g))
          (hρ'.comp (measurable_subtype_coe.mul_const g)).aemeasurable (ae_of_all _ fun n => hρ'lt _),
          hρ'1 g, ENNReal.toReal_one, one_mul, norm_smul, Real.norm_of_nonneg ENNReal.toReal_nonneg]
      rw [hnorm]
      exact hρf.norm
  have hB_int : Integrable B (μH.prod μ) := by
    rw [← hAB]; exact hΨ.integrable_comp_of_integrable hA_int

  have hA_iter : ∫ p, A p ∂μH.prod μ = ∫ g, (ρ g).toReal • f g ∂μ := by
    rw [integral_prod_symm A hA_int]
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    simp only [hAdef]
    rw [integral_smul, integral_smul_const, integral_toReal (f := fun n : H => ρ' ((n : G) * g))
      (hρ'.comp (measurable_subtype_coe.mul_const g)).aemeasurable (ae_of_all _ fun n => hρ'lt _),
      hρ'1 g, ENNReal.toReal_one, one_smul]
  have hB_inner : ∀ g, ∫ n : H, B (n, g) ∂μH = (ρ' g).toReal • f g := fun g => by
    simp only [hBdef]
    rw [integral_smul_const, integral_toReal (f := fun n : H => ρ ((n : G)⁻¹ * g))
      (hρ.comp (measurable_subtype_coe.inv.mul_const g)).aemeasurable (ae_of_all _ fun n => hρlt _),
      lintegral_inv_mul_eq_one μH hinv hρ1 g, ENNReal.toReal_one, one_smul]
  have hB_iter : ∫ p, B p ∂μH.prod μ = ∫ g, (ρ' g).toReal • f g ∂μ := by
    rw [integral_prod_symm B hB_int]
    exact integral_congr_ae (ae_of_all _ hB_inner)
  have hAB_int : ∫ p, A p ∂μH.prod μ = ∫ p, B p ∂μH.prod μ := by
    have h := integral_map (μ := μH.prod μ) hΨ.measurable.aemeasurable
      (f := A) (by rw [hΨ.map_eq]; exact hA_meas)
    rw [hΨ.map_eq] at h
    rw [h, ← hAB]; rfl
  refine ⟨?_, ?_⟩
  · rw [integrable_withDensity_iff_integrable_smul' hρ' (ae_of_all _ hρ'lt)]
    have := hB_int.integral_prod_right
    exact this.congr (ae_of_all _ hB_inner)
  · rw [integral_withDensity_eq_integral_toReal_smul hρ' (ae_of_all _ hρ'lt),
      integral_withDensity_eq_integral_toReal_smul hρ (ae_of_all _ hρlt), ← hB_iter, ← hAB_int, hA_iter]

end Bochner

end Admissible

namespace Small

private theorem ofReal_norm_term (a : ℂ) {w : ℝ} (hw : 0 < w) (s : ℂ) {c : ℝ} (hc : 0 ≤ c) :
    ((‖a * ((w : ℝ) : ℂ) ^ (s - 1 / 2) * (c : ℂ)‖ : ℝ) : ℂ) =
      (((‖a‖ : ℝ) : ℂ) * (1 : ℂ)) * ((w : ℝ) : ℂ) ^ (((s.re : ℝ) : ℂ) - 1 / 2) * (c : ℂ) := by
  have h1 : ‖((w : ℝ) : ℂ) ^ (s - 1 / 2)‖ = w ^ (s.re - 1 / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hw]
    simp
  have h2 : ((w : ℝ) : ℂ) ^ (((s.re : ℝ) : ℂ) - 1 / 2) = ((w ^ (s.re - 1 / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hw.le]
    push_cast
    ring_nf
  rw [norm_mul, norm_mul, h1, h2, Complex.norm_real, Real.norm_of_nonneg hc]
  push_cast
  ring

private theorem ofReal_norm_pair (x y : ℂ) {w : ℝ} (hw : 0 < w) (s : ℂ) :
    ((‖(x * y) * ((w : ℝ) : ℂ) ^ (s - 1 / 2)‖ : ℝ) : ℂ) =
      (((‖x * y‖ : ℝ) : ℂ) * (1 : ℂ)) * ((w : ℝ) : ℂ) ^ (((s.re : ℝ) : ℂ) - 1 / 2) := by
  have h := ofReal_norm_term (x * y) hw s (zero_le_one' ℝ)
  simp only [Complex.ofReal_one] at h
  rw [mul_one, mul_one] at h
  exact h

section Integral

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

private theorem integrable_norm_pair {W F : α → ℂ} {w : α → ℝ} (hw : ∀ g, 0 < w g) (s : ℂ)
    (hint : Integrable (fun g => (W g * F g) * ((w g : ℝ) : ℂ) ^ (s - 1 / 2)) μ) :
    Integrable (fun g => (((‖W g * F g‖ : ℝ) : ℂ) * (1 : ℂ)) * ((w g : ℝ) : ℂ) ^ (((s.re : ℝ) : ℂ) - 1 / 2)) μ := by
  have h := Integrable.ofReal (𝕜 := ℂ) hint.norm
  refine h.congr (Filter.Eventually.of_forall fun g => ?_)
  exact ofReal_norm_pair (W g) (F g) (hw g) s

private theorem norm_integral_le_norm_integral_norm {a : α → ℂ} {w : α → ℝ} (hw : ∀ k, 0 < w k) (s : ℂ) {c : α → ℝ}
    (hc : ∀ k, 0 ≤ c k) :
    ‖∫ k, a k * ((w k : ℝ) : ℂ) ^ (s - 1 / 2) * (c k : ℂ) ∂μ‖ ≤
      ‖∫ k, (((‖a k‖ : ℝ) : ℂ) * (1 : ℂ)) * ((w k : ℝ) : ℂ) ^ (((s.re : ℝ) : ℂ) - 1 / 2) * (c k : ℂ) ∂μ‖ := by
  have hfun : (fun k => (((‖a k‖ : ℝ) : ℂ) * (1 : ℂ)) * ((w k : ℝ) : ℂ) ^ (((s.re : ℝ) : ℂ) - 1 / 2) * (c k : ℂ)) =
      fun k => ((‖a k * ((w k : ℝ) : ℂ) ^ (s - 1 / 2) * (c k : ℂ)‖ : ℝ) : ℂ) := by
    funext k
    exact (ofReal_norm_term (a k) (hw k) s (hc k)).symm
  rw [hfun, integral_complex_ofReal, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun k => norm_nonneg _)]
  exact norm_integral_le_integral_norm _

end Integral

end Small

end Furniture

section PreHelpers

variable (v : HeightOneSpectrum (𝓞 ℚ))

private local instance : MeasurableSpace (GL (Fin 2) (v.adicCompletion ℚ)) :=
  borel (GL (Fin 2) (v.adicCompletion ℚ))

private local instance : BorelSpace (GL (Fin 2) (v.adicCompletion ℚ)) := ⟨rfl⟩

private local instance : BorelSpace (AdelicGL2 (𝓞 ℚ) ℚ) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 ℚ) ℚ

private theorem localWeight_pos (x : GL (Fin 2) (v.adicCompletion ℚ)) : 0 < localWeight v x :=
  TateGlobal.ideleNorm_pos _

private theorem continuous_kerpart : Continuous (kerpart v) := by
  show Continuous fun g : finiteAdelicGL2Subgroup ℚ => g * (sectionAt v (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ)))⁻¹
  exact continuous_id.mul
    ((continuous_sectionAt v).comp ((continuous_localAt (K := ℚ) (v := v)).comp continuous_subtype_val)).inv

private theorem isClosed_ker_localAt :
    IsClosed ((((localAt ℚ v).comp (finiteAdelicGL2Subgroup ℚ).subtype).ker :
      Subgroup (finiteAdelicGL2Subgroup ℚ)) : Set (finiteAdelicGL2Subgroup ℚ)) := by
  have hc : Continuous ((localAt ℚ v).comp (finiteAdelicGL2Subgroup ℚ).subtype) :=
    (continuous_localAt (K := ℚ) (v := v)).comp continuous_subtype_val
  rw [MonoidHom.coe_ker]
  exact isClosed_singleton.preimage hc

private theorem measurableSet_ker_localAt :
    MeasurableSet ((((localAt ℚ v).comp (finiteAdelicGL2Subgroup ℚ).subtype).ker :
      Subgroup (finiteAdelicGL2Subgroup ℚ)) : Set (finiteAdelicGL2Subgroup ℚ)) :=
  (isClosed_ker_localAt v).measurableSet

private theorem measurableEmbedding_split [SecondCountableTopology (finiteAdelicGL2Subgroup ℚ)] :
    MeasurableEmbedding
      (Splitting.splitMap ((localAt ℚ v).comp (finiteAdelicGL2Subgroup ℚ).subtype) (sectionAt v)) :=
  Splitting.measurableEmbedding_splitMap _ _
    ((continuous_localAt (K := ℚ) (v := v)).comp continuous_subtype_val) (continuous_sectionAt v)
    (localAt_sectionAt v)

private theorem localAt_mul_sectionAt (k : finiteAdelicGL2Subgroup ℚ) (hk : localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1)
    (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    localAt ℚ v ((k * sectionAt v x : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) = x := by
  rw [Subgroup.coe_mul, map_mul, hk, one_mul, localAt_sectionAt]

private theorem kerpart_mul_sectionAt (k : finiteAdelicGL2Subgroup ℚ) (hk : localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1)
    (x : GL (Fin 2) (v.adicCompletion ℚ)) : kerpart v (k * sectionAt v x) = k := by
  unfold kerpart
  rw [localAt_mul_sectionAt v k hk x, mul_inv_cancel_right]

private theorem prodDensity_mul_sectionAt (μNv : Measure (unipotentGL2Hom (R := v.adicCompletion ℚ)).range)
    (μ₄ : Measure (unipotentAway v)) (k : finiteAdelicGL2Subgroup ℚ) (x : GL (Fin 2) (v.adicCompletion ℚ))
    (hk : localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1) :
    prodDensity v μNv μ₄ (k * sectionAt v x) =
      density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μNv x * density (unipotentAway v) μ₄ k := by
  unfold prodDensity
  rw [localAt_mul_sectionAt v k hk x, kerpart_mul_sectionAt v k hk x]

private theorem sectionAt_mem_finUnipotent (n : GL (Fin 2) (v.adicCompletion ℚ))
    (hn : n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range) : sectionAt v n ∈ RSCarrier.finUnipotent := by
  obtain ⟨y, rfl⟩ := hn
  rw [Subgroup.mem_subgroupOf]
  refine ⟨Multiplicative.ofAdd ((0 : InfiniteAdeleRing ℚ), splice (𝓞 ℚ) ℚ v 0 (Multiplicative.toAdd y)), ?_⟩
  apply Units.ext
  refine matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 ℚ) ℚ ?_ ?_
  ·
    rw [arch_mapMatrix_eq_one_of_mem _ (sectionAt v _).2]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [unipotentGL2Hom, unipotentGL2, AdelicLevel.adeleArch_apply]
    all_goals rfl
  ·
    refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 ℚ) ℚ fun w => ?_
    rw [finAdeleEval_mapMatrix_sectionAt, finAdeleEval_mapMatrix_adeleFin_mapMatrix, localAt_unipotentGL2Hom]
    by_cases hw : w = v
    · subst hw
      rw [finComponent_localEmbed_self]
      simp
    · rw [finComponent_localEmbed_of_ne (𝓞 ℚ) ℚ v _ hw]
      simp only [toAdd_ofAdd]
      rw [splice_apply_of_ne (𝓞 ℚ) ℚ v _ _ hw]
      rw [show ((0 : FiniteAdeleRing (𝓞 ℚ) ℚ) w) = 0 from rfl]
      simp [unipotentGL2Hom]

private theorem isClosed_finUnipotent :
    IsClosed ((RSCarrier.finUnipotent : Subgroup (finiteAdelicGL2Subgroup ℚ)) : Set (finiteAdelicGL2Subgroup ℚ)) := by
  rw [Subgroup.coe_subgroupOf]
  exact (isClosed_range_unipotentGL2Hom (R := AdeleRing (𝓞 ℚ) ℚ)).preimage continuous_subtype_val

private theorem isClosed_unipotentAway :
    IsClosed ((unipotentAway v : Subgroup (finiteAdelicGL2Subgroup ℚ)) : Set (finiteAdelicGL2Subgroup ℚ)) := by
  unfold unipotentAway
  rw [Subgroup.coe_inf]
  exact (isClosed_finUnipotent).inter (isClosed_ker_localAt v)

private theorem finUnipotent_mul_comm (a b : RSCarrier.finUnipotent) : a * b = b * a :=
  Abelian.subgroupOf_mul_comm _ _ (Abelian.range_mul_comm (unipotentGL2Hom (R := AdeleRing (𝓞 ℚ) ℚ))) a b

end PreHelpers

section DetFurniture

variable {F : Type*} [Field F] {O : ValuationSubring F}

private theorem det_mem {m : Matrix (Fin 2) (Fin 2) F} (hm : ∀ i j, m i j ∈ O) : m.det ∈ O := by
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem (hm 0 0) (hm 1 1)) (mul_mem (hm 0 1) (hm 1 0))

private theorem det_mul_det_inv (k : GL (Fin 2) F) :
    (k : Matrix (Fin 2) (Fin 2) F).det * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]

private theorem eq_one_of_mul_eq_one_of_le_one {Γ : Type*} [LinearOrderedCommMonoidWithZero Γ] {a b : Γ} (ha : a ≤ 1)
    (hb : b ≤ 1) (hab : a * b = 1) : a = 1 :=
  le_antisymm ha (by calc (1 : Γ) = a * b := hab.symm
    _ ≤ a * 1 := mul_le_mul_right hb a
    _ = a := mul_one a)

end DetFurniture

section NormAlgebra

variable {G : Type*} [Group G] (ν : G → ℝ) (hmul : ∀ a b, ν (a * b) = ν a * ν b) (hone : ν 1 = 1) (hpos : ∀ a, 0 < ν a)

include hmul hone in
private theorem nu_inv (t : G) : ν t⁻¹ = (ν t)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← hmul, inv_mul_cancel, hone])

include hmul hone hpos in
private theorem nu_zpow (t : G) (m : ℤ) : ν (t ^ m) = ν t ^ m := by
  induction m using Int.induction_on with
  | zero => rw [zpow_zero, zpow_zero, hone]
  | succ n ih => rw [_root_.zpow_add_one, hmul, ih, zpow_add_one₀ (hpos t).ne']
  | pred n ih => rw [_root_.zpow_sub_one, hmul, ih, nu_inv ν hmul hone, zpow_sub_one₀ (hpos t).ne']

include hmul hone in
private theorem nu_of_unit_quotient (u t : G) (q : ℝ) (hu : ν u = q⁻¹) (h1 : ν (u⁻¹ * t) = 1) : ν t = q⁻¹ := by
  have h := h1
  rw [hmul, nu_inv ν hmul hone, hu, inv_inv] at h
  exact eq_inv_of_mul_eq_one_right h

end NormAlgebra

section TorusDet

variable {K : Type*} [Field K]

private theorem val_det_diagZ
    (π : K) (hπ : π ≠ 0) (m : ℤ) : (Matrix.GeneralLinearGroup.det (diagZ π hπ m) : K) = π ^ m := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  simp [diagZ, Matrix.det_fin_two]

private theorem val_det_scalarPi
    (π : K) (hπ : π ≠ 0) : (Matrix.GeneralLinearGroup.det (scalarPi π hπ) : K) = π * π := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  simp [scalarPi, Matrix.det_fin_two]

end TorusDet

section WeightDocks

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem valued_det_eq_one_of_mem {k : GL (Fin 2) (v.adicCompletion ℚ)} (hk : k ∈ localLevelOne (𝓞 ℚ) ℚ v ⊤) :
    Valued.v (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det = 1 := by
  obtain ⟨h₁, h₂⟩ := (LevelOne.mem_localLevelOne_top_iff v k).mp hk
  have hd₁ := det_mem h₁
  have hd₂ := det_mem h₂
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hd₁ hd₂
  exact eq_one_of_mul_eq_one_of_le_one hd₁ hd₂ (by rw [← map_mul, det_mul_det_inv, map_one])

private theorem valued_det_eq_one_of_mem' {k : GL (Fin 2) (v.adicCompletion ℚ)} (hk : k ∈ localLevelOne (𝓞 ℚ) ℚ v ⊤) :
    Valued.v ((Matrix.GeneralLinearGroup.det k : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact valued_det_eq_one_of_mem v hk

private theorem ideleNorm_one' : TateGlobal.ideleNorm ℚ (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ) = 1 := by
  have h := TateGlobal.ideleNorm_mul (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ) 1
  rw [one_mul] at h
  exact (mul_eq_left₀ (TateGlobal.ideleNorm_pos 1).ne').mp h.symm

private def placeNorm (t : (v.adicCompletion ℚ)ˣ) : ℝ :=
  TateGlobal.ideleNorm ℚ (Units.map (AdelicLevel.finIncl (𝓞 ℚ) ℚ) (AdelicLevel.localUnit (𝓞 ℚ) ℚ v t))

private theorem placeNorm_mul
    (t t' : (v.adicCompletion ℚ)ˣ) : placeNorm v (t * t') = placeNorm v t * placeNorm v t' := by
  unfold placeNorm
  rw [map_mul, map_mul, TateGlobal.ideleNorm_mul]

private theorem placeNorm_one : placeNorm v 1 = 1 := by
  unfold placeNorm
  rw [map_one, map_one, ideleNorm_one']

private theorem placeNorm_pos (t : (v.adicCompletion ℚ)ˣ) : 0 < placeNorm v t :=
  TateGlobal.ideleNorm_pos _

private theorem placeNorm_zpow (t : (v.adicCompletion ℚ)ˣ) (m : ℤ) : placeNorm v (t ^ m) = placeNorm v t ^ m :=
  nu_zpow (placeNorm v) (placeNorm_mul v) (placeNorm_one v) (placeNorm_pos v) t m

private theorem placeNorm_eq_one (t : (v.adicCompletion ℚ)ˣ) (ht : Valued.v (t : v.adicCompletion ℚ) = 1) :
    placeNorm v t = 1 := by
  apply TateGlobal.ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
  · rfl
  · have hfp : AdeleRing.finitePartUnits (𝓞 ℚ) ℚ
        (Units.map (AdelicLevel.finIncl (𝓞 ℚ) ℚ) (AdelicLevel.localUnit (𝓞 ℚ) ℚ v t)) =
        AdelicLevel.localUnit (𝓞 ℚ) ℚ v t := Units.ext rfl
    rw [hfp, FiniteAdeleRing.mem_unitIdeles_iff]
    have hinv : Valued.v ((t⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, ht, inv_one]
    refine ⟨fun w => ?_, fun w => ?_⟩
    · by_cases hw : w = v
      · subst hw
        rw [AdelicLevel.localUnit_apply_self, HeightOneSpectrum.mem_adicCompletionIntegers]
        exact ht.le
      · rw [AdelicLevel.localUnit_apply_of_ne (𝓞 ℚ) ℚ v t hw]
        exact one_mem _
    · rw [← map_inv]
      by_cases hw : w = v
      · subst hw
        rw [AdelicLevel.localUnit_apply_self, HeightOneSpectrum.mem_adicCompletionIntegers]
        exact hinv.le
      · rw [AdelicLevel.localUnit_apply_of_ne (𝓞 ℚ) ℚ v _ hw]
        exact one_mem _

private theorem placeNorm_uniformizerUnit
    : placeNorm v (AdelicLevel.uniformizerUnit ℚ v) = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ :=
  TateGlobal.ideleNorm_uniformizerIdele ℚ v

private theorem placeNorm_of_valued (t : (v.adicCompletion ℚ)ˣ)
    (ht : Valued.v (t : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ)) :
    placeNorm v t = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  have hu : Valued.v (((AdelicLevel.uniformizerUnit ℚ v)⁻¹ * t : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, AdelicLevel.valued_uniformizerUnit, ht,
      inv_mul_cancel₀ WithZero.exp_ne_zero]
  exact nu_of_unit_quotient (placeNorm v) (placeNorm_mul v) (placeNorm_one v) _ t _ (placeNorm_uniformizerUnit v)
    (placeNorm_eq_one v _ hu)

private theorem det_coe_sectionAt (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    Matrix.GeneralLinearGroup.det ((sectionAt v x : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) =
      Units.map (AdelicLevel.finIncl (𝓞 ℚ) ℚ) (AdelicLevel.localUnit (𝓞 ℚ) ℚ v (Matrix.GeneralLinearGroup.det x)) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  have harch : AdelicLevel.adeleArch (𝓞 ℚ) ℚ
      (((sectionAt v x : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)).det = 1 := by
    rw [RingHom.map_det, arch_mapMatrix_eq_one_of_mem _ (sectionAt v x).2, Matrix.det_one]
  have hfin : AdelicLevel.adeleFin (𝓞 ℚ) ℚ
      (((sectionAt v x : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)).det =
        ((AdelicLevel.localUnit (𝓞 ℚ) ℚ v (Matrix.GeneralLinearGroup.det x) : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
          FiniteAdeleRing (𝓞 ℚ) ℚ) := by
    apply RestrictedProduct.ext
    intro w
    change AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w (AdelicLevel.adeleFin (𝓞 ℚ) ℚ
        (((sectionAt v x : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) :
          Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)).det) =
      AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w
        ((AdelicLevel.localUnit (𝓞 ℚ) ℚ v (Matrix.GeneralLinearGroup.det x) : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
          FiniteAdeleRing (𝓞 ℚ) ℚ)
    rw [RingHom.map_det, RingHom.map_det, finAdeleEval_mapMatrix_sectionAt, AdelicLevel.finAdeleEval_apply]
    by_cases hw : w = v
    · subst hw
      rw [finComponent_localEmbed_self, AdelicLevel.localUnit_apply_self, Matrix.GeneralLinearGroup.val_det_apply]
    · rw [finComponent_localEmbed_of_ne (𝓞 ℚ) ℚ v _ hw, AdelicLevel.localUnit_apply_of_ne (𝓞 ℚ) ℚ v _ hw,
        Units.val_one, Matrix.det_one]
  apply Prod.ext
  · exact harch
  · exact hfin

private theorem localWeight_eq_placeNorm_det (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    localWeight v x = placeNorm v (Matrix.GeneralLinearGroup.det x) := by
  unfold localWeight finWeight
  rw [det_coe_sectionAt]
  rfl

private theorem det_torusPt {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0) (p : ℤ × ℤ) :
    Matrix.GeneralLinearGroup.det (torusPt v hπ p) =
      Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (p.1 + p.2) := by
  apply Units.ext
  unfold torusPt
  rw [map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, val_det_diagZ, val_det_scalarPi,
    Units.val_zpow_eq_zpow_val, Units.val_mk0, mul_zpow, ← zpow_add₀ hπ, ← zpow_add₀ hπ]
  congr 1
  ring

end WeightDocks

section ProductDensity

variable (v : HeightOneSpectrum (𝓞 ℚ))

private local instance : MeasurableSpace (GL (Fin 2) (v.adicCompletion ℚ)) :=
  borel (GL (Fin 2) (v.adicCompletion ℚ))

private local instance : BorelSpace (GL (Fin 2) (v.adicCompletion ℚ)) := ⟨rfl⟩

private local instance : BorelSpace (AdelicGL2 (𝓞 ℚ) ℚ) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 ℚ) ℚ

private def unipLocal : RSCarrier.finUnipotent →* (unipotentGL2Hom (R := v.adicCompletion ℚ)).range where
  toFun n := ⟨localAt ℚ v ((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ),
    localAt_mem_range_of_mem_finUnipotent v n⟩
  map_one' := Subtype.ext (by simp)
  map_mul' n n' := Subtype.ext (by simp)

private def unipSection : (unipotentGL2Hom (R := v.adicCompletion ℚ)).range →* RSCarrier.finUnipotent where
  toFun x := ⟨sectionAt v (x : GL (Fin 2) (v.adicCompletion ℚ)), sectionAt_mem_finUnipotent v _ x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x x' := Subtype.ext (by simp)

private theorem coe_unipLocal (n : RSCarrier.finUnipotent) :
    (unipLocal v n : GL (Fin 2) (v.adicCompletion ℚ)) =
      localAt ℚ v ((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) :=
  rfl

private theorem coe_unipSection (x : (unipotentGL2Hom (R := v.adicCompletion ℚ)).range) :
    (unipSection v x : finiteAdelicGL2Subgroup ℚ) = sectionAt v (x : GL (Fin 2) (v.adicCompletion ℚ)) :=
  rfl

private theorem unipLocal_unipSection (x : (unipotentGL2Hom (R := v.adicCompletion ℚ)).range) :
    unipLocal v (unipSection v x) = x :=
  Subtype.ext (by rw [coe_unipLocal, coe_unipSection, localAt_sectionAt])

private theorem continuous_unipLocal : Continuous (unipLocal v) :=
  Continuous.subtype_mk
    ((continuous_localAt (K := ℚ) (v := v)).comp (continuous_subtype_val.comp continuous_subtype_val)) _

private theorem continuous_unipSection : Continuous (unipSection v) :=
  Continuous.subtype_mk ((continuous_sectionAt v).comp continuous_subtype_val) _

private noncomputable def unipSplit :
    RSCarrier.finUnipotent ≃ₜ* (unipotentGL2Hom (R := v.adicCompletion ℚ)).range × (unipLocal v).ker :=
  SplitIso.sectionSplitting (unipLocal v) (unipSection v) (continuous_unipLocal v) (continuous_unipSection v)
    (unipLocal_unipSection v) (fun x k _ => finUnipotent_mul_comm (unipSection v x) k)

private theorem unipSplit_symm_apply (p : (unipotentGL2Hom (R := v.adicCompletion ℚ)).range × (unipLocal v).ker) :
    (unipSplit v).symm p = (p.2 : RSCarrier.finUnipotent) * unipSection v p.1 :=
  rfl

private theorem mem_unipotentAway_of_mem_ker (k : (unipLocal v).ker) :
    ((k : RSCarrier.finUnipotent) : finiteAdelicGL2Subgroup ℚ) ∈ unipotentAway v := by
  refine ⟨(k : RSCarrier.finUnipotent).2, ?_⟩
  have hk : unipLocal v (k : RSCarrier.finUnipotent) = 1 := MonoidHom.mem_ker.mp k.2
  have := congrArg Subtype.val hk
  rw [coe_unipLocal] at this
  exact this

private theorem localAt_coe_of_mem_unipotentAway (u : unipotentAway v) :
    localAt ℚ v (((u : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) = 1 :=
  u.2.2

private noncomputable def kerAwayEquiv : (unipLocal v).ker ≃ₜ* unipotentAway v :=
  { toFun := fun k => ⟨((k : RSCarrier.finUnipotent) : finiteAdelicGL2Subgroup ℚ), mem_unipotentAway_of_mem_ker v k⟩
    invFun := fun u => ⟨⟨(u : finiteAdelicGL2Subgroup ℚ), u.2.1⟩,
      MonoidHom.mem_ker.mpr (Subtype.ext (localAt_coe_of_mem_unipotentAway v u))⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl
    continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
    continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _ }

private theorem coe_kerAwayEquiv (k : (unipLocal v).ker) :
    ((kerAwayEquiv v k : unipotentAway v) : finiteAdelicGL2Subgroup ℚ) =
      ((k : RSCarrier.finUnipotent) : finiteAdelicGL2Subgroup ℚ) :=
  rfl

private theorem unipotentAway_mul_comm (a b : unipotentAway v) : a * b = b * a := by
  have h := finUnipotent_mul_comm ⟨(a : finiteAdelicGL2Subgroup ℚ), a.2.1⟩ ⟨(b : finiteAdelicGL2Subgroup ℚ), b.2.1⟩
  have h' := congrArg Subtype.val h
  exact Subtype.ext (by simpa only [Subgroup.coe_mul] using h')

private theorem isClosed_ker_unipLocal : IsClosed ((unipLocal v).ker : Set RSCarrier.finUnipotent) := by
  rw [MonoidHom.coe_ker]
  exact isClosed_singleton.preimage (continuous_unipLocal v)

private theorem prodDensity_ker_mul_sectionAt_mul (μNv : Measure (unipotentGL2Hom (R := v.adicCompletion ℚ)).range)
    (μ₄ : Measure (unipotentAway v)) (k : finiteAdelicGL2Subgroup ℚ) (hk : localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1)
    (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : finiteAdelicGL2Subgroup ℚ) :
    prodDensity v μNv μ₄ (k * sectionAt v x * g) =
      density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μNv (x * localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ)) *
        density (unipotentAway v) μ₄ (k * (sectionAt v x * kerpart v g * (sectionAt v x)⁻¹)) := by
  have hloc : localAt ℚ v ((k * sectionAt v x * g : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) =
      x * localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) := by
    rw [Subgroup.coe_mul, map_mul, localAt_mul_sectionAt v k hk x]
  unfold prodDensity
  rw [hloc]
  congr 2
  unfold kerpart
  rw [hloc, map_mul]
  group

end ProductDensity

section Contracts

variable (v : HeightOneSpectrum (𝓞 ℚ))

private local instance : MeasurableSpace (GL (Fin 2) (v.adicCompletion ℚ)) :=
  borel (GL (Fin 2) (v.adicCompletion ℚ))

private local instance : BorelSpace (GL (Fin 2) (v.adicCompletion ℚ)) := ⟨rfl⟩

private local instance : BorelSpace (AdelicGL2 (𝓞 ℚ) ℚ) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 ℚ) ℚ

private theorem measurable_prodDensity [SecondCountableTopology (finiteAdelicGL2Subgroup ℚ)]
    (μNv : Measure (unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μNv.IsHaarMeasure]
    (μ₄ : Measure (unipotentAway v)) [μ₄.IsHaarMeasure] : Measurable (prodDensity v μNv μ₄) := by
  haveI : LocallyCompactSpace (GL (Fin 2) (v.adicCompletion ℚ)) := locallyCompactSpace_localGL ℚ v
  haveI : SigmaCompactSpace (GL (Fin 2) (v.adicCompletion ℚ)) := inferInstance
  haveI := sigmaCompactSpace_of_isClosed _ (isClosed_range_unipotentGL2Hom (R := v.adicCompletion ℚ))
  haveI := sfinite_of_isHaarMeasure μNv
  haveI : LocallyCompactSpace (finiteAdelicGL2Subgroup ℚ) := locallyCompactSpace_finiteAdelicGL2Subgroup
  haveI : SigmaCompactSpace (finiteAdelicGL2Subgroup ℚ) := inferInstance
  haveI := sigmaCompactSpace_of_isClosed _ (isClosed_unipotentAway v)
  haveI := sfinite_of_isHaarMeasure μ₄
  unfold prodDensity
  have h1 : Measurable (density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μNv) := measurable_density _ μNv
  have h2 : Measurable (density (unipotentAway v) μ₄) := measurable_density _ μ₄
  have hloc : Measurable fun g : finiteAdelicGL2Subgroup ℚ => localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) :=
    ((continuous_localAt (K := ℚ) (v := v)).comp continuous_subtype_val).measurable
  have hker : Measurable (kerpart v) := (continuous_kerpart v).measurable
  exact (h1.comp hloc).mul (h2.comp hker)

private theorem localDensity_ne_top
    (μNv : Measure (unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μNv.IsHaarMeasure]
    (x : GL (Fin 2) (v.adicCompletion ℚ)) : density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μNv x ≠ ⊤ := by
  haveI : LocallyCompactSpace (GL (Fin 2) (v.adicCompletion ℚ)) := locallyCompactSpace_localGL ℚ v
  haveI : SigmaCompactSpace (GL (Fin 2) (v.adicCompletion ℚ)) := inferInstance
  exact DensNorm.density_ne_top _ μNv (isClosed_range_unipotentGL2Hom (R := v.adicCompletion ℚ)) x

private theorem awayDensity_ne_top [SecondCountableTopology (finiteAdelicGL2Subgroup ℚ)]
    (μ₄ : Measure (unipotentAway v)) [μ₄.IsHaarMeasure] (k : finiteAdelicGL2Subgroup ℚ) :
    density (unipotentAway v) μ₄ k ≠ ⊤ := by
  haveI : LocallyCompactSpace (finiteAdelicGL2Subgroup ℚ) := locallyCompactSpace_finiteAdelicGL2Subgroup
  haveI : SigmaCompactSpace (finiteAdelicGL2Subgroup ℚ) := inferInstance
  exact DensNorm.density_ne_top _ μ₄ (isClosed_unipotentAway v) k

private theorem prodDensity_ne_top [SecondCountableTopology (finiteAdelicGL2Subgroup ℚ)]
    (μNv : Measure (unipotentGL2Hom (R := v.adicCompletion ℚ)).range)
    [μNv.IsHaarMeasure] (μ₄ : Measure (unipotentAway v)) [μ₄.IsHaarMeasure] (g : finiteAdelicGL2Subgroup ℚ) :
    prodDensity v μNv μ₄ g ≠ ⊤ := by
  unfold prodDensity
  exact ENNReal.mul_ne_top (localDensity_ne_top v μNv _) (awayDensity_ne_top v μ₄ _)

private theorem lintegral_finDensity_eq_one [SecondCountableTopology (finiteAdelicGL2Subgroup ℚ)]
    (μN : Measure RSCarrier.finUnipotent) [μN.IsHaarMeasure]
    (g : finiteAdelicGL2Subgroup ℚ) :
    ∫⁻ n : RSCarrier.finUnipotent,
      density RSCarrier.finUnipotent μN ((n : finiteAdelicGL2Subgroup ℚ) * g) ∂μN = 1 := by
  haveI : LocallyCompactSpace (finiteAdelicGL2Subgroup ℚ) := locallyCompactSpace_finiteAdelicGL2Subgroup
  haveI : SigmaCompactSpace (finiteAdelicGL2Subgroup ℚ) := inferInstance
  haveI : μN.IsMulRightInvariant := Abelian.isMulRightInvariant_of_comm μN finUnipotent_mul_comm
  exact HaarQuotient.lintegral_density_mul_eq_one _ isClosed_finUnipotent μN g

private theorem finDensity_ne_top [SecondCountableTopology (finiteAdelicGL2Subgroup ℚ)]
    (μN : Measure RSCarrier.finUnipotent) [μN.IsHaarMeasure]
    (g : finiteAdelicGL2Subgroup ℚ) : density RSCarrier.finUnipotent μN g ≠ ⊤ := by
  haveI : LocallyCompactSpace (finiteAdelicGL2Subgroup ℚ) := locallyCompactSpace_finiteAdelicGL2Subgroup
  haveI : SigmaCompactSpace (finiteAdelicGL2Subgroup ℚ) := inferInstance
  exact DensNorm.density_ne_top _ μN isClosed_finUnipotent g

private theorem lintegral_localDensity_eq_one (μNv : Measure (unipotentGL2Hom (R := v.adicCompletion ℚ)).range)
    [μNv.IsHaarMeasure] (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    ∫⁻ n : (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
      density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μNv ((n : GL (Fin 2) (v.adicCompletion ℚ)) * x)
        ∂μNv = 1 := by
  haveI : LocallyCompactSpace (GL (Fin 2) (v.adicCompletion ℚ)) := locallyCompactSpace_localGL ℚ v
  haveI : SigmaCompactSpace (GL (Fin 2) (v.adicCompletion ℚ)) := inferInstance
  haveI : μNv.IsMulRightInvariant := Abelian.isMulRightInvariant_of_comm μNv (Abelian.range_mul_comm _)
  exact HaarQuotient.lintegral_density_mul_eq_one _ (isClosed_range_unipotentGL2Hom (R := v.adicCompletion ℚ)) μNv x

private theorem lintegral_inv_finUnipotent [SecondCountableTopology (finiteAdelicGL2Subgroup ℚ)]
    (μN : Measure RSCarrier.finUnipotent) [μN.IsHaarMeasure]
    (f : RSCarrier.finUnipotent → ℝ≥0∞) : ∫⁻ n, f n⁻¹ ∂μN = ∫⁻ n, f n ∂μN := by
  haveI : LocallyCompactSpace (finiteAdelicGL2Subgroup ℚ) := locallyCompactSpace_finiteAdelicGL2Subgroup
  haveI : LocallyCompactSpace RSCarrier.finUnipotent := (isClosed_finUnipotent).locallyCompactSpace
  haveI : SecondCountableTopology RSCarrier.finUnipotent := Topology.IsInducing.subtypeVal.secondCountableTopology
  exact Unimodular.lintegral_inv_eq_of_comm' finUnipotent_mul_comm μN f

private theorem isMulRightInvariant_localUnipotent (μNv : Measure (unipotentGL2Hom (R := v.adicCompletion ℚ)).range)
    [μNv.IsHaarMeasure] : μNv.IsMulRightInvariant := by
  exact Abelian.isMulRightInvariant_of_comm μNv (Abelian.range_mul_comm _)

private theorem finWeight_unipotent_mul (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ) :
    finWeight ((n : finiteAdelicGL2Subgroup ℚ) * g) = finWeight g := by
  have hdet : Matrix.GeneralLinearGroup.det ((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := by
    obtain ⟨z, hz⟩ := Subgroup.mem_subgroupOf.mp n.2
    rw [← hz]
    apply Units.ext
    simp [unipotentGL2Hom, unipotentGL2, Matrix.det_fin_two]
  unfold finWeight
  rw [Subgroup.coe_mul, map_mul, hdet, one_mul]

private theorem finWeight_mul_sectionAt (k : finiteAdelicGL2Subgroup ℚ) (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    finWeight (k * sectionAt v x) = finWeight k * localWeight v x := by
  unfold localWeight finWeight
  rw [Subgroup.coe_mul, map_mul, TateGlobal.ideleNorm_mul]

private theorem finWeight_pos (g : finiteAdelicGL2Subgroup ℚ) : 0 < finWeight g := by
  exact TateGlobal.ideleNorm_pos _

private theorem localWeight_unipotent_mul (n : GL (Fin 2) (v.adicCompletion ℚ))
    (hn : n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range) (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    localWeight v (n * x) = localWeight v x := by
  unfold localWeight
  rw [map_mul]
  exact finWeight_unipotent_mul ⟨sectionAt v n, sectionAt_mem_finUnipotent v n hn⟩ (sectionAt v x)

private theorem localWeight_mul_levelOne (k : GL (Fin 2) (v.adicCompletion ℚ)) (hk : k ∈ localLevelOne (𝓞 ℚ) ℚ v ⊤)
    (x : GL (Fin 2) (v.adicCompletion ℚ)) : localWeight v (x * k) = localWeight v x := by
  rw [localWeight_eq_placeNorm_det, localWeight_eq_placeNorm_det, map_mul, placeNorm_mul,
    placeNorm_eq_one v _ (valued_det_eq_one_of_mem' v hk), mul_one]

private theorem localWeight_one : localWeight v 1 = 1 := by
  unfold localWeight finWeight
  rw [map_one, OneMemClass.coe_one, map_one]
  have h := TateGlobal.ideleNorm_mul (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ) 1
  rw [one_mul] at h
  exact (mul_eq_left₀ (TateGlobal.ideleNorm_pos 1).ne').mp h.symm

private theorem localWeight_torusPt {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (p : ℤ × ℤ) : localWeight v (torusPt v hπ p) = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(p.1 + p.2)) := by
  rw [localWeight_eq_placeNorm_det, det_torusPt, placeNorm_zpow,
    placeNorm_of_valued v _ (by rw [Units.val_mk0]; exact hϖ), inv_zpow']

private theorem mul_torusPt_eq_cellValue_mul (W F : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) {ψ : AddChar (v.adicCompletion ℚ) ℂ}
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (lam om : ℂ) {I : Type*} [Fintype I] [Nonempty I] (b : I → v.adicCompletionIntegers ℚ)
    (hI : Fintype.card I = Ideal.absNorm v.asIdeal)
    (hψ0 : ∀ r : v.adicCompletionIntegers ℚ,
      ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) = 1)
    (hψ1 : ∃ r : v.adicCompletionIntegers ℚ,
      ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r /
        algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) ≠ 1)
    (hN : ∀ (x : v.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      W (placeEmbed ℚ v (unipotent x) * g) = ψ x * W g)
    (hWK : ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W (g * placeEmbed ℚ v x) = W g)
    (hT : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      (∑ i, W (g * placeEmbed ℚ v (repSome
          (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ
          (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (b i))))) +
        W (g * placeEmbed ℚ v (repInf
          (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) = lam * W g)
    (hZ : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      W (g * placeEmbed ℚ v (scalarPi
        (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) = om * W g)
    (uZ : ℤ → ℤ → ℂ) (huZ_off : ∀ m₁ m₂ : ℤ, (m₂ < 0 ∨ m₁ < m₂) → uZ m₁ m₂ = 0)
    (hF : ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (m₁ m₂ : ℤ), localAt ℚ v g = 1 →
      F (g * placeEmbed ℚ v
          (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (m₁ - m₂) *
            scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ m₂)) =
        F g * ((Ideal.absNorm v.asIdeal : ℂ)⁻¹ ^ m₁ * uZ m₁ m₂))
    (k : finiteAdelicGL2Subgroup ℚ) (hk : localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1) (p : ℤ × ℤ) :
    W ((k * sectionAt v (torusPt v hπ p) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) *
        F ((k * sectionAt v (torusPt v hπ p) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) =
      cellValue v lam om uZ p * (W (k : AdelicGL2 (𝓞 ℚ) ℚ) * F (k : AdelicGL2 (𝓞 ℚ) ℚ)) := by
  have _ := hϖ
  have hK' : ∀ (r : v.adicCompletionIntegers ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      W (g * placeEmbed ℚ v (unipotent (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r))) = W g :=
    fun r g => hWK _ g (unipotent_integral_mem_localLevelOne_top v r)
  have hg₀ : ∀ x : GL (Fin 2) (v.adicCompletion ℚ),
      (k : AdelicGL2 (𝓞 ℚ) ℚ) * placeEmbed ℚ v x = placeEmbed ℚ v x * (k : AdelicGL2 (𝓞 ℚ) ℚ) := fun x => by
    have h := congrArg (fun z : finiteAdelicGL2Subgroup ℚ => (z : AdelicGL2 (𝓞 ℚ) ℚ)) (sectionAt_mul_comm v x k hk)
    have h__af := h.symm
    simp only [Subgroup.coe_mul] at h__af
    exact h__af
  have hW := UnramifiedWhittaker.apply_mul_placeEmbed_diagZ_eq_mul_torusFactor v hπ b hψ0 hψ1 hN hK' hT hZ hg₀
    (p.1 - p.2)
  have hFk := hF (k : AdelicGL2 (𝓞 ℚ) ℚ) p.1 p.2 hk
  have hcoe : ((k * sectionAt v (torusPt v hπ p) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) =
      (k : AdelicGL2 (𝓞 ℚ) ℚ) * placeEmbed ℚ v (torusPt v hπ p) := by
    rw [Subgroup.coe_mul]
    rfl
  rw [hcoe]
  unfold torusPt
  rw [hFk, map_mul, map_zpow, ← mul_assoc (k : AdelicGL2 (𝓞 ℚ) ℚ)]
  simp only [cellValue]
  rcases lt_or_ge p.2 0 with hneg | hnn
  · simp only [huZ_off p.1 p.2 (Or.inl hneg), mul_zero, zero_mul]
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, p.2 = n := ⟨p.2.toNat, (Int.toNat_of_nonneg hnn).symm⟩
    rw [hn] at hW ⊢
    rw [zpow_natCast, apply_mul_pow_eq_pow_mul W _ om hZ n, hW, hI, Int.toNat_natCast]
    ring

private theorem eq_inv_eval_mul_of_hasSum (s lam om : ℂ) (e₁ e₂ e₃ : ℂ) (h : ℕ → ℂ) (hh0 : h 0 = 1) (hh1 : h 1 = e₁)
    (hh2 : h 2 = e₁ ^ 2 - e₂) (hh : ∀ n : ℕ, h (n + 3) = e₁ * h (n + 2) - e₂ * h (n + 1) + e₃ * h n)
    (u : ℕ → ℕ → ℂ) (hu0 : ∀ k : ℕ, u k 0 = h k)
    (hu : ∀ k₁ k₂ : ℕ, u k₁ (k₂ + 1) = h k₁ * h (k₂ + 1) - h (k₁ + 1) * h k₂)
    (uZ : ℤ → ℤ → ℂ) (huZ_off : ∀ m₁ m₂ : ℤ, (m₂ < 0 ∨ m₁ < m₂) → uZ m₁ m₂ = 0)
    (huZ_cone : ∀ k₁ k₂ : ℕ, k₂ ≤ k₁ → uZ k₁ k₂ = u k₁ k₂) (Y L : ℂ)
    (hL : HasSum (fun p : ℤ × ℤ => seriesTerm v s lam om uZ p * Y) L)
    (habs : Y ≠ 0 → Summable (fun p : ℤ × ℤ => ‖seriesTerm v s lam om uZ p‖)) :
    L = ((rsEulerPoly lam ((Ideal.absNorm v.asIdeal : ℂ) * om) e₁ e₂ e₃).eval
          ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))))⁻¹ * Y := by
  have habs0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have hq0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr habs0
  have hr0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero habs0)

  have ht0 : (Ideal.absNorm v.asIdeal : ℂ) ^ 0 * heckeRecursionSeq (Ideal.absNorm v.asIdeal) lam om 0 = 1 :=
    GGlue.pow_mul_seq_zero
  have ht1 : (Ideal.absNorm v.asIdeal : ℂ) ^ 1 * heckeRecursionSeq (Ideal.absNorm v.asIdeal) lam om 1 = lam :=
    GGlue.pow_mul_seq_one hq0
  have ht : ∀ m : ℕ,
      (Ideal.absNorm v.asIdeal : ℂ) ^ (m + 2) * heckeRecursionSeq (Ideal.absNorm v.asIdeal) lam om (m + 2) =
      lam * ((Ideal.absNorm v.asIdeal : ℂ) ^ (m + 1) * heckeRecursionSeq (Ideal.absNorm v.asIdeal) lam om (m + 1)) -
        (Ideal.absNorm v.asIdeal : ℂ) * om *
          ((Ideal.absNorm v.asIdeal : ℂ) ^ m * heckeRecursionSeq (Ideal.absNorm v.asIdeal) lam om m) :=
    fun m => GGlue.pow_mul_seq_add_two hq0 m

  have hcore := LanglandsTunnell.RankinSelberg.mk_twoRowCauchySum_mul_coe_rsEulerPoly_eq_one lam
    ((Ideal.absNorm v.asIdeal : ℂ) * om) e₁ e₂ e₃
    (fun k => (Ideal.absNorm v.asIdeal : ℂ) ^ k * heckeRecursionSeq (Ideal.absNorm v.asIdeal) lam om k) ht0 ht1 ht
    h hh0 hh1 hh2 hh u hu0 hu

  have hfib : ∀ n : ℕ, ∑ p₂ ∈ Finset.range (n + 1), seriesTerm v s lam om uZ ((n : ℤ) - (p₂ : ℤ), (p₂ : ℤ)) =
      (∑ k₂ ∈ Finset.range (n / 2 + 1), ((Ideal.absNorm v.asIdeal : ℂ) * om) ^ k₂ *
          ((Ideal.absNorm v.asIdeal : ℂ) ^ (n - 2 * k₂) *
            heckeRecursionSeq (Ideal.absNorm v.asIdeal) lam om (n - 2 * k₂)) * u (n - k₂) k₂) *
        ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) ^ n := by
    intro n
    have h1 := Fibre.sum_seriesTerm_eq (q := (Ideal.absNorm v.asIdeal : ℂ)) (om := om)
      (r := (Ideal.absNorm v.asIdeal : ℝ))
      (s := s) (tf := torusFactor (Ideal.absNorm v.asIdeal) lam om) (uZ := uZ)
      (TermMatch.torusFactor_natCast (Ideal.absNorm v.asIdeal) lam om) huZ_off huZ_cone n
    have h2 := TermMatch.sum_cellTerm_heckeRecursionSeq_eq hq0
      (fun k => (Ideal.absNorm v.asIdeal : ℂ) ^ k * heckeRecursionSeq (Ideal.absNorm v.asIdeal) lam om k) ht0 ht1 ht
      u n
    have h3 := Fibre.inv_pow_mul_weight_eq (s := s) hr0 n
    rw [Complex.ofReal_natCast] at h3
    change ∑ p₂ ∈ Finset.range (n + 1),
      Fibre.seriesTerm (Ideal.absNorm v.asIdeal : ℂ) om (Ideal.absNorm v.asIdeal : ℝ) s
      (torusFactor (Ideal.absNorm v.asIdeal) lam om) uZ ((n : ℤ) - (p₂ : ℤ), (p₂ : ℤ)) = _
    rw [h1, h2, mul_assoc, h3]

  exact Regroup.eq_inv_mul_of_hasSum_core (Fibre.seriesTerm_eq_zero huZ_off) hfib
    (fun hsum => CauchyWrapper.tsum_mul_eval_eq_one_of_mk_mul_coe_eq_one hcore hsum) hL habs

private theorem exists_lintegral_prodDensity_eq_one [SecondCountableTopology (finiteAdelicGL2Subgroup ℚ)]
    (μN : Measure RSCarrier.finUnipotent) [μN.IsHaarMeasure]
    (μNv : Measure (unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μNv.IsHaarMeasure] :
    ∃ μ₄ : Measure (unipotentAway v), μ₄.IsHaarMeasure ∧
      ∀ g : finiteAdelicGL2Subgroup ℚ,
        ∫⁻ n : RSCarrier.finUnipotent, prodDensity v μNv μ₄ ((n : finiteAdelicGL2Subgroup ℚ) * g) ∂μN = 1 := by

  haveI : LocallyCompactSpace (GL (Fin 2) (v.adicCompletion ℚ)) := locallyCompactSpace_localGL ℚ v
  haveI : SigmaCompactSpace (GL (Fin 2) (v.adicCompletion ℚ)) := inferInstance
  haveI : LocallyCompactSpace (unipotentGL2Hom (R := v.adicCompletion ℚ)).range :=
    (isClosed_range_unipotentGL2Hom (R := v.adicCompletion ℚ)).locallyCompactSpace
  haveI := sigmaCompactSpace_of_isClosed _ (isClosed_range_unipotentGL2Hom (R := v.adicCompletion ℚ))
  haveI : LocallyCompactSpace (finiteAdelicGL2Subgroup ℚ) := locallyCompactSpace_finiteAdelicGL2Subgroup
  haveI : SigmaCompactSpace (finiteAdelicGL2Subgroup ℚ) := inferInstance
  haveI : SigmaCompactSpace RSCarrier.finUnipotent := sigmaCompactSpace_of_isClosed _ isClosed_finUnipotent
  haveI : SigmaCompactSpace (unipLocal v).ker := sigmaCompactSpace_of_isClosed _ (isClosed_ker_unipLocal v)
  haveI : SigmaCompactSpace (unipotentAway v) := sigmaCompactSpace_of_isClosed _ (isClosed_unipotentAway v)
  haveI : SecondCountableTopology RSCarrier.finUnipotent := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : SecondCountableTopology (unipLocal v).ker := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : SecondCountableTopology (unipotentGL2Hom (R := v.adicCompletion ℚ)).range :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : SecondCountableTopology (unipotentAway v) := Topology.IsInducing.subtypeVal.secondCountableTopology

  obtain ⟨μ₂, hμ₂, -, hmap⟩ :=
    MeasureTheory.Measure.exists_isHaarMeasure_map_continuousMulEquiv_eq_prod μN μNv (unipSplit v)
  haveI := sfinite_of_isHaarMeasure μ₂
  refine ⟨μ₂.map (kerAwayEquiv v), inferInstance, fun g => ?_⟩
  haveI hμ₄ : (μ₂.map (kerAwayEquiv v)).IsHaarMeasure := inferInstance
  haveI : (μ₂.map (kerAwayEquiv v)).IsMulRightInvariant :=
    Abelian.isMulRightInvariant_of_comm _ (unipotentAway_mul_comm v)
  haveI : μNv.IsMulRightInvariant := Abelian.isMulRightInvariant_of_comm μNv (Abelian.range_mul_comm _)
  haveI := sfinite_of_isHaarMeasure (μ₂.map (kerAwayEquiv v))
  haveI := sfinite_of_isHaarMeasure μNv

  have hρv : Measurable (density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μNv) := measurable_density _ μNv
  have hρ₄ : Measurable (density (unipotentAway v) (μ₂.map (kerAwayEquiv v))) := measurable_density _ _

  set μ₄ := μ₂.map (kerAwayEquiv v)
  have hsc : Continuous (unipSplit v) := (unipSplit v).continuous_toFun
  have hsc' : Continuous (unipSplit v).symm := (unipSplit v).continuous_invFun
  have hkc : Continuous (kerAwayEquiv v) := (kerAwayEquiv v).continuous_toFun
  have hf : Measurable fun n : RSCarrier.finUnipotent => prodDensity v μNv μ₄ ((n : finiteAdelicGL2Subgroup ℚ) * g) :=
    (measurable_prodDensity v μNv μ₄).comp (continuous_subtype_val.mul continuous_const).measurable
  have h1 : ∫⁻ n : RSCarrier.finUnipotent, prodDensity v μNv μ₄ ((n : finiteAdelicGL2Subgroup ℚ) * g) ∂μN =
      ∫⁻ p, prodDensity v μNv μ₄ ((((unipSplit v).symm p : RSCarrier.finUnipotent) : finiteAdelicGL2Subgroup ℚ) * g)
        ∂(μN.map (unipSplit v)) := by
    have hf' : Measurable fun p : (unipotentGL2Hom (R := v.adicCompletion ℚ)).range × (unipLocal v).ker =>
        prodDensity v μNv μ₄ ((((unipSplit v).symm p : RSCarrier.finUnipotent) : finiteAdelicGL2Subgroup ℚ) * g) :=
      hf.comp hsc'.measurable
    rw [lintegral_map hf' hsc.measurable]
    simp only [ContinuousMulEquiv.symm_apply_apply]

  have h2 : ∀ p : (unipotentGL2Hom (R := v.adicCompletion ℚ)).range × (unipLocal v).ker,
      prodDensity v μNv μ₄ ((((unipSplit v).symm p : RSCarrier.finUnipotent) : finiteAdelicGL2Subgroup ℚ) * g) =
        density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μNv
            ((p.1 : GL (Fin 2) (v.adicCompletion ℚ)) * localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ)) *
          density (unipotentAway v) μ₄
            ((((p.2 : RSCarrier.finUnipotent)) : finiteAdelicGL2Subgroup ℚ) *
              (sectionAt v (p.1 : GL (Fin 2) (v.adicCompletion ℚ)) * kerpart v g *
                (sectionAt v (p.1 : GL (Fin 2) (v.adicCompletion ℚ)))⁻¹)) := by
    intro p
    rw [unipSplit_symm_apply, Subgroup.coe_mul, coe_unipSection]
    have hk := localAt_coe_of_mem_unipotentAway v ⟨_, mem_unipotentAway_of_mem_ker v p.2⟩
    exact prodDensity_ker_mul_sectionAt_mul v μNv μ₄ _ hk _ g

  have h3 : ∀ h : finiteAdelicGL2Subgroup ℚ,
      ∫⁻ k : (unipLocal v).ker,
        density (unipotentAway v) μ₄ ((((k : RSCarrier.finUnipotent)) : finiteAdelicGL2Subgroup ℚ) * h) ∂μ₂ = 1 := by
    intro h
    have hm : Measurable fun u : unipotentAway v =>
        density (unipotentAway v) μ₄ ((u : finiteAdelicGL2Subgroup ℚ) * h) :=
      hρ₄.comp (continuous_subtype_val.mul continuous_const).measurable
    have this := HaarQuotient.lintegral_density_mul_eq_one _ (isClosed_unipotentAway v) μ₄ h
    have hmap' : ∫⁻ u : unipotentAway v, density (unipotentAway v) μ₄ ((u : finiteAdelicGL2Subgroup ℚ) * h) ∂μ₄ =
        ∫⁻ k : (unipLocal v).ker,
          density (unipotentAway v) μ₄ ((kerAwayEquiv v k : finiteAdelicGL2Subgroup ℚ) * h) ∂μ₂ :=
      lintegral_map hm hkc.measurable
    rw [hmap'] at this
    simpa only [coe_kerAwayEquiv] using this
  have hpm : Measurable fun p : (unipotentGL2Hom (R := v.adicCompletion ℚ)).range × (unipLocal v).ker =>
      prodDensity v μNv μ₄ ((((unipSplit v).symm p : RSCarrier.finUnipotent) : finiteAdelicGL2Subgroup ℚ) * g) :=
    (measurable_prodDensity v μNv μ₄).comp ((continuous_subtype_val.comp hsc').mul continuous_const).measurable
  rw [h1, hmap, lintegral_prod _ hpm.aemeasurable]
  simp only [h2]
  have h4 : ∀ x : (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
      ∫⁻ k : (unipLocal v).ker,
          density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μNv
              ((x : GL (Fin 2) (v.adicCompletion ℚ)) * localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ)) *
            density (unipotentAway v) μ₄
              ((((k : RSCarrier.finUnipotent)) : finiteAdelicGL2Subgroup ℚ) *
                (sectionAt v (x : GL (Fin 2) (v.adicCompletion ℚ)) * kerpart v g *
                  (sectionAt v (x : GL (Fin 2) (v.adicCompletion ℚ)))⁻¹)) ∂μ₂ =
        density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μNv
          ((x : GL (Fin 2) (v.adicCompletion ℚ)) * localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ)) := by
    intro x
    have hmk : Measurable fun k : (unipLocal v).ker =>
        density (unipotentAway v) μ₄
          ((((k : RSCarrier.finUnipotent)) : finiteAdelicGL2Subgroup ℚ) *
            (sectionAt v (x : GL (Fin 2) (v.adicCompletion ℚ)) * kerpart v g *
              (sectionAt v (x : GL (Fin 2) (v.adicCompletion ℚ)))⁻¹)) :=
      hρ₄.comp ((continuous_subtype_val.comp continuous_subtype_val).mul continuous_const).measurable
    rw [lintegral_const_mul _ hmk, h3, mul_one]
  simp only [h4]
  exact HaarQuotient.lintegral_density_mul_eq_one _ (isClosed_range_unipotentGL2Hom (R := v.adicCompletion ℚ)) μNv _

end Contracts

section Reduction

variable (v : HeightOneSpectrum (𝓞 ℚ))

private local instance : MeasurableSpace (GL (Fin 2) (v.adicCompletion ℚ)) :=
  borel (GL (Fin 2) (v.adicCompletion ℚ))

private local instance : BorelSpace (GL (Fin 2) (v.adicCompletion ℚ)) := ⟨rfl⟩

private local instance : BorelSpace (AdelicGL2 (𝓞 ℚ) ℚ) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 ℚ) ℚ

private theorem integral_mul_prodDensity_eq (μ : Measure (finiteAdelicGL2Subgroup ℚ))
    [SecondCountableTopology (finiteAdelicGL2Subgroup ℚ)]
    (μv : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μv.IsHaarMeasure]
    (μ' : Measure ((localAt ℚ v).comp (finiteAdelicGL2Subgroup ℚ).subtype).ker) [μ'.IsHaarMeasure]
    (hmap : Measure.map (fun g : finiteAdelicGL2Subgroup ℚ => (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ), kerpart v g)) μ =
      μv.prod (Measure.map Subtype.val μ'))
    (μNv : Measure (unipotentGL2Hom (R := v.adicCompletion ℚ)).range) (μ₄ : Measure (unipotentAway v))
    (Φ : finiteAdelicGL2Subgroup ℚ → ℂ)
    (hΦ : Integrable (fun g => Φ g * (((prodDensity v μNv μ₄ g).toReal : ℝ) : ℂ)) μ) :
    ∫ g, Φ g * (((prodDensity v μNv μ₄ g).toReal : ℝ) : ℂ) ∂μ =
      ∫ x, (((density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μNv x).toReal : ℝ) : ℂ) *
        (∫ k, Φ (k * sectionAt v x) * (((density (unipotentAway v) μ₄ k).toReal : ℝ) : ℂ)
          ∂(Measure.map Subtype.val μ')) ∂μv := by
  haveI : LocallyCompactSpace (GL (Fin 2) (v.adicCompletion ℚ)) := locallyCompactSpace_localGL ℚ v
  haveI : SigmaCompactSpace (GL (Fin 2) (v.adicCompletion ℚ)) := inferInstance
  haveI : LocallyCompactSpace (finiteAdelicGL2Subgroup ℚ) := locallyCompactSpace_finiteAdelicGL2Subgroup
  haveI : SigmaCompactSpace (finiteAdelicGL2Subgroup ℚ) := inferInstance
  haveI := sigmaCompactSpace_of_isClosed _ (isClosed_ker_localAt v)
  haveI := sfinite_of_isHaarMeasure μ'
  have hΘ := measurableEmbedding_split v
  have hmap' : Measure.map (Splitting.splitMap ((localAt ℚ v).comp (finiteAdelicGL2Subgroup ℚ).subtype)
      (sectionAt v)) μ = μv.prod (Measure.map Subtype.val μ') := hmap
  obtain ⟨-, heq⟩ := Splitting.integral_eq_integral_integral_of_map_eq_prod hΘ hmap'
    (Splitting.snd_mul_section_fst _ _) hΦ
  refine heq.trans ?_
  refine integral_congr_ae ?_
  filter_upwards with x
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Splitting.ae_mem_map_subtype_val (measurableSet_ker_localAt v) μ'] with k hk
  have hk1 : localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := MonoidHom.mem_ker.mp (SetLike.mem_coe.mp hk)
  rw [prodDensity_mul_sectionAt v μNv μ₄ k x hk1, ENNReal.toReal_mul, Complex.ofReal_mul]
  ring

private theorem integrable_kernelIntegral (μ : Measure (finiteAdelicGL2Subgroup ℚ))
    [SecondCountableTopology (finiteAdelicGL2Subgroup ℚ)]
    (μv : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μv.IsHaarMeasure]
    (μ' : Measure ((localAt ℚ v).comp (finiteAdelicGL2Subgroup ℚ).subtype).ker) [μ'.IsHaarMeasure]
    (hmap : Measure.map (fun g : finiteAdelicGL2Subgroup ℚ => (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ), kerpart v g)) μ =
      μv.prod (Measure.map Subtype.val μ'))
    (μNv : Measure (unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μNv.IsHaarMeasure]
    (μ₄ : Measure (unipotentAway v)) [μ₄.IsHaarMeasure] (s : ℂ) (W F : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hΦ : Integrable (fun g : finiteAdelicGL2Subgroup ℚ =>
      (W g * F g) * ((finWeight g : ℝ) : ℂ) ^ (s - 1 / 2) * (((prodDensity v μNv μ₄ g).toReal : ℝ) : ℂ)) μ) :
    Integrable
      (fun x : GL (Fin 2) (v.adicCompletion ℚ) =>
        (kernelIntegral v (Measure.map Subtype.val μ') (density (unipotentAway v) μ₄) s W F x * 1) *
          ((localWeight v x : ℝ) : ℂ) ^ (s - 1 / 2))
      (μv.withDensity (density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μNv)) := by
  haveI : LocallyCompactSpace (GL (Fin 2) (v.adicCompletion ℚ)) := locallyCompactSpace_localGL ℚ v
  haveI : SigmaCompactSpace (GL (Fin 2) (v.adicCompletion ℚ)) := inferInstance
  haveI : LocallyCompactSpace (finiteAdelicGL2Subgroup ℚ) := locallyCompactSpace_finiteAdelicGL2Subgroup
  haveI : SigmaCompactSpace (finiteAdelicGL2Subgroup ℚ) := inferInstance
  haveI := sigmaCompactSpace_of_isClosed _ (isClosed_ker_localAt v)
  haveI := sfinite_of_isHaarMeasure μ'
  have hΘ := measurableEmbedding_split v
  have hmap' : Measure.map (Splitting.splitMap ((localAt ℚ v).comp (finiteAdelicGL2Subgroup ℚ).subtype)
      (sectionAt v)) μ = μv.prod (Measure.map Subtype.val μ') := hmap
  obtain ⟨hint, -⟩ := Splitting.integral_eq_integral_integral_of_map_eq_prod hΘ hmap'
    (Splitting.snd_mul_section_fst _ _) hΦ
  haveI := sigmaCompactSpace_of_isClosed _ (isClosed_range_unipotentGL2Hom (R := v.adicCompletion ℚ))
  haveI := sfinite_of_isHaarMeasure μNv
  rw [integrable_withDensity_iff_integrable_smul' (measurable_density _ μNv)
    (Filter.Eventually.of_forall fun x => (localDensity_ne_top v μNv x).lt_top)]
  refine hint.congr ?_
  filter_upwards with x
  rw [Complex.real_smul]
  have hinner : ∀ᵐ k ∂(Measure.map Subtype.val μ'),
      (W ((k * sectionAt v x : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) *
            F ((k * sectionAt v x : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) *
          ((finWeight (k * sectionAt v x) : ℝ) : ℂ) ^ (s - 1 / 2) *
          (((prodDensity v μNv μ₄ (k * sectionAt v x)).toReal : ℝ) : ℂ) =
        ((((density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μNv x).toReal : ℝ) : ℂ) *
            ((localWeight v x : ℝ) : ℂ) ^ (s - 1 / 2)) *
          ((W ((k * sectionAt v x : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) *
                F ((k * sectionAt v x : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) *
              ((finWeight k : ℝ) : ℂ) ^ (s - 1 / 2) * (((density (unipotentAway v) μ₄ k).toReal : ℝ) : ℂ)) := by
    filter_upwards [Splitting.ae_mem_map_subtype_val (measurableSet_ker_localAt v) μ'] with k hk
    have hk1 : localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := MonoidHom.mem_ker.mp (SetLike.mem_coe.mp hk)
    rw [prodDensity_mul_sectionAt v μNv μ₄ k x hk1, ENNReal.toReal_mul, Complex.ofReal_mul,
      finWeight_mul_sectionAt v k x, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (finWeight_pos k).le (localWeight_pos v x).le]
    ring
  rw [integral_congr_ae hinner, integral_const_mul]
  unfold kernelIntegral
  ring

private theorem kernelIntegral_unipotent_mul
    (μ' : Measure ((localAt ℚ v).comp (finiteAdelicGL2Subgroup ℚ).subtype).ker)
    (ρ' : finiteAdelicGL2Subgroup ℚ → ℝ≥0∞) (s : ℂ) (W F : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hinv : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
      W ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) *
          F ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
        W (g : AdelicGL2 (𝓞 ℚ) ℚ) * F (g : AdelicGL2 (𝓞 ℚ) ℚ))
    (n : GL (Fin 2) (v.adicCompletion ℚ)) (hn : n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range)
    (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    kernelIntegral v (Measure.map Subtype.val μ') ρ' s W F (n * x) =
      kernelIntegral v (Measure.map Subtype.val μ') ρ' s W F x := by
  unfold kernelIntegral
  refine integral_congr_ae ?_
  have hker : ∀ᵐ k ∂(Measure.map Subtype.val μ'),
      k ∈ (((localAt ℚ v).comp (finiteAdelicGL2Subgroup ℚ).subtype).ker : Set (finiteAdelicGL2Subgroup ℚ)) :=
    Splitting.ae_mem_map_subtype_val (measurableSet_ker_localAt v) μ'
  filter_upwards [hker] with k hk
  have hk1 : localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := MonoidHom.mem_ker.mp (SetLike.mem_coe.mp hk)
  have hmem : sectionAt v n ∈ RSCarrier.finUnipotent := sectionAt_mem_finUnipotent v n hn
  have hprod : (k * sectionAt v (n * x) : finiteAdelicGL2Subgroup ℚ) =
      ((⟨sectionAt v n, hmem⟩ : RSCarrier.finUnipotent) : finiteAdelicGL2Subgroup ℚ) * (k * sectionAt v x) := by
    rw [map_mul, ← mul_assoc, ← sectionAt_mul_comm v n k hk1, mul_assoc]
  rw [hprod, hinv]

private theorem kernelIntegral_mul_levelOne (μ' : Measure (finiteAdelicGL2Subgroup ℚ))
    (ρ' : finiteAdelicGL2Subgroup ℚ → ℝ≥0∞) (s : ℂ) (W F : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hWK : ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      x ∈ localLevelOne (𝓞 ℚ) ℚ v ⊤ → W (g * placeEmbed ℚ v x) = W g)
    (hFK : ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      x ∈ localLevelOne (𝓞 ℚ) ℚ v ⊤ → F (g * placeEmbed ℚ v x) = F g)
    (k : GL (Fin 2) (v.adicCompletion ℚ)) (hk : k ∈ localLevelOne (𝓞 ℚ) ℚ v ⊤) (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    kernelIntegral v μ' ρ' s W F (x * k) = kernelIntegral v μ' ρ' s W F x := by
  unfold kernelIntegral
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  have hcoe : ((g * sectionAt v (x * k) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) =
      ((g * sectionAt v x : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) * placeEmbed ℚ v k := by
    rw [map_mul, ← mul_assoc, Subgroup.coe_mul]
    rfl
  simp only [hcoe, hWK k, hFK k, hk]

private theorem kernelIntegral_torusPt (μ' : Measure ((localAt ℚ v).comp (finiteAdelicGL2Subgroup ℚ).subtype).ker)
    (ρ' : finiteAdelicGL2Subgroup ℚ → ℝ≥0∞) (s : ℂ) (W F : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0) (c : ℤ × ℤ → ℂ)
    (heval : ∀ (k : finiteAdelicGL2Subgroup ℚ), localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1 → ∀ p : ℤ × ℤ,
      W ((k * sectionAt v (torusPt v hπ p) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) *
          F ((k * sectionAt v (torusPt v hπ p) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) =
        c p * (W (k : AdelicGL2 (𝓞 ℚ) ℚ) * F (k : AdelicGL2 (𝓞 ℚ) ℚ)))
    (p : ℤ × ℤ) :
    kernelIntegral v (Measure.map Subtype.val μ') ρ' s W F (torusPt v hπ p) =
      c p * kernelIntegral v (Measure.map Subtype.val μ') ρ' s W F 1 := by
  unfold kernelIntegral
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  have hker : ∀ᵐ k ∂(Measure.map Subtype.val μ'),
      k ∈ (((localAt ℚ v).comp (finiteAdelicGL2Subgroup ℚ).subtype).ker : Set (finiteAdelicGL2Subgroup ℚ)) :=
    Splitting.ae_mem_map_subtype_val (measurableSet_ker_localAt v) μ'
  filter_upwards [hker] with k hk
  have hk1 : localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := MonoidHom.mem_ker.mp (SetLike.mem_coe.mp hk)
  rw [heval k hk1 p, map_one, mul_one]
  ring

private theorem integral_cell_eq (μv : Measure (GL (Fin 2) (v.adicCompletion ℚ)))
    (μNv : Measure (unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μNv.IsHaarMeasure] (s : ℂ)
    (Ψ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hΨN : ∀ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range, ∀ x, Ψ (n * x) = Ψ x)
    (hΨK : ∀ k ∈ localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ x, Ψ (x * k) = Ψ x) :
    ∫ x, ({x : GL (Fin 2) (v.adicCompletion ℚ) |
            ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
              ∃ k ∈ localLevelOne (𝓞 ℚ) ℚ v ⊤, x = n * k}.indicator Ψ x *
          ((localWeight v x : ℝ) : ℂ) ^ (s - 1 / 2))
        ∂(μv.withDensity (density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μNv)) =
      (((μv.withDensity (density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μNv))
          {x : GL (Fin 2) (v.adicCompletion ℚ) |
            ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
              ∃ k ∈ localLevelOne (𝓞 ℚ) ℚ v ⊤, x = n * k}).toReal : ℂ) * Ψ 1 := by
  have hS : MeasurableSet {x : GL (Fin 2) (v.adicCompletion ℚ) |
      ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range, ∃ k ∈ localLevelOne (𝓞 ℚ) ℚ v ⊤, x = n * k} :=
    (isOpen_localCell v).measurableSet
  have hpt : ∀ x, {x : GL (Fin 2) (v.adicCompletion ℚ) |
        ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range, ∃ k ∈ localLevelOne (𝓞 ℚ) ℚ v ⊤,
          x = n * k}.indicator Ψ x * ((localWeight v x : ℝ) : ℂ) ^ (s - 1 / 2) =
      {x : GL (Fin 2) (v.adicCompletion ℚ) |
        ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range, ∃ k ∈ localLevelOne (𝓞 ℚ) ℚ v ⊤,
          x = n * k}.indicator (fun _ => Ψ 1) x := by
    intro x
    by_cases hx : x ∈ {x : GL (Fin 2) (v.adicCompletion ℚ) |
        ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range, ∃ k ∈ localLevelOne (𝓞 ℚ) ℚ v ⊤, x = n * k}
    · obtain ⟨n, hn, k, hk, hxnk⟩ := id hx
      subst hxnk
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, hΨN n hn, ← one_mul k, hΨK k hk, one_mul,
        localWeight_unipotent_mul v n hn, ← one_mul k, localWeight_mul_levelOne v k hk, localWeight_one]
      simp
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  simp_rw [hpt]
  rw [integral_indicator_const _ hS, measureReal_def, Complex.real_smul]

end Reduction

section Assembly

variable (v : HeightOneSpectrum (𝓞 ℚ))

private local instance : MeasurableSpace (GL (Fin 2) (v.adicCompletion ℚ)) :=
  borel (GL (Fin 2) (v.adicCompletion ℚ))

private local instance : BorelSpace (GL (Fin 2) (v.adicCompletion ℚ)) := ⟨rfl⟩

private local instance : BorelSpace (AdelicGL2 (𝓞 ℚ) ℚ) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 ℚ) ℚ

private theorem absNorm_pos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  have h : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  exact_mod_cast Nat.pos_of_ne_zero h

private theorem norm_seriesTerm_eq (s lam om : ℂ) (uZ : ℤ → ℤ → ℂ) (p : ℤ × ℤ) :
    ((‖seriesTerm v s lam om uZ p‖ : ℝ) : ℂ) =
      (Ideal.absNorm v.asIdeal : ℂ) ^ (p.1 - p.2) * ((‖cellValue v lam om uZ p‖ : ℝ) : ℂ) *
        ((((Ideal.absNorm v.asIdeal : ℝ) ^ (-(p.1 + p.2)) : ℝ) : ℂ) ^ (((s.re : ℝ) : ℂ) - 1 / 2)) := by
  have hr := absNorm_pos v
  have hw : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) ^ (-(p.1 + p.2)) := zpow_pos hr _
  unfold seriesTerm
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hw, norm_zpow, Complex.norm_natCast]
  set w : ℝ := (Ideal.absNorm v.asIdeal : ℝ) ^ (-(p.1 + p.2)) with hwdef
  have e : ((w : ℂ) ^ (((s.re : ℝ) : ℂ) - 1 / 2)) = Complex.ofReal (w ^ (s - 1 / 2).re) := by
    rw [Complex.ofReal_cpow hw.le]
    congr 1
    simp only [Complex.sub_re, Complex.ofReal_sub]
    norm_num
  rw [e]
  push_cast
  ring

private theorem locallyCompactSpace_local : LocallyCompactSpace (GL (Fin 2) (v.adicCompletion ℚ)) := by
  exact locallyCompactSpace_localGL ℚ v

private theorem locallyCompactSpace_localUnipotent :
    LocallyCompactSpace (unipotentGL2Hom (R := v.adicCompletion ℚ)).range := by
  haveI := locallyCompactSpace_localGL ℚ v
  exact (isClosed_range_unipotentGL2Hom (R := v.adicCompletion ℚ)).locallyCompactSpace

private theorem cell_sum [SecondCountableTopology (GL (Fin 2) (v.adicCompletion ℚ))] {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ)) :
    ∀ (μ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ.IsHaarMeasure]
      (μN : Measure (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure]
      [μN.IsMulRightInvariant]
      (δ : GL (Fin 2) (v.adicCompletion ℚ) → ℝ)
      (_hδN : ∀ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
        ∀ g : GL (Fin 2) (v.adicCompletion ℚ), δ (n * g) = δ g)
      (_hδK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
        ∀ g : GL (Fin 2) (v.adicCompletion ℚ), δ (g * k) = δ g)
      (s : ℂ) (W F : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
      (_hN : ∀ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
        ∀ g : GL (Fin 2) (v.adicCompletion ℚ), W (n * g) * F (n * g) = W g * F g)
      (_hK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
        ∀ g : GL (Fin 2) (v.adicCompletion ℚ), W (g * k) * F (g * k) = W g * F g)
      (_hint : Integrable
        (fun g : GL (Fin 2) (v.adicCompletion ℚ) => (W g * F g) * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2))
        (μ.withDensity
          (HaarQuotient.density (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))),
      HasSum (fun p : ℤ × ℤ =>
          (((μ.withDensity
                (HaarQuotient.density (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))
              {g : GL (Fin 2) (v.adicCompletion ℚ) |
                ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                  ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, g = n * k}).toReal : ℂ) *
            ((Ideal.absNorm v.asIdeal : ℂ) ^ (p.1 - p.2)) *
            ((W (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (p.1 - p.2) *
                  scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ p.2) *
                F (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (p.1 - p.2) *
                  scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ p.2)) *
              ((δ (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (p.1 - p.2) *
                  scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ p.2) :
                    ℝ) : ℂ) ^ (s - 1 / 2)))
        (RSCarrier.rsLocalIntegral μ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN δ s W
          F) :=
  hasSum_cell_terms_rsLocalIntegral v hπ hϖ

private theorem haar_splits [SecondCountableTopology (finiteAdelicGL2Subgroup ℚ)]
    (μ : Measure (finiteAdelicGL2Subgroup ℚ)) [μ.IsHaarMeasure] :
    ∀ (μv : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μv.IsHaarMeasure],
      ∃ μ' : Measure ((localAt ℚ v).comp (finiteAdelicGL2Subgroup ℚ).subtype).ker,
        μ'.IsHaarMeasure ∧
          Measure.map
              (fun g : finiteAdelicGL2Subgroup ℚ =>
                (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ), g * (sectionAt v (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ)))⁻¹))
              μ =
            μv.prod (Measure.map Subtype.val μ') :=
  exists_isHaarMeasure_map_eq_prod_localAt v (sectionAt v) (continuous_sectionAt v) (localAt_sectionAt v)
    (sectionAt_mul_comm v) μ

private theorem mem_preCell_iff (g : finiteAdelicGL2Subgroup ℚ) :
    g ∈ preCell v ↔ localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ localCell v :=
  Iff.rfl

private theorem mem_localCell_unipotent_mul_iff {n : GL (Fin 2) (v.adicCompletion ℚ)}
    (hn : n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range) (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    n * x ∈ localCell v ↔ x ∈ localCell v := by
  constructor
  · rintro ⟨n', hn', k, hk, h⟩
    refine ⟨n⁻¹ * n', mul_mem (inv_mem hn) hn', k, hk, ?_⟩
    rw [mul_assoc, ← h, inv_mul_cancel_left]
  · rintro ⟨n', hn', k, hk, h⟩
    exact ⟨n * n', mul_mem hn hn', k, hk, by rw [h, mul_assoc]⟩

private theorem mem_preCell_unipotent_mul_iff (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ) :
    (n : finiteAdelicGL2Subgroup ℚ) * g ∈ preCell v ↔ g ∈ preCell v := by
  rw [mem_preCell_iff, mem_preCell_iff, Subgroup.coe_mul, map_mul]
  exact mem_localCell_unipotent_mul_iff v (localAt_mem_range_of_mem_finUnipotent v n) _

private theorem measurableSet_preCell : MeasurableSet (preCell v) := by
  have hopen : IsOpen (localCell v) := isOpen_localCell v
  exact (hopen.preimage ((continuous_localAt (K := ℚ) (v := v)).comp continuous_subtype_val)).measurableSet

private theorem integral_weighted_pair_sectionAt (μ'G : Measure (finiteAdelicGL2Subgroup ℚ))
    (ρ' : finiteAdelicGL2Subgroup ℚ → ℝ≥0∞) (s : ℂ) (W F : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    ∫ k, (W ((k * sectionAt v x : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) *
          F ((k * sectionAt v x : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) *
        ((finWeight (k * sectionAt v x) : ℝ) : ℂ) ^ (s - 1 / 2) * (((ρ' k).toReal : ℝ) : ℂ) ∂μ'G =
      ((localWeight v x : ℝ) : ℂ) ^ (s - 1 / 2) * kernelIntegral v μ'G ρ' s W F x := by
  unfold kernelIntegral
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  beta_reduce
  rw [finWeight_mul_sectionAt v k x, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (finWeight_pos k).le (localWeight_pos v x).le]
  ring

private theorem carrier_eq_local (μ : Measure (finiteAdelicGL2Subgroup ℚ)) [μ.IsHaarMeasure]
    (μN : Measure RSCarrier.finUnipotent) [μN.IsHaarMeasure] [SecondCountableTopology (finiteAdelicGL2Subgroup ℚ)]
    (μv : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μv.IsHaarMeasure]
    (μ' : Measure ((localAt ℚ v).comp (finiteAdelicGL2Subgroup ℚ).subtype).ker) [μ'.IsHaarMeasure]
    (hmap : Measure.map (fun g : finiteAdelicGL2Subgroup ℚ => (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ), kerpart v g)) μ =
      μv.prod (Measure.map Subtype.val μ'))
    (μNv : Measure (unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μNv.IsHaarMeasure]
    (μ₄ : Measure (unipotentAway v)) [μ₄.IsHaarMeasure]
    (hρ₂ : ∀ g : finiteAdelicGL2Subgroup ℚ,
      ∫⁻ n : RSCarrier.finUnipotent, prodDensity v μNv μ₄ ((n : finiteAdelicGL2Subgroup ℚ) * g) ∂μN = 1)
    (s : ℂ) (W F : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hinv : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
      W ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) *
          F ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
        W (g : AdelicGL2 (𝓞 ℚ) ℚ) * F (g : AdelicGL2 (𝓞 ℚ) ℚ))
    (hint : Integrable
      (fun g : finiteAdelicGL2Subgroup ℚ => (W g * F g) *
        ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2))
      (μ.withDensity (density RSCarrier.finUnipotent μN))) :
    Integrable
        (fun x : GL (Fin 2) (v.adicCompletion ℚ) =>
          (kernelIntegral v (Measure.map Subtype.val μ') (density (unipotentAway v) μ₄) s W F x * 1) *
            ((localWeight v x : ℝ) : ℂ) ^ (s - 1 / 2))
        (μv.withDensity (density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μNv)) ∧
      RSCarrier.rsFinIntegral μ μN s (fun g => W g) (fun g => F g) =
        RSCarrier.rsLocalIntegral μv (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μNv (localWeight v) s
          (kernelIntegral v (Measure.map Subtype.val μ') (density (unipotentAway v) μ₄) s W F) (fun _ => 1) := by
  haveI : LocallyCompactSpace (GL (Fin 2) (v.adicCompletion ℚ)) := locallyCompactSpace_localGL ℚ v
  haveI : SigmaCompactSpace (GL (Fin 2) (v.adicCompletion ℚ)) := inferInstance
  haveI : LocallyCompactSpace (finiteAdelicGL2Subgroup ℚ) := locallyCompactSpace_finiteAdelicGL2Subgroup
  haveI : SigmaCompactSpace (finiteAdelicGL2Subgroup ℚ) := inferInstance
  haveI : SigmaCompactSpace RSCarrier.finUnipotent := sigmaCompactSpace_of_isClosed _ isClosed_finUnipotent
  haveI := sigmaCompactSpace_of_isClosed _ (isClosed_range_unipotentGL2Hom (R := v.adicCompletion ℚ))
  haveI := sfinite_of_isHaarMeasure μ
  haveI := sfinite_of_isHaarMeasure μN
  haveI := sfinite_of_isHaarMeasure μNv

  have hint' : Integrable
      (fun g : finiteAdelicGL2Subgroup ℚ => (W g * F g) * ((finWeight g : ℝ) : ℂ) ^ (s - 1 / 2))
      (μ.withDensity (density RSCarrier.finUnipotent μN)) := hint
  have hfinv : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
      (W ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) *
          F ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ)) *
        ((finWeight ((n : finiteAdelicGL2Subgroup ℚ) * g) : ℝ) : ℂ) ^ (s - 1 / 2) =
      (W (g : AdelicGL2 (𝓞 ℚ) ℚ) * F (g : AdelicGL2 (𝓞 ℚ) ℚ)) * ((finWeight g : ℝ) : ℂ) ^ (s - 1 / 2) := by
    intro n g
    rw [hinv n g, finWeight_unipotent_mul n g]

  obtain ⟨hint₂, heq⟩ := Admissible.integral_withDensity_eq_of_invariant μ μN (lintegral_inv_finUnipotent μN)
    (measurable_density RSCarrier.finUnipotent μN) (measurable_prodDensity v μNv μ₄) (lintegral_finDensity_eq_one μN)
    hρ₂
    (finDensity_ne_top μN) (prodDensity_ne_top v μNv μ₄) hfinv hint'
  have hΦ : Integrable (fun g : finiteAdelicGL2Subgroup ℚ =>
      (W g * F g) * ((finWeight g : ℝ) : ℂ) ^ (s - 1 / 2) * (((prodDensity v μNv μ₄ g).toReal : ℝ) : ℂ)) μ := by
    refine (Admissible.integrable_toReal_smul_of_integrable_withDensity μ (measurable_prodDensity v μNv μ₄)
      (prodDensity_ne_top v μNv μ₄) hint₂).congr (Filter.Eventually.of_forall fun g => ?_)
    simp only [Complex.real_smul]
    ring
  refine ⟨integrable_kernelIntegral v μ μv μ' hmap μNv μ₄ s W F hΦ, ?_⟩

  unfold RSCarrier.rsFinIntegral RSCarrier.rsLocalIntegral
  show ∫ g, (W g * F g) * ((finWeight g : ℝ) : ℂ) ^ (s - 1 / 2) ∂(μ.withDensity (density RSCarrier.finUnipotent μN)) =
    ∫ x, (kernelIntegral v (Measure.map Subtype.val μ') (density (unipotentAway v) μ₄) s W F x * 1) *
      ((localWeight v x : ℝ) : ℂ) ^ (s - 1 / 2)
      ∂(μv.withDensity (density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μNv))
  rw [← heq, integral_withDensity_eq_integral_toReal_smul (measurable_prodDensity v μNv μ₄)
    (Filter.Eventually.of_forall fun g => (prodDensity_ne_top v μNv μ₄ g).lt_top)]
  have h1 : ∫ g, (prodDensity v μNv μ₄ g).toReal •
        ((W g * F g) * ((finWeight g : ℝ) : ℂ) ^ (s - 1 / 2)) ∂μ =
      ∫ g, (W g * F g) * ((finWeight g : ℝ) : ℂ) ^ (s - 1 / 2) * (((prodDensity v μNv μ₄ g).toReal : ℝ) : ℂ) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [Complex.real_smul]
    ring
  rw [h1, integral_mul_prodDensity_eq v μ μv μ' hmap μNv μ₄ _ hΦ,
    integral_withDensity_eq_integral_toReal_smul (measurable_density _ μNv)
      (Filter.Eventually.of_forall fun x => (localDensity_ne_top v μNv x).lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  beta_reduce
  have hk : ∫ k, (W ((k * sectionAt v x : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) *
          F ((k * sectionAt v x : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) *
        ((finWeight (k * sectionAt v x) : ℝ) : ℂ) ^ (s - 1 / 2) *
        (((density (unipotentAway v) μ₄ k).toReal : ℝ) : ℂ) ∂(Measure.map Subtype.val μ') =
      ((localWeight v x : ℝ) : ℂ) ^ (s - 1 / 2) *
        kernelIntegral v (Measure.map Subtype.val μ') (density (unipotentAway v) μ₄) s W F x := by
    unfold kernelIntegral
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    beta_reduce
    rw [finWeight_mul_sectionAt v k x, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (finWeight_pos k).le (localWeight_pos v x).le]
    ring
  rw [hk, Complex.real_smul]
  ring

private theorem cell_carrier_eq (μ : Measure (finiteAdelicGL2Subgroup ℚ)) [μ.IsHaarMeasure]
    (μN : Measure RSCarrier.finUnipotent) [μN.IsHaarMeasure] [SecondCountableTopology (finiteAdelicGL2Subgroup ℚ)]
    (μv : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μv.IsHaarMeasure]
    (μ' : Measure ((localAt ℚ v).comp (finiteAdelicGL2Subgroup ℚ).subtype).ker) [μ'.IsHaarMeasure]
    (hmap : Measure.map (fun g : finiteAdelicGL2Subgroup ℚ => (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ), kerpart v g)) μ =
      μv.prod (Measure.map Subtype.val μ'))
    (μNv : Measure (unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μNv.IsHaarMeasure]
    (μ₄ : Measure (unipotentAway v)) [μ₄.IsHaarMeasure]
    (hρ₂ : ∀ g : finiteAdelicGL2Subgroup ℚ,
      ∫⁻ n : RSCarrier.finUnipotent, prodDensity v μNv μ₄ ((n : finiteAdelicGL2Subgroup ℚ) * g) ∂μN = 1)
    (s : ℂ) (W F : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hWK : ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W (g * placeEmbed ℚ v x) = W g)
    (hFK : ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → F (g * placeEmbed ℚ v x) = F g)
    (hinv : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
      W ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) *
          F ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
        W (g : AdelicGL2 (𝓞 ℚ) ℚ) * F (g : AdelicGL2 (𝓞 ℚ) ℚ))
    (hint : Integrable
      (fun g : finiteAdelicGL2Subgroup ℚ => (W g * F g) *
        ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2))
      (μ.withDensity (density RSCarrier.finUnipotent μN))) :
    RSCarrier.rsFinIntegral μ μN s ((preCell v).indicator (fun g => W g)) ((preCell v).indicator (fun g => F g)) =
      cellMass v μv μNv * kernelIntegral v (Measure.map Subtype.val μ') (density (unipotentAway v) μ₄) s W F 1 := by
  haveI : LocallyCompactSpace (GL (Fin 2) (v.adicCompletion ℚ)) := locallyCompactSpace_localGL ℚ v
  haveI : SigmaCompactSpace (GL (Fin 2) (v.adicCompletion ℚ)) := inferInstance
  haveI : LocallyCompactSpace (finiteAdelicGL2Subgroup ℚ) := locallyCompactSpace_finiteAdelicGL2Subgroup
  haveI : SigmaCompactSpace (finiteAdelicGL2Subgroup ℚ) := inferInstance
  haveI : SigmaCompactSpace RSCarrier.finUnipotent := sigmaCompactSpace_of_isClosed _ isClosed_finUnipotent
  haveI := sigmaCompactSpace_of_isClosed _ (isClosed_range_unipotentGL2Hom (R := v.adicCompletion ℚ))
  haveI := sfinite_of_isHaarMeasure μ
  haveI := sfinite_of_isHaarMeasure μN
  haveI := sfinite_of_isHaarMeasure μNv

  have hint' : Integrable
      (fun g : finiteAdelicGL2Subgroup ℚ => (W g * F g) * ((finWeight g : ℝ) : ℂ) ^ (s - 1 / 2))
      (μ.withDensity (density RSCarrier.finUnipotent μN)) := hint
  have hindI : Integrable
      ((preCell v).indicator fun g : finiteAdelicGL2Subgroup ℚ => (W g * F g) * ((finWeight g : ℝ) : ℂ) ^ (s - 1 / 2))
      (μ.withDensity (density RSCarrier.finUnipotent μN)) := hint'.indicator (measurableSet_preCell v)
  have hfinv : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
      (preCell v).indicator
          (fun g : finiteAdelicGL2Subgroup ℚ => (W g * F g) * ((finWeight g : ℝ) : ℂ) ^ (s - 1 / 2))
          ((n : finiteAdelicGL2Subgroup ℚ) * g) =
        (preCell v).indicator
          (fun g : finiteAdelicGL2Subgroup ℚ => (W g * F g) * ((finWeight g : ℝ) : ℂ) ^ (s - 1 / 2)) g := by
    intro n g
    by_cases hg : g ∈ preCell v
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((mem_preCell_unipotent_mul_iff v n g).mpr hg), hinv n g,
        finWeight_unipotent_mul n g]
    · rw [Set.indicator_of_notMem hg,
        Set.indicator_of_notMem (fun h => hg ((mem_preCell_unipotent_mul_iff v n g).mp h))]

  obtain ⟨hint₂, heq⟩ := Admissible.integral_withDensity_eq_of_invariant μ μN (lintegral_inv_finUnipotent μN)
    (measurable_density RSCarrier.finUnipotent μN) (measurable_prodDensity v μNv μ₄) (lintegral_finDensity_eq_one μN)
    hρ₂ (finDensity_ne_top μN) (prodDensity_ne_top v μNv μ₄) hfinv hindI
  have hΦ : Integrable (fun g : finiteAdelicGL2Subgroup ℚ =>
      (preCell v).indicator
          (fun g : finiteAdelicGL2Subgroup ℚ => (W g * F g) * ((finWeight g : ℝ) : ℂ) ^ (s - 1 / 2)) g *
        (((prodDensity v μNv μ₄ g).toReal : ℝ) : ℂ)) μ := by
    refine (Admissible.integrable_toReal_smul_of_integrable_withDensity μ (measurable_prodDensity v μNv μ₄)
      (prodDensity_ne_top v μNv μ₄) hint₂).congr (Filter.Eventually.of_forall fun g => ?_)
    simp only [Complex.real_smul]
    ring

  unfold RSCarrier.rsFinIntegral RSCarrier.rsLocalIntegral
  show ∫ g, ((preCell v).indicator (fun g : finiteAdelicGL2Subgroup ℚ => W g) g *
        (preCell v).indicator (fun g : finiteAdelicGL2Subgroup ℚ => F g) g) * ((finWeight g : ℝ) : ℂ) ^ (s - 1 / 2)
      ∂(μ.withDensity (density RSCarrier.finUnipotent μN)) = _
  have hL : ∫ g, ((preCell v).indicator (fun g : finiteAdelicGL2Subgroup ℚ => W g) g *
        (preCell v).indicator (fun g : finiteAdelicGL2Subgroup ℚ => F g) g) * ((finWeight g : ℝ) : ℂ) ^ (s - 1 / 2)
      ∂(μ.withDensity (density RSCarrier.finUnipotent μN)) =
      ∫ g, (preCell v).indicator
          (fun g : finiteAdelicGL2Subgroup ℚ => (W g * F g) * ((finWeight g : ℝ) : ℂ) ^ (s - 1 / 2)) g
        ∂(μ.withDensity (density RSCarrier.finUnipotent μN)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    by_cases hg : g ∈ preCell v
    · simp only [Set.indicator_of_mem hg]
    · simp only [Set.indicator_of_notMem hg, zero_mul]
  rw [hL, ← heq, integral_withDensity_eq_integral_toReal_smul (measurable_prodDensity v μNv μ₄)
    (Filter.Eventually.of_forall fun g => (prodDensity_ne_top v μNv μ₄ g).lt_top)]
  have h1 : ∫ g, (prodDensity v μNv μ₄ g).toReal •
        (preCell v).indicator
          (fun g : finiteAdelicGL2Subgroup ℚ => (W g * F g) * ((finWeight g : ℝ) : ℂ) ^ (s - 1 / 2)) g ∂μ =
      ∫ g, (preCell v).indicator
          (fun g : finiteAdelicGL2Subgroup ℚ => (W g * F g) * ((finWeight g : ℝ) : ℂ) ^ (s - 1 / 2)) g *
        (((prodDensity v μNv μ₄ g).toReal : ℝ) : ℂ) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [Complex.real_smul]
    ring
  rw [h1, integral_mul_prodDensity_eq v μ μv μ' hmap μNv μ₄ _ hΦ]

  have hinner : ∀ x : GL (Fin 2) (v.adicCompletion ℚ),
      (∫ k, (preCell v).indicator
            (fun g : finiteAdelicGL2Subgroup ℚ => (W g * F g) * ((finWeight g : ℝ) : ℂ) ^ (s - 1 / 2))
            (k * sectionAt v x) *
          (((density (unipotentAway v) μ₄ k).toReal : ℝ) : ℂ) ∂(Measure.map Subtype.val μ')) =
        (localCell v).indicator
          (fun x => ((localWeight v x : ℝ) : ℂ) ^ (s - 1 / 2) *
            kernelIntegral v (Measure.map Subtype.val μ') (density (unipotentAway v) μ₄) s W F x) x := by
    intro x
    have hmem : ∀ᵐ k ∂(Measure.map Subtype.val μ'), (k * sectionAt v x ∈ preCell v ↔ x ∈ localCell v) := by
      filter_upwards [Splitting.ae_mem_map_subtype_val (measurableSet_ker_localAt v) μ'] with k hk
      have hk1 : localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := MonoidHom.mem_ker.mp (SetLike.mem_coe.mp hk)
      rw [mem_preCell_iff, localAt_mul_sectionAt v k hk1 x]
    by_cases hx : x ∈ localCell v
    · rw [Set.indicator_of_mem hx,
        ← integral_weighted_pair_sectionAt v (Measure.map Subtype.val μ') (density (unipotentAway v) μ₄) s W F x]
      refine integral_congr_ae ?_
      filter_upwards [hmem] with k hk
      rw [Set.indicator_of_mem (hk.mpr hx)]
    · rw [Set.indicator_of_notMem hx]
      refine (integral_congr_ae (g := fun _ => (0 : ℂ)) ?_).trans (integral_zero _ _)
      filter_upwards [hmem] with k hk
      rw [Set.indicator_of_notMem (fun h => hx (hk.mp h)), zero_mul]
  simp only [hinner]

  have hcell : ∫ x, (localCell v).indicator
        (kernelIntegral v (Measure.map Subtype.val μ') (density (unipotentAway v) μ₄) s W F) x *
        ((localWeight v x : ℝ) : ℂ) ^ (s - 1 / 2)
        ∂(μv.withDensity (density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μNv)) =
      cellMass v μv μNv * kernelIntegral v (Measure.map Subtype.val μ') (density (unipotentAway v) μ₄) s W F 1 :=
    integral_cell_eq v μv μNv s _ (fun n hn x => kernelIntegral_unipotent_mul v μ' _ s W F hinv n hn x)
      (fun k hk x => kernelIntegral_mul_levelOne v _ _ s W F hWK hFK k hk x)
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_density _ μNv)
    (Filter.Eventually.of_forall fun x => (localDensity_ne_top v μNv x).lt_top)] at hcell
  refine Eq.trans ?_ hcell
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  beta_reduce
  by_cases hx : x ∈ localCell v
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Complex.real_smul]
    ring
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero, zero_mul, smul_zero]

private theorem integrable_abs_pair
    (μ : Measure (finiteAdelicGL2Subgroup ℚ)) (μN : Measure RSCarrier.finUnipotent) (s : ℂ)
    (W F : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hint : Integrable
      (fun g : finiteAdelicGL2Subgroup ℚ => (W g * F g) *
        ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2))
      (μ.withDensity (density RSCarrier.finUnipotent μN))) :
    Integrable
      (fun g : finiteAdelicGL2Subgroup ℚ => (((‖W g * F g‖ : ℝ) : ℂ) * (1 : ℂ)) *
        ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^
          (((s.re : ℝ) : ℂ) - 1 / 2))
      (μ.withDensity (density RSCarrier.finUnipotent μN)) := by
  exact Small.integrable_norm_pair _ (W := fun g : finiteAdelicGL2Subgroup ℚ => W g)
    (F := fun g : finiteAdelicGL2Subgroup ℚ => F g)
    (w := fun g : finiteAdelicGL2Subgroup ℚ =>
      TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)))
    (fun _ => TateGlobal.ideleNorm_pos _) s hint

private theorem norm_kernelIntegral_le
    (μ'G : Measure (finiteAdelicGL2Subgroup ℚ)) (ρ' : finiteAdelicGL2Subgroup ℚ → ℝ≥0∞)
    (s : ℂ) (W F : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    ‖kernelIntegral v μ'G ρ' s W F x‖ ≤
      ‖kernelIntegral v μ'G ρ' ((s.re : ℝ) : ℂ) (fun a => ((‖W a * F a‖ : ℝ) : ℂ)) (fun _ => (1 : ℂ)) x‖ := by
  unfold kernelIntegral
  exact Small.norm_integral_le_norm_integral_norm μ'G
    (a := fun k : finiteAdelicGL2Subgroup ℚ =>
      W ((k * sectionAt v x : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) *
        F ((k * sectionAt v x : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ))
    (w := finWeight) (fun k => finWeight_pos k) s (c := fun k => (ρ' k).toReal) (fun _ => ENNReal.toReal_nonneg)

end Assembly

end LanglandsTunnell.RankinSelberg.OnePlaceSplit

end

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RankinSelberg.mk_twoRowCauchySum_mul_coe_rsEulerPoly_eq_one RankinSelberg.mk_heckeRecursionSeq_mul_heckeRecursionSeq_mul_coe_rsEulerPoly_eq_and_hasSum RankinSelberg.exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow"
namespace RankinSelberg
p2m_export "LanglandsTunnell.RankinSelberg" "rsEulerPoly mk_twoRowCauchySum_mul_coe_rsEulerPoly_eq_one exists_isHaarMeasure_map_eq_prod_localAt hasSum_cell_terms_rsLocalIntegral mk_heckeRecursionSeq_mul_heckeRecursionSeq_mul_coe_rsEulerPoly_eq_and_hasSum exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow"
namespace FinPeel
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

def coef (N lam om lam' om' : ℂ) (p : ℤ × ℤ) : ℂ :=
  if 0 ≤ p.1 - p.2 ∧ 0 ≤ p.2 then
    (om * om') ^ p.2.toNat * heckeRecursionSeq N lam om (p.1 - p.2).toNat *
      heckeRecursionSeq N lam' om' (p.1 - p.2).toNat
  else 0

def term (q : ℕ) (s lam om lam' om' : ℂ) (p : ℤ × ℤ) : ℂ :=
  (q : ℂ) ^ (p.1 - p.2) * coef (q : ℂ) lam om lam' om' p *
    ((((q : ℝ) ^ (-(p.1 + p.2)) : ℝ) : ℂ) ^ (s - 1 / 2))

theorem weight_eq (q : ℕ) (_hq : 0 < q) (s : ℂ) (k : ℕ) :
    ((((q : ℝ) ^ (-(k : ℤ)) : ℝ) : ℂ) ^ (s - 1 / 2)) = ((q : ℂ) ^ (-(s - 1 / 2))) ^ k := by
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have e1 : ((q : ℝ) ^ (-(k : ℤ)) : ℝ) = (q : ℝ) ^ ((-(k : ℤ) : ℤ) : ℝ) := by
    rw [Real.rpow_intCast]
  rw [e1, ← Complex.ofReal_natCast, ← Complex.cpow_mul_ofReal_nonneg hq0, ← Complex.cpow_nat_mul]
  congr 1
  push_cast
  ring

theorem hasSum_term (q : ℕ) (hq : 2 ≤ q) (s lam om lam' om' : ℂ) (κ : ℝ)
    (hlam : ‖lam‖ ≤ (q : ℝ) ^ κ) (hom : ‖om‖ ≤ (q : ℝ) ^ κ)
    (hlam' : ‖lam'‖ ≤ (q : ℝ) ^ κ) (hom' : ‖om'‖ ≤ (q : ℝ) ^ κ)
    (hs : 2 * |κ| + 4 < s.re) :
    HasSum (term q s lam om lam' om')
      ((rsEulerPoly (lam / q) (om / q) (lam' / q) (om' / q) 0).eval ((q : ℂ) ^ ((3 / 2 : ℂ) - s)))⁻¹ := by

  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hqpos : 0 < q := by omega
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hκ : κ ≤ |κ| := le_abs_self κ
  have hκ0 : 0 ≤ |κ| := abs_nonneg κ
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq

  set y : ℂ := (q : ℂ) ^ (-(s - 1 / 2)) with hy
  set x : ℂ := (q : ℂ) ^ ((3 / 2 : ℂ) - s) with hx
  have hxy : x = (q : ℂ) * y := by
    rw [hx, hy, show ((3 / 2 : ℂ) - s) = 1 + (-(s - 1 / 2)) by ring, Complex.cpow_add _ _ hqC,
      Complex.cpow_one]
  have hnx : ‖x‖ = (q : ℝ) ^ (3 / 2 - s.re) := by
    rw [hx, Complex.norm_natCast_cpow_of_pos hqpos]
    congr 1
    simp
  have hny : ‖y‖ = (q : ℝ) ^ (-(s.re - 1 / 2)) := by
    rw [hy, Complex.norm_natCast_cpow_of_pos hqpos]
    congr 1
    simp

  have hdiv : ∀ c : ℂ, ‖c‖ ≤ (q : ℝ) ^ κ → ‖c / q‖ ≤ (q : ℝ) ^ |κ| := fun c hc => by
    rw [norm_div, Complex.norm_natCast]
    calc ‖c‖ / q ≤ ‖c‖ := div_le_self (norm_nonneg _) hq1.le
      _ ≤ (q : ℝ) ^ κ := hc
      _ ≤ (q : ℝ) ^ |κ| := Real.rpow_le_rpow_of_exponent_le hq1.le hκ
  have hMle : ∀ c d : ℂ, ‖c‖ ≤ (q : ℝ) ^ κ → ‖d‖ ≤ (q : ℝ) ^ κ →
      max 1 (‖c / q‖ + ‖d / q‖) ≤ 2 * (q : ℝ) ^ |κ| := fun c d hc hd => by
    have h1 : (1 : ℝ) ≤ (q : ℝ) ^ |κ| := Real.one_le_rpow hq1.le (abs_nonneg κ)
    refine max_le (by linarith) ?_
    have := hdiv c hc
    have := hdiv d hd
    linarith
  set M : ℝ := max 1 (‖lam / q‖ + ‖om / q‖) with hM
  set M' : ℝ := max 1 (‖lam' / q‖ + ‖om' / q‖) with hM'
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM'1 : 1 ≤ M' := le_max_left _ _
  have hMb : M ≤ 2 * (q : ℝ) ^ |κ| := hMle lam om hlam hom
  have hM'b : M' ≤ 2 * (q : ℝ) ^ |κ| := hMle lam' om' hlam' hom'

  have h4 : (4 : ℝ) ≤ (q : ℝ) ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    nlinarith
  have hsmall : ‖x‖ * (M * M') < 1 := by
    have hpk : 0 < (q : ℝ) ^ |κ| := Real.rpow_pos_of_pos hq0 _
    have hMM : M * M' ≤ 4 * ((q : ℝ) ^ |κ| * (q : ℝ) ^ |κ|) := by
      calc M * M' ≤ (2 * (q : ℝ) ^ |κ|) * (2 * (q : ℝ) ^ |κ|) :=
            mul_le_mul hMb hM'b (by linarith) (by linarith)
        _ = 4 * ((q : ℝ) ^ |κ| * (q : ℝ) ^ |κ|) := by ring
    have hkk : (q : ℝ) ^ |κ| * (q : ℝ) ^ |κ| = (q : ℝ) ^ (2 * |κ|) := by
      rw [← Real.rpow_add hq0]; congr 1; ring
    calc ‖x‖ * (M * M') ≤ (q : ℝ) ^ (3 / 2 - s.re) * (4 * (q : ℝ) ^ (2 * |κ|)) := by
          rw [← hkk]; rw [hnx]; exact mul_le_mul_of_nonneg_left hMM (Real.rpow_nonneg hq0.le _)
      _ ≤ (q : ℝ) ^ (3 / 2 - s.re) * ((q : ℝ) ^ (2 : ℝ) * (q : ℝ) ^ (2 * |κ|)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hq0.le _)
          exact mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hq0.le _)
      _ = (q : ℝ) ^ (3 / 2 - s.re + 2 + 2 * |κ|) := by
          rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]
          congr 1
          ring
      _ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)

  obtain ⟨-, hbU, h3⟩ :=
    LanglandsTunnell.RankinSelberg.mk_heckeRecursionSeq_mul_heckeRecursionSeq_mul_coe_rsEulerPoly_eq_and_hasSum
      (q : ℂ) lam om lam' om'
  obtain ⟨-, hbU', -⟩ :=
    LanglandsTunnell.RankinSelberg.mk_heckeRecursionSeq_mul_heckeRecursionSeq_mul_coe_rsEulerPoly_eq_and_hasSum
      (q : ℂ) lam' om' lam om
  obtain ⟨hR0, hA, -⟩ := h3 x hsmall

  set ξ : ℂ := om * om' * y ^ 2 with hξ
  have hnξ : ‖ξ‖ < 1 := by
    have hoo : ‖om‖ * ‖om'‖ ≤ (q : ℝ) ^ |κ| * (q : ℝ) ^ |κ| :=
      mul_le_mul (hom.trans (Real.rpow_le_rpow_of_exponent_le hq1.le hκ))
        (hom'.trans (Real.rpow_le_rpow_of_exponent_le hq1.le hκ)) (norm_nonneg _)
        (Real.rpow_nonneg hq0.le _)
    calc ‖ξ‖ = ‖om‖ * ‖om'‖ * ‖y‖ ^ 2 := by rw [hξ, norm_mul, norm_mul, norm_pow]
      _ ≤ (q : ℝ) ^ |κ| * (q : ℝ) ^ |κ| * ((q : ℝ) ^ (-(s.re - 1 / 2))) ^ 2 := by
          rw [hny]; exact mul_le_mul_of_nonneg_right hoo (sq_nonneg _)
      _ = (q : ℝ) ^ (2 * |κ| + 1 - 2 * s.re) := by
          rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hq0.le, ← Real.rpow_add hq0, ← Real.rpow_add hq0]
          congr 1; push_cast; ring
      _ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
  have hgeo : HasSum (fun n : ℕ => ξ ^ n) (1 - ξ)⁻¹ := hasSum_geometric_of_norm_lt_one hnξ

  have hsumA : Summable fun m : ℕ =>
      ‖heckeRecursionSeq (q : ℂ) lam om m * heckeRecursionSeq (q : ℂ) lam' om' m * x ^ m‖ := by
    have hr : ‖x‖ * (M * M') < 1 := hsmall
    have hr0 : 0 ≤ ‖x‖ * (M * M') := mul_nonneg (norm_nonneg _) (mul_nonneg (by linarith) (by linarith))
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
      (summable_geometric_of_lt_one hr0 hr)
    rw [norm_mul, norm_mul, norm_pow, mul_pow, mul_pow]
    have h1 := hbU m
    have h2 := hbU' m
    calc ‖heckeRecursionSeq (q : ℂ) lam om m‖ * ‖heckeRecursionSeq (q : ℂ) lam' om' m‖ * ‖x‖ ^ m
        ≤ M ^ m * M' ^ m * ‖x‖ ^ m := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg _) _)
          exact mul_le_mul h1 h2 (norm_nonneg _) (pow_nonneg (by linarith) _)
      _ = ‖x‖ ^ m * (M ^ m * M' ^ m) := by ring
  have hsumG : Summable fun n : ℕ => ‖ξ ^ n‖ := by
    simp only [norm_pow]
    exact summable_geometric_of_lt_one (norm_nonneg _) hnξ

  set f : ℕ → ℂ := fun m => heckeRecursionSeq (q : ℂ) lam om m * heckeRecursionSeq (q : ℂ) lam' om' m * x ^ m
    with hf
  set gg : ℕ → ℂ := fun n => ξ ^ n with hgg
  have hA' : HasSum f ((1 - om / q * (om' / q) * x ^ 2) /
      (rsEulerPoly (lam / q) (om / q) (lam' / q) (om' / q) 0).eval x) := hA
  have hgeo' : HasSum gg (1 - ξ)⁻¹ := hgeo
  have hsumA' : Summable fun m : ℕ => ‖f m‖ := hsumA
  have hsumG' : Summable fun n : ℕ => ‖gg n‖ := hsumG
  have hS : Summable fun mn : ℕ × ℕ => f mn.1 * gg mn.2 :=
    summable_mul_of_summable_norm (f := f) (g := gg) hsumA' hsumG'
  have hP : HasSum (fun mn : ℕ × ℕ => f mn.1 * gg mn.2)
      ((1 - om / q * (om' / q) * x ^ 2) / (rsEulerPoly (lam / q) (om / q) (lam' / q) (om' / q) 0).eval x *
        (1 - ξ)⁻¹) :=
    HasSum.mul (f := f) (g := gg) hA' hgeo' hS

  have hval : (1 - om / q * (om' / q) * x ^ 2) /
        (rsEulerPoly (lam / q) (om / q) (lam' / q) (om' / q) 0).eval x * (1 - ξ)⁻¹ =
      ((rsEulerPoly (lam / q) (om / q) (lam' / q) (om' / q) 0).eval x)⁻¹ := by
    have hnum : 1 - om / q * (om' / q) * x ^ 2 = 1 - ξ := by
      rw [hξ, hxy]; field_simp
    have hξ1 : 1 - ξ ≠ 0 := by
      intro h
      have h' : ξ = 1 := by linear_combination -h
      rw [h', norm_one] at hnξ
      exact lt_irrefl _ hnξ
    rw [hnum]; field_simp
  rw [hval] at hP

  let g : ℕ × ℕ → ℤ × ℤ := fun mn => ((mn.1 : ℤ) + mn.2, (mn.2 : ℤ))
  have hg : Function.Injective g := by
    intro a b hab
    simp only [g, Prod.mk.injEq] at hab
    obtain ⟨h1, h2⟩ := hab
    have hb2 : a.2 = b.2 := by exact_mod_cast h2
    have hb1 : a.1 = b.1 := by
      have : (a.1 : ℤ) = b.1 := by rw [hb2] at h1; linarith
      exact_mod_cast this
    exact Prod.ext hb1 hb2
  have hoff : ∀ p ∉ Set.range g, term q s lam om lam' om' p = 0 := by
    intro p hp
    have hc : ¬ (0 ≤ p.1 - p.2 ∧ 0 ≤ p.2) := by
      rintro ⟨h1, h2⟩
      apply hp
      refine ⟨((p.1 - p.2).toNat, p.2.toNat), ?_⟩
      simp only [g, Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2]
      ext <;> simp
    simp only [term, coef, if_neg hc, mul_zero, zero_mul]
  rw [← hg.hasSum_iff hoff]
  convert hP using 1
  funext mn
  obtain ⟨m, n⟩ := mn
  simp only [Function.comp_apply, g, term, coef, hf, hgg]
  have hc : (0 : ℤ) ≤ (m : ℤ) + n - n ∧ (0 : ℤ) ≤ (n : ℤ) := ⟨by simp, by positivity⟩
  rw [if_pos hc]
  have e1 : ((m : ℤ) + n - n).toNat = m := by simp
  have e2 : ((n : ℤ)).toNat = n := Int.toNat_natCast n
  rw [e1, e2]
  have e3 : (q : ℂ) ^ ((m : ℤ) + n - n) = (q : ℂ) ^ m := by
    rw [add_sub_cancel_right, zpow_natCast]
  have e4 : -((m : ℤ) + n + n) = -((m + 2 * n : ℕ) : ℤ) := by push_cast; ring
  rw [e3, e4, weight_eq q hqpos s (m + 2 * n), ← hy, hxy, hξ]
  ring

theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 ℚ)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

theorem localAt_placeEmbed_of_ne (w v : HeightOneSpectrum (𝓞 ℚ)) (x : GL (Fin 2) (v.adicCompletion ℚ))
    (hw : w ≠ v) : localAt ℚ w (placeEmbed ℚ v x) = 1 := by
  show AdelicLevel.finComponent (𝓞 ℚ) ℚ w
    (AdelicLevel.glFin (𝓞 ℚ) ℚ (finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ v x))) = 1
  rw [glFin_finEmbed, finComponent_localEmbed_of_ne (𝓞 ℚ) ℚ v x hw]

end LanglandsTunnell.RankinSelberg.FinPeel

end

namespace LanglandsTunnell p2m_export "LanglandsTunnell" "RankinSelberg.mk_twoRowCauchySum_mul_coe_rsEulerPoly_eq_one RankinSelberg.mk_heckeRecursionSeq_mul_heckeRecursionSeq_mul_coe_rsEulerPoly_eq_and_hasSum RankinSelberg.exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow" namespace RankinSelberg p2m_export "LanglandsTunnell.RankinSelberg" "rsEulerPoly mk_twoRowCauchySum_mul_coe_rsEulerPoly_eq_one exists_isHaarMeasure_map_eq_prod_localAt hasSum_cell_terms_rsLocalIntegral mk_heckeRecursionSeq_mul_heckeRecursionSeq_mul_coe_rsEulerPoly_eq_and_hasSum exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow" namespace FinPeel end LanglandsTunnell.RankinSelberg.FinPeel
p2m_open_scoped "LanglandsTunnell LanglandsTunnell.RankinSelberg" in
open _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_RankinSelberg_exists_hasProd_rsFinIntegral_eq_rsFinIntegral_indicator_mul_of_torus_law.LanglandsTunnell _root_.LanglandsTunnell.RankinSelberg _root_.P2MW.S_LanglandsTunnell_RankinSelberg_exists_hasProd_rsFinIntegral_eq_rsFinIntegral_indicator_mul_of_torus_law.LanglandsTunnell.RankinSelberg LanglandsTunnell.RankinSelberg.OnePlaceSplit LanglandsTunnell.RankinSelberg.VSplitInhabitant HaarQuotient in

theorem LanglandsTunnell.RankinSelberg.FinPeel.onePlace
    (μ : Measure (finiteAdelicGL2Subgroup ℚ)) [μ.IsHaarMeasure]
    (μN : Measure (RSCarrier.finUnipotent)) [μN.IsHaarMeasure]
    [SecondCountableTopology (finiteAdelicGL2Subgroup ℚ)]
    (s : ℂ) (W F : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (lam om lam' om' : ℂ) (κ : ℝ)
    (hlam : ‖lam‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ) (hom : ‖om‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ)
    (hlam' : ‖lam'‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ) (hom' : ‖om'‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ)
    (hs : 2 * |κ| + 4 < s.re)
    (hinv : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
      W ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) *
          F ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
        W (g : AdelicGL2 (𝓞 ℚ) ℚ) * F (g : AdelicGL2 (𝓞 ℚ) ℚ))
    (hWK : ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W (g * placeEmbed ℚ v x) = W g)
    (hFK : ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → F (g * placeEmbed ℚ v x) = F g)
    (hT : ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (m n : ℤ), localAt ℚ v g = 1 →
      W (g * placeEmbed ℚ v
            (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m *
              scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n)) *
        F (g * placeEmbed ℚ v
            (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m *
              scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n)) =
        (if 0 ≤ m ∧ 0 ≤ n then
          (om * om') ^ n.toNat *
            heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) lam om m.toNat *
            heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) lam' om' m.toNat
         else 0) * (W g * F g))
    (hint : Integrable
      (fun g : finiteAdelicGL2Subgroup ℚ => (W g * F g) *
        ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^
          (s - 1 / 2))
      (μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN))) :
    RSCarrier.rsFinIntegral μ μN s (fun g => W g) (fun g => F g) =
      ((rsEulerPoly (lam / (Ideal.absNorm v.asIdeal : ℂ)) (om / (Ideal.absNorm v.asIdeal : ℂ))
            (lam' / (Ideal.absNorm v.asIdeal : ℂ)) (om' / (Ideal.absNorm v.asIdeal : ℂ)) 0).eval
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ ((3 / 2 : ℂ) - s)))⁻¹ *
        RSCarrier.rsFinIntegral μ μN s
          ({g : finiteAdelicGL2Subgroup ℚ |
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                  localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => W g))
          ({g : finiteAdelicGL2Subgroup ℚ |
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                  localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => F g)) := by

  letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion ℚ)) := borel (GL (Fin 2) (v.adicCompletion ℚ))
  haveI : BorelSpace (GL (Fin 2) (v.adicCompletion ℚ)) := ⟨rfl⟩
  haveI : SecondCountableTopology (GL (Fin 2) (v.adicCompletion ℚ)) := LocalCountability.secondCountableTopology_gl ℚ v
  haveI := locallyCompactSpace_local v
  haveI := locallyCompactSpace_localUnipotent v

  obtain ⟨μv, hμv⟩ : ∃ μv : Measure (GL (Fin 2) (v.adicCompletion ℚ)), μv.IsHaarMeasure :=
    ⟨Measure.haar, inferInstance⟩
  obtain ⟨μNv, hμNv⟩ :
      ∃ μNv : Measure (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range, μNv.IsHaarMeasure :=
    ⟨Measure.haar, inferInstance⟩
  haveI := isMulRightInvariant_localUnipotent v μNv

  obtain ⟨μ', hμ', hmap⟩ := haar_splits v μ μv
  obtain ⟨μ₄, hμ₄, hρ₂⟩ := exists_lintegral_prodDensity_eq_one v μN μNv

  obtain ⟨hint_loc, hcar⟩ := carrier_eq_local v μ μN μv μ' hmap μNv μ₄ hρ₂ s W F hinv hint
  have hfi := cell_sum v hπ hϖ μv μNv (localWeight v) (localWeight_unipotent_mul v) (localWeight_mul_levelOne v) s
    (kernelIntegral v (Measure.map Subtype.val μ') (density (unipotentAway v) μ₄) s W F) (fun _ => 1)
    (fun n hn x => by rw [kernelIntegral_unipotent_mul v μ' (density (unipotentAway v) μ₄) s W F hinv n hn x])
    (fun k hk x => by
      rw [kernelIntegral_mul_levelOne v (Measure.map Subtype.val μ') (density (unipotentAway v) μ₄) s W F hWK hFK k hk
        x])
    hint_loc

  have heval : ∀ k : finiteAdelicGL2Subgroup ℚ, localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1 → ∀ p : ℤ × ℤ,
      W ((k * sectionAt v (torusPt v hπ p) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) *
          F ((k * sectionAt v (torusPt v hπ p) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) =
        FinPeel.coef ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) lam om lam' om' p *
          (W (k : AdelicGL2 (𝓞 ℚ) ℚ) * F (k : AdelicGL2 (𝓞 ℚ) ℚ)) := by
    intro k hk p
    have hcoe : ((k * sectionAt v (torusPt v hπ p) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) =
        (k : AdelicGL2 (𝓞 ℚ) ℚ) * placeEmbed ℚ v (torusPt v hπ p) := by
      rw [Subgroup.coe_mul]
      rfl
    rw [hcoe]
    unfold torusPt
    rw [hT (k : AdelicGL2 (𝓞 ℚ) ℚ) (p.1 - p.2) p.2 hk]
    simp only [FinPeel.coef]
  have hE := fun p : ℤ × ℤ =>
    kernelIntegral_torusPt v μ' (density (unipotentAway v) μ₄) s W F hπ
      (FinPeel.coef ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) lam om lam' om') heval p
  have hlw := localWeight_torusPt v hπ hϖ
  simp only [torusPt] at hE hlw

  have hq2 : 2 ≤ Ideal.absNorm v.asIdeal := FinPeel.two_le_absNorm v
  have hser := FinPeel.hasSum_term (Ideal.absNorm v.asIdeal) hq2 s lam om lam' om' κ hlam hom hlam' hom' hs
  set Y : ℂ := cellMass v μv μNv *
    kernelIntegral v (Measure.map Subtype.val μ') (density (unipotentAway v) μ₄) s W F 1 with hYdef
  have hfi' : HasSum (fun p : ℤ × ℤ => FinPeel.term (Ideal.absNorm v.asIdeal) s lam om lam' om' p * Y)
      (RSCarrier.rsLocalIntegral μv (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range μNv
        (localWeight v) s (kernelIntegral v (Measure.map Subtype.val μ') (density (unipotentAway v) μ₄) s W F)
        (fun _ => 1)) := by
    convert hfi using 1
    funext p
    rw [hE p, hlw p]
    simp only [FinPeel.term, hYdef, cellMass, localCell]
    ring
  have hY := hfi'.unique (hser.mul_right Y)

  rw [hcar, hY, hYdef]
  congr 1
  exact (cell_carrier_eq v μ μN μv μ' hmap μNv μ₄ hρ₂ s W F hWK hFK hinv hint).symm

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RankinSelberg.mk_twoRowCauchySum_mul_coe_rsEulerPoly_eq_one RankinSelberg.mk_heckeRecursionSeq_mul_heckeRecursionSeq_mul_coe_rsEulerPoly_eq_and_hasSum RankinSelberg.exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow"
namespace RankinSelberg
p2m_export "LanglandsTunnell.RankinSelberg" "rsEulerPoly mk_twoRowCauchySum_mul_coe_rsEulerPoly_eq_one exists_isHaarMeasure_map_eq_prod_localAt hasSum_cell_terms_rsLocalIntegral mk_heckeRecursionSeq_mul_heckeRecursionSeq_mul_coe_rsEulerPoly_eq_and_hasSum exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow"
namespace FinPeel
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

open OnePlaceSplit

theorem countable_heightOneSpectrum (K : Type) [Field K] [NumberField K] :
    Countable (HeightOneSpectrum (𝓞 K)) := by
  have hI : Set.Countable (Set.univ : Set (Ideal (𝓞 K))) := by
    have : (Set.univ : Set (Ideal (𝓞 K))) = ⋃ n : ℕ, {I : Ideal (𝓞 K) | Ideal.absNorm I = n} := by
      ext I; simp
    rw [this]
    exact Set.countable_iUnion (fun n => (Ideal.finite_setOf_absNorm_eq n).countable)
  haveI : Countable (Ideal (𝓞 K)) := Set.countable_univ_iff.mp hI
  exact (Function.Injective.countable (f := fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal)
    (fun v w h => HeightOneSpectrum.ext h))

def cellA (v : HeightOneSpectrum (𝓞 ℚ)) : Set (AdelicGL2 (𝓞 ℚ) ℚ) :=
  {a | ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
    ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v a = n * k}

variable {ι : Type*} (pl : ι → HeightOneSpectrum (𝓞 ℚ))

def cellsA (T : Finset ι) : Set (AdelicGL2 (𝓞 ℚ) ℚ) := {a | ∀ i ∈ T, a ∈ cellA (pl i)}

def cells (T : Finset ι) : Set (finiteAdelicGL2Subgroup ℚ) := {g | ∀ i ∈ T, g ∈ preCell (pl i)}

theorem mem_cellsA_coe (T : Finset ι) (g : finiteAdelicGL2Subgroup ℚ) :
    (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ cellsA pl T ↔ g ∈ cells pl T := Iff.rfl

theorem cells_eq_biInter (T : Finset ι) : cells pl T = ⋂ i ∈ T, preCell (pl i) := by
  ext g; simp [cells]

theorem measurableSet_cells (T : Finset ι) : MeasurableSet (cells pl T) := by
  rw [cells_eq_biInter]
  exact Finset.measurableSet_biInter T (fun i _ => measurableSet_preCell (pl i))

theorem cells_mono {T T' : Finset ι} (h : T ⊆ T') : cells pl T' ⊆ cells pl T :=
  fun _ hg i hi => hg i (h hi)

theorem mul_placeEmbed_mem_cellsA_iff (T : Finset ι) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : ∀ i ∈ T, pl i ≠ v)
    (a : AdelicGL2 (𝓞 ℚ) ℚ) (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    a * placeEmbed ℚ v x ∈ cellsA pl T ↔ a ∈ cellsA pl T := by
  simp only [cellsA, cellA, Set.mem_setOf_eq]
  refine forall₂_congr (fun i hi => ?_)
  rw [map_mul, localAt_placeEmbed_of_ne (pl i) v x (hv i hi), mul_one]

theorem unipotent_mul_mem_cells_iff (T : Finset ι) (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ) :
    (n : finiteAdelicGL2Subgroup ℚ) * g ∈ cells pl T ↔ g ∈ cells pl T := by
  simp only [cells, Set.mem_setOf_eq]
  refine forall₂_congr (fun i _ => ?_)
  exact mem_preCell_unipotent_mul_iff (pl i) n g

theorem indicator_preCell_indicator_cellsA [DecidableEq ι] (T : Finset ι) (i₀ : ι) (W : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (g : finiteAdelicGL2Subgroup ℚ) :
    (preCell (pl i₀)).indicator (fun g : finiteAdelicGL2Subgroup ℚ => (cellsA pl T).indicator W g) g =
      (cellsA pl (insert i₀ T)).indicator W g := by
  classical
  simp only [Set.indicator_apply, mem_cellsA_coe, cells, Set.mem_setOf_eq, Finset.forall_mem_insert]
  by_cases h₀ : g ∈ preCell (pl i₀) <;> by_cases hT : ∀ i ∈ T, g ∈ preCell (pl i) <;> simp [h₀, hT]

end LanglandsTunnell.RankinSelberg.FinPeel

end

open _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_RankinSelberg_exists_hasProd_rsFinIntegral_eq_rsFinIntegral_indicator_mul_of_torus_law.LanglandsTunnell _root_.LanglandsTunnell.RankinSelberg _root_.P2MW.S_LanglandsTunnell_RankinSelberg_exists_hasProd_rsFinIntegral_eq_rsFinIntegral_indicator_mul_of_torus_law.LanglandsTunnell.RankinSelberg LanglandsTunnell.RankinSelberg.OnePlaceSplit LanglandsTunnell.RankinSelberg.VSplitInhabitant HaarQuotient in

theorem solution
    (μ : Measure (finiteAdelicGL2Subgroup ℚ)) [μ.IsHaarMeasure]
    (μN : Measure (RSCarrier.finUnipotent)) [μN.IsHaarMeasure]
    [SecondCountableTopology (finiteAdelicGL2Subgroup ℚ)]
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ)
    (hπ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v) ≠ 0)
    (hϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) = WithZero.exp (-1 : ℤ))
    (lam om lam' om' : HeightOneSpectrum (𝓞 ℚ) → ℂ) (κ : ℝ)
    (hbd : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      ‖lam v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖om v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
      ‖lam' v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖om' v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ)
    (W F : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hinv : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
      W ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) *
          F ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
        W (g : AdelicGL2 (𝓞 ℚ) ℚ) * F (g : AdelicGL2 (𝓞 ℚ) ℚ))
    (hN : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∃ ψ : AddChar (v.adicCompletion ℚ) ℂ,
      (∀ r : v.adicCompletionIntegers ℚ, ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) = 1) ∧
      (∃ r : v.adicCompletionIntegers ℚ,
        ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r /
          algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) ≠ 1) ∧
      ∀ (x : v.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), W (placeEmbed ℚ v (unipotent x) * g) = ψ x * W g)
    (hWK : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W (g * placeEmbed ℚ v x) = W g)
    (hFK : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → F (g * placeEmbed ℚ v x) = F g)
    (hT : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∀ hv : v ∉ S, ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (m n : ℤ), localAt ℚ v g = 1 →
      W (g * placeEmbed ℚ v
            (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) m *
              scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) ^ n)) *
        F (g * placeEmbed ℚ v
            (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) m *
              scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) ^ n)) =
        (if 0 ≤ m ∧ 0 ≤ n then
          (om v * om' v) ^ n.toNat *
            heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (lam v) (om v) m.toNat *
            heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (lam' v) (om' v) m.toNat
         else 0) * (W g * F g)) :
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
      Integrable
        (fun g : finiteAdelicGL2Subgroup ℚ => (W g * F g) *
          ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2))
        (μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN)) →
      ∃ Prod : ℂ,
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} =>
          ((rsEulerPoly (lam v.1 / (Ideal.absNorm v.1.asIdeal : ℂ)) (om v.1 / (Ideal.absNorm v.1.asIdeal : ℂ))
              (lam' v.1 / (Ideal.absNorm v.1.asIdeal : ℂ)) (om' v.1 / (Ideal.absNorm v.1.asIdeal : ℂ)) 0).eval
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((3 / 2 : ℂ) - s)))⁻¹) Prod ∧
        RSCarrier.rsFinIntegral μ μN s (fun g => W g) (fun g => F g) =
          RSCarrier.rsFinIntegral μ μN s
              ({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
                  ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                    ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                      localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => W g))
              ({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
                  ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                    ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                      localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => F g)) *
            Prod := by
  classical

  haveI : Countable (HeightOneSpectrum (𝓞 ℚ)) := FinPeel.countable_heightOneSpectrum ℚ
  set ν := μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN) with hν

  set f : ℂ → {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} → ℂ := fun s v =>
    ((rsEulerPoly (lam v.1 / (Ideal.absNorm v.1.asIdeal : ℂ)) (om v.1 / (Ideal.absNorm v.1.asIdeal : ℂ))
        (lam' v.1 / (Ideal.absNorm v.1.asIdeal : ℂ)) (om' v.1 / (Ideal.absNorm v.1.asIdeal : ℂ)) 0).eval
      (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((3 / 2 : ℂ) - s)))⁻¹ with hf
  have hbd' : ∀ v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S},
      ‖lam v.1 / (Ideal.absNorm v.1.asIdeal : ℂ)‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ ∧
      ‖om v.1 / (Ideal.absNorm v.1.asIdeal : ℂ)‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ ∧
      ‖lam' v.1 / (Ideal.absNorm v.1.asIdeal : ℂ)‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ ∧
      ‖om' v.1 / (Ideal.absNorm v.1.asIdeal : ℂ)‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ := by
    intro v
    have hq1 : (1 : ℝ) ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) := by
      exact_mod_cast (le_trans (by norm_num) (FinPeel.two_le_absNorm v.1))
    have hdiv : ∀ c : ℂ, ‖c‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ →
        ‖c / (Ideal.absNorm v.1.asIdeal : ℂ)‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ := fun c hc => by
      rw [norm_div, Complex.norm_natCast]
      exact (div_le_self (norm_nonneg _) hq1).trans hc
    obtain ⟨h1, h2, h3, h4⟩ := hbd v.1 v.2
    exact ⟨hdiv _ h1, hdiv _ h2, hdiv _ h3, hdiv _ h4⟩
  obtain ⟨σ₁, hmult, -, -⟩ :=
    LanglandsTunnell.RankinSelberg.exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow ℚ S
      (fun v => lam v.1 / (Ideal.absNorm v.1.asIdeal : ℂ)) (fun v => om v.1 / (Ideal.absNorm v.1.asIdeal : ℂ))
      (fun v => lam' v.1 / (Ideal.absNorm v.1.asIdeal : ℂ)) (fun v => om' v.1 / (Ideal.absNorm v.1.asIdeal : ℂ)) κ
      hbd'
  refine ⟨max (2 * |κ| + 4) (σ₁ + 3 / 2), fun s hs hint => ?_⟩
  have hsκ : 2 * |κ| + 4 < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hs₁ : σ₁ < (s - 3 / 2).re := by
    have := lt_of_le_of_lt (le_max_right _ _) hs
    simp only [Complex.sub_re, Complex.div_re, Complex.re_ofNat]
    norm_num
    linarith

  have hM : Multipliable (f s) := by
    refine (hmult (s - 3 / 2) hs₁).congr (fun v => ?_)
    simp only [hf, neg_sub]
  set Prod : ℂ := ∏' v, f s v with hProd
  have hP : HasProd (f s) Prod := hM.hasProd
  refine ⟨Prod, hP, ?_⟩

  have key : ∀ T : Finset {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S},
      RSCarrier.rsFinIntegral μ μN s (fun g => W g) (fun g => F g) =
        (∏ v ∈ T, f s v) *
          RSCarrier.rsFinIntegral μ μN s
            (fun g => (FinPeel.cellsA Subtype.val T).indicator W g)
            (fun g => (FinPeel.cellsA Subtype.val T).indicator F g) ∧
      Integrable
        (fun g : finiteAdelicGL2Subgroup ℚ =>
          ((FinPeel.cellsA Subtype.val T).indicator W g * (FinPeel.cellsA Subtype.val T).indicator F g) *
            ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^
              (s - 1 / 2)) ν := by
    intro T

    have hintT : ∀ T' : Finset {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S}, Integrable
        (fun g : finiteAdelicGL2Subgroup ℚ =>
          ((FinPeel.cellsA Subtype.val T').indicator W g * (FinPeel.cellsA Subtype.val T').indicator F g) *
            ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^
              (s - 1 / 2)) ν := by
      intro T'
      have heq : (fun g : finiteAdelicGL2Subgroup ℚ =>
          ((FinPeel.cellsA Subtype.val T').indicator W g * (FinPeel.cellsA Subtype.val T').indicator F g) *
            ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^
              (s - 1 / 2)) =
          (FinPeel.cells Subtype.val T').indicator (fun g : finiteAdelicGL2Subgroup ℚ => (W g * F g) *
            ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^
              (s - 1 / 2)) := by
        funext g
        simp only [Set.indicator_apply, FinPeel.mem_cellsA_coe]
        split_ifs <;> simp
      rw [heq]
      exact hint.indicator (FinPeel.measurableSet_cells Subtype.val T')
    refine ⟨?_, hintT T⟩
    induction T using Finset.induction_on with
    | empty =>
      have h0 : FinPeel.cellsA (Subtype.val : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} → HeightOneSpectrum (𝓞 ℚ))
          (∅ : Finset {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S}) = Set.univ := by
        ext a; simp [FinPeel.cellsA]
      simp only [Finset.prod_empty, one_mul, h0, Set.indicator_univ]
    | insert v T hvT ih =>

      set WT : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := (FinPeel.cellsA Subtype.val T).indicator W with hWT
      set FT : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := (FinPeel.cellsA Subtype.val T).indicator F with hFT
      have hne : ∀ i ∈ T, (Subtype.val i) ≠ v.1 := fun i hi h => hvT (by rwa [Subtype.ext h] at hi)
      have hmemE : ∀ (a : AdelicGL2 (𝓞 ℚ) ℚ) (x : GL (Fin 2) (v.1.adicCompletion ℚ)),
          a * placeEmbed ℚ v.1 x ∈ FinPeel.cellsA Subtype.val T ↔ a ∈ FinPeel.cellsA Subtype.val T :=
        fun a x => FinPeel.mul_placeEmbed_mem_cellsA_iff Subtype.val T hne a x
      have hinvT : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
          WT ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) *
              FT ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
            WT (g : AdelicGL2 (𝓞 ℚ) ℚ) * FT (g : AdelicGL2 (𝓞 ℚ) ℚ) := by
        intro n g
        have hm : ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) ∈
            FinPeel.cellsA Subtype.val T ↔ (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ FinPeel.cellsA Subtype.val T := by
          rw [FinPeel.mem_cellsA_coe, FinPeel.mem_cellsA_coe]
          exact FinPeel.unipotent_mul_mem_cells_iff Subtype.val T n g
        simp only [hWT, hFT, Set.indicator_apply, hm]
        split_ifs with h
        · exact hinv n g
        · simp
      have hWKT : ∀ (x : GL (Fin 2) (v.1.adicCompletion ℚ)) (a : AdelicGL2 (𝓞 ℚ) ℚ),
          x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v.1 ⊤ → WT (a * placeEmbed ℚ v.1 x) = WT a := by
        intro x a hx
        simp only [hWT, Set.indicator_apply, hmemE a x, hWK v.1 v.2 x a hx]
      have hFKT : ∀ (x : GL (Fin 2) (v.1.adicCompletion ℚ)) (a : AdelicGL2 (𝓞 ℚ) ℚ),
          x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v.1 ⊤ → FT (a * placeEmbed ℚ v.1 x) = FT a := by
        intro x a hx
        simp only [hFT, Set.indicator_apply, hmemE a x, hFK v.1 v.2 x a hx]
      have hTT : ∀ (a : AdelicGL2 (𝓞 ℚ) ℚ) (m n : ℤ), localAt ℚ v.1 a = 1 →
          WT (a * placeEmbed ℚ v.1
                (diagZ (algebraMap (v.1.adicCompletionIntegers ℚ) (v.1.adicCompletion ℚ) (ϖ v.1)) (hπ v.1 v.2) m *
                  scalarPi (algebraMap (v.1.adicCompletionIntegers ℚ) (v.1.adicCompletion ℚ) (ϖ v.1)) (hπ v.1 v.2) ^ n)) *
            FT (a * placeEmbed ℚ v.1
                (diagZ (algebraMap (v.1.adicCompletionIntegers ℚ) (v.1.adicCompletion ℚ) (ϖ v.1)) (hπ v.1 v.2) m *
                  scalarPi (algebraMap (v.1.adicCompletionIntegers ℚ) (v.1.adicCompletion ℚ) (ϖ v.1)) (hπ v.1 v.2) ^ n)) =
            (if 0 ≤ m ∧ 0 ≤ n then
              (om v.1 * om' v.1) ^ n.toNat *
                heckeRecursionSeq ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) (lam v.1) (om v.1) m.toNat *
                heckeRecursionSeq ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) (lam' v.1) (om' v.1) m.toNat
             else 0) * (WT a * FT a) := by
        intro a m n ha
        have hm := hmemE a
          (diagZ (algebraMap (v.1.adicCompletionIntegers ℚ) (v.1.adicCompletion ℚ) (ϖ v.1)) (hπ v.1 v.2) m *
            scalarPi (algebraMap (v.1.adicCompletionIntegers ℚ) (v.1.adicCompletion ℚ) (ϖ v.1)) (hπ v.1 v.2) ^ n)
        by_cases h : a ∈ FinPeel.cellsA Subtype.val T
        · have h' := hm.mpr h
          simp only [hWT, hFT, Set.indicator_apply, if_pos h, if_pos h']
          exact hT v.1 v.2 a m n ha
        · have h' := fun hh => h (hm.mp hh)
          simp only [hWT, hFT, Set.indicator_apply, if_neg h, if_neg h', mul_zero]
      obtain ⟨hl, ho, hl', ho'⟩ := hbd v.1 v.2
      have step := FinPeel.onePlace μ μN s WT FT v.1 (hπ v.1 v.2) (hϖ v.1 v.2) (lam v.1) (om v.1) (lam' v.1) (om' v.1)
        κ hl ho hl' ho' hsκ hinvT hWKT hFKT hTT (by simpa only [hWT, hFT] using hintT T)

      have hcutW : (preCell v.1).indicator (fun g : finiteAdelicGL2Subgroup ℚ => WT g) =
          fun g : finiteAdelicGL2Subgroup ℚ => (FinPeel.cellsA Subtype.val (insert v T)).indicator W g := by
        funext g; exact FinPeel.indicator_preCell_indicator_cellsA Subtype.val T v W g
      have hcutF : (preCell v.1).indicator (fun g : finiteAdelicGL2Subgroup ℚ => FT g) =
          fun g : finiteAdelicGL2Subgroup ℚ => (FinPeel.cellsA Subtype.val (insert v T)).indicator F g := by
        funext g; exact FinPeel.indicator_preCell_indicator_cellsA Subtype.val T v F g
      have hstep : RSCarrier.rsFinIntegral μ μN s (fun g => WT g) (fun g => FT g) =
          f s v * RSCarrier.rsFinIntegral μ μN s
            (fun g => (FinPeel.cellsA Subtype.val (insert v T)).indicator W g)
            (fun g => (FinPeel.cellsA Subtype.val (insert v T)).indicator F g) := by
        rw [← hcutW, ← hcutF, step]
        simp only [hf]
        rfl
      rw [Finset.prod_insert hvT, ih, hstep]
      ring

  set Φ : finiteAdelicGL2Subgroup ℚ → ℂ := fun g => (W g * F g) *
    ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2) with hΦ
  have hIT : ∀ T : Finset {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S},
      RSCarrier.rsFinIntegral μ μN s
          (fun g => (FinPeel.cellsA Subtype.val T).indicator W g)
          (fun g => (FinPeel.cellsA Subtype.val T).indicator F g) =
        ∫ g in FinPeel.cells Subtype.val T, Φ g ∂ν := by
    intro T
    unfold RSCarrier.rsFinIntegral RSCarrier.rsLocalIntegral
    rw [← integral_indicator (FinPeel.measurableSet_cells Subtype.val T)]
    congr 1
    funext g
    simp only [hΦ, Set.indicator_apply, FinPeel.mem_cellsA_coe]
    split_ifs <;> simp

  set C : Set (finiteAdelicGL2Subgroup ℚ) :=
    {g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
        ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
          localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k} with hC
  have hCeq : (⋂ T : Finset {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S}, FinPeel.cells Subtype.val T) = C := by
    ext g
    simp only [Set.mem_iInter, FinPeel.cells, Set.mem_setOf_eq, hC]
    constructor
    · intro h v hv
      exact h {⟨v, hv⟩} ⟨v, hv⟩ (Finset.mem_singleton_self _)
    · intro h T i _
      exact h i.1 i.2
  have hCmeas : MeasurableSet C := by
    rw [← hCeq]
    exact MeasurableSet.iInter (fun T => FinPeel.measurableSet_cells Subtype.val T)
  have hIC : RSCarrier.rsFinIntegral μ μN s (C.indicator (fun g => W g)) (C.indicator (fun g => F g)) =
      ∫ g in C, Φ g ∂ν := by
    unfold RSCarrier.rsFinIntegral RSCarrier.rsLocalIntegral
    rw [← integral_indicator hCmeas]
    congr 1
    funext g
    simp only [hΦ, Set.indicator_apply]
    split_ifs <;> simp

  have hlim : Filter.Tendsto (fun T : Finset {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} =>
      ∫ g in FinPeel.cells Subtype.val T, Φ g ∂ν) Filter.atTop (nhds (∫ g in C, Φ g ∂ν)) := by
    rw [← hCeq]
    exact tendsto_setIntegral_of_antitone (fun T => FinPeel.measurableSet_cells Subtype.val T)
      (fun T T' h => FinPeel.cells_mono Subtype.val h) ⟨∅, hint.integrableOn⟩
  have hprodlim : Filter.Tendsto (fun T : Finset {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} => ∏ v ∈ T, f s v)
      Filter.atTop (nhds Prod) := hP
  have hboth := hprodlim.mul hlim
  have hconst : Filter.Tendsto (fun T : Finset {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} =>
      (∏ v ∈ T, f s v) * ∫ g in FinPeel.cells Subtype.val T, Φ g ∂ν) Filter.atTop
      (nhds (RSCarrier.rsFinIntegral μ μN s (fun g => W g) (fun g => F g))) := by
    refine tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun T => ?_)
    rw [(key T).1, hIT T]
  have hI := tendsto_nhds_unique hconst hboth
  rw [hI, hIC, mul_comm]

#print axioms solution

end S_LanglandsTunnell_RankinSelberg_exists_hasProd_rsFinIntegral_eq_rsFinIntegral_indicator_mul_of_torus_law
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_hasProd_rsFinIntegral_eq_rsFinIntegral_indicator_mul_of_torus_law (solution)
