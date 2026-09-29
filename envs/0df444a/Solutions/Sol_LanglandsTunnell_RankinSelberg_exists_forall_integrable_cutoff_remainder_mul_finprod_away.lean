-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_forall_integrable_cutoff_remainder_mul_finprod_away
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/14b4e531-bd53-5310-96da-82e52e5a477f

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_unisolvence_refPoint_cutoff_of_linearIndependent_slots
import Theorems.Thm_LanglandsTunnell_RankinSelberg_measurable_remainder_and_dualFactor_translate_mul_prod_eq_of_pureTensor_expansion
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_translate_rsFinCellIntegrand_dual_split_of_dualFactor_phase
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_cutoff_remainder_mul_finprod_away
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory UnramifiedWhittaker AdelicDock
open LanglandsTunnell.TateLocal NumberField.StandardAddChar Topology
open scoped nonZeroDivisors NNReal ENNReal Matrix Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace KcRsCellIso

section MatrixFurniture

variable {A : Type*} [CommRing A]

theorem transposeInv3_mul (g h : GL (Fin 3) A) : transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h :=
  Units.ext (by
    show (((g * h)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ =
      ((g⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ * ((h⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ
    rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul])

theorem transposeInv3_one : transposeInv3 (1 : GL (Fin 3) A) = 1 :=
  Units.ext (by
    show (((1 : GL (Fin 3) A)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ = 1
    rw [inv_one, Units.val_one, Matrix.transpose_one])

theorem transposeInv3_transposeInv3 (g : GL (Fin 3) A) : transposeInv3 (transposeInv3 g) = g :=
  Units.ext (by
    show ((((transposeInv3 g)⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A)ᵀ = g
    show (((g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ)ᵀ = g
    rw [Matrix.transpose_transpose])

theorem transposeInv3_inv (g : GL (Fin 3) A) : transposeInv3 g⁻¹ = (transposeInv3 g)⁻¹ := by
  have h : transposeInv3 g⁻¹ * transposeInv3 g = 1 := by rw [← transposeInv3_mul, inv_mul_cancel, transposeInv3_one]
  exact eq_inv_of_mul_eq_one_left h

def transposeInv3Hom : GL (Fin 3) A →* GL (Fin 3) A where
  toFun := transposeInv3
  map_one' := transposeInv3_one
  map_mul' := transposeInv3_mul

@[scoped simp] theorem transposeInv3Hom_apply (g : GL (Fin 3) A) : transposeInv3Hom g = transposeInv3 g := rfl

theorem transposeInv3_map {B : Type*} [CommRing B] (f : A →+* B) (g : GL (Fin 3) A) :
    transposeInv3 (Matrix.GeneralLinearGroup.map f g) = Matrix.GeneralLinearGroup.map f (transposeInv3 g) := by
  refine Units.ext ?_
  show (((Matrix.GeneralLinearGroup.map f g)⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)ᵀ =
    f.mapMatrix (((g⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ)
  rw [← map_inv]
  show (f.mapMatrix ((g⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ = _
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.transpose_map]

theorem longWeyl3_mul_transposeInv3_iotaGL_unipotent {F : Type*} [Field F] (x : F) :
    (longWeyl3 : GL (Fin 3) F) * transposeInv3 (iotaGL (unipotent x)) = upperUnipotent3 0 (-x) 0 * longWeyl3 := by
  refine Units.ext ?_
  have hinv : ((iotaGL (unipotent x))⁻¹ : GL (Fin 3) F) = iotaGL (unipotent (-x)) := by
    rw [← map_inv]
    congr 1
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.coe_inv]
    refine Matrix.inv_eq_left_inv ?_
    simp [unipotent, Matrix.one_fin_two]
  show ((longWeyl3 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (((iotaGL (unipotent x))⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ =
    ((upperUnipotent3 0 (-x) 0 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * ((longWeyl3 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, unipotent, Matrix.mul_apply, Fin.sum_univ_three]

theorem weyl2_mul_transposeInvN_unipotent {F : Type*} [Field F] (w₀ : GL (Fin 2) F)
    (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0]) (x : F) :
    w₀ * transposeInvN (Fin 2) (unipotent x) = unipotent (-x) * w₀ := by
  refine Units.ext ?_
  have hinv : ((unipotent x)⁻¹ : GL (Fin 2) F) = unipotent (-x) := by
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.coe_inv]
    refine Matrix.inv_eq_left_inv ?_
    simp [unipotent, Matrix.one_fin_two]
  show (w₀ : Matrix (Fin 2) (Fin 2) F) * (((unipotent x)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ =
    (unipotent (-x) : Matrix (Fin 2) (Fin 2) F) * w₀
  rw [hinv, hw₀]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipotent, Matrix.mul_apply]

theorem weyl2_mul_transposeInvN_unipotentGL2 (w₀ : GL (Fin 2) A)
    (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) A) = !![0, 1; 1, 0]) (x : A) :
    w₀ * transposeInvN (Fin 2) (unipotentGL2 x) = unipotentGL2 (-x) * w₀ := by
  refine Units.ext ?_
  have hinv : ((unipotentGL2 x)⁻¹ : GL (Fin 2) A) = unipotentGL2 (-x) := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero]
  show (w₀ : Matrix (Fin 2) (Fin 2) A) * (((unipotentGL2 x)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)ᵀ =
    (unipotentGL2 (-x) : Matrix (Fin 2) (Fin 2) A) * w₀
  rw [hinv, hw₀]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

theorem unipotent_eq_unipotentGL2 {F : Type*} [Field F] (x : F) : unipotent x = unipotentGL2 x :=
  Units.ext rfl

theorem det_unipotentGL2 (x : A) : Matrix.GeneralLinearGroup.det (unipotentGL2 x) = 1 :=
  Units.ext (by simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two_of])

theorem transposeInvN_map {B : Type*} [CommRing B] (f : A →+* B) (g : GL (Fin 2) A) :
    transposeInvN (Fin 2) (Matrix.GeneralLinearGroup.map f g) = Matrix.GeneralLinearGroup.map f (transposeInvN (Fin 2) g) := by
  refine Units.ext ?_
  rw [coe_transposeInvN, ← map_inv]
  show ((f.mapMatrix ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)))ᵀ = f.mapMatrix (((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)ᵀ)
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.transpose_map]

end MatrixFurniture

section AdelicGL2

variable (p : HeightOneSpectrum (𝓞 ℚ))

def projAt : ↥(finiteAdelicGL2Subgroup ℚ) →* GL (Fin 2) (p.adicCompletion ℚ) :=
  (localAt ℚ p).comp (finiteAdelicGL2Subgroup ℚ).subtype

theorem projAt_apply (g : finiteAdelicGL2Subgroup ℚ) : projAt p g = localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) := rfl

theorem continuous_projAt : Continuous (projAt p) :=
  (continuous_localAt ℚ p).comp continuous_subtype_val

theorem placeEmbed_mem (x : GL (Fin 2) (p.adicCompletion ℚ)) : placeEmbed ℚ p x ∈ finiteAdelicGL2Subgroup ℚ :=
  (mem_finiteAdelicGL2Subgroup_iff ℚ _).2 (glArch_finEmbed (𝓞 ℚ) ℚ _)

def embAt : GL (Fin 2) (p.adicCompletion ℚ) →* ↥(finiteAdelicGL2Subgroup ℚ) :=
  (placeEmbed ℚ p).codRestrict _ (placeEmbed_mem p)

@[scoped simp] theorem coe_embAt (x : GL (Fin 2) (p.adicCompletion ℚ)) :
    (embAt p x : AdelicGL2 (𝓞 ℚ) ℚ) = placeEmbed ℚ p x := rfl

theorem localAt_apply (g : AdelicGL2 (𝓞 ℚ) ℚ) (i j : Fin 2) :
    (localAt ℚ p g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j =
      ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 p := rfl

theorem localAt_placeEmbed (x : GL (Fin 2) (p.adicCompletion ℚ)) : localAt ℚ p (placeEmbed ℚ p x) = x := by
  show finComponent (𝓞 ℚ) ℚ p (glFin (𝓞 ℚ) ℚ (finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ p x))) = x
  rw [glFin_finEmbed, finComponent_localEmbed_self]

theorem localAt_placeEmbed_of_ne {q : HeightOneSpectrum (𝓞 ℚ)} (hq : q ≠ p) (x : GL (Fin 2) (p.adicCompletion ℚ)) :
    localAt ℚ q (placeEmbed ℚ p x) = 1 := by
  show finComponent (𝓞 ℚ) ℚ q (glFin (𝓞 ℚ) ℚ (finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ p x))) = 1
  rw [glFin_finEmbed, finComponent_localEmbed_of_ne (𝓞 ℚ) ℚ p x hq]

theorem glArch_placeEmbed (x : GL (Fin 2) (p.adicCompletion ℚ)) : glArch (𝓞 ℚ) ℚ (placeEmbed ℚ p x) = 1 :=
  glArch_finEmbed (𝓞 ℚ) ℚ _

@[scoped simp] theorem projAt_embAt (x : GL (Fin 2) (p.adicCompletion ℚ)) : projAt p (embAt p x) = x :=
  localAt_placeEmbed p x

theorem ext_of_glArch_localAt {g h : AdelicGL2 (𝓞 ℚ) ℚ} (harch : glArch (𝓞 ℚ) ℚ g = glArch (𝓞 ℚ) ℚ h)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 ℚ), localAt ℚ v g = localAt ℚ v h) : g = h := by
  refine Units.ext (matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 ℚ) ℚ ?_ ?_)
  · exact congrArg Units.val harch
  · refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 ℚ) ℚ fun w => ?_
    exact congrArg Units.val (hfin w)

theorem continuous_placeEmbed' : Continuous (placeEmbed ℚ p) := by

  have hsplice : ∀ (a : FiniteAdeleRing (𝓞 ℚ) ℚ), Continuous (splice (𝓞 ℚ) ℚ p a) := by
    intro a
    classical
    let S : Set (HeightOneSpectrum (𝓞 ℚ)) := {w | w ≠ p ∧ a w ∈ w.adicCompletionIntegers ℚ}
    have hS : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 ℚ))) ≤ Filter.principal S := by
      rw [Filter.le_principal_iff, Filter.mem_cofinite]
      refine (((Filter.eventually_cofinite.1 a.2)).union (Set.finite_singleton p)).subset fun w hw => ?_
      by_contra h
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff, not_or, not_not] at h
      exact hw ⟨h.2, h.1⟩
    let f₀ : p.adicCompletion ℚ →
        RestrictedProduct (fun w : HeightOneSpectrum (𝓞 ℚ) => w.adicCompletion ℚ)
          (fun w => (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ))) (Filter.principal S) :=
      fun t => ⟨Function.update (⇑a) p t, Filter.eventually_principal.2 fun w hw => by
        rw [Function.update_of_ne hw.1]
        exact hw.2⟩
    have hf₀ : Continuous f₀ :=
      RestrictedProduct.continuous_rng_of_principal.2 (continuous_const.update p continuous_id)
    have heq : splice (𝓞 ℚ) ℚ p a = RestrictedProduct.inclusion _ _ hS ∘ f₀ := by
      funext t
      rfl
    rw [heq]
    exact (RestrictedProduct.continuous_inclusion hS).comp hf₀
  have hlm : Continuous (localMat (𝓞 ℚ) ℚ p) :=
    continuous_matrix fun i j => (hsplice _).comp (continuous_id.matrix_elem i j)
  have hle : Continuous (localEmbed (𝓞 ℚ) ℚ p) :=
    Units.continuous_iff.2 ⟨hlm.comp Units.continuous_val, hlm.comp Units.continuous_coe_inv⟩
  have hfm : Continuous (finMat (𝓞 ℚ) ℚ) :=
    continuous_matrix fun i j =>
      (continuous_const.prodMk (continuous_id.matrix_elem i j) :
        Continuous fun g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
          ((((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j, g i j) : AdeleRing (𝓞 ℚ) ℚ)))
  have hfe : Continuous (finEmbed (𝓞 ℚ) ℚ) :=
    Units.continuous_iff.2 ⟨hfm.comp Units.continuous_val, hfm.comp Units.continuous_coe_inv⟩
  exact hfe.comp hle

theorem continuous_embAt : Continuous (embAt p) :=
  (continuous_placeEmbed' p).subtype_mk _

theorem conj_placeEmbed (Y : AdelicGL2 (𝓞 ℚ) ℚ) (u : GL (Fin 2) (p.adicCompletion ℚ)) :
    Y⁻¹ * placeEmbed ℚ p u * Y = placeEmbed ℚ p ((localAt ℚ p Y)⁻¹ * u * localAt ℚ p Y) := by
  refine ext_of_glArch_localAt ?_ fun v => ?_
  · rw [map_mul, map_mul, glArch_placeEmbed, glArch_placeEmbed, mul_one, map_inv, inv_mul_cancel]
  · by_cases hv : v = p
    · subst hv
      rw [map_mul, map_mul, localAt_placeEmbed, localAt_placeEmbed, map_inv]
    · rw [map_mul, map_mul, localAt_placeEmbed_of_ne p hv, localAt_placeEmbed_of_ne p hv, mul_one, map_inv,
        inv_mul_cancel]

theorem placeEmbed_mul_comm {g : AdelicGL2 (𝓞 ℚ) ℚ} (hg : localAt ℚ p g = 1)
    (x : GL (Fin 2) (p.adicCompletion ℚ)) : placeEmbed ℚ p x * g = g * placeEmbed ℚ p x := by
  have h := conj_placeEmbed p g x
  rw [hg, inv_one, one_mul, mul_one] at h
  calc placeEmbed ℚ p x * g = g * (g⁻¹ * placeEmbed ℚ p x * g) := by group
    _ = g * placeEmbed ℚ p x := by rw [h]

theorem commute_placeEmbed_of_ne {q : HeightOneSpectrum (𝓞 ℚ)} (hpq : p ≠ q)
    (x : GL (Fin 2) (p.adicCompletion ℚ)) (y : GL (Fin 2) (q.adicCompletion ℚ)) :
    Commute (placeEmbed ℚ p x) (placeEmbed ℚ q y) :=
  placeEmbed_mul_comm p (localAt_placeEmbed_of_ne q hpq y) x

theorem localAt_unipotentGL2 (t : AdeleRing (𝓞 ℚ) ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    localAt ℚ v (unipotentGL2 t) = unipotentGL2 (t.2 v) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [localAt_apply]
  fin_cases i <;> fin_cases j <;> rfl

theorem glArch_unipotentGL2 (t : AdeleRing (𝓞 ℚ) ℚ) : glArch (𝓞 ℚ) ℚ (unipotentGL2 t) = unipotentGL2 t.1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glArch_apply]
  fin_cases i <;> fin_cases j <;> rfl

end AdelicGL2

section MultiPlace

variable (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))

abbrev LocProd : Type := ∀ p : ↥SQ, GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)

theorem commute_embAt {p q : ↥SQ} (hpq : p ≠ q) (x : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ))
    (y : GL (Fin 2) ((q : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) :
    Commute (embAt (p : HeightOneSpectrum (𝓞 ℚ)) x) (embAt (q : HeightOneSpectrum (𝓞 ℚ)) y) := by
  have h : (p : HeightOneSpectrum (𝓞 ℚ)) ≠ q := fun h => hpq (Subtype.ext h)
  have hc := commute_placeEmbed_of_ne (p : HeightOneSpectrum (𝓞 ℚ)) h x y
  exact Subtype.ext hc.eq

def embS : LocProd SQ →* ↥(finiteAdelicGL2Subgroup ℚ) :=
  MonoidHom.noncommPiCoprod (fun p : ↥SQ => embAt (p : HeightOneSpectrum (𝓞 ℚ)))
    (fun _ _ hpq x y => commute_embAt SQ hpq x y)

def projS : ↥(finiteAdelicGL2Subgroup ℚ) →* LocProd SQ :=
  MonoidHom.pi fun p : ↥SQ => projAt (p : HeightOneSpectrum (𝓞 ℚ))

@[scoped simp] theorem projS_apply (g : finiteAdelicGL2Subgroup ℚ) (p : ↥SQ) :
    projS SQ g p = localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ) := rfl

theorem continuous_projS : Continuous (projS SQ) :=
  continuous_pi fun p => continuous_projAt _

theorem embS_apply (y : LocProd SQ) :
    embS SQ y = Finset.univ.noncommProd (fun p : ↥SQ => embAt (p : HeightOneSpectrum (𝓞 ℚ)) (y p))
      (fun _ _ _ _ hpq => commute_embAt SQ hpq _ _) := rfl

open scoped Classical in
theorem embS_mulSingle (p : ↥SQ) (x : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) :
    embS SQ (Pi.mulSingle p x) = embAt (p : HeightOneSpectrum (𝓞 ℚ)) x :=
  MonoidHom.noncommPiCoprod_mulSingle
    (N := fun q : ↥SQ => GL (Fin 2) ((q : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ))
    (fun q : ↥SQ => embAt (q : HeightOneSpectrum (𝓞 ℚ))) p x

open scoped Classical in
theorem projS_embS (y : LocProd SQ) : projS SQ (embS SQ y) = y := by
  have h : (projS SQ).comp (embS SQ) = MonoidHom.id _ := by
    refine MonoidHom.pi_ext fun p x => ?_
    rw [MonoidHom.comp_apply, embS_mulSingle, MonoidHom.id_apply]
    funext q
    rw [projS_apply, coe_embAt]
    by_cases hq : q = p
    · subst hq
      rw [localAt_placeEmbed, Pi.mulSingle_eq_same]
    · have hq' : (q : HeightOneSpectrum (𝓞 ℚ)) ≠ p := fun h => hq (Subtype.ext h)
      rw [localAt_placeEmbed_of_ne _ hq', Pi.mulSingle_eq_of_ne hq]
  exact DFunLike.congr_fun h y

theorem localAt_embS_of_mem (y : LocProd SQ) (p : ↥SQ) :
    localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (embS SQ y : AdelicGL2 (𝓞 ℚ) ℚ) = y p := by
  have h := congrFun (projS_embS SQ y) p
  rwa [projS_apply] at h

theorem embS_induction (y : LocProd SQ) (P : ↥(finiteAdelicGL2Subgroup ℚ) → Prop)
    (hmul : ∀ a b, P a → P b → P (a * b)) (hone : P 1)
    (hbase : ∀ p : ↥SQ, P (embAt (p : HeightOneSpectrum (𝓞 ℚ)) (y p))) : P (embS SQ y) := by
  rw [embS_apply]
  exact Finset.noncommProd_induction _ _ _ P hmul hone fun p _ => hbase p

theorem localAt_embS_of_not_mem (y : LocProd SQ) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∉ SQ) :
    localAt ℚ v (embS SQ y : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := by
  refine embS_induction SQ y (fun z => localAt ℚ v (z : AdelicGL2 (𝓞 ℚ) ℚ) = 1) ?_ (map_one _) ?_
  · intro a b ha hb
    show localAt ℚ v ((a : AdelicGL2 (𝓞 ℚ) ℚ) * b) = 1
    rw [map_mul, ha, hb, one_mul]
  · intro p
    have hne : v ≠ (p : HeightOneSpectrum (𝓞 ℚ)) := fun h => hv (h ▸ p.2)
    exact localAt_placeEmbed_of_ne _ hne _

theorem glArch_embS (y : LocProd SQ) : glArch (𝓞 ℚ) ℚ (embS SQ y : AdelicGL2 (𝓞 ℚ) ℚ) = 1 :=
  (mem_finiteAdelicGL2Subgroup_iff ℚ _).1 (embS SQ y).2

theorem embS_mul_comm (y : LocProd SQ) {g : finiteAdelicGL2Subgroup ℚ} (hg : projS SQ g = 1) :
    embS SQ y * g = g * embS SQ y := by
  have hc : Commute g (embS SQ y) := by
    rw [embS_apply]
    refine Finset.noncommProd_commute _ _ _ g fun p _ => ?_
    have hp : localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := by
      have := congrFun hg p
      rwa [projS_apply] at this
    have h := placeEmbed_mul_comm (p : HeightOneSpectrum (𝓞 ℚ)) hp (y p)
    show g * embAt (p : HeightOneSpectrum (𝓞 ℚ)) (y p) = embAt (p : HeightOneSpectrum (𝓞 ℚ)) (y p) * g
    exact Subtype.ext h.symm
  exact hc.eq.symm

def awayPart (g : finiteAdelicGL2Subgroup ℚ) : finiteAdelicGL2Subgroup ℚ := g * (embS SQ (projS SQ g))⁻¹

theorem projS_awayPart (g : finiteAdelicGL2Subgroup ℚ) : projS SQ (awayPart SQ g) = 1 := by
  rw [awayPart, map_mul, map_inv, projS_embS, mul_inv_cancel]

theorem localAt_awayPart_of_mem (g : finiteAdelicGL2Subgroup ℚ) (p : ↥SQ) :
    localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (awayPart SQ g : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := by
  have := congrFun (projS_awayPart SQ g) p
  rwa [projS_apply] at this

theorem localAt_awayPart_of_not_mem (g : finiteAdelicGL2Subgroup ℚ) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∉ SQ) :
    localAt ℚ v (awayPart SQ g : AdelicGL2 (𝓞 ℚ) ℚ) = localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) := by
  show localAt ℚ v ((g : AdelicGL2 (𝓞 ℚ) ℚ) * ((embS SQ (projS SQ g))⁻¹ : finiteAdelicGL2Subgroup ℚ)) = _
  rw [map_mul, Subgroup.coe_inv, map_inv, localAt_embS_of_not_mem SQ _ hv, inv_one, mul_one]

theorem continuous_embS : Continuous (embS SQ) := by
  classical
  have key : ∀ (s : Finset ↥SQ), Continuous fun y : LocProd SQ =>
      s.noncommProd (fun p : ↥SQ => embAt (p : HeightOneSpectrum (𝓞 ℚ)) (y p))
        (fun _ _ _ _ hpq => commute_embAt SQ hpq _ _) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp only [Finset.noncommProd_empty]; exact continuous_const
    | insert a s ha ih =>
      have heq : (fun y : LocProd SQ => (insert a s).noncommProd (fun p : ↥SQ => embAt (p : HeightOneSpectrum (𝓞 ℚ)) (y p))
            (fun _ _ _ _ hpq => commute_embAt SQ hpq _ _)) =
          fun y => embAt (a : HeightOneSpectrum (𝓞 ℚ)) (y a) *
            s.noncommProd (fun p : ↥SQ => embAt (p : HeightOneSpectrum (𝓞 ℚ)) (y p))
              (fun _ _ _ _ hpq => commute_embAt SQ hpq _ _) := by
        funext y
        rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha]
      rw [heq]
      exact ((continuous_embAt _).comp (continuous_apply a)).mul ih
  exact key Finset.univ

theorem continuous_awayPart : Continuous (awayPart SQ) :=
  continuous_id.mul ((continuous_embS SQ).comp (continuous_projS SQ)).inv

theorem awayPart_mul (n g : finiteAdelicGL2Subgroup ℚ) :
    awayPart SQ (n * g) = (n * (embS SQ (projS SQ n))⁻¹) * awayPart SQ g := by
  have hcomm : (embS SQ (projS SQ n))⁻¹ * awayPart SQ g = awayPart SQ g * (embS SQ (projS SQ n))⁻¹ := by
    have h := embS_mul_comm SQ (projS SQ n) (projS_awayPart SQ g)
    have hc : Commute (embS SQ (projS SQ n)) (awayPart SQ g) := h
    exact hc.inv_left.eq
  rw [mul_assoc, hcomm]
  show n * g * (embS SQ (projS SQ (n * g)))⁻¹ = n * (g * (embS SQ (projS SQ g))⁻¹ * (embS SQ (projS SQ n))⁻¹)
  rw [map_mul, map_mul, mul_inv_rev]
  group

theorem awayPart_mul_embS (g : finiteAdelicGL2Subgroup ℚ) (y : LocProd SQ) :
    awayPart SQ (g * embS SQ y) = awayPart SQ g := by
  show g * embS SQ y * (embS SQ (projS SQ (g * embS SQ y)))⁻¹ = g * (embS SQ (projS SQ g))⁻¹
  rw [map_mul, projS_embS, map_mul, mul_inv_rev]
  group

end MultiPlace

section FinFactor

theorem ratArchGL2_mul (g h : AdelicGL2 (𝓞 ℚ) ℚ) : ratArchGL2 (g * h) = ratArchGL2 g * ratArchGL2 h := by
  simp only [ratArchGL2, map_mul]

theorem ratArchGL2_of_mem {g : AdelicGL2 (𝓞 ℚ) ℚ} (hg : g ∈ finiteAdelicGL2Subgroup ℚ) : ratArchGL2 g = 1 := by
  simp only [ratArchGL2, (mem_finiteAdelicGL2Subgroup_iff ℚ g).1 hg, map_one]

theorem finFactor_coe (g : finiteAdelicGL2Subgroup ℚ) : RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) = g := by
  refine Subtype.ext ?_
  show (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 (g : AdelicGL2 (𝓞 ℚ) ℚ)))⁻¹ *
      (g : AdelicGL2 (𝓞 ℚ) ℚ) = g
  rw [ratArchGL2_of_mem g.2, map_one, inv_one, one_mul]

theorem finFactor_mul_coe (Y : AdelicGL2 (𝓞 ℚ) ℚ) (X : finiteAdelicGL2Subgroup ℚ) :
    RSCarrier.finFactor (Y * (X : AdelicGL2 (𝓞 ℚ) ℚ)) = RSCarrier.finFactor Y * X := by
  refine Subtype.ext ?_
  show (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 (Y * (X : AdelicGL2 (𝓞 ℚ) ℚ))))⁻¹ *
      (Y * (X : AdelicGL2 (𝓞 ℚ) ℚ)) =
    (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 Y))⁻¹ * Y * (X : AdelicGL2 (𝓞 ℚ) ℚ)
  rw [ratArchGL2_mul, ratArchGL2_of_mem X.2, mul_one, mul_assoc]

theorem transposeInvN_mem (g : finiteAdelicGL2Subgroup ℚ) :
    transposeInvN (Fin 2) (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ finiteAdelicGL2Subgroup ℚ := by
  rw [mem_finiteAdelicGL2Subgroup_iff]
  show Matrix.GeneralLinearGroup.map (adeleArch (𝓞 ℚ) ℚ) (transposeInvN (Fin 2) (g : AdelicGL2 (𝓞 ℚ) ℚ)) = 1
  rw [← transposeInvN_map]
  have hg : Matrix.GeneralLinearGroup.map (adeleArch (𝓞 ℚ) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := (mem_finiteAdelicGL2Subgroup_iff ℚ _).1 g.2
  rw [hg]
  refine Units.ext ?_
  rw [coe_transposeInvN, inv_one, Units.val_one, Matrix.transpose_one]

theorem continuous_transposeInvN_adelic :
    Continuous fun g : AdelicGL2 (𝓞 ℚ) ℚ => transposeInvN (Fin 2) g := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_coe_inv.matrix_transpose :
      Continuous fun g : AdelicGL2 (𝓞 ℚ) ℚ => (((g⁻¹ : AdelicGL2 (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))ᵀ)
  · exact (Units.continuous_val.matrix_transpose :
      Continuous fun g : AdelicGL2 (𝓞 ℚ) ℚ => ((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))ᵀ)

theorem eq_unipotentGL2_of_mem_adelicUnipotent {n : AdelicGL2 (𝓞 ℚ) ℚ} (hn : n ∈ adelicUnipotent ℚ) :
    ∃ t : AdeleRing (𝓞 ℚ) ℚ, n = unipotentGL2 t := by
  obtain ⟨a, rfl⟩ := hn
  exact ⟨a.toAdd, rfl⟩

theorem fst_eq_zero_of_unipotentGL2_mem {t : AdeleRing (𝓞 ℚ) ℚ} (ht : unipotentGL2 t ∈ finiteAdelicGL2Subgroup ℚ) :
    t.1 = 0 := by
  have h := (mem_finiteAdelicGL2Subgroup_iff ℚ _).1 ht
  rw [glArch_unipotentGL2] at h
  have h01 := congrArg (fun u : GL (Fin 2) (InfiniteAdeleRing ℚ) => (u : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) 0 1) h
  simpa using h01

theorem apply_eq_zero_of_localAt_unipotentGL2_eq_one {t : AdeleRing (𝓞 ℚ) ℚ} {v : HeightOneSpectrum (𝓞 ℚ)}
    (h : localAt ℚ v (unipotentGL2 t) = 1) : t.2 v = 0 := by
  rw [localAt_unipotentGL2] at h
  have h01 := congrArg (fun u : GL (Fin 2) (v.adicCompletion ℚ) => (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1) h
  simpa using h01

end FinFactor

section GL3

theorem componentAt3_iota (v : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ g) = iotaGL (localAt ℚ v g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show ((finAdeleEval (𝓞 ℚ) ℚ v).comp (adeleFin (𝓞 ℚ) ℚ)) (embedMat2 (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j) =
    embedMat2 (localAt ℚ v g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, localAt_apply] <;> rfl

end GL3

section EulerFamily

variable {K : Type} [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
variable {pins : CarrierPins ℚ} {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
  (F : CubicInductionForm K pins ψ μ) (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))

open scoped Classical in

def eFam (Y : AdelicGL2 (𝓞 ℚ) ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) : ℂ :=
  if v ∈ SQ then 1 else dualWhittakerFn3 (F.whittakerLoc v) (iotaGL (localAt ℚ v Y))

def Efun (Y : AdelicGL2 (𝓞 ℚ) ℚ) : ℂ := ∏ᶠ v, eFam F SQ Y v

variable {F SQ}

theorem eFam_of_mem (Y : AdelicGL2 (𝓞 ℚ) ℚ) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∈ SQ) : eFam F SQ Y v = 1 := by
  simp [eFam, hv]

theorem eFam_of_not_mem (Y : AdelicGL2 (𝓞 ℚ) ℚ) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∉ SQ) :
    eFam F SQ Y v = dualWhittakerFn3 (F.whittakerLoc v) (iotaGL (localAt ℚ v Y)) := by
  simp [eFam, hv]

theorem eFam_mul_placeEmbed (Y : AdelicGL2 (𝓞 ℚ) ℚ) {p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ∈ SQ)
    (x : GL (Fin 2) (p.adicCompletion ℚ)) (Z : AdelicGL2 (𝓞 ℚ) ℚ) :
    eFam F SQ (Y * placeEmbed ℚ p x * Z) = eFam F SQ (Y * Z) := by
  funext v
  by_cases hv : v ∈ SQ
  · rw [eFam_of_mem _ hv, eFam_of_mem _ hv]
  · have hne : v ≠ p := fun h => hv (h ▸ hp)
    rw [eFam_of_not_mem _ hv, eFam_of_not_mem _ hv]
    simp only [map_mul, localAt_placeEmbed_of_ne p hne, mul_one]

theorem Efun_mul_placeEmbed (Y : AdelicGL2 (𝓞 ℚ) ℚ) {p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ∈ SQ)
    (x : GL (Fin 2) (p.adicCompletion ℚ)) (Z : AdelicGL2 (𝓞 ℚ) ℚ) :
    Efun F SQ (Y * placeEmbed ℚ p x * Z) = Efun F SQ (Y * Z) := by
  simp only [Efun, eFam_mul_placeEmbed Y hp x Z]

theorem eFam_mul_embS (Y : AdelicGL2 (𝓞 ℚ) ℚ) (y : LocProd SQ) (Z : AdelicGL2 (𝓞 ℚ) ℚ) :
    eFam F SQ (Y * (embS SQ y : AdelicGL2 (𝓞 ℚ) ℚ) * Z) = eFam F SQ (Y * Z) := by
  funext v
  by_cases hv : v ∈ SQ
  · rw [eFam_of_mem _ hv, eFam_of_mem _ hv]
  · rw [eFam_of_not_mem _ hv, eFam_of_not_mem _ hv]
    have h1 : localAt ℚ v (Y * (embS SQ y : AdelicGL2 (𝓞 ℚ) ℚ) * Z) = localAt ℚ v (Y * Z) := by
      rw [map_mul, map_mul, map_mul, localAt_embS_of_not_mem SQ y hv, mul_one]
    rw [h1]

theorem Efun_mul_embS (Y : AdelicGL2 (𝓞 ℚ) ℚ) (y : LocProd SQ) (Z : AdelicGL2 (𝓞 ℚ) ℚ) :
    Efun F SQ (Y * (embS SQ y : AdelicGL2 (𝓞 ℚ) ℚ) * Z) = Efun F SQ (Y * Z) := by
  simp only [Efun, eFam_mul_embS Y y Z]

end EulerFamily

section BigCell

variable (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))

def IsBigCell (X : AdelicGL2 (𝓞 ℚ) ℚ) : Prop :=
  ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
    ∃ n ∈ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range, ∃ k ∈ localLevelOne (𝓞 ℚ) ℚ p ⊤, localAt ℚ p X = n * k

def bigCell : Set (finiteAdelicGL2Subgroup ℚ) :=
  {g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      ∃ n ∈ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
        ∃ k ∈ localLevelOne (𝓞 ℚ) ℚ p ⊤, localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}

theorem mem_bigCell_iff (g : finiteAdelicGL2Subgroup ℚ) : g ∈ bigCell SQ ↔ IsBigCell SQ (g : AdelicGL2 (𝓞 ℚ) ℚ) := Iff.rfl

open scoped Classical in

def cellWt (X : AdelicGL2 (𝓞 ℚ) ℚ) : ℂ := if IsBigCell SQ X then 1 else 0

theorem isBigCell_mul_of_localAt_eq_one {X Z : AdelicGL2 (𝓞 ℚ) ℚ} (hZ : ∀ v, v ∉ SQ → localAt ℚ v Z = 1) :
    IsBigCell SQ (X * Z) ↔ IsBigCell SQ X := by
  simp only [IsBigCell, map_mul]
  constructor
  · intro h p hp; have := h p hp; rwa [hZ p hp, mul_one] at this
  · intro h p hp; rw [hZ p hp, mul_one]; exact h p hp

theorem cellWt_mul_of_localAt_eq_one {X Z : AdelicGL2 (𝓞 ℚ) ℚ} (hZ : ∀ v, v ∉ SQ → localAt ℚ v Z = 1) :
    cellWt SQ (X * Z) = cellWt SQ X := by
  unfold cellWt; rw [isBigCell_mul_of_localAt_eq_one SQ hZ]

theorem cellWt_mul_placeEmbed (X : AdelicGL2 (𝓞 ℚ) ℚ) {p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ∈ SQ)
    (x : GL (Fin 2) (p.adicCompletion ℚ)) : cellWt SQ (X * placeEmbed ℚ p x) = cellWt SQ X :=
  cellWt_mul_of_localAt_eq_one SQ fun v hv => localAt_placeEmbed_of_ne p (fun h : v = p => hv (h ▸ hp)) x

theorem cellWt_mul_embS (X : AdelicGL2 (𝓞 ℚ) ℚ) (y : LocProd SQ) :
    cellWt SQ (X * (embS SQ y : AdelicGL2 (𝓞 ℚ) ℚ)) = cellWt SQ X :=
  cellWt_mul_of_localAt_eq_one SQ fun _ hv => localAt_embS_of_not_mem SQ y hv

theorem isBigCell_unipotent_mul {n : AdelicGL2 (𝓞 ℚ) ℚ} (hn : n ∈ adelicUnipotent ℚ) (X : AdelicGL2 (𝓞 ℚ) ℚ) :
    IsBigCell SQ (n * X) ↔ IsBigCell SQ X := by
  obtain ⟨t, rfl⟩ := eq_unipotentGL2_of_mem_adelicUnipotent hn
  have key : ∀ (s : AdeleRing (𝓞 ℚ) ℚ) (Y : AdelicGL2 (𝓞 ℚ) ℚ), IsBigCell SQ Y → IsBigCell SQ (unipotentGL2 s * Y) := by
    intro s Y hY p hp
    obtain ⟨n', hn', k, hk, hYp⟩ := hY p hp
    refine ⟨unipotentGL2 (s.2 p) * n', ?_, k, hk, ?_⟩
    · exact Subgroup.mul_mem _ ⟨Multiplicative.ofAdd (s.2 p), rfl⟩ hn'
    · rw [map_mul, localAt_unipotentGL2, hYp, mul_assoc]
  refine ⟨fun h => ?_, key t X⟩
  have := key (-t) _ h
  rwa [← mul_assoc, ← unipotentGL2_add, neg_add_cancel, unipotentGL2_zero, one_mul] at this

theorem cellWt_unipotent_mul {n : AdelicGL2 (𝓞 ℚ) ℚ} (hn : n ∈ adelicUnipotent ℚ) (X : AdelicGL2 (𝓞 ℚ) ℚ) :
    cellWt SQ (n * X) = cellWt SQ X := by
  unfold cellWt; rw [isBigCell_unipotent_mul SQ hn]

theorem norm_cellWt_le_one (X : AdelicGL2 (𝓞 ℚ) ℚ) : ‖cellWt SQ X‖ ≤ 1 := by
  unfold cellWt; split_ifs <;> simp

theorem indicator_bigCell_eq (f : finiteAdelicGL2Subgroup ℚ → ℂ) (g : finiteAdelicGL2Subgroup ℚ) :
    (bigCell SQ).indicator f g = cellWt SQ (g : AdelicGL2 (𝓞 ℚ) ℚ) * f g := by
  classical
  unfold cellWt
  by_cases h : g ∈ bigCell SQ
  · rw [Set.indicator_of_mem h, if_pos ((mem_bigCell_iff SQ g).1 h), one_mul]
  · rw [Set.indicator_of_notMem h, if_neg (fun h' => h ((mem_bigCell_iff SQ g).2 h')), zero_mul]

scoped instance : Countable (HeightOneSpectrum (𝓞 ℚ)) := Countable.of_equiv _ Rat.HeightOneSpectrum.primesEquiv.symm

theorem measurableSet_bigCell : MeasurableSet (bigCell SQ) := by
  letI : ∀ p : HeightOneSpectrum (𝓞 ℚ), MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := fun p => localGLBorel ℚ p
  haveI : ∀ p : HeightOneSpectrum (𝓞 ℚ), BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := fun p => borelSpace_localGLBorel ℚ p
  have hopen : ∀ p : HeightOneSpectrum (𝓞 ℚ), IsOpen ((((unipotentGL2Hom (R := p.adicCompletion ℚ)).range : Set (GL (Fin 2) (p.adicCompletion ℚ))) *
      (localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ))))) := fun p =>
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p ⊤ (by simp)).2.mul_left
  have heq : bigCell SQ = ⋂ p : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ SQ},
      (projAt p.1) ⁻¹' ((((unipotentGL2Hom (R := p.1.adicCompletion ℚ)).range : Set _) * (localLevelOne (𝓞 ℚ) ℚ p.1 ⊤ : Set _))) := by
    ext g
    simp only [bigCell, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Subtype.forall, projAt_apply]
    refine forall_congr' fun p => forall_congr' fun hp => ?_
    rw [Set.mem_mul]
    constructor
    · rintro ⟨n, hn, k, hk, h⟩; exact ⟨n, hn, k, hk, h.symm⟩
    · rintro ⟨n, hn, k, hk, h⟩; exact ⟨n, hn, k, hk, h.symm⟩
  rw [heq]
  exact MeasurableSet.iInter fun p => ((hopen p.1).measurableSet).preimage (continuous_projAt p.1).measurable

theorem measurable_cellWt_coe : Measurable fun g : finiteAdelicGL2Subgroup ℚ => cellWt SQ (g : AdelicGL2 (𝓞 ℚ) ℚ) := by
  have : (fun g : finiteAdelicGL2Subgroup ℚ => cellWt SQ (g : AdelicGL2 (𝓞 ℚ) ℚ)) = (bigCell SQ).indicator fun _ => (1 : ℂ) := by
    funext g; rw [indicator_bigCell_eq, mul_one]
  rw [this]
  exact measurable_const.indicator (measurableSet_bigCell SQ)

end BigCell

theorem sum_inv_mul_sum_eq {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (hM : M.det ≠ 0) (x : Fin m → ℂ) (α : Fin m) :
    ∑ i : Fin m, M⁻¹ α i * ∑ β : Fin m, M i β * x β = x α := by
  classical
  have hinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.2 hM)
  have key : ∀ β : Fin m, ∑ i : Fin m, M⁻¹ α i * M i β = if α = β then 1 else 0 := by
    intro β
    have := congrFun (congrFun hinv α) β
    rwa [Matrix.mul_apply, Matrix.one_apply] at this
  calc ∑ i : Fin m, M⁻¹ α i * ∑ β : Fin m, M i β * x β
        = ∑ β : Fin m, (∑ i : Fin m, M⁻¹ α i * M i β) * x β := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun i _ => by ring
    _ = x α := by
          simp only [key]
          rw [Finset.sum_eq_single α]
          · simp
          · intro β _ hβ; simp [Ne.symm hβ]
          · intro h; exact absurd (Finset.mem_univ α) h

def cutSet {p : HeightOneSpectrum (𝓞 ℚ)} (U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ)) :=
  ((unipotentGL2Hom (R := p.adicCompletion ℚ)).range : Set (GL (Fin 2) (p.adicCompletion ℚ))) * (U : Set (GL (Fin 2) (p.adicCompletion ℚ)))

theorem isOpen_cutSet {p : HeightOneSpectrum (𝓞 ℚ)} {U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))}
    (hU : IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ)))) : IsOpen (cutSet U) := hU.mul_left

theorem one_mem_cutSet {p : HeightOneSpectrum (𝓞 ℚ)} (U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : (1 : GL (Fin 2) (p.adicCompletion ℚ)) ∈ cutSet U :=
  Set.mem_mul.2 ⟨1, Subgroup.one_mem _, 1, U.one_mem, mul_one 1⟩

theorem mem_cutSet_iff {p : HeightOneSpectrum (𝓞 ℚ)} (U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) (y : GL (Fin 2) (p.adicCompletion ℚ)) :
    y ∈ cutSet U ↔ ∃ n ∈ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range, ∃ u ∈ U, n * u = y := Set.mem_mul

theorem unipotent_mul_mem_cutSet_iff {p : HeightOneSpectrum (𝓞 ℚ)} (U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)))
    (x : p.adicCompletion ℚ) (y : GL (Fin 2) (p.adicCompletion ℚ)) : unipotent x * y ∈ cutSet U ↔ y ∈ cutSet U := by
  have key : ∀ (x' : p.adicCompletion ℚ) (y' : GL (Fin 2) (p.adicCompletion ℚ)), y' ∈ cutSet U → unipotent x' * y' ∈ cutSet U := by
    intro x' y' hy
    obtain ⟨n, hn, u, hu, rfl⟩ := (mem_cutSet_iff U y').1 hy
    refine (mem_cutSet_iff U _).2 ⟨unipotent x' * n, Subgroup.mul_mem _ ⟨Multiplicative.ofAdd x', ?_⟩ hn, u, hu, by rw [mul_assoc]⟩
    rw [unipotent_eq_unipotentGL2]; rfl
  refine ⟨fun h => ?_, key x y⟩
  have := key (-x) _ h
  rwa [← mul_assoc, unipotent_eq_unipotentGL2, unipotent_eq_unipotentGL2, ← unipotentGL2_add, neg_add_cancel,
    unipotentGL2_zero, one_mul] at this

section IsolationIntegrable

def cw (s' : ℂ) (g : finiteAdelicGL2Subgroup ℚ) : ℂ :=
  ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s' - 1 / 2)

theorem continuous_det_adelic : Continuous fun g : AdelicGL2 (𝓞 ℚ) ℚ => Matrix.GeneralLinearGroup.det g :=
  Units.continuous_iff.2 ⟨(Units.continuous_val.matrix_det :
      Continuous fun g : AdelicGL2 (𝓞 ℚ) ℚ => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)).det),
    (Units.continuous_coe_inv.matrix_det :
      Continuous fun g : AdelicGL2 (𝓞 ℚ) ℚ => ((g⁻¹ : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)).det)⟩

theorem continuous_ideleNorm_det_coe :
    Continuous fun g : finiteAdelicGL2Subgroup ℚ => ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) :=
  ((NumberField.TateGlobal.continuous_ideleNorm ℚ).comp continuous_det_adelic).comp continuous_subtype_val

theorem measurable_cw (s' : ℂ) : Measurable (cw s') :=
  (Complex.continuous_ofReal.comp continuous_ideleNorm_det_coe).measurable.pow_const _

theorem cw_mul (s' : ℂ) (g h : finiteAdelicGL2Subgroup ℚ) : cw s' (g * h) = cw s' g * cw s' h := by
  simp only [cw, Subgroup.coe_mul, map_mul, ideleNorm_mul]
  push_cast
  exact Complex.mul_cpow_ofReal_nonneg (ideleNorm_pos _).le (ideleNorm_pos _).le _

theorem cw_ne_zero (s' : ℂ) (g : finiteAdelicGL2Subgroup ℚ) : cw s' g ≠ 0 := by
  rw [cw, Complex.cpow_def_of_ne_zero]
  · exact Complex.exp_ne_zero _
  · exact_mod_cast (ideleNorm_pos _).ne'

theorem cw_unipotent_mul (s' : ℂ) {n : finiteAdelicGL2Subgroup ℚ} (hn : (n : AdelicGL2 (𝓞 ℚ) ℚ) ∈ adelicUnipotent ℚ)
    (g : finiteAdelicGL2Subgroup ℚ) : cw s' (n * g) = cw s' g := by
  obtain ⟨t, ht⟩ := eq_unipotentGL2_of_mem_adelicUnipotent hn
  simp only [cw, Subgroup.coe_mul, map_mul, ht, det_unipotentGL2, one_mul]

open scoped Classical in

def rloc {p : HeightOneSpectrum (𝓞 ℚ)} (U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) (y : GL (Fin 2) (p.adicCompletion ℚ)) : ℂ :=
  (if y ∈ cutSet U then (1 : ℂ) else 0) *
    ((modulus ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)

theorem rloc_unipotent_mul {p : HeightOneSpectrum (𝓞 ℚ)} (U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)))
    (x : p.adicCompletion ℚ) (y : GL (Fin 2) (p.adicCompletion ℚ)) : rloc U (unipotent x * y) = rloc U y := by
  classical
  have h1 := unipotent_mul_mem_cutSet_iff U x y
  have h2 : Matrix.GeneralLinearGroup.det (unipotent x * y) = Matrix.GeneralLinearGroup.det y := by
    rw [map_mul, unipotent_eq_unipotentGL2, det_unipotentGL2, one_mul]
  simp only [rloc, h1, h2]

theorem cellWt_mul_self (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (X : AdelicGL2 (𝓞 ℚ) ℚ) : cellWt SQ X * cellWt SQ X = cellWt SQ X := by
  unfold cellWt; split_ifs <;> simp

section IsoStep

variable {K : Type} [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
  {pins : CarrierPins ℚ} {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
  (F : CubicInductionForm K pins ψ μ) {SQ : Finset (HeightOneSpectrum (𝓞 ℚ))} {m : ℕ}
  (w : ∀ p : ↥SQ, Fin m → GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) → ℂ) (w₀ : GL (Fin 2) ℚ)
  (yy : Fin m → LocProd SQ) (k₀ : ∀ p : ↥SQ, LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)))
  (hμf : finiteAdelicGL2Subgroup ℚ) (Wd : finiteAdelicGL2Subgroup ℚ → ℂ) (R : Fin m → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
  (U : ∀ p : ↥SQ, Subgroup (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)))

def slotMat (y : LocProd SQ) (β : Fin m) : ℂ :=
  ∏ p : ↥SQ, w p β (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (globalPoints (𝓞 ℚ) ℚ w₀) * transposeInvN (Fin 2) (y p))

def kkAt (i : Fin m) (p : ↥SQ) : LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)) := (transposeInv3 (iotaGL (yy i p)))⁻¹ * k₀ p

def modY (i : Fin m) : ℂ :=
  ∏ p : ↥SQ, ((modulus ((Matrix.GeneralLinearGroup.det (yy i p) : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) :
    (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ)

theorem modY_ne_zero (i : Fin m) : modY yy i ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun p _ => ?_
  exact_mod_cast (modulus_pos (Units.ne_zero _)).ne'

def refGL3 (i : Fin m) (X : AdelicGL2 (𝓞 ℚ) ℚ) : ℂ :=
  ∏ p : ↥SQ, F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ))
    (longWeyl3 * transposeInv3 (iotaGL (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) X)) * kkAt yy k₀ i p)

def Jfun (i : Fin m) (s' : ℂ) (g : finiteAdelicGL2Subgroup ℚ) : ℂ :=
  cellWt SQ (g : AdelicGL2 (𝓞 ℚ) ℚ) * Wd (g * hμf) * refGL3 F yy k₀ i (g : AdelicGL2 (𝓞 ℚ) ℚ) *
    Efun F SQ ((g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf) * cw s' g

def Iso (α : Fin m) (s' : ℂ) (g : finiteAdelicGL2Subgroup ℚ) : ℂ :=
  cellWt SQ (g : AdelicGL2 (𝓞 ℚ) ℚ) * (∏ p : ↥SQ, rloc (U p) (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ))) *
    R α (g : AdelicGL2 (𝓞 ℚ) ℚ) * Efun F SQ ((g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf) * cw s' g

theorem integrable_Iso [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    (μf : Measure (finiteAdelicGL2Subgroup ℚ)) [μf.IsHaarMeasure]
    (μNFin : Measure RSCarrier.finUnipotent) [μNFin.IsHaarMeasure]
    (hUo : ∀ p : ↥SQ, IsOpen (U p : Set (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ))))
    (hc₀ : ∀ p : ↥SQ, F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * k₀ p) ≠ 0)
    (hM : (Matrix.of fun i j : Fin m => slotMat w w₀ (yy i) j).det ≠ 0)
    (hISO : ∀ (g : finiteAdelicGL2Subgroup ℚ),
      (∀ p : ↥SQ, ∃ n ∈ (unipotentGL2Hom (R := (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)).range, ∃ u ∈ U p,
        n * u = localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)) → ∀ i : Fin m,
      Wd ((g * embS SQ (yy i)) * hμf) *
          (∏ p : ↥SQ, F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ))
            (longWeyl3 * transposeInv3 (iotaGL (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) ((g * embS SQ (yy i) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ))) *
              kkAt yy k₀ i p)) =
        (∏ p : ↥SQ, F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * k₀ p) *
            ((modulus ((Matrix.GeneralLinearGroup.det (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)) :
                ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det (yy i p) : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) :
                (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ)) *
          ∑ β : Fin m, slotMat w w₀ (yy i) β * R β (g : AdelicGL2 (𝓞 ℚ) ℚ))
    (s' : ℂ)
    (hJT : ∀ i : Fin m, Integrable (fun g => Jfun F yy k₀ hμf Wd (SQ := SQ) i s' (g * embS SQ (yy i)))
      (μf.withDensity (HaarQuotient.density RSCarrier.finUnipotent μNFin)))
    (α : Fin m) :
    Integrable (Iso F hμf R U (SQ := SQ) α s') (μf.withDensity (HaarQuotient.density RSCarrier.finUnipotent μNFin)) := by
  classical
  letI : ∀ p : HeightOneSpectrum (𝓞 ℚ), MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := fun p => localGLBorel ℚ p
  haveI : ∀ p : HeightOneSpectrum (𝓞 ℚ), BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := fun p => borelSpace_localGLBorel ℚ p
  set ν := μf.withDensity (HaarQuotient.density RSCarrier.finUnipotent μNFin) with hν

  let Reg : Set (finiteAdelicGL2Subgroup ℚ) := {g | ∀ p : ↥SQ, localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ cutSet (U p)}
  have hReg : MeasurableSet Reg := by
    have : Reg = ⋂ p : ↥SQ, (projAt (p : HeightOneSpectrum (𝓞 ℚ))) ⁻¹' cutSet (U p) := by
      ext g; simp [Reg, projAt_apply]
    rw [this]
    exact MeasurableSet.iInter fun p => ((isOpen_cutSet (hUo p)).preimage (continuous_projAt _)).measurableSet

  let M : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun i j : Fin m => slotMat w w₀ (yy i) j
  let C₀ : ℂ := ∏ p : ↥SQ, F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * k₀ p)
  have hC₀ : C₀ ≠ 0 := Finset.prod_ne_zero_iff.2 fun p _ => hc₀ p
  let A : Fin m → ℂ := fun i => M⁻¹ α i * (C₀ * modY yy i * cw s' (embS SQ (yy i)))⁻¹

  have hpt : ∀ g : finiteAdelicGL2Subgroup ℚ, Iso F hμf R U (SQ := SQ) α s' g =
      ∑ i : Fin m, A i * Reg.indicator (fun g => Jfun F yy k₀ hμf Wd (SQ := SQ) i s' (g * embS SQ (yy i))) g := by
    intro g
    by_cases hg : g ∈ Reg
    · simp only [Set.indicator_of_mem hg]
      have hg' : ∀ p : ↥SQ, ∃ n ∈ (unipotentGL2Hom (R := (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)).range, ∃ u ∈ U p,
          n * u = localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ) := fun p => (mem_cutSet_iff (U p) _).1 (hg p)

      let mg : ℂ := ∏ p : ↥SQ, ((modulus ((Matrix.GeneralLinearGroup.det (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)) :
          ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ)
      have hrl : (∏ p : ↥SQ, rloc (U p) (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ))) = mg := by
        refine Finset.prod_congr rfl fun p _ => ?_
        rw [rloc, if_pos (hg p), one_mul]
      have hJi : ∀ i : Fin m, Jfun F yy k₀ hμf Wd (SQ := SQ) i s' (g * embS SQ (yy i)) =
          cellWt SQ (g : AdelicGL2 (𝓞 ℚ) ℚ) * (C₀ * mg * modY yy i * ∑ β : Fin m, M i β * R β (g : AdelicGL2 (𝓞 ℚ) ℚ)) *
            Efun F SQ ((g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf) * cw s' g * cw s' (embS SQ (yy i)) := by
        intro i
        have hiso := hISO g hg' i
        have hprod : (∏ p : ↥SQ, F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * k₀ p) *
            ((modulus ((Matrix.GeneralLinearGroup.det (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)) :
                ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det (yy i p) : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) :
                (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ)) = C₀ * mg * modY yy i := by
          simp only [C₀, mg, modY, ← Finset.prod_mul_distrib]
        rw [hprod] at hiso
        simp only [Jfun]
        rw [Subgroup.coe_mul, cellWt_mul_embS, Efun_mul_embS, cw_mul]
        have : Wd (g * embS SQ (yy i) * hμf) * refGL3 F yy k₀ i ((g : AdelicGL2 (𝓞 ℚ) ℚ) * (embS SQ (yy i) : AdelicGL2 (𝓞 ℚ) ℚ)) =
            C₀ * mg * modY yy i * ∑ β : Fin m, M i β * R β (g : AdelicGL2 (𝓞 ℚ) ℚ) := by
          have e : (∑ β : Fin m, M i β * R β (g : AdelicGL2 (𝓞 ℚ) ℚ)) = ∑ β : Fin m, slotMat w w₀ (yy i) β * R β (g : AdelicGL2 (𝓞 ℚ) ℚ) := by
            simp only [M, Matrix.of_apply]
          rw [e, ← hiso]; rfl
        linear_combination cellWt SQ (g : AdelicGL2 (𝓞 ℚ) ℚ) * Efun F SQ ((g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf) * cw s' g *
          cw s' (embS SQ (yy i)) * this
      simp only [hJi]
      have hsum : ∑ i : Fin m, A i * (cellWt SQ (g : AdelicGL2 (𝓞 ℚ) ℚ) * (C₀ * mg * modY yy i * ∑ β : Fin m, M i β * R β (g : AdelicGL2 (𝓞 ℚ) ℚ)) *
            Efun F SQ ((g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf) * cw s' g * cw s' (embS SQ (yy i))) =
          cellWt SQ (g : AdelicGL2 (𝓞 ℚ) ℚ) * mg * Efun F SQ ((g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf) * cw s' g *
            ∑ i : Fin m, M⁻¹ α i * ∑ β : Fin m, M i β * R β (g : AdelicGL2 (𝓞 ℚ) ℚ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        have h1 : modY yy i ≠ 0 := modY_ne_zero yy i
        have h2 : cw s' (embS SQ (yy i)) ≠ 0 := cw_ne_zero s' _
        simp only [A]
        field_simp
      rw [hsum, sum_inv_mul_sum_eq M hM (fun β => R β (g : AdelicGL2 (𝓞 ℚ) ℚ)) α, Iso, hrl]
      ring
    · simp only [Set.indicator_of_notMem hg, mul_zero, Finset.sum_const_zero]
      have : ∃ p : ↥SQ, localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ) ∉ cutSet (U p) := by
        by_contra h; push Not at h; exact hg h
      obtain ⟨p, hp⟩ := this
      have h0 : (∏ q : ↥SQ, rloc (U q) (localAt ℚ (q : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ))) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ p) (by rw [rloc, if_neg hp, zero_mul])
      simp only [Iso, h0, mul_zero, zero_mul]
  have heq : Iso F hμf R U (SQ := SQ) α s' = fun g =>
      ∑ i : Fin m, A i * Reg.indicator (fun g => Jfun F yy k₀ hμf Wd (SQ := SQ) i s' (g * embS SQ (yy i))) g :=
    funext hpt
  rw [heq]
  refine integrable_finsetSum _ fun i _ => Integrable.const_mul ?_ _
  exact (hJT i).indicator hReg

end IsoStep

end IsolationIntegrable

end KcRsCellIso
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_cutoff_remainder_mul_finprod_away.KcRsCellIso"

open KcRsCellIso in
open LanglandsTunnell.TateLocal UnramifiedWhittaker in
open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSQ : (∀ p : HeightOneSpectrum (𝓞 ℚ), Φ.level ≤ p.asIdeal → p ∈ SQ) ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ SQ →
        Ideal.ramificationIdx' (𝔓.under (𝓞 ℚ)).asIdeal 𝔓.asIdeal = 1)
    (hb : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ‖Φ.b p‖ = 1)
    (ha : ∀ σ : ℝ, 1 < σ →
      Summable fun p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) =>
        ‖Φ.a p‖ * (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ))
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hSK : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∈ SK ↔ 𝔓.under (𝓞 ℚ) ∈ SQ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hS : S ⊆ SQ)
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral) (hRc : Continuous R.toFun)
    (Cfin : FiniteAdeleRing (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hRS : R.exceptionalSet ⊆ S)
    (φv : (InfinitePlace ℚ → ZMod 2) → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : ∀ par, IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) R.centralChar Φ.level S Φ (φv par))
    (hφne : ∀ par, φv par ≠ 0)
    (hφKf : ∀ par, ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ (φv par) α = φv par)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)

    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)

    (F : CubicInductionForm K (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ μ)
    (hF0 : F.form ≠ 0 ∧ ∀ v, ¬ IsRamifiedIn K v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        F.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (F.whittakerLoc v))
    (hFc : Continuous F.form) (hFw : Continuous F.whittaker) (hFdw : Continuous F.dualWhittaker)
    (hFg : IsGaugeMajorised3 ℚ F.whittaker) (hFdg : IsGaugeMajorised3 ℚ F.dualWhittaker)
    (hBad :
        ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
          (∀ v ∈ T, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
            ∀ k ∈ Uv, ∀ g : LocalGL3 v, F.whittakerLoc v (g * k) = F.whittakerLoc v g) ∧
          (∀ v ∈ T, IsBadPlace K μ v → ∀ W ∈ gl3CyclicSubspace (F.whittakerLoc v), W ≠ 0 →
            F.whittakerLoc v ∈ gl3CyclicSubspace W))

    (S' : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSS' : SQ ⊆ S')
    (hgood : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S' → ¬ IsBadPlace K μ p)
    (ϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p.adicCompletionIntegers ℚ)
    (hπ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p) ≠ 0)
    (hϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) = WithZero.exp (-1 : ℤ))
    (hμf : finiteAdelicGL2Subgroup ℚ)
    (hhμf : (hμf : AdelicGL2 (𝓞 ℚ) ℚ) =
      ((S' \ SQ).toList.map (fun p => if hp : p ∉ SQ then
          UnramifiedWhittaker.placeEmbed ℚ p
            ((UnramifiedWhittaker.scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p))
              (hπ p hp)) ^ (-(inducedLevelAt K μ p : ℤ)))
        else 1)).prod)

    (WA : (InfinitePlace ℚ → ZMod 2) → GL (Fin 2) ℝ → ℂ)
    (Wf : (InfinitePlace ℚ → ZMod 2) → finiteAdelicGL2Subgroup ℚ → ℂ)
    (hWAf : ∀ par (g : AdelicGL2 (𝓞 ℚ) ℚ),
      whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ (φv par) 1 g = WA par (ratArchGL2 g) * Wf par (RSCarrier.finFactor g))
    (hWfC : ∀ par (g : finiteAdelicGL2Subgroup ℚ), Wf par g = Cfin 1 (g : AdelicGL2 (𝓞 ℚ) ℚ))

    (hWf1 : ∀ par, Wf par 1 ≠ 0)

    (w₀ : GL (Fin 2) ℚ) (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) ℚ) = !![0, 1; 1, 0])
    (Wfd : (InfinitePlace ℚ → ZMod 2) → finiteAdelicGL2Subgroup ℚ → ℂ)
    (hWfd : ∀ par (gf : finiteAdelicGL2Subgroup ℚ), Wfd par gf =
      ((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (gf : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) *
        Wf par (RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ w₀ * transposeInvN (Fin 2) (gf : AdelicGL2 (𝓞 ℚ) ℚ))))

    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    (μf : MeasureTheory.Measure (finiteAdelicGL2Subgroup ℚ)) [μf.IsHaarMeasure]
    (μNFin : MeasureTheory.Measure RSCarrier.finUnipotent) [μNFin.IsHaarMeasure]
    (par : InfinitePlace ℚ → ZMod 2)

    (m : ℕ) (w : ∀ p : ↥SQ, Fin m → GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) → ℂ) (Wrem : Fin m → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (_hwlaw : ∀ (p : ↥SQ) (α : Fin m) (x : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) (g : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)),
      w p α (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x * w p α g)
    (_hwsm : ∀ (p : ↥SQ) (α : Fin m), ∃ U : Subgroup (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ), w p α (g * k) = w p α g)
    (_hWinv : ∀ (α : Fin m) (p : ↥SQ) (x : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      Wrem α (g * UnramifiedWhittaker.placeEmbed ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x) = Wrem α g)
    (_hWlaw : ∀ (α : Fin m) (t : AdeleRing (𝓞 ℚ) ℚ), t.1 = 0 →
      (∀ p : ↥SQ, localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (unipotentGL2 t) = 1) →
      ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, Wrem α (unipotentGL2 t * g) = NumberField.StandardAddChar.psiQ t * Wrem α g)
    (_hwmeas : ∀ (p : ↥SQ) (α : Fin m), Measurable (fun g : finiteAdelicGL2Subgroup ℚ =>
      w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ))))
    (_hWmeas : ∀ α : Fin m, Measurable (fun g : finiteAdelicGL2Subgroup ℚ => Wrem α (g : AdelicGL2 (𝓞 ℚ) ℚ)))
    (_hsplit : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      Wf par (RSCarrier.finFactor g) = ∑ α : Fin m, (∏ p : ↥SQ, w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) g)) * Wrem α g)
    (_hind : LinearIndependent ℂ (fun α : Fin m => fun y : (∀ p : ↥SQ, GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) => ∏ p : ↥SQ, w p α (y p)))

    (Wb : ∀ p : ↥SQ, LocalGL3 p.1 → ℂ)
    (_hWbmem : ∀ p : ↥SQ, Wb p ∈ gl3CyclicSubspace (F.whittakerLoc p.1))
    (_hWbone : ∀ p : ↥SQ, Wb p (iotaGL 1) = 1)

    (R : Fin m → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (_hRinv : ∀ (α : Fin m) (p : ↥SQ) (x : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      R α (g * UnramifiedWhittaker.placeEmbed ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x) = R α g)
    (_hRexp : ∀ g : finiteAdelicGL2Subgroup ℚ, Wfd par (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf) =
      ∑ α : Fin m, (∏ p : ↥SQ,
        ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)) :
            ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ) *
          w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (globalPoints (𝓞 ℚ) ℚ w₀) *
            transposeInvN (Fin 2) (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)))) * R α (g : AdelicGL2 (𝓞 ℚ) ℚ))
    :
    (∀ α : Fin m, Measurable fun g : finiteAdelicGL2Subgroup ℚ => R α (g : AdelicGL2 (𝓞 ℚ) ℚ)) ∧
    (∀ (α : Fin m) (n : ↥RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
      ‖R α (((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)‖ =
        ‖R α (g : AdelicGL2 (𝓞 ℚ) ℚ)‖) ∧
    ∃ O : ∀ p : ↥SQ, Set (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)),
      (∀ p : ↥SQ, IsOpen (O p) ∧ (1 : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) ∈ O p ∧
        ∀ (x : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) (y : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)),
          UnramifiedWhittaker.unipotent x * y ∈ O p ↔ y ∈ O p) ∧
      ∃ σ : ℝ, ∀ (α : Fin m) (s' : ℂ), σ < s'.re →
        Integrable (fun g : finiteAdelicGL2Subgroup ℚ =>
          {g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                  localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g =>
            (∏ p : ↥SQ, (O p).indicator (fun y =>
              ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det y : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ))
                (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ))) * R α (g : AdelicGL2 (𝓞 ℚ) ℚ)) g *
          {g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                  localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => (∏ᶠ v, if v ∈ SQ then (1 : ℂ) else dualWhittakerFn3 (F.whittakerLoc v)
                (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ ((g * hμf : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ))))) g *
          ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s' - 1 / 2))
        (μf.withDensity (HaarQuotient.density RSCarrier.finUnipotent μNFin)) := by
  classical

  obtain ⟨yy, k₀, U, hUo, hc₀, hM, hU1, hU2⟩ :=
    LanglandsTunnell.RankinSelberg.exists_unisolvence_refPoint_cutoff_of_linearIndependent_slots K _ ψ μ F hBad SQ m w _hwsm w₀
      _hind Wb _hWbmem _hWbone

  obtain ⟨hWmeas, hWph, hRmeas, hRun, hISO⟩ :=
    LanglandsTunnell.RankinSelberg.measurable_remainder_and_dualFactor_translate_mul_prod_eq_of_pureTensor_expansion K _ ψ hψQ μ F
      SQ hμf m w _hwlaw Wrem _hWinv _hWlaw _hwmeas _hWmeas (Wf par) (Wfd par) w₀ hw₀ (fun gf => hWfd par gf) _hsplit R _hRinv _hRexp
      yy k₀ U hU1 hU2 hc₀ hM
  refine ⟨hRmeas, hRun, fun p => cutSet (U p), fun p => ⟨isOpen_cutSet (hUo p), one_mem_cutSet (U p),
    fun x y => unipotent_mul_mem_cutSet_iff (U p) x y⟩, ?_⟩

  have hrow : ∀ i : Fin m, ∃ σ : ℝ, ∀ s' : ℂ, σ < s'.re →
      Integrable (fun g => Jfun F yy k₀ hμf (Wfd par) (SQ := SQ) i s' (g * embS SQ (yy i)))
        (μf.withDensity (HaarQuotient.density RSCarrier.finUnipotent μNFin)) := by
    intro i
    obtain ⟨σ, hσ⟩ := LanglandsTunnell.RankinSelberg.exists_forall_integrable_translate_rsFinCellIntegrand_dual_split_of_dualFactor_phase
      K _hdeg Φ SQ hSQ hb ha SK hSK S hS _ hRc Cfin hRS φv hiso hφne hφKf μ hμ ψ hψ hlev hψQ F hF0 hFc hFw hFdw hFg hFdg hBad S' hSS' hgood
      ϖ hπ hϖ hμf hhμf WA Wf hWAf hWfC hWf1 w₀ hw₀ Wfd hWfd μf μNFin par hWmeas hWph (kkAt yy k₀ i)
    refine ⟨σ, fun s' hs' => ?_⟩
    have hInt := hσ s' hs' (embS SQ (yy i)) (fun v hv => localAt_embS_of_not_mem SQ _ hv)
    refine hInt.congr (Filter.Eventually.of_forall fun g => ?_)
    show (bigCell SQ).indicator _ (g * embS SQ (yy i)) * (bigCell SQ).indicator _ (g * embS SQ (yy i)) * _ = _
    rw [indicator_bigCell_eq, indicator_bigCell_eq]
    simp only [Jfun, refGL3, cw, Efun, eFam, Subgroup.coe_mul]
    have := cellWt_mul_self SQ ((g : AdelicGL2 (𝓞 ℚ) ℚ) * (embS SQ (yy i) : AdelicGL2 (𝓞 ℚ) ℚ))
    linear_combination this * Wfd par (g * embS SQ (yy i) * hμf) *
      (∏ p : ↥SQ, F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ))
        (longWeyl3 * transposeInv3 (iotaGL (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) ((g : AdelicGL2 (𝓞 ℚ) ℚ) * (embS SQ (yy i) : AdelicGL2 (𝓞 ℚ) ℚ)))) * kkAt yy k₀ i p)) *
      (∏ᶠ v, if v ∈ SQ then (1 : ℂ) else dualWhittakerFn3 (F.whittakerLoc v)
        (iotaGL (localAt ℚ v ((g : AdelicGL2 (𝓞 ℚ) ℚ) * (embS SQ (yy i) : AdelicGL2 (𝓞 ℚ) ℚ) * (hμf : AdelicGL2 (𝓞 ℚ) ℚ))))) *
      ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det ((g : AdelicGL2 (𝓞 ℚ) ℚ) * (embS SQ (yy i) : AdelicGL2 (𝓞 ℚ) ℚ))) : ℝ) : ℂ) ^ (s' - 1 / 2)
  choose σv hσv using hrow
  refine ⟨∑ i : Fin m, |σv i|, fun α s' hs' => ?_⟩
  have hall : ∀ i : Fin m, σv i < s'.re := fun i =>
    lt_of_le_of_lt ((le_abs_self _).trans (Finset.single_le_sum (fun j _ => abs_nonneg (σv j)) (Finset.mem_univ i))) hs'
  have hISO' : ∀ (g : finiteAdelicGL2Subgroup ℚ),
      (∀ p : ↥SQ, ∃ n ∈ (unipotentGL2Hom (R := (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)).range, ∃ u ∈ U p,
        n * u = localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)) → ∀ i : Fin m, _ :=
    fun g hg i => hISO g (embS SQ (yy i)) i hg (fun p => localAt_embS_of_mem SQ (yy i) p) (fun v hv => localAt_embS_of_not_mem SQ (yy i) hv)
  have hIso := integrable_Iso F w w₀ yy k₀ hμf (Wfd par) R U μf μNFin hUo hc₀ hM hISO' s' (fun i => hσv i s' (hall i)) α
  refine hIso.congr (Filter.Eventually.of_forall fun g => ?_)

  have hE : (∏ᶠ v, if v ∈ SQ then (1 : ℂ) else dualWhittakerFn3 (F.whittakerLoc v)
      (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ ((g * hμf : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)))) =
      Efun F SQ ((g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf) := by
    refine finprod_congr fun v => ?_
    by_cases hv : v ∈ SQ
    · rw [if_pos hv, eFam_of_mem _ hv]
    · rw [if_neg hv, eFam_of_not_mem _ hv, componentAt3_iota, Subgroup.coe_mul]
  have hO : ∀ p : ↥SQ, (cutSet (U p)).indicator (fun y => ((modulus ((Matrix.GeneralLinearGroup.det y :
      ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ))
      (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)) = rloc (U p) (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)) := by
    intro p
    rw [rloc, Set.indicator_apply]
    split_ifs <;> simp
  symm
  show (bigCell SQ).indicator _ g * (bigCell SQ).indicator _ g * _ = Iso F hμf R U (SQ := SQ) α s' g
  rw [indicator_bigCell_eq, indicator_bigCell_eq, hE, Finset.prod_congr rfl fun p _ => hO p]
  simp only [Iso, cw]
  linear_combination (cellWt_mul_self SQ (g : AdelicGL2 (𝓞 ℚ) ℚ)) *
    (∏ p : ↥SQ, rloc (U p) (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ))) * R α (g : AdelicGL2 (𝓞 ℚ) ℚ) *
    Efun F SQ ((g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf) * ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s' - 1 / 2)

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_cutoff_remainder_mul_finprod_away.KcRsCellIso"

end S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_cutoff_remainder_mul_finprod_away
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_cutoff_remainder_mul_finprod_away (solution)
