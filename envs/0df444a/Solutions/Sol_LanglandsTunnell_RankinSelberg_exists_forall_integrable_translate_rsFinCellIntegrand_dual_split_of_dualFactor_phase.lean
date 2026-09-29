-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_forall_integrable_translate_rsFinCellIntegrand_dual_split_of_dualFactor_phase
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/97478d26-aec6-5ae2-a516-642e906ef11d

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
import Theorems.Thm_NumberField_StandardAddChar_psiLocal_rat_eq_psiV
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_HaarQuotient_exists_lintegral_comp_mul_right_withDensity_density_eq_mul
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_rsFinCellIntegrand_translate_and_dual
import Theorems.Thm_LanglandsTunnell_RankinSelberg_finite_mulSupport_and_continuous_and_exists_phase_finprod_dualWhittakerFn3_away
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_translate_rsFinCellIntegrand_dual_split_of_dualFactor_phase
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

namespace KcRsCellJT

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

section AddChars

theorem norm_psiPadicFun {p : ℕ} [Fact p.Prime] (x : ℚ_[p]) : ‖psiPadicFun x‖ = 1 := by
  unfold psiPadicFun
  set a : ℤ := (exists_pPow_approx x).choose
  set k : ℕ := (exists_pPow_approx x).choose_spec.choose
  have h : -(2 * (Real.pi : ℂ) * Complex.I) * ((a : ℂ) / (p : ℂ) ^ k) =
      ((-(2 * Real.pi * ((a : ℝ) / (p : ℝ) ^ k)) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

local instance (q : Nat.Primes) : Fact q.1.Prime := ⟨q.2⟩ in
theorem norm_psiV (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) : ‖psiV v x‖ = 1 := by
  rw [psiV_apply, psiPadic_apply, norm_psiPadicFun]

theorem norm_psiFin (t : FiniteAdeleRing (𝓞 ℚ) ℚ) : ‖psiFin t‖ = 1 := by
  rw [psiFin_apply, finprod_eq_prod_of_mulSupport_subset _ (s := (mulSupport_psiV_finite t).toFinset)
    (by simp), norm_prod]
  exact Finset.prod_eq_one fun v _ => norm_psiV v _

theorem norm_psiQ_of_fst_eq_zero (t : AdeleRing (𝓞 ℚ) ℚ) (ht : t.1 = 0) : ‖psiQ t‖ = 1 := by
  rw [psiQ_apply, ht, AddChar.map_zero_eq_one, one_mul, norm_psiFin]

theorem psiQ_adeleSingleAt (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) :
    psiQ (adeleSingleAt ℚ v x) = psiV v x := by
  rw [adeleSingleAt_apply, psiQ_apply, AddChar.map_zero_eq_one, one_mul, psiFin_apply]
  rw [finprod_eq_single _ v]
  · rw [finAdeleSingleAt_apply_self]
  · intro w hw
    rw [finAdeleSingleAt_apply_of_ne ℚ v x hw, AddChar.map_zero_eq_one]

theorem psiLoc_eq_of_inv_eq_psiQ {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψQ : ψ⁻¹ = psiQ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) : psiLoc ψ v x = psiV v (-x) := by
  have hψ : ψ = psiQ⁻¹ := by rw [← hψQ, inv_inv]
  show ψ (adeleSingleAt ℚ v x) = _
  rw [hψ, AddChar.inv_apply, ← map_neg, psiQ_adeleSingleAt]

theorem psiLoc_eq_psiLocal_inv {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψQ : ψ⁻¹ = psiQ)
    (v : HeightOneSpectrum (𝓞 ℚ)) : psiLoc ψ v = (psiLocal ℚ v)⁻¹ := by
  refine DFunLike.ext _ _ fun (x : v.adicCompletion ℚ) => ?_
  rw [psiLoc_eq_of_inv_eq_psiQ hψQ, AddChar.inv_apply, psiLocal_rat_eq_psiV]

theorem norm_psiLocal (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) : ‖psiLocal ℚ v x‖ = 1 := by
  rw [psiLocal_rat_eq_psiV, norm_psiV]

theorem norm_psiLoc {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψQ : ψ⁻¹ = psiQ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) : ‖psiLoc ψ v x‖ = 1 := by
  rw [psiLoc_eq_of_inv_eq_psiQ hψQ, norm_psiV]

end AddChars

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

theorem unipotentGL2_adeleSingleAt (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) :
    unipotentGL2 (adeleSingleAt ℚ v x) = placeEmbed ℚ v (unipotentGL2 x) := by
  refine ext_of_glArch_localAt ?_ fun w => ?_
  · rw [glArch_unipotentGL2, glArch_placeEmbed, adeleSingleAt_apply]
    exact unipotentGL2_zero
  · rw [localAt_unipotentGL2, adeleSingleAt_apply]
    by_cases hw : w = v
    · subst hw
      rw [localAt_placeEmbed]
      show unipotentGL2 (finAdeleSingleAt ℚ w x w) = _
      rw [finAdeleSingleAt_apply_self]
    · rw [localAt_placeEmbed_of_ne v hw]
      show unipotentGL2 (finAdeleSingleAt ℚ v x w) = 1
      rw [finAdeleSingleAt_apply_of_ne ℚ v x hw, unipotentGL2_zero]

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

theorem archComponent3_iota (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ g) = iotaGL (glArch (𝓞 ℚ) ℚ g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show (adeleArch (𝓞 ℚ) ℚ) (embedMat2 (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j) =
    embedMat2 (glArch (𝓞 ℚ) ℚ g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, glArch_apply] <;> rfl

theorem componentAt3_transposeInv3 (v : HeightOneSpectrum (𝓞 ℚ)) (k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    componentAt3 (𝓞 ℚ) ℚ v (transposeInv3 k) = transposeInv3 (componentAt3 (𝓞 ℚ) ℚ v k) :=
  (transposeInv3_map _ k).symm

theorem componentAt3_localToAdelic3_self (v : HeightOneSpectrum (𝓞 ℚ)) (x : LocalGL3 v) :
    componentAt3 (𝓞 ℚ) ℚ v (localToAdelic3 v x) = x := by
  refine Units.ext ?_
  show ((finAdeleEval (𝓞 ℚ) ℚ v).comp (adeleFin (𝓞 ℚ) ℚ)).mapMatrix (finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ v x)) = x
  rw [show ((finAdeleEval (𝓞 ℚ) ℚ v).comp (adeleFin (𝓞 ℚ) ℚ)).mapMatrix (finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ v x)) =
      (finAdeleEval (𝓞 ℚ) ℚ v).mapMatrix ((adeleFin (𝓞 ℚ) ℚ).mapMatrix (finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ v x))) from by
      ext i j; rfl,
    mapMatrix_fin_finMatN, mapMatrix_localMatN_self]

theorem componentAt3_localToAdelic3_of_ne {v w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) (x : LocalGL3 v) :
    componentAt3 (𝓞 ℚ) ℚ w (localToAdelic3 v x) = 1 := by
  refine Units.ext ?_
  show ((finAdeleEval (𝓞 ℚ) ℚ w).comp (adeleFin (𝓞 ℚ) ℚ)).mapMatrix (finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ v x)) = 1
  rw [show ((finAdeleEval (𝓞 ℚ) ℚ w).comp (adeleFin (𝓞 ℚ) ℚ)).mapMatrix (finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ v x)) =
      (finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix ((adeleFin (𝓞 ℚ) ℚ).mapMatrix (finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ v x))) from by
      ext i j; rfl,
    mapMatrix_fin_finMatN, mapMatrix_localMatN_of_ne (Fin 3) (𝓞 ℚ) ℚ v _ hw]

theorem archComponent3_localToAdelic3 (v : HeightOneSpectrum (𝓞 ℚ)) (x : LocalGL3 v) :
    archComponent3 (𝓞 ℚ) ℚ (localToAdelic3 v x) = 1 := by
  refine Units.ext ?_
  show (adeleArch (𝓞 ℚ) ℚ).mapMatrix (finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ v x)) = 1
  rw [mapMatrix_arch_finMatN]

theorem ext3_of_components {g h : AdelicGL 3 (𝓞 ℚ) ℚ} (harch : archComponent3 (𝓞 ℚ) ℚ g = archComponent3 (𝓞 ℚ) ℚ h)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ v g = componentAt3 (𝓞 ℚ) ℚ v h) : g = h := by
  refine Units.ext (matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ ?_ ?_)
  · exact congrArg Units.val harch
  · refine matrixFin_ext (Fin 3) (𝓞 ℚ) ℚ fun w => ?_
    have := congrArg Units.val (hfin w)
    change ((finAdeleEval (𝓞 ℚ) ℚ w).comp (adeleFin (𝓞 ℚ) ℚ)).mapMatrix (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      ((finAdeleEval (𝓞 ℚ) ℚ w).comp (adeleFin (𝓞 ℚ) ℚ)).mapMatrix (h : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) at this
    have e : ∀ M : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ),
        ((finAdeleEval (𝓞 ℚ) ℚ w).comp (adeleFin (𝓞 ℚ) ℚ)).mapMatrix M =
          (finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix ((adeleFin (𝓞 ℚ) ℚ).mapMatrix M) := fun M => by ext i j; rfl
    rwa [e, e] at this

theorem commute_localToAdelic3_of_ne {v w : HeightOneSpectrum (𝓞 ℚ)} (hvw : v ≠ w) (x : LocalGL3 v) (y : LocalGL3 w) :
    Commute (localToAdelic3 v x) (localToAdelic3 w y) := by
  refine ext3_of_components ?_ fun u => ?_
  · rw [map_mul, map_mul, archComponent3_localToAdelic3, archComponent3_localToAdelic3]
  · rw [map_mul, map_mul]
    by_cases hu : u = v
    · subst hu
      rw [componentAt3_localToAdelic3_self, componentAt3_localToAdelic3_of_ne hvw, mul_one, one_mul]
    · rw [componentAt3_localToAdelic3_of_ne hu]
      by_cases hu' : u = w
      · subst hu'; rw [componentAt3_localToAdelic3_self, one_mul, mul_one]
      · rw [componentAt3_localToAdelic3_of_ne hu']

variable (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))

abbrev Loc3Prod : Type := ∀ p : ↥SQ, LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ))

def emb3S : Loc3Prod SQ →* AdelicGL 3 (𝓞 ℚ) ℚ :=
  MonoidHom.noncommPiCoprod (fun p : ↥SQ => localToAdelic3 (p : HeightOneSpectrum (𝓞 ℚ)))
    (fun p q hpq x y => commute_localToAdelic3_of_ne (fun h => hpq (Subtype.ext h)) x y)

theorem emb3S_apply (y : Loc3Prod SQ) :
    emb3S SQ y = Finset.univ.noncommProd (fun p : ↥SQ => localToAdelic3 (p : HeightOneSpectrum (𝓞 ℚ)) (y p))
      (fun p _ q _ hpq => commute_localToAdelic3_of_ne (fun h => hpq (Subtype.ext h)) _ _) := rfl

open scoped Classical in
theorem emb3S_mulSingle (p : ↥SQ) (x : LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ))) :
    emb3S SQ (Pi.mulSingle p x) = localToAdelic3 (p : HeightOneSpectrum (𝓞 ℚ)) x :=
  MonoidHom.noncommPiCoprod_mulSingle
    (N := fun q : ↥SQ => LocalGL3 (q : HeightOneSpectrum (𝓞 ℚ)))
    (fun q : ↥SQ => localToAdelic3 (q : HeightOneSpectrum (𝓞 ℚ))) p x

theorem emb3S_induction (y : Loc3Prod SQ) (P : AdelicGL 3 (𝓞 ℚ) ℚ → Prop)
    (hmul : ∀ a b, P a → P b → P (a * b)) (hone : P 1)
    (hbase : ∀ p : ↥SQ, P (localToAdelic3 (p : HeightOneSpectrum (𝓞 ℚ)) (y p))) : P (emb3S SQ y) := by
  rw [emb3S_apply]
  exact Finset.noncommProd_induction _ _ _ P hmul hone fun p _ => hbase p

theorem archComponent3_emb3S (y : Loc3Prod SQ) : archComponent3 (𝓞 ℚ) ℚ (emb3S SQ y) = 1 := by
  refine emb3S_induction SQ y (fun z => archComponent3 (𝓞 ℚ) ℚ z = 1) ?_ (map_one _) fun p => archComponent3_localToAdelic3 _ _
  intro a b ha hb; rw [map_mul, ha, hb, one_mul]

theorem componentAt3_emb3S_of_not_mem (y : Loc3Prod SQ) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∉ SQ) :
    componentAt3 (𝓞 ℚ) ℚ v (emb3S SQ y) = 1 := by
  refine emb3S_induction SQ y (fun z => componentAt3 (𝓞 ℚ) ℚ v z = 1) ?_ (map_one _) fun p => ?_
  · intro a b ha hb; rw [map_mul, ha, hb, one_mul]
  · have hne : v ≠ (p : HeightOneSpectrum (𝓞 ℚ)) := fun h => hv (h ▸ p.2)
    exact componentAt3_localToAdelic3_of_ne hne _

open scoped Classical in
theorem componentAt3_emb3S_of_mem (y : Loc3Prod SQ) (p : ↥SQ) :
    componentAt3 (𝓞 ℚ) ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (emb3S SQ y) = y p := by

  have h : (componentAt3 (𝓞 ℚ) ℚ (p : HeightOneSpectrum (𝓞 ℚ))).comp (emb3S SQ) =
      Pi.evalMonoidHom (fun q : ↥SQ => LocalGL3 (q : HeightOneSpectrum (𝓞 ℚ))) p := by
    refine MonoidHom.pi_ext fun q x => ?_
    rw [MonoidHom.comp_apply, emb3S_mulSingle, Pi.evalMonoidHom_apply]
    by_cases hq : q = p
    · subst hq; rw [componentAt3_localToAdelic3_self, Pi.mulSingle_eq_same]
    · have hq' : (p : HeightOneSpectrum (𝓞 ℚ)) ≠ q := fun h => hq (Subtype.ext h).symm
      rw [componentAt3_localToAdelic3_of_ne hq', Pi.mulSingle_eq_of_ne (Ne.symm hq)]
  exact DFunLike.congr_fun h y

end GL3

section LocallyConstant

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Y : Type*}

theorem isLocallyConstant_of_rightInvariant (U : Subgroup G) (hU : IsOpen (U : Set G)) (W : G → Y)
    (h : ∀ k ∈ U, ∀ g, W (g * k) = W g) : IsLocallyConstant W := by
  refine (IsLocallyConstant.iff_exists_open W).2 fun g => ⟨(fun k => g * k) '' (U : Set G), ?_, ⟨1, U.one_mem, mul_one g⟩, ?_⟩
  · exact (Homeomorph.mulLeft g).isOpenMap _ hU
  · rintro _ ⟨k, hk, rfl⟩
    exact h k hk g

theorem IsLocallyConstant.add' {M : Type*} [Add M] {X : Type*} [TopologicalSpace X] {f g : X → M}
    (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) : IsLocallyConstant (f + g) :=
  (hf.prodMk hg).comp fun q : M × M => q.1 + q.2

theorem IsLocallyConstant.smul' {R M : Type*} [SMul R M] {X : Type*} [TopologicalSpace X] {f : X → M}
    (hf : IsLocallyConstant f) (c : R) : IsLocallyConstant (c • f) :=
  hf.comp fun m => c • m

theorem IsLocallyConstant.mul' {M : Type*} [Mul M] {X : Type*} [TopologicalSpace X] {f g : X → M}
    (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) : IsLocallyConstant (f * g) :=
  (hf.prodMk hg).comp fun q : M × M => q.1 * q.2

def locallyConstantSubmodule (X : Type*) [TopologicalSpace X] : Submodule ℂ (X → ℂ) where
  carrier := {f | IsLocallyConstant f}
  add_mem' := fun hf hg => IsLocallyConstant.add' hf hg
  zero_mem' := IsLocallyConstant.const 0
  smul_mem' := fun c _ hf => IsLocallyConstant.smul' hf c

end LocallyConstant

section Cyclic

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

theorem isLocallyConstant_of_mem_gl3CyclicSubspace {W : GL (Fin 3) F → ℂ} (hW : IsLocallyConstant W)
    {f : GL (Fin 3) F → ℂ} (hf : f ∈ gl3CyclicSubspace W) : IsLocallyConstant f := by
  have hle : gl3CyclicSubspace W ≤ locallyConstantSubmodule (GL (Fin 3) F) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h, rfl⟩
    exact hW.comp_continuous (continuous_mul_const h)
  exact hle hf

theorem isGL3PsiWhittakerFn_of_mem_gl3CyclicSubspace {ψ : AddChar F ℂ} {W : GL (Fin 3) F → ℂ}
    (hW : IsGL3PsiWhittakerFn ψ W) {f : GL (Fin 3) F → ℂ} (hf : f ∈ gl3CyclicSubspace W) : IsGL3PsiWhittakerFn ψ f := by
  have hle : gl3CyclicSubspace W ≤ gl3PsiWhittakerFnSpace F ℂ ψ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h, rfl⟩
    exact rightTranslate_mem_gl3PsiWhittakerFnSpace ψ h hW
  exact hle hf

theorem continuous_iotaGL : Continuous (iotaGL : GL (Fin 2) F →* GL (Fin 3) F) := by
  have hE : Continuous (embedMat2 : Matrix (Fin 2) (Fin 2) F → Matrix (Fin 3) (Fin 3) F) := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    all_goals first
      | exact continuous_const
      | exact continuous_id.matrix_elem _ _
  refine Units.continuous_iff.2 ⟨hE.comp Units.continuous_val, hE.comp Units.continuous_coe_inv⟩

theorem continuous_transposeInv3 : Continuous (transposeInv3 : GL (Fin 3) F → GL (Fin 3) F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_coe_inv.matrix_transpose :
      Continuous fun g : GL (Fin 3) F => (((g⁻¹ : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F)ᵀ)
  · exact (Units.continuous_val.matrix_transpose :
      Continuous fun g : GL (Fin 3) F => ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ)

theorem continuous_transposeInvN2 : Continuous (transposeInvN (Fin 2) : GL (Fin 2) F → GL (Fin 2) F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_coe_inv.matrix_transpose :
      Continuous fun g : GL (Fin 2) F => (((g⁻¹ : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)ᵀ)
  · exact (Units.continuous_val.matrix_transpose :
      Continuous fun g : GL (Fin 2) F => ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ)

end Cyclic

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

section Support
variable (hψQ : ψ⁻¹ = psiQ)
  (hF0 : ∀ v, ¬ IsRamifiedIn K v → addCharLevel (psiLoc ψ v) = 0 → F.whittakerLoc v 1 = 1)
  (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), addCharLevel (psiLoc ψ v) = 0)
  (hBad : ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
      (∀ v ∈ T, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v, F.whittakerLoc v (g * k) = F.whittakerLoc v g) ∧
      (∀ v ∈ T, IsBadPlace K μ v → ∀ W ∈ gl3CyclicSubspace (F.whittakerLoc v), W ≠ 0 →
        F.whittakerLoc v ∈ gl3CyclicSubspace W))
  {S' : Finset (HeightOneSpectrum (𝓞 ℚ))} (hgood : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S' → ¬ IsBadPlace K μ p)
include hψQ hF0 hlev hBad hgood

theorem isLocallyConstant_whittakerLoc' (v : HeightOneSpectrum (𝓞 ℚ)) : IsLocallyConstant (F.whittakerLoc v) :=
  (LanglandsTunnell.RankinSelberg.finite_mulSupport_and_continuous_and_exists_phase_finprod_dualWhittakerFn3_away
    K pins ψ hψQ μ F hF0 hlev hBad S' hgood ∅).1 v

open scoped Classical in

theorem finite_mulSupport_eFam (Y : AdelicGL2 (𝓞 ℚ) ℚ) : (Function.mulSupport (eFam F SQ Y)).Finite :=
  (LanglandsTunnell.RankinSelberg.finite_mulSupport_and_continuous_and_exists_phase_finprod_dualWhittakerFn3_away
    K pins ψ hψQ μ F hF0 hlev hBad S' hgood SQ).2.1 Y

theorem continuous_Efun_coe : Continuous fun g : finiteAdelicGL2Subgroup ℚ => Efun F SQ (g : AdelicGL2 (𝓞 ℚ) ℚ) :=
  (LanglandsTunnell.RankinSelberg.finite_mulSupport_and_continuous_and_exists_phase_finprod_dualWhittakerFn3_away
    K pins ψ hψQ μ F hF0 hlev hBad S' hgood SQ).2.2.1

theorem norm_Efun_unipotentGL2_mul (t : AdeleRing (𝓞 ℚ) ℚ) (Y : AdelicGL2 (𝓞 ℚ) ℚ) :
    ‖Efun F SQ (unipotentGL2 t * Y)‖ = ‖Efun F SQ Y‖ := by
  obtain ⟨θ, hθ, h⟩ := (LanglandsTunnell.RankinSelberg.finite_mulSupport_and_continuous_and_exists_phase_finprod_dualWhittakerFn3_away
    K pins ψ hψQ μ F hF0 hlev hBad S' hgood SQ).2.2.2 t Y
  change ‖∏ᶠ v, eFam F SQ (unipotentGL2 t * Y) v‖ = ‖∏ᶠ v, eFam F SQ Y v‖
  simp only [eFam]
  rw [h, norm_mul, hθ, one_mul]

end Support

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

section EulerSplit

variable {K : Type} [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
  {pins : CarrierPins ℚ} {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
  (F : CubicInductionForm K pins ψ μ) (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
  (hF0 : ∀ v, ¬ IsRamifiedIn K v → addCharLevel (psiLoc ψ v) = 0 → F.whittakerLoc v 1 = 1)
  (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), addCharLevel (psiLoc ψ v) = 0)
  {S' : Finset (HeightOneSpectrum (𝓞 ℚ))} (hgood : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S' → ¬ IsBadPlace K μ p)
  (hμf : finiteAdelicGL2Subgroup ℚ) (hSQμ : ∀ p : ↥SQ, localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (hμf : AdelicGL2 (𝓞 ℚ) ℚ) = 1)

variable (hψQ : ψ⁻¹ = psiQ)
  (hBad : ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
      (∀ v ∈ T, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v, F.whittakerLoc v (g * k) = F.whittakerLoc v g) ∧
      (∀ v ∈ T, IsBadPlace K μ v → ∀ W ∈ gl3CyclicSubspace (F.whittakerLoc v), W ≠ 0 →
        F.whittakerLoc v ∈ gl3CyclicSubspace W))
include hF0 hlev hgood hψQ hBad

theorem finprod_eq_prod_mul_Efun (Y : AdelicGL2 (𝓞 ℚ) ℚ) (fam : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (loc : ↥SQ → ℂ) (hS : ∀ p : ↥SQ, fam p = loc p) (hA : ∀ v, v ∉ SQ → fam v = eFam F SQ Y v) :
    ∏ᶠ v, fam v = (∏ p : ↥SQ, loc p) * Efun F SQ Y := by
  classical
  let famS : HeightOneSpectrum (𝓞 ℚ) → ℂ := fun v => if hv : v ∈ SQ then loc ⟨v, hv⟩ else 1
  have hfam : fam = fun v => famS v * eFam F SQ Y v := by
    funext v
    by_cases hv : v ∈ SQ
    · simp only [famS, dif_pos hv, eFam_of_mem Y hv, mul_one]; exact hS ⟨v, hv⟩
    · simp only [famS, dif_neg hv, one_mul]; exact hA v hv
  have hsuppS : Function.mulSupport famS ⊆ (SQ : Set (HeightOneSpectrum (𝓞 ℚ))) := by
    intro v hv
    by_contra h
    exact hv (by simp [famS, show v ∉ SQ from h])
  rw [hfam, finprod_mul_distrib (SQ.finite_toSet.subset hsuppS) (finite_mulSupport_eFam hψQ hF0 hlev hBad hgood Y), Efun,
    finprod_eq_prod_of_mulSupport_subset _ hsuppS, ← Finset.prod_coe_sort SQ]
  congr 1
  exact Finset.prod_congr rfl fun p _ => by simp [famS, p.2]

include hSQμ

open scoped Classical in

theorem finprod_dual_split (Wb : ∀ p : ↥SQ, LocalGL3 p.1 → ℂ) (X : finiteAdelicGL2Subgroup ℚ) :
    (∏ᶠ v, (if hv : v ∈ SQ then dualWhittakerFn3 (Wb ⟨v, hv⟩) else dualWhittakerFn3 (F.whittakerLoc v))
        (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ ((X * hμf : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)))) =
      (∏ p : ↥SQ, dualWhittakerFn3 (Wb p) (iotaGL (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (X : AdelicGL2 (𝓞 ℚ) ℚ)))) *
        Efun F SQ ((X : AdelicGL2 (𝓞 ℚ) ℚ) * hμf) := by
  refine finprod_eq_prod_mul_Efun F SQ hF0 hlev hgood hψQ hBad _ _ _ (fun p => ?_) (fun v hv => ?_)
  · rw [dif_pos p.2, componentAt3_iota, Subgroup.coe_mul, map_mul, hSQμ p, mul_one]
  · rw [dif_neg hv, componentAt3_iota, eFam_of_not_mem _ hv, Subgroup.coe_mul]

open scoped Classical in

theorem finprod_hybrid_split (Wb : ∀ p : ↥SQ, LocalGL3 p.1 → ℂ) (X : finiteAdelicGL2Subgroup ℚ) :
    (∏ᶠ v, (if hv : v ∈ SQ then Wb ⟨v, hv⟩ else dualWhittakerFn3 (F.whittakerLoc v))
        (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ ((X * hμf : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)))) =
      (∏ p : ↥SQ, Wb p (iotaGL (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (X : AdelicGL2 (𝓞 ℚ) ℚ)))) *
        Efun F SQ ((X : AdelicGL2 (𝓞 ℚ) ℚ) * hμf) := by
  refine finprod_eq_prod_mul_Efun F SQ hF0 hlev hgood hψQ hBad _ _ _ (fun p => ?_) (fun v hv => ?_)
  · rw [dif_pos p.2, componentAt3_iota, Subgroup.coe_mul, map_mul, hSQμ p, mul_one]
  · rw [dif_neg hv, componentAt3_iota, eFam_of_not_mem _ hv, Subgroup.coe_mul]

theorem finprod_translate_split (kk : Loc3Prod SQ) (X : finiteAdelicGL2Subgroup ℚ) :
    (∏ᶠ v, dualWhittakerFn3 (F.whittakerLoc v)
        (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ ((X * hμf : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) *
          transposeInv3 (emb3S SQ kk)))) =
      (∏ p : ↥SQ, F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ))
          (longWeyl3 * transposeInv3 (iotaGL (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (X : AdelicGL2 (𝓞 ℚ) ℚ))) * kk p)) *
        Efun F SQ ((X : AdelicGL2 (𝓞 ℚ) ℚ) * hμf) := by
  refine finprod_eq_prod_mul_Efun F SQ hF0 hlev hgood hψQ hBad _ _ _ (fun p => ?_) (fun v hv => ?_)
  · rw [map_mul, componentAt3_iota, componentAt3_transposeInv3, componentAt3_emb3S_of_mem, Subgroup.coe_mul, map_mul,
      hSQμ p, mul_one, dualWhittakerFn3_apply, transposeInv3_mul, transposeInv3_transposeInv3, mul_assoc]
  · rw [map_mul, componentAt3_iota, componentAt3_transposeInv3, componentAt3_emb3S_of_not_mem SQ kk hv, transposeInv3_one,
      mul_one, eFam_of_not_mem _ hv, Subgroup.coe_mul]

end EulerSplit

theorem localAt_listProd_eq_one {ι : Type*} (L : List ι) (f : ι → AdelicGL2 (𝓞 ℚ) ℚ) (p : HeightOneSpectrum (𝓞 ℚ))
    (h : ∀ q, localAt ℚ p (f q) = 1) : localAt ℚ p (L.map f).prod = 1 := by
  rw [map_list_prod, List.map_map]
  exact List.prod_eq_one fun x hx => by
    obtain ⟨q, _, rfl⟩ := List.mem_map.1 hx
    exact h q

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

theorem mem_range_unipotentGL2Hom_iff {A : Type*} [CommRing A] (g : GL (Fin 2) A) :
    g ∈ (unipotentGL2Hom (R := A)).range ↔
      (g : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 ∧ (g : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 ∧
        (g : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := by
  constructor
  · rintro ⟨a, rfl⟩
    simp [unipotentGL2Hom]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) A) 0 1), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2Hom, h00, h10, h11]

theorem isClosed_range_unipotentGL2Hom {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [T1Space A] : IsClosed (((unipotentGL2Hom (R := A)).range : Subgroup (GL (Fin 2) A)) : Set (GL (Fin 2) A)) := by
  have hc : ∀ i j : Fin 2, Continuous fun g : GL (Fin 2) A => (g : Matrix (Fin 2) (Fin 2) A) i j :=
    fun i j => Units.continuous_val.matrix_elem i j
  have : (((unipotentGL2Hom (R := A)).range : Subgroup (GL (Fin 2) A)) : Set (GL (Fin 2) A)) =
      ((fun g : GL (Fin 2) A => (g : Matrix (Fin 2) (Fin 2) A) 0 0) ⁻¹' {1} ∩
        (fun g : GL (Fin 2) A => (g : Matrix (Fin 2) (Fin 2) A) 1 0) ⁻¹' {0}) ∩
        (fun g : GL (Fin 2) A => (g : Matrix (Fin 2) (Fin 2) A) 1 1) ⁻¹' {1} := by
    ext g
    simp only [SetLike.mem_coe, mem_range_unipotentGL2Hom_iff, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, and_assoc]
  rw [this]
  exact ((isClosed_singleton.preimage (hc 0 0)).inter (isClosed_singleton.preimage (hc 1 0))).inter
    (isClosed_singleton.preimage (hc 1 1))

theorem isClosed_finUnipotent :
    IsClosed ((RSCarrier.finUnipotent : Subgroup ↥(finiteAdelicGL2Subgroup ℚ)) : Set ↥(finiteAdelicGL2Subgroup ℚ)) := by
  rw [show ((RSCarrier.finUnipotent : Subgroup ↥(finiteAdelicGL2Subgroup ℚ)) : Set ↥(finiteAdelicGL2Subgroup ℚ)) =
      Subtype.val ⁻¹' ((adelicUnipotent ℚ : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)) : Set (AdelicGL2 (𝓞 ℚ) ℚ)) from rfl]
  exact isClosed_range_unipotentGL2Hom.preimage continuous_subtype_val

theorem coe_finUnipotent_mem (n : (RSCarrier.finUnipotent : Subgroup ↥(finiteAdelicGL2Subgroup ℚ))) :
    ((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) ∈ adelicUnipotent ℚ := n.2

theorem finUnipotent_comm (a b : (RSCarrier.finUnipotent : Subgroup ↥(finiteAdelicGL2Subgroup ℚ))) : a * b = b * a := by
  obtain ⟨s, hs⟩ := eq_unipotentGL2_of_mem_adelicUnipotent (coe_finUnipotent_mem a)
  obtain ⟨t, ht⟩ := eq_unipotentGL2_of_mem_adelicUnipotent (coe_finUnipotent_mem b)
  refine Subtype.ext (Subtype.ext ?_)
  show ((a : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) * ((b : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) =
    ((b : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) * ((a : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)
  rw [hs, ht, ← unipotentGL2_add, ← unipotentGL2_add, add_comm]

theorem isMulRightInvariant_of_comm {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ' : Measure G) [μ'.IsMulLeftInvariant] (hcomm : ∀ a b : G, a * b = b * a) : μ'.IsMulRightInvariant :=
  ⟨fun g => by
    have : (fun h : G => h * g) = fun h => g * h := funext fun h => hcomm h g
    rw [this]
    exact map_mul_left_eq_self μ' g⟩

theorem cellWt_mul_self (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (X : AdelicGL2 (𝓞 ℚ) ℚ) : cellWt SQ X * cellWt SQ X = cellWt SQ X := by
  unfold cellWt; split_ifs <;> simp

open scoped Classical in

theorem localAt_hμf_eq_one {K : Type} [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (SQ S' : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p.adicCompletionIntegers ℚ)
    (hπ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p) ≠ 0)
    (hμf : finiteAdelicGL2Subgroup ℚ)
    (hhμf : (hμf : AdelicGL2 (𝓞 ℚ) ℚ) =
      ((S' \ SQ).toList.map (fun p => if hp : p ∉ SQ then
          UnramifiedWhittaker.placeEmbed ℚ p
            ((UnramifiedWhittaker.scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p))
              (hπ p hp)) ^ (-(inducedLevelAt K μ p : ℤ)))
        else 1)).prod)
    (p : ↥SQ) : localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (hμf : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := by
  rw [hhμf]
  refine localAt_listProd_eq_one _ _ _ fun q => ?_
  by_cases hq : q ∉ SQ
  · rw [dif_pos hq]
    exact localAt_placeEmbed_of_ne q (fun h => hq (h ▸ p.2)) _
  · rw [dif_neg hq, map_one]

section JT

variable {K : Type} [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
  {pins : CarrierPins ℚ} {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
  (F : CubicInductionForm K pins ψ μ) {SQ : Finset (HeightOneSpectrum (𝓞 ℚ))}
  (kk : Loc3Prod SQ) (hμf : finiteAdelicGL2Subgroup ℚ) (Wd : finiteAdelicGL2Subgroup ℚ → ℂ)

def refK (X : AdelicGL2 (𝓞 ℚ) ℚ) : ℂ :=
  ∏ p : ↥SQ, F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ))
    (longWeyl3 * transposeInv3 (iotaGL (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) X)) * kk p)

theorem norm_refK_unipotent_mul (hψQ : ψ⁻¹ = psiQ) (t : AdeleRing (𝓞 ℚ) ℚ) (X : AdelicGL2 (𝓞 ℚ) ℚ) :
    ‖refK F kk (unipotentGL2 t * X)‖ = ‖refK F kk X‖ := by
  simp only [refK, norm_prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [map_mul, localAt_unipotentGL2, ← unipotent_eq_unipotentGL2, map_mul, transposeInv3_mul, ← mul_assoc,
    longWeyl3_mul_transposeInv3_iotaGL_unipotent, mul_assoc, mul_assoc, F.whittakerLoc_law, zero_add, norm_mul,
    norm_psiLoc hψQ, one_mul, ← mul_assoc]

theorem continuous_refK_coe (hlc : ∀ v : HeightOneSpectrum (𝓞 ℚ), IsLocallyConstant (F.whittakerLoc v)) :
    Continuous fun g : finiteAdelicGL2Subgroup ℚ => refK F kk (g : AdelicGL2 (𝓞 ℚ) ℚ) := by
  refine continuous_finsetProd _ fun p _ => ?_
  refine (hlc _).continuous.comp ?_
  exact ((continuous_const.mul (continuous_transposeInv3.comp (continuous_iotaGL.comp (continuous_projAt _)))).mul continuous_const)

def JfunK (s' : ℂ) (g : finiteAdelicGL2Subgroup ℚ) : ℂ :=
  cellWt SQ (g : AdelicGL2 (𝓞 ℚ) ℚ) * Wd (g * hμf) * refK F kk (g : AdelicGL2 (𝓞 ℚ) ℚ) *
    Efun F SQ ((g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf) * cw s' g

variable (hψQ : ψ⁻¹ = psiQ)
  (hF0 : ∀ v, ¬ IsRamifiedIn K v → addCharLevel (psiLoc ψ v) = 0 → F.whittakerLoc v 1 = 1)
  (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), addCharLevel (psiLoc ψ v) = 0)
  {S' : Finset (HeightOneSpectrum (𝓞 ℚ))} (hgood : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S' → ¬ IsBadPlace K μ p)
  (hBad : ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
      (∀ v ∈ T, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v, F.whittakerLoc v (g * k) = F.whittakerLoc v g) ∧
      (∀ v ∈ T, IsBadPlace K μ v → ∀ W ∈ gl3CyclicSubspace (F.whittakerLoc v), W ≠ 0 →
        F.whittakerLoc v ∈ gl3CyclicSubspace W))
  (hWmeas : Measurable Wd)
  (hWph : ∀ n : ↥RSCarrier.finUnipotent, ∃ θ : ℂ, ‖θ‖ = 1 ∧ ∀ g : finiteAdelicGL2Subgroup ℚ,
      Wd ((n : finiteAdelicGL2Subgroup ℚ) * g) = θ * Wd g)

include hψQ hF0 hlev hgood hBad hWmeas in
theorem measurable_JfunK (s' : ℂ) : Measurable (JfunK F kk hμf Wd (SQ := SQ) s') := by
  unfold JfunK
  refine (((((measurable_cellWt_coe SQ).mul ?_).mul ?_).mul ?_).mul (measurable_cw s'))
  · exact hWmeas.comp (measurable_id.mul_const hμf)
  · exact (continuous_refK_coe F kk (isLocallyConstant_whittakerLoc' hψQ hF0 hlev hBad hgood)).measurable
  · exact ((continuous_Efun_coe (F := F) (SQ := SQ) hψQ hF0 hlev hBad hgood).comp (continuous_id.mul continuous_const :
      Continuous fun g : finiteAdelicGL2Subgroup ℚ => g * hμf)).measurable

include hψQ hF0 hlev hgood hBad hWph in
theorem norm_JfunK_unipotent_mul (s' : ℂ) (n : (RSCarrier.finUnipotent : Subgroup ↥(finiteAdelicGL2Subgroup ℚ)))
    (g : finiteAdelicGL2Subgroup ℚ) :
    ‖JfunK F kk hμf Wd (SQ := SQ) s' ((n : finiteAdelicGL2Subgroup ℚ) * g)‖ = ‖JfunK F kk hμf Wd (SQ := SQ) s' g‖ := by
  have hn : ((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) ∈ adelicUnipotent ℚ := coe_finUnipotent_mem n
  obtain ⟨t, ht⟩ := eq_unipotentGL2_of_mem_adelicUnipotent hn
  obtain ⟨θ, hθ, hph⟩ := hWph n
  simp only [JfunK, norm_mul]
  have e1 : cellWt SQ (((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) = cellWt SQ (g : AdelicGL2 (𝓞 ℚ) ℚ) :=
    cellWt_unipotent_mul SQ hn _
  have e2 : ‖Wd ((n : finiteAdelicGL2Subgroup ℚ) * g * hμf)‖ = ‖Wd (g * hμf)‖ := by
    rw [mul_assoc, hph, norm_mul, hθ, one_mul]
  have e3 : ‖refK F kk (((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)‖ =
      ‖refK F kk (g : AdelicGL2 (𝓞 ℚ) ℚ)‖ := by
    rw [Subgroup.coe_mul, ht]; exact norm_refK_unipotent_mul F kk hψQ t _
  have e4 : ‖Efun F SQ ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) * hμf)‖ =
      ‖Efun F SQ ((g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf)‖ := by
    rw [Subgroup.coe_mul, ht, mul_assoc]; exact norm_Efun_unipotentGL2_mul (F := F) (SQ := SQ) hψQ hF0 hlev hBad hgood t _
  have e5 : cw s' ((n : finiteAdelicGL2Subgroup ℚ) * g) = cw s' g := cw_unipotent_mul s' hn g
  rw [e1, e2, e3, e4, e5]

include hψQ hF0 hlev hgood hBad hWmeas hWph in

theorem integrable_JfunK_translate [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    (μf : Measure (finiteAdelicGL2Subgroup ℚ)) [μf.IsHaarMeasure]
    (μNFin : Measure RSCarrier.finUnipotent) [μNFin.IsHaarMeasure] (s' : ℂ)
    (hJ : Integrable (JfunK F kk hμf Wd (SQ := SQ) s') (μf.withDensity (HaarQuotient.density RSCarrier.finUnipotent μNFin)))
    (y : LocProd SQ) :
    Integrable (fun g => JfunK F kk hμf Wd (SQ := SQ) s' (g * embS SQ y))
      (μf.withDensity (HaarQuotient.density RSCarrier.finUnipotent μNFin)) := by
  haveI : SecondCountableTopology ↥(finiteAdelicGL2Subgroup ℚ) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace ↥(finiteAdelicGL2Subgroup ℚ) :=
    (isClosed_finiteAdelicGL2Subgroup ℚ).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : μNFin.IsMulRightInvariant := isMulRightInvariant_of_comm μNFin finUnipotent_comm
  obtain ⟨c, -, hc⟩ := HaarQuotient.exists_lintegral_comp_mul_right_withDensity_density_eq_mul μf RSCarrier.finUnipotent
    isClosed_finUnipotent μNFin (embS SQ y)
  have hmeas := measurable_JfunK F kk hμf Wd hψQ hF0 hlev hgood hBad hWmeas s'
  refine ⟨(hmeas.comp (measurable_id.mul_const _)).aestronglyMeasurable, ?_⟩
  have hinv : ∀ (n : (RSCarrier.finUnipotent : Subgroup ↥(finiteAdelicGL2Subgroup ℚ))) (g : finiteAdelicGL2Subgroup ℚ),
      (fun g => ‖JfunK F kk hμf Wd (SQ := SQ) s' g‖ₑ) ((n : finiteAdelicGL2Subgroup ℚ) * g) =
        (fun g => ‖JfunK F kk hμf Wd (SQ := SQ) s' g‖ₑ) g := by
    intro n g
    show ‖_‖ₑ = ‖_‖ₑ
    rw [← ofReal_norm, ← ofReal_norm, norm_JfunK_unipotent_mul F kk hμf Wd hψQ hF0 hlev hgood hBad hWph]
  have key := hc _ hmeas.enorm hinv
  show ∫⁻ g, ‖JfunK F kk hμf Wd (SQ := SQ) s' (g * embS SQ y)‖ₑ ∂_ < ⊤
  rw [key]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top hJ.hasFiniteIntegral

end JT

end IsolationIntegrable

end KcRsCellJT
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_translate_rsFinCellIntegrand_dual_split_of_dualFactor_phase.KcRsCellJT"

open KcRsCellJT in
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
    (hWmeas : Measurable (Wfd par))
    (hWph : ∀ n : ↥RSCarrier.finUnipotent, ∃ θ : ℂ, ‖θ‖ = 1 ∧ ∀ g : finiteAdelicGL2Subgroup ℚ,
      Wfd par ((n : finiteAdelicGL2Subgroup ℚ) * g) = θ * Wfd par g)
    (kk : ∀ p : ↥SQ, LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ))) :
    ∃ σ : ℝ, ∀ s' : ℂ, σ < s'.re → ∀ zhat : finiteAdelicGL2Subgroup ℚ,
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → localAt ℚ v (zhat : AdelicGL2 (𝓞 ℚ) ℚ) = 1) →
      Integrable (fun g : finiteAdelicGL2Subgroup ℚ =>
          {g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                  localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => Wfd par (g * hμf) *
              ∏ p : ↥SQ, F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ))
                (longWeyl3 * transposeInv3 (iotaGL (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ))) * kk p)) (g * zhat) *
          {g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                  localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => ∏ᶠ v, if v ∈ SQ then (1 : ℂ) else dualWhittakerFn3 (F.whittakerLoc v)
                (iotaGL (localAt ℚ v ((g * hμf : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)))) (g * zhat) *
          ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det ((g * zhat : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s' - 1 / 2))
        (μf.withDensity (HaarQuotient.density RSCarrier.finUnipotent μNFin)) := by
  classical
  have hSQμ : ∀ p : ↥SQ, localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (hμf : AdelicGL2 (𝓞 ℚ) ℚ) = 1 :=
    localAt_hμf_eq_one μ SQ S' ϖ hπ hμf hhμf
  have hF1 : ∀ v, ¬ IsRamifiedIn K v → addCharLevel (psiLoc ψ v) = 0 → F.whittakerLoc v 1 = 1 :=
    fun v h1 h2 => (hF0.2 v h1 h2).1

  have hk : archComponent3 (𝓞 ℚ) ℚ (emb3S SQ kk) = 1 ∧
      ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → componentAt3 (𝓞 ℚ) ℚ v (emb3S SQ kk) = 1 :=
    ⟨archComponent3_emb3S SQ _, fun v hv => componentAt3_emb3S_of_not_mem SQ _ hv⟩
  obtain ⟨σ, hσ⟩ := LanglandsTunnell.RankinSelberg.exists_forall_integrable_rsFinCellIntegrand_translate_and_dual K _hdeg Φ SQ hSQ hb ha
    SK hSK S hS R hRc Cfin hRS φv hiso hφne hφKf μ hμ ψ hψ hlev hψQ F hF0 hFc hFw hFdw hFg hFdg hBad S' hSS' hgood ϖ hπ hϖ hμf hhμf
    WA Wf hWAf hWfC hWf1 w₀ hw₀ Wfd hWfd μf μNFin (emb3S SQ kk) hk par
  refine ⟨σ, fun s' hs' zhat hz => ?_⟩

  have hJ : Integrable (JfunK F kk hμf (Wfd par) (SQ := SQ) s') (μf.withDensity (HaarQuotient.density RSCarrier.finUnipotent μNFin)) := by
    refine (hσ s' hs').2.congr (Filter.Eventually.of_forall fun g => ?_)
    show (bigCell SQ).indicator (fun g => Wfd par (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf)) g *
        (bigCell SQ).indicator (fun g => ∏ᶠ v, dualWhittakerFn3 (F.whittakerLoc v)
          (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ ((RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf : finiteAdelicGL2Subgroup ℚ) :
            AdelicGL2 (𝓞 ℚ) ℚ) * transposeInv3 (emb3S SQ kk)))) g *
        ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s' - 1 / 2) = _
    rw [indicator_bigCell_eq, indicator_bigCell_eq, finFactor_coe, finprod_translate_split F SQ hF1 hlev hgood hμf hSQμ hψQ hBad]
    simp only [JfunK, refK, cw]
    linear_combination (cellWt_mul_self SQ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * Wfd par (g * hμf) *
      (∏ p : ↥SQ, F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ))
        (longWeyl3 * transposeInv3 (iotaGL (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ))) * kk p)) *
      Efun F SQ ((g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf) *
      ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s' - 1 / 2)

  have hz' : zhat = embS SQ (projS SQ zhat) := by
    refine Subtype.ext (ext_of_glArch_localAt ?_ fun v => ?_)
    · rw [(mem_finiteAdelicGL2Subgroup_iff ℚ _).1 zhat.2, glArch_embS]
    · by_cases hv : v ∈ SQ
      · rw [localAt_embS_of_mem SQ _ ⟨v, hv⟩, projS_apply]
      · rw [hz v hv, localAt_embS_of_not_mem SQ _ hv]
  have hT := integrable_JfunK_translate F kk hμf (Wfd par) hψQ hF1 hlev hgood hBad hWmeas hWph μf μNFin s' hJ (projS SQ zhat)
  rw [← hz'] at hT
  refine hT.congr (Filter.Eventually.of_forall fun g => ?_)
  symm
  show (bigCell SQ).indicator _ (g * zhat) * (bigCell SQ).indicator _ (g * zhat) * _ = JfunK F kk hμf (Wfd par) (SQ := SQ) s' (g * zhat)
  rw [indicator_bigCell_eq, indicator_bigCell_eq]
  simp only [JfunK, refK, cw, Efun, eFam, Subgroup.coe_mul]
  have := cellWt_mul_self SQ ((g : AdelicGL2 (𝓞 ℚ) ℚ) * (zhat : AdelicGL2 (𝓞 ℚ) ℚ))
  linear_combination this * Wfd par (g * zhat * hμf) *
      (∏ p : ↥SQ, F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ))
        (longWeyl3 * transposeInv3 (iotaGL (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) ((g : AdelicGL2 (𝓞 ℚ) ℚ) * (zhat : AdelicGL2 (𝓞 ℚ) ℚ)))) * kk p)) *
      (∏ᶠ v, if v ∈ SQ then (1 : ℂ) else dualWhittakerFn3 (F.whittakerLoc v)
        (iotaGL (localAt ℚ v ((g : AdelicGL2 (𝓞 ℚ) ℚ) * (zhat : AdelicGL2 (𝓞 ℚ) ℚ) * (hμf : AdelicGL2 (𝓞 ℚ) ℚ))))) *
      ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det ((g : AdelicGL2 (𝓞 ℚ) ℚ) * (zhat : AdelicGL2 (𝓞 ℚ) ℚ))) : ℝ) : ℂ) ^ (s' - 1 / 2)

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_translate_rsFinCellIntegrand_dual_split_of_dualFactor_phase.KcRsCellJT"

end S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_translate_rsFinCellIntegrand_dual_split_of_dualFactor_phase
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_translate_rsFinCellIntegrand_dual_split_of_dualFactor_phase (solution)
