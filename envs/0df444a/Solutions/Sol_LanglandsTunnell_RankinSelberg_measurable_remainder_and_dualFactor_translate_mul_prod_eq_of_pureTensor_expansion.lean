-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.measurable_remainder_and_dualFactor_translate_mul_prod_eq_of_pureTensor_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/abb4bc19-1971-560e-8256-172646e7eded

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_measurable_remainder_and_dualFactor_translate_mul_prod_eq_of_pureTensor_expansion
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

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

namespace KcRsCellRem

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

section UnipotentF

theorem localAt_mem_range_of_mem_adelicUnipotent (p : HeightOneSpectrum (𝓞 ℚ)) {g : AdelicGL2 (𝓞 ℚ) ℚ}
    (hg : g ∈ adelicUnipotent ℚ) : localAt ℚ p g ∈ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range := by
  obtain ⟨t, rfl⟩ := eq_unipotentGL2_of_mem_adelicUnipotent hg
  rw [localAt_unipotentGL2]
  exact ⟨Multiplicative.ofAdd (t.2 p), rfl⟩

theorem placeEmbed_unipotentGL2_mem (p : HeightOneSpectrum (𝓞 ℚ)) (x : p.adicCompletion ℚ) :
    placeEmbed ℚ p (unipotentGL2 x) ∈ adelicUnipotent ℚ := by
  rw [← unipotentGL2_adeleSingleAt]
  exact ⟨Multiplicative.ofAdd _, rfl⟩

theorem placeEmbed_mem_adelicUnipotent (p : HeightOneSpectrum (𝓞 ℚ)) {n : GL (Fin 2) (p.adicCompletion ℚ)}
    (hn : n ∈ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range) : placeEmbed ℚ p n ∈ adelicUnipotent ℚ := by
  obtain ⟨a, rfl⟩ := hn
  exact placeEmbed_unipotentGL2_mem p a.toAdd

variable (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))

theorem embS_projS_mem_adelicUnipotent {n : finiteAdelicGL2Subgroup ℚ} (hn : (n : AdelicGL2 (𝓞 ℚ) ℚ) ∈ adelicUnipotent ℚ) :
    (embS SQ (projS SQ n) : AdelicGL2 (𝓞 ℚ) ℚ) ∈ adelicUnipotent ℚ := by
  refine embS_induction SQ (projS SQ n) (fun z => (z : AdelicGL2 (𝓞 ℚ) ℚ) ∈ adelicUnipotent ℚ)
    (fun a b ha hb => Subgroup.mul_mem _ ha hb) (Subgroup.one_mem _) fun p => ?_
  exact placeEmbed_mem_adelicUnipotent _ (localAt_mem_range_of_mem_adelicUnipotent _ hn)

theorem awayPart_unipotent {n : finiteAdelicGL2Subgroup ℚ} (hn : (n : AdelicGL2 (𝓞 ℚ) ℚ) ∈ adelicUnipotent ℚ) :
    ∃ t : AdeleRing (𝓞 ℚ) ℚ, ((n * (embS SQ (projS SQ n))⁻¹ : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) = unipotentGL2 t := by
  have hmem : ((n * (embS SQ (projS SQ n))⁻¹ : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) ∈ adelicUnipotent ℚ :=
    Subgroup.mul_mem _ hn (Subgroup.inv_mem _ (embS_projS_mem_adelicUnipotent SQ hn))
  exact eq_unipotentGL2_of_mem_adelicUnipotent hmem

end UnipotentF

section GL2Side

variable (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (m : ℕ)
  (w : ∀ p : ↥SQ, Fin m → GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) → ℂ)
  (Wrem : Fin m → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
  (Wf Wfd : finiteAdelicGL2Subgroup ℚ → ℂ)
  (w₀ : GL (Fin 2) ℚ)

def w₀At (p : HeightOneSpectrum (𝓞 ℚ)) : GL (Fin 2) (p.adicCompletion ℚ) := localAt ℚ p (globalPoints (𝓞 ℚ) ℚ w₀)

theorem coe_w₀At (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) ℚ) = !![0, 1; 1, 0]) (p : HeightOneSpectrum (𝓞 ℚ)) :
    (w₀At w₀ p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0] := by
  ext i j
  rw [w₀At, localAt_apply]
  have hij : ((globalPoints (𝓞 ℚ) ℚ w₀ : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j =
      algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ((w₀ : Matrix (Fin 2) (Fin 2) ℚ) i j) := rfl
  rw [hij, hw₀]
  fin_cases i <;> fin_cases j <;> simp <;> rfl

theorem coe_globalPoints_w₀ (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) ℚ) = !![0, 1; 1, 0]) :
    ((globalPoints (𝓞 ℚ) ℚ w₀ : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) = !![0, 1; 1, 0] := by
  ext i j
  have hij : ((globalPoints (𝓞 ℚ) ℚ w₀ : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j =
      algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ((w₀ : Matrix (Fin 2) (Fin 2) ℚ) i j) := rfl
  rw [hij, hw₀]
  fin_cases i <;> fin_cases j <;> simp

def slotD (p : ↥SQ) (α : Fin m) (y : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) : ℂ :=
  ((modulus ((Matrix.GeneralLinearGroup.det y : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) :
      (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ) *
    w p α (w₀At w₀ (p : HeightOneSpectrum (𝓞 ℚ)) * transposeInvN (Fin 2) y)

def slotMat (y : LocProd SQ) (β : Fin m) : ℂ := ∏ p : ↥SQ, w p β (w₀At w₀ (p : HeightOneSpectrum (𝓞 ℚ)) * transposeInvN (Fin 2) (y p))

variable {SQ m w Wrem Wf Wfd w₀}

section Splitting

variable (_hsplit : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      Wf (RSCarrier.finFactor g) = ∑ α : Fin m, (∏ p : ↥SQ, w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) g)) * Wrem α g)
include _hsplit

theorem Wf_apply (X : finiteAdelicGL2Subgroup ℚ) :
    Wf X = ∑ α : Fin m, (∏ p : ↥SQ, w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (X : AdelicGL2 (𝓞 ℚ) ℚ))) *
      Wrem α (X : AdelicGL2 (𝓞 ℚ) ℚ) := by
  rw [← _hsplit, finFactor_coe]

theorem measurable_Wf
    (_hwmeas : ∀ (p : ↥SQ) (α : Fin m), Measurable (fun g : finiteAdelicGL2Subgroup ℚ =>
      w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ))))
    (_hWmeas : ∀ α : Fin m, Measurable (fun g : finiteAdelicGL2Subgroup ℚ => Wrem α (g : AdelicGL2 (𝓞 ℚ) ℚ))) :
    Measurable (Wf) := by
  have : Wf = fun X : finiteAdelicGL2Subgroup ℚ => ∑ α : Fin m,
      (∏ p : ↥SQ, w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (X : AdelicGL2 (𝓞 ℚ) ℚ))) * Wrem α (X : AdelicGL2 (𝓞 ℚ) ℚ) :=
    funext fun X => Wf_apply _hsplit X
  rw [this]
  refine Finset.measurable_sum _ fun α _ => Measurable.mul ?_ (_hWmeas α)
  exact Finset.measurable_prod _ fun p _ => _hwmeas p α

variable (hWfd : ∀ (gf : finiteAdelicGL2Subgroup ℚ), Wfd gf =
      ((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (gf : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) *
        Wf (RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ w₀ * transposeInvN (Fin 2) (gf : AdelicGL2 (𝓞 ℚ) ℚ))))
include hWfd

def tInv (g : finiteAdelicGL2Subgroup ℚ) : finiteAdelicGL2Subgroup ℚ := ⟨transposeInvN (Fin 2) (g : AdelicGL2 (𝓞 ℚ) ℚ), transposeInvN_mem g⟩

omit _hsplit hWfd in
theorem continuous_tInv : Continuous (tInv : finiteAdelicGL2Subgroup ℚ → finiteAdelicGL2Subgroup ℚ) :=
  (continuous_transposeInvN_adelic.comp continuous_subtype_val).subtype_mk _

theorem Wfd_eq (gf : finiteAdelicGL2Subgroup ℚ) :
    Wfd gf = ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (gf : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) *
      Wf (RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ w₀) * tInv gf) := by
  rw [hWfd, ← finFactor_mul_coe]; rfl

theorem measurable_Wfd
    (_hwmeas : ∀ (p : ↥SQ) (α : Fin m), Measurable (fun g : finiteAdelicGL2Subgroup ℚ =>
      w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ))))
    (_hWmeas : ∀ α : Fin m, Measurable (fun g : finiteAdelicGL2Subgroup ℚ => Wrem α (g : AdelicGL2 (𝓞 ℚ) ℚ))) :
    Measurable (Wfd) := by
  have : Wfd = fun gf : finiteAdelicGL2Subgroup ℚ => ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (gf : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) *
      Wf (RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ w₀) * tInv gf) := funext fun gf => Wfd_eq _hsplit hWfd gf
  rw [this]
  refine Measurable.mul ?_ ((measurable_Wf _hsplit _hwmeas _hWmeas).comp (continuous_const.mul continuous_tInv).measurable)
  have hc : Continuous fun g : AdelicGL2 (𝓞 ℚ) ℚ => Matrix.GeneralLinearGroup.det g :=
    Units.continuous_iff.2 ⟨(Units.continuous_val.matrix_det :
        Continuous fun g : AdelicGL2 (𝓞 ℚ) ℚ => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)).det),
      (Units.continuous_coe_inv.matrix_det :
        Continuous fun g : AdelicGL2 (𝓞 ℚ) ℚ => ((g⁻¹ : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)).det)⟩
  exact (Complex.continuous_ofReal.comp (((NumberField.TateGlobal.continuous_ideleNorm ℚ).comp hc).comp
    continuous_subtype_val)).measurable

end Splitting

theorem apply_placeEmbed_mul_of_rightInvariant (R' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) {p : HeightOneSpectrum (𝓞 ℚ)}
    (h : ∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ), R' (g * placeEmbed ℚ p x) = R' g)
    (u : GL (Fin 2) (p.adicCompletion ℚ)) (Z : AdelicGL2 (𝓞 ℚ) ℚ) : R' (placeEmbed ℚ p u * Z) = R' Z := by
  have hc := conj_placeEmbed p Z u
  calc R' (placeEmbed ℚ p u * Z) = R' (Z * (Z⁻¹ * placeEmbed ℚ p u * Z)) := by group
    _ = R' Z := by rw [hc, h]

section Phase

variable (hψQ' : True)
  (_hsplit : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      Wf (RSCarrier.finFactor g) = ∑ α : Fin m, (∏ p : ↥SQ, w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) g)) * Wrem α g)
  (_hwlaw : ∀ (p : ↥SQ) (α : Fin m) (x : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) (g : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)),
      w p α (unipotent x * g) = psiLocal ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x * w p α g)
  (_hWinv : ∀ (α : Fin m) (p : ↥SQ) (x : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      Wrem α (g * placeEmbed ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x) = Wrem α g)
  (_hWlaw : ∀ (α : Fin m) (t : AdeleRing (𝓞 ℚ) ℚ), t.1 = 0 →
      (∀ p : ↥SQ, localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (unipotentGL2 t) = 1) →
      ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, Wrem α (unipotentGL2 t * g) = psiQ t * Wrem α g)
include _hsplit _hwlaw _hWinv _hWlaw

theorem Wrem_unipotent_sum_mul (α : Fin m) (x : ↥SQ → AdeleRing (𝓞 ℚ) ℚ)
    (hx : ∀ p : ↥SQ, ∃ y : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ, x p = adeleSingleAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) y)
    (s : Finset ↥SQ) (Z : AdelicGL2 (𝓞 ℚ) ℚ) :
    Wrem α (unipotentGL2 (∑ p ∈ s, x p) * Z) = Wrem α Z := by
  classical
  induction s using Finset.induction_on generalizing Z with
  | empty => rw [Finset.sum_empty, unipotentGL2_zero, one_mul]
  | insert a s ha ih =>
    obtain ⟨y, hy⟩ := hx a
    rw [Finset.sum_insert ha, unipotentGL2_add, mul_assoc, hy, unipotentGL2_adeleSingleAt,
      apply_placeEmbed_mul_of_rightInvariant (Wrem α) (_hWinv α a), ih]

theorem exists_phase_Wf (t : AdeleRing (𝓞 ℚ) ℚ) (ht : t.1 = 0) :
    ∃ θ : ℂ, ‖θ‖ = 1 ∧ ∀ Y : AdelicGL2 (𝓞 ℚ) ℚ,
      Wf (RSCarrier.finFactor (unipotentGL2 t * Y)) = θ * Wf (RSCarrier.finFactor Y) := by
  classical

  let x : ↥SQ → AdeleRing (𝓞 ℚ) ℚ := fun p => adeleSingleAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (t.2 p)
  let tS : AdeleRing (𝓞 ℚ) ℚ := ∑ p : ↥SQ, x p
  let t' : AdeleRing (𝓞 ℚ) ℚ := t - tS
  have htS1 : tS.1 = 0 := by
    have : tS.1 = ∑ p : ↥SQ, (x p).1 := map_sum (adeleArch (𝓞 ℚ) ℚ) _ _
    rw [this]
    exact Finset.sum_eq_zero fun p _ => rfl
  have ht'1 : t'.1 = 0 := by
    show (adeleArch (𝓞 ℚ) ℚ) (t - tS) = 0
    rw [map_sub, show adeleArch (𝓞 ℚ) ℚ t = t.1 from rfl, show adeleArch (𝓞 ℚ) ℚ tS = tS.1 from rfl, ht, htS1, sub_zero]
  let φ : ∀ v : HeightOneSpectrum (𝓞 ℚ), AdeleRing (𝓞 ℚ) ℚ →+* v.adicCompletion ℚ := fun v =>
    (finAdeleEval (𝓞 ℚ) ℚ v).comp (adeleFin (𝓞 ℚ) ℚ)
  have hφ : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (a : AdeleRing (𝓞 ℚ) ℚ), φ v a = a.2 v := fun v a => rfl
  have htS2 : ∀ p : ↥SQ, tS.2 (p : HeightOneSpectrum (𝓞 ℚ)) = t.2 p := by
    intro p
    have : tS.2 (p : HeightOneSpectrum (𝓞 ℚ)) = ∑ q : ↥SQ, (x q).2 (p : HeightOneSpectrum (𝓞 ℚ)) := by
      have e1 := map_sum (φ (p : HeightOneSpectrum (𝓞 ℚ))) x Finset.univ
      simpa only [hφ] using e1
    rw [this, Finset.sum_eq_single p]
    · simp only [x, adeleSingleAt_apply]; exact finAdeleSingleAt_apply_self ℚ _ _
    · intro q _ hq
      have hne : (p : HeightOneSpectrum (𝓞 ℚ)) ≠ q := fun h => hq (Subtype.ext h).symm
      simp only [x, adeleSingleAt_apply]; exact finAdeleSingleAt_apply_of_ne ℚ _ _ hne
    · intro h; exact absurd (Finset.mem_univ p) h
  have ht'2 : ∀ p : ↥SQ, localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (unipotentGL2 t') = 1 := by
    intro p
    rw [localAt_unipotentGL2]
    have : t'.2 (p : HeightOneSpectrum (𝓞 ℚ)) = 0 := by
      have e2 : φ (p : HeightOneSpectrum (𝓞 ℚ)) t' = φ (p : HeightOneSpectrum (𝓞 ℚ)) t - φ (p : HeightOneSpectrum (𝓞 ℚ)) tS :=
        map_sub _ _ _
      simp only [hφ, htS2, sub_self] at e2
      exact e2
    rw [this, unipotentGL2_zero]
  refine ⟨(∏ p : ↥SQ, psiLocal ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (t.2 p)) * psiQ t', ?_, fun Y => ?_⟩
  · rw [norm_mul, norm_prod, Finset.prod_eq_one fun p _ => norm_psiLocal _ _, one_mul]
    exact norm_psiQ_of_fst_eq_zero _ ht'1
  · rw [_hsplit, _hsplit, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    have hslot : ∀ p : ↥SQ, w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (unipotentGL2 t * Y)) =
        psiLocal ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (t.2 p) * w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) Y) := by
      intro p
      rw [map_mul, localAt_unipotentGL2, ← unipotent_eq_unipotentGL2, _hwlaw]
    have hrem : Wrem α (unipotentGL2 t * Y) = psiQ t' * Wrem α Y := by
      have hdec : unipotentGL2 t = unipotentGL2 t' * unipotentGL2 (∑ p : ↥SQ, x p) := by
        rw [← unipotentGL2_add]; congr 1
        show t = (t - tS) + tS
        abel
      rw [hdec, mul_assoc, _hWlaw α t' ht'1 ht'2,
        Wrem_unipotent_sum_mul _hsplit _hwlaw _hWinv _hWlaw α x (fun p => ⟨t.2 p, rfl⟩)]
    rw [Finset.prod_congr rfl fun p _ => hslot p, Finset.prod_mul_distrib, hrem]
    ring

theorem exists_phase_Wfd
    (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) ℚ) = !![0, 1; 1, 0])
    (hWfd : ∀ (gf : finiteAdelicGL2Subgroup ℚ), Wfd gf =
      ((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (gf : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) *
        Wf (RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ w₀ * transposeInvN (Fin 2) (gf : AdelicGL2 (𝓞 ℚ) ℚ))))
    (t : AdeleRing (𝓞 ℚ) ℚ) (ht : unipotentGL2 t ∈ finiteAdelicGL2Subgroup ℚ) :
    ∃ θ : ℂ, ‖θ‖ = 1 ∧ ∀ X : finiteAdelicGL2Subgroup ℚ,
      Wfd (⟨unipotentGL2 t, ht⟩ * X) = θ * Wfd X := by
  have ht1 : t.1 = 0 := fst_eq_zero_of_unipotentGL2_mem ht
  have hnt1 : (-t).1 = 0 := by
    show adeleArch (𝓞 ℚ) ℚ (-t) = 0
    rw [map_neg, show adeleArch (𝓞 ℚ) ℚ t = t.1 from rfl, ht1, neg_zero]
  obtain ⟨θ, hθ, hph⟩ := exists_phase_Wf _hsplit _hwlaw _hWinv _hWlaw (-t) hnt1
  refine ⟨θ, hθ, fun X => ?_⟩
  rw [hWfd, hWfd]
  have hcoe : (((⟨unipotentGL2 t, ht⟩ : finiteAdelicGL2Subgroup ℚ) * X : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) =
      unipotentGL2 t * (X : AdelicGL2 (𝓞 ℚ) ℚ) := rfl
  rw [hcoe, map_mul, det_unipotentGL2, one_mul, transposeInvN_mul, ← mul_assoc,
    weyl2_mul_transposeInvN_unipotentGL2 _ (coe_globalPoints_w₀ w₀ hw₀), mul_assoc, hph]
  ring

end Phase

theorem apply_mul_embS_of_rightInvariant (R' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (h : ∀ (p : ↥SQ) (x : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      R' (g * placeEmbed ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x) = R' g)
    (X : AdelicGL2 (𝓞 ℚ) ℚ) (y : LocProd SQ) : R' (X * (embS SQ y : AdelicGL2 (𝓞 ℚ) ℚ)) = R' X := by
  revert X
  refine embS_induction SQ y (fun z => ∀ X, R' (X * (z : AdelicGL2 (𝓞 ℚ) ℚ)) = R' X) ?_ (fun X => by simp) fun p X => h p _ X
  intro a b ha hb X
  rw [Subgroup.coe_mul, ← mul_assoc, hb, ha]

theorem apply_mul_embS_inv_of_rightInvariant (R' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (h : ∀ (p : ↥SQ) (x : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      R' (g * placeEmbed ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x) = R' g)
    (X : AdelicGL2 (𝓞 ℚ) ℚ) (y : LocProd SQ) : R' (X * ((embS SQ y)⁻¹ : finiteAdelicGL2Subgroup ℚ)) = R' X := by
  have := apply_mul_embS_of_rightInvariant R' h (X * ((embS SQ y)⁻¹ : finiteAdelicGL2Subgroup ℚ)) y
  rw [mul_assoc, Subgroup.coe_inv, inv_mul_cancel, mul_one] at this
  exact this.symm

theorem apply_awayPart (R' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (h : ∀ (p : ↥SQ) (x : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      R' (g * placeEmbed ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x) = R' g)
    (g : finiteAdelicGL2Subgroup ℚ) : R' (awayPart SQ g : AdelicGL2 (𝓞 ℚ) ℚ) = R' g :=
  apply_mul_embS_inv_of_rightInvariant R' h _ _

section Isolation

variable {K : Type} [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
  {pins : CarrierPins ℚ} {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
  (F : CubicInductionForm K pins ψ μ) (hψQ : ψ⁻¹ = psiQ)
  (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) ℚ) = !![0, 1; 1, 0])
  (hμf : finiteAdelicGL2Subgroup ℚ)
  (R : Fin m → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
  (_hRinv : ∀ (α : Fin m) (p : ↥SQ) (x : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      R α (g * placeEmbed ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x) = R α g)
  (_hRexp : ∀ g : finiteAdelicGL2Subgroup ℚ, Wfd (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf) =
      ∑ α : Fin m, (∏ p : ↥SQ,
        ((modulus ((Matrix.GeneralLinearGroup.det (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)) :
            ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ) *
          w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (globalPoints (𝓞 ℚ) ℚ w₀) *
            transposeInvN (Fin 2) (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)))) * R α (g : AdelicGL2 (𝓞 ℚ) ℚ))
  (_hwlaw : ∀ (p : ↥SQ) (α : Fin m) (x : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) (g : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)),
      w p α (unipotent x * g) = psiLocal ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x * w p α g)

  (yy : Fin m → LocProd SQ) (k₀ : ∀ p : ↥SQ, LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)))
  (U : ∀ p : ↥SQ, Subgroup (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)))
  (hU1 : ∀ (p : ↥SQ), ∀ u ∈ U p, ∀ (β : Fin m) (i : Fin m),
      w p β (w₀At w₀ (p : HeightOneSpectrum (𝓞 ℚ)) * transposeInvN (Fin 2) (u * yy i p)) =
        w p β (w₀At w₀ (p : HeightOneSpectrum (𝓞 ℚ)) * transposeInvN (Fin 2) (yy i p)))
  (hU2 : ∀ (p : ↥SQ), ∀ u ∈ U p,
      F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * transposeInv3 (iotaGL u) * k₀ p) =
        F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * k₀ p))

def kkAt (i : Fin m) (p : ↥SQ) : LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)) := (transposeInv3 (iotaGL (yy i p)))⁻¹ * k₀ p

include hψQ hw₀ _hRinv _hRexp _hwlaw hU1 hU2

theorem isolation_identity (g : finiteAdelicGL2Subgroup ℚ)
    (hg : ∀ p : ↥SQ, ∃ n ∈ (unipotentGL2Hom (R := (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)).range, ∃ u ∈ U p,
      n * u = localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ))
    (i : Fin m) :
    Wfd ((g * embS SQ (yy i)) * hμf) *
        ∏ p : ↥SQ, F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ))
          (longWeyl3 * transposeInv3 (iotaGL (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) ((g * embS SQ (yy i) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ))) *
            kkAt yy k₀ i p) =
      (∏ p : ↥SQ, F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * k₀ p) *
          ((modulus ((Matrix.GeneralLinearGroup.det (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)) :
              ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det (yy i p) : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) :
              (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ)) *
        ∑ β : Fin m, slotMat SQ m w w₀ (yy i) β * R β (g : AdelicGL2 (𝓞 ℚ) ℚ) := by
  classical

  have hg' := hg
  choose n hn u hu hnu using hg'
  have hx : ∀ p : ↥SQ, ∃ x : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ, n p = unipotent x := by
    intro p; obtain ⟨a, ha⟩ := hn p; exact ⟨a.toAdd, by rw [← ha, unipotent_eq_unipotentGL2]; rfl⟩
  choose x hxn using hx

  have hexp := _hRexp (g * embS SQ (yy i))
  rw [finFactor_coe] at hexp
  have hloc : ∀ p : ↥SQ, localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) ((g * embS SQ (yy i) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) =
      unipotent (x p) * u p * yy i p := by
    intro p
    rw [Subgroup.coe_mul, map_mul, localAt_embS_of_mem, ← hnu p, hxn p]
  have hR : ∀ β, R β ((g * embS SQ (yy i) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) = R β (g : AdelicGL2 (𝓞 ℚ) ℚ) :=
    fun β => apply_mul_embS_of_rightInvariant (R β) (fun p x g => _hRinv β p x g) _ _

  have hslot : ∀ (p : ↥SQ) (β : Fin m),
      w p β (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (globalPoints (𝓞 ℚ) ℚ w₀) *
          transposeInvN (Fin 2) (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) ((g * embS SQ (yy i) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ))) =
        psiLocal ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (-(x p)) *
          w p β (w₀At w₀ (p : HeightOneSpectrum (𝓞 ℚ)) * transposeInvN (Fin 2) (yy i p)) := by
    intro p β
    rw [hloc, mul_assoc, transposeInvN_mul, ← mul_assoc, show localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (globalPoints (𝓞 ℚ) ℚ w₀) =
      w₀At w₀ (p : HeightOneSpectrum (𝓞 ℚ)) from rfl, weyl2_mul_transposeInvN_unipotent _ (coe_w₀At w₀ hw₀ _), mul_assoc, _hwlaw,
      hU1 p (u p) (hu p)]

  have hgl3 : ∀ p : ↥SQ, F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ))
      (longWeyl3 * transposeInv3 (iotaGL (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) ((g * embS SQ (yy i) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ))) *
        kkAt yy k₀ i p) =
      psiV (p : HeightOneSpectrum (𝓞 ℚ)) (x p) * F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * k₀ p) := by
    intro p
    rw [hloc, kkAt, map_mul, map_mul, transposeInv3_mul, transposeInv3_mul]
    rw [show longWeyl3 * (transposeInv3 (iotaGL (unipotent (x p))) * transposeInv3 (iotaGL (u p)) * transposeInv3 (iotaGL (yy i p))) *
        ((transposeInv3 (iotaGL (yy i p)))⁻¹ * k₀ p) =
        (longWeyl3 * transposeInv3 (iotaGL (unipotent (x p)))) * (transposeInv3 (iotaGL (u p)) *
          (transposeInv3 (iotaGL (yy i p)) * (transposeInv3 (iotaGL (yy i p)))⁻¹) * k₀ p) by group,
      mul_inv_cancel, mul_one, longWeyl3_mul_transposeInv3_iotaGL_unipotent, mul_assoc, F.whittakerLoc_law, zero_add,
      psiLoc_eq_of_inv_eq_psiQ hψQ, neg_neg, ← mul_assoc, hU2 p (u p) (hu p)]

  have hphase : ∀ p : ↥SQ, psiLocal ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (-(x p)) * psiV (p : HeightOneSpectrum (𝓞 ℚ)) (x p) = 1 := by
    intro p
    rw [psiLocal_rat_eq_psiV, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

  have hmod : ∀ p : ↥SQ,
      ((modulus ((Matrix.GeneralLinearGroup.det (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) ((g * embS SQ (yy i) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) :
          ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ) =
      ((modulus ((Matrix.GeneralLinearGroup.det (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)) :
          ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ) *
        ((modulus ((Matrix.GeneralLinearGroup.det (yy i p) : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) :
          (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ) := by
    intro p
    rw [Subgroup.coe_mul, map_mul, localAt_embS_of_mem, map_mul, Units.val_mul, modulus_mul]
    push_cast
    ring

  rw [hexp, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [Finset.prod_congr rfl fun p _ => show _ = _ from by rw [hmod p, hslot p β], Finset.prod_congr rfl fun p _ => hgl3 p, hR]
  simp only [Finset.prod_mul_distrib, slotMat]
  have hph' : (∏ p : ↥SQ, psiLocal ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (-(x p))) * ∏ p : ↥SQ, psiV (p : HeightOneSpectrum (𝓞 ℚ)) (x p) = 1 := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_eq_one fun p _ => hphase p
  linear_combination (∏ p : ↥SQ, ((modulus ((Matrix.GeneralLinearGroup.det (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)) :
          ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ)) *
      (∏ p : ↥SQ, ((modulus ((Matrix.GeneralLinearGroup.det (yy i p) : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) :
          (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ)) *
      (∏ p : ↥SQ, w p β (w₀At w₀ (p : HeightOneSpectrum (𝓞 ℚ)) * transposeInvN (Fin 2) (yy i p))) * R β (g : AdelicGL2 (𝓞 ℚ) ℚ) *
      (∏ p : ↥SQ, F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * k₀ p)) * hph'

end Isolation

end GL2Side

section Remainders

variable {SQ : Finset (HeightOneSpectrum (𝓞 ℚ))} {m : ℕ}
  {w : ∀ p : ↥SQ, Fin m → GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) → ℂ}
  {Wrem : Fin m → AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
  {Wf Wfd : finiteAdelicGL2Subgroup ℚ → ℂ}
  {w₀ : GL (Fin 2) ℚ}
  {K : Type} [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
  {pins : CarrierPins ℚ} {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
  (F : CubicInductionForm K pins ψ μ) (hψQ : ψ⁻¹ = psiQ)
  (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) ℚ) = !![0, 1; 1, 0])
  (hμf : finiteAdelicGL2Subgroup ℚ)
  (R : Fin m → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
  (_hRinv : ∀ (α : Fin m) (p : ↥SQ) (x : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      R α (g * placeEmbed ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x) = R α g)
  (_hRexp : ∀ g : finiteAdelicGL2Subgroup ℚ, Wfd (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf) =
      ∑ α : Fin m, (∏ p : ↥SQ,
        ((modulus ((Matrix.GeneralLinearGroup.det (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)) :
            ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ) *
          w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (globalPoints (𝓞 ℚ) ℚ w₀) *
            transposeInvN (Fin 2) (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)))) * R α (g : AdelicGL2 (𝓞 ℚ) ℚ))
  (_hwlaw : ∀ (p : ↥SQ) (α : Fin m) (x : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) (g : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)),
      w p α (unipotent x * g) = psiLocal ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x * w p α g)
  (yy : Fin m → LocProd SQ) (k₀ : ∀ p : ↥SQ, LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)))
  (U : ∀ p : ↥SQ, Subgroup (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)))
  (hU1 : ∀ (p : ↥SQ), ∀ u ∈ U p, ∀ (β : Fin m) (i : Fin m),
      w p β (w₀At w₀ (p : HeightOneSpectrum (𝓞 ℚ)) * transposeInvN (Fin 2) (u * yy i p)) =
        w p β (w₀At w₀ (p : HeightOneSpectrum (𝓞 ℚ)) * transposeInvN (Fin 2) (yy i p)))
  (hU2 : ∀ (p : ↥SQ), ∀ u ∈ U p,
      F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * transposeInv3 (iotaGL u) * k₀ p) =
        F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * k₀ p))
  (hc₀ : ∀ p : ↥SQ, F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * k₀ p) ≠ 0)
  (hM : (Matrix.of fun i j : Fin m => slotMat SQ m w w₀ (yy i) j).det ≠ 0)

def modY (i : Fin m) : ℂ :=
  ∏ p : ↥SQ, ((modulus ((Matrix.GeneralLinearGroup.det (yy i p) : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) :
    (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ)

omit [NumberField K] in
theorem modY_ne_zero (i : Fin m) : modY yy i ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun p _ => ?_
  exact_mod_cast (modulus_pos (Units.ne_zero _)).ne'

include hψQ hw₀ _hRinv _hRexp _hwlaw hU1 hU2 hc₀

theorem sum_slotMat_mul_R (g : finiteAdelicGL2Subgroup ℚ) (i : Fin m) :
    ∑ β : Fin m, slotMat SQ m w w₀ (yy i) β * R β (g : AdelicGL2 (𝓞 ℚ) ℚ) =
      (modY yy i)⁻¹ * Wfd ((awayPart SQ g * embS SQ (yy i)) * hμf) := by
  have hg : ∀ p : ↥SQ, ∃ n ∈ (unipotentGL2Hom (R := (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)).range, ∃ u ∈ U p,
      n * u = localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (awayPart SQ g : AdelicGL2 (𝓞 ℚ) ℚ) :=
    fun p => ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by rw [one_mul, localAt_awayPart_of_mem]⟩
  have hiso := isolation_identity F hψQ hw₀ hμf R _hRinv _hRexp _hwlaw yy k₀ U hU1 hU2 (awayPart SQ g) hg i
  have hgl3 : ∀ p : ↥SQ, F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ))
      (longWeyl3 * transposeInv3 (iotaGL (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ))
        ((awayPart SQ g * embS SQ (yy i) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ))) * kkAt yy k₀ i p) =
      F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * k₀ p) := by
    intro p
    rw [Subgroup.coe_mul, map_mul, localAt_awayPart_of_mem, one_mul, localAt_embS_of_mem, kkAt, mul_assoc,
      mul_inv_cancel_left]
  have hmod : ∀ p : ↥SQ, ((modulus ((Matrix.GeneralLinearGroup.det (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ))
      (awayPart SQ g : AdelicGL2 (𝓞 ℚ) ℚ)) : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) :
        (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ) = 1 := by
    intro p; rw [localAt_awayPart_of_mem, map_one, Units.val_one, modulus_one]; norm_cast
  have hR : ∀ β, R β (awayPart SQ g : AdelicGL2 (𝓞 ℚ) ℚ) = R β (g : AdelicGL2 (𝓞 ℚ) ℚ) :=
    fun β => apply_awayPart (R β) (fun p x g => _hRinv β p x g) g
  have e1 : (∏ p : ↥SQ, F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * k₀ p) *
      ((modulus ((Matrix.GeneralLinearGroup.det (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ))
        (awayPart SQ g : AdelicGL2 (𝓞 ℚ) ℚ)) : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) :
          (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ) *
      ((modulus ((Matrix.GeneralLinearGroup.det (yy i p) : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) :
        (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ)) =
      (∏ p : ↥SQ, F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * k₀ p)) * modY yy i := by
    rw [modY, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p _ => by rw [hmod p, mul_one]
  have e2 : ∑ β : Fin m, slotMat SQ m w w₀ (yy i) β * R β (awayPart SQ g : AdelicGL2 (𝓞 ℚ) ℚ) =
      ∑ β : Fin m, slotMat SQ m w w₀ (yy i) β * R β (g : AdelicGL2 (𝓞 ℚ) ℚ) :=
    Finset.sum_congr rfl fun β _ => by rw [hR β]
  rw [Finset.prod_congr rfl fun p _ => hgl3 p, e1, e2] at hiso
  have hc : (∏ p : ↥SQ, F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * k₀ p)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun p _ => hc₀ p
  have hy := modY_ne_zero yy i

  have h2 : Wfd ((awayPart SQ g * embS SQ (yy i)) * hμf) =
      modY yy i * ∑ β : Fin m, slotMat SQ m w w₀ (yy i) β * R β (g : AdelicGL2 (𝓞 ℚ) ℚ) := by
    have := hiso
    apply mul_right_cancel₀ hc
    rw [this]; ring
  rw [h2, ← mul_assoc, inv_mul_cancel₀ hy, one_mul]

include hM

theorem R_eq_sum (α : Fin m) (g : finiteAdelicGL2Subgroup ℚ) :
    R α (g : AdelicGL2 (𝓞 ℚ) ℚ) = ∑ i : Fin m, (Matrix.of fun i j : Fin m => slotMat SQ m w w₀ (yy i) j)⁻¹ α i *
      ((modY yy i)⁻¹ * Wfd ((awayPart SQ g * embS SQ (yy i)) * hμf)) := by
  classical
  set M : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun i j : Fin m => slotMat SQ m w w₀ (yy i) j with hMdef
  have hinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.2 hM)
  have key : ∀ β : Fin m, ∑ i : Fin m, M⁻¹ α i * M i β = if α = β then 1 else 0 := by
    intro β
    have := congrFun (congrFun hinv α) β
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    exact this
  calc R α (g : AdelicGL2 (𝓞 ℚ) ℚ) = ∑ β : Fin m, (if α = β then 1 else 0) * R β (g : AdelicGL2 (𝓞 ℚ) ℚ) := by
        rw [Finset.sum_eq_single α]
        · simp
        · intro β _ hβ; simp [Ne.symm hβ]
        · intro h; exact absurd (Finset.mem_univ α) h
    _ = ∑ β : Fin m, (∑ i : Fin m, M⁻¹ α i * M i β) * R β (g : AdelicGL2 (𝓞 ℚ) ℚ) := by simp only [key]
    _ = ∑ i : Fin m, M⁻¹ α i * ∑ β : Fin m, M i β * R β (g : AdelicGL2 (𝓞 ℚ) ℚ) := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun β _ => by ring
    _ = _ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have : ∑ β : Fin m, M i β * R β (g : AdelicGL2 (𝓞 ℚ) ℚ) = ∑ β : Fin m, slotMat SQ m w w₀ (yy i) β * R β (g : AdelicGL2 (𝓞 ℚ) ℚ) := by
          simp only [hMdef, Matrix.of_apply]
        rw [this, sum_slotMat_mul_R F hψQ hw₀ hμf R _hRinv _hRexp _hwlaw yy k₀ U hU1 hU2 hc₀ g i]

theorem measurable_R
    (_hsplit : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      Wf (RSCarrier.finFactor g) = ∑ α : Fin m, (∏ p : ↥SQ, w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) g)) * Wrem α g)
    (hWfd : ∀ (gf : finiteAdelicGL2Subgroup ℚ), Wfd gf =
      ((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (gf : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) *
        Wf (RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ w₀ * transposeInvN (Fin 2) (gf : AdelicGL2 (𝓞 ℚ) ℚ))))
    (_hwmeas : ∀ (p : ↥SQ) (α : Fin m), Measurable (fun g : finiteAdelicGL2Subgroup ℚ =>
      w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ))))
    (_hWmeas : ∀ α : Fin m, Measurable (fun g : finiteAdelicGL2Subgroup ℚ => Wrem α (g : AdelicGL2 (𝓞 ℚ) ℚ)))
    (α : Fin m) : Measurable fun g : finiteAdelicGL2Subgroup ℚ => R α (g : AdelicGL2 (𝓞 ℚ) ℚ) := by
  have heq : (fun g : finiteAdelicGL2Subgroup ℚ => R α (g : AdelicGL2 (𝓞 ℚ) ℚ)) = fun g =>
      ∑ i : Fin m, (Matrix.of fun i j : Fin m => slotMat SQ m w w₀ (yy i) j)⁻¹ α i *
        ((modY yy i)⁻¹ * Wfd ((awayPart SQ g * embS SQ (yy i)) * hμf)) :=
    funext fun g => R_eq_sum F hψQ hw₀ hμf R _hRinv _hRexp _hwlaw yy k₀ U hU1 hU2 hc₀ hM α g
  rw [heq]
  refine Finset.measurable_sum _ fun i _ => Measurable.const_mul (Measurable.const_mul ?_ _) _
  exact (measurable_Wfd _hsplit hWfd _hwmeas _hWmeas).comp
    (((continuous_awayPart SQ).mul continuous_const).mul continuous_const).measurable

theorem norm_R_unipotent_mul
    (_hsplit : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      Wf (RSCarrier.finFactor g) = ∑ α : Fin m, (∏ p : ↥SQ, w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) g)) * Wrem α g)
    (hWfd : ∀ (gf : finiteAdelicGL2Subgroup ℚ), Wfd gf =
      ((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (gf : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) *
        Wf (RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ w₀ * transposeInvN (Fin 2) (gf : AdelicGL2 (𝓞 ℚ) ℚ))))
    (_hWinv : ∀ (α : Fin m) (p : ↥SQ) (x : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      Wrem α (g * placeEmbed ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x) = Wrem α g)
    (_hWlaw : ∀ (α : Fin m) (t : AdeleRing (𝓞 ℚ) ℚ), t.1 = 0 →
      (∀ p : ↥SQ, localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (unipotentGL2 t) = 1) →
      ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, Wrem α (unipotentGL2 t * g) = psiQ t * Wrem α g)
    (α : Fin m) {n : finiteAdelicGL2Subgroup ℚ} (hn : (n : AdelicGL2 (𝓞 ℚ) ℚ) ∈ adelicUnipotent ℚ) (g : finiteAdelicGL2Subgroup ℚ) :
    ‖R α ((n * g : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)‖ = ‖R α (g : AdelicGL2 (𝓞 ℚ) ℚ)‖ := by
  obtain ⟨t, ht⟩ := awayPart_unipotent SQ hn
  have hmem : unipotentGL2 t ∈ finiteAdelicGL2Subgroup ℚ := ht ▸ (n * (embS SQ (projS SQ n))⁻¹).2
  obtain ⟨θ, hθ, hph⟩ := exists_phase_Wfd _hsplit _hwlaw _hWinv _hWlaw hw₀ hWfd t hmem
  have hnt : (n * (embS SQ (projS SQ n))⁻¹ : finiteAdelicGL2Subgroup ℚ) = ⟨unipotentGL2 t, hmem⟩ := Subtype.ext ht
  have key : ∀ i : Fin m, Wfd ((awayPart SQ (n * g) * embS SQ (yy i)) * hμf) =
      θ * Wfd ((awayPart SQ g * embS SQ (yy i)) * hμf) := by
    intro i
    rw [awayPart_mul, hnt, mul_assoc, mul_assoc, ← mul_assoc (awayPart SQ g), hph]
  rw [R_eq_sum F hψQ hw₀ hμf R _hRinv _hRexp _hwlaw yy k₀ U hU1 hU2 hc₀ hM α,
    R_eq_sum F hψQ hw₀ hμf R _hRinv _hRexp _hwlaw yy k₀ U hU1 hU2 hc₀ hM α]
  simp only [key]
  have : ∑ i : Fin m, (Matrix.of fun i j : Fin m => slotMat SQ m w w₀ (yy i) j)⁻¹ α i *
      ((modY yy i)⁻¹ * (θ * Wfd ((awayPart SQ g * embS SQ (yy i)) * hμf))) =
      θ * ∑ i : Fin m, (Matrix.of fun i j : Fin m => slotMat SQ m w w₀ (yy i) j)⁻¹ α i *
      ((modY yy i)⁻¹ * Wfd ((awayPart SQ g * embS SQ (yy i)) * hμf)) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
  rw [this, norm_mul, hθ, one_mul]

end Remainders

theorem coe_finUnipotent_mem (n : (RSCarrier.finUnipotent : Subgroup ↥(finiteAdelicGL2Subgroup ℚ))) :
    ((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) ∈ adelicUnipotent ℚ := n.2

end KcRsCellRem
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_measurable_remainder_and_dualFactor_translate_mul_prod_eq_of_pureTensor_expansion.KcRsCellRem"

open KcRsCellRem in
open LanglandsTunnell.TateLocal UnramifiedWhittaker in
theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (F : CubicInductionForm K pins ψ μ)
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hμf : finiteAdelicGL2Subgroup ℚ)
    (m : ℕ) (w : ∀ p : ↥SQ, Fin m → GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) → ℂ)
    (_hwlaw : ∀ (p : ↥SQ) (α : Fin m) (x : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) (g : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)),
      w p α (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x * w p α g)
    (Wrem : Fin m → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (_hWinv : ∀ (α : Fin m) (p : ↥SQ) (x : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      Wrem α (g * UnramifiedWhittaker.placeEmbed ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x) = Wrem α g)
    (_hWlaw : ∀ (α : Fin m) (t : AdeleRing (𝓞 ℚ) ℚ), t.1 = 0 →
      (∀ p : ↥SQ, localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (unipotentGL2 t) = 1) →
      ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, Wrem α (unipotentGL2 t * g) = NumberField.StandardAddChar.psiQ t * Wrem α g)
    (_hwmeas : ∀ (p : ↥SQ) (α : Fin m), Measurable (fun g : finiteAdelicGL2Subgroup ℚ =>
      w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ))))
    (_hWmeas : ∀ α : Fin m, Measurable (fun g : finiteAdelicGL2Subgroup ℚ => Wrem α (g : AdelicGL2 (𝓞 ℚ) ℚ)))
    (Wf Wfd : finiteAdelicGL2Subgroup ℚ → ℂ)
    (w₀ : GL (Fin 2) ℚ) (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) ℚ) = !![0, 1; 1, 0])
    (hWfd : ∀ gf : finiteAdelicGL2Subgroup ℚ, Wfd gf =
      ((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (gf : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) *
        Wf (RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ w₀ * transposeInvN (Fin 2) (gf : AdelicGL2 (𝓞 ℚ) ℚ))))
    (_hsplit : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      Wf (RSCarrier.finFactor g) = ∑ α : Fin m, (∏ p : ↥SQ, w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) g)) * Wrem α g)
    (R : Fin m → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (_hRinv : ∀ (α : Fin m) (p : ↥SQ) (x : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      R α (g * UnramifiedWhittaker.placeEmbed ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x) = R α g)
    (_hRexp : ∀ g : finiteAdelicGL2Subgroup ℚ, Wfd (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf) =
      ∑ α : Fin m, (∏ p : ↥SQ,
        ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ) *
          w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (globalPoints (𝓞 ℚ) ℚ w₀) *
            transposeInvN (Fin 2) (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)))) * R α (g : AdelicGL2 (𝓞 ℚ) ℚ))
    (yy : Fin m → ∀ p : ↥SQ, GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (k₀ : ∀ p : ↥SQ, LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)))
    (U : ∀ p : ↥SQ, Subgroup (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)))
    (hU1 : (∀ (p : ↥SQ), ∀ u ∈ U p, ∀ (β : Fin m) (i : Fin m),
        w p β (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (globalPoints (𝓞 ℚ) ℚ w₀) * transposeInvN (Fin 2) (u * yy i p)) =
          w p β (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (globalPoints (𝓞 ℚ) ℚ w₀) * transposeInvN (Fin 2) (yy i p))))
    (hU2 : (∀ (p : ↥SQ), ∀ u ∈ U p,
        F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * transposeInv3 (iotaGL u) * k₀ p) =
          F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * k₀ p)))
    (hc₀ : (∀ p : ↥SQ, F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * k₀ p) ≠ 0))
    (hM : ((Matrix.of fun i j : Fin m => ∏ p : ↥SQ,
        w p j (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (globalPoints (𝓞 ℚ) ℚ w₀) * transposeInvN (Fin 2) (yy i p))).det ≠ 0)) :
    Measurable Wfd ∧
    (∀ n : ↥RSCarrier.finUnipotent, ∃ θ : ℂ, ‖θ‖ = 1 ∧ ∀ g : finiteAdelicGL2Subgroup ℚ,
      Wfd ((n : finiteAdelicGL2Subgroup ℚ) * g) = θ * Wfd g) ∧
    (∀ α : Fin m, Measurable fun g : finiteAdelicGL2Subgroup ℚ => R α (g : AdelicGL2 (𝓞 ℚ) ℚ)) ∧
    (∀ (α : Fin m) (n : ↥RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
      ‖R α (((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)‖ =
        ‖R α (g : AdelicGL2 (𝓞 ℚ) ℚ)‖) ∧
    (∀ (g yhat : finiteAdelicGL2Subgroup ℚ) (i : Fin m),
      (∀ p : ↥SQ, ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)).range,
        ∃ u ∈ U p, n * u = localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)) →
      (∀ p : ↥SQ, localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (yhat : AdelicGL2 (𝓞 ℚ) ℚ) = yy i p) →
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → localAt ℚ v (yhat : AdelicGL2 (𝓞 ℚ) ℚ) = 1) →
      Wfd (g * yhat * hμf) *
          (∏ p : ↥SQ, F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ))
            (longWeyl3 * transposeInv3 (iotaGL (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) ((g * yhat : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ))) *
              ((transposeInv3 (iotaGL (yy i p)))⁻¹ * k₀ p))) =
        (∏ p : ↥SQ, F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * k₀ p) *
            ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ) *
            ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (yy i p) : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ)) *
          ∑ β : Fin m, (∏ p : ↥SQ, w p β (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (globalPoints (𝓞 ℚ) ℚ w₀) *
            transposeInvN (Fin 2) (yy i p))) * R β (g : AdelicGL2 (𝓞 ℚ) ℚ)) := by
  refine ⟨measurable_Wfd _hsplit hWfd _hwmeas _hWmeas, fun n => ?_,
    fun α => measurable_R F hψQ hw₀ hμf R _hRinv _hRexp _hwlaw yy k₀ U hU1 hU2 hc₀ hM _hsplit hWfd _hwmeas _hWmeas α,
    fun α n g => norm_R_unipotent_mul F hψQ hw₀ hμf R _hRinv _hRexp _hwlaw yy k₀ U hU1 hU2 hc₀ hM _hsplit hWfd _hWinv _hWlaw α
      (coe_finUnipotent_mem n) g, fun g yhat i hg hy1 hy2 => ?_⟩
  · obtain ⟨t, ht⟩ := eq_unipotentGL2_of_mem_adelicUnipotent (coe_finUnipotent_mem n)
    have hmem : unipotentGL2 t ∈ finiteAdelicGL2Subgroup ℚ := ht ▸ (n : finiteAdelicGL2Subgroup ℚ).2
    obtain ⟨θ, hθ, h⟩ := exists_phase_Wfd _hsplit _hwlaw _hWinv _hWlaw hw₀ hWfd t hmem
    refine ⟨θ, hθ, fun g => ?_⟩
    have hn : (n : finiteAdelicGL2Subgroup ℚ) = ⟨unipotentGL2 t, hmem⟩ := Subtype.ext ht
    rw [hn]
    exact h g
  · have hy : yhat = embS SQ (yy i) := by
      refine Subtype.ext (ext_of_glArch_localAt ?_ fun v => ?_)
      · rw [(mem_finiteAdelicGL2Subgroup_iff ℚ _).1 yhat.2, glArch_embS]
      · by_cases hv : v ∈ SQ
        · rw [hy1 ⟨v, hv⟩, localAt_embS_of_mem SQ (yy i) ⟨v, hv⟩]
        · rw [hy2 v hv, localAt_embS_of_not_mem SQ (yy i) hv]
    rw [hy]
    exact isolation_identity F hψQ hw₀ hμf R _hRinv _hRexp _hwlaw yy k₀ U hU1 hU2 g hg i

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_measurable_remainder_and_dualFactor_translate_mul_prod_eq_of_pureTensor_expansion.KcRsCellRem"

end S_LanglandsTunnell_RankinSelberg_measurable_remainder_and_dualFactor_translate_mul_prod_eq_of_pureTensor_expansion
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_measurable_remainder_and_dualFactor_translate_mul_prod_eq_of_pureTensor_expansion (solution)
