-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.finite_mulSupport_and_continuous_and_exists_phase_finprod_dualWhittakerFn3_away
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/1165eaf2-3ee9-5408-8dec-7b5caffd47ee

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_finite_mulSupport_and_continuous_and_exists_phase_finprod_dualWhittakerFn3_away

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

namespace KcRsCellEuler

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

section LocalCompact3

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem isOpen_localMaximalCompact3 : IsOpen (localMaximalCompact3 (𝓞 ℚ) ℚ v : Set (LocalGL3 v)) := by
  have hO : IsOpen {y : v.adicCompletion ℚ | Valued.v y ≤ 1} := by
    have : {y : v.adicCompletion ℚ | Valued.v y ≤ 1} = (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
      ext y; simp [HeightOneSpectrum.mem_adicCompletionIntegers]
    rw [this]; exact Valued.isOpen_valuationSubring _
  have h1 : ∀ i j : Fin 3, IsOpen {k : LocalGL3 v | Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ 1} :=
    fun i j => hO.preimage (Units.continuous_val.matrix_elem i j)
  have h2 : ∀ i j : Fin 3, IsOpen {k : LocalGL3 v |
      Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ 1} :=
    fun i j => hO.preimage (Units.continuous_coe_inv.matrix_elem i j)
  have heq : (localMaximalCompact3 (𝓞 ℚ) ℚ v : Set (LocalGL3 v)) =
      (⋂ i, ⋂ j, {k : LocalGL3 v | Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ 1}) ∩
        ⋂ i, ⋂ j, {k : LocalGL3 v | Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ 1} := by
    ext k
    simp only [SetLike.mem_coe, mem_localMaximalCompact3_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [heq]
  exact (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => h1 i j).inter
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => h2 i j)

theorem iotaGL_mem_localMaximalCompact3 {g : GL (Fin 2) (v.adicCompletion ℚ)} (hg : g ∈ localIntegralSet ℚ v) :
    iotaGL g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  rw [mem_localIntegralSet] at hg
  have aux : ∀ (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)), (∀ i j, M i j ∈ v.adicCompletionIntegers ℚ) →
      ∀ i j, Valued.v (embedMat2 M i j) ≤ 1 := by
    intro M hM i j
    have hM' : ∀ i j, Valued.v (M i j) ≤ 1 := fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hM i j)
    fin_cases i <;> fin_cases j <;> simp [embedMat2, hM']
  refine ⟨fun i j => aux _ hg.1 i j, fun i j => ?_⟩
  rw [← map_inv]
  exact aux _ hg.2 i j

theorem transposeInv3_mem_localMaximalCompact3 {k : LocalGL3 v} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    transposeInv3 k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · show Valued.v ((((k⁻¹ : LocalGL3 v)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))ᵀ i j) ≤ 1
    rw [Matrix.transpose_apply]; exact hk.2 j i
  · show Valued.v (((k : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))ᵀ i j) ≤ 1
    rw [Matrix.transpose_apply]; exact hk.1 j i

theorem longWeyl3_mem_localMaximalCompact3 : (longWeyl3 : LocalGL3 v) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  have h : ∀ i j : Fin 3, Valued.v ((!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ 1 := by
    intro i j; fin_cases i <;> fin_cases j <;> simp
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · exact h i j
  · have : ((longWeyl3 : LocalGL3 v)⁻¹ : LocalGL3 v) = longWeyl3 := inv_eq_of_mul_eq_one_right (Units.ext (by
      show (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) * !![0, 0, 1; 0, 1, 0; 1, 0, 0] = 1
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]))
    rw [this]; exact h i j

end LocalCompact3

section BadPlaces

variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

variable {K}

variable {pins : CarrierPins ℚ} {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
  (F : CubicInductionForm K pins ψ μ)

theorem exists_open_stabiliser
    (hBad : ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
      (∀ v ∈ T, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v, F.whittakerLoc v (g * k) = F.whittakerLoc v g) ∧
      (∀ v ∈ T, IsBadPlace K μ v → ∀ W ∈ gl3CyclicSubspace (F.whittakerLoc v), W ≠ 0 →
        F.whittakerLoc v ∈ gl3CyclicSubspace W))
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, F.whittakerLoc v (g * k) = F.whittakerLoc v g := by
  by_cases hb : IsBadPlace K μ v
  · exact (hBad {v}).1 v (Finset.mem_singleton_self v) hb
  · exact ⟨localMaximalCompact3 (𝓞 ℚ) ℚ v, isOpen_localMaximalCompact3 v, fun k hk g => (F.spherical v hb).1 g k hk⟩

theorem isLocallyConstant_whittakerLoc
    (hBad : ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
      (∀ v ∈ T, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v, F.whittakerLoc v (g * k) = F.whittakerLoc v g) ∧
      (∀ v ∈ T, IsBadPlace K μ v → ∀ W ∈ gl3CyclicSubspace (F.whittakerLoc v), W ≠ 0 →
        F.whittakerLoc v ∈ gl3CyclicSubspace W))
    (v : HeightOneSpectrum (𝓞 ℚ)) : IsLocallyConstant (F.whittakerLoc v) := by
  obtain ⟨Uv, hUo, hU⟩ := exists_open_stabiliser F hBad v
  exact isLocallyConstant_of_rightInvariant Uv hUo _ hU

theorem dualWhittakerFn3_iotaGL_eq_one_of_good
    (hF0 : ∀ v, ¬ IsRamifiedIn K v → addCharLevel (psiLoc ψ v) = 0 → F.whittakerLoc v 1 = 1)
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), addCharLevel (psiLoc ψ v) = 0)
    {v : HeightOneSpectrum (𝓞 ℚ)} (hgood : ¬ IsBadPlace K μ v)
    {g : GL (Fin 2) (v.adicCompletion ℚ)} (hg : g ∈ localIntegralSet ℚ v) :
    dualWhittakerFn3 (F.whittakerLoc v) (iotaGL g) = 1 := by
  have hnr : ¬ IsRamifiedIn K v := fun h => hgood (Or.inl h)
  have h1 : F.whittakerLoc v 1 = 1 := hF0 v hnr (hlev v)
  have hsph := (F.spherical v hgood).1
  rw [dualWhittakerFn3_apply, ← one_mul (longWeyl3 * transposeInv3 (iotaGL g)), hsph, h1]
  exact Subgroup.mul_mem _ (longWeyl3_mem_localMaximalCompact3 v)
    (transposeInv3_mem_localMaximalCompact3 v (iotaGL_mem_localMaximalCompact3 v hg))

end BadPlaces

section Integrality

theorem finite_setOf_not_mem_localIntegralSet (Y : AdelicGL2 (𝓞 ℚ) ℚ) :
    {v : HeightOneSpectrum (𝓞 ℚ) | localAt ℚ v Y ∉ localIntegralSet ℚ v}.Finite := by
  have hent : ∀ (Z : AdelicGL2 (𝓞 ℚ) ℚ) (i j : Fin 2),
      {v : HeightOneSpectrum (𝓞 ℚ) | ((Z : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 v ∉ v.adicCompletionIntegers ℚ}.Finite :=
    fun Z i j => Filter.eventually_cofinite.1 ((Z : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2.2
  refine (((Set.finite_iUnion fun i => Set.finite_iUnion fun j => hent Y i j)).union
    (Set.finite_iUnion fun i => Set.finite_iUnion fun j => hent Y⁻¹ i j)).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq, mem_localIntegralSet, not_and_or, not_forall] at hv
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq]
  rcases hv with ⟨i, j, h⟩ | ⟨i, j, h⟩
  · exact Or.inl ⟨i, j, h⟩
  · refine Or.inr ⟨i, j, ?_⟩
    rwa [← map_inv] at h

theorem isOpen_setOf_forall_mem_localIntegralSet :
    IsOpen {Y : AdelicGL2 (𝓞 ℚ) ℚ | ∀ v, localAt ℚ v Y ∈ localIntegralSet ℚ v} := by
  have hc : ∀ i j : Fin 2, Continuous fun Y : AdelicGL2 (𝓞 ℚ) ℚ => ((Y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 :=
    fun i j => continuous_snd.comp (Units.continuous_val.matrix_elem i j)
  have hc' : ∀ i j : Fin 2, Continuous fun Y : AdelicGL2 (𝓞 ℚ) ℚ =>
      (((Y⁻¹ : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 :=
    fun i j => continuous_snd.comp (Units.continuous_coe_inv.matrix_elem i j)
  have heq : {Y : AdelicGL2 (𝓞 ℚ) ℚ | ∀ v, localAt ℚ v Y ∈ localIntegralSet ℚ v} =
      (⋂ i, ⋂ j, (fun Y : AdelicGL2 (𝓞 ℚ) ℚ => ((Y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2) ⁻¹'
        {y | ∀ v : HeightOneSpectrum (𝓞 ℚ), y v ∈ v.adicCompletionIntegers ℚ}) ∩
      ⋂ i, ⋂ j, (fun Y : AdelicGL2 (𝓞 ℚ) ℚ => (((Y⁻¹ : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2) ⁻¹'
        {y | ∀ v : HeightOneSpectrum (𝓞 ℚ), y v ∈ v.adicCompletionIntegers ℚ} := by
    ext Y
    simp only [Set.mem_setOf_eq, mem_localIntegralSet, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    constructor
    · intro h
      exact ⟨fun i j v => (h v).1 i j, fun i j v => (h v).2 i j⟩
    · intro h v
      exact ⟨fun i j => h.1 i j v, fun i j => h.2 i j v⟩
  rw [heq]
  exact (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_forall_mem_integers.preimage (hc i j)).inter
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_forall_mem_integers.preimage (hc' i j))

end Integrality

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

variable (hF0 : ∀ v, ¬ IsRamifiedIn K v → addCharLevel (psiLoc ψ v) = 0 → F.whittakerLoc v 1 = 1)
  (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), addCharLevel (psiLoc ψ v) = 0)
  {S' : Finset (HeightOneSpectrum (𝓞 ℚ))} (hgood : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S' → ¬ IsBadPlace K μ p)
include hF0 hlev hgood

theorem mulSupport_eFam_subset (Y : AdelicGL2 (𝓞 ℚ) ℚ) :
    Function.mulSupport (eFam F SQ Y) ⊆ (S' : Set (HeightOneSpectrum (𝓞 ℚ))) ∪ {v | localAt ℚ v Y ∉ localIntegralSet ℚ v} := by
  intro v hv
  by_contra h
  simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at h
  apply hv
  by_cases hvS : v ∈ SQ
  · exact eFam_of_mem Y hvS
  · rw [eFam_of_not_mem Y hvS]
    exact dualWhittakerFn3_iotaGL_eq_one_of_good F hF0 hlev (hgood v h.1) h.2

theorem finite_mulSupport_eFam (Y : AdelicGL2 (𝓞 ℚ) ℚ) : (Function.mulSupport (eFam F SQ Y)).Finite :=
  ((S'.finite_toSet).union (finite_setOf_not_mem_localIntegralSet Y)).subset (mulSupport_eFam_subset hF0 hlev hgood Y)

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

open scoped Classical in

theorem eFam_unipotentGL2_mul (hψQ : ψ⁻¹ = psiQ) (t : AdeleRing (𝓞 ℚ) ℚ) (Y : AdelicGL2 (𝓞 ℚ) ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    eFam F SQ (unipotentGL2 t * Y) v =
      (if v ∈ SQ then (1 : ℂ) else psiV v (t.2 v)) * eFam F SQ Y v := by
  by_cases hv : v ∈ SQ
  · simp [eFam_of_mem _ hv, hv]
  · rw [eFam_of_not_mem _ hv, eFam_of_not_mem _ hv, if_neg hv, map_mul, localAt_unipotentGL2, ← unipotent_eq_unipotentGL2,
      map_mul, dualWhittakerFn3_apply, dualWhittakerFn3_apply, transposeInv3_mul, ← mul_assoc,
      longWeyl3_mul_transposeInv3_iotaGL_unipotent, mul_assoc, F.whittakerLoc_law v, zero_add,
      psiLoc_eq_of_inv_eq_psiQ hψQ, neg_neg]

section Phase

variable (hψQ : ψ⁻¹ = psiQ)
  (hF0 : ∀ v, ¬ IsRamifiedIn K v → addCharLevel (psiLoc ψ v) = 0 → F.whittakerLoc v 1 = 1)
  (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), addCharLevel (psiLoc ψ v) = 0)
  {S' : Finset (HeightOneSpectrum (𝓞 ℚ))} (hgood : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S' → ¬ IsBadPlace K μ p)
include hψQ hF0 hlev hgood

open scoped Classical in

theorem Efun_unipotentGL2_mul (t : AdeleRing (𝓞 ℚ) ℚ) (Y : AdelicGL2 (𝓞 ℚ) ℚ) :
    ∃ θ : ℂ, ‖θ‖ = 1 ∧ Efun F SQ (unipotentGL2 t * Y) = θ * Efun F SQ Y := by
  let ph : HeightOneSpectrum (𝓞 ℚ) → ℂ := fun v => if v ∈ SQ then (1 : ℂ) else psiV v (t.2 v)
  have hph : (Function.mulSupport ph).Finite := by
    refine (mulSupport_psiV_finite t.2).subset fun v hv => ?_
    simp only [Function.mem_mulSupport, ph] at hv ⊢
    by_cases h : v ∈ SQ
    · simp [h] at hv
    · simpa [h] using hv
  refine ⟨∏ᶠ v, ph v, ?_, ?_⟩
  · rw [finprod_eq_prod_of_mulSupport_subset _ (s := hph.toFinset) (by simp), norm_prod]
    refine Finset.prod_eq_one fun v _ => ?_
    by_cases h : v ∈ SQ
    · simp [ph, h]
    · simp only [ph, if_neg h]; exact norm_psiV v _
  · simp only [Efun]
    rw [show (fun v => eFam F SQ (unipotentGL2 t * Y) v) = fun v => ph v * eFam F SQ Y v from
      funext fun v => eFam_unipotentGL2_mul hψQ t Y v]
    exact finprod_mul_distrib hph (finite_mulSupport_eFam hF0 hlev hgood Y)

theorem norm_Efun_unipotentGL2_mul (t : AdeleRing (𝓞 ℚ) ℚ) (Y : AdelicGL2 (𝓞 ℚ) ℚ) :
    ‖Efun F SQ (unipotentGL2 t * Y)‖ = ‖Efun F SQ Y‖ := by
  obtain ⟨θ, hθ, h⟩ := Efun_unipotentGL2_mul hψQ hF0 hlev hgood (SQ := SQ) t Y
  rw [h, norm_mul, hθ, one_mul]

end Phase

section Continuity

variable (hBad : ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
      (∀ v ∈ T, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v, F.whittakerLoc v (g * k) = F.whittakerLoc v g) ∧
      (∀ v ∈ T, IsBadPlace K μ v → ∀ W ∈ gl3CyclicSubspace (F.whittakerLoc v), W ≠ 0 →
        F.whittakerLoc v ∈ gl3CyclicSubspace W))
  {S' : Finset (HeightOneSpectrum (𝓞 ℚ))} (hgood : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S' → ¬ IsBadPlace K μ p)
include hBad hgood

theorem continuous_Efun_coe : Continuous fun g : finiteAdelicGL2Subgroup ℚ => Efun F SQ (g : AdelicGL2 (𝓞 ℚ) ℚ) := by
  classical
  choose U hUo hU using exists_open_stabiliser F hBad
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun g₀ => ?_)
  let κ : finiteAdelicGL2Subgroup ℚ → AdelicGL2 (𝓞 ℚ) ℚ := fun g => (g₀ : AdelicGL2 (𝓞 ℚ) ℚ)⁻¹ * g
  have hκ : Continuous κ := continuous_const.mul continuous_subtype_val
  let N : Set (finiteAdelicGL2Subgroup ℚ) :=
    κ ⁻¹' {Y : AdelicGL2 (𝓞 ℚ) ℚ | ∀ v, localAt ℚ v Y ∈ localIntegralSet ℚ v} ∩
      ⋂ v ∈ S', (fun g => transposeInv3 (iotaGL (localAt ℚ v (κ g)))) ⁻¹' (U v : Set (LocalGL3 v))
  have hN : IsOpen N := by
    refine (isOpen_setOf_forall_mem_localIntegralSet.preimage hκ).inter (isOpen_biInter_finset fun v _ => ?_)
    exact (hUo v).preimage (continuous_transposeInv3.comp (continuous_iotaGL.comp ((continuous_localAt ℚ v).comp hκ)))
  have hg₀ : g₀ ∈ N := by
    refine ⟨?_, ?_⟩
    · show ∀ v, localAt ℚ v (κ g₀) ∈ localIntegralSet ℚ v
      intro v; simp only [κ, inv_mul_cancel, map_one]; exact one_mem_localIntegralSet ℚ v
    · simp only [Set.mem_iInter, Set.mem_preimage]
      intro v _
      simp only [κ, inv_mul_cancel, map_one, transposeInv3_one]
      exact (U v).one_mem
  refine ⟨N, hN, hg₀, fun g hg => ?_⟩
  have hgκ : (g : AdelicGL2 (𝓞 ℚ) ℚ) = (g₀ : AdelicGL2 (𝓞 ℚ) ℚ) * κ g := by simp only [κ, mul_inv_cancel_left]
  simp only [Efun]
  refine finprod_congr fun v => ?_
  by_cases hv : v ∈ SQ
  · rw [eFam_of_mem _ hv, eFam_of_mem _ hv]
  rw [eFam_of_not_mem _ hv, eFam_of_not_mem _ hv, hgκ, map_mul, map_mul, dualWhittakerFn3_apply, dualWhittakerFn3_apply,
    transposeInv3_mul, ← mul_assoc]
  by_cases hvS : v ∈ S'
  · have hmem : transposeInv3 (iotaGL (localAt ℚ v (κ g))) ∈ U v := by
      have := hg.2
      simp only [Set.mem_iInter, Set.mem_preimage] at this
      exact this v hvS
    exact hU v _ hmem _
  · have hint : localAt ℚ v (κ g) ∈ localIntegralSet ℚ v := hg.1 v
    exact (F.spherical v (hgood v hvS)).1 _ _
      (transposeInv3_mem_localMaximalCompact3 v (iotaGL_mem_localMaximalCompact3 v hint))

end Continuity

end EulerFamily

end KcRsCellEuler
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_finite_mulSupport_and_continuous_and_exists_phase_finprod_dualWhittakerFn3_away.KcRsCellEuler"

open KcRsCellEuler in
open LanglandsTunnell.TateLocal UnramifiedWhittaker in
open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (F : CubicInductionForm K pins ψ μ)
    (hF1 : ∀ v, ¬ IsRamifiedIn K v → LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 → F.whittakerLoc v 1 = 1)
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (hBad : ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
      (∀ v ∈ T, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v, F.whittakerLoc v (g * k) = F.whittakerLoc v g) ∧
      (∀ v ∈ T, IsBadPlace K μ v → ∀ W ∈ gl3CyclicSubspace (F.whittakerLoc v), W ≠ 0 →
        F.whittakerLoc v ∈ gl3CyclicSubspace W))
    (S' : Finset (HeightOneSpectrum (𝓞 ℚ))) (hgood : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S' → ¬ IsBadPlace K μ p)
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    (∀ v : HeightOneSpectrum (𝓞 ℚ), IsLocallyConstant (F.whittakerLoc v)) ∧
    (∀ Y : AdelicGL2 (𝓞 ℚ) ℚ, (Function.mulSupport fun v : HeightOneSpectrum (𝓞 ℚ) =>
      if v ∈ SQ then (1 : ℂ) else dualWhittakerFn3 (F.whittakerLoc v) (iotaGL (localAt ℚ v Y))).Finite) ∧
    (Continuous fun g : finiteAdelicGL2Subgroup ℚ => ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
      if v ∈ SQ then (1 : ℂ) else dualWhittakerFn3 (F.whittakerLoc v) (iotaGL (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ)))) ∧
    (∀ (t : AdeleRing (𝓞 ℚ) ℚ) (Y : AdelicGL2 (𝓞 ℚ) ℚ), ∃ θ : ℂ, ‖θ‖ = 1 ∧
      (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), if v ∈ SQ then (1 : ℂ) else
          dualWhittakerFn3 (F.whittakerLoc v) (iotaGL (localAt ℚ v (unipotentGL2 t * Y)))) =
        θ * ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), if v ∈ SQ then (1 : ℂ) else
          dualWhittakerFn3 (F.whittakerLoc v) (iotaGL (localAt ℚ v Y))) := by
  refine ⟨isLocallyConstant_whittakerLoc F hBad, fun Y => finite_mulSupport_eFam (F := F) (SQ := SQ) hF1 hlev hgood Y, ?_,
    fun t Y => Efun_unipotentGL2_mul (F := F) (SQ := SQ) hψQ hF1 hlev hgood t Y⟩
  exact continuous_Efun_coe (F := F) (SQ := SQ) hBad hgood

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_finite_mulSupport_and_continuous_and_exists_phase_finprod_dualWhittakerFn3_away.KcRsCellEuler"

end S_LanglandsTunnell_RankinSelberg_finite_mulSupport_and_continuous_and_exists_phase_finprod_dualWhittakerFn3_away
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_finite_mulSupport_and_continuous_and_exists_phase_finprod_dualWhittakerFn3_away (solution)
