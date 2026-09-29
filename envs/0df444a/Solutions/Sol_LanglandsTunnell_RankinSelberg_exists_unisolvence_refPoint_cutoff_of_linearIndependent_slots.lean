-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_unisolvence_refPoint_cutoff_of_linearIndependent_slots
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/d6f40a2a-b98e-5079-a78a-16a96f40b222

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
import Theorems.Thm_exists_det_of_apply_ne_zero_of_linearIndependent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_unisolvence_refPoint_cutoff_of_linearIndependent_slots

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

namespace KcRsCellChoice

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

end BadPlaces

section GL2Side

variable (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (m : ℕ)
  (w : ∀ p : ↥SQ, Fin m → GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) → ℂ)
  (Wrem : Fin m → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
  (par : InfinitePlace ℚ → ZMod 2)
  (Wf Wfd : (InfinitePlace ℚ → ZMod 2) → finiteAdelicGL2Subgroup ℚ → ℂ)
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

variable {SQ m w Wrem par Wf Wfd w₀}

end GL2Side

section Choices

variable {SQ : Finset (HeightOneSpectrum (𝓞 ℚ))} {m : ℕ}
  {w : ∀ p : ↥SQ, Fin m → GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) → ℂ}
  {w₀ : GL (Fin 2) ℚ}

def transposeInvN2Hom {A : Type*} [CommRing A] : GL (Fin 2) A →* GL (Fin 2) A where
  toFun := transposeInvN (Fin 2)
  map_one' := Units.ext (by rw [coe_transposeInvN, inv_one, Units.val_one, Matrix.transpose_one])
  map_mul' := transposeInvN_mul (Fin 2)

@[scoped simp] theorem transposeInvN2Hom_apply {A : Type*} [CommRing A] (g : GL (Fin 2) A) : transposeInvN2Hom g = transposeInvN (Fin 2) g := rfl

theorem exists_unisolvence
    (hind : LinearIndependent ℂ (fun α : Fin m => fun y : LocProd SQ => ∏ p : ↥SQ, w p α (y p))) :
    ∃ yy : Fin m → LocProd SQ, (Matrix.of fun i j : Fin m => slotMat SQ m w w₀ (yy i) j).det ≠ 0 := by
  classical
  let φ : LocProd SQ → LocProd SQ := fun y p => w₀At w₀ (p : HeightOneSpectrum (𝓞 ℚ)) * transposeInvN (Fin 2) (y p)
  have hφ : Function.Surjective φ := by
    intro z
    refine ⟨fun p => transposeInvN (Fin 2) ((w₀At w₀ (p : HeightOneSpectrum (𝓞 ℚ)))⁻¹ * z p), funext fun p => ?_⟩
    simp only [φ, transposeInvN_transposeInvN, mul_inv_cancel_left]
  have hli : LinearIndependent ℂ (fun β : Fin m => fun y : LocProd SQ => slotMat SQ m w w₀ y β) := by
    have := hind.map' (LinearMap.funLeft ℂ ℂ φ) (LinearMap.ker_eq_bot.2 (LinearMap.funLeft_injective_of_surjective ℂ ℂ φ hφ))
    convert this using 1
    all_goals try rfl
  obtain ⟨yy, hyy⟩ := exists_det_of_apply_ne_zero_of_linearIndependent (fun β : Fin m => fun y : LocProd SQ => slotMat SQ m w w₀ y β) hli
  exact ⟨yy, hyy⟩

variable {K : Type} [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
  {pins : CarrierPins ℚ} {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
  (F : CubicInductionForm K pins ψ μ)

theorem exists_refPoint (Wb : ∀ p : ↥SQ, LocalGL3 p.1 → ℂ)
    (_hWbmem : ∀ p : ↥SQ, Wb p ∈ gl3CyclicSubspace (F.whittakerLoc p.1))
    (_hWbone : ∀ p : ↥SQ, Wb p (iotaGL 1) = 1) :
    ∃ k₀ : ∀ p : ↥SQ, LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)), ∀ p : ↥SQ, F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * k₀ p) ≠ 0 := by
  have hne : ∀ p : ↥SQ, F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) ≠ 0 := by
    intro p h0
    have hbot : gl3CyclicSubspace (F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ))) = ⊥ := by rw [h0]; exact gl3CyclicSubspace_zero
    have hWb : Wb p = 0 := (Submodule.mem_bot ℂ).1 (hbot ▸ _hWbmem p)
    have := _hWbone p
    rw [hWb, Pi.zero_apply] at this
    exact zero_ne_one this
  have hex : ∀ p : ↥SQ, ∃ z : LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)), F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) z ≠ 0 :=
    fun p => Function.ne_iff.1 (hne p)
  choose z hz using hex
  refine ⟨fun p => longWeyl3⁻¹ * z p, fun p => ?_⟩
  rw [mul_inv_cancel_left]; exact hz p

theorem exists_cutoff
    (hBad : ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
      (∀ v ∈ T, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v, F.whittakerLoc v (g * k) = F.whittakerLoc v g) ∧
      (∀ v ∈ T, IsBadPlace K μ v → ∀ W ∈ gl3CyclicSubspace (F.whittakerLoc v), W ≠ 0 →
        F.whittakerLoc v ∈ gl3CyclicSubspace W))
    (_hwsm : ∀ (p : ↥SQ) (α : Fin m), ∃ U : Subgroup (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)),
      IsOpen (U : Set (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ), w p α (g * k) = w p α g)
    (yy : Fin m → LocProd SQ) (k₀ : ∀ p : ↥SQ, LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ))) :
    ∃ U : ∀ p : ↥SQ, Subgroup (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)),
      (∀ p : ↥SQ, IsOpen (U p : Set (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)))) ∧
      (∀ (p : ↥SQ), ∀ u ∈ U p, ∀ (β : Fin m) (i : Fin m),
        w p β (w₀At w₀ (p : HeightOneSpectrum (𝓞 ℚ)) * transposeInvN (Fin 2) (u * yy i p)) =
          w p β (w₀At w₀ (p : HeightOneSpectrum (𝓞 ℚ)) * transposeInvN (Fin 2) (yy i p))) ∧
      (∀ (p : ↥SQ), ∀ u ∈ U p,
        F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * transposeInv3 (iotaGL u) * k₀ p) =
          F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * k₀ p)) := by
  have hwsm' := _hwsm
  choose Uw hUwo hUw using hwsm'
  choose Uv hUvo hUv using exists_open_stabiliser F hBad

  let cj : ∀ p : ↥SQ, Fin m → GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) →* GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) :=
    fun p i => (MulAut.conj (transposeInvN (Fin 2) (yy i p))⁻¹).toMonoidHom.comp transposeInvN2Hom
  let c3 : ∀ p : ↥SQ, GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) →* LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)) :=
    fun p => (MulAut.conj (k₀ p)⁻¹).toMonoidHom.comp (transposeInv3Hom.comp iotaGL)
  have hcj : ∀ p i, Continuous (cj p i) := fun p i =>
    (continuous_const.mul continuous_id).mul continuous_const |>.comp continuous_transposeInvN2
  have hc3 : ∀ p, Continuous (c3 p) := fun p =>
    ((continuous_const.mul continuous_id).mul continuous_const).comp (continuous_transposeInv3.comp continuous_iotaGL)
  refine ⟨fun p => (⨅ β : Fin m, ⨅ i : Fin m, (Uw p β).comap (cj p i)) ⊓ (Uv (p : HeightOneSpectrum (𝓞 ℚ))).comap (c3 p), ?_, ?_, ?_⟩
  · intro p
    rw [Subgroup.coe_inf, Subgroup.coe_iInf]
    refine (isOpen_iInter_of_finite fun β => ?_).inter ((hUvo _).preimage (hc3 p))
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun i => (hUwo p β).preimage (hcj p i)
  · intro p u hu β i
    have hu' : cj p i u ∈ Uw p β := by
      have := (Subgroup.mem_inf.1 hu).1
      rw [Subgroup.mem_iInf] at this
      have := this β
      rw [Subgroup.mem_iInf] at this
      exact this i
    have heq : w₀At w₀ (p : HeightOneSpectrum (𝓞 ℚ)) * transposeInvN (Fin 2) (u * yy i p) =
        (w₀At w₀ (p : HeightOneSpectrum (𝓞 ℚ)) * transposeInvN (Fin 2) (yy i p)) * cj p i u := by
      simp only [cj, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, transposeInvN2Hom_apply, inv_inv,
        transposeInvN_mul]
      group
    rw [heq, hUw p β _ hu']
  · intro p u hu
    have hu' : c3 p u ∈ Uv (p : HeightOneSpectrum (𝓞 ℚ)) := (Subgroup.mem_inf.1 hu).2
    have heq : longWeyl3 * transposeInv3 (iotaGL u) * k₀ p = (longWeyl3 * k₀ p) * c3 p u := by
      simp only [c3, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, transposeInv3Hom_apply, inv_inv]
      group
    rw [heq, hUv _ _ hu']

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

end Choices

end KcRsCellChoice
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_unisolvence_refPoint_cutoff_of_linearIndependent_slots.KcRsCellChoice"

open KcRsCellChoice in
open LanglandsTunnell.TateLocal UnramifiedWhittaker in
theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (F : CubicInductionForm K pins ψ μ)
    (hBad : ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
      (∀ v ∈ T, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v, F.whittakerLoc v (g * k) = F.whittakerLoc v g) ∧
      (∀ v ∈ T, IsBadPlace K μ v → ∀ W ∈ gl3CyclicSubspace (F.whittakerLoc v), W ≠ 0 →
        F.whittakerLoc v ∈ gl3CyclicSubspace W))
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (m : ℕ) (w : ∀ p : ↥SQ, Fin m → GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) → ℂ)
    (_hwsm : ∀ (p : ↥SQ) (α : Fin m), ∃ U : Subgroup (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ), w p α (g * k) = w p α g)
    (w₀ : GL (Fin 2) ℚ)
    (_hind : LinearIndependent ℂ (fun α : Fin m => fun y : (∀ p : ↥SQ, GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) => ∏ p : ↥SQ, w p α (y p)))
    (Wb : ∀ p : ↥SQ, LocalGL3 p.1 → ℂ)
    (_hWbmem : ∀ p : ↥SQ, Wb p ∈ gl3CyclicSubspace (F.whittakerLoc p.1))
    (_hWbone : ∀ p : ↥SQ, Wb p (iotaGL 1) = 1) :
    ∃ (yy : Fin m → ∀ p : ↥SQ, GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (k₀ : ∀ p : ↥SQ, LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)))
      (U : ∀ p : ↥SQ, Subgroup (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ))),
      (∀ p : ↥SQ, IsOpen (U p : Set (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)))) ∧
      (∀ p : ↥SQ, F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * k₀ p) ≠ 0) ∧
      ((Matrix.of fun i j : Fin m => ∏ p : ↥SQ,
        w p j (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (globalPoints (𝓞 ℚ) ℚ w₀) * transposeInvN (Fin 2) (yy i p))).det ≠ 0) ∧
      (∀ (p : ↥SQ), ∀ u ∈ U p, ∀ (β : Fin m) (i : Fin m),
        w p β (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (globalPoints (𝓞 ℚ) ℚ w₀) * transposeInvN (Fin 2) (u * yy i p)) =
          w p β (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (globalPoints (𝓞 ℚ) ℚ w₀) * transposeInvN (Fin 2) (yy i p))) ∧
      (∀ (p : ↥SQ), ∀ u ∈ U p,
        F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * transposeInv3 (iotaGL u) * k₀ p) =
          F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (longWeyl3 * k₀ p)) := by
  obtain ⟨yy, hM⟩ := exists_unisolvence (w₀ := w₀) _hind
  obtain ⟨k₀, hc₀⟩ := exists_refPoint F Wb _hWbmem _hWbone
  obtain ⟨U, hUo, hU1, hU2⟩ := exists_cutoff (w₀ := w₀) F hBad _hwsm yy k₀
  exact ⟨yy, k₀, U, hUo, hc₀, hM, hU1, hU2⟩

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_unisolvence_refPoint_cutoff_of_linearIndependent_slots.KcRsCellChoice"

end S_LanglandsTunnell_RankinSelberg_exists_unisolvence_refPoint_cutoff_of_linearIndependent_slots
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_unisolvence_refPoint_cutoff_of_linearIndependent_slots (solution)
