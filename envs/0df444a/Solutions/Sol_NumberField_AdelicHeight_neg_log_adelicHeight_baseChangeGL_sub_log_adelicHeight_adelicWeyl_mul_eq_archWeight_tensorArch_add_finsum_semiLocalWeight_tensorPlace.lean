-- Prove2me | solution 1 for NumberField.AdelicHeight.neg_log_adelicHeight_baseChangeGL_sub_log_adelicHeight_adelicWeyl_mul_eq_archWeight_tensorArch_add_finsum_semiLocalWeight_tensorPlace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/6f3bb40c-4aee-5898-9c17-0fb494388807

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Theorems.Thm_NumberField_AdelicHeight_neg_log_adelicHeight_sub_log_adelicHeight_adelicWeyl_mul_eq_archWeight_glArch_add_finsum_weight_finComponent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_NumberField_AdelicHeight_neg_log_adelicHeight_baseChangeGL_sub_log_adelicHeight_adelicWeyl_mul_eq_archWeight_tensorArch_add_finsum_semiLocalWeight_tensorPlace

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

namespace WSL9

open AutomorphicForm NumberField.AdelicHeight NumberField.AdelicLevel

theorem finsum_eq_finsum_fiber {α β M : Type*} [AddCommMonoid M] (φ : α → β) (f : α → M)
    (hf : (Function.support f).Finite) :
    ∑ᶠ a, f a = ∑ᶠ b, ∑ᶠ a : {a // φ a = b}, f a.1 := by
  classical
  set S : Finset α := hf.toFinset with hS
  set T : Finset β := S.image φ with hT
  have hsuppS : Function.support f ⊆ (S : Set α) := by intro a ha; simpa [hS] using ha
  have inner : ∀ b : β, ∑ᶠ a : {a // φ a = b}, f a.1 = ∑ a ∈ S.filter (fun a => φ a = b), f a := by
    intro b
    show ∑ᶠ (j : ({a | φ a = b} : Set α)), f j = _
    rw [finsum_set_coe_eq_finsum_mem {a | φ a = b}]
    refine finsum_mem_eq_sum_of_subset f ?_ ?_
    · intro a ha
      simp only [Finset.coe_filter, Set.mem_setOf_eq]
      exact ⟨by simpa [hS] using ha.2, ha.1⟩
    · intro a ha
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha
      exact ha.2
  have houter : (Function.support fun b => ∑ᶠ a : {a // φ a = b}, f a.1) ⊆ (T : Set β) := by
    intro b hb
    rw [Function.mem_support, inner] at hb
    by_contra hbT
    apply hb
    refine Finset.sum_eq_zero fun a ha => ?_
    rw [Finset.mem_filter] at ha
    exfalso
    exact hbT (by rw [hT, Finset.coe_image]; exact ⟨a, ha.1, ha.2⟩)
  rw [finsum_eq_sum_of_support_subset f hsuppS, finsum_eq_sum_of_support_subset _ houter]
  simp_rw [inner]
  exact (Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem φ ha) f).symm

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem semiLocalPlaceComponent_semiLocalComponent (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    semiLocalPlaceComponent K L v w (semiLocalComponent K L v h) = finComponent (𝓞 L) L w.1 h := by
  apply Units.ext
  ext i j
  change ((Pi.evalRingHom (fun w' : v.Extension (𝓞 L) => w'.1.adicCompletion L) w).comp
      (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v).toAlgEquiv.toRingEquiv.toRingHom)
      (semiLocalEval K L v ((h : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j)) =
    ((h : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j) w.1
  rw [semiLocalEval_eq]
  change (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
    ((HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).symm (fun w' : v.Extension (𝓞 L) =>
      ((h : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j) w'.1))) w = _
  rw [AlgEquiv.apply_symm_apply]

theorem val_mul_apply {R : Type*} [CommRing R] (x y : GL (Fin 2) R) (i j : Fin 2) :
    ((x * y : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i j =
      (x : Matrix (Fin 2) (Fin 2) R) i 0 * (y : Matrix (Fin 2) (Fin 2) R) 0 j +
        (x : Matrix (Fin 2) (Fin 2) R) i 1 * (y : Matrix (Fin 2) (Fin 2) R) 1 j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem weyl_finComponent_apply (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2) :
    ((finComponent (𝓞 F) F v (glFin (𝓞 F) F (adelicWeyl (𝓞 F) F)) : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j =
      (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j := by
  change ((finComponent (𝓞 F) F v (glFin (𝓞 F) F (globalPoints (𝓞 F) F gl2Weyl)) :
      GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j = _
  rw [finComponent_globalPoints_apply, gl2Weyl_val]
  fin_cases i <;> fin_cases j <;> simp

theorem local_identity {F : Type*} [NormedField F] (w g : GL (Fin 2) F)
    (hw : ∀ i j, (w : Matrix (Fin 2) (Fin 2) F) i j = (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) i j) :
    -Real.log (finLocalHeight g) - Real.log (finLocalHeight (w * g)) = LocalWeight.weight g := by
  have h00 : ((w * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = (g : Matrix (Fin 2) (Fin 2) F) 0 0 := by
    rw [val_mul_apply, hw, hw]; simp
  have h01 : ((w * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 = (g : Matrix (Fin 2) (Fin 2) F) 0 1 := by
    rw [val_mul_apply, hw, hw]; simp
  have hdetw : (w : Matrix (Fin 2) (Fin 2) F).det = -1 := by
    rw [Matrix.det_fin_two, hw, hw, hw, hw]; simp
  have hdet : ‖((w * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det‖ = ‖(g : Matrix (Fin 2) (Fin 2) F).det‖ := by
    rw [Units.val_mul, Matrix.det_mul, hdetw, neg_one_mul, norm_neg]
  have hD : 0 < ‖(g : Matrix (Fin 2) (Fin 2) F).det‖ := norm_pos_iff.mpr (Matrix.isUnits_det_units g).ne_zero
  have hM1 : 0 < rowMaxNorm (g : Matrix (Fin 2) (Fin 2) F) := rowMaxNorm_pos g
  have hM0 : 0 < max ‖(g : Matrix (Fin 2) (Fin 2) F) 0 0‖ ‖(g : Matrix (Fin 2) (Fin 2) F) 0 1‖ := by
    have := rowMaxNorm_pos (w * g)
    rwa [rowMaxNorm, h00, h01] at this
  unfold finLocalHeight LocalWeight.weight
  rw [hdet, show rowMaxNorm ((w * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      max ‖(g : Matrix (Fin 2) (Fin 2) F) 0 0‖ ‖(g : Matrix (Fin 2) (Fin 2) F) 0 1‖ by rw [rowMaxNorm, h00, h01]]
  rw [Real.log_div hD.ne' (pow_pos hM1 2).ne', Real.log_div hD.ne' (pow_pos hM0 2).ne', Real.log_pow, Real.log_pow,
    Real.log_div (mul_pos hM0 hM1).ne' hD.ne', Real.log_mul hM0.ne' hM1.ne']
  push_cast
  ring

end WSL9

open WSL9 AutomorphicForm NumberField.AdelicHeight NumberField.AdelicLevel in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
    -Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.baseChangeGL K L x))
        - Real.log (NumberField.AdelicHeight.adelicHeight L
            (AutomorphicForm.adelicWeyl (𝓞 L) L * AutomorphicForm.baseChangeGL K L x)) =
      (fun y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
        -Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L y))
          - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
              (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) *
                AutomorphicForm.archIdentGL K L y))) (AutomorphicForm.tensorArch K L x) +
        ∑ᶠ v : HeightOneSpectrum (𝓞 K), AutomorphicForm.semiLocalWeight K L v (AutomorphicForm.tensorPlace K L v x)  := by
  have hD := NumberField.AdelicHeight.neg_log_adelicHeight_sub_log_adelicHeight_adelicWeyl_mul_eq_archWeight_glArch_add_finsum_weight_finComponent
    L (baseChangeGL K L x)
  rw [hD, glArch_baseChangeGL]
  congr 1
  set g := glFin (𝓞 L) L (baseChangeGL K L x) with hg

  have hloc : ∀ w : HeightOneSpectrum (𝓞 L),
      LocalWeight.weight (finComponent (𝓞 L) L w g) =
        -Real.log (finLocalHeight (finComponent (𝓞 L) L w g)) -
          Real.log (finLocalHeight (finComponent (𝓞 L) L w (glFin (𝓞 L) L (adelicWeyl (𝓞 L) L) * g))) := by
    intro w
    rw [map_mul]
    exact (WSL9.local_identity _ _ (WSL9.weyl_finComponent_apply L w)).symm
  have hfin : (Function.support fun w : HeightOneSpectrum (𝓞 L) => LocalWeight.weight (finComponent (𝓞 L) L w g)).Finite := by
    have h1 := hasFiniteMulSupport_finLocalHeight g
    have h2 := hasFiniteMulSupport_finLocalHeight (glFin (𝓞 L) L (adelicWeyl (𝓞 L) L) * g)
    refine (h1.union h2).subset ?_
    intro w hw
    rw [Function.mem_support, hloc] at hw
    by_contra hcon
    rw [Set.mem_union, Function.mem_mulSupport, Function.mem_mulSupport, not_or, not_not, not_not] at hcon
    apply hw
    rw [hcon.1, hcon.2, Real.log_one, neg_zero, sub_zero]
  rw [WSL9.finsum_eq_finsum_fiber (HeightOneSpectrum.under (𝓞 K)) _ hfin]
  refine finsum_congr fun v => ?_
  rw [← semiLocalComponent_glFin_baseChangeGL]
  unfold semiLocalWeight
  exact finsum_congr fun w => by rw [WSL9.semiLocalPlaceComponent_semiLocalComponent]

end S_NumberField_AdelicHeight_neg_log_adelicHeight_baseChangeGL_sub_log_adelicHeight_adelicWeyl_mul_eq_archWeight_tensorArch_add_finsum_semiLocalWeight_tensorPlace
end P2MW
export P2MW.S_NumberField_AdelicHeight_neg_log_adelicHeight_baseChangeGL_sub_log_adelicHeight_adelicWeyl_mul_eq_archWeight_tensorArch_add_finsum_semiLocalWeight_tensorPlace (solution)
