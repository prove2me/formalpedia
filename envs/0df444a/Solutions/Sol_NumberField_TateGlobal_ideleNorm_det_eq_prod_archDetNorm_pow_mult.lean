-- Prove2me | solution 1 for NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/459f036f-a3eb-5ed8-9f65-21ec021201f0

import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult.NumberField NumberField.AdelicLevel NumberField.AdelicVolume NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult.NumberField.TateGlobal AutomorphicForm"
open IsDedekindDomain
open scoped MatrixGroups

namespace NumberField
p2m_export "NumberField" "FinitePlace place InfinitePlace AdeleRing FinitePlace.norm_def AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "ideleNorm"
namespace IdeleNormDetGlue
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type} [Field F] [NumberField F]

private theorem norm_eq_zpow_of_valued (v : HeightOneSpectrum (𝓞 F)) {x : v.adicCompletion F} {m : ℤ}
    (hx : Valued.v x = WithZero.exp m) : ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ m := by
  rw [NumberField.FinitePlace.norm_def, hx,
    show (WithZero.exp m) = ((Multiplicative.ofAdd m : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      from rfl,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero, WithZero.unzero_coe, toAdd_ofAdd,
    NNReal.coe_zpow, NNReal.coe_natCast]

private theorem valued_det_le_one (v : HeightOneSpectrum (𝓞 F)) {M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)}
    (h : ∀ i j, Valued.v (M i j) ≤ 1) : Valued.v M.det ≤ 1 := by
  rw [Matrix.det_fin_two]
  refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
  · rw [map_mul]; exact mul_le_one' (h 0 0) (h 1 1)
  · rw [map_mul]; exact mul_le_one' (h 0 1) (h 1 0)

private theorem det_snd_apply (X : AdelicGL2 (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    ((Matrix.GeneralLinearGroup.det X : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v
      = ((finComponent (𝓞 F) F v (glFin (𝓞 F) F X) : GL (Fin 2) (v.adicCompletion F)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  change ((finAdeleEval (𝓞 F) F v).comp (adeleFin (𝓞 F) F)) (X : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).det = _
  rw [RingHom.map_det]
  rfl

private theorem det_fst_apply (X : AdelicGL2 (𝓞 F) F) (w : InfinitePlace F) :
    ((Matrix.GeneralLinearGroup.det X : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w
      = ((archComponent F w (glArch (𝓞 F) F X) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion).det := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  change ((archEval F w).comp (adeleArch (𝓞 F) F)) (X : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).det = _
  rw [RingHom.map_det]
  rfl

private theorem valued_det_finComponent_eq_one (X : AdelicGL2 (𝓞 F) F)
    (hX : glFin (𝓞 F) F X ∈ finiteIntegralGL2 (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((finComponent (𝓞 F) F v (glFin (𝓞 F) F X) : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det = 1 := by
  set A := finComponent (𝓞 F) F v (glFin (𝓞 F) F X) with hA
  obtain ⟨h1, h2⟩ := mem_finiteIntegralGL2_iff.mp hX
  have ha : Valued.v (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det ≤ 1 :=
    valued_det_le_one v fun i j =>
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp (h1 i j v)
  have hb : Valued.v ((A⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det
      ≤ 1 := by
    rw [hA, ← map_inv]
    exact valued_det_le_one v fun i j =>
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp (h2 i j v)
  have hab : (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det
      * ((A⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  have hprod : Valued.v (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det
      * Valued.v ((A⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det
        = 1 := by
    rw [← map_mul, hab, map_one]
  refine le_antisymm ha ?_
  calc (1 : WithZero (Multiplicative ℤ))
      = Valued.v (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det
          * Valued.v ((A⁻¹ : GL (Fin 2) (v.adicCompletion F)) :
              Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det := hprod.symm
    _ ≤ Valued.v (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det * 1 := mul_le_mul_right hb _
    _ = _ := mul_one _

private theorem ideleNorm_det_eq_prod_archDetNorm_pow (X : AdelicGL2 (𝓞 F) F)
    (hX : glFin (𝓞 F) F X ∈ finiteIntegralGL2 (𝓞 F) F) :
    ideleNorm F (Matrix.GeneralLinearGroup.det X)
      = ∏ w : InfinitePlace F, archDetNorm w X ^ w.mult := by
  have hS := NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm F
    (Matrix.GeneralLinearGroup.det X)
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F),
      ‖((Matrix.GeneralLinearGroup.det X : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v‖ = 1 := by
    intro v
    rw [det_snd_apply, norm_eq_zpow_of_valued v (m := 0)
      (by rw [valued_det_finComponent_eq_one X hX v, WithZero.exp_zero]), zpow_zero]
  have harch : ∀ w : InfinitePlace F,
      ‖((Matrix.GeneralLinearGroup.det X : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖
        = archDetNorm w X := by
    intro w
    rw [det_fst_apply]
    rfl
  unfold ideleNorm
  rw [hS, finprod_eq_one_of_forall_eq_one hfin, mul_one]
  exact Finset.prod_congr rfl fun w _ => by rw [harch w]

end NumberField.TateGlobal.IdeleNormDetGlue

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult.NumberField NumberField.AdelicLevel NumberField.AdelicVolume AutomorphicForm"

open _root_.NumberField.TateGlobal _root_.P2MW.S_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult.NumberField.TateGlobal NumberField.TateGlobal.IdeleNormDetGlue in

theorem solution (F : Type) [Field F] [NumberField F]
    (X : AdelicGL2 (𝓞 F) F) (hX : glFin (𝓞 F) F X ∈ finiteIntegralGL2 (𝓞 F) F) :
    ideleNorm F (Matrix.GeneralLinearGroup.det X) = ∏ w : InfinitePlace F, archDetNorm w X ^ w.mult :=
  ideleNorm_det_eq_prod_archDetNorm_pow X hX

end S_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
end P2MW
export P2MW.S_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult (solution)
