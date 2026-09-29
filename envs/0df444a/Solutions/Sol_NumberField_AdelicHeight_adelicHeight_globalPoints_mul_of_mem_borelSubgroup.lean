-- Prove2me | solution 1 for NumberField.AdelicHeight.adelicHeight_globalPoints_mul_of_mem_borelSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/65f6f56e-7c3a-549e-9c80-3d2058781cea

import Mathlib
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_NumberField_AdelicHeight_adelicHeight_globalPoints_mul_of_mem_borelSubgroup

set_option autoImplicit false

open NumberField IsDedekindDomain Matrix
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates AutomorphicForm.SiegelReduction NumberField.AdelicLevel NumberField.InfinitePlace NumberField.AdelicHeight

namespace R1HeightBorel

section Local

variable {L : Type*} [NormedField L]

private theorem coe_mul' (s g : GL (Fin 2) L) :
    ((s * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
      = (s : Matrix (Fin 2) (Fin 2) L) * (g : Matrix (Fin 2) (Fin 2) L) := rfl

theorem bottom_row_mul {s : GL (Fin 2) L} (h10 : (s : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (g : GL (Fin 2) L) (j : Fin 2) :
    ((s * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 j
      = (s : Matrix (Fin 2) (Fin 2) L) 1 1 * (g : Matrix (Fin 2) (Fin 2) L) 1 j := by
  rw [coe_mul', Matrix.mul_apply, Fin.sum_univ_two, h10]
  ring

theorem norm_s11_ne_zero {s : GL (Fin 2) L} (h10 : (s : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ‖(s : Matrix (Fin 2) (Fin 2) L) 1 1‖ ≠ 0 := by
  have hdet := (Matrix.isUnits_det_units s).ne_zero
  rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
  exact norm_ne_zero_iff.mpr (right_ne_zero_of_mul hdet)

theorem norm_det_mul_of_upper {s : GL (Fin 2) L} (h10 : (s : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (g : GL (Fin 2) L) :
    ‖((s * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).det‖
      = ‖(s : Matrix (Fin 2) (Fin 2) L) 0 0‖ * ‖(s : Matrix (Fin 2) (Fin 2) L) 1 1‖
          * ‖(g : Matrix (Fin 2) (Fin 2) L).det‖ := by
  have hdets : (s : Matrix (Fin 2) (Fin 2) L).det
      = (s : Matrix (Fin 2) (Fin 2) L) 0 0 * (s : Matrix (Fin 2) (Fin 2) L) 1 1 := by
    rw [Matrix.det_fin_two, h10, mul_zero, sub_zero]
  rw [coe_mul', Matrix.det_mul, hdets, norm_mul, norm_mul]

theorem localHeight_mul_of_upper {s : GL (Fin 2) L} (h10 : (s : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (g : GL (Fin 2) L) :
    localHeight (s * g)
      = ‖(s : Matrix (Fin 2) (Fin 2) L) 0 0‖ / ‖(s : Matrix (Fin 2) (Fin 2) L) 1 1‖ * localHeight g := by
  have hrow := rowNormSq_scalar_entries_mul (z := (s : Matrix (Fin 2) (Fin 2) L) 1 1) h10 rfl g
  have hd := norm_s11_ne_zero h10
  have hr := (rowNormSq_pos g).ne'
  unfold localHeight
  rw [norm_det_mul_of_upper h10, hrow]
  field_simp

theorem finLocalHeight_mul_of_upper {s : GL (Fin 2) L}
    (h10 : (s : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (g : GL (Fin 2) L) :
    finLocalHeight (s * g)
      = ‖(s : Matrix (Fin 2) (Fin 2) L) 0 0‖ / ‖(s : Matrix (Fin 2) (Fin 2) L) 1 1‖
          * finLocalHeight g := by
  have hrow : rowMaxNorm ((s * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
      = ‖(s : Matrix (Fin 2) (Fin 2) L) 1 1‖ * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) L) := by
    unfold rowMaxNorm
    rw [bottom_row_mul h10 g 0, bottom_row_mul h10 g 1, norm_mul, norm_mul,
      mul_max_of_nonneg _ _ (norm_nonneg _)]
  have hd := norm_s11_ne_zero h10
  have hr := (rowMaxNorm_pos g).ne'
  unfold finLocalHeight
  rw [norm_det_mul_of_upper h10, hrow]
  field_simp

end Local

section Adelic

variable {F : Type} [Field F] [NumberField F]

theorem archHeight_globalPoints_mul_of_upper {γ : GL (Fin 2) F}
    (h10 : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (h : GL (Fin 2) (InfiniteAdeleRing F)) :
    archHeight F (glArch (𝓞 F) F (globalPoints (𝓞 F) F γ) * h)
      = (∏ w : InfinitePlace F, w ((γ : Matrix (Fin 2) (Fin 2) F) 0 0) ^ w.mult)
          / (∏ w : InfinitePlace F, w ((γ : Matrix (Fin 2) (Fin 2) F) 1 1) ^ w.mult)
          * archHeight F h := by
  unfold archHeight
  rw [← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have h10w : ((archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F γ)) :
      GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 1 0 = 0 := by
    rw [archComponent_globalPoints_apply, h10]
    apply NumberField.InfinitePlace.Completion.ext
    simp
  rw [map_mul, localHeight_mul_of_upper h10w, archComponent_globalPoints_apply,
    archComponent_globalPoints_apply, norm_coe_completion, norm_coe_completion, mul_pow, div_pow]

theorem finHeight_globalPoints_mul_of_upper {γ : GL (Fin 2) F}
    (h10 : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (h : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    finHeight F (glFin (𝓞 F) F (globalPoints (𝓞 F) F γ) * h)
      = (∏ᶠ w : FinitePlace F, w ((γ : Matrix (Fin 2) (Fin 2) F) 0 0))
          / (∏ᶠ w : FinitePlace F, w ((γ : Matrix (Fin 2) (Fin 2) F) 1 1))
          * finHeight F h := by
  have hdet := (Matrix.isUnits_det_units γ).ne_zero
  rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
  have ha : (γ : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul hdet
  have hd : (γ : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := right_ne_zero_of_mul hdet
  set nA := fun v : HeightOneSpectrum (𝓞 F) =>
    ‖FinitePlace.embedding v ((γ : Matrix (Fin 2) (Fin 2) F) 0 0)‖ with hnA
  set nD := fun v : HeightOneSpectrum (𝓞 F) =>
    ‖FinitePlace.embedding v ((γ : Matrix (Fin 2) (Fin 2) F) 1 1)‖ with hnD
  set fB := fun v : HeightOneSpectrum (𝓞 F) => finLocalHeight (finComponent (𝓞 F) F v h) with hfB
  have hnAf : nA.HasFiniteMulSupport := hasFiniteMulSupport_norm_embedding ha
  have hnDf : nD.HasFiniteMulSupport := hasFiniteMulSupport_norm_embedding hd
  have hfBf : fB.HasFiniteMulSupport := hasFiniteMulSupport_finLocalHeight _
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      finLocalHeight (finComponent (𝓞 F) F v (glFin (𝓞 F) F (globalPoints (𝓞 F) F γ) * h))
        = nA v / nD v * fB v := by
    intro v
    have h10v : ((finComponent (𝓞 F) F v (glFin (𝓞 F) F (globalPoints (𝓞 F) F γ)) :
        GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0 := by
      rw [finComponent_globalPoints_apply, h10, map_zero]
    rw [map_mul, finLocalHeight_mul_of_upper h10v, finComponent_globalPoints_apply,
      finComponent_globalPoints_apply]
  unfold finHeight
  simp_rw [hloc]
  have hq : (fun v => nA v / nD v).HasFiniteMulSupport := hnAf.div hnDf
  rw [finprod_mul_distrib hq hfBf, finprod_div_distrib hnAf hnDf, hnA, hnD,
    finprod_norm_embedding, finprod_norm_embedding]

theorem adelicHeight_globalPoints_mul_of_mem_borelSubgroup {γ : GL (Fin 2) F}
    (hγ : γ ∈ borelSubgroup F) (g : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (globalPoints (𝓞 F) F γ * g) = adelicHeight F g := by
  have h10 : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hγ
  have hdet := (Matrix.isUnits_det_units γ).ne_zero
  rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
  have ha : (γ : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul hdet
  have hd : (γ : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := right_ne_zero_of_mul hdet
  have hpa := prod_abs_eq_one ha
  have hpd := prod_abs_eq_one hd
  set A₁ := ∏ w : InfinitePlace F, w ((γ : Matrix (Fin 2) (Fin 2) F) 0 0) ^ w.mult with hA₁
  set A₂ := ∏ᶠ w : FinitePlace F, w ((γ : Matrix (Fin 2) (Fin 2) F) 0 0) with hA₂
  set D₁ := ∏ w : InfinitePlace F, w ((γ : Matrix (Fin 2) (Fin 2) F) 1 1) ^ w.mult with hD₁
  set D₂ := ∏ᶠ w : FinitePlace F, w ((γ : Matrix (Fin 2) (Fin 2) F) 1 1) with hD₂
  have hA₁0 : A₁ ≠ 0 := left_ne_zero_of_mul (hpa.trans_ne one_ne_zero)
  have hD₁0 : D₁ ≠ 0 := left_ne_zero_of_mul (hpd.trans_ne one_ne_zero)
  have hA₂ : A₂ = A₁⁻¹ := eq_inv_of_mul_eq_one_right hpa
  have hD₂ : D₂ = D₁⁻¹ := eq_inv_of_mul_eq_one_right hpd
  unfold adelicHeight
  rw [map_mul, map_mul, archHeight_globalPoints_mul_of_upper h10, finHeight_globalPoints_mul_of_upper h10]
  change A₁ / D₁ * archHeight F (glArch (𝓞 F) F g) * (A₂ / D₂ * finHeight F (glFin (𝓞 F) F g)) =
    archHeight F (glArch (𝓞 F) F g) * finHeight F (glFin (𝓞 F) F g)
  rw [hA₂, hD₂]
  field_simp

end Adelic

end R1HeightBorel

theorem solution
    (F : Type) [Field F] [NumberField F]
    {γ : Matrix.GeneralLinearGroup (Fin 2) F} (hγ : γ ∈ AutomorphicForm.borelSubgroup F)
    (g : AutomorphicForm.AdelicGL2 (𝓞 F) F) :
    NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.globalPoints (𝓞 F) F γ * g)
      = NumberField.AdelicHeight.adelicHeight F g :=
  R1HeightBorel.adelicHeight_globalPoints_mul_of_mem_borelSubgroup hγ g

end S_NumberField_AdelicHeight_adelicHeight_globalPoints_mul_of_mem_borelSubgroup
end P2MW
export P2MW.S_NumberField_AdelicHeight_adelicHeight_globalPoints_mul_of_mem_borelSubgroup (solution)
