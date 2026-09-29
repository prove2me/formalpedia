-- Prove2me | solution 1 for NumberField.AdelicHeight.adelicHeight_diagOne_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/11f8bde5-9354-5d96-8dd1-148566af9615

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicHeight
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicHeight_adelicHeight_diagOne_mul
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal NumberField.AdelicHeight
open NumberField.InfinitePlace AutomorphicForm.SiegelCoordinates AutomorphicForm.SiegelReduction

noncomputable section

namespace C5aD4b

section Local

variable {K : Type*} [NormedField K]

theorem finLocalHeight_upper_entries_mul {s : GL (Fin 2) K} {a t : K} (ht : t ≠ 0)
    (h00 : (s : Matrix (Fin 2) (Fin 2) K) 0 0 = a) (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (h11 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = t) (g : GL (Fin 2) K) :
    finLocalHeight (s * g) = ‖a‖ / ‖t‖ * finLocalHeight g := by
  have hrow : rowMaxNorm ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = ‖t‖ * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
    have e10 : ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = t * (g : Matrix (Fin 2) (Fin 2) K) 1 0 := by
      rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, h10, h11, zero_mul, zero_add]
    have e11 : ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 = t * (g : Matrix (Fin 2) (Fin 2) K) 1 1 := by
      rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, h10, h11, zero_mul, zero_add]
    simp only [rowMaxNorm, e10, e11, norm_mul]
    exact (mul_max_of_nonneg _ _ (norm_nonneg t)).symm
  have hdet : ‖((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖
      = ‖a‖ * ‖t‖ * ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ := by
    rw [Units.val_mul, Matrix.det_mul, norm_mul, Matrix.det_fin_two, h00, h10, h11, mul_zero, sub_zero, norm_mul]
  have hr : 0 < rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := rowMaxNorm_pos g
  have htn : 0 < ‖t‖ := norm_pos_iff.mpr ht
  rw [finLocalHeight, finLocalHeight, hrow, hdet]
  field_simp

end Local

variable {F : Type} [Field F] [NumberField F]

theorem hasFiniteMulSupport_norm_snd (a : (AdeleRing (𝓞 F) F)ˣ) :
    (fun v : HeightOneSpectrum (𝓞 F) => ‖(a : AdeleRing (𝓞 F) F).2 v‖).HasFiniteMulSupport := by
  have h1 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      (a : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F := ((a : AdeleRing (𝓞 F) F).2).2
  have h2 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F :=
    (((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2).2
  refine Filter.eventually_cofinite.mp ?_
  filter_upwards [h1, h2] with v hv hv'
  have hmul : (a : AdeleRing (𝓞 F) F).2 v * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1 := by
    have h := congrArg (fun x : AdeleRing (𝓞 F) F => x.2 v) a.mul_inv
    exact h
  have hle : ‖(a : AdeleRing (𝓞 F) F).2 v‖ ≤ 1 := norm_le_one_of_mem_adicCompletionIntegers hv
  have hle' : ‖((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v‖ ≤ 1 :=
    norm_le_one_of_mem_adicCompletionIntegers hv'
  have hprod : ‖(a : AdeleRing (𝓞 F) F).2 v‖ * ‖((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v‖ = 1 := by
    rw [← norm_mul, hmul, norm_one]
  refine le_antisymm hle ?_
  by_contra hlt
  push Not at hlt
  have : ‖(a : AdeleRing (𝓞 F) F).2 v‖ * ‖((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v‖ < 1 := by
    calc _ ≤ ‖(a : AdeleRing (𝓞 F) F).2 v‖ * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hlt
  exact (lt_irrefl (1 : ℝ)) (hprod ▸ this)

variable (F)

theorem archHeight_diagOne_mul (a : (AdeleRing (𝓞 F) F)ˣ) (h : GL (Fin 2) (InfiniteAdeleRing F)) :
    archHeight F (glArch (𝓞 F) F (diagOne a) * h)
      = (∏ w : InfinitePlace F, ‖(a : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult) * archHeight F h := by
  have hloc : ∀ w : InfinitePlace F,
      localHeight (archComponent F w (glArch (𝓞 F) F (diagOne a) * h))
        = ‖(a : AdeleRing (𝓞 F) F).1 w‖ * localHeight (archComponent F w h) := by
    intro w
    rw [map_mul, localHeight_upper_entries_mul (a := (a : AdeleRing (𝓞 F) F).1 w) (t := 1) one_ne_zero
      ?_ ?_ ?_ (archComponent F w h), norm_one, div_one]
    · rw [archComponent_apply, glArch_apply, diagOne_coe_apply]; rfl
    · rw [archComponent_apply, glArch_apply, diagOne_coe_apply]; rfl
    · rw [archComponent_apply, glArch_apply, diagOne_coe_apply]; rfl
  unfold archHeight
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun w _ => by rw [hloc w, mul_pow]

theorem finHeight_diagOne_mul (a : (AdeleRing (𝓞 F) F)ˣ) (h : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    finHeight F (glFin (𝓞 F) F (diagOne a) * h)
      = (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(a : AdeleRing (𝓞 F) F).2 v‖) * finHeight F h := by
  set nA : HeightOneSpectrum (𝓞 F) → ℝ := fun v => ‖(a : AdeleRing (𝓞 F) F).2 v‖ with hnAdef
  set fB : HeightOneSpectrum (𝓞 F) → ℝ := fun v => finLocalHeight (finComponent (𝓞 F) F v h) with hfBdef
  have hnA : nA.HasFiniteMulSupport := hasFiniteMulSupport_norm_snd a
  have hfB : fB.HasFiniteMulSupport := hasFiniteMulSupport_finLocalHeight _
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      finLocalHeight (finComponent (𝓞 F) F v (glFin (𝓞 F) F (diagOne a) * h)) = nA v * fB v := by
    intro v
    rw [map_mul, finLocalHeight_upper_entries_mul (a := (a : AdeleRing (𝓞 F) F).2 v) (t := 1) one_ne_zero
      ?_ ?_ ?_ (finComponent (𝓞 F) F v h), norm_one, div_one]
    · rw [finComponent_apply, glFin_apply, diagOne_coe_apply]; rfl
    · rw [finComponent_apply, glFin_apply, diagOne_coe_apply]; rfl
    · rw [finComponent_apply, glFin_apply, diagOne_coe_apply]; rfl
  unfold finHeight
  calc ∏ᶠ v, finLocalHeight (finComponent (𝓞 F) F v (glFin (𝓞 F) F (diagOne a) * h))
      = ∏ᶠ v, (nA v * fB v) := finprod_congr hloc
    _ = (∏ᶠ v, nA v) * ∏ᶠ v, fB v := finprod_mul_distrib hnA hfB

end C5aD4b

end

open C5aD4b in
theorem solution
    (F : Type) [Field F] [NumberField F] (a : (AdeleRing (𝓞 F) F)ˣ) (h : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (diagOne a * h) = ideleNorm F a * adelicHeight F h := by
  have hmod := NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm F a
  have hnorm : ideleNorm F a = (∏ w : InfinitePlace F, ‖(a : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult)
      * ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(a : AdeleRing (𝓞 F) F).2 v‖ := by
    unfold ideleNorm; exact hmod
  unfold adelicHeight
  rw [map_mul, map_mul, archHeight_diagOne_mul F a, finHeight_diagOne_mul F a, hnorm]
  ring

end S_NumberField_AdelicHeight_adelicHeight_diagOne_mul
end P2MW
export P2MW.S_NumberField_AdelicHeight_adelicHeight_diagOne_mul (solution)
