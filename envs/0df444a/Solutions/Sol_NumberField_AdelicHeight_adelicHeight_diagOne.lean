-- Prove2me | solution 1 for NumberField.AdelicHeight.adelicHeight_diagOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/eb19b922-f558-5bff-ba7b-554f08b94b72

import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_isInducedSection_adelicHeight_cpow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicHeight_adelicHeight_diagOne
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHeight NumberField.AdelicLevel NumberField.TateGlobal AutomorphicForm

open scoped NNReal ENNReal

namespace HDiag

theorem adelicHeight_borel_mul (L : Type) [Field L] [NumberField L]
    {b : AdelicGL2 (𝓞 L) L} (hb : b ∈ adelicBorel (𝓞 L) L) (g : AdelicGL2 (𝓞 L) L) :
    adelicHeight L (b * g)
      = ideleNorm L (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 L) L)))
        * (ideleNorm L (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 L) L))))⁻¹
        * adelicHeight L g := by
  obtain ⟨hpos, -, hind⟩ := AutomorphicForm.isInducedSection_adelicHeight_cpow L
  have h := hind hpos (1 / 2) b hb g
  simp only at h
  have hexp : (1 / 2 : ℂ) + 1 / 2 = 1 := by norm_num
  rw [etaFst_apply, etaSnd_apply] at h
  simp only [MonoidHom.one_apply, one_mul, cpowChar_apply_val,
    MonoidHom.coe_toHomUnits, MonoidHom.coe_comp, Function.comp_apply,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, NNReal.coe_toRealHom] at h
  rw [hexp, Complex.cpow_one, Complex.cpow_one, Complex.cpow_one, Complex.cpow_neg_one] at h
  have h' : adelicHeight L (b * g)
      = ((distribHaarChar (AdeleRing (𝓞 L) L)
            (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 L) L))) : ℝ≥0) : ℝ)
        * (((distribHaarChar (AdeleRing (𝓞 L) L)
            (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 L) L))) : ℝ≥0) : ℝ))⁻¹
        * adelicHeight L g := by
    exact_mod_cast h
  exact h'

theorem diagOne_mem_adelicBorel (L : Type) [Field L] [NumberField L] (t : (AdeleRing (𝓞 L) L)ˣ) :
    (diagOne t : AdelicGL2 (𝓞 L) L) ∈ adelicBorel (𝓞 L) L := by
  show ((diagOne t : GL (Fin 2) (AdeleRing (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0
  rw [diagOne_coe_apply]
  exact Matrix.diagonal_apply_ne _ (by decide)

theorem borelDiagFst_diagOne (L : Type) [Field L] [NumberField L] (t : (AdeleRing (𝓞 L) L)ˣ) :
    borelDiagFst (⟨diagOne t, diagOne_mem_adelicBorel L t⟩ : ↥(adelicBorel (𝓞 L) L)) = t := by
  apply Units.ext
  show ((diagOne t : GL (Fin 2) (AdeleRing (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 = t
  rw [diagOne_coe_apply, Matrix.diagonal_apply_eq]
  rfl

theorem borelDiagSnd_diagOne (L : Type) [Field L] [NumberField L] (t : (AdeleRing (𝓞 L) L)ˣ) :
    borelDiagSnd (⟨diagOne t, diagOne_mem_adelicBorel L t⟩ : ↥(adelicBorel (𝓞 L) L)) = 1 := by
  apply Units.ext
  show ((diagOne t : GL (Fin 2) (AdeleRing (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1 = 1
  rw [diagOne_coe_apply, Matrix.diagonal_apply_eq]
  rfl

theorem ideleNorm_one (L : Type) [Field L] [NumberField L] :
    ideleNorm L (1 : (AdeleRing (𝓞 L) L)ˣ) = 1 := by
  simp [ideleNorm]

theorem ideleNorm_inv (L : Type) [Field L] [NumberField L] (t : (AdeleRing (𝓞 L) L)ˣ) :
    ideleNorm L t⁻¹ = (ideleNorm L t)⁻¹ := by
  have h : ideleNorm L t⁻¹ * ideleNorm L t = 1 := by
    rw [← ideleNorm_mul, inv_mul_cancel, ideleNorm_one]
  exact eq_inv_of_mul_eq_one_left h

theorem adelicHeight_diagOne_mul (L : Type) [Field L] [NumberField L]
    (t : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) :
    adelicHeight L (diagOne t * g) = ideleNorm L t * adelicHeight L g := by
  rw [adelicHeight_borel_mul L (diagOne_mem_adelicBorel L t), borelDiagFst_diagOne,
    borelDiagSnd_diagOne, ideleNorm_one, inv_one, mul_one]

theorem adelicHeight_one (L : Type) [Field L] [NumberField L] :
    adelicHeight L (1 : AdelicGL2 (𝓞 L) L) = 1 := by
  unfold adelicHeight finHeight
  rw [map_one, map_one, AutomorphicForm.WindowedSiegel.archHeight_one, one_mul]
  refine finprod_eq_one_of_forall_eq_one fun v => ?_
  rw [map_one]
  refine finLocalHeight_eq_one 1 (fun i j => ?_) (fun i j => ?_)
  · rw [Units.val_one]
    fin_cases i <;> fin_cases j <;> simp
  · rw [inv_one, Units.val_one]
    fin_cases i <;> fin_cases j <;> simp

end HDiag

theorem solution (F : Type) [Field F] [NumberField F]
    (t : (AdeleRing (𝓞 F) F)ˣ) :
    NumberField.AdelicHeight.adelicHeight F (NumberField.AdelicLevel.diagOne t : AutomorphicForm.AdelicGL2 (𝓞 F) F) =
      NumberField.TateGlobal.ideleNorm F t := by
  have h := HDiag.adelicHeight_diagOne_mul F t 1
  rw [mul_one, HDiag.adelicHeight_one, mul_one] at h
  exact h

end S_NumberField_AdelicHeight_adelicHeight_diagOne
end P2MW
export P2MW.S_NumberField_AdelicHeight_adelicHeight_diagOne (solution)
