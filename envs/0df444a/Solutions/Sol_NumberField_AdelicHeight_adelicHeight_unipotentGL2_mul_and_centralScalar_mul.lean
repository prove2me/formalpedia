-- Prove2me | solution 1 for NumberField.AdelicHeight.adelicHeight_unipotentGL2_mul_and_centralScalar_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/99ff0cdd-9ad7-524e-8a5e-8e62574a688f

import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicHeight_adelicHeight_unipotentGL2_mul_and_centralScalar_mul

section

set_option autoImplicit false

p2m_open "AutomorphicForm P2MW.S_NumberField_AdelicHeight_adelicHeight_unipotentGL2_mul_and_centralScalar_mul.AutomorphicForm"
open NumberField NumberField.AdelicHeight
open scoped Pointwise

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "WindowedSiegel.rowNormSq WindowedSiegel.localHeight WindowedSiegel.archHeight WindowedSiegel.archHeight_scalar_entries_mul AdelicGL2 centralScalar unipotentGL2 unipotentGL2_coe"
p2m_open "AutomorphicForm"

variable (F : Type) [Field F] [NumberField F]

section LocalFactors

variable {K : Type*} [NormedField K]

private theorem rowNormSq_unipotent_mul (x : K) (g : GL (Fin 2) K) :
    WindowedSiegel.rowNormSq ((unipotentGL2 x * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = WindowedSiegel.rowNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
  unfold WindowedSiegel.rowNormSq
  rw [Matrix.GeneralLinearGroup.coe_mul, unipotentGL2_coe]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem localHeight_unipotent_mul (x : K) (g : GL (Fin 2) K) :
    WindowedSiegel.localHeight (unipotentGL2 x * g) = WindowedSiegel.localHeight g := by
  unfold WindowedSiegel.localHeight
  rw [rowNormSq_unipotent_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, unipotentGL2_coe,
    Matrix.det_fin_two_of]
  simp

private theorem rowMaxNorm_unipotent_mul (x : K) (g : GL (Fin 2) K) :
    rowMaxNorm ((unipotentGL2 x * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
  unfold rowMaxNorm
  rw [Matrix.GeneralLinearGroup.coe_mul, unipotentGL2_coe]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem finLocalHeight_unipotent_mul (x : K) (g : GL (Fin 2) K) :
    finLocalHeight (unipotentGL2 x * g) = finLocalHeight g := by
  unfold finLocalHeight
  rw [rowMaxNorm_unipotent_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, unipotentGL2_coe,
    Matrix.det_fin_two_of]
  simp

private theorem finLocalHeight_scalar_entries_mul {s : GL (Fin 2) K} {c : K} (hc : c ≠ 0)
    (h00 : (s : Matrix (Fin 2) (Fin 2) K) 0 0 = c) (h01 : (s : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (h11 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = c)
    (g : GL (Fin 2) K) : finLocalHeight (s * g) = finLocalHeight g := by
  have hdet : ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det
      = c * c * (g : Matrix (Fin 2) (Fin 2) K).det := by
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, Matrix.det_fin_two, h00, h01, h10, h11]
    ring
  have hrow : rowMaxNorm ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = ‖c‖ * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
    unfold rowMaxNorm
    rw [Matrix.GeneralLinearGroup.coe_mul]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, h10, h11, zero_mul, zero_add, norm_mul]
    exact (mul_max_of_nonneg _ _ (norm_nonneg c)).symm
  have hc' : (0 : ℝ) < ‖c‖ ^ 2 := by positivity
  unfold finLocalHeight
  rw [hdet, hrow, mul_pow, norm_mul, norm_mul, ← pow_two]
  exact mul_div_mul_left _ _ hc'.ne'

end LocalFactors

private theorem map_unipotentGL2 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : R) :
    Matrix.GeneralLinearGroup.map f (unipotentGL2 x) = unipotentGL2 (f x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map_apply, unipotentGL2]

private theorem adelicHeight_unipotentGL2_mul (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (unipotentGL2 x * g) = adelicHeight F g := by
  unfold adelicHeight
  congr 1
  · rw [map_mul]
    unfold WindowedSiegel.archHeight
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [map_mul]
    congr 1
    rw [AdelicLevel.glArch, map_unipotentGL2, AdelicLevel.archComponent, map_unipotentGL2,
      localHeight_unipotent_mul]
  · rw [map_mul]
    unfold finHeight
    refine finprod_congr fun v => ?_
    rw [map_mul, AdelicLevel.glFin, map_unipotentGL2, AdelicLevel.finComponent, map_unipotentGL2,
      finLocalHeight_unipotent_mul]

private theorem adelicHeight_centralScalar_mul (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (centralScalar (𝓞 F) F z * g) = adelicHeight F g := by
  have hent : ∀ (S : Type) [CommRing S] (f : AdeleRing (𝓞 F) F →+* S) (i j : Fin 2),
      ((Matrix.GeneralLinearGroup.map f (centralScalar (𝓞 F) F z) : GL (Fin 2) S) :
        Matrix (Fin 2) (Fin 2) S) i j = if i = j then f z else 0 := by
    intro S _ f i j
    rw [Matrix.GeneralLinearGroup.map_apply]
    fin_cases i <;> fin_cases j <;> simp [centralScalar, Matrix.GeneralLinearGroup.scalar]
  unfold adelicHeight
  congr 1
  · rw [map_mul]
    exact WindowedSiegel.archHeight_scalar_entries_mul F (z := AdelicLevel.adeleArch (𝓞 F) F z)
      (fun v => (z.isUnit.map ((AdelicLevel.archEval F v).comp
        (AdelicLevel.adeleArch (𝓞 F) F))).ne_zero)
      (hent _ _ 0 0) (hent _ _ 0 1) (hent _ _ 1 0) (hent _ _ 1 1) _
  · rw [map_mul]
    unfold finHeight
    refine finprod_congr fun v => ?_
    rw [map_mul, AdelicLevel.glFin, AdelicLevel.finComponent, ← MonoidHom.comp_apply,
      ← Matrix.GeneralLinearGroup.map_comp]
    refine finLocalHeight_scalar_entries_mul
      (c := ((AdelicLevel.finAdeleEval (𝓞 F) F v).comp (AdelicLevel.adeleFin (𝓞 F) F)) z)
      (z.isUnit.map _).ne_zero (hent _ _ 0 0) (hent _ _ 0 1) (hent _ _ 1 0) (hent _ _ 1 1) _

end AutomorphicForm

end

end

section

set_option autoImplicit false

p2m_open "AutomorphicForm P2MW.S_NumberField_AdelicHeight_adelicHeight_unipotentGL2_mul_and_centralScalar_mul.AutomorphicForm NumberField"

open NumberField NumberField.AdelicHeight in

theorem solution
    (F : Type) [Field F] [NumberField F] :
    (∀ (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
        adelicHeight F (unipotentGL2 x * g) = adelicHeight F g) ∧
      ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
        adelicHeight F (centralScalar (𝓞 F) F z * g) = adelicHeight F g :=
  ⟨AutomorphicForm.adelicHeight_unipotentGL2_mul F, AutomorphicForm.adelicHeight_centralScalar_mul F⟩

end

end S_NumberField_AdelicHeight_adelicHeight_unipotentGL2_mul_and_centralScalar_mul
end P2MW
export P2MW.S_NumberField_AdelicHeight_adelicHeight_unipotentGL2_mul_and_centralScalar_mul (solution)
