-- Prove2me | solution 1 for Matrix.GeneralLinearGroup.exists_isCompact_forall_conj_mem_of_conj_mul_self_mem_of_trace_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/2f78212a-c423-5aaa-9b37-efc25f6ccfb5

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_GeneralLinearGroup_exists_isCompact_forall_conj_mem_of_conj_mul_self_mem_of_trace_ne_zero

set_option autoImplicit false

namespace CHUniformBound

open Matrix

variable {𝕜 : Type*} [Field 𝕜]

theorem sq_eq (t : Matrix (Fin 2) (Fin 2) 𝕜) :
    t * t = Matrix.trace t • t - Matrix.det t • (1 : Matrix (Fin 2) (Fin 2) 𝕜) := by
  ext i j
  rw [Matrix.trace_fin_two, Matrix.det_fin_two]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> ring

theorem conj_eq (t x xinv : Matrix (Fin 2) (Fin 2) 𝕜) (hx : xinv * x = 1) (ht : Matrix.trace t ≠ 0) :
    xinv * t * x =
      (Matrix.trace t)⁻¹ • (xinv * (t * t) * x + Matrix.det t • (1 : Matrix (Fin 2) (Fin 2) 𝕜)) := by
  have e : t = (Matrix.trace t)⁻¹ • (t * t + Matrix.det t • (1 : Matrix (Fin 2) (Fin 2) 𝕜)) := by
    rw [sq_eq, sub_add_cancel, smul_smul, inv_mul_cancel₀ ht, one_smul]
  conv_lhs => rw [e]
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, hx]

theorem trace_inv_val (t : GL (Fin 2) 𝕜) :
    Matrix.trace (((t⁻¹ : GL (Fin 2) 𝕜)) : Matrix (Fin 2) (Fin 2) 𝕜) =
      Matrix.trace ((t : GL (Fin 2) 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜) /
        Matrix.det ((t : GL (Fin 2) 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜) := by
  have hdet : Matrix.det ((t : GL (Fin 2) 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜) ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 t.isUnit).ne_zero
  have hinv : (((t⁻¹ : GL (Fin 2) 𝕜)) : Matrix (Fin 2) (Fin 2) 𝕜) = ((t : GL (Fin 2) 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜)⁻¹ :=
    (Matrix.coe_units_inv t)
  rw [hinv, Matrix.inv_def, Matrix.trace_smul, Matrix.adjugate_fin_two, Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Ring.inverse_eq_inv', smul_eq_mul]
  rw [div_eq_inv_mul, add_comm]

end CHUniformBound

open CHUniformBound in
theorem solution
    {𝕜 : Type*} [RCLike 𝕜]
    (T : Set (GL (Fin 2) 𝕜)) (hT : IsCompact T)
    (hTtr : ∀ t ∈ T, Matrix.trace ((t : GL (Fin 2) 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜) ≠ 0)
    (B : Set (GL (Fin 2) 𝕜)) (hB : IsCompact B) :
    ∃ B' : Set (GL (Fin 2) 𝕜), IsCompact B' ∧
      ∀ t ∈ T, ∀ x : GL (Fin 2) 𝕜, x⁻¹ * (t * t) * x ∈ B → x⁻¹ * t * x ∈ B' := by

  set val : GL (Fin 2) 𝕜 → Matrix (Fin 2) (Fin 2) 𝕜 := fun g => (g : Matrix (Fin 2) (Fin 2) 𝕜) with hval
  have hcval : Continuous val := Units.continuous_val
  have hcinv : Continuous fun g : GL (Fin 2) 𝕜 => g⁻¹ := continuous_inv

  set V : GL (Fin 2) 𝕜 × GL (Fin 2) 𝕜 → Matrix (Fin 2) (Fin 2) 𝕜 := fun p =>
    (Matrix.trace (val p.1))⁻¹ • (val p.2 + Matrix.det (val p.1) • (1 : Matrix (Fin 2) (Fin 2) 𝕜)) with hV
  set W : GL (Fin 2) 𝕜 × GL (Fin 2) 𝕜 → Matrix (Fin 2) (Fin 2) 𝕜 := fun p =>
    (Matrix.trace (val p.1⁻¹))⁻¹ • (val p.2⁻¹ + Matrix.det (val p.1⁻¹) • (1 : Matrix (Fin 2) (Fin 2) 𝕜)) with hW
  have htr : Continuous fun m : Matrix (Fin 2) (Fin 2) 𝕜 => Matrix.trace m := by
    have : (fun m : Matrix (Fin 2) (Fin 2) 𝕜 => Matrix.trace m) = fun m => m 0 0 + m 1 1 := by
      funext m; rw [Matrix.trace_fin_two]
    rw [this]; fun_prop
  have hdetc : Continuous fun m : Matrix (Fin 2) (Fin 2) 𝕜 => Matrix.det m := continuous_id.matrix_det
  have hTtr' : ∀ p ∈ T ×ˢ B, Matrix.trace (val p.1) ≠ 0 := fun p hp => hTtr p.1 hp.1
  have hTtr'' : ∀ p ∈ T ×ˢ B, Matrix.trace (val p.1⁻¹) ≠ 0 := by
    intro p hp
    show Matrix.trace (((p.1⁻¹ : GL (Fin 2) 𝕜)) : Matrix (Fin 2) (Fin 2) 𝕜) ≠ 0
    rw [trace_inv_val]
    exact div_ne_zero (hTtr p.1 hp.1) ((Matrix.isUnit_iff_isUnit_det _).1 p.1.isUnit).ne_zero
  have hVc : ContinuousOn V (T ×ˢ B) := by
    refine ContinuousOn.fun_smul ?_ ?_
    · exact ((htr.comp (hcval.comp continuous_fst)).continuousOn).inv₀ hTtr'
    · exact ((hcval.comp continuous_snd).add
        ((hdetc.comp (hcval.comp continuous_fst)).smul continuous_const)).continuousOn
  have hWc : ContinuousOn W (T ×ˢ B) := by
    refine ContinuousOn.fun_smul ?_ ?_
    · exact ((htr.comp (hcval.comp (hcinv.comp continuous_fst))).continuousOn).inv₀ hTtr''
    · exact ((hcval.comp (hcinv.comp continuous_snd)).add
        ((hdetc.comp (hcval.comp (hcinv.comp continuous_fst))).smul continuous_const)).continuousOn
  have hTB : IsCompact (T ×ˢ B) := hT.prod hB
  set M₁ := V '' (T ×ˢ B) with hM₁
  set M₂ := W '' (T ×ˢ B) with hM₂
  have hM₁ : IsCompact M₁ := hTB.image_of_continuousOn hVc
  have hM₂ : IsCompact M₂ := hTB.image_of_continuousOn hWc

  set B' : Set (GL (Fin 2) 𝕜) :=
    (Units.embedProduct (Matrix (Fin 2) (Fin 2) 𝕜)) ⁻¹' (M₁ ×ˢ (MulOpposite.op '' M₂)) with hB'
  have hB'c : IsCompact B' :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage (hM₁.prod (hM₂.image MulOpposite.continuous_op))
  refine ⟨B', hB'c, fun t ht x hx => ?_⟩
  have hx1 : val x⁻¹ * val x = 1 := by
    show (((x⁻¹ : GL (Fin 2) 𝕜)) : Matrix (Fin 2) (Fin 2) 𝕜) * (x : Matrix (Fin 2) (Fin 2) 𝕜) = 1
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine ⟨⟨(t, x⁻¹ * (t * t) * x), ⟨ht, hx⟩, ?_⟩, ⟨W (t, x⁻¹ * (t * t) * x), ⟨_, ⟨ht, hx⟩, rfl⟩, ?_⟩⟩
  ·
    show V (t, x⁻¹ * (t * t) * x) = ((x⁻¹ * t * x : GL (Fin 2) 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜)
    simp only [hV, hval, Units.val_mul]
    exact (conj_eq _ _ _ hx1 (hTtr t ht)).symm
  ·
    show MulOpposite.op (W (t, x⁻¹ * (t * t) * x)) = MulOpposite.op (((x⁻¹ * t * x)⁻¹ : GL (Fin 2) 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜)
    congr 1
    have e1 : (x⁻¹ * t * x)⁻¹ = x⁻¹ * t⁻¹ * x := by group
    have e2 : (x⁻¹ * (t * t) * x)⁻¹ = x⁻¹ * (t⁻¹ * t⁻¹) * x := by group
    rw [e1]
    simp only [hW, hval, e2, Units.val_mul]
    exact (conj_eq _ _ _ hx1 (hTtr'' (t, x⁻¹ * (t * t) * x) ⟨ht, hx⟩)).symm

end S_Matrix_GeneralLinearGroup_exists_isCompact_forall_conj_mem_of_conj_mul_self_mem_of_trace_ne_zero
end P2MW
export P2MW.S_Matrix_GeneralLinearGroup_exists_isCompact_forall_conj_mem_of_conj_mul_self_mem_of_trace_ne_zero (solution)
