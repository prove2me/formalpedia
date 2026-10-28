-- Prove2me | solution 1 for OAI.Kadison.RectangularColumn.column_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:06:47.345507+00:00
-- url     : https://prove2.me/submissions/d0bd0737-e32e-4e77-8df1-23a2b372294e

import Mathlib
import Definitions.Def_OAIQ039C030
import Theorems.Thm_OAI_Kadison_ColumnModule_hom_column_sq

section
-- module Solutions.OAIQ039_CM.Commutator_CyclicMatrix
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder InnerProductSpace

namespace Kadison.CyclicColumns

variable {A H F ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] [Fintype ι]

lemma columnNorm_sq (v : ι → A) :
    columnNorm v ^ 2 = ‖∑ i, star (v i)*v i‖ := by
  rw [columnNorm,WithCStarModule.pi_norm_sq]
  simp only [WithCStarModule.equiv_symm_pi_apply,WithCStarModule.inner_def,star_star]

lemma columnNorm_nonneg (v : ι → A) : 0 ≤ columnNorm v := norm_nonneg _

end Kadison.CyclicColumns

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_RectangularColumn
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

namespace Kadison.RectangularColumn

variable {A K F : Type*} [CStarAlgebra A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma triangularMap_norm_le (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (lam : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (D : A →L[ℂ] (K →L[ℂ] F))
    (hD : ∀ a, ‖D a‖≤‖a‖) (a : A) : ‖triangularMap σ lam D a‖≤2*‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have hl : ‖lam a x.fst‖≤‖a‖*‖x.fst‖ :=
    ((lam a).le_opNorm _).trans (mul_le_mul_of_nonneg_right
      (NonUnitalStarAlgHom.norm_apply_le lam a) (norm_nonneg _))
  have hs : ‖σ a x.snd‖≤‖a‖*‖x.snd‖ :=
    ((σ a).le_opNorm _).trans (mul_le_mul_of_nonneg_right
      (NonUnitalStarAlgHom.norm_apply_le σ a) (norm_nonneg _))
  have hd : ‖WithLp.toLp 2 (lam a x.fst,σ a x.snd)‖≤‖a‖*‖x‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2,mul_pow,WithLp.prod_norm_sq_eq_of_L2]
    change ‖lam a x.fst‖^2+‖σ a x.snd‖^2≤
      ‖a‖^2*(‖x.fst‖^2+‖x.snd‖^2)
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) hl 2,
      pow_le_pow_left₀ (norm_nonneg _) hs 2]
  have ho : ‖WithLp.toLp 2 (D a x.snd,(0:K))‖≤‖a‖*‖x‖ := by
    rw [WithLp.norm_toLp_fst]
    exact ((D a).le_opNorm _).trans (mul_le_mul (hD a) (WithLp.norm_snd_le F x)
      (norm_nonneg _) (norm_nonneg _))
  have he : triangularMap σ lam D a x=
      WithLp.toLp 2 (lam a x.fst,σ a x.snd)+WithLp.toLp 2 (D a x.snd,(0:K)) := by
    apply (WithLp.equiv 2 (F × K)).injective
    exact Prod.ext rfl (by simp)
  rw [he]
  exact (norm_add_le _ _).trans (by linarith)

lemma normalized_column_sq {ι : Type*} [Fintype ι]
    (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (lam : A →⋆ₐ[ℂ] (F →L[ℂ] F))
    (D : A →L[ℂ] (K →L[ℂ] F))
    (hD : ∀ a b, D (a*b)=(D a).comp (σ b)+(lam a).comp (D b))
    (hn : ∀ a, ‖D a‖≤‖a‖) (a : ι → A) (ξ : K) :
    ∑ i, ‖D (a i) ξ‖^2 ≤ 16*‖ξ‖^2*‖∑ i,star (a i)*a i‖ := by
  have h := ColumnModule.hom_column_sq (triangularHom σ lam D hD)
    (M:=2) (by norm_num) (triangularMap_norm_le σ lam D hn) a
    (WithLp.toLp 2 ((0:F),ξ))
  simp only [WithLp.norm_toLp_snd] at h
  norm_num only [show (2:ℝ)^4=16 by norm_num] at h
  refine (Finset.sum_le_sum (fun i _ => ?_)).trans h
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  have hh := WithLp.norm_fst_le F ((triangularHom σ lam D hD) (a i)
    (WithLp.toLp 2 ((0:F),ξ)))
  simpa using hh

attribute [local instance] OAI.Kadison.RectangularColumn.instNormedAddCommGroupContinuousLinearMapComplexId_solutions
attribute [local instance] OAI.Kadison.RectangularColumn.instNormedSpaceComplexContinuousLinearMapId_solutions
theorem column_sq {ι : Type*} [Fintype ι]
    (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (lam : A →⋆ₐ[ℂ] (F →L[ℂ] F))
    (Δ : A →L[ℂ] (K →L[ℂ] F))
    (hΔ : ∀ a b, Δ (a*b)=(Δ a).comp (σ b)+(lam a).comp (Δ b))
    (a : ι → A) (ξ : K) :
    ∑ i, ‖Δ (a i) ξ‖^2 ≤ 16*‖Δ‖^2*‖ξ‖^2*‖∑ i,star (a i)*a i‖ := by
  by_cases hz : Δ=0
  · rw [hz]
    simp only [zero_apply,norm_zero,zero_pow (by norm_num : 2≠0),Finset.sum_const_zero,
      mul_zero,zero_mul]
    positivity
  have hd : 0<‖Δ‖ := norm_pos_iff.mpr hz
  let D : A →L[ℂ] (K →L[ℂ] F) := ‖Δ‖⁻¹ • Δ
  have hD (a b : A) : D (a*b)=(D a).comp (σ b)+(lam a).comp (D b) := by
    simp only [D,smul_apply,hΔ,smul_add,ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.comp_smul]
  have hn (a : A) : ‖D a‖≤‖a‖ := by
    simp only [D,smul_apply,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hd)]
    calc
      _ ≤ ‖Δ‖⁻¹*(‖Δ‖*‖a‖) := mul_le_mul_of_nonneg_left (Δ.le_opNorm a) (by positivity)
      _ = ‖a‖ := by rw [←mul_assoc,inv_mul_cancel₀ hd.ne',one_mul]
  have h := normalized_column_sq σ lam D hD hn a ξ
  have he (i : ι) : Δ (a i) ξ=‖Δ‖ • D (a i) ξ := by
    simp only [D,smul_apply,smul_smul,mul_inv_cancel₀ hd.ne',one_smul]
  calc
    _ = ‖Δ‖^2 * ∑ i, ‖D (a i) ξ‖^2 := by
      simp only [he,norm_smul,Real.norm_eq_abs,abs_norm,mul_pow,Finset.mul_sum]
    _ ≤ ‖Δ‖^2*(16*‖ξ‖^2*‖∑ i,star (a i)*a i‖) :=
      mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ = _ := by ring

theorem column_bound_oai [PartialOrder A] [StarOrderedRing A] {ι : Type*} [Fintype ι]
    (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (lam : A →⋆ₐ[ℂ] (F →L[ℂ] F))
    (Δ : A →L[ℂ] (K →L[ℂ] F))
    (hΔ : ∀ a b, Δ (a*b)=(Δ a).comp (σ b)+(lam a).comp (Δ b))
    (a : ι → A) (ξ : K) :
    ‖WithLp.toLp 2 (fun i => Δ (a i) ξ)‖≤
      (4*‖Δ‖)*CyclicColumns.columnNorm a*‖ξ‖ := by
  have hn := CyclicColumns.columnNorm_nonneg a
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  have h := column_sq σ lam Δ hΔ a ξ
  rw [←CyclicColumns.columnNorm_sq a] at h
  calc
    _ ≤ 16*‖Δ‖^2*‖ξ‖^2*CyclicColumns.columnNorm a^2 := h
    _ = _ := by ring

end Kadison.RectangularColumn

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Kadison.RectangularColumn.column_bound_oai.{u_1, u_2, u_3, u_4} := @OAI.Kadison.RectangularColumn.column_bound_oai.{u_1, u_2, u_3, u_4}
