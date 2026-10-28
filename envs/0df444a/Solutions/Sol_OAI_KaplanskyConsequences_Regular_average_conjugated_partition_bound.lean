-- Prove2me | solution 1 for OAI.KaplanskyConsequences.Regular.average_conjugated_partition_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T15:41:14.694616+00:00
-- url     : https://prove2.me/submissions/9f87af85-e283-4dd6-98b1-60d186aca826

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_KaplanskyStableFiniteness
import Definitions.Def_OAIQ15Sf008

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_CStarEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences

universe u v w
open scoped ComplexOrder InnerProductSpace BigOperators WithCStarModule
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type u} [CStarAlgebra A] {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]

lemma norm_sum_mul_le (a b : ι → A) :
    ‖∑ i, a i * b i‖ ≤ Real.sqrt ‖∑ i, a i * star (a i)‖ *
      Real.sqrt ‖∑ i, star (b i) * b i‖ := by
  let x : C⋆ᵐᵒᵈ(A, ι → A) := WithCStarModule.equiv A _ |>.symm (fun i => star (b i))
  let y : C⋆ᵐᵒᵈ(A, ι → A) := WithCStarModule.equiv A _ |>.symm a
  have h := CStarModule.norm_inner_le (A:=A) (E:=C⋆ᵐᵒᵈ(A, ι → A)) (x:=x) (y:=y)
  simpa only [x,y,WithCStarModule.pi_inner,WithCStarModule.inner_def,
    WithCStarModule.pi_norm,WithCStarModule.equiv_symm_pi_apply,star_star,mul_comm] using h


end KaplanskyConsequences

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_RegularOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped ComplexOrder InnerProductSpace BigOperators ENNReal
attribute [local instance] Classical.propDecidable
variable {G H : Type*} [Group G] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

omit [Group G] [CompleteSpace H] in
lemma mask_norm_le (P : G → Prop) [DecidablePred P] : ‖mask (H:=H) P‖ ≤ 1 :=
  lp.norm_mapCLM_le _ _ _ _


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_FreeEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped ComplexOrder InnerProductSpace BigOperators ENNReal
attribute [local instance] Classical.propDecidable
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

lemma norm_disjoint_sum_le {E : Type*} [NormedAddCommGroup E] (T : ι → E) (P : ι → Prop)
    (hd : ∀ i j, P i → P j → i = j) {c : ℝ} (hc : 0 ≤ c) (hT : ∀ i, ‖T i‖ ≤ c) :
    ‖∑ i, if P i then T i else 0‖ ≤ c := by
  classical
  by_cases h : ∃ i, P i
  · obtain ⟨i,hi⟩ := h
    rw [Finset.sum_eq_single i]
    · simpa [hi] using hT i
    · intro j _ hji
      exact ite_eq_right (fun hj => hji (hd j i hj hi))
    · simp
  · simp only [not_exists] at h
    simpa [h] using hc


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_PowersOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped ComplexOrder InnerProductSpace BigOperators ENNReal
attribute [local instance 2000] Classical.propDecidable Classical.decEq
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {G H : Type*} [Group G] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

omit [Group G] [CompleteSpace H] in
lemma mask_compl (P : G → Prop) : mask (H:=H) (fun g => ¬P g) = 1-mask P := by
  ext x g
  simp only [mask_apply,sub_apply,one_apply_eq_self,lp.coeFn_sub,Pi.sub_apply]
  by_cases h : P g <;> simp [h]

omit [CompleteSpace H] in
lemma mask_left_conjugate (P : G → Prop) (g : G) :
    left (H:=H) g * mask P * left g⁻¹ = mask (fun w => P (g⁻¹*w)) := by
  ext x w
  simp only [mul_apply_eq_comp,left_apply,mask_apply,inv_inv]
  split_ifs <;> simp

omit [Group G] [CompleteSpace H] in
lemma sum_mask_norm_le (P : ι → G → Prop)
    (hd : ∀ i j g, P i g → P j g → i=j) : ‖∑ i, mask (H:=H) (P i)‖ ≤ 1 := by
  let U (g : G) : H →L[ℂ] H := ∑ i, if P i g then 1 else 0
  have hU (g : G) : ‖U g‖ ≤ 1 :=
    norm_disjoint_sum_le (fun _ => (1:H →L[ℂ] H)) (fun i => P i g)
      (fun i j => hd i j g) (by norm_num) (fun _ => ContinuousLinearMap.norm_id_le)
  have he : (∑ i, mask (H:=H) (P i)) = lp.mapCLM 2 U (by norm_num : (0:ℝ) ≤ 1) hU := by
    ext x g
    simp only [sum_apply,lp.coeFn_sum,Finset.sum_apply,mask_apply]
    change (∑ i, if P i g then x g else 0) = (U g) (x g)
    simp only [U,sum_apply]
    apply Finset.sum_congr rfl; intro i _
    split_ifs <;> rfl
  rw [he]
  exact lp.norm_mapCLM_le _ _ _ _

omit [Group G] in
lemma norm_sum_mul_mask_le (P : ι → G → Prop)
    (hd : ∀ i j g, P i g → P j g → i=j)
    (T : ι → HilbertSum G H →L[ℂ] HilbertSum G H) {c : ℝ}
    (hc : 0 ≤ c) (hT : ∀ i, ‖T i‖ ≤ c) :
    ‖∑ i, T i * mask (P i)‖ ≤ Real.sqrt (Fintype.card ι) * c := by
  have hsum : ‖∑ i, T i*star (T i)‖ ≤ (Fintype.card ι:ℝ)*c^2 := by
    calc
      _ ≤ ∑ i, ‖T i*star (T i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i : ι, c^2 := by
        apply Finset.sum_le_sum; intro i _
        rw [CStarRing.norm_self_mul_star (x := T i)]
        nlinarith [norm_nonneg (T i),hT i]
      _ = _ := by simp
  have hq : ‖∑ i, star (mask (H:=H) (P i))*mask (P i)‖ ≤ 1 := by
    simpa only [mask_star,mask_sq] using sum_mask_norm_le P hd
  calc
    _ ≤ Real.sqrt ‖∑ i, T i*star (T i)‖ * Real.sqrt ‖∑ i, star (mask (H:=H) (P i))*mask (P i)‖ :=
      norm_sum_mul_le _ _
    _ ≤ Real.sqrt ((Fintype.card ι:ℝ)*c^2) * Real.sqrt 1 :=
      mul_le_mul (Real.sqrt_le_sqrt hsum) (Real.sqrt_le_sqrt hq) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg _),Real.sqrt_sq hc,Real.sqrt_one,mul_one]

omit [CompleteSpace H] in
lemma left_norm_le (g : G) : ‖left (H:=H) g‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  exact le_of_eq ((reindex (Equiv.mulLeft g)).norm_map x |>.trans (one_mul _).symm)

lemma conjugate_norm_le (g : G) (T : HilbertSum G H →L[ℂ] HilbertSum G H) :
    ‖left g*T*left g⁻¹‖ ≤ ‖T‖ := by
  calc
    _ ≤ ‖left (H:=H) g‖ * ‖T‖ * ‖left (H:=H) g⁻¹‖ := norm_mul_le_of_le (norm_mul_le _ _) le_rfl
    _ ≤ 1 * ‖T‖ * 1 := mul_le_mul
      (mul_le_mul_of_nonneg_right (left_norm_le g) (norm_nonneg _)) (left_norm_le _)
      (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma powers_operator_estimate (D : G → Prop) (h : ι → G)
    (hd : ∀ i j g, ¬D ((h i)⁻¹*g) → ¬D ((h j)⁻¹*g) → i=j)
    (T : HilbertSum G H →L[ℂ] HilbertSum G H)
    (hT : mask D*T*mask D=0) :
    ‖∑ i, left (h i)*T*left (h i)⁻¹‖ ≤ 2 * Real.sqrt (Fintype.card ι) * ‖T‖ := by
  let X (i : ι) := left (h i)*T*left (h i)⁻¹
  let P (i : ι) := mask (H:=H) (fun g => D ((h i)⁻¹*g))
  let E (i : ι) := fun g => ¬D ((h i)⁻¹*g)
  let Q (i : ι) := mask (H:=H) (E i)
  have hpq (i : ι) : Q i = 1-P i := mask_compl _
  have hpxp (i : ι) : P i*X i*P i=0 := by
    simp only [P,X,←mask_left_conjugate]
    calc
      _ = left (h i)*(mask D*T*mask D)*left (h i)⁻¹ := by
        simp only [mul_assoc]
        rw [←mul_assoc (left (h i)⁻¹), ←left_mul,inv_mul_cancel,left_one,one_mul]
        rw [←mul_assoc (left (h i)⁻¹), ←left_mul,inv_mul_cancel,left_one,one_mul]
      _ = 0 := by rw [hT]; simp
  have hsplit (i : ι) : X i = X i*Q i + Q i*X i*P i := by
    rw [hpq]
    simp only [mul_sub,sub_mul,mul_one,one_mul,hpxp,sub_zero,sub_add_cancel]
  have hX (i : ι) : ‖X i‖ ≤ ‖T‖ := conjugate_norm_le _ _
  have hright : ‖∑ i, X i*Q i‖ ≤ Real.sqrt (Fintype.card ι)*‖T‖ :=
    by
      simpa only [Q] using norm_sum_mul_mask_le E hd X (norm_nonneg _) hX
  have hleft : ‖∑ i, Q i*X i*P i‖ ≤ Real.sqrt (Fintype.card ι)*‖T‖ := by
    have he : (∑ i, Q i*X i*P i) = star (∑ i, star (P i)*star (X i)*Q i) := by
      rw [star_sum (R := HilbertSum G H →L[ℂ] HilbertSum G H)
        Finset.univ (fun index => star (P index) * star (X index) * Q index)]
      simp only [star_mul,star_star,Q,mask_star,mul_assoc]
    rw [he,norm_star (∑ i, star (P i)*star (X i)*Q i)]
    apply norm_sum_mul_mask_le E hd _ (norm_nonneg _)
    intro i
    calc
      ‖star (P i)*star (X i)‖ ≤ ‖P i‖*‖X i‖ := by simpa only [norm_star (P i),norm_star (X i)] using norm_mul_le (star (P i)) (star (X i))
      _ ≤ 1*‖T‖ := mul_le_mul (mask_norm_le _) (hX i) (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  change ‖∑ i, X i‖ ≤ _
  calc
    _ = ‖(∑ i, X i*Q i)+(∑ i, Q i*X i*P i)‖ := by rw [←Finset.sum_add_distrib]; congr 1; exact Finset.sum_congr rfl (fun i _ => hsplit i)
    _ ≤ ‖∑ i, X i*Q i‖+‖∑ i, Q i*X i*P i‖ := norm_add_le _ _
    _ ≤ _ := by linarith


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_PowersAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped BigOperators InnerProductSpace ENNReal
attribute [local instance 2000] Classical.propDecidable Classical.decEq
variable {G : Type*} [Group G]

lemma conjugateMap_val (g : G) (x : Algebra G) :
    (conjugateMap g x).val = left g*x.val*left g⁻¹ := rfl
lemma conjugateMap_norm_le (g : G) (x : Algebra G) :
    ‖conjugateMap g x‖ ≤ ‖x‖ := conjugate_norm_le g x.val
lemma conjugateMap_mul (g h : G) (x : Algebra G) :
    conjugateMap (g*h) x = conjugateMap g (conjugateMap h x) := by
  apply Subtype.ext
  simp only [conjugateMap_val,mul_inv_rev,left_mul,mul_assoc]

lemma averageConjugate_apply {N : ℕ} (h : Fin N → G) (x : Algebra G) :
    averageConjugate h x = (N:ℂ)⁻¹ • ∑ i, conjugateMap (h i) x := by
  change (N:ℂ)⁻¹ • ((∑ i, conjugateMap (h i)) : Algebra G →ₗ[ℂ] Algebra G) x = _
  rw [LinearMap.sum_apply]

@[simp] lemma averageConjugate_one {N : ℕ} (hN : 0<N) (h : Fin N → G) :
    averageConjugate h (1:Algebra G) = 1 := by
  rw [averageConjugate_apply]
  simp only [conjugateMap_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  rw [←Nat.cast_smul_eq_nsmul ℂ,smul_smul,inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)),one_smul]

lemma averageConjugate_val {N : ℕ} (h : Fin N → G) (x : Algebra G) :
    (averageConjugate h x).val = (N:ℂ)⁻¹ • ∑ i, left (h i)*x.val*left (h i)⁻¹ := by
  rw [averageConjugate_apply]
  change (Algebra G).subtype ((N:ℂ)⁻¹ • ∑ i, conjugateMap (h i) x) = _
  simp only [map_smul,map_sum]
  rfl


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_PowersAverageBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped BigOperators InnerProductSpace ENNReal
attribute [local instance 2000] Classical.propDecidable Classical.decEq
variable {G : Type*} [Group G]

lemma averageConjugate_norm_eq {N : ℕ} (h : Fin N → G) (x : Algebra G) :
    ‖averageConjugate h x‖ = (N:ℝ)⁻¹ * ‖∑ i, left (h i)*x.val*left (h i)⁻¹‖ := by
  change ‖(averageConjugate h x).val‖ = _
  rw [averageConjugate_val,norm_smul,norm_inv,Complex.norm_natCast]

lemma averageConjugate_mul {N : ℕ} (h : Fin N → G) (u : G) (x : Algebra G) :
    averageConjugate (fun i => h i*u) x = averageConjugate h (conjugateMap u x) := by
  rw [averageConjugate_apply,averageConjugate_apply]
  congr 1
  exact Finset.sum_congr rfl (fun i hi => conjugateMap_mul _ _ _)

lemma average_partition_bound {N : ℕ} (D : G → Prop) (h : Fin N → G)
    (hd : ∀ i j w, ¬D ((h i)⁻¹*w) → ¬D ((h j)⁻¹*w) → i=j)
    (x : Algebra G) (hT : mask D*x.val*mask D=0) :
    ‖averageConjugate h x‖ ≤ (N:ℝ)⁻¹*(2*Real.sqrt N*‖x‖) := by
  rw [averageConjugate_norm_eq]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  have he := powers_operator_estimate D h hd x.val hT
  rw [Fintype.card_fin] at he
  exact he

lemma average_conjugated_partition_bound_oai {N : ℕ} (D : G → Prop) (h : Fin N → G)
    (hd : ∀ i j w, ¬D ((h i)⁻¹*w) → ¬D ((h j)⁻¹*w) → i=j)
    (u : G) (x : Algebra G) (hT : mask D*(conjugateMap u x).val*mask D=0) :
    ‖averageConjugate (fun i => h i*u) x‖ ≤ (N:ℝ)⁻¹*(2*Real.sqrt N*‖x‖) := by
  rw [averageConjugate_mul]
  apply (average_partition_bound D h hd (conjugateMap u x) hT).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact mul_le_mul_of_nonneg_left (conjugateMap_norm_le _ _) (by positivity)


end KaplanskyConsequences.Regular

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KaplanskyConsequences.Regular.average_conjugated_partition_bound_oai.{u_1} := @OAI.KaplanskyConsequences.Regular.average_conjugated_partition_bound_oai.{u_1}
