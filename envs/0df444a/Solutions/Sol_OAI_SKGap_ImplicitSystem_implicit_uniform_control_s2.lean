-- Prove2me | solution 1 for OAI.SKGap.ImplicitSystem.implicit_uniform_control_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:53:38.669246+00:00
-- url     : https://prove2.me/submissions/08d9f20b-ef49-498c-bb49-7cfa5cce97d7

import Mathlib
import Definitions.Def_OAIQ072A000

section
-- module Solutions.OAIQ074_CM.SKGap_Stability_ImplicitLinear
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.ImplicitLinear
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma lower_norm_of_quadratic (M : E →L[ℝ] E) {c : ℝ}
    (h : ∀v,c*‖v‖^2 ≤ ⟪v, M v⟫) (v : E) : c*‖v‖≤‖M v‖ := by
  by_cases hv : ‖v‖=0
  · simp [hv]
  have hn : 0<‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
  have H:=(h v).trans (real_inner_le_norm v (M v))
  nlinarith

lemma quadratic_perturbation (M S : E →L[ℝ] E) {c e : ℝ}
    (hS : ∀v,c*‖v‖^2 ≤ ⟪v, S v⟫) (hMS : ‖M-S‖≤e) (v : E) :
    (c-e)*‖v‖^2 ≤ ⟪v, M v⟫ := by
  have hI:=abs_real_inner_le_norm v ((M-S) v)
  have hO:=(M-S).le_opNorm v
  have hm:=mul_le_mul_of_nonneg_right hMS (norm_nonneg v)
  have hh:=mul_le_mul_of_nonneg_left (hO.trans hm) (norm_nonneg v)
  have he : ⟪v, (M-S) v⟫=⟪v, M v⟫-⟪v, S v⟫ := by simp only [sub_apply,inner_sub_right]
  rw [he] at hI
  have H := (neg_abs_le (⟪v, M v⟫-⟪v, S v⟫)).trans (le_refl _)
  nlinarith [hS v]

lemma injective_of_lower_norm (M : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (h : ∀v,c*‖v‖≤‖M v‖) : Function.Injective M := by
  intro x y hxy
  have H:=h (x-y)
  have he : M (x-y)=0 := by simp [hxy]
  rw [he,norm_zero] at H
  have hz : ‖x-y‖=0 := by nlinarith [norm_nonneg (x-y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

variable [FiniteDimensional ℝ E]

theorem exists_bounded_inverse (M S : E →L[ℝ] E) {c e : ℝ}
    (hce : e < c) (hS : ∀v,c*‖v‖^2 ≤ ⟪v, S v⟫) (hMS : ‖M-S‖≤e) :
    ∃ N : E →L[ℝ] E,M*N=1 ∧ N*M=1 ∧ ‖N‖≤(c-e)⁻¹ := by
  have hc : 0 < c-e := sub_pos.mpr hce
  have hlow : ∀v,(c-e)*‖v‖≤‖M v‖ :=
    lower_norm_of_quadratic M (quadratic_perturbation M S hS hMS)
  have hinj := injective_of_lower_norm M hc hlow
  let L : E ≃ₗ[ℝ] E := LinearEquiv.ofBijective M.toLinearMap
    ⟨hinj,LinearMap.injective_iff_surjective.mp hinj⟩
  let N : E →L[ℝ] E := L.symm.toLinearMap.toContinuousLinearMap
  have hMN : M*N=1 := by
    ext x; exact L.apply_symm_apply x
  have hNM : N*M=1 := by
    ext x; exact L.symm_apply_apply x
  refine ⟨N,hMN,hNM,N.opNorm_le_bound (inv_nonneg.mpr hc.le) ?_⟩
  intro x
  have H:=hlow (N x)
  have hx : M (N x)=x := by change (M*N) x=x; rw [hMN]; rfl
  rw [hx] at H
  exact (le_div_iff₀ hc).2 (by nlinarith) |>.trans_eq (by ring)

end SKGap.ImplicitLinear

namespace SKGap.ImplicitLinear
variable {R : Type*} [Ring R]

lemma jacobson_left (X Y N : R) (hN : (1+Y*X)*N=1) :
    (1+X*Y)*(1-X*N*Y)=1 := by
  calc
    _ = 1+X*(1-(1+Y*X)*N)*Y := by noncomm_ring
    _ = 1 := by rw [hN]; simp

lemma jacobson_right (X Y N : R) (hN : N*(1+Y*X)=1) :
    (1-X*N*Y)*(1+X*Y)=1 := by
  calc
    _ = 1+X*(1-N*(1+Y*X))*Y := by noncomm_ring
    _ = 1 := by rw [hN]; simp

end SKGap.ImplicitLinear

namespace SKGap.ImplicitLinear
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem unnormalized_inverse (X L S : E →L[ℝ] E) {c e : ℝ}
    (hce : e < c) (hS : ∀v,c*‖v‖^2 ≤ ⟪v, S v⟫)
    (hMS : ‖(1+X*L*X)-S‖≤e) :
    ∃ B : E →L[ℝ] E,(1+X*X*L)*B=1 ∧ B*(1+X*X*L)=1 ∧
      ‖B‖≤1+‖X‖^2*(c-e)⁻¹*‖L‖ := by
  obtain ⟨N,hN,hN',hNb⟩ := exists_bounded_inverse (1+X*L*X) S hce hS hMS
  let B:=1-X*N*(X*L)
  refine ⟨B,?_,?_,?_⟩
  · simpa only [B,mul_assoc] using jacobson_left X (X*L) N hN
  · simpa only [B,mul_assoc] using jacobson_right X (X*L) N hN'
  · calc
      ‖B‖ ≤ ‖(1 : E →L[ℝ] E)‖+‖X*N*(X*L)‖ := norm_sub_le _ _
      _ ≤ 1+‖X‖*‖N‖*(‖X‖*‖L‖) := by
        apply add_le_add (ContinuousLinearMap.norm_id_le)
        exact (norm_mul_le _ _).trans (mul_le_mul (norm_mul_le _ _) (norm_mul_le _ _)
          (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
      _ ≤ 1+‖X‖*(c-e)⁻¹*(‖X‖*‖L‖) := by
        gcongr
      _ = _ := by ring

end SKGap.ImplicitLinear

end
end

section

noncomputable section
namespace SKGap.ImplicitSystem
open SKGap.ImplicitLinear
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma rank_add_right (u v w : E) : rank u (v+w)=rank u v+rank u w := by
  ext x; simp only [rank_apply,inner_add_left,add_smul,add_apply]

lemma rank_sub_left (u v w : E) : rank (u-v) w=rank u w-rank v w := by
  ext x; simp only [rank_apply,smul_sub,sub_apply]

lemma rank_smul_left (a : ℝ) (u v : E) : rank (a • u) v=a • rank u v := by
  ext x; simp only [rank_apply,smul_apply]; module

lemma rank_norm_le (u v : E) : ‖rank u v‖≤‖u‖*‖v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro x
  simp only [rank_apply,norm_smul,Real.norm_eq_abs]
  calc
    _ ≤ (‖v‖*‖x‖)*‖u‖ := mul_le_mul_of_nonneg_right (abs_real_inner_le_norm v x) (norm_nonneg _)
    _ = _ := by ring

lemma rank_perturbation (v ell m : E) :
    rank v ell+(2:ℝ) • rank m m=rank (v-(2:ℝ) • m) ell+(2:ℝ) • rank m (ell+m) := by
  rw [rank_sub_left,rank_smul_left,rank_add_right,smul_add]
  module

lemma rank_perturbation_bound (v ell m : E) :
    ‖rank v ell+(2:ℝ) • rank m m‖≤‖v-(2:ℝ) • m‖*‖ell‖+2*‖m‖*‖ell+m‖ := by
  rw [rank_perturbation]
  calc
    _ ≤ ‖rank (v-(2:ℝ) • m) ell‖+‖(2:ℝ) • rank m (ell+m)‖ := norm_add_le _ _
    _ ≤ ‖v-(2:ℝ) • m‖*‖ell‖+2*(‖m‖*‖ell+m‖) := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)]
      exact add_le_add (rank_norm_le _ _) (mul_le_mul_of_nonneg_left (rank_norm_le _ _) (by norm_num))
    _ = _ := by ring

lemma normalized_difference (j χ b r : ℝ) (X J : E →L[ℝ] E) (v ell m : E) :
    (1+X*L₂ j χ r J v ell*X)-stableMatrix j b r X J m=
      (j*(χ-b)) • (X*X)+(j*r) • (X*(rank v ell+(2:ℝ) • rank m m)*X) := by
  simp only [L₂,stableMatrix,mul_add,add_mul,mul_neg,neg_mul,mul_smul_comm,
    smul_mul_assoc,mul_one,smul_add,smul_smul]
  module

lemma normalized_difference_bound (j χ b r : ℝ) (X J : E →L[ℝ] E) (v ell m : E) :
    ‖(1+X*L₂ j χ r J v ell*X)-stableMatrix j b r X J m‖≤
      |j| * |χ-b| * ‖X‖^2+|j*r| * ‖X‖^2*(‖v-(2:ℝ) • m‖*‖ell‖+2*‖m‖*‖ell+m‖) := by
  rw [normalized_difference]
  calc
    _ ≤ ‖(j*(χ-b)) • (X*X)‖+‖(j*r) • (X*(rank v ell+(2:ℝ) • rank m m)*X)‖ := norm_add_le _ _
    _ ≤ |j| * |χ-b| * (‖X‖*‖X‖)+|j*r| * (‖X‖*(‖v-(2:ℝ) • m‖*‖ell‖+2*‖m‖*‖ell+m‖)*‖X‖) := by
      simp only [norm_smul,Real.norm_eq_abs,abs_mul]
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (norm_mul_le X X) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      · apply mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (rank_perturbation_bound v ell m) (norm_nonneg _)))
          (norm_nonneg _))
    _ = _ := by ring

lemma eliminated_equation (j χ r p : ℝ) (A J : E →L[ℝ] E) (u m t ell w : E) :
    Equations j χ r p A J u m t ell w
      (J w-(j*χ) • w-(j*(r*inner ℝ ell w+p)) • m) (r*inner ℝ ell w+p) ↔
      (1+A*L₂ j χ r J (m+t) ell) w=A (u-(j*p) • (m+t)) := by
  simp only [Equations,and_true,L₂,add_apply,smul_apply,neg_apply,one_apply_eq_self,
    mul_apply_eq_comp,rank_apply,map_add,map_sub,map_smul,map_neg]
  constructor <;> intro h <;> linear_combination (norm := module) h

end SKGap.ImplicitSystem

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Stability_ImplicitCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.ImplicitSystem
open SKGap.ImplicitLinear
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma eliminated_rhs_bound (A : E →L[ℝ] E) (j p : ℝ) (u m t : E) :
    ‖A (u-(j*p) • (m+t))‖≤‖A‖*(‖u‖+|j| *|p| *(‖m‖+‖t‖)) := by
  calc
    _ ≤ ‖A‖*‖u-(j*p) • (m+t)‖ := A.le_opNorm _
    _ ≤ ‖A‖*(‖u‖+‖(j*p) • (m+t)‖) := mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
    _ ≤ _ := by
      simp only [norm_smul,Real.norm_eq_abs,abs_mul]
      exact mul_le_mul_of_nonneg_left (add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left (norm_add_le m t) (mul_nonneg (abs_nonneg _) (abs_nonneg _)))) (norm_nonneg _)

lemma implicit_scalar_size (r p : ℝ) (ell w : E) :
    |r*inner ℝ ell w+p|≤|r| *‖ell‖*‖w‖+|p| := by
  calc
    _ ≤ |r*inner ℝ ell w|+|p| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul]
      nlinarith only [mul_le_mul_of_nonneg_left (abs_real_inner_le_norm ell w) (abs_nonneg r)]

lemma implicit_field_size (J : E →L[ℝ] E) (j χ c : ℝ) (w m : E) :
    ‖J w-(j*χ) • w-(j*c) • m‖≤(‖J‖+|j*χ|)*‖w‖+|j| *|c| *‖m‖ := by
  calc
    _ ≤ ‖J w-(j*χ) • w‖+‖(j*c) • m‖ := norm_sub_le _ _
    _ ≤ ‖J w‖+‖(j*χ) • w‖+‖(j*c) • m‖ := add_le_add (norm_sub_le _ _) (le_refl _)
    _ ≤ _ := by
      simp only [norm_smul,Real.norm_eq_abs,abs_mul]
      nlinarith only [J.le_opNorm w]

variable [FiniteDimensional ℝ E]

theorem implicit_size_bounds (j χ b r p : ℝ) (X J : E →L[ℝ] E)
    (u m t ell q w y : E) (c : ℝ) {δ : ℝ} (hδ : 0<δ)
    (hStable : ∀v,δ*‖v‖^2 ≤ inner ℝ v (stableMatrix j b r X J q v))
    (hSmall : |j| *|χ-b| *‖X‖^2+|j*r| *‖X‖^2*
      (‖m+t-(2:ℝ) • q‖*‖ell‖+2*‖q‖*‖ell+q‖)≤δ/2)
    (hEq : Equations j χ r p (X*X) J u m t ell w y c) :
    let W := (1+‖X‖^2*(δ/2)⁻¹*‖L₂ j χ r J (m+t) ell‖)*
      ‖X‖^2*(‖u‖+|j| *|p| *(‖m‖+‖t‖))
    ‖w‖≤W ∧ |c|≤|r| *‖ell‖*W+|p| ∧
      ‖y‖≤(‖J‖+|j*χ|)*W+|j| *(|r| *‖ell‖*W+|p|)*‖m‖ := by
  dsimp only
  let W := (1+‖X‖^2*(δ/2)⁻¹*‖L₂ j χ r J (m+t) ell‖)*
      ‖X‖^2*(‖u‖+|j| *|p| *(‖m‖+‖t‖))
  have hPert := (normalized_difference_bound j χ b r X J (m+t) ell q).trans hSmall
  obtain ⟨B,hMB,hBM,hB⟩ := unnormalized_inverse X (L₂ j χ r J (m+t) ell)
    (stableMatrix j b r X J q) (by linarith : δ/2<δ) hStable hPert
  have hw : (1+X*X*L₂ j χ r J (m+t) ell) w=(X*X) (u-(j*p) • (m+t)) := by
    apply (eliminated_equation j χ r p (X*X) J u m t ell w).mp
    rcases hEq with ⟨hw,hy,hc⟩
    refine ⟨?_,rfl,rfl⟩
    simpa only [←hc,←hy] using hw
  have hform : w=B ((X*X) (u-(j*p) • (m+t))) := by
    rw [←hw]
    change w=(B*(1+X*X*L₂ j χ r J (m+t) ell)) w
    rw [hBM]; rfl
  have hBB : ‖B‖≤1+‖X‖^2*(δ/2)⁻¹*‖L₂ j χ r J (m+t) ell‖ := by
    convert hB using 2
    all_goals try with_reducible_and_instances rfl
    congr 2
    ring
  have hwB : ‖w‖≤W := by
    calc
      ‖w‖=‖B ((X*X) (u-(j*p) • (m+t)))‖ := congrArg norm hform
      _ ≤ ‖B‖*‖(X*X) (u-(j*p) • (m+t))‖ := B.le_opNorm _
      _ ≤ ‖B‖*(‖X*X‖*(‖u‖+|j| *|p| *(‖m‖+‖t‖))) :=
        mul_le_mul_of_nonneg_left (eliminated_rhs_bound (X*X) j p u m t) (norm_nonneg _)
      _ ≤ W := by
        dsimp [W]
        have hX : ‖X*X‖≤‖X‖^2 := by simpa only [pow_two] using norm_mul_le X X
        have h0 : 0≤‖u‖+|j| *|p| *(‖m‖+‖t‖) := by positivity
        have hK : 0≤1+‖X‖^2*(δ/2)⁻¹*‖L₂ j χ r J (m+t) ell‖ := by positivity
        calc
          _ ≤ (1+‖X‖^2*(δ/2)⁻¹*‖L₂ j χ r J (m+t) ell‖)*
              (‖X‖^2*(‖u‖+|j| *|p| *(‖m‖+‖t‖))) :=
            mul_le_mul hBB (mul_le_mul_of_nonneg_right hX h0) (by positivity) hK
          _ = _ := by ring
  have hcB : |c|≤|r| *‖ell‖*W+|p| := by
    rw [hEq.2.2]
    exact (implicit_scalar_size r p ell w).trans
      (add_le_add (mul_le_mul_of_nonneg_left hwB (mul_nonneg (abs_nonneg _) (norm_nonneg _))) (le_refl _))
  refine ⟨hwB,hcB,?_⟩
  rw [hEq.2.1]
  apply (implicit_field_size J j χ c w m).trans
  exact add_le_add (mul_le_mul_of_nonneg_left hwB (by positivity))
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcB (abs_nonneg j)) (norm_nonneg m))

end SKGap.ImplicitSystem

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Stability_ImplicitFlip
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.ImplicitSystem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma equations_balance (j χ r p : ℝ) (A J : E →L[ℝ] E) (u m t ell w y : E) (c : ℝ)
    (h : Equations j χ r p A J u m t ell w y c) :
    w=A (u+J w-(j*χ) • w-(j*c) • (m+t)) := by
  rcases h with ⟨hw,hy,hc⟩
  calc
    w=A (u+y-(j*c) • t) := hw
    _=A (u+J w-(j*χ) • w-(j*c) • (m+t)) := by
      rw [hy]
      congr 1
      module

theorem implicit_difference_equation (j χ χ' r p p' : ℝ)
    (A A' J : E →L[ℝ] E) (u u' m m' t ell ell' w w' y y' : E) (c c' : ℝ)
    (h : Equations j χ r p A J u m t ell w y c)
    (h' : Equations j χ' r p' A' J u' m' t ell' w' y' c') :
    (1+A'*L₂ j χ' r J (m'+t) ell') (w-w')=
      (A-A') (u+J w-(j*χ) • w-(j*c) • (m+t))+
      A' (u-u')-(j*(χ-χ')) • A' w-(j*c) • A' (m-m')-
      (j*(r*inner ℝ (ell-ell') w+(p-p'))) • A' (m'+t) := by
  have hw:=equations_balance j χ r p A J u m t ell w y c h
  have hw':=equations_balance j χ' r p' A' J u' m' t ell' w' y' c' h'
  have hc:=h.2.2
  have hc':=h'.2.2
  simp only [L₂,add_apply,sub_apply,smul_apply,neg_apply,one_apply_eq_self,
    mul_apply_eq_comp,rank_apply,map_add,map_sub,map_smul,map_neg,inner_sub_left] at hw hw' ⊢
  rw [hc] at hw ⊢
  rw [hc'] at hw'
  linear_combination (norm := module) hw-hw'

theorem implicit_scaled_difference (s j χ χ' r p p' : ℝ)
    (A A' J : E →L[ℝ] E) (u u' m m' t ell ell' w w' y y' : E) (c c' : ℝ)
    (h : Equations j χ r p A J u m t ell w y c)
    (h' : Equations j χ' r p' A' J u' m' t ell' w' y' c') :
    (1+A'*L₂ j χ' r J (m'+t) ell') (s • (w-w'))=
      (s • (A-A')) (u+J w-(j*χ) • w-(j*c) • (m+t))+
      A' (s • (u-u'))-(j*(s*(χ-χ'))) • A' w-(j*c) • A' (s • (m-m'))-
      (j*(r*inner ℝ (s • (ell-ell')) w+s*(p-p'))) • A' (m'+t) := by
  have H:=congrArg (fun x:E=>s • x)
    (implicit_difference_equation j χ χ' r p p' A A' J u u' m m' t ell ell' w w' y y' c c' h h')
  simp only [map_smul,smul_apply,real_inner_smul_left] at H ⊢
  linear_combination (norm := module) H

lemma implicit_scalar_difference (s r p p' : ℝ) (ell ell' w w' : E) :
    s*(r*inner ℝ ell w+p-(r*inner ℝ ell' w'+p'))=
      r*inner ℝ (s • (ell-ell')) w+s*(p-p')+
        r*inner ℝ ell' (s • (w-w')) := by
  simp only [real_inner_smul_left,real_inner_smul_right,inner_sub_left,inner_sub_right]
  ring

end SKGap.ImplicitSystem

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.ImplicitSystem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]

omit [InnerProductSpace ℝ E] in
lemma columnNorm_nonneg (V : ι→E) : 0 ≤ columnNorm V := norm_nonneg _
omit [InnerProductSpace ℝ E] in
lemma columnNorm_sq (V : ι→E) : columnNorm V^2=∑i,‖V i‖^2 := by
  exact PiLp.norm_sq_eq_of_L2 (fun _ : ι=>E) (WithLp.toLp 2 V : PiLp 2 (fun _ : ι=>E))
omit [InnerProductSpace ℝ E] in
lemma columnNorm_add (U V : ι→E) : columnNorm (U+V) ≤ columnNorm U+columnNorm V :=
  norm_add_le (WithLp.toLp 2 U : PiLp 2 (fun _ : ι=>E)) (WithLp.toLp 2 V)
omit [InnerProductSpace ℝ E] in
lemma columnNorm_neg (V : ι→E) : columnNorm (-V)=columnNorm V := norm_neg _
omit [InnerProductSpace ℝ E] in
lemma columnNorm_sub (U V : ι→E) : columnNorm (U-V) ≤ columnNorm U+columnNorm V := by
  simpa only [sub_eq_add_neg,columnNorm_neg] using columnNorm_add U (-V)
lemma columnNorm_smul (a : ℝ) (V : ι→E) : columnNorm (a • V)=|a| *columnNorm V :=
  norm_smul a (WithLp.toLp 2 V : PiLp 2 (fun _ : ι=>E))
omit [InnerProductSpace ℝ E] in
lemma columnNorm_bound {U V : ι→E} {C : ℝ} (hC : 0≤C)
    (h : ∀i,‖U i‖≤C*‖V i‖) : columnNorm U≤C*columnNorm V := by
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hC (columnNorm_nonneg _))
  simp only [←sq,columnNorm_sq,mul_pow,Finset.mul_sum]
  exact Finset.sum_le_sum fun i _=>by simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg (U i)) (h i) 2
lemma columnNorm_operator (A : ι→E→L[ℝ]E) (V : ι→E) {C : ℝ}
    (hC : 0≤C) (hA : ∀i,‖A i‖≤C) :
    columnNorm (fun i=>A i (V i))≤C*columnNorm V := by
  apply columnNorm_bound hC
  intro i; exact ((A i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg _))
lemma columnNorm_vector_scalar (V : ι→E) (a : ι→ℝ) {C : ℝ}
    (hC : 0≤C) (hV : ∀i,‖V i‖≤C) :
    columnNorm (fun i=>a i • V i)≤C*columnNorm a := by
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hC (columnNorm_nonneg _))
  simp only [←sq,columnNorm_sq,norm_smul,Real.norm_eq_abs,mul_pow,Finset.mul_sum]
  exact Finset.sum_le_sum fun i _=>by
    have h:=pow_le_pow_left₀ (norm_nonneg (V i)) (hV i) 2
    nlinarith only [mul_le_mul_of_nonneg_left h (sq_nonneg |a i|)]

omit [InnerProductSpace ℝ E] in
lemma columnNorm_add_sub_sub_sub (a b c d e : ι→E) :
    columnNorm (a+b-c-d-e) ≤ columnNorm a+columnNorm b+columnNorm c+columnNorm d+columnNorm e := by
  have h₁:=columnNorm_add a b
  have h₂:=columnNorm_sub (a+b) c
  have h₃:=columnNorm_sub (a+b-c) d
  have h₄:=columnNorm_sub (a+b-c-d) e
  linarith

variable [FiniteDimensional ℝ E]

lemma column_inverse_estimate (X L S : ι→E→L[ℝ]E) (U V : ι→E)
    {δ X₀ L₀ : ℝ} (hδ : 0<δ) (hX₀ : 0≤X₀) (hL₀ : 0≤L₀)
    (hX : ∀i,‖X i‖≤X₀) (hL : ∀i,‖L i‖≤L₀)
    (hS : ∀i v,δ*‖v‖^2≤ inner ℝ v (S i v))
    (hPert : ∀i,‖(1+X i*L i*X i)-S i‖≤δ/2)
    (hEq : ∀i,(1+X i*X i*L i) (U i)=V i) :
    columnNorm U≤(1+X₀^2*(δ/2)⁻¹*L₀)*columnNorm V := by
  apply columnNorm_bound (by positivity)
  intro i
  obtain ⟨B,hMB,hBM,hB⟩:=SKGap.ImplicitLinear.unnormalized_inverse (X i) (L i) (S i)
    (by linarith : δ/2<δ) (hS i) (hPert i)
  have he : U i=B (V i) := by
    rw [←hEq i]
    change U i=(B*(1+X i*X i*L i)) (U i)
    rw [hBM]; rfl
  rw [he]
  apply (B.le_opNorm _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply hB.trans
  have hX2 : ‖X i‖^2≤X₀^2 := (sq_le_sq₀ (norm_nonneg _) hX₀).mpr (hX i)
  have hinv : 0≤(δ-δ/2)⁻¹ := inv_nonneg.mpr (by linarith)
  calc
    _ ≤ 1+X₀^2*(δ-δ/2)⁻¹*L₀ := add_le_add le_rfl
      (mul_le_mul (mul_le_mul_of_nonneg_right hX2 hinv) (hL i) (norm_nonneg _) (by positivity))
    _ = _ := by congr 2; ring

theorem implicit_columns_bound (j χ r p : ℝ) (X J : E→L[ℝ]E)
    (u m t ell w y : E) (c : ℝ)
    (s χ' p' c' : ι→ℝ) (X' : ι→E→L[ℝ]E) (u' m' ell' w' y' q' : ι→E) (b' : ι→ℝ)
    (h : Equations j χ r p (X*X) J u m t ell w y c)
    (h' : ∀i,Equations j (χ' i) r (p' i) (X' i*X' i) J (u' i) (m' i) t (ell' i) (w' i) (y' i) (c' i))
    {δ X₀ L₀ : ℝ} (hδ : 0<δ) (hX₀ : 0≤X₀) (hL₀ : 0≤L₀)
    (hX : ∀i,‖X' i‖≤X₀) (hL : ∀i,‖L₂ j (χ' i) r J (m' i+t) (ell' i)‖≤L₀)
    (hS : ∀i v,δ*‖v‖^2≤ inner ℝ v (stableMatrix j (b' i) r (X' i) J (q' i) v))
    (hSmall : ∀i,|j| *|χ' i-b' i| *‖X' i‖^2+|j*r| *‖X' i‖^2*
      (‖m' i+t-(2:ℝ) • q' i‖*‖ell' i‖+2*‖q' i‖*‖ell' i+q' i‖)≤δ/2) :
    let A:=X*X
    let A':=fun i=>X' i*X' i
    let B:=u+J w-(j*χ) • w-(j*c) • (m+t)
    let z:=fun i=>r*inner ℝ (s i • (ell-ell' i)) w+s i*(p-p' i)
    columnNorm (fun i=>s i • (w-w' i))≤(1+X₀^2*(δ/2)⁻¹*L₀)*
      (columnNorm (fun i=>(s i • (A-A' i)) B)+
        columnNorm (fun i=>A' i (s i • (u-u' i)))+
        columnNorm (fun i=>(j*(s i*(χ-χ' i))) • A' i w)+
        columnNorm (fun i=>(j*c) • A' i (s i • (m-m' i)))+
        columnNorm (fun i=>(j*z i) • A' i (m' i+t))) := by
  dsimp only
  let V:=fun i=>(s i • (X*X-X' i*X' i)) (u+J w-(j*χ) • w-(j*c) • (m+t))+
    (X' i*X' i) (s i • (u-u' i))-(j*(s i*(χ-χ' i))) • (X' i*X' i) w-
    (j*c) • (X' i*X' i) (s i • (m-m' i))-
    (j*(r*inner ℝ (s i • (ell-ell' i)) w+s i*(p-p' i))) • (X' i*X' i) (m' i+t)
  have hlow:=column_inverse_estimate X' (fun i=>L₂ j (χ' i) r J (m' i+t) (ell' i))
    (fun i=>stableMatrix j (b' i) r (X' i) J (q' i)) (fun i=>s i • (w-w' i)) V
    hδ hX₀ hL₀ hX hL hS
    (fun i=>(normalized_difference_bound j (χ' i) (b' i) r (X' i) J (m' i+t) (ell' i) (q' i)).trans (hSmall i))
    (fun i=>implicit_scaled_difference (s i) j χ (χ' i) r p (p' i) (X*X) (X' i*X' i) J
      u (u' i) m (m' i) t ell (ell' i) w (w' i) y (y' i) c (c' i) h (h' i))
  apply hlow.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact columnNorm_add_sub_sub_sub _ _ _ _ _

end SKGap.ImplicitSystem

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Stability_ImplicitFrobenius
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.ImplicitSystem
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {ι : Type*} [Fintype ι]

omit [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] in
lemma columnNorm_compare (U : ι→E) (V : ι→F) {C : ℝ} (hC : 0≤C)
    (h : ∀i,‖U i‖≤C*‖V i‖) : columnNorm U≤C*columnNorm V := by
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hC (columnNorm_nonneg _))
  simp only [←sq,columnNorm_sq,mul_pow,Finset.mul_sum]
  exact Finset.sum_le_sum fun i _=>by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg (U i)) (h i) 2

lemma columnNorm_inner_common (V : ι→E) (w : E) :
    columnNorm (fun i=>inner ℝ (V i) w)≤‖w‖*columnNorm V := by
  apply columnNorm_compare _ _ (norm_nonneg w)
  intro i
  simpa only [Real.norm_eq_abs,mul_comm] using abs_real_inner_le_norm (V i) w

lemma columnNorm_inner_variable (V W : ι→E) {C : ℝ}
    (hC : 0≤C) (hV : ∀i,‖V i‖≤C) :
    columnNorm (fun i=>inner ℝ (V i) (W i))≤C*columnNorm W := by
  apply columnNorm_compare _ _ hC
  intro i
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hV i) (norm_nonneg _))

lemma normalized_coefficient_difference (D : ι→E) (dp : ι→ℝ) (w : E)
    {r d R P : ℝ} (hr : 0 ≤ r) (hd : 0<d) (hscale : r*d^2=1)
    (_hR : 0≤R) (hD : columnNorm D≤R*d) (hP : d*columnNorm dp≤P) :
    d*columnNorm (fun i=>r*inner ℝ (D i) w+dp i)≤R*‖w‖+P := by
  have he : (fun i=>r*inner ℝ (D i) w+dp i)=r • (fun i=>inner ℝ (D i) w)+dp := rfl
  rw [he]
  have hc:=columnNorm_add (r • (fun i=>inner ℝ (D i) w)) dp
  rw [columnNorm_smul,abs_of_nonneg hr] at hc
  have hi:=(columnNorm_inner_common D w).trans
    (mul_le_mul_of_nonneg_left hD (norm_nonneg w))
  calc
    _ ≤ d*(r*(‖w‖*(R*d))+columnNorm dp) := mul_le_mul_of_nonneg_left
      (hc.trans (add_le_add (mul_le_mul_of_nonneg_left hi hr) le_rfl)) hd.le
    _ = R*‖w‖*(r*d^2)+d*columnNorm dp := by ring
    _ = R*‖w‖+d*columnNorm dp := by rw [hscale]; ring
    _ ≤ _ := add_le_add le_rfl hP

lemma normalized_scalar_difference (D W L : ι→E) (dp : ι→ℝ) (w : E)
    {r d R P Q : ℝ} (hr : 0 ≤ r) (hd : 0<d) (hscale : r*d^2=1)
    (hR : 0≤R) (hD : columnNorm D≤R*d) (hP : d*columnNorm dp≤P)
    (hQ : 0≤Q) (hL : ∀i,‖L i‖≤Q*d) :
    d*columnNorm (fun i=>r*inner ℝ (D i) w+dp i+r*inner ℝ (L i) (W i))≤
      R*‖w‖+P+Q*columnNorm W := by
  have h₁:=normalized_coefficient_difference D dp w hr hd hscale hR hD hP
  have h₂:=columnNorm_inner_variable L W (mul_nonneg hQ hd.le) hL
  have he : (fun i=>r*inner ℝ (D i) w+dp i+r*inner ℝ (L i) (W i))=
      (fun i=>r*inner ℝ (D i) w+dp i)+r • (fun i=>inner ℝ (L i) (W i)) := rfl
  rw [he]
  have hh:=columnNorm_add (fun i=>r*inner ℝ (D i) w+dp i) (r • (fun i=>inner ℝ (L i) (W i)))
  rw [columnNorm_smul,abs_of_nonneg hr] at hh
  calc
    _ ≤ d*columnNorm (fun i=>r*inner ℝ (D i) w+dp i)+d*r*((Q*d)*columnNorm W) := by
      nlinarith only [mul_le_mul_of_nonneg_left hh hd.le,
        mul_le_mul_of_nonneg_left h₂ (mul_nonneg hd.le hr)]
    _ = d*columnNorm (fun i=>r*inner ℝ (D i) w+dp i)+Q*columnNorm W*(r*d^2) := by ring
    _ = d*columnNorm (fun i=>r*inner ℝ (D i) w+dp i)+Q*columnNorm W := by rw [hscale]; ring
    _ ≤ _ := add_le_add h₁ le_rfl

variable [FiniteDimensional ℝ E]

theorem implicit_frobenius_estimate (j χ r p : ℝ) (X J : E→L[ℝ]E)
    (u m t ell w y : E) (c : ℝ)
    (s χ' p' c' : ι→ℝ) (X' : ι→E→L[ℝ]E) (u' m' ell' w' y' q' : ι→E) (b' : ι→ℝ)
    (h : Equations j χ r p (X*X) J u m t ell w y c)
    (h' : ∀i,Equations j (χ' i) r (p' i) (X' i*X' i) J (u' i) (m' i) t (ell' i) (w' i) (y' i) (c' i))
    {δ X₀ L₀ d RA U Rχ Rm Rell P C V : ℝ}
    (hδ : 0<δ) (hX₀ : 0≤X₀) (hL₀ : 0≤L₀) (hd : 0<d) (hr : 0 ≤ r) (hscale : r*d^2=1)
    (_hRA : 0≤RA) (_hU : 0≤U) (_hRχ : 0≤Rχ) (hRm : 0≤Rm) (hRell : 0≤Rell)
    (_hP : 0≤P) (_hC : 0≤C) (hV : 0≤V)
    (hX : ∀i,‖X' i‖≤X₀) (hL : ∀i,‖L₂ j (χ' i) r J (m' i+t) (ell' i)‖≤L₀)
    (hS : ∀i v,δ*‖v‖^2≤ inner ℝ v (stableMatrix j (b' i) r (X' i) J (q' i) v))
    (hSmall : ∀i,|j| *|χ' i-b' i| *‖X' i‖^2+|j*r| *‖X' i‖^2*
      (‖m' i+t-(2:ℝ) • q' i‖*‖ell' i‖+2*‖q' i‖*‖ell' i+q' i‖)≤δ/2)
    (hDA : ∀B, columnNorm (fun i=>(s i • (X*X-X' i*X' i)) B)≤RA*‖B‖)
    (hDu : columnNorm (fun i=>s i • (u-u' i))≤U)
    (hDχ : columnNorm (fun i=>s i*(χ-χ' i))≤Rχ)
    (hDm : columnNorm (fun i=>s i • (m-m' i))≤Rm*d)
    (hDell : columnNorm (fun i=>s i • (ell-ell' i))≤Rell*d)
    (hDp : d*columnNorm (fun i=>s i*(p-p' i))≤P)
    (hc : d*|c|≤C) (hv : ∀i,‖m' i+t‖≤V*d) :
    columnNorm (fun i=>s i • (w-w' i))≤(1+X₀^2*(δ/2)⁻¹*L₀)*
      (RA*‖u+J w-(j*χ) • w-(j*c) • (m+t)‖+X₀^2*U+
        |j| *X₀^2*‖w‖*Rχ+|j| *X₀^2*C*Rm+
        |j| *X₀^2*V*(Rell*‖w‖+P)) := by
  let A':=fun i=>X' i*X' i
  have hA : ∀i,‖A' i‖≤X₀^2 := fun i=>(norm_mul_le _ _).trans
    (by simpa only [pow_two] using mul_le_mul (hX i) (hX i) (norm_nonneg _) hX₀)
  let z:=fun i=>r*inner ℝ (s i • (ell-ell' i)) w+s i*(p-p' i)
  have hz : d*columnNorm z≤Rell*‖w‖+P :=
    normalized_coefficient_difference _ _ w hr hd hscale hRell hDell hDp
  have h₂ : columnNorm (fun i=>A' i (s i • (u-u' i)))≤X₀^2*U :=
    (columnNorm_operator A' _ (sq_nonneg _) hA).trans (mul_le_mul_of_nonneg_left hDu (sq_nonneg _))
  have h₃ : columnNorm (fun i=>(j*(s i*(χ-χ' i))) • A' i w)≤|j| *X₀^2*‖w‖*Rχ := by
    have he : (fun i=>(j*(s i*(χ-χ' i))) • A' i w)=
        j • (fun i=>(s i*(χ-χ' i)) • A' i w) := by ext i; simp [mul_smul]
    rw [he,columnNorm_smul]
    have hb : ∀i,‖A' i w‖≤X₀^2*‖w‖ := fun i=>((A' i).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg _))
    have hh:=(columnNorm_vector_scalar _ _ (by positivity : 0≤X₀^2*‖w‖) hb).trans
      (mul_le_mul_of_nonneg_left hDχ (by positivity))
    nlinarith only [mul_le_mul_of_nonneg_left hh (abs_nonneg j)]
  have h₄ : columnNorm (fun i=>(j*c) • A' i (s i • (m-m' i)))≤|j| *X₀^2*C*Rm := by
    change columnNorm ((j*c) • (fun i=>A' i (s i • (m-m' i))))≤_
    rw [columnNorm_smul,abs_mul]
    have hh:=(columnNorm_operator A' _ (sq_nonneg _) hA).trans
      (mul_le_mul_of_nonneg_left hDm (sq_nonneg _))
    calc
      _ ≤ |j| *|c| *(X₀^2*(Rm*d)) := mul_le_mul_of_nonneg_left hh (by positivity)
      _ = (|j| *X₀^2*Rm)*(d*|c|) := by ring
      _ ≤ (|j| *X₀^2*Rm)*C := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := by ring
  have h₅ : columnNorm (fun i=>(j*z i) • A' i (m' i+t))≤|j| *X₀^2*V*(Rell*‖w‖+P) := by
    have he : (fun i=>(j*z i) • A' i (m' i+t))=j • (fun i=>z i • A' i (m' i+t)) := by
      ext i; simp [mul_smul]
    rw [he,columnNorm_smul]
    have hb : ∀i,‖A' i (m' i+t)‖≤X₀^2*(V*d) := fun i=>((A' i).le_opNorm _).trans
      (mul_le_mul (hA i) (hv i) (norm_nonneg _) (sq_nonneg _))
    have hh:=columnNorm_vector_scalar (fun i=>A' i (m' i+t)) z (by positivity : 0≤X₀^2*(V*d)) hb
    calc
      _ ≤ |j| *((X₀^2*(V*d))*columnNorm z) := mul_le_mul_of_nonneg_left hh (abs_nonneg _)
      _ = (|j| *X₀^2*V)*(d*columnNorm z) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hz (by positivity)
  have H:=implicit_columns_bound j χ r p X J u m t ell w y c s χ' p' c' X' u' m' ell' w' y' q' b'
    h h' hδ hX₀ hL₀ hX hL hS hSmall
  apply H.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add (add_le_add (add_le_add (add_le_add (hDA _) h₂) h₃) h₄) h₅

end SKGap.ImplicitSystem

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Stability_ImplicitUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.ImplicitSystem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma L₂_norm_le (j χ r : ℝ) (J : E→L[ℝ]E) (v ell : E) :
    ‖L₂ j χ r J v ell‖≤‖J‖+|j| *|χ|+|j| *|r| *‖v‖*‖ell‖ := by
  unfold L₂
  calc
    _ ≤ ‖-J+(j*χ) • (1:E→L[ℝ]E)‖+‖(j*r) • rank v ell‖ := norm_add_le _ _
    _ ≤ (‖J‖+|j| *|χ|)+|j| *|r| *(‖v‖*‖ell‖) := by
      apply add_le_add
      · apply (norm_add_le _ _).trans
        simp only [norm_neg,norm_smul,Real.norm_eq_abs,abs_mul]
        exact add_le_add le_rfl (mul_le_of_le_one_right (by positivity) ContinuousLinearMap.norm_id_le)
      · rw [norm_smul,Real.norm_eq_abs,abs_mul]
        exact mul_le_mul_of_nonneg_left (rank_norm_le v ell) (by positivity)
    _ = _ := by ring

lemma L₂_normalized_bound (j χ r : ℝ) (J : E→L[ℝ]E) (v ell : E)
    {d V Q A L : ℝ} (hr : 0 ≤ r) (hd : 0≤d) (hscale : r*d^2=1)
    (hV : 0≤V) (hQ : 0≤Q) (hv : ‖v‖≤V*d) (hell : ‖ell‖≤Q*d)
    (hχ : |χ|≤A) (hJ : ‖J‖≤L) :
    ‖L₂ j χ r J v ell‖≤L+|j| *A+|j| *V*Q := by
  apply (L₂_norm_le j χ r J v ell).trans
  rw [abs_of_nonneg hr]
  have hmul:=mul_le_mul hv hell (norm_nonneg ell) (mul_nonneg hV hd)
  calc
    _ ≤ L+|j| *A+|j| *r*((V*d)*(Q*d)) := by
      rw [mul_assoc (|j| *r)]
      exact add_le_add (add_le_add hJ (mul_le_mul_of_nonneg_left hχ (abs_nonneg _)))
        (mul_le_mul_of_nonneg_left hmul (by positivity))
    _ = L+|j| *A+|j| *V*Q*(r*d^2) := by ring
    _ ≤ _ := by
      simpa only [mul_one] using add_le_add (le_refl (L+|j| *A))
        (mul_le_mul_of_nonneg_left hscale.le (mul_nonneg (mul_nonneg (abs_nonneg j) hV) hQ))

variable [FiniteDimensional ℝ E]

theorem implicit_uniform_size (j χ b r p : ℝ) (X J : E→L[ℝ]E)
    (u m t ell q w y : E) (c : ℝ)
    {δ d A L Q U P : ℝ} (hδ : 0<δ) (hd : 0<d) (hr : 0 ≤ r) (hscale : r*d^2=1)
    (hA : 0≤A) (hL : 0≤L) (hQ : 0≤Q) (hU : 0≤U) (hP : 0≤P)
    (hX : ‖X‖^2≤A) (hJ : ‖J‖≤L) (hχ : |χ|≤A)
    (hu : ‖u‖≤U) (hm : ‖m‖≤d) (ht : ‖t‖≤d) (hell : ‖ell‖≤Q*d) (hp : d*|p|≤P)
    (hStable : ∀v,δ*‖v‖^2≤ inner ℝ v (stableMatrix j b r X J q v))
    (hSmall : |j| *|χ-b| *‖X‖^2+|j*r| *‖X‖^2*
      (‖m+t-(2:ℝ) • q‖*‖ell‖+2*‖q‖*‖ell+q‖)≤δ/2)
    (hEq : Equations j χ r p (X*X) J u m t ell w y c) :
    let W:=(1+A*(δ/2)⁻¹*(L+|j| *A+2*|j| *Q))*A*(U+2*|j| *P)
    ‖w‖≤W ∧ d*|c|≤Q*W+P ∧ ‖y‖≤(L+|j| *A)*W+|j| *(Q*W+P) := by
  dsimp only
  let W:=(1+A*(δ/2)⁻¹*(L+|j| *A+2*|j| *Q))*A*(U+2*|j| *P)
  have hv : ‖m+t‖≤2*d := (norm_add_le _ _).trans (by linarith)
  have hL₂ : ‖L₂ j χ r J (m+t) ell‖≤L+|j| *A+2*|j| *Q := by
    convert L₂_normalized_bound j χ r J (m+t) ell hr hd.le hscale (by norm_num : (0:ℝ)≤2) hQ hv hell hχ hJ using 1 <;> first | rfl | ring
  have hRHS : ‖u‖+|j| *|p| *(‖m‖+‖t‖)≤U+2*|j| *P := by
    calc
      _ ≤ U+|j| *|p| *(2*d) := add_le_add hu (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
      _ = U+2*|j| *(d*|p|) := by ring
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hp (by positivity))
  have hinv : 0≤(δ/2)⁻¹ := by positivity
  have hK : 0≤1+A*(δ/2)⁻¹*(L+|j| *A+2*|j| *Q) := by positivity
  have hKK : 1+‖X‖^2*(δ/2)⁻¹*‖L₂ j χ r J (m+t) ell‖≤
      1+A*(δ/2)⁻¹*(L+|j| *A+2*|j| *Q) := by
    exact add_le_add le_rfl (mul_le_mul (mul_le_mul_of_nonneg_right hX hinv) hL₂ (norm_nonneg _) (by positivity))
  obtain ⟨hw,hc,hy⟩:=implicit_size_bounds j χ b r p X J u m t ell q w y c hδ hStable hSmall hEq
  have hw' : ‖w‖≤W := hw.trans (by
    simpa only [W,mul_comm] using mul_le_mul hRHS
      (mul_le_mul_of_nonneg_right hKK (sq_nonneg _) |>.trans (mul_le_mul_of_nonneg_left hX hK))
      (by positivity)
      (add_nonneg hU (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) (abs_nonneg j)) hP)))
  have hc' : d*|c|≤Q*W+P := by
    have hh:=implicit_scalar_size r p ell w
    rw [←hEq.2.2,abs_of_nonneg hr] at hh
    have hb:=mul_le_mul hell hw' (norm_nonneg w) (mul_nonneg hQ hd.le)
    calc
      _ ≤ d*(r*((Q*d)*W)+|p|) := mul_le_mul_of_nonneg_left
        (hh.trans (add_le_add (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hb hr) le_rfl)) hd.le
      _ = Q*W*(r*d^2)+d*|p| := by ring
      _ = Q*W+d*|p| := by rw [hscale]; ring
      _ ≤ _ := add_le_add le_rfl hp
  refine ⟨hw',hc',?_⟩
  rw [hEq.2.1]
  apply (implicit_field_size J j χ c w m).trans
  rw [abs_mul]
  have h₁:=mul_le_mul (add_le_add hJ (mul_le_mul_of_nonneg_left hχ (abs_nonneg _))) hw'
    (norm_nonneg w) (by positivity : 0≤L+|j| *A)
  have h₂ : |j| *|c| *‖m‖≤|j| *(Q*W+P) := by
    calc
      _ ≤ |j| *|c| *d := mul_le_mul_of_nonneg_left hm (by positivity)
      _ = |j| *(d*|c|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hc' (abs_nonneg _)
  exact add_le_add h₁ h₂
end SKGap.ImplicitSystem

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGap.ImplicitSystem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]

lemma implicit_field_difference (s j χ χ' r p p' : ℝ) (A A' J : E→L[ℝ]E)
    (u u' m m' t ell ell' w w' y y' : E) (c c' : ℝ)
    (h : Equations j χ r p A J u m t ell w y c)
    (h' : Equations j χ' r p' A' J u' m' t ell' w' y' c') :
    s • (y-y')=J (s • (w-w'))-(j*χ') • (s • (w-w'))-
      (j*(s*(χ-χ'))) • w-(j*c) • (s • (m-m'))-(j*(s*(c-c'))) • m' := by
  rw [h.2.1,h'.2.1]
  simp only [map_sub,map_smul]
  module

theorem implicit_scalar_columns (s : ι→ℝ) (r p : ℝ) (ell w : E) (c : ℝ)
    (p' c' : ι→ℝ) (ell' w' : ι→E)
    (hc : c=r*inner ℝ ell w+p) (hc' : ∀i,c' i=r*inner ℝ (ell' i) (w' i)+p' i)
    {d R P Q : ℝ} (hr : 0 ≤ r) (hd : 0<d) (hscale : r*d^2=1)
    (hR : 0≤R) (hD : columnNorm (fun i=>s i • (ell-ell' i))≤R*d)
    (hP : d*columnNorm (fun i=>s i*(p-p' i))≤P)
    (hQ : 0≤Q) (hL : ∀i,‖ell' i‖≤Q*d) :
    d*columnNorm (fun i=>s i*(c-c' i))≤R*‖w‖+P+Q*columnNorm (fun i=>s i • (w-w' i)) := by
  have he : (fun i=>s i*(c-c' i))=(fun i=>r*inner ℝ (s i • (ell-ell' i)) w+s i*(p-p' i)+
      r*inner ℝ (ell' i) (s i • (w-w' i))) := by
    funext i
    rw [hc,hc' i]
    exact implicit_scalar_difference (s i) r p (p' i) ell (ell' i) w (w' i)
  rw [he]
  exact normalized_scalar_difference _ _ _ _ w hr hd hscale hR hD hP hQ hL

theorem implicit_field_columns (s : ι→ℝ) (j χ r p : ℝ) (A J : E→L[ℝ]E)
    (u m t ell w y : E) (c : ℝ) (χ' p' c' : ι→ℝ)
    (A' : ι→E→L[ℝ]E) (u' m' ell' w' y' : ι→E)
    (h : Equations j χ r p A J u m t ell w y c)
    (h' : ∀i,Equations j (χ' i) r (p' i) (A' i) J (u' i) (m' i) t (ell' i) (w' i) (y' i) (c' i))
    {L H d Rχ Rm C M Dc : ℝ} (hL : 0≤L) (hH : 0≤H) (hd : 0<d)
    (hRχ : 0≤Rχ) (hRm : 0≤Rm) (hC : 0≤C) (hM : 0≤M)
    (hJ : ‖J‖≤L) (hχ : ∀i,|χ' i|≤H)
    (hDχ : columnNorm (fun i=>s i*(χ-χ' i))≤Rχ)
    (hDm : columnNorm (fun i=>s i • (m-m' i))≤Rm*d)
    (hc : d*|c|≤C) (hm : ∀i,‖m' i‖≤M*d)
    (hdc : d*columnNorm (fun i=>s i*(c-c' i))≤Dc) :
    columnNorm (fun i=>s i • (y-y' i))≤
      (L+|j| *H)*columnNorm (fun i=>s i • (w-w' i))+|j| *‖w‖*Rχ+|j| *C*Rm+|j| *M*Dc := by
  let Dw:=fun i=>s i • (w-w' i)
  let Dχ:=fun i=>s i*(χ-χ' i)
  let Dm:=fun i=>s i • (m-m' i)
  let Dc':=fun i=>s i*(c-c' i)
  have ha : columnNorm (fun i=>J (Dw i))≤L*columnNorm Dw :=
    columnNorm_operator (fun _=>J) Dw hL (fun _=>hJ)
  have hb : columnNorm (fun i=>(j*χ' i) • Dw i)≤(|j| *H)*columnNorm Dw := by
    apply columnNorm_compare _ _ (by positivity)
    intro i
    rw [norm_smul,Real.norm_eq_abs,abs_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hχ i) (abs_nonneg j)) (norm_nonneg _)
  have he : columnNorm (fun i=>(j*Dχ i) • w)≤|j| *‖w‖*Rχ := by
    have eq : (fun i=>(j*Dχ i) • w)=j • (fun i=>Dχ i • w) := by ext i; simp [mul_smul]
    rw [eq,columnNorm_smul]
    exact (mul_le_mul_of_nonneg_left (columnNorm_vector_scalar (fun _=>w) Dχ (norm_nonneg w) (fun _=>le_rfl)) (abs_nonneg j)).trans
      (by
        simpa only [mul_assoc,mul_comm,mul_left_comm] using mul_le_mul hDχ
          (le_refl (|j| *‖w‖)) (mul_nonneg (abs_nonneg j) (norm_nonneg w)) hRχ)
  have hf : columnNorm (fun i=>(j*c) • Dm i)≤|j| *C*Rm := by
    change columnNorm ((j*c) • Dm)≤_
    rw [columnNorm_smul,abs_mul]
    calc
      _ ≤ |j| *|c| *(Rm*d) := mul_le_mul_of_nonneg_left hDm (by positivity)
      _ = (|j| *Rm)*(d*|c|) := by ring
      _ ≤ (|j| *Rm)*C := by
        simpa only [mul_comm] using mul_le_mul hc (le_refl (|j| *Rm))
          (mul_nonneg (abs_nonneg j) hRm) hC
      _ = _ := by ring
  have hg : columnNorm (fun i=>(j*Dc' i) • m' i)≤|j| *M*Dc := by
    have eq : (fun i=>(j*Dc' i) • m' i)=j • (fun i=>Dc' i • m' i) := by ext i; simp [mul_smul]
    rw [eq,columnNorm_smul]
    calc
      _ ≤ |j| *((M*d)*columnNorm Dc') := mul_le_mul_of_nonneg_left
        (columnNorm_vector_scalar m' Dc' (by positivity) hm) (abs_nonneg j)
      _ = (|j| *M)*(d*columnNorm Dc') := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdc (by positivity)
  have eq : (fun i=>s i • (y-y' i))=(fun i=>J (Dw i))+(fun i=>-((j*χ' i) • Dw i))-
      (fun i=>(j*Dχ i) • w)-(fun i=>(j*c) • Dm i)-(fun i=>(j*Dc' i) • m' i) := by
    funext i
    simpa only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Dw,Dχ,Dm,Dc',sub_eq_add_neg] using
      implicit_field_difference (s i) j χ (χ' i) r p (p' i) A (A' i) J u (u' i) m (m' i) t ell (ell' i) w (w' i) y (y' i) c (c' i) h (h' i)
  rw [eq]
  have ht:=columnNorm_add_sub_sub_sub (fun i=>J (Dw i)) (fun i=>-((j*χ' i) • Dw i))
    (fun i=>(j*Dχ i) • w) (fun i=>(j*c) • Dm i) (fun i=>(j*Dc' i) • m' i)
  change columnNorm _≤_ at ht
  have hn : columnNorm (fun i=>-((j*χ' i) • Dw i))=columnNorm (fun i=>(j*χ' i) • Dw i) := columnNorm_neg _
  rw [hn] at ht
  exact ht.trans (by nlinarith only [ha,hb,he,hf,hg])
end SKGap.ImplicitSystem

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Stability_ImplicitUniformControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.ImplicitSystem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]

theorem implicit_uniform_control_s2_oai (j χ b r p : ℝ) (X J : E→L[ℝ]E)
    (u m t ell q w y : E) (c : ℝ)
    (s χ' p' c' b' : ι→ℝ) (X' : ι→E→L[ℝ]E) (u' m' ell' w' y' q' : ι→E)
    {δ d B : ℝ} (hδ : 0<δ) (hd : 0<d) (hr : 0 ≤ r) (hscale : r*d^2=1) (hB : 0≤B)
    (hX : ‖X‖≤B) (hX' : ∀i,‖X' i‖≤B) (hJ : ‖J‖≤B)
    (hχ : |χ|≤B^2) (hχ' : ∀i,|χ' i|≤B^2)
    (hu : ‖u‖≤B) (hm : ‖m‖≤d) (hm' : ∀i,‖m' i‖≤d) (ht : ‖t‖≤d)
    (hell : ‖ell‖≤B*d) (hell' : ∀i,‖ell' i‖≤B*d) (hp : d*|p|≤B)
    (hS : ∀v,δ*‖v‖^2≤ inner ℝ v (stableMatrix j b r X J q v))
    (hS' : ∀i v,δ*‖v‖^2≤ inner ℝ v (stableMatrix j (b' i) r (X' i) J (q' i) v))
    (hSmall : |j| *|χ-b| *‖X‖^2+|j*r| *‖X‖^2*
      (‖m+t-(2:ℝ) • q‖*‖ell‖+2*‖q‖*‖ell+q‖)≤δ/2)
    (hSmall' : ∀i,|j| *|χ' i-b' i| *‖X' i‖^2+|j*r| *‖X' i‖^2*
      (‖m' i+t-(2:ℝ) • q' i‖*‖ell' i‖+2*‖q' i‖*‖ell' i+q' i‖)≤δ/2)
    (h : Equations j χ r p (X*X) J u m t ell w y c)
    (h' : ∀i,Equations j (χ' i) r (p' i) (X' i*X' i) J (u' i) (m' i) t (ell' i) (w' i) (y' i) (c' i))
    (hDA : ∀V,columnNorm (fun i=>(s i • (X*X-X' i*X' i)) V)≤B*‖V‖)
    (hDu : columnNorm (fun i=>s i • (u-u' i))≤B)
    (hDχ : columnNorm (fun i=>s i*(χ-χ' i))≤B)
    (hDm : columnNorm (fun i=>s i • (m-m' i))≤B*d)
    (hDell : columnNorm (fun i=>s i • (ell-ell' i))≤B*d)
    (hDp : d*columnNorm (fun i=>s i*(p-p' i))≤B) :
    ‖w‖+d*|c|+‖y‖+columnNorm (fun i=>s i • (w-w' i))+
      d*columnNorm (fun i=>s i*(c-c' i))+columnNorm (fun i=>s i • (y-y' i))≤
        uniformControlBudget j δ B := by
  let L:=B+|j| *B^2+2*|j| *B
  let W:=(1+B^2*(δ/2)⁻¹*L)*B^2*(B+2*|j| *B)
  let C:=B*W+B
  let Y:=(B+|j| *B^2)*W+|j| *C
  let F:=(1+B^2*(δ/2)⁻¹*L)*(B*(B+Y+|j| *C)+B^2*B+
        |j| *B^2*W*B+|j| *B^2*C*B+|j| *B^2*2*(B*W+B))
  let G:=B*W+B+B*F
  let H:=(B+|j| *B^2)*F+|j| *W*B+|j| *C*B+|j| *G
  have hW0 : 0≤W := by dsimp [W,L]; positivity
  have hC0 : 0≤C := by dsimp [C]; positivity
  have hY0 : 0≤Y := by dsimp [Y]; positivity
  have hL0 : 0≤L := by dsimp [L]; positivity
  have hF0 : 0≤F := by dsimp [F]; positivity
  obtain ⟨hw,hc,hy⟩:=implicit_uniform_size j χ b r p X J u m t ell q w y c
    hδ hd hr hscale (sq_nonneg B) hB hB hB hB
    (pow_le_pow_left₀ (norm_nonneg X) hX 2) hJ hχ hu hm ht hell hp hS hSmall h
  change ‖w‖≤W at hw
  change d*|c|≤C at hc
  change ‖y‖≤Y at hy
  have hl : ∀i,‖L₂ j (χ' i) r J (m' i+t) (ell' i)‖≤L := by
    intro i
    have hv : ‖m' i+t‖≤2*d := (norm_add_le _ _).trans (by linarith [hm' i])
    convert L₂_normalized_bound j (χ' i) r J (m' i+t) (ell' i) hr hd.le hscale
      (by norm_num : (0:ℝ)≤2) hB hv (hell' i) (hχ' i) hJ using 1; dsimp [L]; ring
  have hb : ‖u+J w-(j*χ) • w-(j*c) • (m+t)‖≤B+Y+|j| *C := by
    have he : u+J w-(j*χ) • w-(j*c) • (m+t)=u+y-(j*c) • t := by
      rw [h.2.1]; module
    rw [he]
    apply (norm_sub_le _ _).trans
    have hct : ‖(j*c) • t‖≤|j| *C := by
      rw [norm_smul,Real.norm_eq_abs,abs_mul]
      calc
        _ ≤ |j| *|c| *d := mul_le_mul_of_nonneg_left ht (by positivity)
        _ = |j| *(d*|c|) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hc (abs_nonneg j)
    exact add_le_add ((norm_add_le _ _).trans (add_le_add hu hy)) hct
  have hf:=implicit_frobenius_estimate j χ r p X J u m t ell w y c
    s χ' p' c' X' u' m' ell' w' y' q' b' h h' hδ hB hL0 hd hr hscale
    hB hB hB hB hB hB hC0 (by norm_num : (0:ℝ)≤2) hX' hl hS' hSmall'
    hDA hDu hDχ hDm hDell hDp hc (fun i=>(norm_add_le _ _).trans (by linarith [hm' i]))
  have hf' : columnNorm (fun i=>s i • (w-w' i))≤F := by
    apply hf.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact add_le_add (add_le_add (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hb hB) le_rfl)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw (by positivity)) hB)) le_rfl)
      (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hw hB) le_rfl) (by positivity))
  have hg : d*columnNorm (fun i=>s i*(c-c' i))≤G := by
    exact (implicit_scalar_columns s r p ell w c p' c' ell' w' h.2.2 (fun i=>(h' i).2.2)
      hr hd hscale hB hDell hDp hB hell').trans (add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hw hB) le_rfl) (mul_le_mul_of_nonneg_left hf' hB))
  have hh : columnNorm (fun i=>s i • (y-y' i))≤H := by
    have hh:=implicit_field_columns s j χ r p (X*X) J u m t ell w y c χ' p' c'
      (fun i=>X' i*X' i) u' m' ell' w' y' h h' hB (sq_nonneg B) hd hB hB hC0
      (by norm_num : (0:ℝ)≤1) hJ hχ' hDχ hDm hc (by simpa only [one_mul] using hm') hg
    apply hh.trans
    simp only [mul_one]
    exact add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hf' (by positivity))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw (abs_nonneg j)) hB)) le_rfl) le_rfl
  change _≤W+C+Y+F+G+H
  exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hw hc) hy) hf') hg) hh
end SKGap.ImplicitSystem

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.SKGap.ImplicitSystem.implicit_uniform_control_s2_oai.{u_1, u_2} := @OAI.SKGap.ImplicitSystem.implicit_uniform_control_s2_oai.{u_1, u_2}
