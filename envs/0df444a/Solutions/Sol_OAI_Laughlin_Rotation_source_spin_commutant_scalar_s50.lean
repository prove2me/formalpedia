-- Prove2me | solution 1 for OAI.Laughlin.Rotation.source_spin_commutant_scalar_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:37:29.534519+00:00
-- url     : https://prove2.me/submissions/e5233319-7f2f-4bed-a070-48924b159f83

import Mathlib
import Definitions.Def_OAIQ050L013
import Definitions.Def_OAIQ050L016

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Tensor_WeightProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators

 theorem tensorWeight_zero_iff (Q : ℕ) (a : Fin Q → Fin 2) :
    tensorWeight Q a=0 ↔ a=fun _ => 0 := by
  constructor
  · intro h
    have he : tensorBits Q a=∅ := Finset.card_eq_zero.mp h
    funext i
    have hn : a i ≠ 1 := by
      intro hi
      have hm : i ∈ tensorBits Q a := by simp [tensorBits,hi]
      rw [he] at hm
      exact Finset.notMem_empty _ hm
    apply Fin.ext
    have ha := (a i).isLt
    have hn' : (a i).val ≠ 1 := by intro he; exact hn (Fin.ext he)
    simp only [Fin.val_zero]
    omega
  · rintro rfl
    simp [tensorWeight,tensorBits]

 theorem symmetricTensor_zero_column (Q : ℕ) (a : Fin Q → Fin 2) :
    symmetricTensorInclusion Q a 0 = if a=(fun _ => 0) then 1 else 0 := by
  simp [symmetricTensorInclusion,symmetricTensorInclusionReal,tensorWeight_zero_iff,apply_ite]

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Torus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

theorem sourceSpinRepresentation_torus (Q : ℕ) (z : ℂ) (hz : ‖z‖=1) :
    sourceSpinRepresentation Q (sourceTorus z hz) =
      Matrix.diagonal (fun p : Fin (Q+1) => (star z)^p.val*z^(Q-p.val)) := by
  change (symmetricTensorInclusion Q)ᴴ * tensorMatrix Q
    (Matrix.diagonal (fun i : Fin 2 => if i=0 then z else star z)) * symmetricTensorInclusion Q = _
  rw [tensorMatrix_diagonal,Matrix.mul_assoc,symmetricTensor_diagonal_intertwining Q (fun k => (star z)^k*z^(Q-k)),
    ← Matrix.mul_assoc,symmetricTensorInclusion_isometry,Matrix.one_mul]

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Mixing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

 theorem tensorWeight_sum_const (Q p : ℕ) (c : ℂ) :
    (∑ a : Fin Q → Fin 2, if tensorWeight Q a=p then c else 0) = (Q.choose p : ℂ)*c := by
  have he (a : Fin Q → Fin 2) : (if tensorWeight Q a=p then c else 0) =
      ((if tensorWeight Q a=p then (1 : ℝ) else 0) : ℂ)*c := by split_ifs <;> simp
  simp_rw [he]
  rw [← Finset.sum_mul]
  have hc := congrArg Complex.ofReal (tensorWeight_count Q p)
  simp only [Complex.ofReal_sum,apply_ite,Complex.ofReal_one,Complex.ofReal_zero,Complex.ofReal_natCast] at hc
  simpa only [Complex.ofReal_one] using congrArg (fun z : ℂ => z*c) hc

 theorem symmetricTensorInclusion_column_sum (Q : ℕ) (p : Fin (Q+1)) :
    (∑ a, symmetricTensorInclusion Q a p) = (Real.sqrt (Q.choose p.val : ℝ) : ℂ) := by
  simp only [symmetricTensorInclusion,Matrix.map_apply,symmetricTensorInclusionReal,apply_ite,
    Complex.ofReal_zero]
  rw [tensorWeight_sum_const]
  have hs : (Real.sqrt (Q.choose p.val : ℝ) : ℂ)^2=(Q.choose p.val : ℂ) := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ Q.choose p.val by positivity)
  have hn : (Real.sqrt (Q.choose p.val : ℝ) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    apply Real.sqrt_ne_zero'.mpr
    exact_mod_cast Nat.choose_pos (by omega : p.val ≤ Q)
  rw [Complex.ofReal_inv,← hs]
  field_simp

 theorem tensorMatrix_uniform_first_column (Q : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ)
    (h0 : A 0 0=c) (h1 : A 1 0=c) (a : Fin Q → Fin 2) :
    (tensorMatrix Q A*symmetricTensorInclusion Q) a 0=c^Q := by
  classical
  rw [Matrix.mul_apply,Finset.sum_eq_single (fun _ => (0 : Fin 2))]
  · rw [symmetricTensor_zero_column,ite_eq_left rfl,mul_one]
    have he (i : Fin Q) : A (a i) 0=c := by
      have h : a i=0 ∨ a i=1 := by omega
      rcases h with h | h
      · rw [h]; exact h0
      · rw [h]; exact h1
    simp [tensorMatrix,he]
  · intro b hb hne
    rw [symmetricTensor_zero_column,ite_eq_right hne,mul_zero]
  · simp

theorem sourceSpinRepresentation_mixer_column (Q : ℕ) (p : Fin (Q+1)) :
    sourceSpinRepresentation Q sourceMixer p 0 =
      (Real.sqrt (Q.choose p.val : ℝ) : ℂ)*(Real.sqrt (1/2) : ℂ)^Q := by
  change ((symmetricTensorInclusion Q)ᴴ*tensorMatrix Q sourceMixer.val*symmetricTensorInclusion Q) p 0 = _
  rw [Matrix.mul_assoc,Matrix.mul_apply]
  have he (a : Fin Q → Fin 2) : (tensorMatrix Q sourceMixer.val*symmetricTensorInclusion Q) a 0 =
      (Real.sqrt (1/2) : ℂ)^Q := tensorMatrix_uniform_first_column Q _ _ rfl rfl a
  simp_rw [he,Matrix.conjTranspose_apply]
  have hr (a : Fin Q → Fin 2) : star (symmetricTensorInclusion Q a p)=symmetricTensorInclusion Q a p := by
    simp [symmetricTensorInclusion]
  simp_rw [hr]
  rw [← Finset.sum_mul,symmetricTensorInclusion_column_sum]

 theorem sourceSpinRepresentation_mixer_column_ne_zero (Q : ℕ) (p : Fin (Q+1)) :
    sourceSpinRepresentation Q sourceMixer p 0 ≠ 0 := by
  rw [sourceSpinRepresentation_mixer_column]
  apply mul_ne_zero
  · apply Complex.ofReal_ne_zero.mpr
    apply Real.sqrt_ne_zero'.mpr
    exact_mod_cast Nat.choose_pos (by omega : p.val ≤ Q)
  · apply pow_ne_zero
    exact Complex.ofReal_ne_zero.mpr (by positivity)

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Schur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

 theorem spinSeparatingRoot_primitive (Q : ℕ) : IsPrimitiveRoot (spinSeparatingRoot Q) (2*Q+1) :=
  Complex.isPrimitiveRoot_exp _ (by omega)
 theorem spinSeparatingRoot_norm (Q : ℕ) : ‖spinSeparatingRoot Q‖=1 := by
  simp [spinSeparatingRoot,Complex.norm_exp,Complex.div_re]

 theorem torus_weight_fraction (Q : ℕ) (z : ℂ) (hz : ‖z‖=1) (p : Fin (Q+1)) :
    (star z)^p.val*z^(Q-p.val) = z^Q/z^(2*p.val) := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hinv : star z=z⁻¹ := by
    simp [Complex.inv_def,Complex.normSq_eq_norm_sq,hz]
  rw [hinv,inv_pow]
  have hQ : Q=(Q-p.val)+p.val := by omega
  have hp : z^Q=z^(Q-p.val)*z^p.val := by rw [← pow_add,← hQ]
  rw [hp,show 2*p.val=p.val+p.val by omega,pow_add]
  field_simp

 theorem spinSeparatingRoot_weights_injective (Q : ℕ) : Function.Injective
    (fun p : Fin (Q+1) => (star (spinSeparatingRoot Q))^p.val*(spinSeparatingRoot Q)^(Q-p.val)) := by
  intro p q hpq
  dsimp only at hpq
  let z := spinSeparatingRoot Q
  have hz := spinSeparatingRoot_norm Q
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  rw [torus_weight_fraction Q _ hz p,torus_weight_fraction Q _ hz q] at hpq
  have he := (div_eq_div_iff (pow_ne_zero (2*p.val) hz0) (pow_ne_zero (2*q.val) hz0)).mp hpq
  have hpows : z^(2*p.val)=z^(2*q.val) := (mul_left_cancel₀ (pow_ne_zero Q hz0) he).symm
  have h := (spinSeparatingRoot_primitive Q).pow_inj (by omega : 2*p.val < 2*Q+1)
    (by omega : 2*q.val < 2*Q+1) hpows
  exact Fin.ext (by omega)

theorem source_spin_commutant_scalar_s50_oai (Q : ℕ) (M : Matrix (Fin (Q+1)) (Fin (Q+1)) ℂ)
    (hM : ∀ g : SourceSU2, sourceSpinRepresentation Q g*M=M*sourceSpinRepresentation Q g) :
    M=M 0 0 • (1 : Matrix (Fin (Q+1)) (Fin (Q+1)) ℂ) := by
  have ht := hM (sourceTorus (spinSeparatingRoot Q) (spinSeparatingRoot_norm Q))
  rw [sourceSpinRepresentation_torus] at ht
  have hd : M=Matrix.diagonal (fun p => M p p) := by
    ext p q
    by_cases hpq : p=q
    · subst q; simp
    · rw [Matrix.diagonal_apply_ne _ hpq]
      have he := congrFun (congrFun ht p) q
      simp only [Matrix.diagonal_mul,Matrix.mul_diagonal] at he
      have hn := (spinSeparatingRoot_weights_injective Q).ne hpq
      exact (mul_eq_zero.mp (show
        ((star (spinSeparatingRoot Q))^p.val*(spinSeparatingRoot Q)^(Q-p.val)-
         (star (spinSeparatingRoot Q))^q.val*(spinSeparatingRoot Q)^(Q-q.val))*M p q=0 by
          linear_combination he)).resolve_left (sub_ne_zero.mpr hn)
  have hm := hM sourceMixer
  rw [hd] at hm
  have hc (p : Fin (Q+1)) : M p p=M 0 0 := by
    have he := congrFun (congrFun hm p) 0
    simp only [Matrix.mul_diagonal,Matrix.diagonal_mul] at he
    apply (mul_left_cancel₀ (sourceSpinRepresentation_mixer_column_ne_zero Q p))
    calc
      _ = M p p*sourceSpinRepresentation Q sourceMixer p 0 := by ring
      _ = _ := he.symm
  rw [hd]
  ext p q
  by_cases hpq : p=q
  · subst q; simp [hc]
  · simp [hpq]

end Laughlin.Rotation

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Rotation.source_spin_commutant_scalar_s50_oai := @OAI.Laughlin.Rotation.source_spin_commutant_scalar_s50_oai
