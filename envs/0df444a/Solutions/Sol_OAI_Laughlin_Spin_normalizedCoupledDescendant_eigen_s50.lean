-- Prove2me | solution 1 for OAI.Laughlin.Spin.normalizedCoupledDescendant_eigen_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:41:08.513055+00:00
-- url     : https://prove2.me/submissions/3920851e-5df7-4e40-8a05-462dc091f6b0

import Mathlib
import Definitions.Def_OAIQ050L016
import Definitions.Def_OAIQ050L018
import Theorems.Thm_OAI_Laughlin_Fock_threeBodyColumn_gram_s50
import Theorems.Thm_OAI_Laughlin_Fock_threeBodyGram_highest_first_coordinate_s50
import Theorems.Thm_OAI_Laughlin_Spin_threeGram_raising_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_Orthonormality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators

theorem pairCoefficient_swap (Q p : ℕ) (x y : Fin (Q+1)) :
    pairCoefficient Q p y x = -pairCoefficient Q p x y := by
  unfold pairCoefficient
  rw [Nat.add_comm y.val x.val]
  split_ifs
  · have hn : ((Q.descFactorial y.val : ℝ) * (Q.descFactorial x.val : ℝ) * (p.factorial : ℝ)) =
        ((Q.descFactorial x.val : ℝ) * (Q.descFactorial y.val : ℝ) * (p.factorial : ℝ)) := by ring
    have hd : ((Q : ℝ) * ((2*Q-2).descFactorial p : ℝ) * (y.val.factorial : ℝ) * (x.val.factorial : ℝ)) =
        ((Q : ℝ) * ((2*Q-2).descFactorial p : ℝ) * (x.val.factorial : ℝ) * (y.val.factorial : ℝ)) := by ring
    rw [hn, hd]
    ring
  · simp

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_HighestSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem highest_unique (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (f : ℕ → ℝ)
    (hf : ∀ p < z, ladder A p*f (p+1)+ladder B (z-p-1)*f p = 0) :
    ∀ p ≤ z, f p = (f 0 / highestRaw A B z 0)*highestRaw A B z p := by
  intro p hp
  induction p with
  | zero => field_simp [highestRaw_ne_zero A B z 0 hA hB (by omega)]
  | succ p ih =>
    have hlt : p < z := by omega
    have he := highestRaw_raising A B z p hA hB hlt
    have hh := hf p hlt
    have hi := ih (by omega)
    have ha : ladder A p ≠ 0 := ne_of_gt (ladder_pos A p (by omega))
    apply (mul_left_cancel₀ ha)
    linear_combination hh - (f 0 / highestRaw A B z 0)*he - ladder B (z-p-1)*hi

theorem highestUnit_ne_zero (A B z p : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (hp : p ≤ z) : highestUnit A B z p ≠ 0 :=
  div_ne_zero (highestRaw_ne_zero A B z p hA hB hp)
    (ne_of_gt (highestNorm_pos A B z hA hB))

theorem raiseSlice_kernel (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (f : Fin (z+1) → ℝ) :
    (∀ p, raiseSlice A B z f p = 0) ↔
      ∃ c : ℝ, ∀ p, f p = c*highestUnit A B z p.val := by
  constructor
  · intro hf
    let g : ℕ → ℝ := fun p => if h : p < z+1 then f ⟨p,h⟩ else 0
    have hg : ∀ p < z, ladder A p*g (p+1)+ladder B (z-p-1)*g p = 0 := by
      intro p hp
      simpa [g,raiseSlice,hp,show p ≤ z by omega] using hf ⟨p,hp⟩
    refine ⟨(g 0 / highestRaw A B z 0)*highestNorm A B z,?_⟩
    intro p
    have he := highest_unique A B z hA hB g hg p.val (by omega)
    have hn := ne_of_gt (highestNorm_pos A B z hA hB)
    have hfval : g p.val = f p := by simp [g,show p.val ≤ z by omega]
    rw [hfval] at he
    rw [he]
    unfold highestUnit
    field_simp
  · rintro ⟨c,hc⟩ p
    simp only [raiseSlice,hc]
    linear_combination c * highestUnit_raising A B z p.val hA hB p.isLt

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_GramSlice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem threeBodyGramSlice_physical (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q)
    (p q : Fin (z+1)) :
    (threeBodyGramSlice Q z hz p q : ℂ) =
      occupationInner Q (threeBodyColumn Q p.val (sliceOrbital Q z hz p))
        (threeBodyColumn Q q.val (sliceOrbital Q z hz q)) := by
  rw [threeBodyColumn_gram_s50 Q p.val q.val hQ (by omega)]
  unfold threeBodyGramSlice
  push_cast
  congr 1
  by_cases h : p = q
  · subst q; simp
  · have hv : p.val ≠ q.val := by simpa only [Fin.ext_iff] using h
    simp [h,hv]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_SpinCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

theorem swapCompression_entry (Q : ℕ) (a b : PairOrbitalIndex Q) :
    swapCompression Q a b = ∑ t : Orbital Q,
      pairCoefficient Q a.1.val b.2 t * pairCoefficient Q b.1.val a.2 t := by
  have he (i : TripleIndex Q) :
      ((tripleInclusion Q)ᵀ * swap23Matrix Q) a i = tripleInclusion Q (swap23 i) a := by
    have hi (k : TripleIndex Q) : swap23 k=i ↔ k=swap23 i := by
      constructor
      · intro h; simpa using congrArg swap23 h
      · intro h; rw [h,swap23_involutive]
    simp [Matrix.mul_apply,swap23Matrix,hi,Matrix.transpose_apply]
  unfold swapCompression
  rw [Matrix.mul_apply]
  simp_rw [he]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp only [tripleInclusion,pairInclusion,Matrix.kroneckerMap,
    Matrix.of_apply,Matrix.one_apply,swap23]
  simp only [mul_ite,mul_one,mul_zero,ite_mul,zero_mul,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true]
  apply Finset.sum_congr rfl
  intro t ht
  rw [pairCoefficient_swap Q a.1.val t b.2,pairCoefficient_swap Q b.1.val t a.2]
  ring

theorem threeGram_entry (Q : ℕ) (a b : PairOrbitalIndex Q) :
    threeGram Q a b = (if a=b then 1 else 0) - 2*∑ t : Orbital Q,
      pairCoefficient Q a.1.val b.2 t * pairCoefficient Q b.1.val a.2 t := by
  simp only [threeGram,Matrix.sub_apply,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,
    swapCompression_entry]

theorem threeGram_physical (Q : ℕ) (hQ : 2 ≤ Q) (a b : PairOrbitalIndex Q) :
    (threeGram Q a b : ℂ) =
      Fock.occupationInner Q (Fock.threeBodyColumn Q a.1.val a.2)
        (Fock.threeBodyColumn Q b.1.val b.2) := by
  rw [threeGram_entry,Fock.threeBodyColumn_gram_s50 Q a.1.val b.1.val hQ (by omega)]
  push_cast
  congr 1
  by_cases ha : a.1=b.1 <;> by_cases hb : a.2=b.2 <;>
    simp [Prod.ext_iff,ha,hb]
  simp_all [Fin.ext_iff]

theorem threeGram_weight (Q : ℕ) (a b : PairOrbitalIndex Q)
    (h : a.1.val+a.2.val ≠ b.1.val+b.2.val) : threeGram Q a b = 0 := by
  have hab : a ≠ b := by intro he; apply h; rw [he]
  rw [threeGram_entry,ite_eq_right hab]
  have hz : (∑ t : Orbital Q, pairCoefficient Q a.1.val b.2 t *
      pairCoefficient Q b.1.val a.2 t) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    by_cases ha : b.2.val+t.val=a.1.val+1
    · have hb : a.2.val+t.val ≠ b.1.val+1 := by omega
      simp [pairCoefficient,hb]
    · simp [pairCoefficient,ha]
  rw [hz]; ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_HighestEigen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem threeGram_on_slice (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) (p q : Fin (z+1)) :
    threeGram Q (weightSliceIndex (2*Q-2) Q z (by omega) hz p)
      (weightSliceIndex (2*Q-2) Q z (by omega) hz q) = Fock.threeBodyGramSlice Q z hz p q := by
  apply Complex.ofReal_injective
  rw [threeGram_physical Q hQ,Fock.threeBodyGramSlice_physical Q z hQ hz]
  rfl

theorem threeGram_extend_off (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q)
    (f : Fin (z+1) → ℝ) (i : PairOrbitalIndex Q) (hi : i.1.val+i.2.val ≠ z) :
    (threeGram Q *ᵥ extendWeightSlice (2*Q-2) Q z (by omega) hz f) i = 0 := by
  change (∑ j, threeGram Q i j * extendWeightSlice (2*Q-2) Q z (by omega) hz f j) = 0
  rw [sum_extendWeightSlice]
  apply Finset.sum_eq_zero
  intro p hp
  rw [threeGram_weight]
  · ring
  · dsimp [weightSliceIndex]
    omega

theorem threeGram_highest_eigen (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    threeGram Q *ᵥ coupledHighest Q z hQ hz =
      (1+gramEigenvalueFormula Q z) • coupledHighest Q z hQ hz := by
  let v := coupledHighest Q z hQ hz
  let g := threeGram Q *ᵥ v
  let f : Fin (z+1) → ℝ := fun p => g (weightSliceIndex (2*Q-2) Q z (by omega) hz p)
  have hv : totalRaise (2*Q-2) Q *ᵥ v = 0 := by
    apply extendWeightSlice_highest
    intro p
    exact highestUnit_raising (2*Q-2) Q z p.val (by omega) hz p.isLt
  have hg : totalRaise (2*Q-2) Q *ᵥ g = 0 := by
    dsimp [g]
    rw [Matrix.mulVec_mulVec,← threeGram_raising_s50 Q (by omega),← Matrix.mulVec_mulVec,hv,
      Matrix.mulVec_zero]
  have hf : ∀ p, raiseSlice (2*Q-2) Q z f p = 0 := by
    intro p
    have he := congrFun hg ((⟨p.val,by omega⟩,⟨z-p.val-1,by omega⟩) : PairOrbitalIndex Q)
    rw [totalRaise_below_slice (2*Q-2) Q z (by omega) hz] at he
    exact he
  obtain ⟨c,hc⟩ := (raiseSlice_kernel (2*Q-2) Q z (by omega) hz f).mp hf
  have hfirst : f ⟨0,by omega⟩ =
      (1+gramEigenvalueFormula Q z)*highestUnit (2*Q-2) Q z 0 := by
    dsimp [f,g,v,coupledHighest]
    change (∑ j,threeGram Q _ j*extendWeightSlice (2*Q-2) Q z (by omega) hz _ j) = _
    rw [sum_extendWeightSlice]
    simp_rw [threeGram_on_slice Q z hQ hz]
    exact Fock.threeBodyGram_highest_first_coordinate_s50 Q z hQ hz
  have hcz : c = 1+gramEigenvalueFormula Q z := by
    apply (mul_right_cancel₀ (highestUnit_ne_zero (2*Q-2) Q z 0 (by omega) hz (by omega)))
    exact (hc ⟨0,by omega⟩).symm.trans hfirst
  funext i
  change g i = (1+gramEigenvalueFormula Q z)*v i
  by_cases hi : i.1.val+i.2.val=z
  · let p : Fin (z+1) := ⟨i.1.val,by omega⟩
    have he : i = weightSliceIndex (2*Q-2) Q z (by omega) hz p := by
      apply Prod.ext
      · rfl
      · apply Fin.ext; dsimp [weightSliceIndex,p]; omega
    rw [he]
    change f p = (1+gramEigenvalueFormula Q z)*extendWeightSlice (2*Q-2) Q z (by omega) hz _ _
    rw [extendWeightSlice_at,hc p,hcz]
  · have hg₀ : g i = 0 := threeGram_extend_off Q z hQ hz _ i hi
    have hv₀ : v i = 0 := extendWeightSlice_off (2*Q-2) Q z (by omega) hz _ i hi
    rw [hg₀,hv₀,mul_zero]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_Descendants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem threeGram_transpose (Q : ℕ) : (threeGram Q)ᵀ = threeGram Q := by
  ext a b
  simp only [Matrix.transpose_apply,threeGram_entry]
  have hd : (if b=a then (1 : ℝ) else 0) = (if a=b then 1 else 0) := by
    by_cases h : a=b
    · simp [h]
    · simp [h,Ne.symm h]
  rw [hd]
  congr 2
  apply Finset.sum_congr rfl
  intro t ht
  ring

theorem threeGram_lowering (Q : ℕ) (hQ : 0 < Q) :
    threeGram Q * (totalRaise (2*Q-2) Q)ᵀ = (totalRaise (2*Q-2) Q)ᵀ * threeGram Q := by
  have h := congrArg Matrix.transpose (threeGram_raising_s50 Q hQ)
  simpa only [Matrix.transpose_mul,threeGram_transpose] using h.symm

theorem coupledDescendant_succ (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) (n : ℕ) :
    coupledDescendant Q z hQ hz (n+1) =
      (totalRaise (2*Q-2) Q)ᵀ *ᵥ coupledDescendant Q z hQ hz n := by
  simp only [coupledDescendant,pow_succ',Matrix.mulVec_mulVec]

theorem threeGram_descendant_eigen (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) (n : ℕ) :
    threeGram Q *ᵥ coupledDescendant Q z hQ hz n =
      (1+gramEigenvalueFormula Q z) • coupledDescendant Q z hQ hz n := by
  induction n with
  | zero => simpa [coupledDescendant] using threeGram_highest_eigen Q z hQ hz
  | succ n ih =>
    rw [coupledDescendant_succ,Matrix.mulVec_mulVec,threeGram_lowering Q (by omega),
      ← Matrix.mulVec_mulVec,ih,Matrix.mulVec_smul]

theorem threeGram_sub_one_descendant_eigen (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) (n : ℕ) :
    (threeGram Q-1) *ᵥ coupledDescendant Q z hQ hz n =
      gramEigenvalueFormula Q z • coupledDescendant Q z hQ hz n := by
  rw [Matrix.sub_mulVec,threeGram_descendant_eigen,Matrix.one_mulVec]
  funext i
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_DescendantNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem normalizedCoupledDescendant_eigen_s50_oai (Q z n : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    (threeGram Q-1) *ᵥ normalizedCoupledDescendant Q z hQ hz n =
      gramEigenvalueFormula Q z • normalizedCoupledDescendant Q z hQ hz n := by
  unfold normalizedCoupledDescendant
  rw [Matrix.mulVec_smul,threeGram_sub_one_descendant_eigen,smul_comm]

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.normalizedCoupledDescendant_eigen_s50_oai := @OAI.Laughlin.Spin.normalizedCoupledDescendant_eigen_s50_oai
