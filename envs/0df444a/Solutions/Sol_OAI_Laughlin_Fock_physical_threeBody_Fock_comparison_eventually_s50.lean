-- Prove2me | solution 1 for OAI.Laughlin.Fock.physical_threeBody_Fock_comparison_eventually_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:48:06.537727+00:00
-- url     : https://prove2.me/submissions/1e95ee5f-0723-4d76-a785-2a60d4aaaf78

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L020
import Definitions.Def_OAIQ050L021
import Theorems.Thm_OAI_Laughlin_Fock_physical_threeBody_Fock_haar_real_s50
import Theorems.Thm_OAI_Laughlin_Fock_physical_threeBody_Fock_null_s50
import Theorems.Thm_OAI_Laughlin_Fock_physical_threeBody_projector_nonneg_s50
import Theorems.Thm_OAI_Laughlin_Spin_source_threeBody_trace_strict_eventually_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_RankTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem realOuter_quadratic {I : Type*} [Fintype I] (u v x : I → ℝ) :
    dotProduct x (realOuter u v *ᵥ x) = dotProduct x u * dotProduct x v := by
  simp only [dotProduct,Matrix.mulVec,realOuter]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem threeSpinProjector_trace (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1))
    (M : Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℝ) :
    Matrix.trace (threeSpinProjector Q hQ z * M) =
      ∑ n : Fin (coupledWeight Q z.val+1),
        dotProduct (normalizedCoupledDescendant Q z.val hQ (by omega) n.val)
          (M *ᵥ normalizedCoupledDescendant Q z.val hQ (by omega) n.val) := by
  let B := coupledBasisMatrix Q hQ
  have he : Matrix.trace (threeSpinProjector Q hQ z * M) =
      Matrix.trace (coupledSelector Q z * (Bᵀ*M*B)) := by
    change Matrix.trace (B*coupledSelector Q z*Bᵀ*M) = _
    calc
      _ = Matrix.trace ((B*coupledSelector Q z)*(Bᵀ*M)) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((Bᵀ*M)*(B*coupledSelector Q z)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((Bᵀ*M*B)*coupledSelector Q z) := by simp only [Matrix.mul_assoc]
      _ = _ := Matrix.trace_mul_comm _ _
  rw [he]
  unfold coupledSelector
  simp only [Matrix.trace,Matrix.diag,Matrix.diagonal_mul]
  rw [Fintype.sum_sigma]
  simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Matrix.mul_apply,Matrix.transpose_apply,B,coupledBasisMatrix,Matrix.mulVec,dotProduct]
  simp only [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_PhysicalMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem pairOrbitalUnit_dot (Q p j : ℕ) (hp : p < 2*Q-2+1) (hj : j ≤ Q)
    (v : PairOrbitalIndex Q → ℝ) :
    dotProduct v (pairOrbitalUnit Q p j) = v (⟨p,hp⟩,⟨j,by omega⟩) := by
  classical
  simp only [dotProduct,pairOrbitalUnit,mul_ite,mul_one,mul_zero]
  have he : ∀ i : PairOrbitalIndex Q, (i.1.val=p ∧ i.2.val=j) ↔ i=(⟨p,hp⟩,⟨j,by omega⟩) := by
    intro i
    constructor
    · rintro ⟨h1,h2⟩; exact Prod.ext (Fin.ext h1) (Fin.ext h2)
    · intro h; subst i; exact ⟨rfl,rfl⟩
  simp_rw [he]
  simp

theorem threeBodyLevelMatrix_quadratic (Q t T : ℕ) (ell : ℤ) (entries : List (ℕ × ℕ × ℤ))
    (v : PairOrbitalIndex Q → ℝ) :
    dotProduct v (threeBodyLevelMatrix Q t T ell entries *ᵥ v) =
      2*((ell : ℝ)/10^7)*dotProduct v (pairOrbitalUnit Q t (T-t))*
        dotProduct v (threeBodyLevelVector Q t T entries) +
      (dotProduct v (threeBodyLevelVector Q t T entries))^2 := by
  simp only [threeBodyLevelMatrix,Matrix.add_mulVec,Matrix.smul_mulVec,
    dotProduct_add,dotProduct_smul,realOuter_quadratic,smul_eq_mul]
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_TraceReadout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem phasedThreeDescendant_off (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (n : ℕ)
    (i : PairOrbitalIndex Q) (hi : i.1.val+i.2.val ≠ z.val+n) :
    phasedThreeDescendant Q hQ z n i = 0 := by
  have hh := genericUnitDescendant_off (2*Q-2) Q z.val n (by omega) (by omega) i hi
  change (-1 : ℝ)^z.val * genericUnitDescendant (2*Q-2) Q z.val (by omega) (by omega) n i = 0
  rw [hh,mul_zero]

theorem phasedThreeDescendant_at_level (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (T p j : ℕ)
    (hz : z.val ≤ T) (hT : T ≤ Q) (hpj : p+j=T) :
    phasedThreeDescendant Q hQ z (T-z.val) (⟨p,by omega⟩,⟨j,by omega⟩) =
      physicalCouplingCoefficient (2*Q-2) Q z.val T p := by
  rw [physicalCouplingCoefficient,dite_eq_left ⟨hz,by omega,by omega,hT⟩]
  have hj : T-p=j := by omega
  subst j
  rfl

theorem threeBodyLevelVector_dot {Q : ℕ} (v : PairOrbitalIndex Q → ℝ) (t T : ℕ)
    (entries : List (ℕ × ℕ × ℤ)) :
    dotProduct v (threeBodyLevelVector Q t T entries) =
      (entries.map (fun e => if e.1+e.2.1=T then sourceAlpha t e *
        dotProduct v (pairOrbitalUnit Q e.1 e.2.1) else 0)).sum := by
  induction entries with
  | nil => simp [threeBodyLevelVector]
  | cons e es ih =>
    simp only [threeBodyLevelVector,List.map_cons,List.sum_cons] at ih ⊢
    rw [dotProduct_add,ih]
    by_cases h : e.1+e.2.1=T
    · simp [h,dotProduct_smul,mul_comm]
    · simp [h]

theorem phasedThreeDescendant_unit_off (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (n p j : ℕ)
    (h : p+j ≠ z.val+n) :
    dotProduct (phasedThreeDescendant Q hQ z n) (pairOrbitalUnit Q p j) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  simp only [pairOrbitalUnit]
  split_ifs with he
  · rw [phasedThreeDescendant_off Q hQ z n i (by omega),zero_mul]
  · exact mul_zero _

theorem threeBodyLevelVector_descendant_off (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (n t T : ℕ)
    (entries : List (ℕ × ℕ × ℤ)) (h : T ≠ z.val+n) :
    dotProduct (phasedThreeDescendant Q hQ z n) (threeBodyLevelVector Q t T entries) = 0 := by
  rw [threeBodyLevelVector_dot]
  have he : entries.map (fun e => if e.1+e.2.1=T then sourceAlpha t e *
      dotProduct (phasedThreeDescendant Q hQ z n) (pairOrbitalUnit Q e.1 e.2.1) else 0) = entries.map (fun _ => (0 : ℝ)) := by
    apply List.map_congr_left
    intro e he
    split_ifs with hT
    · rw [phasedThreeDescendant_unit_off Q hQ z n e.1 e.2.1 (by omega),mul_zero]
    · rfl
  rw [he]
  simp

theorem threeBodyLevelVector_descendant (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (t T : ℕ)
    (entries : List (ℕ × ℕ × ℤ)) (hz : z.val ≤ T) (hT : T ≤ Q) :
    dotProduct (phasedThreeDescendant Q hQ z (T-z.val)) (threeBodyLevelVector Q t T entries) =
      threeBodyInner (physicalCouplingCoefficient (2*Q-2) Q) z.val T t entries := by
  rw [threeBodyLevelVector_dot]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  split_ifs with h
  · rw [pairOrbitalUnit_dot Q e.1 e.2.1 (by omega) (by omega),
      phasedThreeDescendant_at_level Q hQ z T e.1 e.2.1 hz hT h]
  · rfl

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_LevelTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

 theorem phasedThreeDescendant_quadratic (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (n : ℕ)
    (M : Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℝ) :
    dotProduct (phasedThreeDescendant Q hQ z n) (M *ᵥ phasedThreeDescendant Q hQ z n) =
      dotProduct (normalizedCoupledDescendant Q z.val hQ (by omega) n)
        (M *ᵥ normalizedCoupledDescendant Q z.val hQ (by omega) n) := by
  simp only [phasedThreeDescendant,Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  have hs : ((-1 : ℝ)^z.val)^2=1 := by rw [← pow_mul,mul_comm z.val 2,pow_mul]; norm_num
  nlinarith only [congrArg (fun s : ℝ => s * dotProduct
    (normalizedCoupledDescendant Q z.val hQ (by omega) n)
    (M *ᵥ normalizedCoupledDescendant Q z.val hQ (by omega) n)) hs]

theorem threeBodyLevelMatrix_descendant_off (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (n t T : ℕ)
    (ell : ℤ) (entries : List (ℕ × ℕ × ℤ)) (h : T ≠ z.val+n) :
    dotProduct (phasedThreeDescendant Q hQ z n)
      (threeBodyLevelMatrix Q t T ell entries *ᵥ phasedThreeDescendant Q hQ z n) = 0 := by
  rw [threeBodyLevelMatrix_quadratic,threeBodyLevelVector_descendant_off Q hQ z n t T entries h]
  ring

theorem threeBodyLevelMatrix_descendant (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (t T : ℕ)
    (ell : ℤ) (entries : List (ℕ × ℕ × ℤ)) (hz : z.val ≤ T) (hT : T ≤ Q) (ht : t ≤ T) :
    dotProduct (phasedThreeDescendant Q hQ z (T-z.val))
      (threeBodyLevelMatrix Q t T ell entries *ᵥ phasedThreeDescendant Q hQ z (T-z.val)) =
      physicalThreeBodyLevel Q z.val T t ell entries := by
  rw [threeBodyLevelMatrix_quadratic,threeBodyLevelVector_descendant Q hQ z t T entries hz hT,
    pairOrbitalUnit_dot Q t (T-t) (by omega) (by omega),
    phasedThreeDescendant_at_level Q hQ z T t (T-t) hz hT (by omega)]
  rfl

theorem threeBodyLevelMatrix_trace (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (t T : ℕ)
    (ell : ℤ) (entries : List (ℕ × ℕ × ℤ)) (hT : T ≤ Q) (ht : t ≤ T) :
    Matrix.trace (threeSpinProjector Q hQ z * threeBodyLevelMatrix Q t T ell entries) =
      if z.val ≤ T then physicalThreeBodyLevel Q z.val T t ell entries else 0 := by
  classical
  rw [threeSpinProjector_trace]
  simp_rw [← phasedThreeDescendant_quadratic]
  by_cases hz : z.val ≤ T
  · rw [ite_eq_left hz]
    have hn : T-z.val < coupledWeight Q z.val+1 := by unfold coupledWeight; omega
    rw [Finset.sum_eq_single (⟨T-z.val,hn⟩ : Fin (coupledWeight Q z.val+1))]
    · exact threeBodyLevelMatrix_descendant Q hQ z t T ell entries hz hT ht
    · intro n hn' hne
      apply threeBodyLevelMatrix_descendant_off
      intro he
      apply hne
      exact Fin.ext (by dsimp; omega)
    · simp
  · rw [ite_eq_right hz]
    apply Finset.sum_eq_zero
    intro n hn
    exact threeBodyLevelMatrix_descendant_off Q hQ z n.val t T ell entries (by omega)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_PhysicalTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Topology

 theorem trace_mul_list_sum {I : Type*} [Fintype I] (P : Matrix I I ℝ)
    (l : List (Matrix I I ℝ)) :
    Matrix.trace (P*l.sum) = (l.map (fun M => Matrix.trace (P*M))).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.sum_cons,List.map_cons,Matrix.mul_add,Matrix.trace_add,ih]

 theorem list_filter_sum_if {I : Type*} (l : List I) (p q : I → Prop)
    [DecidablePred p] [DecidablePred q] (f : I → ℝ) :
    ((l.filter p).map (fun i => if q i then f i else 0)).sum =
      ((l.filter (fun i => p i ∧ q i)).map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases hp : p a <;> by_cases hq : q a <;> simp [hp,hq,ih]

theorem source_physical_threeBody_trace_identity (Q : ℕ) (hQ : 15 ≤ Q) (z : Fin (Q+1)) :
    Matrix.trace (threeSpinProjector Q (by omega) z * physicalThreeBodyMatrix Q) =
      physicalThreeBodyTraceFormula Q z.val := by
  unfold physicalThreeBodyMatrix
  rw [trace_mul_list_sum]
  simp only [List.map_map,Function.comp_def]
  unfold physicalThreeBodyTraceFormula threeBodyTraceFormula
  apply congrArg List.sum
  apply List.map_congr_left
  intro row hrow
  rw [trace_mul_list_sum]
  simp only [List.map_map,Function.comp_def]
  have he : (((List.range 16).filter (fun T => row.1 ≤ T)).map
      (fun T => Matrix.trace (threeSpinProjector Q (by omega) z * threeBodyLevelMatrix Q row.1 T row.2.1 row.2.2))) =
      (((List.range 16).filter (fun T => row.1 ≤ T)).map
        (fun T => if z.val ≤ T then physicalThreeBodyLevel Q z.val T row.1 row.2.1 row.2.2 else 0)) := by
    apply List.map_congr_left
    intro T hT
    simp only [List.mem_filter,List.mem_range,decide_eq_true_eq] at hT
    exact threeBodyLevelMatrix_trace Q (by omega) z row.1 T row.2.1 row.2.2 (by omega) hT.2
  rw [he,list_filter_sum_if]
  simp only [physicalThreeBodyLevel,max_le_iff,and_comm]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_FockTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix

theorem threeBody_dimension_ratio (Q z : ℕ) (hQ : 4 ≤ Q) (hz : z ≤ Q) :
    ((coupledWeight Q z+1 : ℕ)/(2*Q-2+1 : ℕ) : ℝ) =
      (3*(Q : ℝ)-1-2*(z : ℝ))/(2*(Q : ℝ)-1) := by
  have hn : ((coupledWeight Q z+1 : ℕ) : ℝ)=3*(Q : ℝ)-1-2*(z : ℝ) := by
    unfold coupledWeight
    rw [Nat.cast_add,Nat.cast_sub (by omega : 2*z ≤ 3*Q-2),
      Nat.cast_sub (by omega : 2 ≤ 3*Q)]
    push_cast
    ring
  have hd : ((2*Q-2+1 : ℕ) : ℝ)=2*(Q : ℝ)-1 := by
    rw [Nat.cast_add,Nat.cast_sub (by omega : 2 ≤ 2*Q)]
    push_cast
    ring
  rw [hn,hd]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_TraceComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem eventually_list_all {I : Type*} (l : List I) (P : ℕ → I → Prop)
    (h : ∀ i ∈ l, ∀ᶠ Q in atTop, P Q i) : ∀ᶠ Q in atTop, ∀ i ∈ l, P Q i := by
  induction l with
  | nil => simp
  | cons a l ih =>
    filter_upwards [h a (by simp),ih (fun i hi => h i (by simp [hi]))] with Q ha hl
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact ha
    · exact hl i hi

theorem source_threeBody_physical_traces_strict_eventually :
    ∀ᶠ Q : ℕ in atTop, ∃ hQ : 15 ≤ Q, ∀ z : Fin (Q+1),
      z.val ∈ [2,4,5,6,7,8,9,10,11,12,13,14,15] →
      Matrix.trace (threeSpinProjector Q (by omega) z * physicalThreeBodyMatrix Q) <
        threeBodyDimensionRatio Q z.val * gramEigenvalueFormula Q z.val := by
  have hall := eventually_list_all [2,4,5,6,7,8,9,10,11,12,13,14,15]
    (fun Q z => physicalThreeBodyTraceFormula Q z < threeBodyDimensionRatio Q z * gramEigenvalueFormula Q z)
    source_threeBody_trace_strict_eventually_s50
  filter_upwards [eventually_ge_atTop 15,hall] with Q hQ h
  refine ⟨hQ,?_⟩
  intro z hz
  rw [source_physical_threeBody_trace_identity Q hQ]
  exact h z.val hz

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_FockComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory Filter
open scoped BigOperators Matrix

theorem physicalThreeBodyTraceFormula_high (Q z : ℕ) (hz : 15 < z) :
    physicalThreeBodyTraceFormula Q z=0 := by
  have he (t : ℕ) : (List.range 16).filter (fun T => max z t ≤ T) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro T hT
    simp only [List.mem_range] at hT
    simp only [decide_eq_true_eq,max_le_iff]
    omega
  simp only [physicalThreeBodyTraceFormula,threeBodyTraceFormula,he,List.map_nil,List.sum_nil,
    List.map_const',List.sum_replicate,nsmul_zero]

theorem physical_threeBody_Fock_comparison_eventually_s50_oai :
    ∀ᶠ Q : ℕ in atTop, ∃ hQ : 15 ≤ Q, ∀ x : Space Q,
      (2*Q-2+1 : ℕ) * (∫ g, contractionForm Q (sourceThreeEnd Q)
        ((physicalThreeBodyMatrix Q).map Complex.ofReal) (exteriorRotation Q g⁻¹ x) ∂sourceHaar).re ≤
      ∑ z : Fin (Q+1), if z.val ≤ 15 then gramEigenvalueFormula Q z.val *
        (contractionForm Q (sourceThreeEnd Q)
          ((threeSpinProjector Q (by omega) z).map Complex.ofReal) x).re else 0 := by
  filter_upwards [source_threeBody_physical_traces_strict_eventually] with Q h
  obtain ⟨hQ,hs⟩ := h
  refine ⟨hQ,fun x => ?_⟩
  rw [physical_threeBody_Fock_haar_real_s50 Q hQ,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  by_cases h15 : z.val ≤ 15
  · rw [ite_eq_left h15]
    by_cases hn : z.val=0 ∨ z.val=1 ∨ z.val=3
    · rw [physical_threeBody_Fock_null_s50 Q (by omega) z hn]
      simp
    · have hm : z.val ∈ [2,4,5,6,7,8,9,10,11,12,13,14,15] := by
        simp only [List.mem_cons]
        omega
      have ht := hs z hm
      rw [source_physical_threeBody_trace_identity Q hQ] at ht
      have hr := threeBody_dimension_ratio Q z.val (by omega) (by omega)
      change _ = threeBodyDimensionRatio Q z.val at hr
      rw [← hr] at ht
      have ha : (0 : ℝ) < (2*Q-2+1 : ℕ) := by positivity
      have hd : (0 : ℝ) < (coupledWeight Q z.val+1 : ℕ) := by positivity
      have hc : (2*Q-2+1 : ℕ) *
          (physicalThreeBodyTraceFormula Q z.val/(coupledWeight Q z.val+1 : ℕ)) ≤
            gramEigenvalueFormula Q z.val := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ hd).mpr
        have hh := mul_lt_mul_of_pos_left ht ha
        have he : ((2*Q-2+1 : ℕ) : ℝ) *
            (((coupledWeight Q z.val+1 : ℕ)/(2*Q-2+1 : ℕ) : ℝ) * gramEigenvalueFormula Q z.val) =
            gramEigenvalueFormula Q z.val*(coupledWeight Q z.val+1 : ℕ) := by
          field_simp
        rw [he] at hh
        exact hh.le
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc
        (physical_threeBody_projector_nonneg_s50 Q (by omega) z x)
  · rw [ite_eq_right h15,physicalThreeBodyTraceFormula_high Q z.val (by omega)]
    simp

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.physical_threeBody_Fock_comparison_eventually_s50_oai := @OAI.Laughlin.Fock.physical_threeBody_Fock_comparison_eventually_s50_oai
