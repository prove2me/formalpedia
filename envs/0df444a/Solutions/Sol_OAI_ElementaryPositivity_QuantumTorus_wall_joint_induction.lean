-- Prove2me | solution 1 for OAI.ElementaryPositivity.QuantumTorus.wall_joint_induction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T20:04:13.35345+00:00
-- url     : https://prove2.me/submissions/434f1492-d62e-46dc-9753-d9bec58ba3c6

import Mathlib
import Definitions.Def_OAIQ368Chrom007
import Definitions.Def_OAIQ368Chrom013
import Definitions.Def_OAIQ368Chrom054
import Definitions.Def_OAIQ368Chrom073
import Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_finiteInput_zero_rootClosure

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_WeightedTorusSeries
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceZeroUnique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.WeightedTorusSeries
open ElementaryPositivity.RawShuffle ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (w : I → ℕ) [hw : Fact (∀i,0<w i)]

lemma sum_split {A : Type*} [AddCommMonoid A] (n : ℕ) (H : (I→ℕ) → (I→ℕ) → A) :
    (∑d : Slice w n,∑s : DimensionSplit d.val,H s.left s.right)=
      ∑k : Fin (n+1),∑d : Slice w k.val,∑e : Slice w (n-k.val),H d.val e.val := by
  classical
  let E := (splitSliceEquiv w n).trans (pairSliceEquiv w n).symm
  calc
    _ = ∑x : (Σ d : Slice w n,DimensionSplit d.val),H x.2.left x.2.right :=
      (Fintype.sum_sigma (fun x : (Σ d : Slice w n,DimensionSplit d.val)=>H x.2.left x.2.right)).symm
    _ = ∑y : (Σ k : Fin (n+1),Slice w k.val × Slice w (n-k.val)),H y.2.1.val y.2.2.val :=
      Fintype.sum_equiv E _ _ (fun _=>rfl)
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro k hk
      exact Fintype.sum_prod_type _

variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)

attribute [local instance] OAI.ElementaryPositivity.WeightedTorusSeries.instRingTorus
attribute [local instance] OAI.ElementaryPositivity.WeightedTorusSeries.instAddCommMonoidTorus
local instance instAddGroupTorus_re19c27_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
lemma monomial_sum {A : Type*} (s : Finset A) (m : M) (f : A → R) :
    Torus.monomial v Ω m (∑i∈s,f i)=∑i∈s,Torus.monomial v Ω m (f i) := by
  exact map_sum (Finsupp.singleAddHom m) f s

lemma pushCoeff_convolution (f g : (I→ℕ) → R) (n : ℕ) :
    pushCoeff w v Ω P (convolution v Ω P f g) n=
      ∑k : Fin (n+1),pushCoeff w v Ω P f k.val*pushCoeff w v Ω P g (n-k.val) := by
  classical
  simp only [pushCoeff,convolution,monomial_sum,torus_sum_mul,torus_mul_sum,
    Torus.monomial_mul_monomial]
  have H:=sum_split w n (fun d e=>Torus.monomial v Ω (P d+P e)
    (f d*g e*↑(v^(Ω (P d) (P e)))))
  convert H using 1
  · apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro s hs
    rw [←map_add,DimensionSplit.left_add_right]
  · apply Finset.sum_congr rfl
    intro k hk
    exact Finset.sum_comm

lemma push_convolution (f g : (I→ℕ) → R) :
    push w v Ω P (convolution v Ω P f g)=push w v Ω P f*push w v Ω P g := by
  apply PowerSeries.ext
  intro n
  simp only [push,coeff_mk,coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,←Fin.sum_univ_eq_sum_range]
  exact pushCoeff_convolution w v Ω P f g n

end
end ElementaryPositivity.WeightedTorusSeries

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_InputTorusEnergy
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ)

lemma crossInteraction_offdiagonal (d : I → ℕ) :
    crossInteraction a d=∑ i,∑ j,if i=j then 0 else (a i j:ℤ)*d i*d j := by
  unfold crossInteraction
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i hi
  have H : (∑ j,(a i j:ℤ)*d i*d j)=
      (a i i:ℤ)*(d i:ℤ)^2+∑ j,if i=j then 0 else (a i j:ℤ)*d i*d j := by
    calc
      _ = ∑ j,((if i=j then (a i i:ℤ)*(d i:ℤ)^2 else 0)+
          if i=j then 0 else (a i j:ℤ)*d i*d j) := by
        apply Finset.sum_congr rfl; intro j hj
        by_cases h : i=j
        · subst j; simp [pow_two,mul_assoc]
        · simp [h]
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  linear_combination H

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma euler_skew_sum (a : I → I → ℕ) (d e : I → ℕ) :
    eulerForm a d e-eulerForm a e d=
      ∑ i,∑ j,((a j i:ℤ)-a i j)*d i*e j := by
  have H₁ : (∑ i,(d i:ℤ)*e i)=(∑ i,(e i:ℤ)*d i) := by
    apply Finset.sum_congr rfl; intro i hi; ring
  have H₂ : (∑ i,∑ j,(a i j:ℤ)*e i*d j)=(∑ i,∑ j,(a j i:ℤ)*d i*e j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i hi
    apply Finset.sum_congr rfl; intro j hj
    ring
  simp only [eulerForm,H₁,H₂,sub_mul,Finset.sum_sub_distrib]
  ring

omit [DecidableEq I] in
lemma euler_skew_plane (a : I → I → ℕ) (c η : I → ℝ) (t : ℝ)
    (ha : ∀ i j,(a j i:ℝ)-a i j=t*(η i*c j-c i*η j)) (d e : I → ℕ) :
    (eulerForm a d e:ℝ)-eulerForm a e d=
      t*(mass η d*mass c e-mass c d*mass η e) := by
  have H:=congrArg (fun k : ℤ=>(k:ℝ)) (euler_skew_sum a d e)
  push_cast at H
  rw [H]
  simp only [ha]
  have HS (f g : I → ℝ) : (∑ i,∑ j,f i*g j)=(∑ i,f i)*(∑ j,g j) := by
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
  calc
    _ = t*((∑ i,∑ j,(d i:ℝ)*η i*((e j:ℝ)*c j))-
        ∑ i,∑ j,(d i:ℝ)*c i*((e j:ℝ)*η j)) := by
      simp only [mul_sub,Finset.mul_sum,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i hi
      apply Finset.sum_congr rfl; intro j hj
      ring
    _ = _ := by rw [HS,HS]; rfl

omit [DecidableEq I] in
theorem slopeEulerSymmetric_of_plane (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (t : ℝ)
    (ha : ∀ i j,(a j i:ℝ)-a i j=t*(η i*c j-c i*η j)) :
    ∀ θ,SlopeEulerSymmetric a c η θ := by
  intro θ d e hd he hs ht
  have H:=euler_skew_plane a c η t ha d e
  rw [mass_eq c η hc d,mass_eq c η hc e,hs,ht] at H
  have Hz : (eulerForm a d e:ℝ)-eulerForm a e d=0 := by
    rw [H]; ring
  exact_mod_cast sub_eq_zero.mp Hz
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_HNSeries
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.WeightedTorusSeries
open ElementaryPositivity.RawShuffle ElementaryPositivity.QuantumTorus PowerSeries
noncomputable section
universe u
variable {I : Type u} [Fintype I]
variable (w : I → ℕ) [hw : Fact (∀i,0<w i)]

variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)

local instance instAddCommMonoidTorus_1_re19c27_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
lemma pushCoeff_zero (f : (I→ℕ) → R) :
    pushCoeff w v Ω P f 0=Torus.monomial v Ω 0 (f 0) := by
  classical
  rw [pushCoeff,Fintype.sum_unique]
  change Torus.monomial v Ω (P 0) (f 0)=_
  rw [map_zero]
lemma push_constant (f : (I→ℕ) → R) (hf : f 0=1) : constantCoeff (push w v Ω P f)=1 := by
  rw [push,constantCoeff_mk,pushCoeff_zero,hf]
  rfl

end
end ElementaryPositivity.WeightedTorusSeries

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_SupportedConvolution
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.DimensionSplit.left_swap _root_.OAI.ElementaryPositivity.RawShuffle.DimensionSplit.right_swap _root_.OAI.ElementaryPositivity.RawShuffle.DimensionSplit.swap_swap _root_.OAI.ElementaryPositivity.RawShuffle.cutShapeDimensionEquiv_left _root_.OAI.ElementaryPositivity.RawShuffle.cutShapeDimensionEquiv_right _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.WeightedTorusSeries
open ElementaryPositivity.RawShuffle
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I R M : Type*} [Fintype I] [DecidableEq I] [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)

omit [Fintype I] in
lemma restrictDim_supported (S : Finset I) (d : I → ℕ) : Supported S (restrictDim S d) := by
  intro i hi
  simp [restrictDim,hi]

omit [Fintype I] in
lemma supported_add (S T : Finset I) (d e : I → ℕ) (hd : Supported S d) (he : Supported T e) :
    Supported (S∪T) (d+e) := by
  intro i hi
  have H : i∉S ∧ i∉T := by simpa only [Finset.mem_union,not_or] using hi
  simp [hd i H.1,he i H.2]

omit [Fintype I] in
lemma restrictDim_split (S T : Finset I) (hST : Disjoint S T) (d : I → ℕ)
    (hd : Supported (S∪T) d) : restrictDim S d+restrictDim T d=d := by
  funext i
  by_cases hS : i∈S
  · have hT : i∉T := fun hi=>Finset.disjoint_left.mp hST hS hi
    simp [restrictDim,hS,hT]
  · by_cases hT : i∈T
    · simp [restrictDim,hS,hT]
    · simp [restrictDim,hS,hT,hd i (by simp [hS,hT])]

omit [Fintype I] in
lemma split_left_restrict (S T : Finset I) (hST : Disjoint S T) (d : I → ℕ)
    (s : DimensionSplit d) (hs : Supported S s.left) (ht : Supported T s.right) :
    s.left=restrictDim S d := by
  funext i
  by_cases hS : i∈S
  · have hT : i∉T := fun hi=>Finset.disjoint_left.mp hST hS hi
    have H:=congrFun (DimensionSplit.left_add_right s) i
    simp only [Pi.add_apply,ht i hT,add_zero] at H
    simp [restrictDim,hS,H]
  · simp [restrictDim,hS,hs i hS]

lemma supported_convolution (S T : Finset I) (hST : Disjoint S T)
    (f g : (I → ℕ) → R) (d : I → ℕ) :
    convolution v Ω P (supportedCoefficient S f) (supportedCoefficient T g) d=
      if Supported (S∪T) d then
        f (restrictDim S d)*g (restrictDim T d)*↑(v^(Ω (P (restrictDim S d)) (P (restrictDim T d))))
      else 0 := by
  classical
  unfold convolution
  by_cases hd : Supported (S∪T) d
  · rw [ite_eq_left hd]
    let s₀:=DimensionSplit.ofPair (restrictDim S d) (restrictDim T d) (restrictDim_split S T hST d hd)
    rw [Finset.sum_eq_single s₀]
    · simp [s₀,supportedCoefficient,restrictDim_supported]
    · intro s hs hne
      by_cases hS : Supported S s.left
      · by_cases hT : Supported T s.right
        · exact (hne (DimensionSplit.ext (split_left_restrict S T hST d s hS hT))).elim
        · simp [supportedCoefficient,hT]
      · simp [supportedCoefficient,hS]
    · simp
  · rw [ite_eq_right hd]
    apply Finset.sum_eq_zero
    intro s hs
    by_cases hS : Supported S s.left
    · have hT : ¬Supported T s.right := by
        intro hT
        have H:=supported_add S T s.left s.right hS hT
        rw [DimensionSplit.left_add_right] at H
        exact hd H
      simp [supportedCoefficient,hT]
    · simp [supportedCoefficient,hS]

end
end ElementaryPositivity.WeightedTorusSeries

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_InputOrderedEnergy
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open WeightedTorusSeries
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ)

omit [DecidableEq I] in
lemma crossInteraction_euler (d : I → ℕ) :
    crossInteraction a d=crossDiagonal a d-eulerForm a d d := by
  have H : crossDiagonal a d=(∑ i,(d i:ℤ)*(d i:ℤ))-∑i,(a i i:ℤ)*(d i:ℤ)^2 := by
    rw [crossDiagonal,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [H,crossInteraction,eulerForm]
  ring

omit [DecidableEq I] in
lemma crossDiagonal_add_disjoint (d e : I → ℕ) (hde : ∀i,d i=0 ∨ e i=0) :
    crossDiagonal a (d+e)=crossDiagonal a d+crossDiagonal a e := by
  rw [crossDiagonal,crossDiagonal,crossDiagonal,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rcases hde i with H|H <;> simp [H]

omit [DecidableEq I] in
lemma eulerForm_zero_separated (d e : I → ℕ) (hde : ∀i,d i=0 ∨ e i=0)
    (ha : ∀i j,d i≠0 → e j≠0 → a i j=0) : eulerForm a d e=0 := by
  unfold eulerForm
  have H₁ : (∑i,(d i:ℤ)*(e i:ℤ))=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rcases hde i with H|H <;> simp [H]
  have H₂ : (∑ i,∑j,(a i j:ℤ)*(d i:ℤ)*(e j:ℤ))=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hd : d i=0
    · simp [hd]
    · by_cases he : e j=0
      · simp [he]
      · simp [ha i j hd he]
  rw [H₁,H₂,sub_self]

omit [DecidableEq I] in
lemma crossInteraction_add_separated (d e : I → ℕ) (hde : ∀i,d i=0 ∨ e i=0)
    (ha : ∀i j,d i≠0 → e j≠0 → a i j=0) :
    crossInteraction a (d+e)=crossInteraction a d+crossInteraction a e+
      (eulerForm a d e-eulerForm a e d) := by
  rw [crossInteraction_euler,crossInteraction_euler,crossInteraction_euler,
    crossDiagonal_add_disjoint a d e hde,eulerForm_add_left,eulerForm_add_right,eulerForm_add_right,
    eulerForm_zero_separated a d e hde ha]
  ring

lemma crossInteraction_restrict_union (S T : Finset I) (hST : Disjoint S T)
    (ha : ∀i∈S,∀j∈T,a i j=0) (d : I → ℕ) (hd : Supported (S∪T) d) :
    crossInteraction a d=crossInteraction a (restrictDim S d)+crossInteraction a (restrictDim T d)+
      (eulerForm a (restrictDim S d) (restrictDim T d)-eulerForm a (restrictDim T d) (restrictDim S d)) := by
  conv_lhs => rw [←restrictDim_split S T hST d hd]
  apply crossInteraction_add_separated
  · intro i
    by_cases hS : i∈S
    · exact Or.inr (restrictDim_supported T d i (fun hT=>Finset.disjoint_left.mp hST hS hT))
    · exact Or.inl (restrictDim_supported S d i hS)
  · intro i j hi hj
    apply ha
    · by_contra H
      exact hi (restrictDim_supported S d i H)
    · by_contra H
      exact hj (restrictDim_supported T d j H)

end
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_InputOrderedProduct
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.WeightedTorusSeries
open ElementaryPositivity.RawShuffle QuantumTorus PowerSeries
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I R M : Type*} [Fintype I] [DecidableEq I] [CommRing R] [AddCommGroup M]
variable (a : I → I → ℕ) (u : I → ℕ → R)
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)
variable (hΩ : ∀d e,Ω (P d) (P e)=eulerForm a d e-eulerForm a e d)

include hΩ in
lemma partialCoefficient_union (S T : Finset I) (hST : Disjoint S T)
    (ha : ∀i∈S,∀j∈T,a i j=0) :
    partialCoefficient a u v (S∪T)=convolution v Ω P
      (partialCoefficient a u v S) (partialCoefficient a u v T) := by
  funext d
  rw [partialCoefficient,partialCoefficient,partialCoefficient,supported_convolution v Ω P S T hST]
  unfold supportedCoefficient
  by_cases hd : Supported (S∪T) d
  · rw [ite_eq_left hd,ite_eq_left hd]
    dsimp only
    rw [Finset.prod_union hST,crossInteraction_restrict_union a S T hST ha d hd,←hΩ]
    have hS : (∏i∈S,u i (restrictDim S d i))=∏i∈S,u i (d i) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [restrictDim,ite_eq_left hi]
    have hT : (∏i∈T,u i (restrictDim T d i))=∏i∈T,u i (d i) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [restrictDim,ite_eq_left hi]
    rw [hS,hT,zpow_add,zpow_add,Units.val_mul,Units.val_mul]
    ring
  · rw [ite_eq_right hd,ite_eq_right hd]

variable (w : I → ℕ) [Fact (∀i,0<w i)]

omit [DecidableEq I] in
lemma partialCoefficient_empty (d : I → ℕ) :
    partialCoefficient a u v ∅ d=if d=0 then 1 else 0 := by
  have H : Supported ∅ d ↔ d=0 := by simp [Supported,funext_iff]
  simp only [partialCoefficient,supportedCoefficient,H,Finset.prod_empty,one_mul]
  split_ifs with hd
  · subst d
    simp [crossInteraction]
  · rfl

local instance partialCoefficientAddCommMonoid_re19c27_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
omit [DecidableEq I] in
lemma push_partial_empty : push w v Ω P (partialCoefficient a u v ∅)=1 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero=>
    rw [coeff_zero_eq_constantCoeff]
    rw [push_constant w v Ω P _ (by simp [partialCoefficient_empty])]
    simp
  | succ n=>
    simp only [push,coeff_mk,pushCoeff,coeff_one,show n+1≠0 from Nat.succ_ne_zero n,ite_false, if_false]
    apply Finset.sum_eq_zero
    intro d hd
    have H : d.val≠0 := by
      intro hzero
      have HH:=d.property
      rw [hzero,map_zero] at HH
      omega
    rw [partialCoefficient_empty,ite_eq_right H,Torus.monomial_zero]

include hΩ in
lemma push_partial_union (S T : Finset I) (hST : Disjoint S T)
    (ha : ∀i∈S,∀j∈T,a i j=0) :
    push w v Ω P (partialCoefficient a u v (S∪T))=
      push w v Ω P (partialCoefficient a u v S)*push w v Ω P (partialCoefficient a u v T) := by
  rw [partialCoefficient_union a u v Ω P hΩ S T hST ha,push_convolution]

include hΩ in

theorem push_partial_list (l : List I) (hl : l.Nodup) (ho : l.Pairwise fun i j=>a i j=0) :
    push w v Ω P (partialCoefficient a u v l.toFinset)=
      (l.map (fun i=>push w v Ω P (partialCoefficient a u v {i}))).prod := by
  induction l with
  | nil=> simpa using push_partial_empty a u v Ω P w
  | cons i l ih=>
    have hnil:=List.nodup_cons.mp hl
    have hord:=List.pairwise_cons.mp ho
    rw [List.toFinset_cons,←Finset.singleton_union]
    rw [push_partial_union a u v Ω P hΩ w {i} l.toFinset]
    · simp only [ih hnil.2 hord.2,List.map_cons,List.prod_cons]
    · simpa using hnil.1
    · intro j hj k hk
      have hji : j=i := by simpa using hj
      subst j
      exact hord.1 k (List.mem_toFinset.mp hk)

end
end ElementaryPositivity.WeightedTorusSeries

end
section
namespace ElementaryPositivity.WeightedTorusSeries
open QuantumTorus PowerSeries
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I R M : Type*} [Fintype I] [DecidableEq I] [CommRing R] [AddCommGroup M]
variable (w : I → ℕ) [hw : Fact (∀i,0<w i)]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)

omit hw in
lemma weight_single (i : I) (k : ℕ) : weight w (Pi.single i k)=k*w i := by
  simp [weight,Pi.single_apply,ite_mul]

omit [Fintype I] in
lemma supported_single_eq (i : I) (d : I → ℕ) (hd : Supported {i} d) : d=Pi.single i (d i) := by
  funext j
  by_cases hj : j=i
  · subst j; simp
  · simp [hj,hd j (by simpa)]

omit [Fintype I] in
lemma single_nsmul (i : I) (k : ℕ) : Pi.single i k=k • (Pi.single i 1 : I → ℕ) := by
  funext j
  by_cases hj : j=i
  · subst j; simp
  · simp [hj]

local instance pushAxisAddCommMonoid_re19c27_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
lemma push_axis (i : I) (f : PowerSeries R) :
    push w v Ω P (supportedCoefficient {i} (fun d=>coeff (d i) f))=
      weightedRay v Ω (w i) (P (Pi.single i 1)) f := by
  apply PowerSeries.ext
  intro n
  rw [push,coeff_mk,pushCoeff,coeff_weightedRay]
  by_cases hn : w i∣n
  · rw [ite_eq_left hn]
    let d₀ : Slice w n:=⟨Pi.single i (n/w i),by
      rw [weight_single,Nat.div_mul_cancel hn]⟩
    rw [Finset.sum_eq_single d₀]
    · have HS : Supported {i} d₀.val := by
        intro j hj
        have H : j≠i := by simpa using hj
        simp [d₀,H]
      rw [supportedCoefficient,ite_eq_left HS]
      dsimp only [d₀]
      rw [Pi.single_eq_same,single_nsmul,map_nsmul]
    · intro d hd hne
      have HS : ¬Supported {i} d.val := by
        intro HS
        apply hne
        apply Subtype.ext
        have HE:=d.property
        rw [supported_single_eq i d.val HS,weight_single] at HE
        have HV : d.val i=n/w i := by
          calc
            d.val i=(d.val i*w i)/(w i) := (Nat.mul_div_left _ (hw.out i)).symm
            _=n/(w i) := congrArg (fun x=>x/(w i)) HE
        rw [supported_single_eq i d.val HS,HV]
      rw [supportedCoefficient,ite_eq_right HS,Torus.monomial_zero]
    · simp
  · rw [ite_eq_right hn]
    apply Finset.sum_eq_zero
    intro d hd
    have HS : ¬Supported {i} d.val := by
      intro HS
      apply hn
      have HE:=d.property
      rw [supported_single_eq i d.val HS,weight_single] at HE
      exact ⟨d.val i,by rw [Nat.mul_comm,HE]⟩
    rw [supportedCoefficient,ite_eq_right HS,Torus.monomial_zero]

end
end ElementaryPositivity.WeightedTorusSeries

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentContinuity
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder _root_.OAI.ElementaryPositivity.RawShuffle.globalStringIndexLinearOrder _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LaurentPrecision
open Filter
open scoped LaurentSeries

lemma lowerBound_iff_orderTop (b : ℤ) (f : Series) :
    LowerBound b f ↔ (b : WithTop ℤ)≤f.orderTop := by
  rw [HahnSeries.le_orderTop_iff_forall]
  simp only [LowerBound,WithTop.coe_lt_coe]

lemma lowerBound_order (f : Series) : LowerBound f.order f :=
  fun _ h=>HahnSeries.coeff_eq_zero_of_lt_order h

lemma lowerBound_add {b : ℤ} {f g : Series} (hf : LowerBound b f) (hg : LowerBound b g) :
    LowerBound b (f+g) := by
  intro j hj
  simp only [HahnSeries.coeff_add,hf j hj,hg j hj,add_zero]

lemma lowerBound_mul {a b : ℤ} {f g : Series} (hf : LowerBound a f) (hg : LowerBound b g) :
    LowerBound (a+b) (f*g) := by
  rw [lowerBound_iff_orderTop] at *
  rw [WithTop.coe_add,HahnSeries.orderTop_mul]
  exact add_le_add hf hg

lemma agrees_iff_sub {b : ℤ} {f g : Series} : Agrees b f g ↔ LowerBound b (f-g) := by
  simp only [Agrees,LowerBound,HahnSeries.coeff_sub,sub_eq_zero]

lemma agrees_refl (b : ℤ) (f : Series) : Agrees b f f := fun _ _=>rfl
lemma agrees_add {b : ℤ} {f f' g g' : Series} (hf : Agrees b f f') (hg : Agrees b g g') :
    Agrees b (f+g) (f'+g') := by
  intro j hj
  simp only [HahnSeries.coeff_add,hf j hj,hg j hj]
lemma agrees_neg {b : ℤ} {f g : Series} (h : Agrees b f g) : Agrees b (-f) (-g) := by
  intro j hj
  simp only [HahnSeries.coeff_neg,h j hj]
lemma agrees_sub {b : ℤ} {f f' g g' : Series} (hf : Agrees b f f') (hg : Agrees b g g') :
    Agrees b (f-g) (f'-g') := by
  simpa only [sub_eq_add_neg] using agrees_add hf (agrees_neg hg)

lemma agrees_mul {N a b : ℤ} {f f' g g' : Series}
    (hf : Agrees (N-b) f f') (hg : Agrees (N-a) g g')
    (hf' : LowerBound a f') (hgb : LowerBound b g) :
    Agrees N (f*g) (f'*g') := by
  rw [agrees_iff_sub] at *
  have h₁ := lowerBound_mul hf hgb
  have h₂ := lowerBound_mul hf' hg
  have he : f*g-f'*g'=(f-f')*g+f'*(g-g') := by ring
  rw [he]
  apply lowerBound_add
  · simpa using h₁
  · convert h₂ using 1
    all_goals try with_reducible_and_instances rfl
    omega

variable {ι : Type*} (l : Filter ι)

lemma converges_const (F : Series) : Converges l (fun _=>F) F :=
  fun N=>Eventually.of_forall (fun _=>agrees_refl N F)

lemma Converges.lowerBound {f : ι → Series} {F : Series} (h : Converges l f F)
    (b : ℤ) (hb : LowerBound b F) : ∀ᶠ i in l,LowerBound b (f i) := by
  filter_upwards [h b] with i hi
  intro j hj
  rw [hi j hj,hb j hj]

lemma Converges.add {f g : ι → Series} {F G : Series}
    (hf : Converges l f F) (hg : Converges l g G) :
    Converges l (fun i=>f i+g i) (F+G) := by
  intro N
  filter_upwards [hf N,hg N] with i hi hj
  exact agrees_add hi hj

lemma Converges.sub {f g : ι → Series} {F G : Series}
    (hf : Converges l f F) (hg : Converges l g G) :
    Converges l (fun i=>f i-g i) (F-G) := by
  intro N
  filter_upwards [hf N,hg N] with i hi hj
  exact agrees_sub hi hj

lemma Converges.mul {f g : ι → Series} {F G : Series}
    (hf : Converges l f F) (hg : Converges l g G) :
    Converges l (fun i=>f i*g i) (F*G) := by
  intro N
  filter_upwards [hf (N-G.order),hg (N-F.order),
    hg.lowerBound l G.order (lowerBound_order G)] with i hi hj hb
  exact agrees_mul hi hj (lowerBound_order F) hb

lemma Converges.sum {α : Type*} (s : Finset α) {f : α → ι → Series} {F : α → Series}
    (h : ∀a∈s,Converges l (f a) (F a)) :
    Converges l (fun i=>∑a∈s,f a i) (∑a∈s,F a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using converges_const l 0
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      (h a (Finset.mem_insert_self _ _)).add l (ih (fun b hb=>h b (Finset.mem_insert_of_mem hb)))

end ElementaryPositivity.LaurentPrecision

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_PowerSeriesProductLeading
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.PowerSeriesSplit
open PowerSeries
noncomputable section
variable {R : Type*} [Ring R]
lemma multiply_leading_difference (f g f' g' : PowerSeries R) (n : ℕ)
    (hf : constantCoeff f=1) (hg : constantCoeff g=1)
    (hf' : constantCoeff f'=1) (hg' : constantCoeff g'=1)
    (hff : ∀k≤n,coeff k f=coeff k f') (hgg : ∀k≤n,coeff k g=coeff k g') :
    coeff (n+1) (f*g)-coeff (n+1) (f'*g')=
      (coeff (n+1) f-coeff (n+1) f')+(coeff (n+1) g-coeff (n+1) g') := by
  rw [coeff_mul_succ _ _ _ hf hg,coeff_mul_succ _ _ _ hf' hg']
  have he : (∑i : Fin n,coeff (i.val+1) f*coeff (n-i.val) g)=
      ∑i : Fin n,coeff (i.val+1) f'*coeff (n-i.val) g' := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hff (i.val+1) (by omega),hgg (n-i.val) (by omega)]
  rw [he]
  abel

variable {A : Type*} (f g : A → PowerSeries R)
lemma product_constant (l : List A) (hf : ∀a∈l,constantCoeff (f a)=1) :
    constantCoeff (l.map f).prod=1 := by
  induction l with
  | nil => exact map_one _
  | cons a l ih =>
    rw [List.map_cons,List.prod_cons,map_mul,hf a List.mem_cons_self,one_mul,
      ih (fun b hb=>hf b (List.mem_cons_of_mem a hb))]

lemma product_leading_difference (l : List A) (n : ℕ)
    (hf : ∀a∈l,constantCoeff (f a)=1) (hg : ∀a∈l,constantCoeff (g a)=1)
    (hfg : ∀a∈l,∀k≤n,coeff k (f a)=coeff k (g a)) :
    coeff (n+1) (l.map f).prod-coeff (n+1) (l.map g).prod=
      (l.map (fun a=>coeff (n+1) (f a)-coeff (n+1) (g a))).sum := by
  induction l with
  | nil => simp only [List.map_nil,List.prod_nil,sub_self,List.sum_nil]
  | cons a l ih =>
    have hfl : ∀b∈l,constantCoeff (f b)=1:=fun b hb=>hf b (List.mem_cons_of_mem a hb)
    have hgl : ∀b∈l,constantCoeff (g b)=1:=fun b hb=>hg b (List.mem_cons_of_mem a hb)
    have hfg' : ∀b∈l,∀k≤n,coeff k (f b)=coeff k (g b):=
      fun b hb=>hfg b (List.mem_cons_of_mem a hb)
    simp only [List.map_cons,List.prod_cons,List.sum_cons]
    rw [multiply_leading_difference _ _ _ _ n (hf a List.mem_cons_self)
      (product_constant f l hfl) (hg a List.mem_cons_self) (product_constant g l hgl)
      (hfg a List.mem_cons_self) (fun k hk=>product_coeff_congr f g l k
        (fun b hb j hj=>hfg' b hb j (hj.trans hk))),ih hfl hgl hfg']
end
end ElementaryPositivity.PowerSeriesSplit
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_QuantumTorusWallLeading
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries ElementaryPositivity.PowerSeriesSplit
noncomputable section
variable {R M I A : Type*} [CommRing R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M) (h : M →+ ℝ)

local instance instAddGroupTorus_re19c27_2 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instSubTorus
omit [Fintype I] in
lemma joint_middle_leading_difference (f g : A → PowerSeries (Torus v Ω))
    (l : List A) (n : ℕ)
    (hf : ∀a∈l,constantCoeff (f a)=1) (hg : ∀a∈l,constantCoeff (g a)=1)
    (hlow : ∀a∈l,∀k≤n,coeff k (f a)=coeff k (g a)) :
    coeff (n+1) (zeroFactor (positiveProject v Ω h) (zeroProject v Ω h) (l.map f).prod)-
      coeff (n+1) (zeroFactor (positiveProject v Ω h) (zeroProject v Ω h) (l.map g).prod)=
      zeroProject v Ω h
        (l.map (fun a=>coeff (n+1) (f a)-coeff (n+1) (g a))).sum := by
  rw [zero_leading_difference (positiveProject v Ω h) (zeroProject v Ω h)
    (zero_positive_project v Ω h) _ _ n
    (fun k hk=>product_coeff_congr f g l k (fun a ha j hj=>hlow a ha j (hj.trans hk)))]
  rw [product_leading_difference f g l n hf hg hlow]

omit [Fintype I] in
lemma joint_middle_monomial_unaffected (f g : A → PowerSeries (Torus v Ω))
    (l : List A) (n : ℕ) (m : M)
    (hf : ∀a∈l,constantCoeff (f a)=1) (hg : ∀a∈l,constantCoeff (g a)=1)
    (hlow : ∀a∈l,∀k≤n,coeff k (f a)=coeff k (g a))
    (hlast : ∀a∈l,coeff (n+1) (f a) m=coeff (n+1) (g a) m) :
    coeff (n+1) (zeroFactor (positiveProject v Ω h) (zeroProject v Ω h) (l.map f).prod) m=
      coeff (n+1) (zeroFactor (positiveProject v Ω h) (zeroProject v Ω h) (l.map g).prod) m := by
  classical
  have eval_sub (x y : Torus v Ω) : (x-y) m=x m-y m := by
    change x m + -y m=x m-y m
    exact (sub_eq_add_neg _ _).symm
  have he:=congrArg (fun x : Torus v Ω=>x m)
    (joint_middle_leading_difference v Ω h f g l n hf hg hlow)
  rw [eval_sub] at he
  change _-_=((l.map (fun a=>coeff (n+1) (f a)-coeff (n+1) (g a))).sum.filter
    (fun x=>h x=0)) m at he
  rw [Finsupp.filter_apply] at he
  have hz : (l.map (fun a=>coeff (n+1) (f a)-coeff (n+1) (g a))).sum m=0 := by
    clear he hf hg hlow
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.map_cons,List.sum_cons,Finsupp.add_apply]
      rw [eval_sub,hlast a List.mem_cons_self,sub_self,zero_add]
      exact ih (fun b hb=>hlast b (List.mem_cons_of_mem a hb))
  rw [hz,ite_self] at he
  exact sub_eq_zero.mp he
end
end ElementaryPositivity.QuantumTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_TorusContinuity
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder _root_.OAI.ElementaryPositivity.RawShuffle.globalStringIndexLinearOrder _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries LaurentPrecision ElementaryPositivity.PowerSeriesSplit
noncomputable section
variable {M I ι : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ)
variable (C : (I → ℤ) →+ M) (l : Filter ι)
attribute [local instance] Classical.propDecidable

local instance instAddGroupTorusLaurentSeriesRat_re19c27_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instSubTorusLaurentSeriesRat
lemma torusConverges_const (F : Torus v Ω) : TorusConverges v Ω l (fun _=>F) F :=
  fun m=>converges_const l (F m)

lemma TorusConverges.sub {f g : ι → Torus v Ω} {F G : Torus v Ω}
    (hf : TorusConverges v Ω l f F) (hg : TorusConverges v Ω l g G) :
    TorusConverges v Ω l (fun i=>f i-g i) (F-G) := by
  intro m
  simp only [torus_sub_apply]
  exact (hf m).sub l (hg m)

lemma TorusConverges.sum {α : Type*} (s : Finset α)
    {f : α → ι → Torus v Ω} {F : α → Torus v Ω}
    (h : ∀a∈s,TorusConverges v Ω l (f a) (F a)) :
    TorusConverges v Ω l (fun i=>∑a∈s,f a i) (∑a∈s,F a) := by
  intro m
  simp only [Finsupp.finsetSum_apply]
  exact LaurentPrecision.Converges.sum l s (fun a ha=>h a ha m)

lemma torus_mul_finite (S T : Finset M) (f g : Torus v Ω)
    (hf : f.support⊆S) (hg : g.support⊆T) (m : M) :
    (f*g) m=∑x∈S,∑y∈T,
      (Finsupp.single (x+y) (f x*g y*(↑(v^(Ω x y)) : LaurentSeries ℚ)) : Torus v Ω) m := by
  change Torus.multiply v Ω f g m=_
  unfold Torus.multiply
  rw [Finsupp.sum_of_support_subset f hf _ (by intros; simp)]
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finsupp.sum_of_support_subset g hg _ (by intros; simp),Finsupp.finsetSum_apply]

lemma TorusConverges.mul_of_support {f g : ι → Torus v Ω} {F G : Torus v Ω}
    (hf : TorusConverges v Ω l f F) (hg : TorusConverges v Ω l g G)
    (S T : Finset M) (hS : ∀i,(f i).support⊆S) (hT : ∀i,(g i).support⊆T)
    (hSF : F.support⊆S) (hTG : G.support⊆T) :
    TorusConverges v Ω l (fun i=>f i*g i) (F*G) := by
  intro m
  simp only [torus_mul_finite v Ω S T _ _ (hS _) (hT _) m,
    torus_mul_finite v Ω S T F G hSF hTG m]
  apply LaurentPrecision.Converges.sum l S
  intro x hx
  apply LaurentPrecision.Converges.sum l T
  intro y hy
  by_cases hxy : x+y=m
  · simp only [hxy,Finsupp.single_eq_same]
    exact ((hf x).mul l (hg y)).mul l (converges_const l _)
  · simp only [Finsupp.single_eq_of_ne (Ne.symm hxy)]
    exact converges_const l 0

lemma rootGrade_support (n : ℕ) (f : Torus v Ω) (hf : f∈rootGrade v Ω C n) :
    f.support⊆(rootDegree_finite C n).toFinset := by
  intro m hm
  apply (rootDegree_finite C n).mem_toFinset.mpr
  by_contra h
  exact (Finsupp.mem_support_iff.mp hm) (hf m h)

lemma TorusConverges.mul_graded {f g : ι → Torus v Ω} {F G : Torus v Ω}
    (hf : TorusConverges v Ω l f F) (hg : TorusConverges v Ω l g G)
    (n k : ℕ) (hfn : ∀i,f i∈rootGrade v Ω C n) (hgk : ∀i,g i∈rootGrade v Ω C k)
    (hFn : F∈rootGrade v Ω C n) (hGk : G∈rootGrade v Ω C k) :
    TorusConverges v Ω l (fun i=>f i*g i) (F*G) :=
  hf.mul_of_support v Ω l hg (rootDegree_finite C n).toFinset (rootDegree_finite C k).toFinset
    (fun i=>rootGrade_support v Ω C n _ (hfn i))
    (fun i=>rootGrade_support v Ω C k _ (hgk i))
    (rootGrade_support v Ω C n F hFn) (rootGrade_support v Ω C k G hGk)

lemma TorusConverges.filter {f : ι → Torus v Ω} {F : Torus v Ω}
    (hf : TorusConverges v Ω l f F) (p : M → Prop) :
    TorusConverges v Ω l (fun i=>(f i).filter p) (F.filter p) := by
  intro m
  by_cases h : p m
  · simpa only [Finsupp.filter_apply,ite_eq_left h] using hf m
  · simpa only [Finsupp.filter_apply,ite_eq_right h] using converges_const l (0 : LaurentSeries ℚ)

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_SplitContinuity
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries LaurentPrecision ElementaryPositivity.PowerSeriesSplit
noncomputable section
variable {M I ι : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ)
variable (C : (I → ℤ) →+ M) (l : Filter ι)
attribute [local instance] Classical.propDecidable

local instance instAddGroupTorusLaurentSeriesRat_1_re19c27_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instSubTorusLaurentSeriesRat_1_re19c27_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
lemma seriesConverges_const (F : PowerSeries (Torus v Ω)) :
    SeriesConverges v Ω l (fun _=>F) F := fun _=>torusConverges_const v Ω l _

lemma SeriesConverges.mul {f g : ι → PowerSeries (Torus v Ω)} {F G : PowerSeries (Torus v Ω)}
    (hf : SeriesConverges v Ω l f F) (hg : SeriesConverges v Ω l g G)
    (hfg : ∀i,SeriesGraded v Ω C (f i)) (hgg : ∀i,SeriesGraded v Ω C (g i))
    (hF : SeriesGraded v Ω C F) (hG : SeriesGraded v Ω C G) :
    SeriesConverges v Ω l (fun i=>f i*g i) (F*G) := by
  intro n
  simp only [coeff_mul]
  apply TorusConverges.sum
  intro p hp
  exact (hf p.1).mul_graded v Ω C l (hg p.2) p.1 p.2
    (fun i=>hfg i p.1) (fun i=>hgg i p.2) (hF p.1) (hG p.2)

lemma filter_pair_graded (p : M → Prop) (F : PowerSeries (Torus v Ω))
    (hF : SeriesGraded v Ω C F) (n : ℕ) :
    (pairCoefficients (Finsupp.filterAddHom p) F n).1∈rootGrade v Ω C n ∧
    (pairCoefficients (Finsupp.filterAddHom p) F n).2∈rootGrade v Ω C n := by
  have H := factors_graded (Finsupp.filterAddHom p) (rootGrade v Ω C)
    (rootGrade_one v Ω C) (rootGrade_mul v Ω C)
    (fun n x hx=>rootGrade_filter v Ω C p n x hx) F hF
  simpa only [leftFactor,rightFactor,coeff_mk] using And.intro (H.1 n) (H.2 n)

lemma filter_pair_converges (p : M → Prop)
    {f : ι → PowerSeries (Torus v Ω)} {F : PowerSeries (Torus v Ω)}
    (hf : SeriesConverges v Ω l f F)
    (hfg : ∀i,SeriesGraded v Ω C (f i)) (hF : SeriesGraded v Ω C F) (n : ℕ) :
    TorusConverges v Ω l (fun i=>(pairCoefficients (Finsupp.filterAddHom p) (f i) n).1)
      (pairCoefficients (Finsupp.filterAddHom p) F n).1 ∧
    TorusConverges v Ω l (fun i=>(pairCoefficients (Finsupp.filterAddHom p) (f i) n).2)
      (pairCoefficients (Finsupp.filterAddHom p) F n).2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa only [pairCoefficients] using
        And.intro (torusConverges_const v Ω l 1) (torusConverges_const v Ω l 1)
    | succ n =>
      let P : Torus v Ω →+ Torus v Ω := Finsupp.filterAddHom p
      have hprod : TorusConverges v Ω l
          (fun i=>∑j : Fin n,(pairCoefficients P (f i) (j.val+1)).1 *
            (pairCoefficients P (f i) (n-j.val)).2)
          (∑j : Fin n,(pairCoefficients P F (j.val+1)).1 *
            (pairCoefficients P F (n-j.val)).2) := by
        apply TorusConverges.sum
        intro j hj
        exact (ih (j.val+1) (by omega)).1.mul_graded v Ω C l
          (ih (n-j.val) (by omega)).2 (j.val+1) (n-j.val)
          (fun i=>(filter_pair_graded v Ω C p (f i) (hfg i) _).1)
          (fun i=>(filter_pair_graded v Ω C p (f i) (hfg i) _).2)
          (filter_pair_graded v Ω C p F hF _).1
          (filter_pair_graded v Ω C p F hF _).2
      have hr := (hf (n+1)).sub v Ω l hprod
      have hp := hr.filter v Ω l p
      constructor
      · unfold pairCoefficients
        exact hp
      · unfold pairCoefficients
        exact hr.sub v Ω l hp

lemma filter_factors_converge (p : M → Prop)
    {f : ι → PowerSeries (Torus v Ω)} {F : PowerSeries (Torus v Ω)}
    (hf : SeriesConverges v Ω l f F)
    (hfg : ∀i,SeriesGraded v Ω C (f i)) (hF : SeriesGraded v Ω C F) :
    SeriesConverges v Ω l (fun i=>leftFactor (Finsupp.filterAddHom p) (f i))
      (leftFactor (Finsupp.filterAddHom p) F) ∧
    SeriesConverges v Ω l (fun i=>rightFactor (Finsupp.filterAddHom p) (f i))
      (rightFactor (Finsupp.filterAddHom p) F) := by
  constructor
  · intro n
    simpa only [leftFactor,coeff_mk] using (filter_pair_converges v Ω C l p hf hfg hF n).1
  · intro n
    simpa only [rightFactor,coeff_mk] using (filter_pair_converges v Ω C l p hf hfg hF n).2

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RootTruncation
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity
namespace RootTruncation
open PowerSeries
noncomputable section
variable {A : Type*} [Ring A]
lemma cut_congr {N : ℕ} {F G : PowerSeries A} (h : ∀n≤N,coeff n F=coeff n G) :
    cut N F=cut N G := by
  ext n
  simp only [coeff_cut]
  split_ifs with hn
  · exact h n hn
  · rfl
@[simp] lemma cut_cut (N : ℕ) (F : PowerSeries A) : cut N (cut N F)=cut N F :=
  cut_congr (fun _ hn=>coeff_cut_of_le F hn)
end
end RootTruncation
namespace QuantumTorus
open PowerSeries RootTruncation
section Continuity
open PowerSeries RootTruncation Filter LaurentPrecision
variable {M I J : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M→+M→+ℤ) (C : (I→ℤ)→+M) (l : Filter J)
lemma SeriesGraded.cut (N : ℕ) {F : PowerSeries (Torus v Ω)} (hF : SeriesGraded v Ω C F) :
    SeriesGraded v Ω C (cut N F) := by
  intro n
  rw [coeff_cut]
  split_ifs
  · exact hF n
  · intro m hm; rfl
lemma SeriesConverges.cut (N : ℕ) {f : J→PowerSeries (Torus v Ω)} {F : PowerSeries (Torus v Ω)}
    (hf : SeriesConverges v Ω l f F) :
    SeriesConverges v Ω l (fun j=>cut N (f j)) (cut N F) := by
  intro n
  simp only [coeff_cut]
  by_cases hn : n≤N
  · simp only [hn,ite_true, if_true]; exact hf n
  · simp only [hn,ite_false, if_false]; exact torusConverges_const v Ω l 0
end Continuity
end QuantumTorus
end ElementaryPositivity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_SeriesApproximation
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries LaurentPrecision Filter
noncomputable section
variable {M ι : Type*} [AddCommGroup M]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M→+M→+ℤ)

lemma TestAgreement.trans {T : Finset (PrecisionTest (M:=M))}
    {F G H : PowerSeries (Torus v Ω)}
    (hf : TestAgreement v Ω T F G) (hg : TestAgreement v Ω T G H) :
    TestAgreement v Ω T F H := fun t ht j hj=>(hf t ht j hj).trans (hg t ht j hj)

lemma InPrecisionClosure.mono {A B : Set (PowerSeries (Torus v Ω))} {F : PowerSeries (Torus v Ω)}
    (hF : InPrecisionClosure v Ω A F) (hAB : A⊆B) : InPrecisionClosure v Ω B F := by
  intro T
  obtain ⟨G,hG,H⟩:=hF T
  exact ⟨G,hAB hG,H⟩

variable (l : Filter ι)
lemma SeriesConverges.testAgreement {f : ι→PowerSeries (Torus v Ω)} {F : PowerSeries (Torus v Ω)}
    (hf : SeriesConverges v Ω l f F) (T : Finset (PrecisionTest (M:=M))) :
    ∀ᶠi in l,TestAgreement v Ω T (f i) F := by
  classical
  induction T using Finset.induction_on with
  | empty=>exact Eventually.of_forall (by simp [TestAgreement])
  | @insert t T ht ih=>
    filter_upwards [ih,hf t.1 t.2.1 t.2.2] with i hi hj
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl|ha
    · exact hj
    · exact hi a ha

lemma InPrecisionClosure.of_converges [l.NeBot]
    {A : Set (PowerSeries (Torus v Ω))} {f : ι→PowerSeries (Torus v Ω)}
    {F : PowerSeries (Torus v Ω)} (hf : SeriesConverges v Ω l f F)
    (hA : ∀ᶠi in l,InPrecisionClosure v Ω A (f i)) : InPrecisionClosure v Ω A F := by
  intro T
  obtain ⟨i,hi,hAi⟩:=((hf.testAgreement v Ω l T).and hA).exists
  obtain ⟨G,hG,H⟩:=hAi T
  exact ⟨G,hG,H.trans v Ω hi⟩

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_TruncatedPrecisionClosure
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries RootTruncation LaurentPrecision Filter WallUnits
noncomputable section
variable {M I J : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M→+M→+ℤ)
lemma RootClosedThrough.congr {N : ℕ} {A : Set (PowerSeries (Torus v Ω))}
    {F G : PowerSeries (Torus v Ω)} (hF : RootClosedThrough v Ω N A F)
    (he : ∀n≤N,coeff n F=coeff n G) : RootClosedThrough v Ω N A G := by
  change InPrecisionClosure v Ω _ _ at hF ⊢
  rw [←cut_congr he]
  exact hF
lemma InPrecisionClosure.cut {A : Set (PowerSeries (Torus v Ω))}
    {F : PowerSeries (Torus v Ω)} (hF : InPrecisionClosure v Ω A F) (N : ℕ) :
    RootClosedThrough v Ω N A F := by
  intro T
  obtain ⟨G,hG,H⟩:=hF T
  refine ⟨RootTruncation.cut N G,⟨G,hG,rfl⟩,?_⟩
  intro t ht
  simp only [coeff_cut]
  by_cases hn : t.1≤N
  · simp only [hn,ite_true, if_true]; exact H t ht
  · simp only [hn,ite_false, if_false]; exact agrees_refl _ _
lemma RootClosedThrough.mono {N : ℕ} {A B : Set (PowerSeries (Torus v Ω))}
    {F : PowerSeries (Torus v Ω)} (hF : RootClosedThrough v Ω N A F) (hAB : A⊆B) :
    RootClosedThrough v Ω N B F := InPrecisionClosure.mono v Ω hF (Set.image_mono hAB)
variable {N : ℕ} {A : Set (PowerSeries (Torus v Ω))} {F : PowerSeries (Torus v Ω)}
lemma rootApprox_mem (hF : RootClosedThrough v Ω N A F)
    (T : Finset (PrecisionTest (M:=M))) : rootApprox v Ω hF T∈A :=
  (Classical.choose_spec (rootClosedThrough_approx_exists v Ω hF T)).1
lemma rootApprox_converges (hF : RootClosedThrough v Ω N A F) :
    SeriesConverges v Ω (atTop : Filter (Finset (PrecisionTest (M:=M))))
      (fun T=>RootTruncation.cut N (rootApprox v Ω hF T)) (RootTruncation.cut N F) := by
  classical
  intro n m K
  apply eventually_atTop.mpr
  refine ⟨{(n,m,K)},fun T hT=>?_⟩
  exact (Classical.choose_spec (rootClosedThrough_approx_exists v Ω hF T)).2
    (n,m,K) (hT (by simp))
lemma RootClosedThrough.of_converges (l : Filter J) [l.NeBot]
    {f : J→PowerSeries (Torus v Ω)}
    (hf : SeriesConverges v Ω l (fun j=>RootTruncation.cut N (f j)) (RootTruncation.cut N F))
    (hA : ∀ᶠj in l,RootClosedThrough v Ω N A (f j)) : RootClosedThrough v Ω N A F :=
  InPrecisionClosure.of_converges v Ω l hf hA
end

end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_InputProduct
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.WeightedTorusSeries
open RawShuffle QuantumTorus PowerSeries WallUnits
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I R M : Type*} [Fintype I] [DecidableEq I] [CommRing R] [AddCommGroup M]
variable (a : I → I → ℕ) (u : I → ℕ → R)
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)

lemma crossInteraction_axis (i : I) (d : I → ℕ) (hd : Supported {i} d) : crossInteraction a d=0 := by
  rw [crossInteraction_offdiagonal]
  apply Finset.sum_eq_zero
  intro j hj
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hjk : j=k
  · simp [hjk]
  · rw [ite_eq_right hjk]
    by_cases hji : j=i
    · subst j
      rw [hd k (by simp [Ne.symm hjk]),Nat.cast_zero,mul_zero]
    · rw [hd j (by simp [hji]),Nat.cast_zero,mul_zero,zero_mul]

lemma partialCoefficient_singleton (i : I) :
    partialCoefficient a u v {i}=supportedCoefficient {i} (fun d=>u i (d i)) := by
  funext d
  rw [partialCoefficient,supportedCoefficient,supportedCoefficient]
  by_cases hd : Supported {i} d
  · rw [ite_eq_left hd,ite_eq_left hd]
    simp only [Finset.prod_singleton,crossInteraction_axis a i d hd,zpow_zero,Units.val_one,mul_one]
  · rw [ite_eq_right hd,ite_eq_right hd]

variable (w : I → ℕ) [Fact (∀i,0<w i)]

lemma push_partial_axis_family (i : I) (f : I → PowerSeries R) :
    push w v Ω P (partialCoefficient a (fun j n=>coeff n (f j)) v {i})=
      weightedRay v Ω (w i) (P (Pi.single i 1)) (f i) := by
  rw [partialCoefficient_singleton,push_axis]

end
end ElementaryPositivity.WeightedTorusSeries

namespace ElementaryPositivity.RawShuffle
open QuantumTorus WeightedTorusSeries PowerSeries WallUnits
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I M : Type*} [Fintype I] [DecidableEq I] [AddCommGroup M]
variable (a : I → I → ℕ) (κ : I → ℤ) (ε : I → Bool)
variable (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)
variable (w : I → ℕ) [Fact (∀i,0<w i)]

omit [DecidableEq I] in
lemma partial_univ_literal :
    partialCoefficient a (fun i n=>coeff n (literalAxisScalar κ ε i)) LaurentRay.vUnit Finset.univ=
      literalInputCoefficient a κ ε := by
  funext d
  have HS : Supported Finset.univ d := by intro i hi; exact (hi (Finset.mem_univ i)).elim
  rw [partialCoefficient,supportedCoefficient,ite_eq_left HS]
  dsimp only [literalAxisScalar]
  simp only [coeff_map,LaurentRay.vUnit_zpow]
  rfl

theorem literalInput_ordered (hΩ : ∀d e,Ω (P d) (P e)=eulerForm a d e-eulerForm a e d)
    (l : List I) (hl : l.Nodup) (hall : l.toFinset=Finset.univ)
    (ho : l.Pairwise fun i j=>a i j=0) :
    push w LaurentRay.vUnit Ω P (literalInputCoefficient a κ ε)=
      (l.map (literalAxis κ ε Ω P w)).prod := by
  have H:=push_partial_list a (fun i n=>coeff n (literalAxisScalar κ ε i))
    LaurentRay.vUnit Ω P hΩ w l hl ho
  rw [hall,partial_univ_literal a κ ε] at H
  rw [H]
  apply congrArg List.prod
  apply List.map_congr_left
  intro i hi
  exact push_partial_axis_family a LaurentRay.vUnit Ω P w i (literalAxisScalar κ ε)

end
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic QuantumTorus
noncomputable section
variable {I M : Type*} [Fintype I] [DecidableEq I] [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ) (p : I → M) (ε : I → Bool)

lemma rootSum_single (i : I) (n : ℕ) : rootSum p (Pi.single i n)=n • p i := by
  classical
  simp [rootSum,Pi.single_apply,ite_smul,Finset.sum_ite_eq']

omit [Fintype I] in
lemma geometricQuiver_diag (i : I) : geometricQuiver Ω p ε i i=elementaryDiagonal ε i := by
  simp [geometricQuiver]

variable (hΩ : ∀m,Ω m m=0)
omit [Fintype I] in
include hΩ in
lemma geometricQuiver_skew (i j : I) :
    (geometricQuiver Ω p ε j i:ℤ)-geometricQuiver Ω p ε i j=Ω (p i) (p j) := by
  by_cases h : i=j
  · subst j; rw [sub_self,hΩ]
  · rw [geometricQuiver,ite_eq_right (Ne.symm h),geometricQuiver,ite_eq_right h,
      alternating_skew Ω hΩ (p j) (p i)]
    omega

include hΩ in
lemma geometricQuiver_euler (d e : I→ℕ) :
    Ω (rootSum p d) (rootSum p e)=
      eulerForm (geometricQuiver Ω p ε) d e-eulerForm (geometricQuiver Ω p ε) e d := by
  rw [euler_skew_sum]
  simp only [rootSum,AddMonoidHom.coe_mk,ZeroHom.coe_mk,map_sum,map_nsmul,
    AddMonoidHom.finsetSum_apply,AddMonoidHom.nsmul_apply,nsmul_eq_mul,
    geometricQuiver_skew Ω p ε hΩ]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

omit [Fintype I] in
include hΩ in
lemma geometricQuiver_forward (i j : I) (hij : i≠j) (hp : 0≤Ω (p i) (p j)) :
    geometricQuiver Ω p ε i j=0 := by
  rw [geometricQuiver,ite_eq_right hij,alternating_skew Ω hΩ (p j) (p i)]
  exact Int.toNat_eq_zero.mpr (by omega)

omit [Fintype I] in
include hΩ in
lemma geometricQuiver_pairwise (l : List I) (hn : l.Nodup)
    (hl : l.Pairwise (fun i j=>0≤Ω (p i) (p j))) :
    l.Pairwise (fun i j=>geometricQuiver Ω p ε i j=0) := by
  apply (hn.and hl).imp
  intro i j h
  exact geometricQuiver_forward Ω p ε hΩ i j h.1 h.2

include hΩ in
lemma geometricQuiver_symmetric (c η : I→ℝ) (hc : ∀i,0 < c i) (t : ℝ)
    (hp : ∀i j,(Ω (p i) (p j):ℝ)=t*(η i*c j-c i*η j)) :
    ∀θ,SlopeEulerSymmetric (geometricQuiver Ω p ε) c η θ := by
  apply slopeEulerSymmetric_of_plane _ c η hc t
  intro i j
  have H:=congrArg (fun z:ℤ=>(z:ℝ)) (geometricQuiver_skew Ω p ε hΩ i j)
  push_cast at H
  exact H.trans (hp i j)

end
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GeometricRootClosure
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic QuantumTorus WeightedTorusSeries WallUnits PowerSeries
noncomputable section
variable {I J M : Type*} [Fintype I] [DecidableEq I] [Fintype J] [AddCommGroup M]
variable (Ω : M→+M→+ℤ) (hΩ : ∀p,Ω p p=0)
variable (p : I→M) (κ : I→ℤ) (ε : I→Bool)
variable (w : I→ℕ) [Fact (∀i,0<w i)]
variable (c η : I→ℝ) (hc : ∀i,0 < c i) (t : ℝ)
variable (hp : ∀i j,(Ω (p i) (p j):ℝ)=t*(η i*c j-c i*η j))
variable (l : List I) (hn : l.Nodup) (hall : l.toFinset=Finset.univ)
variable (hl : l.Pairwise (fun i j=>0≤Ω (p i) (p j)))
variable (C : (J→ℤ)→+M) (hroot : ∀d,HasRootDegree C (weight w d) (rootSum p d))
variable (h : M→+ℝ) (θ : ℝ) (hh : ∀d,h (rootSum p d)=slopeValue c η θ d)
variable (V : M→Prop) (hv : ∀d∈slopeDimensions c η hc θ,V (rootSum p d))

include hΩ hc hp hn hall hl hroot hh hv in
theorem geometric_zero_rootClosure :
    InPrecisionClosure LaurentRay.vUnit Ω (literalRootProducts Ω C V)
      (PowerSeriesSplit.zeroFactor (positiveProject LaurentRay.vUnit Ω h)
        (zeroProject LaurentRay.vUnit Ω h)
        ((l.map (literalAxis κ ε Ω (rootSum p) w)).prod)) := by
  let a:=geometricQuiver Ω p ε
  let : Fact (∀θ,SlopeEulerSymmetric a c η θ) :=
    ⟨geometricQuiver_symmetric Ω p ε hΩ c η hc t hp⟩
  have H:=literalInput_ordered a κ ε Ω (rootSum p) w
    (geometricQuiver_euler Ω p ε hΩ) l hn hall
    (geometricQuiver_pairwise Ω p ε hΩ l hn hl)
  rw [←H]
  exact finiteInput_zero_rootClosure a κ c η hc w Ω (rootSum p) C
    (geometricQuiver_euler Ω p ε hΩ) hroot θ V hv h hh ε
    (geometricQuiver_diag Ω p ε)
end
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic QuantumTorus WeightedTorusSeries WallUnits
noncomputable section
variable {I J M : Type*} [Fintype I] [DecidableEq I] [Fintype J] [AddCommGroup M]
variable (p : I→M) (w : I→ℕ) (C : (J→ℤ)→+M)

lemma rootDegree_finset_sum {A : Type*} (s : Finset A) (n : A→ℕ) (m : A→M)
    (h : ∀i∈s,HasRootDegree C (n i) (m i)) :
    HasRootDegree C (∑i∈s,n i) (∑i∈s,m i) := by
  classical
  induction s using Finset.induction_on with
  | empty=>simpa using rootDegree_zero C
  | @insert a s ha ih=>
    simp only [Finset.sum_insert ha]
    exact rootDegree_add C (h a (by simp)) (ih (fun i hi=>h i (by simp [hi])))

omit [DecidableEq I] in
lemma rootSum_rootDegree (hp : ∀i,HasRootDegree C (w i) (p i)) (d : I→ℕ) :
    HasRootDegree C (weight w d) (rootSum p d) := by
  exact rootDegree_finset_sum C Finset.univ (fun i=>d i*w i) (fun i=>d i • p i)
    (fun i _=>rootDegree_nsmul C (hp i) (d i))

omit [DecidableEq I] in
lemma rootSum_mem (V : AddSubmonoid M) (hp : ∀i,p i∈V) (d : I→ℕ) : rootSum p d∈V := by
  exact V.sum_mem (fun i _=>V.nsmul_mem (hp i) (d i))

omit [DecidableEq I] in
lemma rootSum_slope_zero (h : M→+ℝ) (c : I→ℝ) (d : I→ℕ) :
    h (rootSum p d)=slopeValue c (fun i=>h (p i)) 0 d := by
  simp only [rootSum,AddMonoidHom.coe_mk,ZeroHom.coe_mk,map_sum,map_nsmul,
    slopeValue,zero_mul,sub_zero,mass,nsmul_eq_mul]
end
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_DegreeIsolatedReordering
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity
namespace RootTruncation
open PowerSeries
noncomputable section
variable {A : Type*} [Ring A]
lemma patchTop_low (n : ℕ) (G F : PowerSeries A) (j : ℕ) (hj : j≤n) :
    coeff j (patchTop n G F)=coeff j G := by simp [hj]
@[simp] lemma patchTop_constant (n : ℕ) (G F : PowerSeries A) :
    constantCoeff (patchTop n G F)=constantCoeff G := by
  rw [←coeff_zero_eq_constantCoeff,patchTop_low n G F 0 (Nat.zero_le _),coeff_zero_eq_constantCoeff]
end
end RootTruncation
namespace QuantumTorus
open PowerSeries PowerSeriesSplit RootTruncation LaurentPrecision Filter
noncomputable section
variable {M I A J : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M→+M→+ℤ) (C : (I→ℤ)→+M)
lemma SeriesConverges.zero_middle (l : Filter J) (h : M→+ℝ)
    {f : J→PowerSeries (Torus v Ω)} {F : PowerSeries (Torus v Ω)}
    (hf : SeriesConverges v Ω l f F) (hg : ∀i,SeriesGraded v Ω C (f i))
    (hF : SeriesGraded v Ω C F) :
    SeriesConverges v Ω l
      (fun j=>zeroFactor (positiveProject v Ω h) (zeroProject v Ω h) (f j))
      (zeroFactor (positiveProject v Ω h) (zeroProject v Ω h) F) := by
  have H:=filter_factors_converge v Ω C l (fun m=>0<h m) hf hg hF
  exact (filter_factors_converge v Ω C l (fun m=>h m=0) H.2
    (fun j n=>by simpa only [rightFactor,coeff_mk] using (filter_pair_graded v Ω C (fun m=>0<h m) (f j) (hg j) n).2)
    (fun n=>by simpa only [rightFactor,coeff_mk] using (filter_pair_graded v Ω C (fun m=>0<h m) F hF n).2)).1
lemma SeriesGraded.patchTop (n : ℕ) {G F : PowerSeries (Torus v Ω)}
    (hG : SeriesGraded v Ω C G) (hF : SeriesGraded v Ω C F) :
    SeriesGraded v Ω C (patchTop n G F) := by
  intro j
  rw [coeff_patchTop]
  split_ifs
  · exact hG j
  · exact hF j
  · intro m hm; rfl
lemma SeriesConverges.patchTop (l : Filter J) (n : ℕ)
    {g : J→PowerSeries (Torus v Ω)} {F : PowerSeries (Torus v Ω)}
    (hg : SeriesConverges v Ω l (fun j=>RootTruncation.cut n (g j)) (RootTruncation.cut n F)) :
    SeriesConverges v Ω l (fun j=>patchTop n (g j) F) (RootTruncation.cut (n+1) F) := by
  intro k
  simp only [coeff_patchTop,coeff_cut]
  by_cases hk : k≤n
  · simp only [hk,ite_true, if_true,show k≤n+1 by omega]
    simpa only [coeff_cut,hk,ite_true, if_true] using hg k
  · by_cases he : k=n+1
    · simp only [he,Nat.not_succ_le_self,ite_false, if_false,ite_true, if_true,le_refl]
      exact torusConverges_const v Ω l _
    · simp only [hk,he,ite_false, if_false,show ¬k≤n+1 by omega]
      exact torusConverges_const v Ω l _
lemma zero_middle_off (h : M→+ℝ) (F : PowerSeries (Torus v Ω)) (n : ℕ) (m : M) (hm : h m≠0) :
    coeff (n+1) (zeroFactor (positiveProject v Ω h) (zeroProject v Ω h) F) m=0 := by
  simp only [zeroFactor,leftFactor,coeff_mk]
  rw [pairCoefficients]
  exact Finsupp.filter_apply_neg _ _ hm

lemma joint_middle_isolated_through (h : M→+ℝ) (l : List A)
    (f g : A→PowerSeries (Torus v Ω)) (n : ℕ)
    (hf : ∀a∈l,constantCoeff (f a)=1) (hg : ∀a∈l,constantCoeff (g a)=1)
    (hlow : ∀a∈l,∀k≤n,coeff k (f a)=coeff k (g a))
    (hlast : ∀a∈l,∀m,h m=0 → coeff (n+1) (f a) m=coeff (n+1) (g a) m) :
    RootTruncation.cut (n+1) (zeroFactor (positiveProject v Ω h) (zeroProject v Ω h) (l.map f).prod)=
      RootTruncation.cut (n+1) (zeroFactor (positiveProject v Ω h) (zeroProject v Ω h) (l.map g).prod) := by
  apply cut_congr
  intro k hk
  by_cases hkn : k≤n
  · exact zero_coeff_congr _ _ _ _ k (fun j hj=>product_coeff_congr f g l j
      (fun a ha i hi=>hlow a ha i (hi.trans (hj.trans hkn))))
  · have he : k=n+1:=by omega
    subst k
    apply Finsupp.ext
    intro m
    by_cases hm : h m=0
    · exact joint_middle_monomial_unaffected v Ω h f g l n m hf hg hlow (fun a ha=>hlast a ha m hm)
    · rw [zero_middle_off v Ω h _ n m hm,zero_middle_off v Ω h _ n m hm]
end
end QuantumTorus
end ElementaryPositivity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_OrderedRootReordering
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open RawShuffle SlopeArithmetic WeightedTorusSeries WallUnits UnitSelections PowerSeries
noncomputable section
variable {M J : Type*} [AddCommGroup M] [Fintype J]
variable (Ω : M→+M→+ℤ) (C : (J→ℤ)→+M) (L h : M→+ℝ) (V : AddSubmonoid M)

lemma indexedUnit_bool (a : ℕ) (k : ℤ) :
    indexedUnit (if decide (a=0) then 0 else 1) k=indexedUnit a k := by
  by_cases ha : a=0 <;> simp [indexedUnit,ha]

lemma listLiteral_product (l : List (WallUnitDatum M)) :
    ((List.finRange l.length).map (literalAxis (fun i=> (l.get i).parameter)
      (fun i=>decide ((l.get i).kind=0)) Ω (rootSum (fun i=> (l.get i).root))
      (fun i=> (l.get i).degree))).prod=(l.map (WallUnitDatum.value Ω)).prod := by
  have H : (List.finRange l.length).map (literalAxis (fun i=> (l.get i).parameter)
      (fun i=>decide ((l.get i).kind=0)) Ω (rootSum (fun i=> (l.get i).root))
      (fun i=> (l.get i).degree)) =
      (List.finRange l.length).map (fun i=>(l.get i).value Ω) := by
    apply List.map_congr_left
    intro i hi
    unfold literalAxis literalAxisScalar elementaryDiagonal WallUnitDatum.value
    rw [rootSum_single,one_nsmul,indexedUnit_bool]
  rw [H]
  change ((List.finRange l.length).map (WallUnitDatum.value Ω ∘ l.get)).prod=_
  rw [←List.map_map,List.map_get_finRange]

variable (hΩ : ∀p,Ω p p=0) (t : ℝ)
variable (hplane : ∀p∈V,∀q∈V,(Ω p q:ℝ)=t*(h p*L q-L p*h q))

include hΩ hplane in
lemma orderedPlane_zero_finite {F : PowerSeries (Torus LaurentRay.vUnit Ω)}
    (hF : F∈orderedPlaneProducts Ω C L V) :
    InPrecisionClosure LaurentRay.vUnit Ω
      (literalRootProducts Ω C (fun p=>p∈V ∧ h p=0))
      (PowerSeriesSplit.zeroFactor (positiveProject LaurentRay.vUnit Ω h)
        (zeroProject LaurentRay.vUnit Ω h) F) := by
  classical
  obtain ⟨l,hl,ho,rfl⟩:=hF
  let p : Fin l.length→M := fun i=>(l.get i).root
  let w : Fin l.length→ℕ := fun i=>(l.get i).degree
  let c : Fin l.length→ℝ := fun i=>L (p i)
  let η : Fin l.length→ℝ := fun i=>h (p i)
  have hall : ∀i,(l.get i).Allowed C (fun p=>p∈V ∧ 0<L p) := fun i=>hl _ (List.get_mem _ _)
  let : Fact (∀i,0<w i) := ⟨fun i=>(hall i).1⟩
  have hc : ∀i,0 < c i := fun i=>(hall i).2.2.2
  have hp : ∀i j,(Ω (p i) (p j):ℝ)=t*(η i*c j-c i*η j) :=
    fun i j=>hplane _ (hall i).2.2.1 _ (hall j).2.2.1
  have hh : ∀d,h (rootSum p d)=slopeValue c η 0 d := rootSum_slope_zero p h c
  have hsort : (List.finRange l.length).Pairwise (fun i j=>0≤Ω (p i) (p j)) := by
    apply (List.pairwise_map (f:=l.get)
      (R:=fun u v : WallUnitDatum M=>0≤Ω u.root v.root)).mp
    simpa only [List.map_get_finRange] using ho
  have hv : ∀d∈slopeDimensions c η hc 0,rootSum p d∈V ∧ h (rootSum p d)=0 := by
    intro d hd
    refine ⟨rootSum_mem p V (fun i=>(hall i).2.2.1) d,?_⟩
    rw [hh]
    by_cases h0 : d=0
    · subst d; exact slopeValue_zero c η 0
    · exact (slopeValue_eq_zero_iff c η hc 0 d h0).mpr (hd.resolve_left h0)
  rw [←listLiteral_product Ω l]
  exact geometric_zero_rootClosure Ω hΩ p (fun i=>(l.get i).parameter)
    (fun i=>decide ((l.get i).kind=0)) w c η hc t hp (List.finRange l.length)
    (List.nodup_finRange _) (List.toFinset_finRange _) hsort C
    (rootSum_rootDegree p w C (fun i=>(hall i).2.1)) h 0 hh
    (fun p=>p∈V ∧ h p=0) hv

end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries LaurentPrecision Filter WallUnits
noncomputable section
variable {M J A ι : Type*} [AddCommGroup M] [Fintype J]
variable (Ω : M→+M→+ℤ) (C : (J→ℤ)→+M)

lemma SeriesGraded.list_prod (s : List A)
    (F : A→PowerSeries (Torus LaurentRay.vUnit Ω))
    (hF : ∀a∈s,SeriesGraded LaurentRay.vUnit Ω C (F a)) :
    SeriesGraded LaurentRay.vUnit Ω C (s.map F).prod := by
  induction s with
  | nil=>simpa using SeriesGraded.one LaurentRay.vUnit Ω C
  | cons a s ih=>
    simpa only [List.map_cons,List.prod_cons] using
      (hF a (by simp)).mul LaurentRay.vUnit Ω C (ih (fun x hx=>hF x (by simp [hx])))

lemma SeriesConverges.list_prod (l : Filter ι) (s : List A)
    (f : A→ι→PowerSeries (Torus LaurentRay.vUnit Ω))
    (F : A→PowerSeries (Torus LaurentRay.vUnit Ω))
    (hf : ∀a∈s,SeriesConverges LaurentRay.vUnit Ω l (f a) (F a))
    (hg : ∀a∈s,∀i,SeriesGraded LaurentRay.vUnit Ω C (f a i))
    (hG : ∀a∈s,SeriesGraded LaurentRay.vUnit Ω C (F a)) :
    SeriesConverges LaurentRay.vUnit Ω l (fun i=>(s.map (fun a=>f a i)).prod) (s.map F).prod := by
  induction s with
  | nil=>simpa using seriesConverges_const LaurentRay.vUnit Ω l 1
  | cons a s ih=>
    simpa only [List.map_cons,List.prod_cons] using
      (hf a (by simp)).mul LaurentRay.vUnit Ω C l
        (ih (fun x hx=>hf x (by simp [hx])) (fun x hx=>hg x (by simp [hx]))
          (fun x hx=>hG x (by simp [hx])))
        (hg a (by simp))
        (fun i=>SeriesGraded.list_prod Ω C s (fun x=>f x i) (fun x hx=>hg x (by simp [hx]) i))
        (hG a (by simp))
        (SeriesGraded.list_prod Ω C s F (fun x hx=>hG x (by simp [hx])))

lemma literal_lists_ordered_product (L : M→+ℝ) (V : AddSubmonoid M)
    (s : List A) (P : A→M→Prop)
    (g : A→PowerSeries (Torus LaurentRay.vUnit Ω))
    (hg : ∀a∈s,g a∈literalRootProducts Ω C (P a))
    (hP : ∀a∈s,∀p,P a p→p∈V ∧ 0<L p)
    (hself : ∀a∈s,∀p q,P a p→P a q→0≤Ω p q)
    (hpair : s.Pairwise (fun a b=>∀p q,P a p→P b q→0≤Ω p q)) :
    (s.map g).prod∈orderedPlaneProducts Ω C L V := by
  classical
  let ls (a : A) : List (WallUnitDatum M) :=
    if ha : a∈s then Classical.choose (hg a ha) else []
  have hls : ∀a∈s,(∀u∈ls a,u.Allowed C (P a)) ∧
      g a=((ls a).map (WallUnitDatum.value Ω)).prod:=by
    intro a ha
    dsimp [ls]
    rw [dite_eq_left ha]
    exact Classical.choose_spec (hg a ha)
  refine ⟨s.flatMap ls,?_,?_,?_⟩
  · intro u hu
    obtain ⟨a,ha,hu⟩:=List.mem_flatMap.mp hu
    have H:=(hls a ha).1 u hu
    exact ⟨H.1,H.2.1,hP a ha u.root H.2.2⟩
  · rw [List.pairwise_flatMap]
    constructor
    · intro a ha
      apply List.pairwise_iff_getElem.mpr
      intro i j hi hj hij
      exact hself a ha _ _ ((hls a ha).1 _ (List.getElem_mem hi)).2.2
        ((hls a ha).1 _ (List.getElem_mem hj)).2.2
    · apply hpair.imp_of_mem
      intro a b ha hb H u hu w hw
      exact H u.root w.root ((hls a ha).1 u hu).2.2 ((hls b hb).1 w hw).2.2
  · rw [List.map_flatMap,List.flatMap_def,List.prod_flatten]
    simp only [List.map_map]
    congr 1
    apply List.map_congr_left
    intro a ha
    exact (hls a ha).2

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_IsolatedPositivePlane
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesSplit RootTruncation LaurentPrecision Filter WallUnits
noncomputable section
variable {M I A : Type*} [AddCommGroup M] [Fintype I]
variable (Ω : M →+M →+ℤ) (C : (I → ℤ) →+M)
variable (hΩ : ∀m,Ω m m=0) (L h : M →+ℝ) (V : AddSubmonoid M) (t : ℝ)
variable (hplane : ∀p∈V,∀q∈V,(Ω p q:ℝ)=t*(h p*L q-L p*h q))
include hΩ hplane in
theorem isolated_positive_plane (n : ℕ) (s : List A) (active : A → Bool) (P : A → M → Prop)
    (F : A → CompletedPositive LaurentRay.vUnit Ω C)
    (hF : ∀a∈s,RootClosedThrough LaurentRay.vUnit Ω (if active a then n+1 else n)
      (literalRootProducts Ω C (P a)) (F a).val)
    (hadd : ∀a∈s,∀p q,P a p → P a q → P a (p+q))
    (hP : ∀a∈s,∀p,P a p → p∈V ∧ 0<L p)
    (hself : ∀a∈s,∀p q,P a p → P a q → 0 ≤ Ω p q)
    (hpair : s.Pairwise (fun a b=>∀p q,P a p → P b q → 0 ≤ Ω p q))
    (hker : ∀a∈s,active a=false  →  ∀p,P a p → h p≠0)
    (hsupport : ∀a∈s,SupportedOn LaurentRay.vUnit Ω (P a) (coeff (n+1) (F a).val)) :
    RootClosedThrough LaurentRay.vUnit Ω (n+1)
      (literalRootProducts Ω C (fun p=>p∈V ∧ h p=0))
      (zeroFactor (positiveProject LaurentRay.vUnit Ω h) (zeroProject LaurentRay.vUnit Ω h)
        (s.map (fun a=>(F a).val)).prod) := by
  classical
  let g (a : A) (T : Finset (PrecisionTest (M:=M))) :=
    if ha : a∈s then rootApprox LaurentRay.vUnit Ω (hF a ha) T else 1
  have hg : ∀a∈s,∀T,g a T∈literalRootProducts Ω C (P a):=by
    intro a ha T
    dsimp [g]; rw [dite_eq_left ha]
    exact rootApprox_mem LaurentRay.vUnit Ω (hF a ha) T
  have hconv : ∀a∈s,SeriesConverges LaurentRay.vUnit Ω Filter.atTop
      (fun T=>cut (if active a then n+1 else n) (g a T))
      (cut (if active a then n+1 else n) (F a).val):=by
    intro a ha
    have he : g a=rootApprox LaurentRay.vUnit Ω (hF a ha):=by
      funext T; dsimp [g]; rw [dite_eq_left ha]
    rw [he]
    exact rootApprox_converges LaurentRay.vUnit Ω (hF a ha)
  let k (a : A) (T : Finset (PrecisionTest (M:=M))) :=
    if active a then cut (n+1) (g a T) else patchTop n (g a T) (F a).val
  have hkg : ∀a∈s,∀T,SeriesGraded LaurentRay.vUnit Ω C (k a T):=by
    intro a ha T
    dsimp [k]
    split_ifs
    · exact (literalRootProducts_graded Ω C (P a) (hg a ha T)).cut LaurentRay.vUnit Ω C (n+1)
    · exact (literalRootProducts_graded Ω C (P a) (hg a ha T)).patchTop LaurentRay.vUnit Ω C n (F a).property.2
  have hkconv : ∀a∈s,SeriesConverges LaurentRay.vUnit Ω Filter.atTop (k a) (cut (n+1) (F a).val):=by
    intro a ha
    cases he : active a
    · have H:=hconv a ha
      simp only [he,Bool.false_eq_true,ite_false, if_false] at H
      simpa only [k,he,Bool.false_eq_true,ite_false, if_false] using
        H.patchTop LaurentRay.vUnit Ω Filter.atTop n
    · simpa only [k,he,ite_true, if_true] using hconv a ha
  have hcprod:=SeriesConverges.list_prod Ω C Filter.atTop s k
    (fun a=>cut (n+1) (F a).val) hkconv hkg
    (fun a ha=>SeriesGraded.cut LaurentRay.vUnit Ω C (n+1) (F a).property.2)
  have hcmid:=hcprod.zero_middle LaurentRay.vUnit Ω C Filter.atTop h
    (fun T=>SeriesGraded.list_prod Ω C s (fun a=>k a T) (fun a ha=>hkg a ha T))
    (SeriesGraded.list_prod Ω C s (fun a=>cut (n+1) (F a).val)
      (fun a ha=>SeriesGraded.cut LaurentRay.vUnit Ω C (n+1) (F a).property.2))
  have hout : RootClosedThrough LaurentRay.vUnit Ω (n+1)
      (literalRootProducts Ω C (fun p=>p∈V ∧ h p=0))
      (zeroFactor (positiveProject LaurentRay.vUnit Ω h) (zeroProject LaurentRay.vUnit Ω h)
        (s.map (fun a=>cut (n+1) (F a).val)).prod):=by
    apply RootClosedThrough.of_converges LaurentRay.vUnit Ω Filter.atTop
      (hcmid.cut LaurentRay.vUnit Ω Filter.atTop (n+1))
    apply Eventually.of_forall
    intro T
    have hraw:=orderedPlane_zero_finite Ω C L h V hΩ t hplane
      (literal_lists_ordered_product Ω C L V s P (fun a=>g a T) (fun a ha=>hg a ha T) hP hself hpair)
    have he:=joint_middle_isolated_through LaurentRay.vUnit Ω h s (fun a=>k a T) (fun a=>g a T) n
      (fun a ha=>by
        dsimp [k]; split_ifs <;>
          simpa using literalRootProducts_constant Ω C (P a) (hg a ha T))
      (fun a ha=>literalRootProducts_constant Ω C (P a) (hg a ha T))
      (fun a ha j hj=>by
        dsimp [k]; split_ifs
        · exact coeff_cut_of_le _ (by omega)
        · exact patchTop_low n _ _ j hj)
      (fun a ha m hm=>by
        dsimp [k]
        cases hn : active a
        · simp only [Bool.false_eq_true,ite_false, if_false,coeff_patchTop,Nat.not_succ_le_self,ite_true, if_true,ite_false]
          have hp : ¬P a m:=fun H=>hker a ha hn m H hm
          rw [hsupport a ha m hp,literalRootProducts_strictSupport Ω C (P a) (hadd a ha) (hg a ha T) n m hp]
        · simp only [ite_true, if_true,coeff_cut,le_refl,ite_true])
    change InPrecisionClosure LaurentRay.vUnit Ω _ _
    rw [he]
    exact hraw.cut LaurentRay.vUnit Ω (n+1)
  apply hout.congr LaurentRay.vUnit Ω
  intro j hj
  exact zero_coeff_congr _ _ _ _ j (fun z hz=>product_coeff_congr _ _ s z
    (fun a ha i hi=>coeff_cut_of_le _ (hi.trans (hz.trans hj))))
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
lemma OnPositiveRay.mem_submodule (e : M→+E) (V : Submodule ℝ E)
    {r p : M} (H : OnPositiveRay r p) (hr : e r∈V) : e p∈V := by
  obtain ⟨a,b,ha,hb,he⟩:=H
  have H:=congrArg e he
  simp only [map_nsmul,←Nat.cast_smul_eq_nsmul ℝ] at H
  have hA : (a:ℝ)≠0:=by exact_mod_cast (Nat.ne_of_gt ha)
  exact (V.smul_mem_iff hA).mp (H.symm ▸ V.smul_mem (b:ℝ) hr)
variable (Ω : M→+M→+ℤ)
lemma OnPositiveRay.pair_nonneg {r s p q : M} (hp : OnPositiveRay r p) (hq : OnPositiveRay s q)
    (h : 0≤Ω r s) : 0≤Ω p q := by
  have hright:=hq.incomingSigns Ω r
  have hleft:=hp.eval (incomingCovector Ω q)
  by_contra hn
  have hn' : incomingCovector Ω q p < 0:=by change (Ω p q:ℝ)<0; exact_mod_cast (lt_of_not_ge hn)
  have H:=hright.2.2.mpr (hleft.2.2.mp hn')
  change (Ω r s:ℝ)<0 at H
  have h' : (0:ℝ)≤Ω r s:=by exact_mod_cast h
  linarith
lemma OnPositiveRay.pair_zero {r p q : M} (hp : OnPositiveRay r p) (hq : OnPositiveRay r q)
    (hΩ : Ω r r=0) : Ω p q=0 := by
  have hright:=hq.incomingSigns Ω r
  have hleft:=hp.eval (incomingCovector Ω q)
  have H : incomingCovector Ω r r=0:=by change (Ω r r:ℝ)=0; rw [hΩ,Int.cast_zero]
  have HH:=hleft.2.1.mpr (hright.2.1.mp H)
  change (Ω p q:ℝ)=0 at HH
  exact_mod_cast HH
lemma literalRootProducts_allowed_mono (C : (I→ℤ)→+M) (P Q : M→Prop)
    (H : ∀n,0<n → ∀p,HasRootDegree C n p → P p → Q p) :
    literalRootProducts Ω C P⊆literalRootProducts Ω C Q := by
  rintro F ⟨l,hl,rfl⟩
  refine ⟨l,?_,rfl⟩
  intro u hu
  have h:=hl u hu
  exact ⟨h.1,h.2.1,H u.degree h.1 u.root h.2.1 h.2.2⟩
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FiniteSignCharts
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesSplit RootTruncation
noncomputable section
variable {R M I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
lemma RayGeneric.mono {N K : ℕ} {r : M} {h : M →+ ℝ}
    (H : RayGeneric C N r h) (hK : K ≤ N) : RayGeneric C K r h :=
  ⟨H.1,fun n hn hN m hm h0 => H.2 n hn (hN.trans hK) m hm h0⟩
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesSplit RootTruncation WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include he hB hcomp hdeg in
theorem positive_joint_transport (n dr : ℕ) (r : M) (s : E)
    (hdr : 0 < dr) (hrd : HasRootDegree C dr r) (hrs : B (e r) s≠0)
    (F : CompletedPositive LaurentRay.vUnit Ω C)
    (hF : ∀j,coeff j F.val∈supportedSubring LaurentRay.vUnit Ω (planeRoots e (e r) s))
    (hincoming : ∀p d,0 < d → d ≤ n+1 → HasRootDegree C d p → p∈planeRoots e (e r) s →
      RootClosedThrough LaurentRay.vUnit Ω (if Ω p r=0 then n+1 else n)
        (literalRootProducts Ω C (OnPositiveRay p))
        (chartZero LaurentRay.vUnit Ω C (incomingCovector Ω p) F).val) :
    RootClosedThrough LaurentRay.vUnit Ω (n+1) (literalRootProducts Ω C (OnPositiveRay r))
      (chartZero LaurentRay.vUnit Ω C (-incomingCovector Ω r) F).val := by
  classical
  have hr : 0 < L (e r):=by rw [hdeg dr r hrd]; exact_mod_cast hdr
  have hΩ : ∀m,Ω m m=0:=by
    intro m; have H:=hB (e m); rw [hcomp] at H; exact_mod_cast H
  obtain ⟨l,hl,hpair,hRay,hfact⟩:=planar_joint_factorization LaurentRay.vUnit Ω C e he B hB hcomp L hdeg
    (e r) s hr hrs F hF (n+1)
  let V:=planeRoots e (e r) s
  let h : M →+ ℝ:= -incomingCovector Ω r
  let Lm : M →+ ℝ:=L.toAddMonoidHom.comp e
  let J (p : M):=chartZero LaurentRay.vUnit Ω C (incomingCovector Ω p) F
  have hpP : ∀p∈l,e p∈Submodule.span ℝ {e r,s}:=by
    intro p hp; obtain ⟨d,hd,hdN,hdp,hpP⟩:=hl p hp; exact hpP
  have hpL : ∀p∈l,0 < Lm p:=by
    intro p hp; obtain ⟨d,hd,hdN,hdp,hpP⟩:=hl p hp
    change 0 < L (e p); rw [hdeg d p hdp]; exact_mod_cast hd
  have hplane : ∀p∈V,∀q∈V,(Ω p q:ℝ)=(-1/L (e r))*(h p*Lm q-Lm p*h q):=by
    intro p hp q hq
    have HH:=PlanarRayOrder.plane_determinant B hB L (e r) s (e p) (e q) hp hq
    simp only [hcomp] at HH
    change (Ω p q:ℝ)=(-1/L (e r))* (-(Ω p r:ℝ)*L (e q)-L (e p)* -(Ω q r:ℝ))
    field_simp [ne_of_gt hr]
    nlinarith only [HH]
  have H:=isolated_positive_plane Ω C hΩ Lm h V (-1/L (e r)) hplane n l
    (fun p => decide (Ω p r=0)) (fun p => OnPositiveRay p) J
    (fun p hp => by
      obtain ⟨d,hd,hdN,hdp,hpP⟩:=hl p hp
      simpa only [decide_eq_true_eq,J] using hincoming p d hd hdN hdp hpP)
    (fun p hp a b ha hb => ha.add hb)
    (fun p hp a ha => ⟨ha.mem_submodule e _ (hpP p hp), (ha.eval Lm).1.mpr (hpL p hp)⟩)
    (fun p hp a b ha hb => le_of_eq (ha.pair_zero Ω hb (hΩ p)).symm)
    (hpair.imp (fun {a b} hab p q hp hq => hp.pair_nonneg Ω hq hab.le))
    (fun p hp hact a ha => by
      have hn : Ω p r≠0:=by simpa only [decide_eq_false_iff_not] using hact
      intro hz
      have hz' : incomingCovector Ω r a=0:=by simpa only [h,AddMonoidHom.neg_apply,neg_eq_zero] using hz
      have hz'' := (ha.eval (incomingCovector Ω r)).2.1.mp hz'
      change (Ω p r:ℝ)=0 at hz''
      exact hn (by exact_mod_cast hz''))
    (fun p hp a ha => by
      by_contra hh
      exact ha (hRay p hp n (by omega) a hh))
  have Hn:=H.mono LaurentRay.vUnit Ω (literalRootProducts_allowed_mono Ω C _ (OnPositiveRay r) (by
    intro d hd p hp hpV
    have hz : B (e p) (e r)=0:=by
      rw [hcomp]
      have Hz:=hpV.2
      change -(Ω p r:ℝ)=0 at Hz
      exact neg_eq_zero.mp Hz
    exact positive_ray_of_pairing_zero e he B hB L (e r) s C hdeg hrs p r d dr hd hdr hp hrd
      hpV.1 (Submodule.subset_span (by simp)) hz))
  apply Hn.congr LaurentRay.vUnit Ω
  intro j hj
  exact zero_coeff_congr _ _ _ _ j (fun i hi => (hfact i (hi.trans hj)).symm)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PlanarRefinement
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.segmentBetween_finish _root_.OAI.ElementaryPositivity.QuantumTorus.segmentBetween_start _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry RootTruncation
noncomputable section
variable {R M E I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M]
  [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
omit [Algebra ℚ R] in
lemma joint_cut_supported (N : ℕ) (r : M) (k : Module.Dual ℝ E)
    (H : GenericOffset (realRootsThrough e C N) (e r) (B.flip (e r)) k)
    (a : ℝ) (s : E) (hs : s∈realRootsThrough e C N) (hv : B s (e r)≠0)
    (hsa : (k+a • B.flip (e r)) s=0) (F : CompletedPositive v Ω C) :
    ∀n,coeff n (completedCut v Ω C N
      (chartZero v Ω C ((k+a • B.flip (e r)).toAddMonoidHom.comp e) F)).val∈
      supportedSubring v Ω (planeRoots e (e r) s) := by
  apply completedCut_supported v Ω C N _ _
  intro n hn m hm
  by_contra hx
  have hroot:=chart_root_of_ne v Ω C _ n m hx
  have hz : (k+a • B.flip (e r)) (e m)=0:=by
    have Hker:=chartZero_supported_kernel v Ω C ((k+a • B.flip (e r)).toAddMonoidHom.comp e) F n
    by_contra hh
    exact hx (Hker m hh)
  exact hm (joint_roots_plane C e B N r k H a s hs hv hsa n hn m hroot hz)
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry RootTruncation WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M) (e : M →+ E)
variable (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include hcomp in
lemma line_plus_covector (k : Module.Dual ℝ E) (r : M) (a δ : ℝ) :
    (k+(a+δ) • B.flip (e r)).toAddMonoidHom.comp e=
      (k+a • B.flip (e r)).toAddMonoidHom.comp e+δ • incomingCovector Ω r := by
  ext m
  change k (e m)+(a+δ)*B (e m) (e r)=k (e m)+a*B (e m) (e r)+δ*(Ω m r:ℝ)
  rw [hcomp]; ring
include hcomp in
lemma line_minus_covector (k : Module.Dual ℝ E) (r : M) (a δ : ℝ) :
    (k+(a-δ) • B.flip (e r)).toAddMonoidHom.comp e=
      (k+a • B.flip (e r)).toAddMonoidHom.comp e+δ • (-incomingCovector Ω r) := by
  ext m
  change k (e m)+(a-δ)*B (e m) (e r)=k (e m)+a*B (e m) (e r)+δ* -(Ω m r:ℝ)
  rw [hcomp]; ring
include he hB hcomp hdeg in
theorem wall_joint_induction_oai (n dr : ℕ) (r : M) (hdr : 0 < dr) (hrd : HasRootDegree C dr r)
    (F : CompletedPositive LaurentRay.vUnit Ω C) (ih : WallsPositiveThrough Ω C e n F)
    (k : Module.Dual ℝ E)
    (H : GenericOffset (realRootsThrough e C (n+1)) (e r) (B.flip (e r)) k)
    (a : ℝ) (ha : a∈lineEvents (realRootsThrough e C (n+1)) (B.flip (e r)) k) :
    ∃ε > 0,∀δ : ℝ,0 < δ → δ < ε →
      RootClosedThrough LaurentRay.vUnit Ω (n+1) (literalRootProducts Ω C (OnPositiveRay r))
        (chartZero LaurentRay.vUnit Ω C ((k+(a+δ) • B.flip (e r)).toAddMonoidHom.comp e) F).val →
      RootClosedThrough LaurentRay.vUnit Ω (n+1) (literalRootProducts Ω C (OnPositiveRay r))
        (chartZero LaurentRay.vUnit Ω C ((k+(a-δ) • B.flip (e r)).toAddMonoidHom.comp e) F).val := by
  obtain ⟨s,hs,hsv,hsa⟩:=(mem_lineEvents_iff _ _ _ _).mp ha
  have hrs : B (e r) s≠0:=by
    rw [PlanarRayOrder.alternating_swap B hB]
    exact neg_ne_zero.mpr hsv
  let ka:=k+a • B.flip (e r)
  let kaM:=ka.toAddMonoidHom.comp e
  let J:=chartZero LaurentRay.vUnit Ω C kaM F
  let Jc:=completedCut LaurentRay.vUnit Ω C (n+1) J
  have hkr : ka (e r)=0:=by
    change k (e r)+a*B (e r) (e r)=0
    rw [H.on_ray,hB,mul_zero,add_zero]
  have hks : ka s=0:=hsa
  have hzero:=joint_roots_plane C e B (n+1) r k H a s hs hsv hsa
  have hJc : ∀i,coeff i Jc.val∈supportedSubring LaurentRay.vUnit Ω (planeRoots e (e r) s):=
    joint_cut_supported LaurentRay.vUnit Ω C e B (n+1) r k H a s hs hsv hsa F
  have hcut (h : M →+ ℝ) : ∀i ≤ n+1,
      coeff i (chartZero LaurentRay.vUnit Ω C h Jc).val=coeff i (chartZero LaurentRay.vUnit Ω C h J).val:=by
    apply chartZero_congr_through LaurentRay.vUnit Ω C h Jc J (n+1)
    intro i hi
    exact coeff_cut_of_le J.val hi
  obtain ⟨εp,hεp,Hεp⟩:=root_lex_epsilon C (n+1) kaM (incomingCovector Ω r)
  obtain ⟨εm,hεm,Hεm⟩:=root_lex_epsilon C (n+1) kaM (-incomingCovector Ω r)
  refine ⟨min εp εm,lt_min hεp hεm,?_⟩
  intro δ hδ hδε hright
  have hδp:=lt_of_lt_of_le hδε (min_le_left _ _)
  have hδm:=lt_of_lt_of_le hδε (min_le_right _ _)
  have hrefp:=chart_zero_refinement LaurentRay.vUnit Ω C kaM (incomingCovector Ω r)
    (kaM+δ • incomingCovector Ω r) F (n+1) (Hεp δ hδ hδp)
  have hrefm:=chart_zero_refinement LaurentRay.vUnit Ω C kaM (-incomingCovector Ω r)
    (kaM+δ • (-incomingCovector Ω r)) F (n+1) (Hεm δ hδ hδm)
  have hrpos : RootClosedThrough LaurentRay.vUnit Ω (n+1) (literalRootProducts Ω C (OnPositiveRay r))
      (chartZero LaurentRay.vUnit Ω C (incomingCovector Ω r) Jc).val:=by
    apply hright.congr LaurentRay.vUnit Ω
    intro i hi
    rw [line_plus_covector Ω e B hcomp]
    exact (hrefp i hi).trans (hcut _ i hi).symm
  have hout:=positive_joint_transport Ω C e he B hB hcomp L hdeg n dr r s hdr hrd hrs Jc hJc (by
    intro p d hd hdN hp hpP
    by_cases hpr : Ω p r=0
    · rw [ite_eq_left hpr]
      have hpp : OnPositiveRay r p:=positive_ray_of_pairing_zero e he B hB L (e r) s C hdeg hrs
        p r d dr hd hdr hp hrd hpP (Submodule.subset_span (by simp)) (by rw [hcomp,hpr,Int.cast_zero])
      rw [←hpp.eq_pred,←incoming_same_ray LaurentRay.vUnit Ω C hpp Jc]
      exact hrpos
    · rw [ite_eq_right hpr]
      obtain ⟨η,hη,Hη⟩:=planar_refinement_generic LaurentRay.vUnit Ω C e he B hB hcomp L hdeg
        (n+1) (e r) s hrs ka hkr hks hzero p d hd hp hpP F
      have hη2 : 0 < η/2:=by positivity
      have hηlt : η/2 < η:=by linarith
      obtain ⟨hgen,Href⟩:=Hη (η/2) hη2 hηlt
      have HI:=ih p d hd hp (ka+(η/2) • B.flip (e p)) (hgen.mono C (by omega))
      apply HI.congr LaurentRay.vUnit Ω
      intro i hi
      exact (Href i (by omega)).trans (hcut _ i (by omega)).symm)
  apply hout.congr LaurentRay.vUnit Ω
  intro i hi
  rw [line_minus_covector Ω e B hcomp]
  exact (hcut _ i hi).trans (hrefm i hi).symm
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.ElementaryPositivity.QuantumTorus.wall_joint_induction_oai.{u_1, u_2, u_3} := @OAI.ElementaryPositivity.QuantumTorus.wall_joint_induction_oai.{u_1, u_2, u_3}
