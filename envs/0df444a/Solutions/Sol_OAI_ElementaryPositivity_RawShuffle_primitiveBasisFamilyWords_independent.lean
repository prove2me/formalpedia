-- Prove2me | solution 1 for OAI.ElementaryPositivity.RawShuffle.primitiveBasisFamilyWords_independent
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T19:19:55.948543+00:00
-- url     : https://prove2.me/submissions/ca74dbc1-05cd-4d23-accd-4b620ca73406

import Mathlib
import Definitions.Def_OAIQ368Chrom047
import Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_globalCoproduct_mul

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalPrimitiveBracket
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open WithConv
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [hχ : Fact (SlopeEulerSymmetric a c η θ)]

omit [DecidableEq I] [Fact (SlopeEulerSymmetric a c η θ)] in
lemma globalColorSign_zero_left (k : SlopeWeight c η hc θ) :
    globalColorSign a c η hc θ 0 k=1 := by simp [globalColorSign,eulerForm]
omit [DecidableEq I] [Fact (SlopeEulerSymmetric a c η θ)] in
lemma globalColorSign_zero_right (k : SlopeWeight c η hc θ) :
    globalColorSign a c η hc θ k 0=1 := by simp [globalColorSign,eulerForm]

omit hχ in
lemma globalHomogeneous_one : (1 : UnitalShuffle a c η hc θ) ∈ globalHomogeneous a c η hc θ 0 :=
  ⟨unitalGradeOne a c η hc θ,rfl⟩

lemma signedTensor_mul_homogeneous {k l m n : SlopeWeight c η hc θ}
    {x y z w : UnitalShuffle a c η hc θ}
    (hx : x ∈ globalHomogeneous a c η hc θ k) (hy : y ∈ globalHomogeneous a c η hc θ l)
    (hz : z ∈ globalHomogeneous a c η hc θ m) (hw : w ∈ globalHomogeneous a c η hc θ n) :
    globalSignedTensorMultiply a c η hc θ (x⊗ₜ[ℚ]y) (z⊗ₜ[ℚ]w)=
      globalColorSign a c η hc θ l m • ((x*z)⊗ₜ[ℚ](y*w)) := by
  obtain ⟨x,rfl⟩ := hx
  obtain ⟨y,rfl⟩ := hy
  obtain ⟨z,rfl⟩ := hz
  obtain ⟨w,rfl⟩ := hw
  exact globalSignedTensorMultiply_tmul_lof a c η hc θ k l m n x y z w

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {J : Type*}

lemma primitiveWord_nil (b : J → UnitalShuffle a c η hc θ) : primitiveWord a c η hc θ b []=1 := rfl
lemma primitiveWord_cons (b : J → UnitalShuffle a c η hc θ) (i : J) (l : List J) :
    primitiveWord a c η hc θ b (i::l)=b i*primitiveWord a c η hc θ b l := rfl

lemma primitiveWord_homogeneous (w : J → SlopeWeight c η hc θ)
    (b : J → UnitalShuffle a c η hc θ) (hb : ∀ i,b i ∈ globalHomogeneous a c η hc θ (w i))
    (l : List J) : primitiveWord a c η hc θ b l ∈
      globalHomogeneous a c η hc θ (wordWeight c η hc θ w l) := by
  induction l with
  | nil => exact globalHomogeneous_one a c η hc θ
  | cons i l ih => exact globalHomogeneous_mul a c η hc θ (hb i) ih

omit [DecidableEq I] [Fact (SlopeEulerSymmetric a c η θ)] in
lemma signedWordCuts_lengths (w : J → SlopeWeight c η hc θ) (l : List J)
    (s : SignedWordCut J) (hs : s ∈ signedWordCuts a c η hc θ w l) :
    s.left.length+s.right.length=l.length := by
  induction l generalizing s with
  | nil => simp only [signedWordCuts,List.mem_singleton] at hs; subst s; rfl
  | cons i l ih =>
    simp only [signedWordCuts,List.mem_append,List.mem_map] at hs
    rcases hs with ⟨s,hs,rfl⟩ | ⟨s,hs,rfl⟩
    · have h := ih s hs
      change (s.left.length+1)+s.right.length=l.length+1
      omega
    · have h := ih s hs
      change s.left.length+(s.right.length+1)=l.length+1
      omega

omit [DecidableEq I] [Fact (SlopeEulerSymmetric a c η θ)] in
lemma signedWordCuts_sublist (w : J → SlopeWeight c η hc θ) (l : List J)
    (s : SignedWordCut J) (hs : s ∈ signedWordCuts a c η hc θ w l) :
    s.left.Sublist l ∧ s.right.Sublist l := by
  induction l generalizing s with
  | nil => simp only [signedWordCuts,List.mem_singleton] at hs; subst s; exact ⟨.refl _,.refl _⟩
  | cons i l ih =>
    simp only [signedWordCuts,List.mem_append,List.mem_map] at hs
    rcases hs with ⟨s,hs,rfl⟩ | ⟨s,hs,rfl⟩
    · exact ⟨(ih s hs).1.cons_cons i,(ih s hs).2.cons i⟩
    · exact ⟨(ih s hs).1.cons i,(ih s hs).2.cons_cons i⟩

lemma wordCutTensor_left (w : J → SlopeWeight c η hc θ)
    (b : J → UnitalShuffle a c η hc θ) (hb : ∀ i,b i ∈ globalHomogeneous a c η hc θ (w i))
    (i : J) (s : SignedWordCut J) :
    globalSignedTensorMultiply a c η hc θ (b i⊗ₜ[ℚ]1) (wordCutTensor a c η hc θ b s)=
      wordCutTensor a c η hc θ b (s.prependLeft i) := by
  unfold wordCutTensor
  rw [map_smul,signedTensor_mul_homogeneous a c η hc θ (hb i) (globalHomogeneous_one a c η hc θ)
    (primitiveWord_homogeneous a c η hc θ w b hb s.left)
    (primitiveWord_homogeneous a c η hc θ w b hb s.right),globalColorSign_zero_left,one_smul]
  rw [show (1:UnitalShuffle a c η hc θ)*primitiveWord a c η hc θ b s.right=_ from one_mul _]
  rfl

lemma wordCutTensor_right (w : J → SlopeWeight c η hc θ)
    (b : J → UnitalShuffle a c η hc θ) (hb : ∀ i,b i ∈ globalHomogeneous a c η hc θ (w i))
    (i : J) (s : SignedWordCut J) :
    globalSignedTensorMultiply a c η hc θ (1⊗ₜ[ℚ]b i) (wordCutTensor a c η hc θ b s)=
      wordCutTensor a c η hc θ b (s.prependRight a c η hc θ w i) := by
  unfold wordCutTensor
  rw [map_smul,signedTensor_mul_homogeneous a c η hc θ (globalHomogeneous_one a c η hc θ) (hb i)
    (primitiveWord_homogeneous a c η hc θ w b hb s.left)
    (primitiveWord_homogeneous a c η hc θ w b hb s.right)]
  rw [show (1:UnitalShuffle a c η hc θ)*primitiveWord a c η hc θ b s.left=_ from one_mul _,smul_smul]
  rfl

theorem globalCoproduct_primitiveWord (w : J → SlopeWeight c η hc θ)
    (b : J → UnitalShuffle a c η hc θ) (hb : ∀ i,b i ∈ globalHomogeneous a c η hc θ (w i))
    (hp : ∀ i,b i ∈ globalPrimitives a c η hc θ) (l : List J) :
    globalCoproduct a c η hc θ (primitiveWord a c η hc θ b l)=
      ((signedWordCuts a c η hc θ w l).map (wordCutTensor a c η hc θ b)).sum := by
  induction l with
  | nil =>
    change globalCoproduct a c η hc θ (globalUnit a c η hc θ)=_
    rw [globalCoproduct_unit]
    simp only [signedWordCuts,List.map_singleton,List.sum_singleton,wordCutTensor,
      primitiveWord_nil,one_smul]
    rfl
  | cons i l ih =>
    rw [primitiveWord_cons,globalCoproduct_mul,(mem_globalPrimitives a c η hc θ (b i)).mp (hp i),ih]
    change globalSignedTensorMultiply a c η hc θ (b i⊗ₜ[ℚ]1+1⊗ₜ[ℚ]b i) _=_
    rw [map_add,LinearMap.add_apply]
    simp only [map_list_sum,List.map_map,Function.comp_def,signedWordCuts,List.map_append,List.sum_append]
    congr 1
    · congr 1
      apply List.map_congr_left
      intro s hs
      exact wordCutTensor_left a c η hc θ w b hb i s
    · congr 1
      apply List.map_congr_left
      intro s hs
      exact wordCutTensor_right a c η hc θ w b hb i s

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalWordPairing
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open WithConv
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {J K : Type*}

lemma functionalWord_cons (f : K → UnitalShuffle a c η hc θ →ₗ[ℚ] ℚ) (i : K) (l : List K) :
    functionalWord a c η hc θ f (i::l)=toConv (f i)*functionalWord a c η hc θ f l := rfl

lemma convolution_primitiveWord (w : J → SlopeWeight c η hc θ)
    (b : J → UnitalShuffle a c η hc θ) (hb : ∀ i,b i ∈ globalHomogeneous a c η hc θ (w i))
    (hp : ∀ i,b i ∈ globalPrimitives a c η hc θ)
    (f g : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] ℚ)) (l : List J) :
    (f*g).ofConv (primitiveWord a c η hc θ b l)=
      ((signedWordCuts a c η hc θ w l).map fun s=>s.coeff*
        (f.ofConv (primitiveWord a c η hc θ b s.left)*
          g.ofConv (primitiveWord a c η hc θ b s.right))).sum := by
  rw [LinearMap.convMul_apply]
  change LinearMap.mul' ℚ ℚ (TensorProduct.map f.ofConv g.ofConv
    (globalCoproduct a c η hc θ (primitiveWord a c η hc θ b l)))=_
  rw [globalCoproduct_primitiveWord a c η hc θ w b hb hp l]
  simp only [map_list_sum,List.map_map,Function.comp_def,wordCutTensor,map_smul,
    TensorProduct.map_tmul,LinearMap.mul'_apply,smul_eq_mul]

theorem functionalWord_longer (w : J → SlopeWeight c η hc θ)
    (b : J → UnitalShuffle a c η hc θ) (hb : ∀ i,b i ∈ globalHomogeneous a c η hc θ (w i))
    (hp : ∀ i,b i ∈ globalPrimitives a c η hc θ)
    (f : K → UnitalShuffle a c η hc θ →ₗ[ℚ] ℚ) (hf : ∀ i,f i (globalUnit a c η hc θ)=0)
    (u : List K) (v : List J) (h : v.length<u.length) :
    (functionalWord a c η hc θ f u).ofConv (primitiveWord a c η hc θ b v)=0 := by
  induction u generalizing v with
  | nil => simp at h
  | cons i u ih =>
    rw [functionalWord_cons,convolution_primitiveWord a c η hc θ w b hb hp]
    apply List.sum_eq_zero
    intro z hz
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hz
    by_cases he : s.left=[]
    · change s.coeff*(f i (primitiveWord a c η hc θ b s.left)*_)=0
      rw [he,primitiveWord_nil]
      change s.coeff*(f i (globalUnit a c η hc θ)*_)=0
      rw [hf,zero_mul,mul_zero]
    · have hl := signedWordCuts_lengths a c η hc θ w v s hs
      have hpos : 0 < s.left.length := List.length_pos_iff.mpr he
      have hr : s.right.length<u.length := by simp only [List.length_cons] at h; omega
      rw [ih s.right hr,mul_zero,mul_zero]

theorem functionalWord_top_cuts (w : J → SlopeWeight c η hc θ)
    (b : J → UnitalShuffle a c η hc θ) (hb : ∀ i,b i ∈ globalHomogeneous a c η hc θ (w i))
    (hp : ∀ i,b i ∈ globalPrimitives a c η hc θ)
    (f : K → UnitalShuffle a c η hc θ →ₗ[ℚ] ℚ) (hf : ∀ i,f i (globalUnit a c η hc θ)=0)
    (i : K) (u : List K) (v : List J) (h : v.length=u.length+1) :
    (functionalWord a c η hc θ f (i::u)).ofConv (primitiveWord a c η hc θ b v)=
      ((signedWordCuts a c η hc θ w v).map fun s=>if s.left.length=1 then s.coeff*
        (f i (primitiveWord a c η hc θ b s.left)*
          (functionalWord a c η hc θ f u).ofConv (primitiveWord a c η hc θ b s.right)) else 0).sum := by
  rw [functionalWord_cons,convolution_primitiveWord a c η hc θ w b hb hp]
  congr 1
  apply List.map_congr_left
  intro s hs
  by_cases h1 : s.left.length=1
  · simp only [h1,ite_eq_left]
  rw [ite_eq_right h1]
  by_cases he : s.left=[]
  · change s.coeff*(f i (primitiveWord a c η hc θ b s.left)*_)=0
    rw [he,primitiveWord_nil]
    change s.coeff*(f i (globalUnit a c η hc θ)*_)=0
    rw [hf,zero_mul,mul_zero]
  · have hl := signedWordCuts_lengths a c η hc θ w v s hs
    have hpos : 0 < s.left.length := List.length_pos_iff.mpr he
    have hr : s.right.length<u.length := by omega
    rw [functionalWord_longer a c η hc θ w b hb hp f hf u s.right hr,mul_zero,mul_zero]

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open WithConv
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {J : Type*}

omit [DecidableEq I] [Fact (SlopeEulerSymmetric a c η θ)] in
lemma emptyCutSum_eq (w : J → SlopeWeight c η hc θ) (l : List J) (g : List J → ℚ) :
    emptyCutSum a c η hc θ w l g=g l := by
  induction l generalizing g with
  | nil => simp [emptyCutSum,signedWordCuts]
  | cons i l ih =>
    unfold emptyCutSum
    simp only [signedWordCuts,List.map_append,List.sum_append,List.map_map,Function.comp_def]
    have hl : ((signedWordCuts a c η hc θ w l).map fun s =>
        if (s.prependLeft i).left=[] then (s.prependLeft i).coeff*g (s.prependLeft i).right else 0).sum=0 := by
      simp [SignedWordCut.prependLeft]
    rw [hl,zero_add]
    have hr : ((signedWordCuts a c η hc θ w l).map fun s =>
        if (SignedWordCut.prependRight a c η hc θ w i s).left=[] then
          (SignedWordCut.prependRight a c η hc θ w i s).coeff*g (SignedWordCut.prependRight a c η hc θ w i s).right else 0).sum=
        emptyCutSum a c η hc θ w l (fun r=>g (i::r)) := by
      unfold emptyCutSum
      congr 1
      apply List.map_congr_left
      intro s hs
      by_cases h : s.left=[]
      · simp [SignedWordCut.prependRight,h,wordWeight,globalColorSign_zero_right]
      · simp [SignedWordCut.prependRight,h]
    rw [hr,ih]

omit [DecidableEq I] [Fact (SlopeEulerSymmetric a c η θ)] in
lemma singletonCutSum_nil (w : J → SlopeWeight c η hc θ) (i : J) (g : List J → ℚ) :
    singletonCutSum a c η hc θ w i [] g=0 := by simp [singletonCutSum,signedWordCuts]

omit [DecidableEq I] [Fact (SlopeEulerSymmetric a c η θ)] in
lemma singletonCutSum_cons (w : J → SlopeWeight c η hc θ) (i j : J) (l : List J) (g : List J → ℚ) :
    singletonCutSum a c η hc θ w i (j::l) g=
      (if j=i then g l else 0)+globalColorSign a c η hc θ (w j) (w i)*
        singletonCutSum a c η hc θ w i l (fun r=>g (j::r)) := by
  unfold singletonCutSum
  simp only [signedWordCuts,List.map_append,List.sum_append,List.map_map,Function.comp_def]
  congr 1
  · by_cases h : j=i
    · subst j
      rw [ite_eq_left rfl]
      convert emptyCutSum_eq a c η hc θ w l g using 1
      all_goals try with_reducible_and_instances rfl
      unfold emptyCutSum
      congr 1
      apply List.map_congr_left
      intro s hs
      simp [SignedWordCut.prependLeft]
    · rw [ite_eq_right h]
      apply List.sum_eq_zero
      intro z hz
      obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hz
      simp [SignedWordCut.prependLeft,h]
  · rw [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro s hs
    by_cases h : s.left=[i]
    · simp [SignedWordCut.prependRight,h,wordWeight,mul_left_comm,mul_comm,mul_assoc]
    · simp [SignedWordCut.prependRight,h]

lemma functionalWord_top_singleton (w : J → SlopeWeight c η hc θ)
    (b : J → UnitalShuffle a c η hc θ) (hb : ∀ i,b i ∈ globalHomogeneous a c η hc θ (w i))
    (hp : ∀ i,b i ∈ globalPrimitives a c η hc θ)
    (f : J → UnitalShuffle a c η hc θ →ₗ[ℚ] ℚ) (hf : ∀ i,f i (globalUnit a c η hc θ)=0)
    (hfb : ∀ i j,f i (b j)=if i=j then 1 else 0)
    (i : J) (u v : List J) (h : v.length=u.length+1) :
    (functionalWord a c η hc θ f (i::u)).ofConv (primitiveWord a c η hc θ b v)=
      singletonCutSum a c η hc θ w i v
        (fun r=>(functionalWord a c η hc θ f u).ofConv (primitiveWord a c η hc θ b r)) := by
  rw [functionalWord_top_cuts a c η hc θ w b hb hp f hf i u v h]
  unfold singletonCutSum
  congr 1
  apply List.map_congr_left
  intro s hs
  by_cases h1 : s.left.length=1
  · obtain ⟨j,hj⟩ := List.length_eq_one_iff.mp h1
    rw [hj]
    simp only [List.length_singleton,ite_eq_left,primitiveWord_cons,primitiveWord_nil]
    rw [show b j*(1:UnitalShuffle a c η hc θ)=b j from mul_one _,hfb]
    by_cases hji : i=j
    · subst j; simp
    · simp [hji,Ne.symm hji]
  · rw [ite_eq_right h1]
    have hne : s.left ≠ [i] := fun hh=>h1 (by rw [hh]; rfl)
    rw [ite_eq_right hne]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalWordDetection
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open WithConv
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {J : Type*}

omit [DecidableEq I] [Fact (SlopeEulerSymmetric a c η θ)] in
lemma signedWordCuts_perm (w : J → SlopeWeight c η hc θ) (l : List J)
    (s : SignedWordCut J) (hs : s ∈ signedWordCuts a c η hc θ w l) :
    (s.left++s.right).Perm l := by
  induction l generalizing s with
  | nil => simp only [signedWordCuts,List.mem_singleton] at hs; subst s; exact .refl _
  | cons i l ih =>
    simp only [signedWordCuts,List.mem_append,List.mem_map] at hs
    rcases hs with ⟨s,hs,rfl⟩ | ⟨s,hs,rfl⟩
    · exact (ih s hs).cons i
    · exact List.perm_middle.trans ((ih s hs).cons i)

omit [DecidableEq I] [Fact (SlopeEulerSymmetric a c η θ)] in
lemma singletonCutSum_not_mem (w : J → SlopeWeight c η hc θ) (i : J) (l : List J)
    (g : List J → ℚ) (hi : i ∉ l) : singletonCutSum a c η hc θ w i l g=0 := by
  unfold singletonCutSum
  apply List.sum_eq_zero
  intro z hz
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hz
  apply ite_eq_right
  intro h
  apply hi
  exact (signedWordCuts_sublist a c η hc θ w l s hs).1.subset (by simp [h])

omit [DecidableEq I] [Fact (SlopeEulerSymmetric a c η θ)] in
lemma singletonCutSum_congr (w : J → SlopeWeight c η hc θ) (i : J) (l : List J)
    (g h : List J → ℚ)
    (he : ∀ s ∈ signedWordCuts a c η hc θ w l, s.left=[i] → g s.right=h s.right) :
    singletonCutSum a c η hc θ w i l g=singletonCutSum a c η hc θ w i l h := by
  unfold singletonCutSum
  congr 1
  apply List.map_congr_left
  intro s hs
  by_cases hi : s.left=[i]
  · rw [ite_eq_left hi,ite_eq_left hi,he s hs hi]
  · rw [ite_eq_right hi,ite_eq_right hi]

omit [DecidableEq I] [Fact (SlopeEulerSymmetric a c η θ)] in
lemma singletonCutSum_unique (w : J → SlopeWeight c η hc θ) (i : J) (l : List J)
    (g : List J → ℚ) (hi : i ∉ l) : singletonCutSum a c η hc θ w i (i::l) g=g l := by
  rw [singletonCutSum_cons,ite_eq_left rfl,singletonCutSum_not_mem a c η hc θ w i l _ hi,mul_zero,add_zero]

lemma functionalWord_top_not_perm (w : J → SlopeWeight c η hc θ)
    (b : J → UnitalShuffle a c η hc θ) (hb : ∀ i,b i ∈ globalHomogeneous a c η hc θ (w i))
    (hp : ∀ i,b i ∈ globalPrimitives a c η hc θ)
    (f : J → UnitalShuffle a c η hc θ →ₗ[ℚ] ℚ) (hf : ∀ i,f i (globalUnit a c η hc θ)=0)
    (hfb : ∀ i j,f i (b j)=if i=j then 1 else 0)
    (u v : List J) (h : v.length=u.length) (hne : ¬u.Perm v) :
    (functionalWord a c η hc θ f u).ofConv (primitiveWord a c η hc θ b v)=0 := by
  induction u generalizing v with
  | nil =>
    have hv : v=[] := List.length_eq_zero_iff.mp h
    subst v
    exact (hne (.refl _)).elim
  | cons i u ih =>
    rw [functionalWord_top_singleton a c η hc θ w b hb hp f hf hfb i u v h]
    unfold singletonCutSum
    apply List.sum_eq_zero
    intro z hz
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hz
    by_cases hi : s.left=[i]
    · rw [ite_eq_left hi]
      have hpv := signedWordCuts_perm a c η hc θ w v s hs
      rw [hi,List.singleton_append] at hpv
      have hl := signedWordCuts_lengths a c η hc θ w v s hs
      rw [hi,List.length_singleton] at hl
      have hn : ¬u.Perm s.right := fun hh=>hne ((hh.cons i).trans hpv)
      change s.coeff * (functionalWord a c η hc θ f u).ofConv (primitiveWord a c η hc θ b s.right)=0
      rw [ih s.right (by simp only [List.length_cons] at h; omega) hn,mul_zero]
    · rw [ite_eq_right hi]

section Ordered
variable [LinearOrder J]

omit [DecidableEq I] [Fact (SlopeEulerSymmetric a c η θ)] in
lemma singletonCutSum_even_sorted (w : J → SlopeWeight c η hc θ) (i : J) (v : List J)
    (hv : v.Pairwise (· ≤ ·)) (hmin : ∀ j∈v,i≤j)
    (he : globalColorSign a c η hc θ (w i) (w i)=1) (r : ℚ) :
    singletonCutSum a c η hc θ w i v (fun _=>r)=(v.count i:ℚ)*r := by
  induction v with
  | nil => simp [singletonCutSum_nil]
  | cons j v ih =>
    rw [singletonCutSum_cons]
    have hv' := List.pairwise_cons.mp hv
    by_cases hij : j=i
    · subst j
      rw [ite_eq_left rfl,he,one_mul,ih hv'.2 (fun j hj=>hmin j (List.mem_cons_of_mem _ hj))]
      simp only [List.count_cons_self,Nat.cast_add,Nat.cast_one]
      ring
    · have hi : i∉j::v := by
        intro hm
        rcases List.mem_cons.mp hm with hh | hh
        · exact hij hh.symm
        · exact hij (le_antisymm (hv'.1 i hh) (hmin j (by simp)))
      have hit : i∉v := fun hm=>hi (List.mem_cons_of_mem _ hm)
      rw [ite_eq_right hij,singletonCutSum_not_mem a c η hc θ w i v _ hit,mul_zero,add_zero]
      rw [List.count_eq_zero.mpr hi,Nat.cast_zero,zero_mul]

lemma functionalWord_top_sorted_ne (w : J → SlopeWeight c η hc θ)
    (b : J → UnitalShuffle a c η hc θ) (hb : ∀ i,b i ∈ globalHomogeneous a c η hc θ (w i))
    (hp : ∀ i,b i ∈ globalPrimitives a c η hc θ)
    (f : J → UnitalShuffle a c η hc θ →ₗ[ℚ] ℚ) (hf : ∀ i,f i (globalUnit a c η hc θ)=0)
    (hfb : ∀ i j,f i (b j)=if i=j then 1 else 0)
    (u v : List J) (hu : u.Pairwise (· ≤ ·)) (hv : v.Pairwise (· ≤ ·))
    (h : v.length=u.length) (hne : u≠v) :
    (functionalWord a c η hc θ f u).ofConv (primitiveWord a c η hc θ b v)=0 := by
  apply functionalWord_top_not_perm a c η hc θ w b hb hp f hf hfb u v h
  intro hpv
  exact hne (hpv.eq_of_pairwise' hu hv)

end Ordered
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open WithConv
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {J : Type*} [LinearOrder J]

omit [DecidableEq I] [Fact (SlopeEulerSymmetric a c η θ)] in
lemma PBWAdmissible.sorted {w : J → SlopeWeight c η hc θ} {l : List J}
    (h : PBWAdmissible a c η hc θ w l) : l.Pairwise (· ≤ ·) := h.imp (fun h=>h.1)

omit [DecidableEq I] [Fact (SlopeEulerSymmetric a c η θ)] in
lemma PBWAdmissible.tail {w : J → SlopeWeight c η hc θ} {i : J} {l : List J}
    (h : PBWAdmissible a c η hc θ w (i::l)) : PBWAdmissible a c η hc θ w l :=
  (List.pairwise_cons.mp h).2

omit [DecidableEq I] [Fact (SlopeEulerSymmetric a c η θ)] in
lemma singletonCutSum_sorted_self (w : J → SlopeWeight c η hc θ) (i : J) (l : List J)
    (h : PBWAdmissible a c η hc θ w (i::l)) (g : List J → ℚ) :
    singletonCutSum a c η hc θ w i (i::l) g=((l.count i+1:ℕ):ℚ)*g l := by
  by_cases hi : i∈l
  · have he := (List.pairwise_cons.mp h).1 i hi |>.2 rfl
    have hcst : singletonCutSum a c η hc θ w i (i::l) g=
        singletonCutSum a c η hc θ w i (i::l) (fun _=>g l) := by
      apply singletonCutSum_congr
      intro s hs hsi
      have hp := signedWordCuts_perm a c η hc θ w (i::l) s hs
      rw [hsi,List.singleton_append] at hp
      have hr := (signedWordCuts_sublist a c η hc θ w (i::l) s hs).2
      have heq : s.right=l := hp.cons_inv.eq_of_pairwise' (h.sorted.sublist hr) h.tail.sorted
      rw [heq]
    rw [hcst,singletonCutSum_even_sorted a c η hc θ w i (i::l) h.sorted
      (fun j hj=>by
        rcases List.mem_cons.mp hj with rfl | hj
        · exact le_rfl
        · exact (List.pairwise_cons.mp h.sorted).1 j hj) he,List.count_cons_self]
  · rw [singletonCutSum_unique a c η hc θ w i l g hi,List.count_eq_zero.mpr hi]
    simp

omit [LinearOrder J] in
lemma wordMultiplicity_pos (l : List J) : 0<wordMultiplicity l := by
  induction l with
  | nil => exact Nat.zero_lt_one
  | cons i l ih => exact Nat.mul_pos (Nat.succ_pos _) ih

lemma functionalWord_diagonal (w : J → SlopeWeight c η hc θ)
    (b : J → UnitalShuffle a c η hc θ) (hb : ∀ i,b i ∈ globalHomogeneous a c η hc θ (w i))
    (hp : ∀ i,b i ∈ globalPrimitives a c η hc θ)
    (f : J → UnitalShuffle a c η hc θ →ₗ[ℚ] ℚ) (hf : ∀ i,f i (globalUnit a c η hc θ)=0)
    (hfb : ∀ i j,f i (b j)=if i=j then 1 else 0)
    (l : List J) (hl : PBWAdmissible a c η hc θ w l) :
    (functionalWord a c η hc θ f l).ofConv (primitiveWord a c η hc θ b l)=(wordMultiplicity l:ℚ) := by
  induction l with
  | nil => exact globalCounit_unit a c η hc θ
  | cons i l ih =>
    rw [functionalWord_top_singleton a c η hc θ w b hb hp f hf hfb i l (i::l) rfl,
      singletonCutSum_sorted_self a c η hc θ w i l hl]
    rw [ih hl.tail]
    exact (Nat.cast_mul _ _).symm

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FilteredDualIndependence
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity
attribute [local instance] Classical.propDecidable

lemma linearIndependent_of_filtered_dual {J V : Type*} [AddCommGroup V] [Module ℚ V]
    (v : J → V) (degree : J → ℕ) (f : J → V →ₗ[ℚ] ℚ) (diag : J → ℚ)
    (hd : ∀ i,diag i ≠ 0)
    (hf : ∀ i j,degree j ≤ degree i → f i (v j)=if i=j then diag i else 0) :
    LinearIndependent ℚ v := by
  classical
  apply linearIndependent_iff.mpr
  intro l hl
  by_contra hn
  have hs : l.support.Nonempty := Finsupp.support_nonempty_iff.mpr hn
  obtain ⟨i,hi,hmax⟩ := l.support.exists_max_image degree hs
  have he := congrArg (f i) hl
  rw [map_zero,Finsupp.linearCombination_apply,Finsupp.sum] at he
  simp only [map_sum,map_smul,smul_eq_mul] at he
  have hh : (∑ j ∈ l.support,l j * f i (v j))=l i*diag i := by
    rw [Finset.sum_eq_single i]
    · rw [hf i i le_rfl,ite_eq_left rfl]
    · intro j hj hji
      rw [hf i j (hmax j hj),ite_eq_right (Ne.symm hji),mul_zero]
    · exact fun h=>False.elim (h hi)
  rw [hh] at he
  exact (Finsupp.mem_support_iff.mp hi) ((mul_eq_zero.mp he).resolve_right (hd i))

end ElementaryPositivity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalPBWIndependent
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open WithConv
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {J : Type*} [LinearOrder J]

theorem globalPBW_independent (w : J → SlopeWeight c η hc θ)
    (b : J → UnitalShuffle a c η hc θ) (hb : ∀ i,b i ∈ globalHomogeneous a c η hc θ (w i))
    (hp : ∀ i,b i ∈ globalPrimitives a c η hc θ)
    (f : J → UnitalShuffle a c η hc θ →ₗ[ℚ] ℚ) (hf : ∀ i,f i (globalUnit a c η hc θ)=0)
    (hfb : ∀ i j,f i (b j)=if i=j then 1 else 0) :
    LinearIndependent ℚ (fun l : PBWWord a c η hc θ w=>primitiveWord a c η hc θ b l.val) := by
  apply linearIndependent_of_filtered_dual
    (degree:=fun l=>l.val.length)
    (f:=fun l=>(functionalWord a c η hc θ f l.val).ofConv)
    (diag:=fun l=>(wordMultiplicity l.val:ℚ))
  · intro l
    exact_mod_cast (Nat.ne_of_gt (wordMultiplicity_pos l.val))
  · intro u v h
    by_cases huv : u=v
    · subst v
      rw [ite_eq_left rfl]
      exact functionalWord_diagonal a c η hc θ w b hb hp f hf hfb u.val u.property
    · rw [ite_eq_right huv]
      by_cases hlen : v.val.length=u.val.length
      · exact functionalWord_top_sorted_ne a c η hc θ w b hb hp f hf hfb u.val v.val
          u.property.sorted v.property.sorted hlen (fun hh=>huv (Subtype.ext hh))
      · exact functionalWord_longer a c η hc θ w b hb hp f hf u.val v.val (lt_of_le_of_ne h hlen)

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open WithConv
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

lemma globalPrimitiveProjection_unit :
    globalPrimitiveProjection a c η hc θ (globalUnit a c η hc θ)=0 := by
  apply Subtype.ext
  change (convSeries a c η hc θ (convolutionJ a c η hc θ) (PowerSeries.log ℚ)).ofConv
    (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (0,0) (unitalGradeOne a c η hc θ))=0
  rw [convSeries_lof]
  simp [dimensionSize]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalPBWBasis
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable Classical.decEq
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {J : Type*} [LinearOrder J] (b : J → UnitalShuffle a c η hc θ)
  (w : J → SlopeWeight c η hc θ)
  (hw : ∀ i,b i∈globalHomogeneous a c η hc θ (w i))
  (hp : ∀ i,b i∈globalPrimitives a c η hc θ)
  (hspan : Submodule.span ℚ (Set.range b)=globalPrimitives a c η hc θ)
  (hli : LinearIndependent ℚ b)

omit [LinearOrder J] in
lemma primitiveBasisRetraction_unit :
    primitiveBasisRetraction a c η hc θ b hspan (globalUnit a c η hc θ)=0 := by
  apply Subtype.ext
  change globalPrimitiveLog a c η hc θ (globalUnit a c η hc θ)=0
  exact congrArg (fun x : globalPrimitives a c η hc θ=>x.val) (globalPrimitiveProjection_unit a c η hc θ)

include hp in
omit [LinearOrder J] in
lemma primitiveBasisRetraction_apply (j : J) :
    primitiveBasisRetraction a c η hc θ b hspan (b j)=(Module.Basis.span hli) j := by
  apply Subtype.ext
  rw [Module.Basis.span_apply]
  exact globalPrimitiveLog_on_primitive a c η hc θ (hp j)

omit [LinearOrder J] in
lemma primitiveBasisDual_unit (j : J) :
    primitiveBasisDual a c η hc θ b hspan hli j (globalUnit a c η hc θ)=0 := by
  change (Module.Basis.span hli).coord j (primitiveBasisRetraction a c η hc θ b hspan _)=0
  rw [primitiveBasisRetraction_unit,map_zero]

include hp in
omit [LinearOrder J] in
lemma primitiveBasisDual_apply (i j : J) :
    primitiveBasisDual a c η hc θ b hspan hli i (b j)=if i=j then 1 else 0 := by
  change (Module.Basis.span hli).coord i (primitiveBasisRetraction a c η hc θ b hspan _)=_
  rw [primitiveBasisRetraction_apply a c η hc θ b hp hspan hli,Module.Basis.coord_apply,
    Module.Basis.repr_self_apply]
  congr 1
  exact propext eq_comm

include hw hp hspan hli in
lemma primitiveBasisFamilyWords_independent_oai :
    LinearIndependent ℚ (fun l : PBWWord a c η hc θ w=>primitiveWord a c η hc θ b l.val) :=
  globalPBW_independent a c η hc θ w b hw hp _
    (primitiveBasisDual_unit a c η hc θ b hspan hli)
    (primitiveBasisDual_apply a c η hc θ b hp hspan hli)

end ElementaryPositivity.RawShuffle

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.ElementaryPositivity.RawShuffle.primitiveBasisFamilyWords_independent_oai.{u_1, u_2} := @OAI.ElementaryPositivity.RawShuffle.primitiveBasisFamilyWords_independent_oai.{u_1, u_2}
