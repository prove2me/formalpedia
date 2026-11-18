-- Prove2me | solution 1 for OAI.ElementaryPositivity.RawShuffle.primitiveBasisFamilyWords_span
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T19:19:57.185211+00:00
-- url     : https://prove2.me/submissions/a21c7244-da50-43c4-a74b-0078e9a58a49

import Mathlib
import Definitions.Def_OAIQ368Chrom047
import Definitions.Def_OAIQ368Chrom048
import Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_globalCoproduct_mul

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_NilpotentSeriesInverse
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.quotientAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.FiniteLog
open PowerSeries
variable {A : Type*} [Ring A] [Algebra ℚ A]

open scoped IsMulCommutative in
lemma nilEval_exp_log {x : A} (hx : IsNilpotent x) :
    nilEval (nilEval x (log ℚ)) (exp ℚ)=1+x := by
  let s : Set A := {x}
  have hs : ∀ u ∈ s, ∀ v ∈ s, u*v=v*u := by
    intro u hu v hv
    rw [Set.mem_singleton_iff] at hu hv
    subst u; subst v; rfl
  let T := Algebra.adjoin ℚ s
  let : IsMulCommutative T := Algebra.isMulCommutative_adjoin ℚ
    (fun left hleft right hright => hs left hleft right hright)
  let : CommRing T := inferInstance
  let tx : T := ⟨x,Algebra.subset_adjoin (Set.mem_singleton x)⟩
  have htx : IsNilpotent tx := by
    obtain ⟨n,hn⟩ := hx
    exact ⟨n,Subtype.ext hn⟩
  have h := congrArg (Algebra.adjoin ℚ s).val (exp_nilEval_log htx)
  rw [←nilEval_exp (nilEval_nilpotent htx (constantCoeff_log (A := ℚ))),
    map_nilEval _ (nilEval_nilpotent htx (constantCoeff_log (A := ℚ))),
    map_nilEval _ htx,map_add,map_one] at h
  exact h

end ElementaryPositivity.FiniteLog

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_WordLengthFiltration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity
open scoped BigOperators
variable {J A : Type*} [Ring A]

lemma wordProduct_nil (b : J → A) : wordProduct b []=1 := rfl
lemma wordProduct_cons (b : J → A) (i : J) (l : List J) :
    wordProduct b (i::l)=b i*wordProduct b l := rfl
lemma wordProduct_append (b : J → A) (l m : List J) :
    wordProduct b (l++m)=wordProduct b l*wordProduct b m := by
  simp only [wordProduct,List.map_append,List.prod_append]

variable [Algebra ℚ A]

lemma wordLengthFiltration_word (b : J → A) (l : List J) (n : ℕ) (h : l.length≤n) :
    wordProduct b l ∈ wordLengthFiltration b n := Submodule.subset_span ⟨l,h,rfl⟩

lemma wordLengthFiltration_letter (b : J → A) (i : J) : b i ∈ wordLengthFiltration b 1 := by
  simpa only [wordProduct_cons,wordProduct_nil,mul_one] using wordLengthFiltration_word b [i] 1 le_rfl

lemma wordLengthFiltration_mul (b : J → A) {m n : ℕ} {x y : A}
    (hx : x ∈ wordLengthFiltration b m) (hy : y ∈ wordLengthFiltration b n) :
    x*y ∈ wordLengthFiltration b (m+n) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l,hl,rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k,hk,rfl⟩ := hy
      rw [← wordProduct_append]
      exact wordLengthFiltration_word b (l++k) (m+n) (by simpa using Nat.add_le_add hl hk)
    | zero => simpa only [mul_zero] using (wordLengthFiltration b (m+n)).zero_mem
    | add x y hx hy hxi hyi => simpa only [mul_add] using (wordLengthFiltration b (m+n)).add_mem hxi hyi
    | smul r x hx hxi => simpa only [Algebra.mul_smul_comm] using (wordLengthFiltration b (m+n)).smul_mem r hxi
  | zero => simpa only [zero_mul] using (wordLengthFiltration b (m+n)).zero_mem
  | add x z hx hz hxi hzi => simpa only [add_mul] using (wordLengthFiltration b (m+n)).add_mem hxi hzi
  | smul r x hx hxi => simpa only [Algebra.smul_mul_assoc] using (wordLengthFiltration b (m+n)).smul_mem r hxi

lemma wordLengthFiltration_span_range (b : J → A) :
    Submodule.span ℚ (Set.range b) ≤ wordLengthFiltration b 1 := by
  apply Submodule.span_le.mpr
  rintro x ⟨i,rfl⟩
  exact wordLengthFiltration_letter b i

lemma adjoin_le_span_words (b : J → A) :
    (Algebra.adjoin ℚ (Set.range b)).toSubmodule ≤
      Submodule.span ℚ (Set.range (wordProduct b)) := by
  let S := Submodule.span ℚ (Set.range (wordProduct b))
  have hm : ∀ x∈S,∀ y∈S,x*y∈S := by
    intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l,rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨k,rfl⟩ := hy
        rw [←wordProduct_append]
        exact Submodule.subset_span ⟨l++k,rfl⟩
      | zero => simpa only [mul_zero] using S.zero_mem
      | add x y hx hy hxi hyi => simpa only [mul_add] using S.add_mem hxi hyi
      | smul r x hx hxi => simpa only [Algebra.mul_smul_comm] using S.smul_mem r hxi
    | zero => simpa only [zero_mul] using S.zero_mem
    | add x z hx hz hxi hzi => simpa only [add_mul] using S.add_mem hxi hzi
    | smul r x hx hxi => simpa only [Algebra.smul_mul_assoc] using S.smul_mem r hxi
  let T : Subalgebra ℚ A :=
    { S with
      one_mem' := Submodule.subset_span ⟨[],rfl⟩
      mul_mem' := fun hx hy=>hm _ hx _ hy
      algebraMap_mem' := fun r=>by
        rw [Algebra.algebraMap_eq_smul_one]
        exact S.smul_mem r (Submodule.subset_span ⟨[],rfl⟩) }
  have h : Algebra.adjoin ℚ (Set.range b) ≤ T := by
    apply Algebra.adjoin_le
    rintro x ⟨i,rfl⟩
    change b i∈S
    have hi : wordProduct b [i]∈S := Submodule.subset_span ⟨[i],rfl⟩
    simpa only [wordProduct_cons,wordProduct_nil,mul_one] using hi
  exact h

end ElementaryPositivity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Histories_ColorWordReordering
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity
variable {J A : Type*} [Ring A] [Algebra ℚ A]
variable (b : J → A) (ε : J → J → ℚ)

lemma wordProduct_perm_mod_lower
    (hε : ∀ i j,ε i j ≠ 0)
    (hcomm : ∀ i j,b i*b j-ε i j • (b j*b i) ∈ wordLengthFiltration b 1)
    {l m : List J} (h : l.Perm m) :
    ∃ r : ℚ,r ≠ 0 ∧ wordProduct b l-r • wordProduct b m ∈ wordLengthFiltration b (l.length-1) := by
  induction h with
  | nil => exact ⟨1,one_ne_zero,by simp⟩
  | @cons i l m hp ih =>
    by_cases hl : l=[]
    · subst l
      have hm : m=[] := List.nil_perm.mp hp
      subst m
      exact ⟨1,one_ne_zero,by simp⟩
    obtain ⟨r,hr,hd⟩ := ih
    refine ⟨r,hr,?_⟩
    have hh := wordLengthFiltration_mul b (wordLengthFiltration_letter b i) hd
    have he : 1+(l.length-1)=(i::l).length-1 := by
      have hn := List.length_pos_iff.mpr hl
      simp only [List.length_cons]
      omega
    rw [he] at hh
    simpa only [wordProduct_cons,mul_sub,Algebra.mul_smul_comm] using hh
  | swap i j l =>
    refine ⟨ε j i,hε j i,?_⟩
    have hh := wordLengthFiltration_mul b (hcomm j i) (wordLengthFiltration_word b l l.length le_rfl)
    have he : 1+l.length=(j::i::l).length-1 := by simp; omega
    rw [he] at hh
    simpa only [wordProduct_cons,sub_mul,Algebra.smul_mul_assoc,mul_assoc] using hh
  | @trans l m n hlm hmn ihl ihm =>
    obtain ⟨r,hr,hdl⟩ := ihl
    obtain ⟨s,hs,hdm⟩ := ihm
    refine ⟨r*s,mul_ne_zero hr hs,?_⟩
    rw [←hlm.length_eq] at hdm
    have hh := (wordLengthFiltration b (l.length-1)).add_mem hdl
      ((wordLengthFiltration b (l.length-1)).smul_mem r hdm)
    simpa only [smul_sub,smul_smul,sub_add_sub_cancel] using hh

section Ordered
variable [LinearOrder J]

lemma sorted_not_colorAdmissible {l : List J} (hl : l.Pairwise (· ≤ ·))
    (hn : ¬ColorAdmissible ε l) : ∃ i t,ε i i ≠ 1 ∧ l.Perm (i::i::t) := by
  induction l with
  | nil => exact (hn (by simp [ColorAdmissible])).elim
  | cons j l ih =>
    have hlc := List.pairwise_cons.mp hl
    by_cases ht : ColorAdmissible ε l
    · have hj : ¬∀ i∈l,j ≤ i ∧ (j=i → ε j j=1) := by
        intro hh
        exact hn (List.pairwise_cons.mpr ⟨hh,ht⟩)
      obtain ⟨i,hi⟩ := not_forall.mp hj
      obtain ⟨hi,hbad⟩ := Classical.not_imp.mp hi
      have heq : j=i := by
        by_contra hne
        exact hbad ⟨hlc.1 i hi,fun h=>False.elim (hne h)⟩
      subst i
      have he : ε j j ≠ 1 := fun h=>hbad ⟨le_rfl,fun _=>h⟩
      obtain ⟨u,v,rfl⟩ := List.mem_iff_append.mp hi
      exact ⟨j,u++v,he,List.Perm.cons j List.perm_middle⟩
    · obtain ⟨i,t,he,hp⟩ := ih hlc.2 ht
      refine ⟨i,j::t,he,?_⟩
      exact (hp.cons j).trans ((List.Perm.swap i j (i::t)).trans
        (List.Perm.cons i (List.Perm.swap i j t)))

lemma colorWordSpan_admissible (l : List J) (hl : ColorAdmissible ε l) :
    wordProduct b l ∈ colorWordSpan b ε := Submodule.subset_span ⟨l,hl,rfl⟩

theorem colorWordSpan_word
    (hε : ∀ i j,ε i j ≠ 0)
    (hcomm : ∀ i j,b i*b j-ε i j • (b j*b i) ∈ wordLengthFiltration b 1)
    (hsquare : ∀ i,ε i i ≠ 1 → b i*b i ∈ wordLengthFiltration b 1)
    (l : List J) : wordProduct b l ∈ colorWordSpan b ε := by
  have hmain : ∀ n,∀ l : List J,l.length=n → wordProduct b l ∈ colorWordSpan b ε := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro l hl
      by_cases hn : n=0
      · have hnil : l=[] := List.length_eq_zero_iff.mp (hl.trans hn)
        rw [hnil]
        exact colorWordSpan_admissible b ε [] (by simp [ColorAdmissible])
      have hlow : wordLengthFiltration b (n-1) ≤ colorWordSpan b ε := by
        apply Submodule.span_le.mpr
        rintro x ⟨t,ht,rfl⟩
        exact ih t.length (by omega) t rfl
      let m := l.insertionSort (· ≤ ·)
      have hm : m.Pairwise (· ≤ ·) := List.pairwise_insertionSort _ _
      have hpm : l.Perm m := (List.perm_insertionSort _ l).symm
      have htransfer : ∀ t : List J,l.Perm t → wordProduct b t ∈ colorWordSpan b ε →
          wordProduct b l ∈ colorWordSpan b ε := by
        intro t hp ht
        obtain ⟨r,hr,hd⟩ := wordProduct_perm_mod_lower b ε hε hcomm hp
        rw [hl] at hd
        have hh := (colorWordSpan b ε).add_mem (hlow hd) ((colorWordSpan b ε).smul_mem r ht)
        simpa only [sub_add_cancel] using hh
      by_cases ha : ColorAdmissible ε m
      · exact htransfer m hpm (colorWordSpan_admissible b ε m ha)
      · obtain ⟨i,t,hi,hpt⟩ := sorted_not_colorAdmissible ε hm ha
        apply htransfer (i::i::t) (hpm.trans hpt)
        have hh := wordLengthFiltration_mul b (hsquare i hi) (wordLengthFiltration_word b t t.length le_rfl)
        have hlen : 1+t.length=n-1 := by
          have he := (hpm.trans hpt).length_eq
          simp only [List.length_cons] at he
          omega
        rw [hlen] at hh
        apply hlow
        simpa only [wordProduct_cons,mul_assoc] using hh
  exact hmain l.length l rfl

lemma colorWordSpan_top
    (hε : ∀ i j,ε i j ≠ 0)
    (hcomm : ∀ i j,b i*b j-ε i j • (b j*b i) ∈ wordLengthFiltration b 1)
    (hsquare : ∀ i,ε i i ≠ 1 → b i*b i ∈ wordLengthFiltration b 1)
    (hgen : Algebra.adjoin ℚ (Set.range b)=⊤) : colorWordSpan b ε=⊤ := by
  apply top_unique
  have ha := adjoin_le_span_words b
  rw [hgen] at ha
  apply le_trans ha
  apply Submodule.span_le.mpr
  rintro x ⟨l,rfl⟩
  exact colorWordSpan_word b ε hε hcomm hsquare l

end Ordered
end ElementaryPositivity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalConvolutionSeries
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped DirectSum
open WithConv ElementaryPositivity.FiniteLog
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {A B : Type*} [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]

lemma convSeries_order_one
    {f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)} (p : PowerSeries ℚ)
    (hp : PowerSeries.constantCoeff p=0) : convVanishes a c η hc θ 1 (convSeries a c η hc θ f p) := by
  intro k hk x
  have hd : dimensionSize k.1.val=0 := by omega
  rw [convSeries_lof,hd]
  simp only [zero_add,Finset.sum_range_one,PowerSeries.coeff_zero_eq_constantCoeff,hp,zero_smul]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalPrimitiveGeneration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open WithConv ElementaryPositivity.FiniteLog
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {A : Type*} [Ring A] [Algebra ℚ A]

lemma convSeries_exp_log {f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)}
    (hf : convVanishes a c η hc θ 1 f) :
    convSeries a c η hc θ (convSeries a c η hc θ f (PowerSeries.log ℚ)) (PowerSeries.exp ℚ)=1+f := by
  apply convolutionProjection_jointly_injective a c η hc θ
  intro n
  rw [convolutionProjection_series a c η hc θ n
    (convSeries_order_one a c η hc θ (PowerSeries.log ℚ) (PowerSeries.constantCoeff_log (A := ℚ))),
    convolutionProjection_series a c η hc θ n hf,map_add,map_one]
  exact nilEval_exp_log ⟨n,convolutionProjection_nilpotent a c η hc θ n hf⟩

theorem globalPrimitiveLog_exponential :
    convSeries a c η hc θ (toConv (globalPrimitiveLog a c η hc θ)) (PowerSeries.exp ℚ)=
      toConv (LinearMap.id : UnitalShuffle a c η hc θ →ₗ[ℚ] UnitalShuffle a c η hc θ) := by
  have h := convSeries_exp_log a c η hc θ (convolutionJ_vanishes a c η hc θ)
  change convSeries a c η hc θ (toConv (globalPrimitiveLog a c η hc θ)) (PowerSeries.exp ℚ)=_ at h
  rw [convolutionJ] at h
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (abel)

lemma convolution_mapsTo_mul (S : Subalgebra ℚ A)
    {f g : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)}
    (hf : ∀ x,f.ofConv x ∈ S) (hg : ∀ x,g.ofConv x ∈ S) :
    ∀ x,(f*g).ofConv x ∈ S := by
  intro x
  rw [LinearMap.convMul_apply]
  generalize Coalgebra.comul (R := ℚ) x=t
  induction t using OAI.tensorInductionOn with
  | add t u ht hu => simpa only [map_add] using S.add_mem ht hu
  | tmul x y =>
    rw [TensorProduct.map_tmul,LinearMap.mul'_apply]
    exact S.mul_mem (hf x) (hg y)

lemma convolution_mapsTo_pow (S : Subalgebra ℚ A)
    {f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)}
    (hf : ∀ x,f.ofConv x ∈ S) (n : ℕ) : ∀ x,(f^n).ofConv x ∈ S := by
  induction n with
  | zero => intro x; exact S.algebraMap_mem _
  | succ n ih =>
    rw [pow_succ]
    exact convolution_mapsTo_mul a c η hc θ S ih hf

theorem globalPrimitiveLog_adjoin :
    Algebra.adjoin ℚ (Set.range (globalPrimitiveLog a c η hc θ))=⊤ := by
  apply top_unique
  intro x hx
  clear hx
  induction x using DirectSum.induction_on with
  | zero => exact Subalgebra.zero_mem _
  | add x y hx hy => exact Subalgebra.add_mem _ hx hy
  | of k x =>
    let S := Algebra.adjoin ℚ (Set.range (globalPrimitiveLog a c η hc θ))
    have h := congrArg (fun f=>f.ofConv (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x))
      (globalPrimitiveLog_exponential a c η hc θ)
    rw [convSeries_lof] at h
    simp only [LinearMap.id_apply] at h
    change DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x ∈ S
    rw [←h]
    apply Subalgebra.sum_mem
    intro r hr
    exact S.smul_mem (convolution_mapsTo_pow a c η hc θ S
      (fun x=>Algebra.subset_adjoin ⟨x,rfl⟩) r _) _

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalPrimitiveBracket
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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

omit [DecidableEq I] in
lemma globalColorSign_symm (k l : SlopeWeight c η hc θ) :
    globalColorSign a c η hc θ k l=globalColorSign a c η hc θ l k := by
  unfold globalColorSign
  congr 1
  by_cases hk : k.1.val=0
  · rw [hk]; simp [eulerForm]
  by_cases hl : l.1.val=0
  · rw [hl]; simp [eulerForm]
  exact hχ.out _ _ hk hl (k.1.property.resolve_left hk) (l.1.property.resolve_left hl)

omit [DecidableEq I] [Fact (SlopeEulerSymmetric a c η θ)] in
lemma globalColorSign_sq (k l : SlopeWeight c η hc θ) :
    globalColorSign a c η hc θ k l*globalColorSign a c η hc θ k l=1 := by
  simp only [globalColorSign,neg_one_zpow_eq_ite]
  split <;> norm_num

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

lemma globalPrimitive_product_coproduct {k l : SlopeWeight c η hc θ}
    {x y : UnitalShuffle a c η hc θ}
    (hx : x ∈ globalHomogeneous a c η hc θ k) (hy : y ∈ globalHomogeneous a c η hc θ l)
    (hpx : x ∈ globalPrimitives a c η hc θ) (hpy : y ∈ globalPrimitives a c η hc θ) :
    globalCoproduct a c η hc θ (x*y)=
      (x*y)⊗ₜ[ℚ](1:UnitalShuffle a c η hc θ)+x⊗ₜ[ℚ]y+
        globalColorSign a c η hc θ k l • (y⊗ₜ[ℚ]x)+
        (1:UnitalShuffle a c η hc θ)⊗ₜ[ℚ](x*y) := by
  rw [globalCoproduct_mul,(mem_globalPrimitives a c η hc θ x).mp hpx,
    (mem_globalPrimitives a c η hc θ y).mp hpy]
  change globalSignedTensorMultiply a c η hc θ (x⊗ₜ[ℚ]1+1⊗ₜ[ℚ]x) (y⊗ₜ[ℚ]1+1⊗ₜ[ℚ]y)=_
  simp only [map_add,LinearMap.add_apply]
  rw [signedTensor_mul_homogeneous a c η hc θ hx (globalHomogeneous_one a c η hc θ) hy (globalHomogeneous_one a c η hc θ),
    signedTensor_mul_homogeneous a c η hc θ hx (globalHomogeneous_one a c η hc θ) (globalHomogeneous_one a c η hc θ) hy,
    signedTensor_mul_homogeneous a c η hc θ (globalHomogeneous_one a c η hc θ) hx hy (globalHomogeneous_one a c η hc θ),
    signedTensor_mul_homogeneous a c η hc θ (globalHomogeneous_one a c η hc θ) hx (globalHomogeneous_one a c η hc θ) hy]
  simp only [globalColorSign_zero_left,globalColorSign_zero_right,one_smul]
  change ((x*y)⊗ₜ[ℚ]((1:UnitalShuffle a c η hc θ)*1)+
    globalColorSign a c η hc θ k l • ((1*y)⊗ₜ[ℚ](x*1)))+
    ((x*1)⊗ₜ[ℚ](1*y)+(1*1)⊗ₜ[ℚ](x*y))=_
  rw [show x*1=x from mul_one x,show (1:UnitalShuffle a c η hc θ)*1=1 from one_mul 1,
    show 1*y=y from one_mul y]
  abel

theorem globalPrimitive_bracket {k l : SlopeWeight c η hc θ}
    {x y : UnitalShuffle a c η hc θ}
    (hx : x ∈ globalHomogeneous a c η hc θ k) (hy : y ∈ globalHomogeneous a c η hc θ l)
    (hpx : x ∈ globalPrimitives a c η hc θ) (hpy : y ∈ globalPrimitives a c η hc θ) :
    x*y-globalColorSign a c η hc θ k l • (y*x) ∈ globalPrimitives a c η hc θ := by
  rw [mem_globalPrimitives,map_sub,map_smul,
    globalPrimitive_product_coproduct a c η hc θ hx hy hpx hpy,
    globalPrimitive_product_coproduct a c η hc θ hy hx hpy hpx,
    globalColorSign_symm a c η hc θ l k]
  change _=(x*y-_ • (y*x))⊗ₜ[ℚ]1+1⊗ₜ[ℚ](x*y-_ • (y*x))
  simp only [smul_add,smul_smul,globalColorSign_sq,one_smul,
    TensorProduct.sub_tmul,TensorProduct.tmul_sub,TensorProduct.smul_tmul,TensorProduct.tmul_smul]
  abel

theorem globalPrimitive_odd_square {k : SlopeWeight c η hc θ}
    {x : UnitalShuffle a c η hc θ}
    (hx : x ∈ globalHomogeneous a c η hc θ k) (hpx : x ∈ globalPrimitives a c η hc θ)
    (hodd : globalColorSign a c η hc θ k k = -1) : x*x ∈ globalPrimitives a c η hc θ := by
  rw [mem_globalPrimitives,globalPrimitive_product_coproduct a c η hc θ hx hx hpx hpx,hodd]
  change (x*x)⊗ₜ[ℚ]1+x⊗ₜ[ℚ]x+(-1:ℚ) • (x⊗ₜ[ℚ]x)+1⊗ₜ[ℚ](x*x)=
    (x*x)⊗ₜ[ℚ]1+1⊗ₜ[ℚ](x*x)
  have hs : (-1:ℚ) • (x⊗ₜ[ℚ]x)= -(x⊗ₜ[ℚ]x) := neg_one_smul ℚ (x⊗ₜ[ℚ]x)
  rw [hs]
  abel

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalPBWBasis
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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

include hspan in
omit [LinearOrder J] in
lemma primitiveBasisFamily_adjoin :
    Algebra.adjoin ℚ (Set.range (b))=⊤ := by
  have hp : globalPrimitives a c η hc θ ≤
      (Algebra.adjoin ℚ (Set.range (b))).toSubmodule := by
    rw [←hspan]
    apply Submodule.span_le.mpr
    exact fun _ hx=>Algebra.subset_adjoin hx
  apply top_unique
  rw [←globalPrimitiveLog_adjoin a c η hc θ]
  apply Algebra.adjoin_le
  rintro x ⟨y,rfl⟩
  exact hp ((mem_globalPrimitives a c η hc θ _).mpr (globalPrimitiveLog_primitive a c η hc θ y))

include hspan in
omit [LinearOrder J] in
lemma primitiveBasisFamily_wordLength {x : UnitalShuffle a c η hc θ}
    (hx : x ∈ globalPrimitives a c η hc θ) :
    x ∈ wordLengthFiltration (b) 1 := by
  apply wordLengthFiltration_span_range
  rwa [hspan]

include hw hp hspan in
lemma primitiveBasisFamilyWords_span_oai :
    Submodule.span ℚ (Set.range (fun l : PBWWord a c η hc θ (w)=>
      primitiveWord a c η hc θ (b) l.val))=⊤ := by
  let ε := fun i j=>globalColorSign a c η hc θ (w i) (w j)
  have he : ∀ i j,ε i j ≠ 0 := by
    intro i j h
    have hh := globalColorSign_sq a c η hc θ (w i) (w j)
    change ε i j*ε i j=1 at hh
    rw [h,zero_mul] at hh
    exact zero_ne_one hh
  have hcomm : ∀ i j,b i*b j-ε i j • (b j*b i) ∈ wordLengthFiltration b 1 := by
    intro i j
    exact primitiveBasisFamily_wordLength a c η hc θ b hspan
      (globalPrimitive_bracket a c η hc θ (hw i)
        (hw j)
        (hp i)
        (hp j))
  have hsquare : ∀ i,ε i i ≠ 1 → b i*b i ∈ wordLengthFiltration b 1 := by
    intro i hi
    have hs : ε i i= -1 := (mul_self_eq_one_iff.mp (globalColorSign_sq a c η hc θ (w i) (w i))).resolve_left hi
    exact primitiveBasisFamily_wordLength a c η hc θ b hspan
      (globalPrimitive_odd_square a c η hc θ (hw i)
        (hp i) hs)
  have ht := colorWordSpan_top b ε he hcomm hsquare (primitiveBasisFamily_adjoin a c η hc θ b hspan)
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  unfold colorWordSpan
  congr 1
  ext x
  constructor
  · rintro ⟨l,rfl⟩
    exact ⟨l.val,l.property,rfl⟩
  · rintro ⟨l,hl,rfl⟩
    exact ⟨⟨l,hl⟩,rfl⟩

end ElementaryPositivity.RawShuffle

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.ElementaryPositivity.RawShuffle.primitiveBasisFamilyWords_span_oai.{u_1, u_2} := @OAI.ElementaryPositivity.RawShuffle.primitiveBasisFamilyWords_span_oai.{u_1, u_2}
