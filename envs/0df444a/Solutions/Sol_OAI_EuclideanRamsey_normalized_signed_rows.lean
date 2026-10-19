-- Prove2me | solution 1 for OAI.EuclideanRamsey.normalized_signed_rows
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:33:38.89813+00:00
-- url     : https://prove2.me/submissions/b862ffbe-1539-494f-9629-551d1a87e973

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/SignedRows.lean:L158-L230
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.normalized_signed_rows. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows

-- ---- from OAI.Combinatorics.EuclideanRamsey.SignedRows ----
namespace OAI

universe uAlpha uBeta

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators

open scoped BigOperators
namespace EuclideanRamsey

lemma integerize_finsupp {α : Type uAlpha} (f : α →₀ ℚ) :
    ∃ (M : ℕ) (z : α →₀ ℤ), 0 < M ∧ ∀ a, (z a:ℚ) = M*f a := by
  classical
  let A : Matrix Unit ↥f.support ℚ := fun _ a => f a
  let z := f.mapRange (fun q => Int.floor ((A.den:ℚ)*q)) (by simp)
  refine ⟨A.den,z,Nat.pos_of_ne_zero A.den_ne_zero,?_⟩
  intro a
  by_cases ha : a∈f.support
  · have he := A.num_div_den () ⟨a,ha⟩
    have hd : (A.den:ℚ) ≠ 0 := by exact_mod_cast A.den_ne_zero
    have hn : (A.num () ⟨a,ha⟩:ℚ) = (A.den:ℚ)*f a := by
      exact ((div_eq_iff hd).mp he).trans (mul_comm _ _)
    simp only [z,Finsupp.mapRange_apply,← hn,Int.floor_intCast]
  · simp [z,Finsupp.notMem_support_iff.mp ha]

lemma integerize_finsupp_real {α : Type uAlpha} (f : α →₀ ℚ) :
    ∃ (M : ℕ) (z : α →₀ ℤ), 0 < M ∧ ∀ a, (z a:ℝ) = M*(f a:ℝ) := by
  obtain ⟨M,z,hM,hz⟩ := integerize_finsupp f
  exact ⟨M,z,hM,fun a => by exact_mod_cast hz a⟩

lemma positiveCount_cast {α : Type uAlpha} (z : α →₀ ℤ) (a : α) :
    (positiveCount z a : ℝ) = max (z a:ℝ) 0 := by
  change ((z a).toNat:ℝ) = _
  exact_mod_cast Int.toNat_eq_max (z a)
lemma negativeCount_cast {α : Type uAlpha} (z : α →₀ ℤ) (a : α) :
    (negativeCount z a : ℝ) = max (-(z a:ℝ)) 0 := by
  change ((-(z a)).toNat:ℝ) = _
  exact_mod_cast Int.toNat_eq_max (-(z a))

lemma count_difference {α : Type uAlpha} (z : α →₀ ℤ) (a : α) :
    (positiveCount z a : ℝ)-(negativeCount z a:ℝ) = z a := by
  rw [positiveCount_cast,negativeCount_cast]
  by_cases h : 0 ≤ (z a:ℝ)
  · rw [max_eq_left h,max_eq_right (neg_nonpos.mpr h),sub_zero]
  · have h := le_of_not_ge h
    rw [max_eq_right h,max_eq_left (neg_nonneg.mpr h)]
    ring

lemma sum_multiset_elements {α : Type uAlpha} {β : Type uBeta} [DecidableEq α] [AddCommMonoid β]
    (m : Multiset α) (f : α → β) : (∑ x : m, f x) = (m.map f).sum := by
  change ((Finset.univ : Finset m).val.map (fun x : m => f x)).sum = _
  rw [Multiset.map_univ]

lemma sum_count_elements {α : Type uAlpha} [DecidableEq α] (c : α →₀ ℕ) (f : α → ℝ) :
    (∑ x : c.toMultiset, f x) = c.sum (fun a n => (n:ℝ)*f a) := by
  rw [sum_multiset_elements,Finsupp.toMultiset_map,Finsupp.sum_toMultiset,
    Finsupp.sum_mapDomain_index]
  · simp only [nsmul_eq_mul]
  · intro a; simp
  · intro a n m; simp [add_smul]

lemma multiset_map_equiv {α : Type uAlpha} {β : Type uBeta} [DecidableEq α] [DecidableEq β]
    (m n : Multiset α) (f : α → β) (h : m.map f = n.map f) :
    ∃ e : m ≃ n, ∀ x : m, f (e x) = f x := by
  let e := (m.mapEquiv f).trans ((Multiset.cast h).trans (n.mapEquiv f).symm)
  refine ⟨e,?_⟩
  intro x
  have ht := (n.mapEquiv f).apply_symm_apply ((Multiset.cast h) (m.mapEquiv f x))
  have hh := congrArg (fun y : n.map f => (y : β)) ht
  simp only [Multiset.mapEquiv_apply] at hh
  change f (e x) = (m.mapEquiv f x : β) at hh
  exact hh.trans (Multiset.mapEquiv_apply m f x)

lemma count_difference_finsupp {α : Type uAlpha} (f : α →₀ ℚ) (M : ℕ) (z : α →₀ ℤ)
    (hz : ∀ a,(z a:ℝ) = M*(f a:ℝ)) :
    (positiveCount z).mapRange (Nat.cast : ℕ → ℝ) (by simp) -
      (negativeCount z).mapRange (Nat.cast : ℕ → ℝ) (by simp) =
      (M:ℝ) • f.mapRange (Rat.cast : ℚ → ℝ) (by simp) := by
  ext a
  simp only [Finsupp.sub_apply,Finsupp.mapRange_apply,Finsupp.smul_apply,smul_eq_mul]
  exact (count_difference z a).trans (hz a)

lemma equal_count_pushforward {α : Type uAlpha} {β : Type uBeta} (f : α →₀ ℚ) (M : ℕ) (z : α →₀ ℤ)
    (hz : ∀ a,(z a:ℝ) = M*(f a:ℝ)) (g : α → β) (hg : f.mapDomain g = 0) :
    (positiveCount z).mapDomain g = (negativeCount z).mapDomain g := by
  apply Finsupp.mapRange_injective (Nat.cast : ℕ → ℝ) (by simp) Nat.cast_injective
  apply sub_eq_zero.mp
  rw [← Finsupp.mapDomain_mapRange g _ _ _ (fun x y => Nat.cast_add x y),
    ← Finsupp.mapDomain_mapRange g _ _ _ (fun x y => Nat.cast_add x y),
    ← Finsupp.mapDomain_sub,count_difference_finsupp f M z hz,
    Finsupp.mapDomain_smul,Finsupp.mapDomain_mapRange g _ _ _ (fun x y => Rat.cast_add x y),hg]
  simp

lemma equal_evaluated_multisets {α : Type uAlpha} {β : Type uBeta} (f : α →₀ ℚ) (M : ℕ) (z : α →₀ ℤ)
    (hz : ∀ a,(z a:ℝ) = M*(f a:ℝ)) (g : α → β) (hg : f.mapDomain g = 0) :
    (positiveCount z).toMultiset.map g = (negativeCount z).toMultiset.map g := by
  simp only [Finsupp.toMultiset_map,equal_count_pushforward f M z hz g hg]

lemma sum_counts_difference {α : Type uAlpha} [DecidableEq α]
    (f : α →₀ ℚ) (M : ℕ) (z : α →₀ ℤ)
    (hz : ∀ a,(z a:ℝ) = M*(f a:ℝ)) (g : α → ℝ) :
    (∑ x : (positiveCount z).toMultiset,g x) -
      (∑ x : (negativeCount z).toMultiset,g x) =
      M*f.sum (fun a q => (q:ℝ)*g a) := by
  rw [sum_count_elements,sum_count_elements]
  have hs := congrArg (fun c : α →₀ ℝ => c.sum (fun a q => q*g a))
    (count_difference_finsupp f M z hz)
  rw [Finsupp.sum_sub_index (fun a b c => sub_mul b c (g a)),
    Finsupp.sum_mapRange_index (by intro a; simp),
    Finsupp.sum_mapRange_index (by intro a; simp),
    Finsupp.sum_smul_index (by intro a; simp),
    Finsupp.sum_mapRange_index (by intro a; simp)] at hs
  rw [hs]
  simp only [Finsupp.sum,Finset.mul_sum,mul_assoc]

lemma sum_counts_negative {α : Type uAlpha} [DecidableEq α]
    (f : α →₀ ℚ) (M : ℕ) (z : α →₀ ℤ)
    (hz : ∀ a,(z a:ℝ) = M*(f a:ℝ)) (g : α → ℝ) :
    (∑ x : (negativeCount z).toMultiset,g x) =
      M*f.sum (fun a q => max (-(q:ℝ)) 0*g a) := by
  have he : (negativeCount z).mapRange (Nat.cast : ℕ → ℝ) (by simp) =
      (M:ℝ) • f.mapRange (fun q : ℚ => max (-(q:ℝ)) 0) (by simp) := by
    ext a
    simp only [Finsupp.mapRange_apply,Finsupp.smul_apply,smul_eq_mul,
      negativeCount_cast,hz,← mul_neg, mul_max_of_nonneg _ _ (Nat.cast_nonneg M),mul_zero]
  rw [sum_count_elements]
  have hs := congrArg (fun c : α →₀ ℝ => c.sum (fun a q => q*g a)) he
  rw [Finsupp.sum_mapRange_index (by intro a; simp),
    Finsupp.sum_smul_index (by intro a; simp),
    Finsupp.sum_mapRange_index (by intro a; simp)] at hs
  rw [hs]
  simp only [Finsupp.sum,Finset.mul_sum,mul_assoc]

end EuclideanRamsey

namespace EuclideanRamsey
open Matrix

theorem normalized_signed_rows {α : Type} [DecidableEq α] {d s : ℕ} (hs : 0 < s)
    (a : Fin s → Fin d → ℝ) (v : α → ℝ) (g : α → Fin d → ℝ)
    (f : α →₀ ℚ) (ζ η : ℝ) (hζ : 0 < ζ)
    (heval : ∀ i,f.mapDomain (fun x => v x+∑ j,a i j*g x j)=0)
    (hmom : ∀ j l,f.sum (fun x q => (q:ℝ)*g x j*g x l)=ζ*(if j=l then 1 else 0))
    (hneg : f.sum (fun x q => max (-(q:ℝ)) 0*(∑ j,(g x j)^2)) < η*ζ) :
    ∃ (τ : Type) (_ : Fintype τ) (vp vn : τ → ℝ) (U V : Matrix (Fin d) τ ℝ),
      U*U.transpose-V*V.transpose=1 ∧ (V*V.transpose).trace < η ∧
      ∀ i,∃ σ : Equiv.Perm τ,∀ x,
        vn (σ x)+∑ j,a i j*V j (σ x) = vp x+∑ j,a i j*U j x := by
  classical
  obtain ⟨M,z,hM,hz⟩ := integerize_finsupp_real f
  let m := (positiveCount z).toMultiset
  let n := (negativeCount z).toMultiset
  have hh (i : Fin s) : ∃ e : m ≃ n,∀ x : m,
      v (e x)+∑ j,a i j*g (e x) j = v x+∑ j,a i j*g x j :=
    multiset_map_equiv m n _ (equal_evaluated_multisets f M z hz _ (heval i))
  choose e he using hh
  let e₀ := e ⟨0,hs⟩
  let c := (Real.sqrt ((M:ℝ)*ζ))⁻¹
  have hMp : (0:ℝ)<M := by exact_mod_cast hM
  have hsq : c^2*((M:ℝ)*ζ)=1 := by
    dsimp [c]
    rw [inv_pow,Real.sq_sqrt (by positivity),inv_mul_cancel₀ (by positivity)]
  have hc : 0 ≤ c^2 := sq_nonneg _
  let U : Matrix (Fin d) m ℝ := fun j x => c*g x j
  let V : Matrix (Fin d) m ℝ := fun j x => c*g (e₀ x) j
  have hu (j l : Fin d) : (U*U.transpose) j l = c^2*∑ x : m,g x j*g x l := by
    change (∑ x : m,(c*g x j)*(c*g x l)) = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  have hv (j l : Fin d) : (V*V.transpose) j l = c^2*∑ x : n,g x j*g x l := by
    change (∑ x : m,(c*g (e₀ x) j)*(c*g (e₀ x) l)) = _
    rw [← e₀.sum_comp (fun x : n => g x j*g x l),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  refine ⟨m,inferInstance,(fun x => c*v x),(fun x => c*v (e₀ x)),U,V,?_,?_,?_⟩
  · ext j l
    simp only [Matrix.sub_apply,hu,hv,← mul_sub]
    have hm' := sum_counts_difference f M z hz (fun x => g x j*g x l)
    change (∑ x : m,g x j*g x l)-(∑ x : n,g x j*g x l) = _ at hm'
    rw [hm']
    have hm := hmom j l
    simp only [mul_assoc] at hm
    rw [hm]
    calc c^2*((M:ℝ)*(ζ*(if j=l then 1 else 0))) =
        (c^2*((M:ℝ)*ζ))*(if j=l then 1 else 0) := by ring
      _ = _ := by simp [hsq,Matrix.one_apply]
  · have ht : (V*V.transpose).trace = c^2*(M:ℝ)*
        f.sum (fun x q => max (-(q:ℝ)) 0*(∑ j,(g x j)^2)) := by
      change (∑ j,(V*V.transpose) j j) = _
      simp only [hv,← Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [← pow_two]
      have hn' := sum_counts_negative f M z hz (fun x => ∑ j,(g x j)^2)
      change (∑ x : n,∑ j,(g x j)^2) = _ at hn'
      rw [hn']
      ring
    rw [ht]
    have hc' : 0 < c^2*(M:ℝ) := by
      have hc0 : c ≠ 0 := by dsimp [c]; positivity
      exact mul_pos (sq_pos_of_ne_zero hc0) hMp
    calc c^2*(M:ℝ)*_ < c^2*(M:ℝ)*(η*ζ) := mul_lt_mul_of_pos_left hneg hc'
      _ = (c^2*((M:ℝ)*ζ))*η := by ring
      _ = η := by rw [hsq,one_mul]
  · intro i
    refine ⟨(e i).trans e₀.symm,?_⟩
    intro x
    have he' := congrArg (fun r : ℝ => c*r) (he i x)
    simpa [U,V,Equiv.trans_apply,e₀,Finset.mul_sum,mul_add,mul_assoc,mul_comm,mul_left_comm] using he'
end EuclideanRamsey

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators
open Matrix


theorem solution : type_of% @_root_.OAI.EuclideanRamsey.normalized_signed_rows := @_root_.OAI.EuclideanRamsey.normalized_signed_rows
