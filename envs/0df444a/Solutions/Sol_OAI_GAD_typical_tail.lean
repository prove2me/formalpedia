-- Prove2me | solution 1 for OAI.GAD.typical_tail
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:46:43.193295+00:00
-- url     : https://prove2.me/submissions/bad4dda1-cdad-4017-ae6f-f92625e8d0fc

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/TypicalSets.lean:L133-L149
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.typical_tail. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Pinching
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_GramMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ScalarDeficit
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ThermalEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TensorEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PureRecursion
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_StateEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_EntropyContinuity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_BlockFactors
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Naimark
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_HolevoInformation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_EnsembleBounds
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PhaseStates
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PhaseProducts
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_CapacityConverse
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_SequentialMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TypicalSets

-- ---- from OAI.InformationTheory.AmplitudeDamping.TypicalSets ----
namespace OAI

noncomputable section

universe u_1 u_2

section
open scoped BigOperators
namespace GAD
variable {α : Type u_1} [Fintype α]

omit [Fintype α] in
theorem iidWeight_nonneg (q : α → ℝ) (hq : ∀ a, 0 ≤ q a) (n : ℕ) (x : Fin n → α) :
    0 ≤ iidWeight q n x := Finset.prod_nonneg (fun j _ ↦ hq (x j))

theorem iidWeight_total (q : α → ℝ) (hs : ∑ a, q a=1) (n : ℕ) :
    (∑ x : Fin n → α, iidWeight q n x)=1 := by
  rw [show (∑ x : Fin n → α, iidWeight q n x) = ∏ j : Fin n, ∑ a, q a from
    (Fintype.prod_sum (fun _ : Fin n ↦ q)).symm]
  simp only [hs,Finset.prod_const_one]

theorem iid_split_sum (q : α → ℝ) (n : ℕ) (f : (Fin (n+1) → α) → ℝ) :
    (∑ x, iidWeight q (n+1) x*f x) =
      ∑ a, ∑ x : Fin n → α, q a*iidWeight q n x*f (Fin.cons a x) := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) ↦ α))
    (fun x ↦ iidWeight q (n+1) x*f x)]
  simp only [Fintype.sum_prod_type,Fin.consEquiv_apply,iidWeight,Fin.prod_univ_succ,
    Fin.cons_zero,Fin.cons_succ]
  rfl

omit [Fintype α] in
theorem iidSum_cons (f : α → ℝ) (n : ℕ) (a : α) (x : Fin n → α) :
    iidSum f (n+1) (Fin.cons a x)=f a+iidSum f n x := by
  simp only [iidSum,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]

theorem iid_centered_mean (q f : α → ℝ) (hs : ∑ a, q a=1)
    (hf : ∑ a, q a*f a=0) (n : ℕ) :
    (∑ x : Fin n → α, iidWeight q n x*iidSum f n x)=0 := by
  induction n with
  | zero => simp [iidSum]
  | succ n ih =>
      rw [iid_split_sum]
      have he (a : α) : (∑ x : Fin n → α, q a*iidWeight q n x*iidSum f (n+1) (Fin.cons a x)) = q a*f a := by
        simp only [iidSum_cons]
        have hpoly (x : Fin n → α) : q a*iidWeight q n x*(f a+iidSum f n x) =
            (q a*f a)*iidWeight q n x+q a*(iidWeight q n x*iidSum f n x) := by ring
        simp only [hpoly,Finset.sum_add_distrib,← Finset.mul_sum,iidWeight_total q hs n,
          ih,mul_one,mul_zero,add_zero]
      simpa only [he] using hf

theorem iid_centered_second (q f : α → ℝ) (hs : ∑ a, q a=1)
    (hf : ∑ a, q a*f a=0) (n : ℕ) :
    (∑ x : Fin n → α, iidWeight q n x*(iidSum f n x)^2)=
      (n:ℝ)*(∑ a, q a*(f a)^2) := by
  induction n with
  | zero => simp [iidSum]
  | succ n ih =>
      rw [iid_split_sum]
      simp only [iidSum_cons]
      have he (a : α) : (∑ x : Fin n → α, q a*iidWeight q n x*(f a+iidSum f n x)^2) =
          q a*(f a)^2+q a*((n:ℝ)*∑ b, q b*(f b)^2) := by
        have hpoly (x : Fin n → α) : q a*iidWeight q n x*(f a+iidSum f n x)^2 =
            (q a*(f a)^2)*iidWeight q n x+(2*q a*f a)*(iidWeight q n x*iidSum f n x)+
              q a*(iidWeight q n x*(iidSum f n x)^2) := by ring
        simp only [hpoly,Finset.sum_add_distrib,← Finset.mul_sum,iidWeight_total q hs n,
          iid_centered_mean q f hs hf n,ih,mul_one,mul_zero,add_zero]
      simp only [he,Finset.sum_add_distrib,← Finset.sum_mul,hs,one_mul,Nat.cast_add,Nat.cast_one]
      ring

theorem iid_chebyshev (q f : α → ℝ) (hq : ∀ a, 0 ≤ q a) (hs : ∑ a, q a=1)
    (hf : ∑ a, q a*f a=0) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (∑ x : Fin n → α, if t < |iidSum f n x| then iidWeight q n x else 0) ≤
      (n:ℝ)*(∑ a, q a*(f a)^2)/t^2 := by
  apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
  rw [Finset.sum_mul,← iid_centered_second q f hs hf n]
  apply Finset.sum_le_sum
  intro x _
  split_ifs with hx
  · apply mul_le_mul_of_nonneg_left _ (iidWeight_nonneg q hq n x)
    nlinarith [sq_abs (iidSum f n x)]
  · simp only [zero_mul]
    exact mul_nonneg (iidWeight_nonneg q hq n x) (sq_nonneg _)

end GAD

end

open scoped BigOperators
namespace GAD
variable {α : Type u_2} [Fintype α]
attribute [local instance] OAI.GAD.instDecidablePred_oAI
theorem centeredLog_mean (q : α → ℝ) (hs : ∑ a, q a=1) :
    (∑ a, q a*centeredLog q a)=0 := by
  simp only [centeredLog,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hs,one_mul]
  simp [classicalEntropy,Real.negMulLog,mul_neg]

theorem typical_tail (q : α → ℝ) (hq : ∀ a, 0 ≤ q a) (hs : ∑ a, q a=1)
    {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 0 < n) :
    (∑ x : Fin n → α, if IsTypical q δ n x then 0 else iidWeight q n x) ≤
      logVariance q / ((n:ℝ)*δ^2) := by
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have he (x : Fin n → α) : (if IsTypical q δ n x then 0 else iidWeight q n x) =
      (if (n:ℝ)*δ < |iidSum (centeredLog q) n x| then iidWeight q n x else 0) := by
    by_cases hx : 0 < iidWeight q n x
    · simp only [IsTypical,hx,true_and]
      split_ifs <;> first | rfl | (exfalso; linarith)
    · have hz : iidWeight q n x=0 := le_antisymm (not_lt.mp hx) (iidWeight_nonneg q hq n x)
      simp [hz]
  simp only [he]
  have h := iid_chebyshev q (centeredLog q) hq hs (centeredLog_mean q hs) n (mul_pos hn' hδ)
  convert h using 1
  dsimp only [logVariance]
  field_simp

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators
attribute [local instance] OAI.GAD.instDecidablePred_oAI


theorem solution : type_of% @_root_.OAI.GAD.typical_tail := @_root_.OAI.GAD.typical_tail
