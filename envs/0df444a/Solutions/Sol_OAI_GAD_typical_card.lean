-- Prove2me | solution 1 for OAI.GAD.typical_card
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:48:30.42829+00:00
-- url     : https://prove2.me/submissions/2e86a049-36dc-40c2-8c9c-bd7583d983ee

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/TypicalSets.lean:L154-L174
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.typical_card. The node keeps its source
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

end GAD

end

open scoped BigOperators
namespace GAD
variable {α : Type u_2} [Fintype α]
attribute [local instance] OAI.GAD.instDecidablePred_oAI
theorem iid_log (q : α → ℝ) (n : ℕ) (x : Fin n → α) (hx : 0 < iidWeight q n x) :
    iidSum (centeredLog q) n x = -Real.log (iidWeight q n x)-(n:ℝ)*classicalEntropy q := by
  have hn : ∀ j ∈ Finset.univ, q (x j) ≠ 0 := (Finset.prod_ne_zero_iff.mp hx.ne')
  simp only [iidSum,centeredLog,Finset.sum_sub_distrib,Finset.sum_neg_distrib,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [iidWeight,Real.log_prod hn]

theorem typical_weight_lower (q : α → ℝ) (δ : ℝ) (n : ℕ) (x : Fin n → α)
    (hx : IsTypical q δ n x) : Real.exp (-(n:ℝ)*(classicalEntropy q+δ)) ≤ iidWeight q n x := by
  rw [← Real.exp_log hx.1]
  apply Real.exp_le_exp.mpr
  have h := (abs_le.mp hx.2).2
  rw [iid_log q n x hx.1] at h
  nlinarith

theorem typical_card (q : α → ℝ) (hq : ∀ a, 0 ≤ q a) (hs : ∑ a, q a=1)
    (δ : ℝ) (n : ℕ) :
    ((typicalSet q δ n).card : ℝ) ≤ Real.exp ((n:ℝ)*(classicalEntropy q+δ)) := by
  let c := Real.exp (-(n:ℝ)*(classicalEntropy q+δ))
  have hc : 0 < c := Real.exp_pos _
  have hsum : ((typicalSet q δ n).card : ℝ)*c ≤ 1 := by
    calc
      _ = ∑ x ∈ typicalSet q δ n, c := by rw [Finset.sum_const,nsmul_eq_mul]
      _ ≤ ∑ x ∈ typicalSet q δ n, iidWeight q n x := by
        apply Finset.sum_le_sum
        intro x hx
        exact typical_weight_lower q δ n x (Finset.mem_filter.mp hx).2
      _ ≤ ∑ x : Fin n → α, iidWeight q n x := Finset.sum_le_univ_sum_of_nonneg
        (fun x ↦ iidWeight_nonneg q hq n x)
      _ = 1 := iidWeight_total q hs n
  have h := mul_le_mul_of_nonneg_right hsum (Real.exp_pos ((n:ℝ)*(classicalEntropy q+δ))).le
  have hexp : c*Real.exp ((n:ℝ)*(classicalEntropy q+δ))=1 := by
    dsimp [c]
    rw [← Real.exp_add]
    simp only [neg_mul, neg_add_cancel, Real.exp_zero]
  rwa [mul_assoc,hexp,mul_one,one_mul] at h

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators
attribute [local instance] OAI.GAD.instDecidablePred_oAI


theorem solution : type_of% @_root_.OAI.GAD.typical_card := @_root_.OAI.GAD.typical_card
