-- Prove2me | solution 1 for GlobalTheory.PairOp.isAdj_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:37:42.561228+00:00
-- url     : https://prove2.me/submissions/5eabbdc2-61e1-4319-8641-7476daa1ce24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointOperatorIdentities
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Theorems.Thm_GlobalTheory_PairOp_cntIp_smul_right
import Theorems.Thm_GlobalTheory_PairOp_cntIp_smul_left
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
noncomputable section
namespace GlobalTheory.PairOp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
  {M : Type} [AddCommGroup M] [Module ℂ M]
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ)
variable {χ}
section Adjoint
variable {A B A' B' : Module.End ℂ (Form k n ℂ)}
private theorem cntIp_eq_sum_of_support_subset (φ φ' : Form k n ℂ) (s : Finset (Pair k n))
    (hs : Function.support φ' ⊆ s ∨ Function.support φ ⊆ s) :
    cntIp φ φ' = ∑ P ∈ s, φ P * (starRingEnd ℂ) (φ' P) := by
  unfold cntIp
  refine finsum_eq_sum_of_support_subset _ fun P hP => ?_
  rw [Function.mem_support] at hP
  rcases hs with hs | hs
  · exact hs (Function.mem_support.mpr fun h0 => hP (by rw [h0]; simp))
  · exact hs (Function.mem_support.mpr fun h0 => hP (by rw [h0]; simp))
private theorem cntIp_add_left (φ₁ φ₂ φ' : Form k n ℂ) (h : (Function.support φ').Finite) :
    cntIp (φ₁ + φ₂) φ' = cntIp φ₁ φ' + cntIp φ₂ φ' := by
  rw [cntIp_eq_sum_of_support_subset _ _ h.toFinset (Or.inl (by simp)), cntIp_eq_sum_of_support_subset _ _ h.toFinset (Or.inl (by simp)),
    cntIp_eq_sum_of_support_subset _ _ h.toFinset (Or.inl (by simp)), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun P _ => by rw [Pi.add_apply, add_mul]
private theorem cntIp_add_right (φ φ₁ φ₂ : Form k n ℂ) (h : (Function.support φ).Finite) :
    cntIp φ (φ₁ + φ₂) = cntIp φ φ₁ + cntIp φ φ₂ := by
  rw [cntIp_eq_sum_of_support_subset _ _ h.toFinset (Or.inr (by simp)), cntIp_eq_sum_of_support_subset _ _ h.toFinset (Or.inr (by simp)),
    cntIp_eq_sum_of_support_subset _ _ h.toFinset (Or.inr (by simp)), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun P _ => by rw [Pi.add_apply, map_add, mul_add]
end Adjoint
end GlobalTheory.PairOp
end
end

set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
noncomputable section
open GlobalTheory GlobalTheory.PairOp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
  {M : Type} [AddCommGroup M] [Module ℂ M]
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ)
variable {χ}
variable {A B A' B' : Module.End ℂ (Form k n ℂ)}
namespace GlobalTheory.PairOp
theorem _root_.solution {ι : Type} (s : Finset ι) (a b : ι → ℂ) (A B : ι → Module.End ℂ (Form k n ℂ))
    (hab : ∀ i, (starRingEnd ℂ) (b i) = a i) (h : ∀ i, IsAdj (A i) (B i)) :
    IsAdj (∑ i ∈ s, a i • A i) (∑ i ∈ s, b i • B i) := by
  classical
  intro φ φ' hφ hφ'
  induction s using Finset.induction_on with
  | empty => simp [cntIp]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, LinearMap.add_apply, LinearMap.add_apply,
      cntIp_add_left _ _ _ hφ', cntIp_add_right _ _ _ hφ, ih, LinearMap.smul_apply, LinearMap.smul_apply,
      cntIp_smul_left, cntIp_smul_right, h j φ φ' hφ hφ', hab j]
end GlobalTheory.PairOp
