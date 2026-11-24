-- Prove2me | solution 1 for GlobalTheory.BrauerZero.ind_ind_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:03:40.394376+00:00
-- url     : https://prove2.me/submissions/cee3eb19-ef7b-4227-862d-169a13f8fb60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IndApplyOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InducedClassFunctionFromSubgroupTrans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI GlobalTheory.BrauerZero
open GlobalTheory GlobalTheory.BrauerZero
namespace GlobalTheory.BrauerZero
theorem _root_.solution {G : Type} [Group G] [Finite G] (K A : Subgroup G) (hKA : K ≤ A)
    (ψ : K → ℂ) :
    ind A (ind (K.subgroupOf A) (fun k => ψ ⟨((k : A) : G), k.2⟩)) = ind K ψ := by
  classical
  haveI := Fintype.ofFinite G
  funext g
  have hcard : Nat.card (K.subgroupOf A) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKA).toEquiv
  have key : ∀ a y : A, ext0 (K.subgroupOf A) (fun k => ψ ⟨((k : A) : G), k.2⟩) (y⁻¹ * a * y)
      = ext0 K ψ ((y : G)⁻¹ * (a : G) * y) := by
    intro a y
    have hc : ((y⁻¹ * a * y : A) : G) = (y : G)⁻¹ * (a : G) * y := by simp
    by_cases h : (y : G)⁻¹ * (a : G) * y ∈ K
    · have h' : y⁻¹ * a * y ∈ K.subgroupOf A := by rw [Subgroup.mem_subgroupOf, hc]; exact h
      rw [ext0, ext0, dif_pos h', dif_pos h]
      congr 1
    · have h' : y⁻¹ * a * y ∉ K.subgroupOf A := by rw [Subgroup.mem_subgroupOf, hc]; exact h
      rw [ext0, ext0, dif_neg h', dif_neg h]
  have step : ∀ x : G, ext0 A (ind (K.subgroupOf A) (fun k => ψ ⟨((k : A) : G), k.2⟩)) (x⁻¹ * g * x)
      = (Nat.card K : ℂ)⁻¹ * ∑ y : A, ext0 K ψ ((x * y)⁻¹ * g * (x * y)) := by
    intro x
    by_cases hx : x⁻¹ * g * x ∈ A
    · rw [ext0, dif_pos hx, ind, hcard, finsum_eq_sum_of_fintype]
      congr 1
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [key ⟨_, hx⟩ y]
      congr 1
      simp only [mul_inv_rev]
      group
    · rw [ext0, dif_neg hx]
      symm
      refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun y _ => ?_)
      have hn : (x * y)⁻¹ * g * (x * y) ∉ K := by
        intro hk
        apply hx
        have hA : (x * y)⁻¹ * g * (x * y) ∈ A := hKA hk
        have e : x⁻¹ * g * x = (y : G) * ((x * y)⁻¹ * g * (x * y)) * (y : G)⁻¹ := by group
        rw [e]
        exact A.mul_mem (A.mul_mem y.2 hA) (A.inv_mem y.2)
      rw [ext0, dif_neg hn]
  rw [ind, ind, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    Finset.sum_congr rfl (fun x _ => step x), ← Finset.mul_sum, Finset.sum_comm]
  have shift : ∀ y : A, ∑ x : G, ext0 K ψ ((x * y)⁻¹ * g * (x * y)) = ∑ z : G, ext0 K ψ (z⁻¹ * g * z) :=
    fun y => Fintype.sum_equiv (Equiv.mulRight (y : G)) _ _ (fun x => rfl)
  rw [Finset.sum_congr rfl (fun y _ => shift y), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card]
  have hA0 : (Nat.card A : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := A)).ne'
  field_simp
end GlobalTheory.BrauerZero
