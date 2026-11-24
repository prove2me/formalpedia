-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LatticePoint.exists_compact_open_addSubgroup_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:05:10.083663+00:00
-- url     : https://prove2.me/submissions/9574d7aa-f5b4-4b7f-a6b7-64d9c0776403

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCompactOpenSubgroupMem
import Theorems.Thm_GlobalTheory_CompanionTheory_LatticePoint_isOpen_valBall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LatticePoint
namespace GlobalTheory.CompanionTheory.LatticePoint
theorem _root_.solution :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (n : ℕ) (x : Fin n → k),
      ∃ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) ∧
        IsOpen (A : Set (Fin n → k)) ∧ x ∈ A := by
  intro k _ _ _ _ n x
  let γ : ValueGroupWithZero k := Finset.univ.sup (fun i => valuation k (x i)) ⊔ 1
  have hγ : γ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one le_sup_right)
  let S : AddSubgroup k :=
    { carrier := {y | valuation k y ≤ γ}
      add_mem' := fun {a b} ha hb => by
        change valuation k a ≤ γ at ha
        change valuation k b ≤ γ at hb
        show valuation k (a + b) ≤ γ
        exact (Valuation.map_add _ _ _).trans (max_le ha hb)
      zero_mem' := by
        show valuation k 0 ≤ γ
        simp
      neg_mem' := fun {a} ha => by
        change valuation k a ≤ γ at ha
        show valuation k (-a) ≤ γ
        rwa [Valuation.map_neg] }
  have hS : (S : Set k) = {y | valuation k y ≤ γ} := rfl
  refine ⟨AddSubgroup.pi Set.univ (fun _ => S), ?_, ?_, ?_⟩
  · rw [AddSubgroup.coe_pi, hS]
    exact isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k γ
  · rw [AddSubgroup.coe_pi, hS]
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_valBall γ hγ
  · rw [AddSubgroup.mem_pi]
    intro i _
    show valuation k (x i) ≤ γ
    exact le_sup_of_le_left (Finset.le_sup (f := fun i => valuation k (x i)) (Finset.mem_univ i))
end GlobalTheory.CompanionTheory.LatticePoint
