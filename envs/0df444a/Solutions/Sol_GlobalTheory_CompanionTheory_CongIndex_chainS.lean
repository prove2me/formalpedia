-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CongIndex.chainS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:56:35.635577+00:00
-- url     : https://prove2.me/submissions/83ae661d-73bc-4eaf-81ae-857acad134e7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ValZpowIff
import Theorems.Thm_GlobalTheory_CompanionTheory_CongIndex_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CongIndex
open ValuativeRel
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {N : ℕ}
namespace GlobalTheory.CompanionTheory.CongIndex
theorem _root_.solution {ϖ : k} (h0 : ϖ ≠ 0) (h1 : valuation k ϖ < 1)
    (hu : ∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ)
    {m : ℕ} (hm : 1 ≤ m) {b : Fin N → Fin N → ℕ} (hb : ∀ i j l, b i j ≤ b i l + b l j)
    (G : Subgroup (GL (Fin N) k)) (hG : (G : Set (GL (Fin N) k)) = Kset ϖ (fun i j => m + b i j))
    (S : Finset (Fin N × Fin N)) (hS : ∀ p ∈ S, p.1 ≠ p.2) :
    ∃ G' : Subgroup (GL (Fin N) k),
      (G' : Set (GL (Fin N) k)) = Kset ϖ (fun i j => m + b i j + if (i, j) ∈ S then 1 else 0) ∧
      G' ≤ G ∧
      G'.relIndex G = Nat.card (IsLocalRing.ResidueField (valuation k).integer) ^ S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨G, by simpa using hG, le_rfl, by simp⟩
  | insert p S hp ih =>
    obtain ⟨G₁, hG₁, hle, hidx⟩ := ih fun q hq => hS q (Finset.mem_insert_of_mem hq)
    obtain ⟨G₂, hG₂, hle₂, hidx₂⟩ := step (c := fun i j => m + b i j + if (i, j) ∈ S then 1 else 0)
      (c' := fun i j => m + b i j + if (i, j) ∈ insert p S then 1 else 0) h0 h1 hu
      (i := p.1) (j := p.2) (hS _ (Finset.mem_insert_self _ _))
      (fun l => by
        have := hb p.1 p.2 l
        simp only [Prod.mk.eta, hp, if_false]
        split_ifs <;> omega)
      (by simp [hp])
      (fun a c hac => by
        have hne : (a, c) ≠ p := fun h => hac (by simp [← h])
        simp [Finset.mem_insert, hne])
      G₁ hG₁
    refine ⟨G₂, hG₂, hle₂.trans hle, ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex G₂ G₁ G hle₂ hle, hidx₂, hidx, Finset.card_insert_of_notMem hp,
      pow_succ, mul_comm]
end GlobalTheory.CompanionTheory.CongIndex
