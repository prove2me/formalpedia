-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CongIndex.chainT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:13:54.061308+00:00
-- url     : https://prove2.me/submissions/3d1c9a96-4f56-4859-a653-355b0e8efced

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ValZpowIff
import Theorems.Thm_GlobalTheory_CompanionTheory_CongIndex_chainS

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
    (hb0 : ∀ i, b i i = 0)
    (H : Subgroup (GL (Fin N) k)) (hH : (H : Set (GL (Fin N) k)) = Kset ϖ (fun _ _ => m)) (t : ℕ) :
    ∃ G : Subgroup (GL (Fin N) k),
      (G : Set (GL (Fin N) k)) = Kset ϖ (fun i j => m + min (b i j) t) ∧ G ≤ H ∧
      G.relIndex H = Nat.card (IsLocalRing.ResidueField (valuation k).integer) ^
        (∑ i, ∑ j, min (b i j) t) := by
  classical
  induction t with
  | zero => exact ⟨H, by simpa using hH, le_rfl, by simp⟩
  | succ t ih =>
    obtain ⟨G₁, hG₁, hle, hidx⟩ := ih
    obtain ⟨G₂, hG₂, hle₂, hidx₂⟩ := chainS h0 h1 hu hm (b := fun i j => min (b i j) t)
      (fun i j l => by have := hb i j l; omega) G₁ hG₁
      (Finset.univ.filter fun p => t < b p.1 p.2)
      (fun p hp he => by
        have := (Finset.mem_filter.1 hp).2
        rw [he, hb0] at this
        omega)
    refine ⟨G₂, ?_, hle₂.trans hle, ?_⟩
    · rw [hG₂]
      congr 1
      funext i j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs <;> omega
    · rw [← Subgroup.relIndex_mul_relIndex G₂ G₁ H hle₂ hle, hidx₂, hidx, ← pow_add]
      congr 1
      rw [Finset.card_filter, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only
      split_ifs <;> omega
end GlobalTheory.CompanionTheory.CongIndex
