-- Prove2me | solution 1 for GlobalTheory.SympTower.rank_le_of_smul_sub_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:02:40.258523+00:00
-- url     : https://prove2.me/submissions/221d3fbe-754c-43fc-bed5-044f78e796ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompatibleSymplectic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.SympTower
namespace GlobalTheory.SympTower
theorem _root_.solution {R : Type} [CommRing R] [Finite R] {r : ℕ} {ι : Type}
    [Fintype ι] (φ : (ι → R) →ₗ[R] (Fin r → R)) (ψ : (Fin r → R) →ₗ[R] (ι → R)) (c : R)
    (hc : c ≠ 0) (h : ∀ x, c • (x - φ (ψ x)) = 0) : r ≤ Fintype.card ι := by
  classical
  let S := {y : R // ∃ z, y = c * z}
  haveI : Fintype S := Fintype.ofFinite _
  haveI : Nontrivial S := ⟨⟨⟨c, 1, by simp⟩, ⟨0, 0, by simp⟩, fun h => hc (congrArg Subtype.val h)⟩⟩
  have key : ∀ s : Fin r → S, ∃ x : Fin r → R, (fun i => (s i).1) = c • x := by
    intro s
    choose z hz using fun i => (s i).2
    exact ⟨z, funext fun i => by simpa using hz i⟩
  let f : (Fin r → S) → (ι → S) := fun s j => ⟨ψ (fun i => (s i).1) j, by
    obtain ⟨x, hx⟩ := key s
    exact ⟨ψ x j, by rw [hx]; simp⟩⟩
  have hφ : ∀ s : Fin r → S, φ (ψ (fun i => (s i).1)) = fun i => (s i).1 := by
    intro s
    obtain ⟨x, hx⟩ := key s
    have := h x
    rw [smul_sub, sub_eq_zero] at this
    rw [hx, map_smul, map_smul, ← this]
  have hf : Function.Injective f := by
    intro s t hst
    have h1 : ψ (fun i => (s i).1) = ψ (fun i => (t i).1) :=
      funext fun j => congrArg Subtype.val (congrFun hst j)
    have h2 := hφ s
    rw [h1, hφ t] at h2
    exact funext fun i => Subtype.ext (congrFun h2 i).symm
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fun, Fintype.card_fin] at hcard
  exact (Nat.pow_le_pow_iff_right Fintype.one_lt_card).1 hcard
end GlobalTheory.SympTower
