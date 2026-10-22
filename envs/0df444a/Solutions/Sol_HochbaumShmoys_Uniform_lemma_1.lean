-- Prove2me | solution 1 for HochbaumShmoys.Uniform.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:36:30.237997+00:00
-- url     : https://prove2.me/submissions/108bc0bb-0b6d-49db-a8c6-c99249079229

import Mathlib
import Definitions.Def_HochbaumShmoys_Uniform_LayeredGraph
open HochbaumShmoys.Uniform

def g69g_nodeEnc {m N n : ℕ} : Node m N n → Option (Bool × Fin m × StateVector N n)
  | .pre t u => some (true, t, u)
  | .fin t u => some (false, t, u)
  | .success => none

theorem g69g_nodeEnc_inj {m N n : ℕ} : Function.Injective (@g69g_nodeEnc m N n) := by
  intro a b h
  cases a <;> cases b <;> simp_all [g69g_nodeEnc]

def g69g_svEnc {N n : ℕ} (s : StateVector N n) :
    (Fin (numClasses N) → Fin (n + 1)) × (Fin (numClasses N) → Fin (n + 1)) ×
      Fin (slackCap N n + 1) × Fin (slackCap N n + 1) × Fin (slackCap N n + 1) :=
  (s.L, s.M, s.V₁, s.V₂, s.V)

theorem g69g_svEnc_inj {N n : ℕ} : Function.Injective (@g69g_svEnc N n) := by
  intro a b h
  cases a; cases b; simp_all [g69g_svEnc]

theorem g69g_card_node (m N n : ℕ) :
    Fintype.card (Node m N n) ≤ 2 * m * ((n + 1) ^ (2 * numClasses N) *
      (slackCap N n + 1) ^ 3) + 1 := by
  have h1 := Fintype.card_le_of_injective _ (@g69g_nodeEnc_inj m N n)
  have h2 := Fintype.card_le_of_injective _ (@g69g_svEnc_inj N n)
  simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin,
    Fintype.card_fun] at h1 h2
  calc Fintype.card (Node m N n) ≤ 2 * (m * Fintype.card (StateVector N n)) + 1 := h1
    _ ≤ 2 * (m * ((n + 1) ^ numClasses N * ((n + 1) ^ numClasses N *
        ((slackCap N n + 1) * ((slackCap N n + 1) * (slackCap N n + 1)))))) + 1 := by
        gcongr
    _ = _ := by ring

theorem solution : ∃ C : ℕ, ∀ (N : ℕ), 2 ≤ N → ∀ (m n : ℕ) (hm : 0 < m)
    (β : Fin m → ℝ) (π : Fin n → ℝ),
    Antitone β → β ⟨0, hm⟩ = 1 → (∀ t, 0 < β t) → (∀ j, 0 < π j ∧ π j ≤ 1) →
    nodeCount N β π ≤ C * (2 * m) * (n + 1) ^ (2 * N ^ 2 + 3) * N ^ 6 := by
  refine ⟨9, fun N hN m n hm β π _ _ _ _ => ?_⟩
  have hc : nodeCount N β π ≤ Fintype.card (Node m N n) := by
    unfold nodeCount
    exact (Finite.card_subtype_le _).trans Nat.card_eq_fintype_card.le
  refine hc.trans ((g69g_card_node m N n).trans ?_)
  have hK : 2 * numClasses N ≤ 2 * N ^ 2 := by
    unfold numClasses
    have : N ≤ N ^ 2 := by nlinarith
    omega
  have hN1 : 1 ≤ N ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hS : slackCap N n + 1 ≤ 2 * (n + 1) * N ^ 2 := by
    unfold slackCap; nlinarith
  have hp1 : (n + 1) ^ (2 * numClasses N) ≤ (n + 1) ^ (2 * N ^ 2) :=
    Nat.pow_le_pow_right (by omega) hK
  have hp2 : (slackCap N n + 1) ^ 3 ≤ (2 * (n + 1) * N ^ 2) ^ 3 := Nat.pow_le_pow_left hS 3
  have hpos : 1 ≤ (n + 1) ^ (2 * N ^ 2 + 3) * N ^ 6 :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  calc 2 * m * ((n + 1) ^ (2 * numClasses N) * (slackCap N n + 1) ^ 3) + 1
      ≤ 2 * m * ((n + 1) ^ (2 * N ^ 2) * (2 * (n + 1) * N ^ 2) ^ 3) + 1 := by gcongr
    _ = 16 * m * ((n + 1) ^ (2 * N ^ 2 + 3) * N ^ 6) + 1 := by ring
    _ ≤ 9 * (2 * m) * (n + 1) ^ (2 * N ^ 2 + 3) * N ^ 6 := by
        have : 1 ≤ m * ((n + 1) ^ (2 * N ^ 2 + 3) * N ^ 6) := Nat.one_le_iff_ne_zero.mpr (by positivity)
        nlinarith
