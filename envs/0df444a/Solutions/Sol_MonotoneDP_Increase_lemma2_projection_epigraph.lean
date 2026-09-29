-- Prove2me | solution 1 for MonotoneDP.Increase.lemma2_projection_epigraph
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:53:49.579324+00:00
-- url     : https://prove2.me/submissions/fd407f2a-b95d-49fa-aefd-6674acc8eece

import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model
import Definitions.Def_MonotoneDP_Increase_Assumptions
import Definitions.Def_MonotoneDP_Increase_Epigraph

namespace MonotoneDP.Increase

open Filter Topology

/-- Unfolding `T^[k]` for `k ≥ 1`. -/
theorem aux_l2p_iter {S C : Type*} (m : Model S C) (k : ℕ) (hk : 1 ≤ k) (x : S) :
    (m.T)^[k] m.Jbar x = ⨅ v ∈ m.U x, m.H x v ((m.T)^[k - 1] m.Jbar) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Function.iterate_succ_apply']
  simp [Model.T]

/-- Pointwise: the closure-in-λ of the projection equals the epigraph of the infimum. -/
theorem aux_l2p_pbar_pt {C : Type*} (U : Set C) (h : C → EReal) (l : ℝ) :
    (∃ lam : ℕ → ℝ, Tendsto lam atTop (𝓝 l) ∧ ∀ n, ∃ u ∈ U, h u ≤ (lam n : EReal)) ↔
      (⨅ v ∈ U, h v) ≤ (l : EReal) := by
  constructor
  · rintro ⟨lam, hlam, hmem⟩
    have h1 : ∀ n, (⨅ v ∈ U, h v) ≤ ((lam n : ℝ) : EReal) := by
      intro n
      obtain ⟨u, hu, hle⟩ := hmem n
      exact le_trans (iInf₂_le u hu) hle
    have h2 : Tendsto (fun n => ((lam n : ℝ) : EReal)) atTop (𝓝 (l : EReal)) :=
      (continuous_coe_real_ereal.tendsto l).comp hlam
    exact ge_of_tendsto' h2 h1
  · intro hle
    refine ⟨fun n => l + 1 / ((n : ℝ) + 1), ?_, ?_⟩
    · have := (tendsto_const_nhds (x := l)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa using this
    · intro n
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have hlt : (⨅ v ∈ U, h v) < ((l + 1 / ((n : ℝ) + 1) : ℝ) : EReal) := by
        refine lt_of_le_of_lt hle ?_
        exact EReal.coe_lt_coe_iff.mpr (by linarith)
      obtain ⟨u, hu⟩ := iInf_lt_iff.mp hlt
      obtain ⟨hU, hu2⟩ := iInf_lt_iff.mp hu
      exact ⟨u, hU, hu2.le⟩

theorem aux_l2p_pbar_eq {S C : Type*} (m : Model S C) (k : ℕ) (hk : 1 ≤ k) :
    Pbar (m.P (m.Ck k)) = E ((m.T)^[k] m.Jbar) := by
  ext ⟨x, l⟩
  simp only [Pbar, E, Model.P, Model.Ck, Set.mem_ofPred_eq]
  rw [aux_l2p_iter m k hk x]
  have := aux_l2p_pbar_pt (m.U x) (fun u => m.H x u ((m.T)^[k - 1] m.Jbar)) l
  rw [← this]
  constructor
  · rintro ⟨lam, hlam, hmem⟩
    exact ⟨lam, hlam, fun n => by
      obtain ⟨u, hu, _, h2⟩ := hmem n
      exact ⟨u, hu, h2⟩⟩
  · rintro ⟨lam, hlam, hmem⟩
    exact ⟨lam, hlam, fun n => by
      obtain ⟨u, hu, h2⟩ := hmem n
      exact ⟨u, hu, hu, h2⟩⟩

/-- Under Assumption I, `J̄ ≤ T^k(J̄)`. -/
theorem aux_l2p_ge {S C : Type*} (m : Model S C) (hI : m.AssumptionI) :
    ∀ k : ℕ, m.Jbar ≤ (m.T)^[k] m.Jbar := by
  intro k
  induction k with
  | zero => exact le_rfl
  | succ j ih =>
    intro x
    rw [Function.iterate_succ_apply']
    simp only [Model.T]
    refine le_iInf₂ fun u hu => ?_
    exact le_trans (hI x u hu) (m.mono x u hu _ _ ih)

end MonotoneDP.Increase

open MonotoneDP.Increase

theorem solution {S C : Type*} (m : Model S C) (hI : m.AssumptionI) :
    ∀ k : ℕ, 1 ≤ k →
      (m.P (m.Ck k) ⊆ Pbar (m.P (m.Ck k)) ∧
        Pbar (m.P (m.Ck k)) = E ((m.T)^[k] m.Jbar)) ∧
      ((m.P (m.Ck k) = Pbar (m.P (m.Ck k)) ∧
          Pbar (m.P (m.Ck k)) = E ((m.T)^[k] m.Jbar)) ↔
        ∀ x : S, ∃ u ∈ m.U x,
          m.H x u ((m.T)^[k - 1] m.Jbar) =
            ⨅ v ∈ m.U x, m.H x v ((m.T)^[k - 1] m.Jbar)) := by
  intro k hk
  have hPE := aux_l2p_pbar_eq m k hk
  have hsub : m.P (m.Ck k) ⊆ Pbar (m.P (m.Ck k)) := by
    rintro ⟨x, l⟩ hp
    exact ⟨fun _ => l, tendsto_const_nhds, fun _ => hp⟩
  refine ⟨⟨hsub, hPE⟩, ?_⟩
  rw [hPE]
  constructor
  · rintro ⟨hPeq, -⟩ x
    set t : EReal := ⨅ v ∈ m.U x, m.H x v ((m.T)^[k - 1] m.Jbar) with ht
    have htk : (m.T)^[k] m.Jbar x = t := aux_l2p_iter m k hk x
    suffices hex : ∃ u ∈ m.U x, m.H x u ((m.T)^[k - 1] m.Jbar) ≤ t by
      obtain ⟨u, hu, hle⟩ := hex
      exact ⟨u, hu, le_antisymm hle (iInf₂_le u hu)⟩
    by_cases htop : t = ⊤
    · obtain ⟨u, hu⟩ := m.U_nonempty x
      exact ⟨u, hu, by rw [htop]; exact le_top⟩
    · have hbot : t ≠ ⊥ := by
        intro hb
        have h1 := aux_l2p_ge m hI k x
        rw [htk, hb, le_bot_iff] at h1
        exact m.Jbar_ne_bot x h1
      have hcoe : ((t.toReal : ℝ) : EReal) = t := EReal.coe_toReal htop hbot
      have hmemE : (x, t.toReal) ∈ E ((m.T)^[k] m.Jbar) := by
        simp only [E, Set.mem_ofPred_eq]
        rw [htk, hcoe]
      rw [← hPeq] at hmemE
      obtain ⟨u, hu, hC⟩ := hmemE
      refine ⟨u, hu, ?_⟩
      have := hC.2
      simp only at this
      rwa [hcoe] at this
  · intro hatt
    refine ⟨?_, rfl⟩
    apply Set.Subset.antisymm
    · rw [← hPE]; exact hsub
    · rintro ⟨x, l⟩ hp
      simp only [E, Set.mem_ofPred_eq] at hp
      rw [aux_l2p_iter m k hk x] at hp
      obtain ⟨u, hu, heq⟩ := hatt x
      refine ⟨u, hu, hu, ?_⟩
      simp only
      rw [heq]
      exact hp
