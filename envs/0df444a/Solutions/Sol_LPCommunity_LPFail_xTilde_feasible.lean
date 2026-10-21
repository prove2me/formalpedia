-- Prove2me | solution 1 for LPCommunity.LPFail.xTilde_feasible
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:21:31.601132+00:00
-- url     : https://prove2.me/submissions/9d2bb206-0bcd-40e7-8592-2afc827343ec

import Mathlib
import Definitions.Def_LPCommunity_LPFail_Setting
import Definitions.Def_LPCommunity_LPFail_XTilde

set_option autoImplicit false
open Finset
open scoped Classical ENNReal
open LPCommunity.LPFail

theorem lpf_ediam_ne_top {n : ℕ} (G : SimpleGraph (Fin n)) (hconn : G.Connected) :
    G.ediam ≠ ⊤ := by
  have : Nonempty (Fin n × Fin n) := ⟨(hconn.nonempty.some, hconn.nonempty.some)⟩
  obtain ⟨p, hp⟩ := Finite.exists_max (fun p : Fin n × Fin n => G.edist p.1 p.2)
  have h1 : G.ediam ≤ G.edist p.1 p.2 :=
    SimpleGraph.ediam_le_of_edist_le fun u v => hp (u, v)
  have h2 : G.edist p.1 p.2 ≠ ⊤ := SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected _ _)
  exact ne_top_of_le_ne_top h2 h1

theorem lpf_rho_toReal {n : ℕ} (G : SimpleGraph (Fin n)) (hconn : G.Connected) (i j : Fin n) :
    ((rho G i j : ℕ∞) : ℝ≥0∞).toReal = (G.dist i j : ℝ) := by
  have h : (G.dist i j : ℕ∞) = G.edist i j := (hconn.preconnected i j).coe_dist_eq_edist
  unfold rho
  rw [← h]
  simp

theorem lpf_dist_le_max {n : ℕ} (G : SimpleGraph (Fin n)) (hconn : G.Connected) (i j : Fin n) :
    (G.dist i j : ℝ) ≤ (((rhoMax G : ℕ∞) : ℝ≥0∞).toReal) := by
  have hmax : ((rhoMax G : ℕ∞) : ℝ≥0∞) ≠ ⊤ := by
    have := lpf_ediam_ne_top G hconn
    unfold rhoMax
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp this
    rw [← hm]; simp
  rw [← lpf_rho_toReal G hconn]
  apply ENNReal.toReal_mono hmax
  exact_mod_cast (SimpleGraph.edist_le_ediam : G.edist i j ≤ G.ediam)

theorem lpf_rhoAvg_toReal {n : ℕ} (G : SimpleGraph (Fin n)) (hconn : G.Connected) :
    (rhoAvg G).toReal = 2 / (n : ℝ) ^ 2 * ∑ i : Fin n, ∑ j : Fin n, (if i < j then (G.dist i j : ℝ) else 0) := by
  have h : ∀ i j : Fin n, ((G.edist i j : ℕ∞) : ℝ≥0∞) = ((G.dist i j : ℕ) : ℝ≥0∞) := by
    intro i j
    have h : (G.dist i j : ℕ∞) = G.edist i j := (hconn.preconnected i j).coe_dist_eq_edist
    rw [← h]; simp
  unfold rhoAvg
  simp only [h]
  have h2 : (∑ i : Fin n, ∑ j : Fin n, if i < j then ((G.dist i j : ℕ) : ℝ≥0∞) else 0) =
      ((∑ i : Fin n, ∑ j : Fin n, if i < j then G.dist i j else 0 : ℕ) : ℝ≥0∞) := by
    push_cast
    rfl
  rw [h2, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow]
  simp only [ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
  push_cast
  rfl

theorem lpf_pairs {n : ℕ} :
    2 * (∑ i : Fin n, ∑ j : Fin n, (if i < j then (1 : ℝ) else 0)) = (n : ℝ) * (n - 1) := by
  have h1 : (∑ i : Fin n, ∑ j : Fin n, ((if i < j then (1 : ℝ) else 0) + (if j < i then 1 else 0) +
      (if i = j then 1 else 0))) = (n : ℝ) ^ 2 := by
    have : ∀ i j : Fin n, ((if i < j then (1 : ℝ) else 0) + (if j < i then 1 else 0) +
        (if i = j then 1 else 0)) = 1 := by
      intro i j
      rcases lt_trichotomy i j with h | h | h
      · simp [h, h.ne, not_lt.mpr h.le]
      · simp [h]
      · simp [h, h.ne', not_lt.mpr h.le]
    simp [this]
    ring
  simp only [Finset.sum_add_distrib] at h1
  have h2 : (∑ i : Fin n, ∑ j : Fin n, (if j < i then (1 : ℝ) else 0)) =
      ∑ i : Fin n, ∑ j : Fin n, (if i < j then (1 : ℝ) else 0) := Finset.sum_comm
  have h3 : (∑ i : Fin n, ∑ j : Fin n, (if i = j then (1 : ℝ) else 0)) = n := by simp
  rw [h2, h3] at h1
  nlinarith

theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (hconn : G.Connected) (hn : 5 ≤ n) :
    LPCommunity.LPRecovery.LPFeasible n (xTilde G) := by
  have hnpos : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hc : 0 ≤ cG G := le_max_left _ _
  have hn1 : 0 < 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  set c := cG G with hcdef
  set S : ℝ := ∑ i : Fin n, ∑ j : Fin n, (if i < j then (G.dist i j : ℝ) else 0) with hS
  have hAvg := lpf_rhoAvg_toReal G hconn
  rw [← hS] at hAvg
  -- S > 0
  have hSpos : 0 < S := by
    have ha : (0 : ℕ) < n := by omega
    have hb : (1 : ℕ) < n := by omega
    set a : Fin n := ⟨0, ha⟩ with ha_def
    set b : Fin n := ⟨1, hb⟩ with hb_def
    have hab : a < b := by rw [Fin.lt_def]; simp [ha_def, hb_def]
    have hdist : 0 < (G.dist a b : ℝ) := by exact_mod_cast hconn.pos_dist_of_ne hab.ne
    have hnn : ∀ i j : Fin n, (0 : ℝ) ≤ (if i < j then (G.dist i j : ℝ) else 0) := by
      intro i j; split_ifs <;> simp
    refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j _ => hnn i j) ⟨a, Finset.mem_univ _, ?_⟩
    refine Finset.sum_pos' (fun j _ => hnn a j) ⟨b, Finset.mem_univ _, ?_⟩
    simpa [hab] using hdist
  have hn2 : (0 : ℝ) < n := by linarith
  have hAvgPos : 0 < (rhoAvg G).toReal := by
    rw [hAvg]; positivity
  set D : ℝ := (rhoAvg G).toReal + c * (1 - 1 / (n : ℝ)) with hDdef
  have hD : 0 < D := by
    have := mul_nonneg hc hn1.le
    linarith
  have hx : ∀ a b : Fin n, a ≠ b → xTilde G a b = ((G.dist a b : ℝ) + c) / (2 * D) := by
    intro a b hab
    simp only [xTilde, hab, if_false]
    rw [lpf_rho_toReal G hconn]
    congr 1
    rw [hDdef]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    by_cases h : i = j
    · rw [h]
    · rw [hx i j h, hx j i (Ne.symm h), SimpleGraph.dist_comm]
  · intro i; simp [xTilde]
  · intro i j k hij hki hkj
    rw [hx i j hij.ne, hx i k (Ne.symm hki), hx j k (Ne.symm hkj), ← add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have tri : G.dist i j ≤ G.dist i k + G.dist k j := hconn.dist_triangle (u := i) (v := k) (w := j)
    have tri' : (G.dist i j : ℝ) ≤ G.dist i k + G.dist j k := by
      rw [SimpleGraph.dist_comm (u := j) (v := k)]; exact_mod_cast tri
    linarith
  · intro i j k hij hjk
    rw [hx i j hij.ne, hx i k (hij.trans hjk).ne, hx j k hjk.ne, ← add_div, ← add_div,
      div_le_iff₀ (by positivity)]
    have h1 := lpf_dist_le_max G hconn i j
    have h2 := lpf_dist_le_max G hconn i k
    have h3 := lpf_dist_le_max G hconn j k
    have hn4 : 0 < 1 - 4 / (n : ℝ) := by
      have : 4 / (n : ℝ) < 1 := by rw [div_lt_one hn2]; linarith
      linarith
    have hcm : (3 * (((rhoMax G : ℕ∞) : ℝ≥0∞).toReal) - 4 * (rhoAvg G).toReal) / (1 - 4 / (n : ℝ)) ≤ c :=
      le_max_right _ _
    rw [div_le_iff₀ hn4] at hcm
    rw [hDdef]
    have e : c * (1 - 4 / (n : ℝ)) = c - 4 * (c / n) := by ring
    have e' : c * (1 - 1 / (n : ℝ)) = c - (c / n) := by ring
    rw [e] at hcm
    rw [e']
    linarith
  · have hxsum : ∀ i j : Fin n, (if i < j then xTilde G i j else 0) =
        1 / (2 * D) * ((if i < j then (G.dist i j : ℝ) else 0) + c * (if i < j then (1 : ℝ) else 0)) := by
      intro i j
      by_cases h : i < j
      · simp only [h, if_true]
        rw [hx i j h.ne]
        field_simp
      · simp [h]
    simp only [hxsum, ← Finset.mul_sum, Finset.sum_add_distrib]
    rw [← hS]
    have hm := lpf_pairs (n := n)
    set m : ℝ := ∑ i : Fin n, ∑ j : Fin n, (if i < j then (1 : ℝ) else 0) with hmdef
    have hD2 : 2 * D * ((n : ℝ) ^ 2 / 4) = S + c * m := by
      rw [hDdef, hAvg]
      have : m = (n : ℝ) * (n - 1) / 2 := by linarith
      rw [this]
      field_simp
      ring
    rw [show (1 : ℝ) / (2 * D) * (S + c * m) = (S + c * m) / (2 * D) by ring, ← hD2]
    field_simp
