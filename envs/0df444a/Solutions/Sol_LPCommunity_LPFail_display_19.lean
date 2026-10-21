-- Prove2me | solution 1 for LPCommunity.LPFail.display_19
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:45:29.129989+00:00
-- url     : https://prove2.me/submissions/e6d4bf7f-c65a-473d-9707-084d492dade7

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

theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (hconn : G.Connected) (hn : 5 ≤ n)
    (i j k : Fin n) (hij : i < j) (hjk : j < k) :
    xTilde G i j + xTilde G i k + xTilde G j k ≤
      3 / 2 * ((((rhoMax G : ℕ∞) : ℝ≥0∞).toReal + cG G) /
        ((rhoAvg G).toReal + cG G * (1 - 1 / (n : ℝ)))) := by
  have hnpos : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hc : 0 ≤ cG G := le_max_left _ _
  have hn1 : 0 ≤ 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  set D : ℝ := (rhoAvg G).toReal + cG G * (1 - 1 / (n : ℝ)) with hD
  have hD0 : 0 ≤ D := by
    have := ENNReal.toReal_nonneg (a := rhoAvg G)
    have := mul_nonneg hc hn1
    linarith
  have hmax : ((rhoMax G : ℕ∞) : ℝ≥0∞) ≠ ⊤ := by
    have := lpf_ediam_ne_top G hconn
    unfold rhoMax
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp this
    rw [← hm]; simp
  have hle : ∀ a b : Fin n, a ≠ b →
      xTilde G a b ≤ (((rhoMax G : ℕ∞) : ℝ≥0∞).toReal + cG G) / (2 * D) := by
    intro a b hab
    simp only [xTilde, hab, if_false]
    have h2D : 2 * (rhoAvg G).toReal + 2 * cG G * (1 - 1 / (n : ℝ)) = 2 * D := by rw [hD]; ring
    rw [h2D]
    apply div_le_div_of_nonneg_right _ (by linarith)
    have : ((rho G a b : ℕ∞) : ℝ≥0∞).toReal ≤ ((rhoMax G : ℕ∞) : ℝ≥0∞).toReal := by
      apply ENNReal.toReal_mono hmax
      exact_mod_cast (SimpleGraph.edist_le_ediam : G.edist a b ≤ G.ediam)
    linarith
  have h1 := hle i j hij.ne
  have h2 := hle i k (hij.trans hjk).ne
  have h3 := hle j k hjk.ne
  have : 3 / 2 * ((((rhoMax G : ℕ∞) : ℝ≥0∞).toReal + cG G) / D) =
      3 * ((((rhoMax G : ℕ∞) : ℝ≥0∞).toReal + cG G) / (2 * D)) := by
    ring
  rw [this]
  linarith
