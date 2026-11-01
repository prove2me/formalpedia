-- Prove2me | solution 1 for MaxValSens.Wolfe.theorem_3_3_limit_solution
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T18:12:26.130015+00:00
-- url     : https://prove2.me/submissions/d6a821d0-deff-40ec-8786-193ae055f8e7

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MaxValSens_Wolfe_Setting
open Filter Topology
open scoped InnerProductSpace

open MaxValSens.Wolfe

theorem solution {n m q : ℕ} (f : E n → E m → ℝ)
    (g : Fin q → E n → E m → ℝ) (xbar : E n)
    (hS : Standing f g xbar) (hRSC : RestrictedSupCompact f g xbar)
    (xs : ℕ → E n) (hx : Tendsto xs atTop (𝓝 xbar))
    (hV : Tendsto (fun k => V f g (xs k)) atTop (𝓝 (V f g xbar))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ys : ℕ → E m, (∀ k, ys k ∈ S f g (xs (φ k))) ∧
      ∃ ytil ∈ S f g xbar, Tendsto ys atTop (𝓝 ytil) := by
  obtain ⟨hVt, hVb, ε, hε, δ, hδ, K, hK, hRS⟩ := hRSC
  have hlt : V f g xbar - (ε : EReal) < V f g xbar := by
    lift V f g xbar to ℝ using ⟨hVt, hVb⟩ with v
    rw [← EReal.coe_sub]
    exact EReal.coe_lt_coe_iff.mpr (by linarith)
  have h1 : ∀ᶠ k in atTop, xs k ∈ Metric.ball xbar δ := hx (Metric.ball_mem_nhds _ hδ)
  have h2 : ∀ᶠ k in atTop, V f g xbar - (ε : EReal) < V f g (xs k) := hV (Ioi_mem_nhds hlt)
  obtain ⟨N, hN⟩ := (h1.and h2).exists_forall_of_atTop
  have key : ∀ k, ∃ y, y ∈ S f g (xs (k + N)) ∧ y ∈ K := by
    intro k
    obtain ⟨a, b⟩ := hN (k + N) (by omega)
    exact hRS _ a b
  choose y hyS hyK using key
  obtain ⟨ytil, hytK, φ, hφ, hlim⟩ := hK.tendsto_subseq hyK
  have hxφ : Tendsto (fun k => xs (φ k + N)) atTop (𝓝 xbar) :=
    hx.comp (tendsto_atTop_mono (fun k => Nat.le_add_right (φ k) N) hφ.tendsto_atTop)
  have hpair : Tendsto (fun k => (xs (φ k + N), y (φ k))) atTop (𝓝 (xbar, ytil)) :=
    hxφ.prodMk_nhds hlim
  refine ⟨fun k => φ k + N, fun a b hab => by simpa using hφ hab, fun k => y (φ k),
    fun k => hyS (φ k), ytil, ⟨?_, ?_⟩, hlim⟩
  · intro i
    have hc : Continuous (fun p : E n × E m => g i p.1 p.2) := (hS.2.1 i).continuous
    have ht := (hc.tendsto _).comp hpair
    exact le_of_tendsto' ht (fun k => (hyS (φ k)).1 i)
  · have hc : Continuous (fun p : E n × E m => f p.1 p.2) := hS.1.continuous
    have ht : Tendsto (fun k => ((f (xs (φ k + N)) (y (φ k)) : ℝ) : EReal)) atTop
        (𝓝 ((f xbar ytil : ℝ) : EReal)) :=
      (continuous_coe_real_ereal.tendsto _).comp ((hc.tendsto _).comp hpair)
    have ht2 : Tendsto (fun k => ((f (xs (φ k + N)) (y (φ k)) : ℝ) : EReal)) atTop
        (𝓝 (V f g xbar)) := by
      have : (fun k => ((f (xs (φ k + N)) (y (φ k)) : ℝ) : EReal)) =
          fun k => V f g (xs (φ k + N)) := funext fun k => (hyS (φ k)).2
      rw [this]
      exact hV.comp (tendsto_atTop_mono (fun k => Nat.le_add_right (φ k) N) hφ.tendsto_atTop)
    exact tendsto_nhds_unique ht ht2
