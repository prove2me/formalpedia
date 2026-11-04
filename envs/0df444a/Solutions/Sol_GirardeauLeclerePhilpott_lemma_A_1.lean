-- Prove2me | solution 1 for GirardeauLeclerePhilpott.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T00:20:40.692205+00:00
-- url     : https://prove2.me/submissions/df585ed8-143b-4527-8810-a5c667b74566

import Mathlib
open Filter Topology

theorem solution {E : Type*} [PseudoMetricSpace E] (X : Set E) (hX : IsCompact X)
    (f : E → ℝ) (F : ℕ → E → ℝ) (L : ℝ)
    (hL : ∀ k, ∀ x ∈ X, ∀ y ∈ X, |F k x - F k y| ≤ L * dist x y)
    (hmono : ∀ k, ∀ x ∈ X, F k x ≤ F (k + 1) x) (hle : ∀ k, ∀ x ∈ X, F k x ≤ f x)
    (x : ℕ → E) (hx : ∀ k, x k ∈ X)
    (h : Tendsto (fun k => f (x k) - F k (x k)) atTop (𝓝 0)) :
    Tendsto (fun k => f (x (k + 1)) - F k (x (k + 1))) atTop (𝓝 0) := by
  -- the shifted gap sequence a (k+1) → 0
  have hsh : Tendsto (fun k => f (x (k + 1)) - F (k + 1) (x (k + 1))) atTop (𝓝 0) :=
    h.comp (tendsto_add_atTop_nat 1)
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨xs, hxsX, ψ, hψ, hconv⟩ :=
    hX.tendsto_subseq (x := fun n => x (ns n + 1)) (fun n => hx _)
  refine ⟨ψ, ?_⟩
  have hm : Tendsto (fun n => ns (ψ n)) atTop atTop := hns.comp hψ.tendsto_atTop
  -- increments of the monotone bounded sequence F k xs tend to 0
  have hmonoxs : Monotone (fun k => F k xs) := monotone_nat_of_le_succ fun k => hmono k xs hxsX
  have hbdd : BddAbove (Set.range fun k => F k xs) := ⟨f xs, by
    rintro _ ⟨k, rfl⟩; exact hle k xs hxsX⟩
  have hlim := tendsto_atTop_ciSup hmonoxs hbdd
  have hinc : Tendsto (fun k => F (k + 1) xs - F k xs) atTop (𝓝 0) := by
    have := (hlim.comp (tendsto_add_atTop_nat 1)).sub hlim
    simpa using this
  have hd : Tendsto (fun n => dist (x (ns (ψ n) + 1)) xs) atTop (𝓝 0) :=
    (tendsto_iff_dist_tendsto_zero.1 hconv)
  have hlow : Tendsto (fun n => f (x (ns (ψ n) + 1)) - F (ns (ψ n) + 1) (x (ns (ψ n) + 1)))
      atTop (𝓝 0) := hsh.comp hm
  have hup : Tendsto (fun n =>
      (f (x (ns (ψ n) + 1)) - F (ns (ψ n) + 1) (x (ns (ψ n) + 1))) +
        (L * dist (x (ns (ψ n) + 1)) xs + L * dist (x (ns (ψ n) + 1)) xs) +
        (F (ns (ψ n) + 1) xs - F (ns (ψ n)) xs)) atTop (𝓝 0) := by
    have := (hlow.add ((hd.const_mul L).add (hd.const_mul L))).add (hinc.comp hm)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup (fun n => ?_) (fun n => ?_)
  · show _ ≤ f (x (ns (ψ n) + 1)) - F (ns (ψ n)) (x (ns (ψ n) + 1))
    linarith [hmono (ns (ψ n)) _ (hx (ns (ψ n) + 1))]
  · show f (x (ns (ψ n) + 1)) - F (ns (ψ n)) (x (ns (ψ n) + 1)) ≤ _
    set m := ns (ψ n)
    have h1 := (abs_le.1 (hL (m + 1) _ (hx (m + 1)) xs hxsX)).2
    have h2 := (abs_le.1 (hL m _ (hx (m + 1)) xs hxsX)).1
    linarith
