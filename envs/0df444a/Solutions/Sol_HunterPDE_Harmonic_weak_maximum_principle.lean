-- Prove2me | solution 1 for HunterPDE.Harmonic.weak_maximum_principle
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T16:14:17.033806+00:00
-- url     : https://prove2.me/submissions/84bf81ff-0f32-4d80-bb45-7152f9f2c822

import Theorems.Thm_HunterPDE_Harmonic_strong_maximum_principle
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.Compact

open Set HunterPDE.Harmonic Topology Laplacian
set_option autoImplicit false

theorem solution {n : ℕ} (hn : 0 < n) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hΩ : IsOpen Ω) (hbdd : Bornology.IsBounded Ω)
    (hconn : IsConnected Ω) (hu : InnerProductSpace.HarmonicOnNhd u Ω)
    (hcont : ContinuousOn u (closure Ω)) :
    (∃ y ∈ frontier Ω, ∀ x ∈ closure Ω, u x ≤ u y) ∧
      (∃ y ∈ frontier Ω, ∀ x ∈ closure Ω, u y ≤ u x) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hcompact : IsCompact (closure Ω) := hbdd.isCompact_closure
  have hproper : Ω ≠ univ := by
    intro h
    have hc : IsCompact (univ : Set (EuclideanSpace ℝ (Fin n))) := by
      simpa [h] using hcompact
    exact hc.ne_univ rfl
  obtain ⟨b, hb⟩ := nonempty_frontier_iff.mpr ⟨hconn.nonempty, hproper⟩
  have hmax : ∀ (v : EuclideanSpace ℝ (Fin n) → ℝ),
      IsSubharmonicOn Ω v → ContinuousOn v (closure Ω) →
      ∃ y ∈ frontier Ω, ∀ x ∈ closure Ω, v x ≤ v y := by
    intro v hv hvc
    obtain ⟨a, ha, hamax⟩ := hcompact.exists_isMaxOn
      (hconn.nonempty.mono subset_closure) hvc
    by_cases hai : a ∈ Ω
    · obtain ⟨c, hc⟩ := strong_maximum_principle hΩ hconn.isPreconnected hv
        ⟨a, hai, fun x hx => hamax (subset_closure hx)⟩
      have heq : ∀ x ∈ closure Ω, v x = c := by
        intro x hx
        exact (hvc x hx).mono subset_closure |>.eq_const_of_mem_closure hx hc
      refine ⟨b, hb, fun x hx => ?_⟩
      rw [heq x hx, heq b (frontier_subset_closure hb)]
    · exact ⟨a, by simpa [hΩ.frontier_eq] using And.intro ha hai, hamax⟩
  have hsub : IsSubharmonicOn Ω u := ⟨hu.contDiffOn, fun x hx => by
    have hz : Δ u x = 0 := (hu x hx).2.eq_of_nhds
    exact hz.ge⟩
  have hnsub : IsSubharmonicOn Ω (-u) := ⟨hu.neg.contDiffOn, fun x hx => by
    have hz : Δ (-u) x = 0 := (hu.neg x hx).2.eq_of_nhds
    exact hz.ge⟩
  refine ⟨hmax u hsub hcont, ?_⟩
  obtain ⟨y, hy, hmin⟩ := hmax (-u) hnsub hcont.neg
  exact ⟨y, hy, fun x hx => neg_le_neg_iff.mp (hmin x hx)⟩
