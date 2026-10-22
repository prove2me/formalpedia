-- Prove2me | solution 1 for NumStochOpt.Nonstationary.theorem_6_4_nonmonotone_convergence_criterion
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T02:00:05.129992+00:00
-- url     : https://prove2.me/submissions/0d141bc8-3411-43e3-a64c-de312dc08726

import Mathlib
import Definitions.Def_NumStochOpt_Nonstationary_ExitTime

open Filter Topology


namespace NumStochOpt.Nonstationary

theorem crit_core {n : ℕ}
    (Xstar K : Set (EuclideanSpace ℝ (Fin n))) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (V : EuclideanSpace ℝ (Fin n) → ℝ)
    (hXstar : IsClosed Xstar)
    (hK : IsCompact K) (hxK : ∀ s, x s ∈ K)
    (h2a : ∀ (φ : ℕ → ℕ) (x' : EuclideanSpace ℝ (Fin n)), StrictMono φ →
      Tendsto (x ∘ φ) atTop (𝓝 x') → x' ∈ Xstar →
        Tendsto (fun k => ‖x (φ k + 1) - x (φ k)‖) atTop (𝓝 0))
    (hV : Continuous V) (hVcount : (V '' Xstar).Countable)
    (h2b3 : ∀ (φ : ℕ → ℕ) (x' : EuclideanSpace ℝ (Fin n)), StrictMono φ →
      Tendsto (x ∘ φ) atTop (𝓝 x') → x' ∉ Xstar →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
          (∀ k, ∃ s, φ k ≤ s ∧ ε < ‖x s - x (φ k)‖) ∧
          limsup (fun k => V (x (exitTime x (φ k) ε))) atTop < V x') :
    (∃ L : ℝ, Tendsto (fun s => V (x s)) atTop (𝓝 L)) ∧
      ∀ x' : EuclideanSpace ℝ (Fin n), MapClusterPt x' atTop x → x' ∈ Xstar := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hV.continuousOn
  have hup : IsBoundedUnder (· ≤ ·) atTop (fun s => V (x s)) :=
    isBoundedUnder_of ⟨M, fun s => (le_abs_self _).trans (by simpa using hM _ (hxK s))⟩
  have hlo : IsBoundedUnder (· ≥ ·) atTop (fun s => V (x s)) :=
    isBoundedUnder_of ⟨-M, fun s => by
      have := hM _ (hxK s)
      simp only [Real.norm_eq_abs] at this
      linarith [neg_abs_le (V (x s))]⟩
  have hconv : ∃ L : ℝ, Tendsto (fun s => V (x s)) atTop (𝓝 L) := by
    by_contra hnc
    have hne : liminf (fun s => V (x s)) atTop ≠ limsup (fun s => V (x s)) atTop := by
      intro heq
      exact hnc ⟨_, tendsto_of_liminf_eq_limsup (a := limsup (fun s => V (x s)) atTop)
        heq rfl hup hlo⟩
    have hlt : liminf (fun s => V (x s)) atTop < limsup (fun s => V (x s)) atTop :=
      lt_of_le_of_ne (liminf_le_limsup hup hlo) hne
    set lo := liminf (fun s => V (x s)) atTop
    set hi := limsup (fun s => V (x s)) atTop
    have hnc2 : ¬ (Set.Ioo lo hi) ⊆ V '' Xstar := by
      intro hsub
      have := Cardinal.Real.Ioo_countable_iff.mp (hVcount.mono hsub)
      linarith
    obtain ⟨u, ⟨hu1, hu2⟩, hu3⟩ := Set.not_subset.mp hnc2
    set c := (u + hi) / 2 with hc
    have huc : u < c := by rw [hc]; linarith
    have hch : c < hi := by rw [hc]; linarith
    have fr1 : ∃ᶠ s in atTop, V (x s) < u := frequently_lt_of_liminf_lt hup.isCoboundedUnder_flip hu1
    have fr2 : ∃ᶠ s in atTop, c < V (x s) := frequently_lt_of_lt_limsup hlo.isCoboundedUnder_flip hch
    -- the good times
    let P : ℕ → Prop := fun p => V (x p) ≤ u ∧ ∃ q, p < q ∧ c ≤ V (x q) ∧
      ∀ s, p < s → s ≤ q → u < V (x s)
    have hP : ∃ᶠ p in atTop, P p := by
      rw [frequently_atTop]
      intro N
      obtain ⟨s0, hs0, hs0'⟩ := (frequently_atTop.mp fr1) N
      obtain ⟨q, hq, hq'⟩ := (frequently_atTop.mp fr2) (s0 + 1)
      have hex : ∃ p, p < q ∧ V (x p) ≤ u := ⟨s0, by omega, hs0'.le⟩
      classical
      obtain ⟨p, hpdef⟩ : ∃ p, p = Nat.findGreatest (fun p => V (x p) ≤ u) q := ⟨_, rfl⟩
      have hp_spec : V (x p) ≤ u := by
        rw [hpdef]
        exact Nat.findGreatest_spec (P := fun p => V (x p) ≤ u) (m := s0) (by omega) hs0'.le
      have hs0p : s0 ≤ p := by
        rw [hpdef]; exact Nat.le_findGreatest (by omega) hs0'.le
      have hpq : p < q := by
        rcases (show p ≤ q by rw [hpdef]; exact Nat.findGreatest_le q).lt_or_eq with h | h
        · exact h
        · exfalso; rw [h] at hp_spec; linarith
      refine ⟨p, by omega, hp_spec, q, hpq, hq'.le, ?_⟩
      intro s hps hsq
      by_contra hcon
      push_neg at hcon
      have := Nat.le_findGreatest (P := fun p => V (x p) ≤ u) hsq hcon
      rw [← hpdef] at this
      omega
    obtain ⟨φ, hφ, hPφ⟩ := extraction_of_frequently_atTop hP
    obtain ⟨x', hx'K, ψ, hψ, hψt⟩ := hK.tendsto_subseq (x := fun k => x (φ k)) (fun k => hxK _)
    have hφψ : StrictMono (φ ∘ ψ) := hφ.comp hψ
    have hxt : Tendsto (x ∘ (φ ∘ ψ)) atTop (𝓝 x') := hψt
    choose q hq using fun k => (hPφ k).2
    -- value at x'
    have hVt : Tendsto (fun k => V (x (φ (ψ k)))) atTop (𝓝 (V x')) :=
      (hV.continuousAt.tendsto).comp hxt
    have hVx' : V x' ≤ u := le_of_tendsto' hVt (fun k => (hPφ _).1)
    by_cases hx'X : x' ∈ Xstar
    · have hs := h2a (φ ∘ ψ) x' hφψ hxt hx'X
      have hs2 : Tendsto (fun k => x (φ (ψ k) + 1)) atTop (𝓝 x') := by
        have h1 : Tendsto (fun k => x (φ (ψ k) + 1) - x (φ (ψ k))) atTop (𝓝 0) :=
          tendsto_zero_iff_norm_tendsto_zero.mpr hs
        simpa using h1.add hxt
      have hVt2 : Tendsto (fun k => V (x (φ (ψ k) + 1))) atTop (𝓝 (V x')) :=
        (hV.continuousAt.tendsto).comp hs2
      have : u ≤ V x' := by
        refine ge_of_tendsto' hVt2 (fun k => ?_)
        have := (hq (ψ k)).2.2 (φ (ψ k) + 1) (by omega) (by have := (hq (ψ k)).1; omega)
        exact this.le
      exact hu3 ⟨x', hx'X, by linarith⟩
    · obtain ⟨ε₀, hε₀, hε⟩ := h2b3 (φ ∘ ψ) x' hφψ hxt hx'X
      -- continuity of V at x'
      have hcont : ∀ᶠ y in 𝓝 x', V y < c :=
        hV.continuousAt.eventually (gt_mem_nhds (by linarith : V x' < c))
      obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp hcont
      set ε := min (ε₀ / 2) (δ / 2) with hεdef
      have hεpos : 0 < ε := by positivity
      have hεlt : ε < ε₀ := by
        have : ε ≤ ε₀ / 2 := min_le_left _ _
        linarith
      obtain ⟨hex, hlim⟩ := hε ε hεpos hεlt
      have hdist : ∀ᶠ k in atTop, dist (x (φ (ψ k))) x' < ε := by
        exact (Metric.tendsto_nhds.mp hxt) ε hεpos
      have hbig : ∀ᶠ k in atTop, ε < ‖x (q (ψ k)) - x (φ (ψ k))‖ := by
        filter_upwards [hdist] with k hk
        by_contra hcon
        push_neg at hcon
        have : dist (x (q (ψ k))) x' < δ := by
          have h1 : dist (x (q (ψ k))) x' ≤ dist (x (q (ψ k))) (x (φ (ψ k))) + dist (x (φ (ψ k))) x' :=
            dist_triangle _ _ _
          rw [dist_eq_norm (x (q (ψ k))) (x (φ (ψ k)))] at h1
          have : ε ≤ δ / 2 := min_le_right _ _
          linarith
        have h3 := hδ' this
        have h4 := (hq (ψ k)).2.1
        linarith
      have hτ : ∀ᶠ k in atTop, u < V (x (exitTime x (φ (ψ k)) ε)) := by
        filter_upwards [hbig] with k hk
        have hmem : q (ψ k) ∈ {s : ℕ | φ (ψ k) ≤ s ∧ ε < ‖x s - x (φ (ψ k))‖} :=
          ⟨by have := (hq (ψ k)).1; have := hφψ.monotone (le_refl k); simp only [Function.comp] at this; omega, hk⟩
        have hne : {s : ℕ | φ (ψ k) ≤ s ∧ ε < ‖x s - x (φ (ψ k))‖}.Nonempty := ⟨_, hmem⟩
        have hτmem := Nat.sInf_mem hne
        have hτle : exitTime x (φ (ψ k)) ε ≤ q (ψ k) := Nat.sInf_le hmem
        have hτ1 : φ (ψ k) ≤ exitTime x (φ (ψ k)) ε := hτmem.1
        have hτ2 : φ (ψ k) ≠ exitTime x (φ (ψ k)) ε := by
          intro heq
          have h5 : ε < ‖x (exitTime x (φ (ψ k)) ε) - x (φ (ψ k))‖ := hτmem.2
          rw [← heq, sub_self, norm_zero] at h5
          linarith
        have hP2 := (hq (ψ k)).2.2 (exitTime x (φ (ψ k)) ε) (by omega) hτle
        exact hP2
      have hge : u ≤ limsup (fun k => V (x (exitTime x (φ (ψ k)) ε))) atTop := by
        apply le_limsup_of_frequently_le
        · exact (hτ.mono fun k hk => hk.le).frequently
        · exact isBoundedUnder_of ⟨M, fun k => (le_abs_self _).trans (by simpa using hM _ (hxK _))⟩
      have hlim' : limsup (fun k => V (x (exitTime x (φ (ψ k)) ε))) atTop < V x' := hlim
      linarith
  refine ⟨hconv, ?_⟩
  intro x' hx'
  by_contra hnot
  obtain ⟨L, hL⟩ := hconv
  obtain ⟨φ, hφ, hφt⟩ := hx'.tendsto_subseq
  obtain ⟨ε₀, hε₀, h⟩ := h2b3 φ x' hφ hφt hnot
  obtain ⟨hex, hlim⟩ := h (ε₀ / 2) (by positivity) (by linarith)
  have hVx : V x' = L := by
    have h1 : Tendsto (fun k => V (x (φ k))) atTop (𝓝 (V x')) := (hV.continuousAt.tendsto).comp hφt
    have h2 : Tendsto (fun k => V (x (φ k))) atTop (𝓝 L) := hL.comp hφ.tendsto_atTop
    exact tendsto_nhds_unique h1 h2
  have hτge : ∀ k, φ k ≤ exitTime x (φ k) (ε₀ / 2) := fun k => by
    have hne : {s : ℕ | φ k ≤ s ∧ ε₀ / 2 < ‖x s - x (φ k)‖}.Nonempty := by
      obtain ⟨s, hs⟩ := hex k
      exact ⟨s, hs⟩
    exact (Nat.sInf_mem hne).1
  have hτt : Tendsto (fun k => exitTime x (φ k) (ε₀ / 2)) atTop atTop :=
    tendsto_atTop_mono hτge hφ.tendsto_atTop
  have h3 : Tendsto (fun k => V (x (exitTime x (φ k) (ε₀ / 2)))) atTop (𝓝 L) := hL.comp hτt
  rw [h3.limsup_eq, hVx] at hlim
  exact lt_irrefl _ hlim

end NumStochOpt.Nonstationary

open NumStochOpt.Nonstationary


theorem solution {n : ℕ}
    (Xstar K : Set (EuclideanSpace ℝ (Fin n))) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (V : EuclideanSpace ℝ (Fin n) → ℝ)
    (hXstar : IsClosed Xstar)
    (hK : IsCompact K) (hxK : ∀ s, x s ∈ K)
    (h2a : ∀ (φ : ℕ → ℕ) (x' : EuclideanSpace ℝ (Fin n)), StrictMono φ →
      Tendsto (x ∘ φ) atTop (𝓝 x') → x' ∈ Xstar →
        Tendsto (fun k => ‖x (φ k + 1) - x (φ k)‖) atTop (𝓝 0))
    (hV : Continuous V) (hVcount : (V '' Xstar).Countable)
    (h2b3 : ∀ (φ : ℕ → ℕ) (x' : EuclideanSpace ℝ (Fin n)), StrictMono φ →
      Tendsto (x ∘ φ) atTop (𝓝 x') → x' ∉ Xstar →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
          (∀ k, ∃ s, φ k ≤ s ∧ ε < ‖x s - x (φ k)‖) ∧
          limsup (fun k => V (x (exitTime x (φ k) ε))) atTop < V x') :
    (∃ L : ℝ, Tendsto (fun s => V (x s)) atTop (𝓝 L)) ∧
      ∀ x' : EuclideanSpace ℝ (Fin n), MapClusterPt x' atTop x → x' ∈ Xstar := by
  exact crit_core Xstar K x V hXstar hK hxK h2a hV hVcount h2b3
