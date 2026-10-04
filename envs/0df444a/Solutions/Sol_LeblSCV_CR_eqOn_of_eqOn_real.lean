-- Prove2me | solution 1 for LeblSCV.CR.eqOn_of_eqOn_real
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:25:48.374537+00:00
-- url     : https://prove2.me/submissions/cd4b1898-c411-4925-bad7-2762ccd39ebc

import Mathlib
import Definitions.Def_LeblSCV_CR_realEmbed

open Filter Topology

namespace LeblSCV.CR

/-- Separate holomorphy (the second clause of Definition 1.1.2). -/
def SepHolo_core {n : ℕ} (f : (Fin n → ℂ) → ℂ) (U : Set (Fin n → ℂ)) : Prop :=
  ∀ z ∈ U, ∀ k : Fin n, DifferentiableAt ℂ (fun ξ : ℂ => f (Function.update z k (z k + ξ))) 0

/-- The slice `ζ ↦ f (update z k ζ)` is differentiable at every `ξ` with `update z k ξ ∈ U`. -/
lemma slice_differentiableAt_core {n : ℕ} {f : (Fin n → ℂ) → ℂ} {U : Set (Fin n → ℂ)}
    (hf : SepHolo_core f U) (z : Fin n → ℂ) (k : Fin n) (ξ : ℂ)
    (hz : Function.update z k ξ ∈ U) :
    DifferentiableAt ℂ (fun ζ : ℂ => f (Function.update z k ζ)) ξ := by
  have h := hf _ hz k
  simp only [Function.update_idem, Function.update_self] at h
  have hcomp : (fun ζ : ℂ => f (Function.update z k ζ)) =
      (fun ξ' : ℂ => f (Function.update z k (ξ + ξ'))) ∘ (fun ζ : ℂ => ζ - ξ) := by
    ext ζ; simp
  rw [hcomp]
  have hinner : DifferentiableAt ℂ (fun ζ : ℂ => ζ - ξ) ξ := differentiableAt_id.sub_const ξ
  have h0 : DifferentiableAt ℂ (fun ξ' : ℂ => f (Function.update z k (ξ + ξ')))
      ((fun ζ : ℂ => ζ - ξ) ξ) := by simpa using h
  exact DifferentiableAt.comp (f := fun ζ : ℂ => ζ - ξ) ξ h0 hinner

/-- Local step: if `f` is separately holomorphic on `U ⊇ ball z₀ r` (sup-norm ball, i.e. a
polydisc) and vanishes near some `w ∈ ball z₀ r`, then `f` vanishes on `ball z₀ r`. -/
lemma vanish_on_ball_core {n : ℕ} {f : (Fin n → ℂ) → ℂ} {U : Set (Fin n → ℂ)}
    (hf : SepHolo_core f U) (z₀ : Fin n → ℂ) (r : ℝ) (hr : 0 < r)
    (hB : Metric.ball z₀ r ⊆ U) (w : Fin n → ℂ) (hw : w ∈ Metric.ball z₀ r)
    (r' : ℝ) (hr' : 0 < r') (hw0 : ∀ v ∈ Metric.ball w r', f v = 0) :
    ∀ z ∈ Metric.ball z₀ r, f z = 0 := by
  have key : ∀ j : ℕ, ∀ z ∈ Metric.ball z₀ r,
      (∀ k : Fin n, j ≤ k.val → dist (z k) (w k) < r') → f z = 0 := by
    intro j
    induction j with
    | zero =>
      intro z _ hzk
      apply hw0
      rw [Metric.mem_ball, dist_pi_lt_iff hr']
      intro k; exact hzk k (Nat.zero_le _)
    | succ j ih =>
      intro z hz hzk
      by_cases hjn : j < n
      · obtain ⟨k, hk⟩ : ∃ k : Fin n, k.val = j := ⟨⟨j, hjn⟩, rfl⟩
        have hz' := hz
        rw [Metric.mem_ball, dist_pi_lt_iff hr] at hz'
        have hslice : DifferentiableOn ℂ (fun ζ : ℂ => f (Function.update z k ζ))
            (Metric.ball (z₀ k) r) := by
          intro ζ hζ
          refine (slice_differentiableAt_core hf z k ζ ?_).differentiableWithinAt
          apply hB
          rw [Metric.mem_ball, dist_pi_lt_iff hr]
          intro i
          by_cases hik : i = k
          · subst hik; simpa using hζ
          · rw [Function.update_of_ne hik]; exact hz' i
        have hanalytic := hslice.analyticOnNhd Metric.isOpen_ball
        have hwk : w k ∈ Metric.ball (z₀ k) r := by
          rw [Metric.mem_ball, dist_pi_lt_iff hr] at hw; exact hw k
        have hev : (fun ζ : ℂ => f (Function.update z k ζ)) =ᶠ[𝓝 (w k)] 0 := by
          filter_upwards [Metric.ball_mem_nhds (w k) hr', Metric.isOpen_ball.mem_nhds hwk]
            with ζ hζ hζ'
          apply ih
          · rw [Metric.mem_ball, dist_pi_lt_iff hr]
            intro i
            by_cases hik : i = k
            · subst hik; rw [Function.update_self]; exact hζ'
            · rw [Function.update_of_ne hik]; exact hz' i
          · intro i hi
            by_cases hik : i = k
            · subst hik; rw [Function.update_self]; exact hζ
            · rw [Function.update_of_ne hik]
              apply hzk i
              rcases Nat.lt_or_ge j i.val with h | h
              · exact h
              · exfalso; apply hik; ext; omega
        have hzero := hanalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
          (convex_ball _ _).isPreconnected hwk hev
        have hzk' : z k ∈ Metric.ball (z₀ k) r := hz' k
        have := hzero hzk'
        simpa [Function.update_eq_self] using this
      · apply ih z hz
        intro k hk
        exfalso
        have := k.isLt
        omega
  intro z hz
  exact key n z hz (fun k hk => absurd hk (by have := k.isLt; omega))

/-- Identity theorem for separately holomorphic functions on a connected open set. -/
lemma identity_core {n : ℕ} {f : (Fin n → ℂ) → ℂ} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (hUc : IsPreconnected U) (hf : SepHolo_core f U) {N : Set (Fin n → ℂ)} (hN : IsOpen N)
    (hNne : N.Nonempty) (hNU : N ⊆ U) (hzero : ∀ z ∈ N, f z = 0) : ∀ z ∈ U, f z = 0 := by
  let S : Set (Fin n → ℂ) := {z | ∀ᶠ w in 𝓝 z, f w = 0}
  have hSopen : IsOpen S := isOpen_setOfPred_eventually_nhds
  have hNS : N ⊆ S := fun z hz => (hN.eventually_mem hz).mono (fun w hw => hzero w hw)
  have hsub : U ⊆ S := by
    refine hUc.subset_of_closure_inter_subset hSopen ?_ ?_
    · obtain ⟨z, hz⟩ := hNne; exact ⟨z, hNU hz, hNS hz⟩
    · rintro z₀ ⟨hcl, hz₀U⟩
      obtain ⟨r, hr, hB⟩ := Metric.isOpen_iff.mp hU z₀ hz₀U
      obtain ⟨w, hwS, hwd⟩ := Metric.mem_closure_iff.mp hcl r hr
      have hwB : w ∈ Metric.ball z₀ r := by rw [Metric.mem_ball, dist_comm]; exact hwd
      obtain ⟨r', hr', hw0⟩ := Metric.eventually_nhds_iff.mp hwS
      have hball := vanish_on_ball_core hf z₀ r hr hB w hwB r' hr'
        (fun v hv => hw0 (Metric.mem_ball.mp hv))
      show ∀ᶠ v in 𝓝 z₀, f v = 0
      filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)] with v hv
      exact hball v hv
  intro z hz
  exact (hsub hz).self_of_nhds


/-- A `ℂ`-differentiable function on an open set is separately holomorphic. -/
lemma sepHolo_of_differentiableOn_core {n : ℕ} {f : (Fin n → ℂ) → ℂ} {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) : SepHolo_core f U := by
  intro z hz k
  have hfz : DifferentiableAt ℂ f (Function.update z k (z k + 0)) := by
    rw [add_zero, Function.update_eq_self]; exact hf.differentiableAt (hU.mem_nhds hz)
  have hΦ : DifferentiableAt ℂ (fun ξ : ℂ => Function.update z k (z k + ξ)) 0 := by
    rw [differentiableAt_pi]
    intro i
    by_cases hik : i = k
    · subst hik
      simp only [Function.update_self]
      exact (differentiableAt_const _).add differentiableAt_id
    · simp only [Function.update_of_ne hik]
      exact differentiableAt_const _
  exact DifferentiableAt.comp (g := f) (f := fun ξ : ℂ => Function.update z k (z k + ξ)) 0 hfz hΦ

/-- If a holomorphic `h` vanishes on the real points of an open `V`, it vanishes on a polydisc
around any real point of `V`. -/
lemma vanish_near_real_core {n : ℕ} {h : (Fin n → ℂ) → ℂ} {V : Set (Fin n → ℂ)}
    (hV : IsOpen V) (hh : DifferentiableOn ℂ h V) (x : Fin n → ℝ) (hx : realEmbed x ∈ V)
    (hzero : ∀ z ∈ V ∩ Set.range (realEmbed (n := n)), h z = 0) :
    ∃ r > 0, Metric.ball (realEmbed x) r ⊆ V ∧ ∀ z ∈ Metric.ball (realEmbed x) r, h z = 0 := by
  obtain ⟨r, hr, hB⟩ := Metric.isOpen_iff.mp hV _ hx
  refine ⟨r, hr, hB, ?_⟩
  have hsep := sepHolo_of_differentiableOn_core hV hh
  have hx₀im : ∀ k, (realEmbed x k).im = 0 := fun k => by simp [realEmbed]
  have key : ∀ j : ℕ, ∀ z ∈ Metric.ball (realEmbed x) r,
      (∀ k : Fin n, j ≤ k.val → (z k).im = 0) → h z = 0 := by
    intro j
    induction j with
    | zero =>
      intro z hz hzk
      apply hzero
      refine ⟨hB hz, fun k => (z k).re, ?_⟩
      funext k
      apply Complex.ext
      · simp [realEmbed]
      · simp [realEmbed, hzk k (Nat.zero_le _)]
    | succ j ih =>
      intro z hz hzk
      by_cases hjn : j < n
      · obtain ⟨k, hk⟩ : ∃ k : Fin n, k.val = j := ⟨⟨j, hjn⟩, rfl⟩
        have hz' := hz
        rw [Metric.mem_ball, dist_pi_lt_iff hr] at hz'
        have hmem : ∀ ζ ∈ Metric.ball (realEmbed x k) r,
            Function.update z k ζ ∈ Metric.ball (realEmbed x) r := by
          intro ζ hζ
          rw [Metric.mem_ball, dist_pi_lt_iff hr]
          intro i
          by_cases hik : i = k
          · subst hik; simpa using hζ
          · rw [Function.update_of_ne hik]; exact hz' i
        have hslice : DifferentiableOn ℂ (fun ζ : ℂ => h (Function.update z k ζ))
            (Metric.ball (realEmbed x k) r) := fun ζ hζ =>
          (slice_differentiableAt_core hsep z k ζ (hB (hmem ζ hζ))).differentiableWithinAt
        have hanalytic := hslice.analyticOnNhd Metric.isOpen_ball
        have hx₀k : realEmbed x k ∈ Metric.ball (realEmbed x k) r := Metric.mem_ball_self hr
        have hreal : ∀ ζ ∈ Metric.ball (realEmbed x k) r, ζ.im = 0 →
            h (Function.update z k ζ) = 0 := by
          intro ζ hζ hζim
          apply ih _ (hmem ζ hζ)
          intro i hi
          by_cases hik : i = k
          · subst hik; rw [Function.update_self]; exact hζim
          · rw [Function.update_of_ne hik]
            apply hzk i
            rcases Nat.lt_or_ge j i.val with h' | h'
            · exact h'
            · exfalso; apply hik; ext; omega
        have hfreq : ∃ᶠ ζ in 𝓝[≠] (realEmbed x k),
            (fun ζ : ℂ => h (Function.update z k ζ)) ζ = 0 := by
          rw [frequently_iff]
          intro W hW
          obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhdsWithin_iff.mp hW
          obtain ⟨δ, hδ, hδε, hδr⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧ δ < r :=
            ⟨min ε r / 2, by have := lt_min hε hr; linarith,
              by have := min_le_left ε r; linarith, by have := min_le_right ε r; linarith⟩
          have hdist : dist (realEmbed x k + (δ : ℂ)) (realEmbed x k) = δ := by
            rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos hδ]
          refine ⟨realEmbed x k + (δ : ℂ), hεW ⟨?_, ?_⟩, ?_⟩
          · rw [Metric.mem_ball, hdist]; exact hδε
          · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
            intro heq
            have : (δ : ℂ) = 0 := by linear_combination heq
            exact hδ.ne' (by exact_mod_cast this)
          · apply hreal
            · rw [Metric.mem_ball, hdist]; exact hδr
            · simp [hx₀im k]
        have hzero' := hanalytic.eqOn_zero_of_preconnected_of_frequently_eq_zero
          (convex_ball _ _).isPreconnected hx₀k hfreq
        have := hzero' (hz' k)
        simpa [Function.update_eq_self] using this
      · apply ih z hz
        intro k hk
        exfalso
        have := k.isLt
        omega
  intro z hz
  exact key n z hz (fun k hk => absurd hk (by have := k.isLt; omega))

end LeblSCV.CR

theorem solution {n : ℕ} (V : Set (Fin n → ℂ)) (hV : IsOpen V) (hVc : IsConnected V)
    (hVR : (V ∩ Set.range (LeblSCV.CR.realEmbed (n := n))).Nonempty) (f g : (Fin n → ℂ) → ℂ)
    (hf : DifferentiableOn ℂ f V) (hg : DifferentiableOn ℂ g V)
    (hfg : ∀ z ∈ V ∩ Set.range (LeblSCV.CR.realEmbed (n := n)), f z = g z) :
    Set.EqOn f g V := by
  obtain ⟨x₀, hx₀V, x, rfl⟩ := hVR
  have hh : DifferentiableOn ℂ (fun z => f z - g z) V := hf.sub hg
  obtain ⟨r, hr, hB, hzero⟩ := LeblSCV.CR.vanish_near_real_core hV hh x hx₀V
    (fun z hz => sub_eq_zero.mpr (hfg z hz))
  have := LeblSCV.CR.identity_core hV hVc.isPreconnected
    (LeblSCV.CR.sepHolo_of_differentiableOn_core hV hh) Metric.isOpen_ball
    ⟨_, Metric.mem_ball_self hr⟩ hB hzero
  intro z hz
  exact sub_eq_zero.mp (this z hz)

#print axioms solution
