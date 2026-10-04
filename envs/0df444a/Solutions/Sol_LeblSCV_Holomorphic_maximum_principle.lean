-- Prove2me | solution 1 for LeblSCV.Holomorphic.maximum_principle
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:22:47.759569+00:00
-- url     : https://prove2.me/submissions/03358eae-a29b-4fd5-81c2-d4ddd823d0a8

import Mathlib
import Definitions.Def_LeblSCV_Holomorphic_IsHolomorphicOn

open Filter Topology

namespace LeblSCV.Holomorphic

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


/-- Local maximum principle on a polydisc: if `‖f‖ ≤ ‖f a‖` on `ball a r ⊆ U` then `f = f a`
on `ball a r`, for `f` separately holomorphic on `U`. -/
lemma const_on_ball_core {n : ℕ} {f : (Fin n → ℂ) → ℂ} {U : Set (Fin n → ℂ)}
    (hf : SepHolo_core f U) (a : Fin n → ℂ) (r : ℝ) (hr : 0 < r)
    (hB : Metric.ball a r ⊆ U) (hle : ∀ z ∈ Metric.ball a r, ‖f z‖ ≤ ‖f a‖) :
    ∀ z ∈ Metric.ball a r, f z = f a := by
  have key : ∀ j : ℕ, ∀ z ∈ Metric.ball a r,
      (∀ k : Fin n, j ≤ k.val → z k = a k) → f z = f a := by
    intro j
    induction j with
    | zero =>
      intro z _ hzk
      have : z = a := funext fun k => hzk k (Nat.zero_le _)
      rw [this]
    | succ j ih =>
      intro z hz hzk
      by_cases hjn : j < n
      · obtain ⟨k, hk⟩ : ∃ k : Fin n, k.val = j := ⟨⟨j, hjn⟩, rfl⟩
        have hz' := hz
        rw [Metric.mem_ball, dist_pi_lt_iff hr] at hz'
        have hmem : ∀ ζ ∈ Metric.ball (a k) r, Function.update z k ζ ∈ Metric.ball a r := by
          intro ζ hζ
          rw [Metric.mem_ball, dist_pi_lt_iff hr]
          intro i
          by_cases hik : i = k
          · subst hik; simpa using hζ
          · rw [Function.update_of_ne hik]; exact hz' i
        have hslice : DifferentiableOn ℂ (fun ζ : ℂ => f (Function.update z k ζ))
            (Metric.ball (a k) r) := fun ζ hζ =>
          (slice_differentiableAt_core hf z k ζ (hB (hmem ζ hζ))).differentiableWithinAt
        have hak : a k ∈ Metric.ball (a k) r := Metric.mem_ball_self hr
        -- the value at the centre is `f a` by the induction hypothesis
        have hcen : f (Function.update z k (a k)) = f a := by
          apply ih _ (hmem _ hak)
          intro i hi
          by_cases hik : i = k
          · subst hik; rw [Function.update_self]
          · rw [Function.update_of_ne hik]
            apply hzk i
            rcases Nat.lt_or_ge j i.val with h | h
            · exact h
            · exfalso; apply hik; ext; omega
        have hmaxOn : IsMaxOn (norm ∘ fun ζ : ℂ => f (Function.update z k ζ))
            (Metric.ball (a k) r) (a k) := by
          intro ζ hζ
          simp only [Function.comp, Set.mem_ofPred_eq]
          rw [hcen]
          exact hle _ (hmem ζ hζ)
        have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
          (convex_ball _ _).isPreconnected Metric.isOpen_ball hslice hak hmaxOn
        have hzk' : z k ∈ Metric.ball (a k) r := hz' k
        have := hconst hzk'
        simp only [Function.const_apply, Function.update_eq_self] at this
        rw [this, hcen]
      · apply ih z hz
        intro k hk
        exfalso
        have := k.isLt
        omega
  intro z hz
  exact key n z hz (fun k hk => absurd hk (by have := k.isLt; omega))

end LeblSCV.Holomorphic

theorem solution {n : ℕ} {U : Set (Fin n → ℂ)} (hU : IsOpen U) (hUc : IsConnected U)
    {f : (Fin n → ℂ) → ℂ} (hf : LeblSCV.Holomorphic.IsHolomorphicOn f U)
    {a : Fin n → ℂ} (ha : a ∈ U) (hmax : IsLocalMaxOn (fun z => ‖f z‖) U a) :
    ∀ z ∈ U, f z = f a := by
  -- a polydisc around `a` inside `U` on which `‖f‖ ≤ ‖f a‖`
  have hmax' : ∀ᶠ z in 𝓝 a, ‖f z‖ ≤ ‖f a‖ := by
    have := hmax
    unfold IsLocalMaxOn IsMaxFilter at this
    rwa [hU.nhdsWithin_eq ha] at this
  obtain ⟨r₁, hr₁, hB₁⟩ := Metric.isOpen_iff.mp hU a ha
  obtain ⟨r₂, hr₂, hle⟩ := Metric.eventually_nhds_iff.mp hmax'
  set r := min r₁ r₂ with hr_def
  have hr : 0 < r := lt_min hr₁ hr₂
  have hB : Metric.ball a r ⊆ U := (Metric.ball_subset_ball (min_le_left _ _)).trans hB₁
  have hle' : ∀ z ∈ Metric.ball a r, ‖f z‖ ≤ ‖f a‖ := fun z hz =>
    hle (lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_right _ _))
  have hconst := LeblSCV.Holomorphic.const_on_ball_core hf.2 a r hr hB hle'
  -- apply the identity theorem to `f - f a`
  have hsep : LeblSCV.Holomorphic.SepHolo_core (fun z => f z - f a) U := by
    intro z hz k
    exact (hf.2 z hz k).sub_const _
  have hzero := LeblSCV.Holomorphic.identity_core hU hUc.isPreconnected hsep Metric.isOpen_ball
    ⟨a, Metric.mem_ball_self hr⟩ hB (fun z hz => sub_eq_zero.mpr (hconst z hz))
  intro z hz
  exact sub_eq_zero.mp (hzero z hz)

#print axioms solution
