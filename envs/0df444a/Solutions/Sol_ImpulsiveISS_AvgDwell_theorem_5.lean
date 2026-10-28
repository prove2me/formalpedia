-- Prove2me | solution 1 for ImpulsiveISS.AvgDwell.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T13:54:51.253722+00:00
-- url     : https://prove2.me/submissions/f7fcf77a-f020-444b-8d5b-a6f6c305b656

import Mathlib
import Definitions.Def_ImpulsiveISS_AvgDwell_Setting

set_option autoImplicit false

open scoped NNReal
open Filter Topology Set

namespace P8698

open SmallGainISS.Lyapunov ProcessingNetworks.LyapunovCriteria ImpulsiveISS.AvgDwell

lemma natCard_eq_sub (P : ℕ → Prop) (a b : ℕ) (h : ∀ k, P k ↔ a ≤ k ∧ k < b) :
    Nat.card {k : ℕ // P k} = b - a := by
  have e : {k : ℕ // P k} ≃ (Finset.Ico a b) :=
    Equiv.subtypeEquivRight (fun k => by simp [h k, Finset.mem_Ico])
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, Nat.card_Ico]

lemma exists_idx {τ : ℕ → ℝ} (hτ : ImpulsiveISS.FixedDwell.IsImpulseSeq τ) (t : ℝ) :
    ∃ n : ℕ, ∀ k, τ k ≤ t ↔ k < n := by
  classical
  have hex : ∃ n, t < τ n := (hτ.2.2.eventually_gt_atTop t).exists
  refine ⟨Nat.find hex, fun k => ⟨fun hk => ?_, fun hk => ?_⟩⟩
  · by_contra hlt
    push Not at hlt
    have h1 := hτ.1.monotone hlt
    have h2 := Nat.find_spec hex
    linarith
  · have := Nat.find_min hex hk
    push Not at this
    exact this

lemma count_eq {τ : ℕ → ℝ} {t s : ℝ} {a b : ℕ} (ht : ∀ k, τ k ≤ t ↔ k < a)
    (hs : ∀ k, τ k ≤ s ↔ k < b) : count τ t s = a - b := by
  unfold count
  apply natCard_eq_sub
  intro k
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨not_lt.1 (fun hb => absurd ((hs k).2 hb) (not_le.2 h1)), (ht k).1 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨not_le.1 (fun hb => absurd ((hs k).1 hb) (not_lt.2 h1)), (ht k).2 h2⟩

lemma tau_pos {τ : ℕ → ℝ} (hτ : ImpulsiveISS.FixedDwell.IsImpulseSeq τ) (k : ℕ) : 0 < τ k :=
  hτ.2.1.trans_le (hτ.1.monotone (Nat.zero_le k))

lemma idx_zero {τ : ℕ → ℝ} (hτ : ImpulsiveISS.FixedDwell.IsImpulseSeq τ) :
    ∀ k, τ k ≤ 0 ↔ k < 0 :=
  fun k => ⟨fun h => absurd h (not_le.2 (tau_pos hτ k)), fun h => absurd h (Nat.not_lt_zero _)⟩

lemma count_eq_of {τ : ℕ → ℝ} (hτ : ImpulsiveISS.FixedDwell.IsImpulseSeq τ) {t : ℝ} {n : ℕ}
    (h : ∀ k, τ k ≤ t ↔ k < n) : count τ t 0 = n := by
  rw [count_eq h (idx_zero hτ)]
  simp

lemma idx {τ : ℕ → ℝ} (hτ : ImpulsiveISS.FixedDwell.IsImpulseSeq τ) (t : ℝ) :
    ∀ k, τ k ≤ t ↔ k < count τ t 0 := by
  obtain ⟨n, hn⟩ := exists_idx hτ t
  rw [count_eq_of hτ hn]
  exact hn

lemma count_sub {τ : ℕ → ℝ} (hτ : ImpulsiveISS.FixedDwell.IsImpulseSeq τ) (t s : ℝ) :
    count τ t s = count τ t 0 - count τ s 0 :=
  count_eq (idx hτ t) (idx hτ s)

lemma count_mono {τ : ℕ → ℝ} (hτ : ImpulsiveISS.FixedDwell.IsImpulseSeq τ) {s t : ℝ}
    (hst : s ≤ t) : count τ s 0 ≤ count τ t 0 := by
  by_contra hlt
  push Not at hlt
  have h1 := (idx hτ s _).2 hlt
  have h2 := (idx hτ t (count τ t 0)).1 (h1.trans hst)
  exact lt_irrefl _ h2

lemma epoch_zero (τ : ℕ → ℝ) : epoch τ 0 = 0 := rfl

lemma epoch_succ (τ : ℕ → ℝ) (k : ℕ) : epoch τ (k + 1) = τ k := rfl

lemma epoch_nonneg {τ : ℕ → ℝ} (hτ : ImpulsiveISS.FixedDwell.IsImpulseSeq τ) (k : ℕ) :
    0 ≤ epoch τ k := by
  cases k with
  | zero => exact le_rfl
  | succ j => exact (tau_pos hτ j).le

lemma epoch_lt {τ : ℕ → ℝ} (hτ : ImpulsiveISS.FixedDwell.IsImpulseSeq τ) (k : ℕ) :
    epoch τ k < τ k := by
  cases k with
  | zero => exact hτ.2.1
  | succ j => exact hτ.1 (Nat.lt_succ_self j)

lemma count_piece {τ : ℕ → ℝ} (hτ : ImpulsiveISS.FixedDwell.IsImpulseSeq τ) {k : ℕ} {σ : ℝ}
    (h1 : epoch τ k ≤ σ) (h2 : σ < τ k) : count τ σ 0 = k := by
  apply count_eq_of hτ
  intro i
  constructor
  · intro hi
    by_contra hki
    push Not at hki
    have := hτ.1.monotone hki
    linarith
  · intro hi
    cases k with
    | zero => exact absurd hi (Nat.not_lt_zero _)
    | succ j =>
      have : τ i ≤ τ j := hτ.1.monotone (Nat.lt_succ_iff.1 hi)
      rw [epoch_succ] at h1
      linarith

lemma piece_of {τ : ℕ → ℝ} (hτ : ImpulsiveISS.FixedDwell.IsImpulseSeq τ) {t : ℝ} (ht : 0 ≤ t) :
    epoch τ (count τ t 0) ≤ t ∧ t < τ (count τ t 0) := by
  have h := idx hτ t
  refine ⟨?_, ?_⟩
  · obtain ⟨k, hk⟩ : ∃ k, k = count τ t 0 := ⟨_, rfl⟩
    rw [← hk]
    cases k with
    | zero => exact ht
    | succ j =>
      rw [epoch_succ]
      exact (h j).2 (hk ▸ Nat.lt_succ_self j)
  · by_contra hle
    push Not at hle
    exact lt_irrefl _ ((h _).1 hle)

lemma shift_isPC {U : Type*} [NormedAddCommGroup U] {u : ℝ → U}
    (hu : ImpulsiveISS.FixedDwell.IsPCInput u) {e : ℝ} (he : 0 ≤ e) :
    ImpulsiveISS.FixedDwell.IsPCInput (ImpulsiveISS.FixedDwell.shift u e) := by
  obtain ⟨h1, h2, h3, h4⟩ := hu
  have hcont : Continuous (fun r : ℝ => r + e) := continuous_id.add continuous_const
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun T => ?_, ?_⟩
  · have := h1 (t + e) (by linarith)
    exact ContinuousWithinAt.comp (f := fun r : ℝ => r + e) (x := t) this
      hcont.continuousWithinAt (fun x hx => by simp only [Set.mem_Ici] at hx ⊢; linarith)
  · obtain ⟨v, hv⟩ := h2 (t + e) (by linarith)
    refine ⟨v, hv.comp ?_⟩
    rw [tendsto_nhdsWithin_iff]
    refine ⟨(hcont.tendsto t).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_Iio] at hx ⊢
    linarith
  · refine ((h3 (T + e)).image (fun s => s - e)).subset ?_
    intro t ht
    obtain ⟨⟨ht0, htT⟩, hnc⟩ := ht
    refine ⟨t + e, ⟨⟨by linarith, by linarith⟩, fun hc => hnc ?_⟩, by ring⟩
    exact ContinuousWithinAt.comp (f := fun r : ℝ => r + e) (x := t) hc
      hcont.continuousWithinAt (fun x hx => by simp only [Set.mem_Ici] at hx ⊢; linarith)
  · obtain ⟨M, hM⟩ := h4
    exact ⟨M, fun t ht => hM (t + e) (by linarith)⟩

lemma leftLim_nnnorm_le {U : Type*} [NormedAddCommGroup U] {u : ℝ → U}
    (hu : ImpulsiveISS.FixedDwell.IsPCInput u) {M : ℝ≥0} (hM : ∀ t : ℝ, 0 ≤ t → ‖u t‖₊ ≤ M)
    {a : ℝ} (ha : 0 < a) : ‖Function.leftLim u a‖₊ ≤ M := by
  obtain ⟨v, hv⟩ := hu.2.1 a ha
  rw [leftLim_eq_of_tendsto hv]
  have h2 := (continuous_nnnorm.tendsto v).comp hv
  exact le_of_tendsto h2 (by
    filter_upwards [Ioo_mem_nhdsLT ha] with x hx using hM x hx.1.le)

lemma exp_bound {w : ℝ → ℝ} {c G r0 L : ℝ} (hle : r0 ≤ L)
    (hw : ContinuousOn w (Icc r0 L))
    (hsl : ∀ x ∈ Ico r0 L, G ≤ w x → ∀ ρ, -c * w x < ρ → ∃ᶠ z in 𝓝[>] x, slope w x z < ρ)
    (hG : ∀ x ∈ Ico r0 L, G ≤ w x) (hw0 : 0 ≤ w r0) :
    w L ≤ Real.exp (-c * (L - r0)) * w r0 := by
  have key : ∀ ε > (0:ℝ), w L ≤ (w r0 + ε) * Real.exp (-(c - ε) * (L - r0)) := by
    intro ε hε
    have hder : ∀ x, HasDerivAt (fun x => (w r0 + ε) * Real.exp (-(c - ε) * (x - r0)))
        ((w r0 + ε) * (Real.exp (-(c - ε) * (x - r0)) * (-(c - ε)))) x := by
      intro x
      have h1 : HasDerivAt (fun x => -(c - ε) * (x - r0)) (-(c - ε)) x := by
        simpa using ((hasDerivAt_id x).sub_const r0).const_mul (-(c - ε))
      exact (h1.exp).const_mul _
    have hbd : ∀ x ∈ Ico r0 L, w x = (w r0 + ε) * Real.exp (-(c - ε) * (x - r0)) →
        -c * w x < (w r0 + ε) * (Real.exp (-(c - ε) * (x - r0)) * (-(c - ε))) := by
      intro x _ hfx
      have hpos : 0 < (w r0 + ε) * Real.exp (-(c - ε) * (x - r0)) := by positivity
      have := mul_pos hε hpos
      rw [hfx]
      nlinarith
    have ha : w r0 ≤ (w r0 + ε) * Real.exp (-(c - ε) * (r0 - r0)) := by
      simp only [sub_self, mul_zero, Real.exp_zero, mul_one]
      linarith
    exact image_le_of_liminf_slope_right_lt_deriv_boundary (f := w) (f' := fun x => -c * w x)
      hw (fun x hx ρ hρ => hsl x hx (hG x hx) ρ hρ) ha hder hbd ⟨hle, le_rfl⟩
  have hT : Tendsto (fun ε => (w r0 + ε) * Real.exp (-(c - ε) * (L - r0))) (𝓝[>] (0:ℝ))
      (𝓝 ((w r0 + 0) * Real.exp (-(c - 0) * (L - r0)))) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    apply Continuous.tendsto
    fun_prop
  simp only [add_zero, sub_zero] at hT
  have := ge_of_tendsto hT (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)
  rw [mul_comm] at this
  exact this

lemma flow_bound {w : ℝ → ℝ} {c G L : ℝ} (hL : 0 ≤ L)
    (hw : ContinuousOn w (Icc 0 L))
    (hsl : ∀ x ∈ Icc 0 L, G ≤ w x → ∀ ρ, -c * w x < ρ → ∃ᶠ z in 𝓝[>] x, slope w x z < ρ)
    (hnn : ∀ x, 0 ≤ w x) :
    w L ≤ Real.exp (-c * L) * w 0 ∨ ∃ r ∈ Icc 0 L, w L ≤ Real.exp (-c * (L - r)) * G := by
  by_cases hex : ∃ r ∈ Icc 0 L, w r ≤ G
  · right
    have hSc : IsClosed (Icc 0 L ∩ w ⁻¹' Iic G) :=
      hw.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hSk : IsCompact (Icc 0 L ∩ w ⁻¹' Iic G) :=
      isCompact_Icc.of_isClosed_subset hSc inter_subset_left
    have hSne : (Icc 0 L ∩ w ⁻¹' Iic G).Nonempty := by
      obtain ⟨r, hr, hr'⟩ := hex
      exact ⟨r, hr, hr'⟩
    have hmem := hSk.sSup_mem hSne
    have hub : ∀ x ∈ Icc 0 L ∩ w ⁻¹' Iic G, x ≤ sSup (Icc 0 L ∩ w ⁻¹' Iic G) :=
      fun x hx => le_csSup hSk.bddAbove hx
    obtain ⟨⟨h0r, hrL⟩, hwr⟩ := hmem
    have hwr' : w (sSup (Icc 0 L ∩ w ⁻¹' Iic G)) ≤ G := hwr
    rcases eq_or_lt_of_le hrL with heq | hlt
    · refine ⟨L, ⟨hL, le_rfl⟩, ?_⟩
      rw [heq] at hwr'
      simpa using hwr'
    · set r0 := sSup (Icc 0 L ∩ w ⁻¹' Iic G) with hr0
      have hgt : ∀ x ∈ Ioc r0 L, G < w x := by
        intro x hx
        by_contra hle
        push Not at hle
        have := hub x ⟨⟨by linarith [hx.1], hx.2⟩, hle⟩
        linarith [hx.1]
      have hGr : G ≤ w r0 := by
        have hct : ContinuousWithinAt w (Ioc r0 L) r0 :=
          (hw r0 ⟨h0r, hrL⟩).mono (fun x hx => ⟨by linarith [hx.1], hx.2⟩)
        haveI : (𝓝[Ioc r0 L] r0).NeBot := by
          rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioc hlt.ne]
          exact ⟨le_rfl, hlt.le⟩
        exact ge_of_tendsto hct (eventually_nhdsWithin_of_forall fun x hx => (hgt x hx).le)
      have hG' : ∀ x ∈ Ico r0 L, G ≤ w x := by
        intro x hx
        rcases eq_or_lt_of_le hx.1 with h | h
        · rw [← h]; exact hGr
        · exact (hgt x ⟨h, hx.2.le⟩).le
      have := exp_bound (w := w) (c := c) (G := G) hrL (hw.mono (Icc_subset_Icc h0r le_rfl))
        (fun x hx => hsl x ⟨by linarith [hx.1], hx.2.le⟩) hG' (hnn r0)
      refine ⟨r0, ⟨h0r, hrL⟩, this.trans ?_⟩
      exact mul_le_mul_of_nonneg_left hwr' (Real.exp_pos _).le
  · left
    push Not at hex
    have := exp_bound (r0 := 0) hL hw (fun x hx => hsl x ⟨hx.1, hx.2.le⟩)
      (fun x hx => (hex x ⟨hx.1, hx.2.le⟩).le) (hnn 0)
    simpa using this

lemma slope_freq {X U : Type*} [NormedAddCommGroup X] [NormedAddCommGroup U]
    (S : ImpulsiveISS.FixedDwell.System X U) (V : X → ℝ≥0) (γ : ℝ≥0 → ℝ≥0) (c : ℝ)
    (h0 : ∀ (x : X) (u : ℝ → U), S.flow 0 x u = x)
    (hcoc : ∀ (x : X) (u : ℝ → U), ImpulsiveISS.FixedDwell.IsPCInput u → ∀ s t : ℝ, 0 ≤ s →
      0 ≤ t → S.flow (t + s) x u = S.flow t (S.flow s x u) (ImpulsiveISS.FixedDwell.shift u s))
    (hγm : Monotone γ)
    (hlie : ∀ (x : X) (ξ : U) (u : ℝ → U), ImpulsiveISS.FixedDwell.IsPCInput u → u 0 = ξ →
      γ ‖ξ‖₊ ≤ V x →
      ImpulsiveISS.FixedDwell.lieDeriv S V x u ≤ (((-c * (V x : ℝ)) : ℝ) : EReal))
    {x : X} {v : ℝ → U} (hv : ImpulsiveISS.FixedDwell.IsPCInput v) {M : ℝ≥0}
    (hM : ∀ t : ℝ, 0 ≤ t → ‖v t‖₊ ≤ M) {r : ℝ} (hr : 0 ≤ r)
    (hG : ((γ M : ℝ≥0) : ℝ) ≤ (V (S.flow r x v) : ℝ)) (ρ : ℝ)
    (hρ : -c * (V (S.flow r x v) : ℝ) < ρ) :
    ∃ᶠ z in 𝓝[>] r, slope (fun t => (V (S.flow t x v) : ℝ)) r z < ρ := by
  have hv' := shift_isPC hv hr
  have hξ : γ ‖ImpulsiveISS.FixedDwell.shift v r 0‖₊ ≤ V (S.flow r x v) := by
    have h1 : γ ‖ImpulsiveISS.FixedDwell.shift v r 0‖₊ ≤ γ M := hγm (by
      simp only [ImpulsiveISS.FixedDwell.shift, zero_add]; exact hM r hr)
    exact h1.trans (by exact_mod_cast hG)
  have hL := hlie (S.flow r x v) _ _ hv' rfl hξ
  unfold ImpulsiveISS.FixedDwell.lieDeriv diniUpperRight at hL
  have hlt := hL.trans_lt (EReal.coe_lt_coe_iff.2 hρ)
  have hev := Filter.eventually_lt_of_limsup_lt hlt
  have htend : Tendsto (fun z : ℝ => z - r) (𝓝[>] r) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Tendsto (fun z : ℝ => z - r) (𝓝 r) (𝓝 (r - r)) :=
        (continuous_id.sub continuous_const).tendsto r
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [Set.mem_Ioi] at hz ⊢
      linarith
  have hev2 := htend.eventually hev
  refine Filter.Eventually.frequently ?_
  filter_upwards [hev2, self_mem_nhdsWithin] with z hz hzr
  simp only [Set.mem_Ioi] at hzr
  rw [EReal.coe_lt_coe_iff] at hz
  rw [slope_def_field]
  have e1 : S.flow (0 + (z - r)) (S.flow r x v) (ImpulsiveISS.FixedDwell.shift v r) =
      S.flow z x v := by
    rw [zero_add, ← hcoc x v hv r (z - r) hr (by linarith), sub_add_cancel]
  rw [e1, h0] at hz
  exact hz

lemma kinf_inverse {ψ : ℝ≥0 → ℝ≥0} (hψ : IsKInf ψ) :
    ∃ inv : ℝ≥0 → ℝ≥0, Continuous inv ∧ StrictMono inv ∧ inv 0 = 0 ∧
      (∀ y, ψ (inv y) = y) ∧ (∀ x, inv (ψ x) = x) := by
  obtain ⟨⟨hc, hm, h0⟩, hub⟩ := hψ
  have hsurj : Function.Surjective ψ := by
    intro y
    rw [not_bddAbove_iff] at hub
    obtain ⟨_, ⟨a, rfl⟩, ha⟩ := hub y
    have := intermediate_value_Icc (zero_le : (0:ℝ≥0) ≤ a) hc.continuousOn
    obtain ⟨x, -, hx⟩ := this ⟨by rw [h0]; exact zero_le, ha.le⟩
    exact ⟨x, hx⟩
  let e := StrictMono.orderIsoOfSurjective ψ hm hsurj
  have he : ∀ x, e x = ψ x := fun x => rfl
  refine ⟨e.symm, e.symm.continuous, e.symm.strictMono, ?_, fun y => ?_, fun x => ?_⟩
  · have h00 : e 0 = 0 := (he 0).trans h0
    calc e.symm 0 = e.symm (e 0) := by rw [h00]
      _ = 0 := e.symm_apply_apply 0
  · rw [← he, e.apply_symm_apply]
  · rw [← he, e.symm_apply_apply]

end P8698

open P8698

-- Theorem 5, p. 11 (Dashkovskiy-Mironchenko), corrected max-form jump clause.
open NNReal ImpulsiveISS.AvgDwell in
theorem solution {X U : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    (S : ImpulsiveISS.FixedDwell.System X U) (V : X → ℝ≥0) (ψ₁ ψ₂ γ : ℝ≥0 → ℝ≥0)
    (c d : ℝ) (h : ℝ≥0 → ℝ) (g : ℝ≥0 → ℝ≥0)
    (hS : ImpulsiveISS.FixedDwell.IsImpulsiveSystem S)
    (hV : IsExpLyapunov S V ψ₁ ψ₂ γ c d)
    (hd : d ≠ 0)
    (hh : ∀ r, 0 < h r)
    (hg : ImpulsiveISS.FixedDwell.IsL g)
    (hdom : ∀ r, h r ≤ (g r : ℝ)) :
    UniformISS S (fun τ => IsGADT τ c d h) := by
  obtain ⟨h0, hcoc, hcont, -, -⟩ := hS
  obtain ⟨hVc, hψ₁, hψ₂, hγ, hsand, hlie, hjump⟩ := hV
  obtain ⟨hgc, hga, hgt⟩ := hg
  obtain ⟨inv, hinvc, hinvm, hinv0, -, hinvψ⟩ := kinf_inverse hψ₁
  have gpos : ∀ r, 0 < g r := fun r => lt_of_le_of_lt zero_le (hga (lt_add_one r))
  refine ⟨fun r t => inv (g t * ψ₂ r), fun M => inv (g 0 * γ M), ?_, ?_, ?_⟩
  · refine ⟨?_, fun t => ⟨?_, ?_, ?_⟩, fun r hr => ⟨?_, ?_, ?_⟩⟩
    · show Continuous (fun p : ℝ≥0 × ℝ≥0 => inv (g p.2 * ψ₂ p.1))
      exact hinvc.comp ((hgc.comp continuous_snd).mul (hψ₂.1.1.comp continuous_fst))
    · exact hinvc.comp (continuous_const.mul hψ₂.1.1)
    · intro a b hab
      exact hinvm (mul_lt_mul_of_pos_left (hψ₂.1.2.1 hab) (gpos t))
    · simp [hψ₂.1.2.2, hinv0]
    · exact hinvc.comp (hgc.mul continuous_const)
    · have hψr : 0 < ψ₂ r := by
        have := hψ₂.1.2.1 hr
        rwa [hψ₂.1.2.2] at this
      intro a b hab
      exact hinvm (mul_lt_mul_of_pos_right (hga hab) hψr)
    · have h1 : Tendsto (fun t => g t * ψ₂ r) atTop (𝓝 (0 * ψ₂ r)) := hgt.mul_const _
      rw [zero_mul] at h1
      have h2 := (hinvc.tendsto 0).comp h1
      rw [hinv0] at h2
      exact h2
  · refine ⟨⟨hinvc.comp (continuous_const.mul hγ.1.1),
      fun a b hab => hinvm (mul_lt_mul_of_pos_left (hγ.1.2.1 hab) (gpos 0)),
      by simp [hγ.1.2.2, hinv0]⟩, ?_⟩
    rw [not_bddAbove_iff]
    intro B
    have hub := hγ.2
    rw [not_bddAbove_iff] at hub
    obtain ⟨_, ⟨M, rfl⟩, hM⟩ := hub (ψ₁ (B + 1) / g 0)
    refine ⟨inv (g 0 * γ M), ⟨M, rfl⟩, ?_⟩
    have h1 : ψ₁ (B + 1) < g 0 * γ M := by
      have := (div_lt_iff₀ (gpos 0)).1 hM
      rwa [mul_comm] at this
    calc B < B + 1 := lt_add_one B
      _ = inv (ψ₁ (B + 1)) := (hinvψ _).symm
      _ < inv (g 0 * γ M) := hinvm h1
  · intro τ hτG x₀ u hu M hM t ht
    obtain ⟨hτ, hgadt⟩ := hτG
    -- notation
    set G : ℝ := ((γ M : ℝ≥0) : ℝ) with hGdef
    set V0 : ℝ := ((V x₀ : ℝ≥0) : ℝ) with hV0
    set L0 : ℝ := Real.log (g 0) with hL0
    let ex : ℝ → ℝ := fun t => -(d * (count τ t 0 : ℝ)) - c * t
    have hex : ∀ t, ex t = -(d * (count τ t 0 : ℝ)) - c * t := fun t => rfl
    have hγm : Monotone γ := hγ.1.2.1.monotone
    -- admissibility from the dwell-time condition
    have hadm : ∀ σ t', 0 ≤ σ → σ ≤ t' → ex t' - ex σ ≤ L0 := by
      intro σ t' hσ hσt
      have h1 := hgadt σ t' hσ hσt
      rw [count_sub hτ, Nat.cast_sub (count_mono hτ hσt)] at h1
      have hl : Real.log (h (t' - σ).toNNReal) ≤ L0 :=
        Real.log_le_log (hh _) ((hdom _).trans (by exact_mod_cast hga.antitone zero_le))
      rw [hex, hex]
      nlinarith
    have hadmP : ∀ k : ℕ, ∀ σ t', epoch τ k ≤ σ → σ ≤ τ k → σ ≤ t' →
        ex t' - (-(d * (k : ℝ)) - c * σ) ≤ L0 := by
      have hlt : ∀ k : ℕ, ∀ σ t', epoch τ k ≤ σ → σ < τ k → σ ≤ t' →
          ex t' - (-(d * (k : ℝ)) - c * σ) ≤ L0 := by
        intro k σ t' h1 h2 h3
        have hc := count_piece hτ h1 h2
        have := hadm σ t' ((epoch_nonneg hτ k).trans h1) h3
        rw [hex σ, hc] at this
        exact this
      intro k σ t' h1 h2 h3
      rcases eq_or_lt_of_le h2 with heq | h2'
      · have hT : Tendsto (fun s : ℝ => ex t' - (-(d * (k : ℝ)) - c * s)) (𝓝[<] (τ k))
            (𝓝 (ex t' - (-(d * (k : ℝ)) - c * τ k))) := by
          apply Tendsto.mono_left _ nhdsWithin_le_nhds
          apply Continuous.tendsto
          fun_prop
        rw [heq]
        refine le_of_tendsto hT ?_
        filter_upwards [Ioo_mem_nhdsLT (epoch_lt hτ k)] with s hs
        exact hlt k s t' hs.1.le hs.2 (by linarith [hs.2])
      · exact hlt k σ t' h1 h2' h3
    -- the invariant
    let Inv : ℝ → ℝ → ℝ → Prop := fun a T v =>
      v ≤ Real.exp a * V0 ∨ ∃ E : ℝ, (∀ t', T ≤ t' → ex t' - E ≤ L0) ∧ v ≤ Real.exp (a - E) * G
    -- flow comparison on one piece
    have hFL : ∀ (x : X) (e : ℝ), 0 ≤ e → ∀ L, 0 ≤ L →
        (V (S.flow L x (ImpulsiveISS.FixedDwell.shift u e)) : ℝ) ≤
            Real.exp (-c * L) * (V x : ℝ) ∨
          ∃ r ∈ Icc 0 L, (V (S.flow L x (ImpulsiveISS.FixedDwell.shift u e)) : ℝ) ≤
            Real.exp (-c * (L - r)) * G := by
      intro x e he L hL
      have hv := shift_isPC hu he
      have hMv : ∀ t : ℝ, 0 ≤ t → ‖ImpulsiveISS.FixedDwell.shift u e t‖₊ ≤ M :=
        fun t ht => hM (t + e) (by linarith)
      have hw : ContinuousOn (fun r => (V (S.flow r x (ImpulsiveISS.FixedDwell.shift u e)) : ℝ))
          (Icc 0 L) :=
        ((NNReal.continuous_coe.comp hVc).comp_continuousOn (hcont x _ hv)).mono
          Icc_subset_Ici_self
      have := flow_bound (G := G) (c := c) hL hw
        (fun r hr hGr ρ hρ => slope_freq S V γ c h0 hcoc hγm hlie hv hMv hr.1 hGr ρ hρ)
        (fun r => NNReal.coe_nonneg _)
      simpa only [h0] using this
    -- one piece, from the post-jump state
    have hpiece : ∀ k : ℕ, Inv (ex (epoch τ k)) (epoch τ k) (V (post S τ x₀ u k)) →
        ∀ L, 0 ≤ L → L ≤ τ k - epoch τ k →
        Inv (-(d * (k : ℝ)) - c * (epoch τ k + L)) (epoch τ k + L)
          (V (S.flow L (post S τ x₀ u k) (ImpulsiveISS.FixedDwell.shift u (epoch τ k)))) := by
      intro k hk L hL0' hLk
      have hck : ex (epoch τ k) = -(d * (k : ℝ)) - c * epoch τ k := by
        rw [hex, count_piece hτ le_rfl (epoch_lt hτ k)]
      rw [hck] at hk
      have hexp : ∀ E : ℝ, Real.exp (-(d * (k : ℝ)) - c * (epoch τ k + L) - E) =
          Real.exp (-c * L) * Real.exp (-(d * (k : ℝ)) - c * epoch τ k - E) := by
        intro E
        rw [← Real.exp_add]
        ring_nf
      have hexp0 : Real.exp (-(d * (k : ℝ)) - c * (epoch τ k + L)) =
          Real.exp (-c * L) * Real.exp (-(d * (k : ℝ)) - c * epoch τ k) := by
        rw [← Real.exp_add]
        ring_nf
      rcases hFL (post S τ x₀ u k) (epoch τ k) (epoch_nonneg hτ k) L hL0' with h1 | ⟨r, hr, h2⟩
      · rcases hk with hA | ⟨E, hE, hB⟩
        · left
          rw [hexp0, mul_assoc]
          exact h1.trans (mul_le_mul_of_nonneg_left hA (Real.exp_pos _).le)
        · right
          refine ⟨E, fun t' ht' => hE t' (by linarith), ?_⟩
          rw [hexp E, mul_assoc]
          exact h1.trans (mul_le_mul_of_nonneg_left hB (Real.exp_pos _).le)
      · right
        refine ⟨-(d * (k : ℝ)) - c * (epoch τ k + r), fun t' ht' => ?_, ?_⟩
        · exact hadmP k (epoch τ k + r) t' (by linarith [hr.1]) (by linarith [hr.2])
            (by linarith [hr.2])
        · have : -(d * (k : ℝ)) - c * (epoch τ k + L) - (-(d * (k : ℝ)) - c * (epoch τ k + r)) =
              -c * (L - r) := by ring
          rw [this]
          exact h2
    -- all post-jump states
    have hpost : ∀ k : ℕ, Inv (ex (epoch τ k)) (epoch τ k) (V (post S τ x₀ u k)) := by
      intro k
      induction k with
      | zero =>
        left
        have : ex (epoch τ 0) = 0 := by
          rw [hex, epoch_zero, count_eq_of hτ (idx_zero hτ)]
          simp
        rw [this, Real.exp_zero, one_mul]
        exact le_rfl
      | succ k ih =>
        have hp := hpiece k ih (τ k - epoch τ k) (sub_nonneg.2 (epoch_lt hτ k).le) le_rfl
        rw [add_sub_cancel] at hp
        have hpost1 : post S τ x₀ u (k + 1) =
            S.jump (S.flow (τ k - epoch τ k) (post S τ x₀ u k)
              (ImpulsiveISS.FixedDwell.shift u (epoch τ k))) (Function.leftLim u (τ k)) := rfl
        have hck : ex (epoch τ (k + 1)) = -d + (-(d * (k : ℝ)) - c * τ k) := by
          rw [hex, epoch_succ, count_piece hτ (k := k + 1) (le_of_eq (epoch_succ τ k))
            (hτ.1 (Nat.lt_succ_self k))]
          push_cast
          ring
        have hj := hjump (S.flow (τ k - epoch τ k) (post S τ x₀ u k)
              (ImpulsiveISS.FixedDwell.shift u (epoch τ k))) (Function.leftLim u (τ k))
        rw [← hpost1] at hj
        have hξ : γ ‖Function.leftLim u (τ k)‖₊ ≤ γ M :=
          hγm (leftLim_nnnorm_le hu hM (tau_pos hτ k))
        rcases le_max_iff.1 hj with hj1 | hj2
        · have hj1' : (V (post S τ x₀ u (k + 1)) : ℝ) ≤ Real.exp (-d) *
              (V (S.flow (τ k - epoch τ k) (post S τ x₀ u k)
                (ImpulsiveISS.FixedDwell.shift u (epoch τ k))) : ℝ) := by
            have := NNReal.coe_le_coe.2 hj1
            rwa [NNReal.coe_mul, Real.coe_toNNReal _ (Real.exp_pos _).le] at this
          rw [hck]
          rcases hp with hA | ⟨E, hE, hB⟩
          · left
            rw [Real.exp_add, mul_assoc]
            exact hj1'.trans (mul_le_mul_of_nonneg_left hA (Real.exp_pos _).le)
          · right
            refine ⟨E, fun t' ht' => hE t' (by rw [epoch_succ] at ht'; exact ht'), ?_⟩
            rw [add_sub_assoc, Real.exp_add, mul_assoc]
            exact hj1'.trans (mul_le_mul_of_nonneg_left hB (Real.exp_pos _).le)
        · right
          refine ⟨ex (epoch τ (k + 1)), fun t' ht' => ?_, ?_⟩
          · rw [epoch_succ] at ht' ⊢
            exact hadm (τ k) t' (tau_pos hτ k).le ht'
          · rw [sub_self, Real.exp_zero, one_mul]
            exact_mod_cast hj2.trans hξ
    -- the final estimate
    obtain ⟨hk1, hk2⟩ := piece_of hτ ht
    have hfin := hpiece (count τ t 0) (hpost _) (t - epoch τ (count τ t 0))
      (sub_nonneg.2 hk1) (by linarith)
    rw [add_sub_cancel] at hfin
    have htraj : traj S τ x₀ u t = S.flow (t - epoch τ (count τ t 0))
        (post S τ x₀ u (count τ t 0))
        (ImpulsiveISS.FixedDwell.shift u (epoch τ (count τ t 0))) := rfl
    rw [← htraj] at hfin
    have hexT : Real.exp (-(d * ((count τ t 0 : ℕ) : ℝ)) - c * t) ≤ (g t.toNNReal : ℝ) := by
      have h1 := hgadt 0 t le_rfl ht
      simp only [sub_zero] at h1
      calc Real.exp (-(d * ((count τ t 0 : ℕ) : ℝ)) - c * t)
          ≤ Real.exp (Real.log (h t.toNNReal)) := Real.exp_le_exp.2 h1
        _ = h t.toNNReal := Real.exp_log (hh _)
        _ ≤ g t.toNNReal := hdom _
    have hVt : V (traj S τ x₀ u t) ≤ max (g t.toNNReal * ψ₂ ‖x₀‖₊) (g 0 * γ M) := by
      rw [← NNReal.coe_le_coe, NNReal.coe_max, NNReal.coe_mul, NNReal.coe_mul]
      rcases hfin with hA | ⟨E, hE, hB⟩
      · apply le_max_of_le_left
        calc (V (traj S τ x₀ u t) : ℝ) ≤ Real.exp (-(d * ((count τ t 0 : ℕ) : ℝ)) - c * t) * V0 := hA
          _ ≤ (g t.toNNReal : ℝ) * V0 := mul_le_mul_of_nonneg_right hexT (NNReal.coe_nonneg _)
          _ ≤ (g t.toNNReal : ℝ) * (ψ₂ ‖x₀‖₊ : ℝ) :=
            mul_le_mul_of_nonneg_left (by exact_mod_cast (hsand x₀).2) (NNReal.coe_nonneg _)
      · apply le_max_of_le_right
        have hE' := hE t le_rfl
        rw [hex] at hE'
        have hle : Real.exp (-(d * ((count τ t 0 : ℕ) : ℝ)) - c * t - E) ≤ (g 0 : ℝ) := by
          calc Real.exp (-(d * ((count τ t 0 : ℕ) : ℝ)) - c * t - E)
              ≤ Real.exp L0 := Real.exp_le_exp.2 hE'
            _ = g 0 := Real.exp_log (by exact_mod_cast gpos 0)
        calc (V (traj S τ x₀ u t) : ℝ)
            ≤ Real.exp (-(d * ((count τ t 0 : ℕ) : ℝ)) - c * t - E) * G := hB
          _ ≤ (g 0 : ℝ) * G := mul_le_mul_of_nonneg_right hle (NNReal.coe_nonneg _)
    have hψt : ψ₁ ‖traj S τ x₀ u t‖₊ ≤ max (g t.toNNReal * ψ₂ ‖x₀‖₊) (g 0 * γ M) :=
      (hsand _).1.trans hVt
    show ‖traj S τ x₀ u t‖₊ ≤ inv (g t.toNNReal * ψ₂ ‖x₀‖₊) + inv (g 0 * γ M)
    calc ‖traj S τ x₀ u t‖₊ = inv (ψ₁ ‖traj S τ x₀ u t‖₊) := (hinvψ _).symm
      _ ≤ inv (max (g t.toNNReal * ψ₂ ‖x₀‖₊) (g 0 * γ M)) := hinvm.monotone hψt
      _ = max (inv (g t.toNNReal * ψ₂ ‖x₀‖₊)) (inv (g 0 * γ M)) := hinvm.monotone.map_max
      _ ≤ inv (g t.toNNReal * ψ₂ ‖x₀‖₊) + inv (g 0 * γ M) :=
        max_le (le_add_right le_rfl) (le_add_left le_rfl)
