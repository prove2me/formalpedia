-- Prove2me | solution 1 for NondomArb.Superhedge.theorem_3_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T06:42:11.450566+00:00
-- url     : https://prove2.me/submissions/a688711c-1b25-4a1e-b9f6-d87ab409b79f

import Mathlib
import Definitions.Def_NondomArb_Superhedge_Basic
import Definitions.Def_NondomArb_Superhedge_OnePeriod
import Definitions.Def_NondomArb_Superhedge_General
import Theorems.Thm_NondomArb_Superhedge_theorem_2_2
import Theorems.Thm_NondomArb_Superhedge_theorem_2_3
import Theorems.Thm_NondomArb_Superhedge_lemma_3_5
import Theorems.Thm_NondomArb_Superhedge_lemma_3_6
open MeasureTheory Filter Topology NondomArb.Superhedge.OnePeriod
open NondomArb.Superhedge

namespace Thm34Aux

/-! ### Quasi-sure bookkeeping -/

section QSlemmas
variable {Ω : Type*} [MeasurableSpace Ω] {Pset : Set (Measure Ω)}

lemma qs_mono {p q : Ω → Prop} (hp : QS Pset p) (h : ∀ ω, p ω → q ω) : QS Pset q := by
  obtain ⟨A, hA, hsub, h0⟩ := hp
  exact ⟨A, hA, fun ω hω => hsub (fun hp => hω (h ω hp)), h0⟩

lemma qs_always (p : Ω → Prop) (h : ∀ ω, p ω) : QS Pset p :=
  ⟨∅, MeasurableSet.empty, fun ω hω => (hω (h ω)).elim, fun _ _ => measure_empty⟩

lemma ae_of_qs {p : Ω → Prop} (hp : QS Pset p) {Q : Measure Ω} (hQ : AbsContSet Q Pset) :
    ∀ᵐ ω ∂Q, p ω := by
  obtain ⟨A, _, hsub, h0⟩ := hp
  obtain ⟨P, hP, hQP⟩ := hQ
  exact measure_mono_null hsub (hQP (h0 P hP))

end QSlemmas

/-! ### Extended expectations -/

section ExtExp
variable {Ω : Type*} [MeasurableSpace Ω]

lemma ereal_sub_fin {a b : ENNReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (a : EReal) - (b : EReal) = ((a.toReal - b.toReal : ℝ) : EReal) := by
  lift a to NNReal using ha
  lift b to NNReal using hb
  show ((a:ENNReal):EReal) - ((b:ENNReal):EReal) = (((a:ℝ) - (b:ℝ) : ℝ) : EReal)
  rw [EReal.coe_sub]; rfl

lemma extExp_coe_eq (Q : Measure Ω) (u : Ω → ℝ) :
    extExp Q (fun ω => ((u ω : ℝ) : EReal)) =
      ((∫⁻ ω, ENNReal.ofReal (u ω) ∂Q : ENNReal) : EReal) -
        ((∫⁻ ω, ENNReal.ofReal (-u ω) ∂Q : ENNReal) : EReal) := by
  unfold NondomArb.Superhedge.extExp
  congr 3

lemma extExp_of_integrable (Q : Measure Ω) {u : Ω → ℝ} (hu : Integrable u Q) :
    extExp Q (fun ω => ((u ω : ℝ) : EReal)) = ((∫ ω, u ω ∂Q : ℝ) : EReal) := by
  rw [extExp_coe_eq]
  have h1 : ∫⁻ ω, ENNReal.ofReal (u ω) ∂Q ≠ ⊤ := hu.lintegral_lt_top.ne
  have h2 : ∫⁻ ω, ENNReal.ofReal (-u ω) ∂Q ≠ ⊤ := hu.neg.lintegral_lt_top.ne
  rw [ereal_sub_fin h1 h2, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hu]

lemma extExp_le_integral (Q : Measure Ω) {u G : Ω → ℝ} (hG : Integrable G Q)
    (hle : ∀ᵐ ω ∂Q, u ω ≤ G ω) :
    extExp Q (fun ω => ((u ω : ℝ) : EReal)) ≤ ((∫ ω, G ω ∂Q : ℝ) : EReal) := by
  rw [extExp_coe_eq, ← extExp_of_integrable Q hG, extExp_coe_eq]
  refine EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.mpr ?_)
    (EReal.coe_ennreal_le_coe_ennreal_iff.mpr ?_)
  · exact lintegral_mono_ae (hle.mono fun ω h => ENNReal.ofReal_le_ofReal h)
  · exact lintegral_mono_ae (hle.mono fun ω h => ENNReal.ofReal_le_ofReal (by linarith))

lemma extExp_mono (Q : Measure Ω) {u v : Ω → ℝ} (h : ∀ ω, u ω ≤ v ω) :
    extExp Q (fun ω => ((u ω : ℝ) : EReal)) ≤ extExp Q (fun ω => ((v ω : ℝ) : EReal)) := by
  rw [extExp_coe_eq, extExp_coe_eq]
  refine EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.mpr ?_)
    (EReal.coe_ennreal_le_coe_ennreal_iff.mpr ?_)
  · exact lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (h ω)
  · exact lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (by linarith [h ω])

/-- Lemma A.2 in the one-period market: superhedging bounds the expectation under `Q ∈ 𝒬`. -/
lemma extExp_le_of_superhedge {Pset : Set (Measure Ω)} {d : ℕ} {ΔS : Ω → (Fin d → ℝ)}
    {Q : Measure Ω} (hQ : Q ∈ MartMeasures Pset ΔS) (f : Ω → ℝ) (x : ℝ) (H : Fin d → ℝ)
    (hq : QS Pset (fun ω => f ω ≤ x + H ⬝ᵥ ΔS ω)) :
    extExp Q (fun ω => ((f ω : ℝ) : EReal)) ≤ (x : EReal) := by
  obtain ⟨hprob, hac, hint, hzero⟩ := hQ
  haveI := hprob
  have hcomp : ∀ i, Integrable (fun ω => ΔS ω i) Q := fun i => hint.eval i
  have hdot : Integrable (fun ω => H ⬝ᵥ ΔS ω) Q := by
    show Integrable (fun ω => ∑ i, H i * ΔS ω i) Q
    exact integrable_finsetSum _ fun i _ => (hcomp i).const_mul (H i)
  have hG : Integrable (fun ω => x + H ⬝ᵥ ΔS ω) Q := (integrable_const x).add hdot
  have hval : ∫ ω, (x + H ⬝ᵥ ΔS ω) ∂Q = x := by
    rw [integral_add (integrable_const x) hdot]
    have : ∫ ω, H ⬝ᵥ ΔS ω ∂Q = 0 := by
      show ∫ ω, ∑ i, H i * ΔS ω i ∂Q = 0
      rw [integral_finsetSum _ fun i _ => (hcomp i).const_mul (H i)]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [integral_const_mul, ← eval_integral hcomp i, hzero]
      simp
    rw [this]; simp
  have := extExp_le_integral Q hG (ae_of_qs hq hac)
  rwa [hval] at this

end ExtExp

/-! ### The one-period market as a `T = 1` instance of §2 -/

section Bridge
variable {Ω : Type*} [m : MeasurableSpace Ω]

/-- The filtration `F_0 = {∅, Ω}`, `F_t = F` for `t ≥ 1`. -/
def filt : Filtration ℕ m where
  seq t := if t = 0 then ⊥ else m
  mono' := by
    intro i j hij
    by_cases hi : i = 0
    · simp only [hi, if_true]; exact bot_le
    · have hj : j ≠ 0 := by omega
      simp only [hi, hj, if_false]; exact le_rfl
  le' := by
    intro i
    by_cases hi : i = 0
    · simp only [hi, if_true]; exact bot_le
    · simp only [hi, if_false]; exact le_rfl

lemma filt_zero : (filt : Filtration ℕ m) 0 = ⊥ := by
  show (if (0:ℕ) = 0 then ⊥ else m) = ⊥
  simp

/-- `S_0 = 0`, `S_t = ΔS` for `t ≥ 1`. -/
def Sproc {d : ℕ} (ΔS : Ω → (Fin d → ℝ)) : ℕ → Ω → (Fin d → ℝ) :=
  fun t ω => if t = 0 then 0 else ΔS ω

lemma Sproc_meas {d : ℕ} {ΔS : Ω → (Fin d → ℝ)} (hΔS : Measurable ΔS) :
    ∀ t ≤ 1, Measurable (Sproc ΔS t) := by
  intro t _
  by_cases ht : t = 0
  · have : Sproc ΔS t = fun _ => 0 := by funext ω; simp [Sproc, ht]
    rw [this]; exact measurable_const
  · have : Sproc ΔS t = ΔS := by funext ω; simp [Sproc, ht]
    rw [this]; exact hΔS

lemma wealth_one {d : ℕ} (ΔS : Ω → (Fin d → ℝ)) (H : ℕ → Ω → (Fin d → ℝ)) (ω : Ω) :
    NondomArb.Superhedge.General.wealth 1 (Sproc ΔS) H ω = H 0 ω ⬝ᵥ ΔS ω := by
  simp [NondomArb.Superhedge.General.wealth, Sproc]

lemma pred_const {d : ℕ} (c : Fin d → ℝ) :
    NondomArb.Superhedge.General.IsPredictable (filt : Filtration ℕ m) 1 (fun _ _ => c) :=
  fun _ _ => measurable_const

lemma pred_is_const [Nonempty Ω] {d : ℕ} {H : ℕ → Ω → (Fin d → ℝ)}
    (hH : NondomArb.Superhedge.General.IsPredictable (filt : Filtration ℕ m) 1 H) :
    ∃ c : Fin d → ℝ, ∀ ω, H 0 ω = c := by
  have h0 := hH 0 (by norm_num)
  rw [filt_zero] at h0
  obtain ⟨ω0⟩ := ‹Nonempty Ω›
  refine ⟨H 0 ω0, fun ω => ?_⟩
  have hs := h0 (measurableSet_singleton (H 0 ω0))
  rcases MeasurableSpace.measurableSet_bot_iff.mp hs with h | h
  · have : ω0 ∈ H 0 ⁻¹' {H 0 ω0} := rfl
    rw [h] at this; exact this.elim
  · have : ω ∈ H 0 ⁻¹' {H 0 ω0} := by rw [h]; trivial
    exact this

lemma nonempty_of_model {Pset : Set (Measure Ω)} (hP : IsConvexModelSet Pset) : Nonempty Ω := by
  obtain ⟨⟨P, hP0⟩, hprob, _⟩ := hP
  haveI := hprob P hP0
  by_contra hne
  rw [not_nonempty_iff] at hne
  have : P Set.univ = 0 := by rw [Set.univ_eq_empty_iff.mpr hne]; exact measure_empty
  rw [measure_univ] at this; exact one_ne_zero this

lemma NA_bridge {Pset : Set (Measure Ω)} (hP : IsConvexModelSet Pset) {d : ℕ}
    {ΔS : Ω → (Fin d → ℝ)} (hNA : NA Pset ΔS) :
    NondomArb.Superhedge.General.NA Pset (filt : Filtration ℕ m) 1 (Sproc ΔS) := by
  haveI := nonempty_of_model hP
  intro H hH hge
  obtain ⟨c, hc⟩ := pred_is_const hH
  have hge' : QS Pset (fun ω => 0 ≤ c ⬝ᵥ ΔS ω) :=
    qs_mono hge fun ω h => by rw [wealth_one, hc] at h; exact h
  exact qs_mono (hNA c hge') fun ω h => by rw [wealth_one, hc]; exact h

lemma price_bridge {Pset : Set (Measure Ω)} (hP : IsConvexModelSet Pset) {d : ℕ}
    (ΔS : Ω → (Fin d → ℝ)) (f : Ω → ℝ) :
    NondomArb.Superhedge.General.price Pset (filt : Filtration ℕ m) 1 (Sproc ΔS) f =
      price Pset ΔS f := by
  haveI := nonempty_of_model hP
  unfold NondomArb.Superhedge.General.price price
  congr 1
  ext z
  constructor
  · rintro ⟨x', rfl, H, hH, hq⟩
    obtain ⟨c, hc⟩ := pred_is_const hH
    exact ⟨x', rfl, c, qs_mono hq fun ω h => by rw [wealth_one, hc] at h; exact h⟩
  · rintro ⟨x', rfl, c, hq⟩
    exact ⟨x', rfl, fun _ _ => c, pred_const c,
      qs_mono hq fun ω h => by rw [wealth_one]; exact h⟩

/-- Theorem 2.3 in the one-period market. -/
lemma attain {Pset : Set (Measure Ω)} (hP : IsConvexModelSet Pset) {d : ℕ}
    {ΔS : Ω → (Fin d → ℝ)} (hΔS : Measurable ΔS) (hNA : NA Pset ΔS) (f : Ω → ℝ)
    (hf : Measurable f) :
    ⊥ < price Pset ΔS f ∧ ∃ c : Fin d → ℝ,
      QS Pset (fun ω => (f ω : EReal) ≤ price Pset ΔS f + ((c ⬝ᵥ ΔS ω : ℝ) : EReal)) := by
  haveI := nonempty_of_model hP
  obtain ⟨h1, H, hH, hq⟩ := theorem_2_3 (filt : Filtration ℕ m) Pset hP.1 hP.2.1 (Sproc ΔS)
    (Sproc_meas hΔS) (NA_bridge hP hNA) f hf
  rw [price_bridge hP] at h1 hq
  obtain ⟨c, hc⟩ := pred_is_const hH
  exact ⟨h1, c, qs_mono hq fun ω h => by rw [wealth_one, hc] at h; exact h⟩

/-- Theorem 2.2 in the one-period market. -/
lemma closed {Pset : Set (Measure Ω)} (hP : IsConvexModelSet Pset) {d : ℕ}
    {ΔS : Ω → (Fin d → ℝ)} (hΔS : Measurable ΔS) (hNA : NA Pset ΔS) (W : ℕ → Ω → ℝ)
    (hW : ∀ n, Measurable (W n)) (c : ℕ → Fin d → ℝ)
    (hWc : ∀ n, QS Pset (fun ω => W n ω ≤ c n ⬝ᵥ ΔS ω)) (Wl : Ω → ℝ) (hWl : Measurable Wl)
    (hconv : QS Pset (fun ω => Tendsto (fun n => W n ω) atTop (𝓝 (Wl ω)))) :
    ∃ c0 : Fin d → ℝ, QS Pset (fun ω => Wl ω ≤ c0 ⬝ᵥ ΔS ω) := by
  haveI := nonempty_of_model hP
  have hdot : ∀ c : Fin d → ℝ, Measurable fun ω => c ⬝ᵥ ΔS ω := by
    intro c
    show Measurable fun ω => ∑ i, c i * ΔS ω i
    exact Finset.measurable_sum _ fun i _ => measurable_const.mul ((measurable_pi_apply i).comp hΔS)
  have hC : ∀ n, NondomArb.Superhedge.General.InCone Pset (filt : Filtration ℕ m) 1
      (Sproc ΔS) (W n) := by
    intro n
    refine ⟨fun _ _ => c n, pred_const _, fun ω => max (c n ⬝ᵥ ΔS ω - W n ω) 0,
      ((hdot (c n)).sub (hW n)).max measurable_const, fun ω => le_max_right _ _, ?_⟩
    refine qs_mono (hWc n) fun ω h => ?_
    show W n ω = NondomArb.Superhedge.General.wealth 1 (Sproc ΔS) (fun _ _ => c n) ω -
      max (c n ⬝ᵥ ΔS ω - W n ω) 0
    rw [wealth_one, max_eq_left (by linarith)]; ring
  obtain ⟨H, hH, K, _, hK0, hq⟩ := theorem_2_2 (filt : Filtration ℕ m) Pset hP.1 hP.2.1
    (Sproc ΔS) (Sproc_meas hΔS) (NA_bridge hP hNA) W hW hC Wl hWl hconv
  obtain ⟨c0, hc0⟩ := pred_is_const hH
  refine ⟨c0, qs_mono hq fun ω h => ?_⟩
  have h' : Wl ω = NondomArb.Superhedge.General.wealth 1 (Sproc ΔS) H ω - K ω := h
  rw [wealth_one, hc0] at h'
  linarith [hK0 ω]

end Bridge

end Thm34Aux

open Thm34Aux in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (Pset : Set (Measure Ω))
    (hP : IsConvexModelSet Pset) {d : ℕ} (ΔS : Ω → (Fin d → ℝ)) (hΔS : Measurable ΔS)
    (hNA : NA Pset ΔS) (f : Ω → ℝ) (hf : Measurable f) :
    (⨆ Q ∈ MartMeasures Pset ΔS, extExp Q (fun ω => (f ω : EReal))) = price Pset ΔS f ∧
      ⊥ < price Pset ΔS f ∧
      ∃ H : Fin d → ℝ,
        QS Pset (fun ω => (f ω : EReal) ≤ price Pset ΔS f + ((H ⬝ᵥ ΔS ω : ℝ) : EReal)) := by
  classical
  obtain ⟨hbot, hatt⟩ := attain hP hΔS hNA f hf
  refine ⟨?_, hbot, hatt⟩
  -- membership in the superhedging set
  have hmem : ∀ (u : Ω → ℝ) (y : ℝ), price Pset ΔS u < (y : EReal) →
      ∃ x' : ℝ, x' < y ∧ ∃ H : Fin d → ℝ, QS Pset (fun ω => u ω ≤ x' + H ⬝ᵥ ΔS ω) := by
    intro u y hy
    obtain ⟨z, hz, hzy⟩ := sInf_lt_iff.mp hy
    obtain ⟨x', rfl, H, hq⟩ := hz
    exact ⟨x', by exact_mod_cast hzy, H, hq⟩
  have hle_price : ∀ (u : Ω → ℝ) (x' : ℝ) (H : Fin d → ℝ),
      QS Pset (fun ω => u ω ≤ x' + H ⬝ᵥ ΔS ω) → price Pset ΔS u ≤ (x' : EReal) :=
    fun u x' H hq => sInf_le ⟨x', rfl, H, hq⟩
  -- "≤": Lemma A.2
  have hsup_le : ∀ u : Ω → ℝ,
      (⨆ Q ∈ MartMeasures Pset ΔS, extExp Q (fun ω => (u ω : EReal))) ≤ price Pset ΔS u := by
    intro u
    refine iSup₂_le fun Q hQ => le_sInf ?_
    rintro z ⟨x', rfl, H, hq⟩
    exact extExp_le_of_superhedge hQ u x' H hq
  -- "≥" for claims bounded from above
  have hbdd : ∀ u : Ω → ℝ, Measurable u → (∃ C : ℝ, ∀ ω, u ω ≤ C) →
      price Pset ΔS u ≤ ⨆ Q ∈ MartMeasures Pset ΔS, extExp Q (fun ω => (u ω : EReal)) := by
    intro u hu ⟨C, hC⟩
    have hbu := (attain hP hΔS hNA u hu).1
    have htop : price Pset ΔS u ≠ ⊤ := by
      refine ne_top_of_le_ne_top (EReal.coe_ne_top C) (hle_price u C 0 ?_)
      exact qs_always _ fun ω => by simp [hC ω]
    set r := (price Pset ΔS u).toReal with hr
    have hpr : price Pset ΔS u = (r : EReal) := (EReal.coe_toReal htop hbu.ne').symm
    set u' : Ω → ℝ := fun ω => u ω - r with hu'
    have hu'm : Measurable u' := hu.sub_const r
    have hp0 : price Pset ΔS u' = 0 := by
      apply le_antisymm
      · by_contra hcon
        rw [not_le] at hcon
        obtain ⟨ε, hε0, hεp⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
        have hε0' : (0:ℝ) < ε := by exact_mod_cast hε0
        obtain ⟨x', hx', H, hq⟩ := hmem u (r + ε) (by rw [hpr]; exact_mod_cast (by linarith))
        have : price Pset ΔS u' ≤ ((x' - r : ℝ) : EReal) :=
          hle_price u' (x' - r) H (qs_mono hq fun ω h => by simp only [u']; linarith)
        have h2 : ((x' - r : ℝ) : EReal) < (ε : EReal) := by exact_mod_cast (by linarith)
        exact absurd (lt_trans (this.trans_lt h2) hεp) (lt_irrefl _)
      · refine le_sInf ?_
        rintro z ⟨x', rfl, H, hq⟩
        have h1 : price Pset ΔS u ≤ ((x' + r : ℝ) : EReal) :=
          hle_price u (x' + r) H (qs_mono hq fun ω h => by simp only [u'] at h; linarith)
        rw [hpr] at h1
        have : r ≤ x' + r := by exact_mod_cast h1
        exact_mod_cast (by linarith : (0:ℝ) ≤ x')
    obtain ⟨R, hR, hRS, hRf⟩ := lemma_3_5 Pset hP ΔS hΔS hNA u' hu'm hp0
    obtain ⟨c, _, hc⟩ := lemma_3_6 Pset hP ΔS hΔS hNA u' hu'm
    choose Q hQ hQi hQb using fun n => hc (R n) (hR n)
    have hQ0 : Tendsto (fun n => ∫ ω, u' ω ∂(Q n)) atTop (𝓝 0) := by
      have hb : Tendsto (fun n => c * (1 + |∫ ω, u' ω ∂(R n)|) * ‖∫ ω, ΔS ω ∂(R n)‖) atTop
          (𝓝 (c * (1 + |0|) * ‖(0 : Fin d → ℝ)‖)) :=
        ((tendsto_const_nhds.add hRf.abs).const_mul c).mul hRS.norm
      simp only [abs_zero, norm_zero, mul_zero] at hb
      have hdiff : Tendsto (fun n => ∫ ω, u' ω ∂(Q n) - ∫ ω, u' ω ∂(R n)) atTop (𝓝 0) :=
        squeeze_zero_norm (fun n => hQb n) hb
      simpa using hdiff.add hRf
    have hval : ∀ n, extExp (Q n) (fun ω => (u ω : EReal)) =
        ((∫ ω, u' ω ∂(Q n) + r : ℝ) : EReal) := by
      intro n
      haveI := (hQ n).1
      have hui : Integrable u (Q n) := by
        have : u = fun ω => u' ω + r := by funext ω; simp [u']
        rw [this]; exact (hQi n).add (integrable_const r)
      rw [extExp_of_integrable _ hui]
      congr 1
      simp only [u']
      rw [integral_sub hui (integrable_const r)]
      simp
    have hge : ∀ n, ((∫ ω, u' ω ∂(Q n) + r : ℝ) : EReal) ≤
        ⨆ Q ∈ MartMeasures Pset ΔS, extExp Q (fun ω => (u ω : EReal)) := by
      intro n
      rw [← hval n]
      exact le_iSup₂ (f := fun Q (_ : Q ∈ MartMeasures Pset ΔS) =>
        extExp Q (fun ω => (u ω : EReal))) (Q n) (hQ n)
    rw [hpr]
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨s, hs1, hs2⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
    have hs2' : s < r := by exact_mod_cast hs2
    have hev : ∀ᶠ n in atTop, s < ∫ ω, u' ω ∂(Q n) + r := by
      have := (hQ0.add_const r)
      simp only [zero_add] at this
      exact this.eventually (lt_mem_nhds hs2')
    obtain ⟨n, hn⟩ := hev.exists
    have := (hge n).trans_lt hs1
    have h3 : (∫ ω, u' ω ∂(Q n) + r : ℝ) < s := by exact_mod_cast this
    linarith
  -- general case: truncation and closedness
  apply le_antisymm (hsup_le f)
  let fn : ℕ → Ω → ℝ := fun n ω => min (f ω) n
  have hfnm : ∀ n, Measurable (fn n) := fun n => hf.min measurable_const
  have hstep : ∀ n, price Pset ΔS (fn n) ≤
      ⨆ Q ∈ MartMeasures Pset ΔS, extExp Q (fun ω => (f ω : EReal)) := by
    intro n
    refine (hbdd (fn n) (hfnm n) ⟨n, fun ω => min_le_right _ _⟩).trans ?_
    exact iSup₂_mono fun Q _ => extExp_mono Q fun ω => min_le_left _ _
  set α := ⨆ n, price Pset ΔS (fn n) with hα
  have hαle : α ≤ ⨆ Q ∈ MartMeasures Pset ΔS, extExp Q (fun ω => (f ω : EReal)) := iSup_le hstep
  refine le_trans ?_ hαle
  by_cases hαtop : α = ⊤
  · rw [hαtop]; exact le_top
  have hαbot : α ≠ ⊥ := by
    have h0 := (attain hP hΔS hNA (fn 0) (hfnm 0)).1
    exact (lt_of_lt_of_le h0 (le_iSup (fun n => price Pset ΔS (fn n)) 0)).ne'
  set a := α.toReal with ha
  have hαa : α = (a : EReal) := (EReal.coe_toReal hαtop hαbot).symm
  have hW : ∀ n, ∃ c : Fin d → ℝ, QS Pset (fun ω => fn n ω - a ≤ c ⬝ᵥ ΔS ω) := by
    intro n
    obtain ⟨hb, c, hq⟩ := attain hP hΔS hNA (fn n) (hfnm n)
    have hpn : price Pset ΔS (fn n) ≤ (a : EReal) := hαa ▸ le_iSup (fun n => price Pset ΔS (fn n)) n
    have hpt : price Pset ΔS (fn n) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top a) hpn
    have hpr : price Pset ΔS (fn n) = (((price Pset ΔS (fn n)).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal hpt hb.ne').symm
    have hpa : (price Pset ΔS (fn n)).toReal ≤ a := by
      have := hpn; rw [hpr] at this; exact_mod_cast this
    refine ⟨c, qs_mono hq fun ω h => ?_⟩
    rw [hpr, ← EReal.coe_add] at h
    have h' : fn n ω ≤ (price Pset ΔS (fn n)).toReal + c ⬝ᵥ ΔS ω := by exact_mod_cast h
    linarith
  choose c hc using hW
  have hdot : ∀ c : Fin d → ℝ, Measurable fun ω => c ⬝ᵥ ΔS ω := by
    intro c
    show Measurable fun ω => ∑ i, c i * ΔS ω i
    exact Finset.measurable_sum _ fun i _ => measurable_const.mul ((measurable_pi_apply i).comp hΔS)
  have hconv : QS Pset (fun ω => Tendsto (fun n => fn n ω - a) atTop (𝓝 (f ω - a))) := by
    refine qs_always _ fun ω => ?_
    refine (tendsto_const_nhds.congr' ?_)
    obtain ⟨N, hN⟩ := exists_nat_ge (f ω)
    filter_upwards [eventually_ge_atTop N] with n hn
    have : (N:ℝ) ≤ n := by exact_mod_cast hn
    simp only [fn]
    rw [min_eq_left (by linarith)]
  obtain ⟨c0, hc0⟩ := closed hP hΔS hNA (fun n ω => fn n ω - a)
    (fun n => (hfnm n).sub_const a) c hc (fun ω => f ω - a) (hf.sub_const a) hconv
  rw [hαa]
  exact hle_price f a c0 (qs_mono hc0 fun ω h => by linarith)
