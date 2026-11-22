-- Prove2me | solution 1 for MasulloGRH.completedHeckeLFunction_logDeriv_bound_on_good_heights
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:19:34.887954+00:00
-- url     : https://prove2.me/submissions/623580e2-a856-41c9-909f-9b4ad2cddfe0

import Definitions.Def_MasulloGRH_CompletedL
import Theorems.Thm_MasulloGRH_completedHeckeLFunction_logDeriv_local_partial_fraction
import Theorems.Thm_MasulloGRH_completedHeckeLFunction_zeros_unit_window_le_log

set_option autoImplicit false

namespace Sol_MasulloGRH_completedHeckeLFunction_logDeriv_bound_on_good_heights

open MeasureTheory Metric Complex

/-- The zeros of `f` (with positive order) whose ordinate lies within `1` of `c`. -/
def Zs (f : ℂ → ℂ) (c : ℝ) : Set ℂ := {ρ : ℂ | 0 < meromorphicOrderAt f ρ ∧ |ρ.im - c| ≤ 1}

/-- The multiplicity (order) of `f` at `ρ`, as an integer. -/
noncomputable def mult (f : ℂ → ℂ) (ρ : ℂ) : ℤ := (meromorphicOrderAt f ρ).untop₀

lemma exists_avoid (m δ : ℝ) (_hδ : 0 < δ) (Y : Finset ℝ) (hY : 2 * (Y.card : ℝ) * δ < 1)
    (P : Set ℝ) (hP : P.Countable) :
    ∃ T ∈ Set.Icc m (m + 1), T ∉ P ∧ ∀ y ∈ Y, δ ≤ |T - y| := by
  by_contra h
  push_neg at h
  have hsub : Set.Icc m (m + 1) ⊆ P ∪ ⋃ y ∈ Y, Metric.ball y δ := by
    intro T hT
    by_cases hTP : T ∈ P
    · exact Or.inl hTP
    · obtain ⟨y, hy, hlt⟩ := h T hT hTP
      refine Or.inr (Set.mem_biUnion hy ?_)
      rw [Metric.mem_ball, Real.dist_eq]
      exact hlt
  have h1 : volume (Set.Icc m (m + 1)) ≤ volume (P ∪ ⋃ y ∈ Y, Metric.ball y δ) :=
    measure_mono hsub
  have h2 : volume (P ∪ ⋃ y ∈ Y, Metric.ball y δ) ≤ ∑ y ∈ Y, volume (Metric.ball y δ) := by
    calc volume (P ∪ ⋃ y ∈ Y, Metric.ball y δ)
        ≤ volume P + volume (⋃ y ∈ Y, Metric.ball y δ) := measure_union_le _ _
      _ = volume (⋃ y ∈ Y, Metric.ball y δ) := by rw [hP.measure_zero, zero_add]
      _ ≤ _ := measure_biUnion_finset_le _ _
  rw [Real.volume_Icc] at h1
  simp only [Real.volume_ball, Finset.sum_const, nsmul_eq_mul] at h2
  have h3 : ENNReal.ofReal (m + 1 - m) ≤ (Y.card : ENNReal) * ENNReal.ofReal (2 * δ) :=
    h1.trans h2
  rw [show m + 1 - m = 1 by ring, ENNReal.ofReal_one, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at h3
  have h4 := ENNReal.one_le_ofReal.1 h3
  nlinarith

section facts

variable {f : ℂ → ℂ}

lemma ntop (hNF : MeromorphicNFOn f Set.univ) (hfin : (Zs f 0).Finite) (z : ℂ) :
    meromorphicOrderAt f z ≠ ⊤ := by
  intro hz
  have hall : ∀ y : ℂ, meromorphicOrderAt f y = ⊤ := by
    intro y
    by_contra hy
    exact hNF.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (Set.mem_univ y) (Set.mem_univ z) hy hz
  have hinf : (Zs f 0).Infinite := by
    apply Set.infinite_of_injective_forall_mem (f := fun r : ℝ => (r : ℂ)) Complex.ofReal_injective
    intro r
    refine ⟨?_, ?_⟩
    · rw [hall]; simp
    · simp
  exact hinf hfin

lemma one_le_mult (hntop : ∀ z, meromorphicOrderAt f z ≠ ⊤) {ρ : ℂ}
    (h : 0 < meromorphicOrderAt f ρ) : (1 : ℝ) ≤ (mult f ρ : ℝ) := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (hntop ρ)
  unfold mult
  rw [← hn] at h ⊢
  rw [WithTop.untop₀_coe]
  have : (0 : ℤ) < n := by exact_mod_cast h
  exact_mod_cast this

lemma analyticAt_of_ne_zero (hNF : MeromorphicNFOn f Set.univ) {z : ℂ} (hz : f z ≠ 0) :
    AnalyticAt ℂ f z := by
  rcases meromorphicNFAt_iff_analyticAt_or.1 (hNF (Set.mem_univ z)) with h | h
  · exact h
  · exact absurd h.2.2 hz

lemma zeros_finite (hNF : MeromorphicNFOn f Set.univ) (hntop : ∀ z, meromorphicOrderAt f z ≠ ⊤)
    (K : Set ℂ) (hK : IsCompact K) : (K ∩ f ⁻¹' {0}).Finite := by
  have hNFK : MeromorphicNFOn f K := fun x _ => hNF (Set.mem_univ x)
  rw [hNFK.zero_set_eq_divisor_support (fun u => hntop u)]
  exact (MeromorphicOn.divisor f K).finiteSupport hK

lemma mem_ball_of_seg (m : ℤ) {T σ : ℝ} (hT : T ∈ Set.Icc (m : ℝ) (m + 1)) (h1 : -1 ≤ σ)
    (h2 : σ ≤ 2) : (σ : ℂ) + T * I ∈ closedBall ((m : ℂ) * I) 3 := by
  rw [mem_closedBall, dist_eq_norm]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have hre : ((σ : ℂ) + T * I - (m : ℂ) * I).re = σ := by simp
  have him : ((σ : ℂ) + T * I - (m : ℂ) * I).im = T - m := by simp
  rw [hre, him]
  have : |σ| ≤ 2 := abs_le.2 ⟨by linarith, h2⟩
  have : |T - m| ≤ 1 := abs_le.2 ⟨by linarith [hT.1], by linarith [hT.2]⟩
  linarith

/-- The ordinates of the zeros and poles of `f` near the strip `m ≤ Im s ≤ m + 1`. -/
def badOrd (f : ℂ → ℂ) (m : ℤ) : Set ℝ := Complex.im '' (closedBall ((m : ℂ) * I) 3 ∩ f ⁻¹' {0})

lemma badOrd_countable (hNF : MeromorphicNFOn f Set.univ)
    (hntop : ∀ z, meromorphicOrderAt f z ≠ ⊤) (m : ℤ) : (badOrd f m).Countable :=
  ((zeros_finite hNF hntop _ (isCompact_closedBall _ _)).image _).countable

lemma seg_good (hNF : MeromorphicNFOn f Set.univ) (m : ℤ) {T : ℝ}
    (hT : T ∈ Set.Icc (m : ℝ) (m + 1)) (hTP : T ∉ badOrd f m) {σ : ℝ} (h1 : -1 ≤ σ) (h2 : σ ≤ 2) :
    AnalyticAt ℂ f (σ + T * I) ∧ f (σ + T * I) ≠ 0 := by
  have hne : f (σ + T * I) ≠ 0 := by
    intro h0
    apply hTP
    refine ⟨(σ : ℂ) + T * I, ⟨mem_ball_of_seg m hT h1 h2, h0⟩, ?_⟩
    simp
  exact ⟨analyticAt_of_ne_zero hNF hne, hne⟩

lemma small_case (hNF : MeromorphicNFOn f Set.univ) (hntop : ∀ z, meromorphicOrderAt f z ≠ ⊤)
    (m : ℤ) : ∃ T B : ℝ, (m : ℝ) ≤ T ∧ T ≤ m + 1 ∧ ∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
      AnalyticAt ℂ f (σ + T * I) ∧ f (σ + T * I) ≠ 0 ∧ ‖logDeriv f (σ + T * I)‖ ≤ B := by
  obtain ⟨T, hT, hTP, -⟩ := exists_avoid (m : ℝ) 1 one_pos ∅ (by simp) (badOrd f m)
    (badOrd_countable hNF hntop m)
  have hcont : ContinuousOn (fun σ : ℝ => logDeriv f (σ + T * I)) (Set.Icc (-1) 2) := by
    intro σ hσ
    obtain ⟨hA, hne⟩ := seg_good hNF m hT hTP hσ.1 hσ.2
    apply ContinuousAt.continuousWithinAt
    have hL : ContinuousAt (logDeriv f) ((σ : ℂ) + T * I) := by
      have : ContinuousAt (fun z => deriv f z / f z) ((σ : ℂ) + T * I) :=
        hA.deriv.continuousAt.div hA.continuousAt hne
      exact this
    exact hL.comp (f := fun σ : ℝ => (σ : ℂ) + T * I) (by fun_prop)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨T, B, hT.1, hT.2, fun σ h1 h2 => ?_⟩
  obtain ⟨hA, hne⟩ := seg_good hNF m hT hTP h1 h2
  exact ⟨hA, hne, hB σ ⟨h1, h2⟩⟩

lemma large_case (hNF : MeromorphicNFOn f Set.univ) (hntop : ∀ z, meromorphicOrderAt f z ≠ ⊤)
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ T : ℝ, (Zs f T).Finite ∧
      ∑ᶠ ρ ∈ Zs f T, ((mult f ρ : ℤ) : ℝ) ≤ Cw * Real.log (|T| + 2))
    (Cp T₀ : ℝ) (hCp : 0 ≤ Cp) (hT₀ : 2 ≤ T₀)
    (hp : ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → T₀ ≤ |s.im| → f s ≠ 0 →
      ‖logDeriv f s - ∑ᶠ ρ ∈ Zs f s.im, ((mult f ρ : ℤ) : ℂ) / (s - ρ)‖ ≤ Cp * Real.log |s.im|)
    (m : ℤ) (hm : T₀ ≤ (m : ℝ) ∨ (m : ℝ) + 1 ≤ -T₀) :
    ∃ T : ℝ, (m : ℝ) ≤ T ∧ T ≤ m + 1 ∧ ∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
      AnalyticAt ℂ f (σ + T * I) ∧ f (σ + T * I) ≠ 0 ∧
      ‖logDeriv f (σ + T * I)‖ ≤
        (2 * Cp / Real.log 2 + 24 * Cw ^ 2 + 8 * Cw / Real.log 2) *
          Real.log (|(m : ℝ)| + 2) ^ 2 := by
  set L := Real.log (|(m : ℝ)| + 2) with hL
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLge : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith [abs_nonneg (m : ℝ)])
  have hLpos : 0 < L := lt_of_lt_of_le hl2 hLge
  have hLL : L ≤ L ^ 2 / Real.log 2 := by
    rw [le_div_iff₀ hl2]
    nlinarith
  have hnear : ∀ x : ℝ, |x| ≤ |(m : ℝ)| + 1 → Real.log (|x| + 2) ≤ 2 * L := by
    intro x hx
    have h2L : 2 * L = Real.log ((|(m : ℝ)| + 2) ^ 2) := by
      rw [Real.log_pow]; push_cast; ring
    rw [h2L]
    exact Real.log_le_log (by linarith [abs_nonneg x]) (by nlinarith [abs_nonneg (m : ℝ)])
  -- zeros near the strip, counted with multiplicity
  have hcardA : ∀ c : ℝ, ((hw c).1.toFinset.card : ℝ) ≤ Cw * Real.log (|c| + 2) := by
    intro c
    calc ((hw c).1.toFinset.card : ℝ) = ∑ ρ ∈ (hw c).1.toFinset, (1 : ℝ) := by simp
      _ ≤ ∑ ρ ∈ (hw c).1.toFinset, ((mult f ρ : ℤ) : ℝ) :=
          Finset.sum_le_sum (fun ρ hρ => one_le_mult hntop ((hw c).1.mem_toFinset.1 hρ).1)
      _ = ∑ᶠ ρ ∈ Zs f c, ((mult f ρ : ℤ) : ℝ) :=
          (finsum_mem_eq_finite_toFinset_sum _ (hw c).1).symm
      _ ≤ _ := (hw c).2
  set A1 := (hw (m : ℝ)).1.toFinset with hA1
  set A2 := (hw ((m : ℝ) + 1)).1.toFinset with hA2
  set Yz := (A1 ∪ A2).image Complex.im with hYz
  set N := Yz.card with hNdef
  have hN : (N : ℝ) ≤ 3 * Cw * L := by
    have h1 : (N : ℝ) ≤ (A1.card : ℝ) + A2.card := by
      have := (Finset.card_image_le (s := A1 ∪ A2) (f := Complex.im)).trans
        (Finset.card_union_le A1 A2)
      exact_mod_cast this
    have h2 := hcardA (m : ℝ)
    have h3 := hcardA ((m : ℝ) + 1)
    have h4 : Real.log (|(m : ℝ) + 1| + 2) ≤ 2 * L :=
      hnear _ ((abs_add_le _ _).trans (by simp))
    have h5 : Cw * Real.log (|(m : ℝ) + 1| + 2) ≤ Cw * (2 * L) :=
      mul_le_mul_of_nonneg_left h4 hCw
    rw [← hA1] at h2
    rw [← hA2] at h3
    linarith
  set δ := 1 / (4 * ((N : ℝ) + 1)) with hδdef
  have hNnn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hδ : 0 < δ := by positivity
  have hδinv : (4 * ((N : ℝ) + 1)) * δ = 1 := by
    rw [hδdef]; field_simp
  have hδY : 2 * (N : ℝ) * δ < 1 := by
    have : 2 * (N : ℝ) * δ = (2 * N) / (4 * ((N : ℝ) + 1)) := by rw [hδdef]; ring
    rw [this, div_lt_one (by positivity)]
    linarith
  obtain ⟨T, hT, hTP, hTY⟩ :=
    exists_avoid (m : ℝ) δ hδ Yz hδY (badOrd f m) (badOrd_countable hNF hntop m)
  refine ⟨T, hT.1, hT.2, fun σ h1 h2 => ?_⟩
  obtain ⟨hA, hne⟩ := seg_good hNF m hT hTP h1 h2
  refine ⟨hA, hne, ?_⟩
  set s : ℂ := σ + T * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = T := by simp [hs]
  have hTabs : |T| ≤ |(m : ℝ)| + 1 := by
    apply abs_le.2
    constructor
    · linarith [neg_abs_le (m : ℝ), hT.1]
    · linarith [le_abs_self (m : ℝ), hT.2]
  have hT0 : T₀ ≤ |T| := by
    rcases hm with h | h
    · exact le_trans (by linarith [hT.1]) (le_abs_self T)
    · exact le_trans (by linarith [hT.2]) (neg_le_abs T)
  have hpf := hp s (by rw [hsre]; exact h1) (by rw [hsre]; exact h2) (by rw [hsim]; exact hT0) hne
  rw [hsim] at hpf
  have hsum : ‖∑ᶠ ρ ∈ Zs f T, ((mult f ρ : ℤ) : ℂ) / (s - ρ)‖ ≤
      (Cw * Real.log (|T| + 2)) * (4 * ((N : ℝ) + 1)) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ (hw T).1]
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ ρ ∈ (hw T).1.toFinset, ‖((mult f ρ : ℤ) : ℂ) / (s - ρ)‖ ≤
        ((mult f ρ : ℤ) : ℝ) * (4 * ((N : ℝ) + 1)) := by
      intro ρ hρ
      have hρZ := (hw T).1.mem_toFinset.1 hρ
      have hmult := one_le_mult hntop hρZ.1
      have hρ1 := abs_le.1 hρZ.2
      have hρY : ρ.im ∈ Yz := by
        apply Finset.mem_image_of_mem
        rw [Finset.mem_union]
        by_cases hle : ρ.im ≤ (m : ℝ) + 1
        · left
          rw [hA1, Set.Finite.mem_toFinset]
          exact ⟨hρZ.1, abs_le.2 ⟨by linarith [hT.1], by linarith⟩⟩
        · right
          rw [hA2, Set.Finite.mem_toFinset]
          exact ⟨hρZ.1, abs_le.2 ⟨by linarith, by linarith [hT.2]⟩⟩
      have hgap := hTY _ hρY
      have hdist : δ ≤ ‖s - ρ‖ := by
        refine hgap.trans (le_of_eq_of_le ?_ (Complex.abs_im_le_norm (s - ρ)))
        rw [Complex.sub_im, hsim]
      have hpos : 0 < ‖s - ρ‖ := lt_of_lt_of_le hδ hdist
      rw [norm_div, Complex.norm_intCast, abs_of_nonneg (by linarith), div_le_iff₀ hpos]
      have h1' : 1 ≤ (4 * ((N : ℝ) + 1)) * ‖s - ρ‖ := by
        calc (1 : ℝ) = (4 * ((N : ℝ) + 1)) * δ := hδinv.symm
          _ ≤ (4 * ((N : ℝ) + 1)) * ‖s - ρ‖ :=
            mul_le_mul_of_nonneg_left hdist (by linarith)
      nlinarith
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul, ← finsum_mem_eq_finite_toFinset_sum _ (hw T).1]
    exact mul_le_mul_of_nonneg_right (hw T).2 (by positivity)
  have hlogT2 : Real.log (|T| + 2) ≤ 2 * L := hnear T hTabs
  have hlogT : Real.log |T| ≤ 2 * L :=
    (Real.log_le_log (by linarith) (by linarith)).trans hlogT2
  have hlogT2nn : 0 ≤ Real.log (|T| + 2) := Real.log_nonneg (by linarith [abs_nonneg T])
  have e1 : Cp * Real.log |T| ≤ Cp * (2 * L) := mul_le_mul_of_nonneg_left hlogT hCp
  have e2 : Cw * Real.log (|T| + 2) * (4 * ((N : ℝ) + 1)) ≤
      (Cw * (2 * L)) * (4 * (3 * Cw * L + 1)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hlogT2 hCw) (by linarith) (by positivity)
      (mul_nonneg hCw (by linarith))
  have e2' : (Cw * (2 * L)) * (4 * (3 * Cw * L + 1)) = 24 * Cw ^ 2 * L ^ 2 + 8 * (Cw * L) := by
    ring
  have e3 : Cp * L ≤ Cp * (L ^ 2 / Real.log 2) := mul_le_mul_of_nonneg_left hLL hCp
  have e4 : Cw * L ≤ Cw * (L ^ 2 / Real.log 2) := mul_le_mul_of_nonneg_left hLL hCw
  have key : ‖logDeriv f s‖ ≤
      Cp * Real.log |T| + Cw * Real.log (|T| + 2) * (4 * ((N : ℝ) + 1)) :=
    (norm_le_norm_sub_add _ _).trans (add_le_add hpf hsum)
  have expand : (2 * Cp / Real.log 2 + 24 * Cw ^ 2 + 8 * Cw / Real.log 2) * L ^ 2 =
      2 * (Cp * (L ^ 2 / Real.log 2)) + 24 * Cw ^ 2 * L ^ 2 +
        8 * (Cw * (L ^ 2 / Real.log 2)) := by ring
  rw [expand]
  linarith

end facts

end Sol_MasulloGRH_completedHeckeLFunction_logDeriv_bound_on_good_heights

open MasulloGRH Sol_MasulloGRH_completedHeckeLFunction_logDeriv_bound_on_good_heights

theorem solution
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) :
    ∃ C : ℝ, ∀ m : ℤ, ∃ T : ℝ, (m : ℝ) ≤ T ∧ T ≤ m + 1 ∧
      ∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
        AnalyticAt ℂ (completedHeckeLFunction χ) (σ + T * Complex.I) ∧
        completedHeckeLFunction χ (σ + T * Complex.I) ≠ 0 ∧
        ‖logDeriv (completedHeckeLFunction χ) (σ + T * Complex.I)‖
          ≤ C * Real.log (|(m : ℝ)| + 2) ^ 2 := by
  obtain ⟨Cw, hw⟩ := completedHeckeLFunction_zeros_unit_window_le_log F χ
  obtain ⟨Cp, T₀, hT₀, hp⟩ := completedHeckeLFunction_logDeriv_local_partial_fraction F χ
  have hNF : MeromorphicNFOn (completedHeckeLFunction χ) Set.univ :=
    meromorphicNFOn_toMeromorphicNFOn _ _
  have hntop : ∀ z, meromorphicOrderAt (completedHeckeLFunction χ) z ≠ ⊤ :=
    ntop hNF (hw 0).1
  have hw' : ∀ T : ℝ, (Zs (completedHeckeLFunction χ) T).Finite ∧
      ∑ᶠ ρ ∈ Zs (completedHeckeLFunction χ) T,
        ((mult (completedHeckeLFunction χ) ρ : ℤ) : ℝ) ≤ max Cw 0 * Real.log (|T| + 2) :=
    fun T => ⟨(hw T).1, (hw T).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.log_nonneg (by linarith [abs_nonneg T])))⟩
  have hp' : ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → T₀ ≤ |s.im| → completedHeckeLFunction χ s ≠ 0 →
      ‖logDeriv (completedHeckeLFunction χ) s -
        ∑ᶠ ρ ∈ Zs (completedHeckeLFunction χ) s.im,
          ((mult (completedHeckeLFunction χ) ρ : ℤ) : ℂ) / (s - ρ)‖ ≤
        max Cp 0 * Real.log |s.im| :=
    fun s h1 h2 h3 h4 => (hp s h1 h2 h3 h4).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.log_nonneg (by linarith)))
  choose Tf Bf hTB using small_case hNF hntop
  set K := 2 * max Cp 0 / Real.log 2 + 24 * max Cw 0 ^ 2 + 8 * max Cw 0 / Real.log 2 with hK
  set Bs := ∑ m ∈ Finset.Icc (-(⌈T₀⌉ + 1)) (⌈T₀⌉ + 1), |Bf m| with hBs
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hBs0 : 0 ≤ Bs := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  refine ⟨max K (Bs / Real.log 2 ^ 2), fun m => ?_⟩
  by_cases hm : T₀ ≤ (m : ℝ) ∨ (m : ℝ) + 1 ≤ -T₀
  · obtain ⟨T, h1, h2, h3⟩ := large_case hNF hntop (max Cw 0) (le_max_right _ _) hw'
      (max Cp 0) T₀ (le_max_right _ _) hT₀ hp' m hm
    refine ⟨T, h1, h2, fun σ hσ1 hσ2 => ?_⟩
    obtain ⟨a, b, c⟩ := h3 σ hσ1 hσ2
    exact ⟨a, b, c.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))⟩
  · push_neg at hm
    obtain ⟨hm1, hm2⟩ := hm
    have hc := Int.le_ceil T₀
    have hlo : ((-(⌈T₀⌉ + 1) : ℤ) : ℝ) ≤ (m : ℝ) := by push_cast; linarith
    have hhi : (m : ℝ) ≤ ((⌈T₀⌉ + 1 : ℤ) : ℝ) := by push_cast; linarith
    have hmem : m ∈ Finset.Icc (-(⌈T₀⌉ + 1)) (⌈T₀⌉ + 1) :=
      Finset.mem_Icc.2 ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
    obtain ⟨h1, h2, h3⟩ := hTB m
    refine ⟨Tf m, h1, h2, fun σ hσ1 hσ2 => ?_⟩
    obtain ⟨a, b, c⟩ := h3 σ hσ1 hσ2
    refine ⟨a, b, ?_⟩
    have hB : Bf m ≤ Bs := (le_abs_self _).trans
      (Finset.single_le_sum (f := fun m => |Bf m|) (fun i _ => abs_nonneg _) hmem)
    have hL : Real.log 2 ^ 2 ≤ Real.log (|(m : ℝ)| + 2) ^ 2 :=
      pow_le_pow_left₀ hl2.le
        (Real.log_le_log (by norm_num) (by linarith [abs_nonneg (m : ℝ)])) 2
    calc ‖logDeriv (completedHeckeLFunction χ) (↑σ + ↑(Tf m) * Complex.I)‖ ≤ Bf m := c
      _ ≤ Bs := hB
      _ = Bs / Real.log 2 ^ 2 * Real.log 2 ^ 2 := by field_simp
      _ ≤ max K (Bs / Real.log 2 ^ 2) * Real.log (|(m : ℝ)| + 2) ^ 2 :=
        mul_le_mul (le_max_right _ _) hL (by positivity)
          ((div_nonneg hBs0 (by positivity)).trans (le_max_right _ _))
