-- Prove2me | solution 2 for LargeSupplyFPA.Asymptotic.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T17:29:16.317247+00:00
-- url     : https://prove2.me/submissions/c4ff8534-91b4-4b50-86d8-3182b6c000dc

import Definitions.Def_LargeSupplyFPA_Asymptotic_Assumptions
import Definitions.Def_LargeSupplyFPA_Asymptotic_Thresholds
import Definitions.Def_LargeSupplyFPA_Asymptotic_Extremizing
import Definitions.Def_LargeSupplyFPA_Asymptotic_Model
import Theorems.Thm_LargeSupplyFPA_Asymptotic_fact_3
import Theorems.Thm_LargeSupplyFPA_Asymptotic_lemma_1
import Theorems.Thm_LargeSupplyFPA_Asymptotic_lemma_3

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics
open LargeSupplyFPA.Asymptotic
open scoped BigOperators

set_option autoImplicit false

namespace MultiUnitPoA

theorem marginalBid_probability {n : ℕ} {V : Fin n → Measure ℝ} {E : Fin n → Kernel ℝ ℝ}
    (hV : IsValueProfile V) (hE : IsStrategyProfile E) (i : Fin n) :
    IsProbabilityMeasure (marginalBid V E i) := by
  let hv := hV i
  let he := (hE i).1
  exact isProbabilityMeasure_bind (E i).aemeasurable (Filter.Eventually.of_forall fun _ => inferInstance)


private theorem continuous_cdf_of_atomless (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : ∀ b : ℝ, μ {b} = 0) : Continuous (ProbabilityTheory.cdf μ : ℝ → ℝ) := by
  rw [continuous_iff_continuousAt]
  intro b
  let F := ProbabilityTheory.cdf μ
  apply F.mono.continuousAt_iff_leftLim_eq_rightLim.mpr
  rw [F.rightLim_eq]
  have hz := F.measure_singleton b
  rw [show F.measure = μ from measure_cdf μ, h b] at hz
  have hleft := F.mono.leftLim_le (le_refl b)
  have hz' := ENNReal.ofReal_eq_zero.mp hz.symm
  linarith [show Function.leftLim (F : ℝ → ℝ) b ≤ F b from hleft]

theorem continuous_expNumAbove {n : ℕ} {V : Fin n → Measure ℝ} {E : Fin n → Kernel ℝ ℝ}
    [∀ i, IsProbabilityMeasure (marginalBid V E i)] (h : IsAtomless V E) :
    Continuous (expNumAbove V E) := by
  unfold expNumAbove
  apply continuous_finsetSum
  intro i _
  have heq (b : ℝ) : (marginalBid V E i).real (Set.Ioi b) =
      1 - ProbabilityTheory.cdf (marginalBid V E i) b := by
    rw [cdf_eq_real, ← probReal_compl_eq_one_sub measurableSet_Iic, Set.compl_Iic]
  simp_rw [heq]
  exact continuous_const.sub (continuous_cdf_of_atomless _ (h i))

theorem tendsto_expNumAbove {n : ℕ} {V : Fin n → Measure ℝ} {E : Fin n → Kernel ℝ ℝ}
    [∀ i, IsProbabilityMeasure (marginalBid V E i)] :
    Tendsto (expNumAbove V E) atTop (𝓝 0) := by
  unfold expNumAbove
  have hsum (i : Fin n) : Tendsto (fun b : ℝ => (marginalBid V E i).real (Set.Ioi b))
      atTop (𝓝 0) := by
    have heq (b : ℝ) : (marginalBid V E i).real (Set.Ioi b) =
        1 - ProbabilityTheory.cdf (marginalBid V E i) b := by
      rw [cdf_eq_real, ← probReal_compl_eq_one_sub measurableSet_Iic, Set.compl_Iic]
    simp_rw [heq]
    simpa only [sub_self] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_cdf_atTop (marginalBid V E i))
  simpa using tendsto_finsetSum Finset.univ (fun i _ => hsum i)


theorem threshold_mem {f : ℝ → ℝ} (hc : Continuous f)
    (hf : Tendsto f atTop (𝓝 0)) {q : ℝ} (hq : 0 < q) :
    sInf {b : ℝ | 0 ≤ b ∧ f b ≤ q} ∈ {b : ℝ | 0 ≤ b ∧ f b ≤ q} := by
  have hclosed : IsClosed {b : ℝ | 0 ≤ b ∧ f b ≤ q} :=
    isClosed_Ici.inter (isClosed_le hc continuous_const)
  have hEventually : ∀ᶠ x : ℝ in atTop, 0 ≤ x ∧ f x ≤ q :=
    (eventually_ge_atTop 0).and (hf.eventually (eventually_le_nhds hq))
  obtain ⟨x, hx⟩ := hEventually.exists
  exact hclosed.csInf_mem ⟨x, hx⟩ ⟨0, fun _ hy => hy.1⟩


end MultiUnitPoA

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators

set_option autoImplicit false

namespace MultiUnitPoA

variable {n : ℕ} (B : Fin n → Measure ℝ) [∀ j, IsProbabilityMeasure (B j)]


end MultiUnitPoA

open MeasureTheory ProbabilityTheory Filter Topology
open LargeSupplyFPA.Asymptotic
open scoped BigOperators

set_option autoImplicit false

namespace MultiUnitPoA

theorem eventually_threshold_scale (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 0.5) :
    ∀ᶠ k : ℕ in atTop,
      4 ≤ (k : ℝ) ^ ((0.5 : ℝ) + δ) ∧ (k : ℝ) ^ ((0.5 : ℝ) + δ) ≤ k ∧
      0 < (k : ℝ) - (k : ℝ) ^ ((0.5 : ℝ) + δ) - 1 := by
  have hExp : 0 < (0.5 : ℝ) + δ := by linarith [hδ.1]
  have hGap : 0 < 1 - ((0.5 : ℝ) + δ) := by linarith [hδ.2]
  have hlarge := (tendsto_rpow_atTop hExp).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsmall := (tendsto_rpow_neg_atTop hGap).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hlarge.eventually (eventually_ge_atTop (4 : ℝ)),
    hsmall.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num)),
    eventually_ge_atTop (4 : ℕ)] with k hlarge hsmall hk
  have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hkP : 0 < (k : ℝ) := by linarith
  change 4 ≤ (k : ℝ) ^ ((0.5 : ℝ) + δ) at hlarge
  change (k : ℝ) ^ (-(1 - ((0.5 : ℝ) + δ))) < 1 / 2 at hsmall
  have hrewrite : (k : ℝ) ^ ((0.5 : ℝ) + δ) =
      (k : ℝ) ^ (-(1 - ((0.5 : ℝ) + δ))) * (k : ℝ) := by
    conv_rhs => rw [← Real.rpow_add_one hkP.ne']
    congr 1
    ring
  have hhalf : (k : ℝ) ^ ((0.5 : ℝ) + δ) < (k : ℝ) / 2 := by
    rw [hrewrite]
    linarith [mul_lt_mul_of_pos_right hsmall hkP]
  exact ⟨hlarge, by linarith, by linarith⟩


end MultiUnitPoA

open MeasureTheory ProbabilityTheory Filter Topology Set
open LargeSupplyFPA.Asymptotic
open scoped BigOperators

set_option autoImplicit false

namespace MultiUnitPoA

variable {n : ℕ} {V : Fin n → Measure ℝ} {E : Fin n → Kernel ℝ ℝ}
variable [∀ j, IsProbabilityMeasure (marginalBid V E j)]


omit [∀ j, IsProbabilityMeasure (marginalBid V E j)] in
theorem alloc_nonneg (k : ℕ) (i : Fin n) (b : ℝ) : 0 ≤ alloc k V E i b := by
  apply integral_nonneg
  intro β
  unfold tieShare
  exact le_min (div_nonneg (le_max_right _ _) (by positivity)) zero_le_one

theorem alloc_le_one (k : ℕ) (i : Fin n) (b : ℝ) : alloc k V E i b ≤ 1 := by
  change (∫ β, tieShare k i b β ∂Measure.pi (marginalBid V E)) ≤ 1
  calc
    _ ≤ ∫ _ : Fin n → ℝ, (1 : ℝ) ∂Measure.pi (marginalBid V E) := by
      apply integral_mono_of_nonneg _ (integrable_const _) _
      · exact Filter.Eventually.of_forall fun β =>
          le_min (div_nonneg (le_max_right _ _) (by positivity)) zero_le_one
      · exact Filter.Eventually.of_forall fun _ => min_le_right _ _
    _ = 1 := by simp


end MultiUnitPoA

open MeasureTheory ProbabilityTheory Filter Topology
open LargeSupplyFPA.Asymptotic

set_option autoImplicit false

namespace MultiUnitPoA

theorem threshold_nonneg {f : ℝ → ℝ} {q : ℝ} :
    0 ≤ sInf {b : ℝ | 0 ≤ b ∧ f b ≤ q} :=
  Real.sInf_nonneg (fun _ hb => hb.1)

theorem lowThreshold_le_highThreshold (δ : ℝ) {n : ℕ} (k : ℕ)
    (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ)
    (hHigh : {b : ℝ | 0 ≤ b ∧
      expNumAbove V E b ≤ (k : ℝ) - (k : ℝ) ^ ((0.5 : ℝ) + δ) - 1}.Nonempty) :
    lowThreshold δ k V E ≤ highThreshold δ k V E := by
  apply le_csInf hHigh
  intro b hb
  apply csInf_le ⟨0, fun _ hx => hx.1⟩
  refine ⟨hb.1, hb.2.trans ?_⟩
  have hpow : 0 ≤ (k : ℝ) ^ ((0.5 : ℝ) + δ) := by positivity
  linarith

private theorem deviation_le_optUtility {n : ℕ} {V : Fin n → Measure ℝ}
    {E : Fin n → Kernel ℝ ℝ} (k : ℕ) (i : Fin n) (v d : ℝ) (hd : 0 ≤ d)
    (hAlloc : ∀ b : ℝ, 0 ≤ alloc k V E i b ∧ alloc k V E i b ≤ 1) :
    utility k V E i v d ≤ optUtility k V E i v := by
  unfold optUtility
  refine le_ciSup (f := fun bid : Set.Ici (0 : ℝ) => utility k V E i v bid.val) ?_ ⟨d, hd⟩
  refine ⟨max v 0, ?_⟩
  rintro _ ⟨bid, rfl⟩
  unfold utility
  rcases le_or_gt v bid.val with hv | hv
  · exact (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hv) (hAlloc _).1).trans
      (le_max_right _ _)
  · exact (mul_le_of_le_one_right (sub_nonneg.mpr hv.le) (hAlloc _).2).trans
      ((sub_le_self _ bid.property).trans (le_max_left _ _))

/-- The compactness and utility argument in Lemma 4. Its bid-count and allocation
inputs can be supplied by the mission's preceding milestones. -/
theorem positive_utility_interval (δ : ℝ) (H : ℝ) (n : ℕ → ℕ)
    (V : ∀ k, Fin (n k) → Measure ℝ) (E : ∀ k, Fin (n k) → Kernel ℝ ℝ)
    (s : ℕ → ℕ) (hs : StrictMono s) (c : ℝ) (hc : 0 < c)
    (hOrder : ∀ᶠ k in atTop, lowThreshold δ k (V k) (E k) ≤ highThreshold δ k (V k) (E k))
    (hBound : ∀ᶠ k in atTop, highThreshold δ k (V k) (E k) ≤ H + 1)
    (hLo : Tendsto (fun k => kthBidCDF k (V k) (E k) (lowThreshold δ k (V k) (E k)))
      atTop (𝓝 0))
    (hHi : Tendsto (fun k => kthBidCDF k (V k) (E k) (highThreshold δ k (V k) (E k)))
      atTop (𝓝 1))
    (hCDF : ∀ k d, 0 ≤ kthBidCDF k (V k) (E k) d ∧ kthBidCDF k (V k) (E k) d ≤ 1)
    (hAlloc : ∀ k i d, 0 ≤ alloc k (V k) (E k) i d ∧ alloc k (V k) (E k) i d ≤ 1)
    (hFact3 : ∀ k i d, 0 ≤ d → kthBidCDF k (V k) (E k) d ≤ alloc k (V k) (E k) i d)
    (hwide : ∀ (lo hi : ℕ → ℝ) (θ : ℕ → ℕ), StrictMono θ → IsExtremizing n V E lo hi (s ∘ θ) →
      ∀ L : ℝ, Tendsto (fun l => hi (s (θ l)) - lo (s (θ l))) atTop (𝓝 L) → c < L) :
    ∃ ubar : ℝ, 0 < ubar ∧ ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ mstar : ℕ, ∀ m : ℕ, mstar < m →
      ∃ a b : ℝ, lowThreshold δ (s (θ m)) (V (s (θ m))) (E (s (θ m))) < a ∧ a + c / 8 ≤ b ∧
        b < highThreshold δ (s (θ m)) (V (s (θ m))) (E (s (θ m))) ∧
        ∀ i : Fin (n (s (θ m))), ∀ v ∈ Set.Icc a b,
          ubar ≤ optUtility (s (θ m)) (V (s (θ m))) (E (s (θ m))) i v := by
  let lo : ℕ → ℝ := fun k => lowThreshold δ k (V k) (E k)
  let hi : ℕ → ℝ := fun k => highThreshold δ k (V k) (E k)
  let orderedLo : ℕ → ℝ := fun k => min (lo k) (hi k)
  let d : ℕ → ℝ := fun k => max (hi k - c / 2) 0
  have hlo0 (k : ℕ) : 0 ≤ lo k := threshold_nonneg
  have hhi0 (k : ℕ) : 0 ≤ hi k := threshold_nonneg
  have hord : ∀ᶠ k in atTop, orderedLo k = lo k :=
    hOrder.mono fun k hk => min_eq_left hk
  have hLo' : Tendsto (fun k => kthBidCDF k (V k) (E k) (orderedLo k)) atTop (𝓝 0) := by
    apply hLo.congr'
    filter_upwards [hord] with k hk
    change kthBidCDF k (V k) (E k) (lo k) = kthBidCDF k (V k) (E k) (orderedLo k)
    rw [hk]
  have hWidths : ∀ᶠ k in atTop, hi k - orderedLo k ∈ Set.Icc (0 : ℝ) (H + 1) := by
    filter_upwards [hBound] with k hk
    have h0 : 0 ≤ orderedLo k := le_min (hlo0 k) (hhi0 k)
    exact ⟨sub_nonneg.mpr (min_le_right _ _), (sub_le_self _ h0).trans hk⟩
  obtain ⟨L, _, θ, hθ, hL⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := H + 1)).tendsto_subseq'
    ((hs.tendsto_atTop.eventually hWidths).frequently)
  have hφ : StrictMono (s ∘ θ) := hs.comp hθ
  have hExt : IsExtremizing n V E orderedLo hi (s ∘ θ) :=
    ⟨hφ, fun k => ⟨le_min (hlo0 k) (hhi0 k), min_le_right _ _⟩,
      hLo'.comp hφ.tendsto_atTop, hHi.comp hφ.tendsto_atTop⟩
  have hLc := hwide orderedLo hi θ hθ hExt L hL
  have hGap : ∀ᶠ m in atTop, c < hi (s (θ m)) - lo (s (θ m)) := by
    filter_upwards [hL.eventually (eventually_gt_nhds hLc), hφ.tendsto_atTop.eventually hord]
      with m hm ho
    change c < hi (s (θ m)) - orderedLo (s (θ m)) at hm
    change orderedLo (s (θ m)) = lo (s (θ m)) at ho
    rwa [ho] at hm
  let prob : ℕ → ℝ := fun k => kthBidCDF k (V k) (E k) (d k)
  obtain ⟨p, hp, ρ, hρ, hProb⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).tendsto_subseq
    (x := prob ∘ s ∘ θ) (fun m => hCDF (s (θ m)) (d (s (θ m))))
  let τε := θ ∘ ρ
  have hτε : StrictMono τε := hθ.comp hρ
  have hτεs : StrictMono (s ∘ τε) := hs.comp hτε
  have hGap' : ∀ᶠ m in atTop, c < hi (s (τε m)) - lo (s (τε m)) :=
    hρ.tendsto_atTop.eventually hGap
  have hd (k : ℕ) : 0 ≤ d k := le_max_right _ _
  have hdhi (k : ℕ) : d k ≤ hi k := max_le (by linarith) (hhi0 k)
  have hdEq : ∀ᶠ m in atTop, d (s (τε m)) = hi (s (τε m)) - c / 2 := by
    filter_upwards [hGap'] with m hm
    exact max_eq_left (by linarith [hlo0 (s (τε m))])
  have hp0 : 0 < p := by
    by_contra! hn
    have hpz : p = 0 := le_antisymm hn hp.1
    have hExt' : IsExtremizing n V E d hi (s ∘ τε) :=
      ⟨hτεs, fun k => ⟨hd k, hdhi k⟩, hpz ▸ hProb, hHi.comp hτεs.tendsto_atTop⟩
    have hWidth : Tendsto (fun l => hi (s (τε l)) - d (s (τε l))) atTop (𝓝 (c / 2)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [hdEq] with m hm
      rw [hm]
      ring
    linarith [hwide d hi τε hτε hExt' (c / 2) hWidth]
  have hpHalf : p / 2 < p := by linarith
  have hProb' : ∀ᶠ m in atTop, p / 2 < prob (s (τε m)) :=
    hProb.eventually (eventually_gt_nhds hpHalf)
  obtain ⟨mstar, hmstar⟩ := eventually_atTop.mp (hGap'.and (hdEq.and hProb'))
  refine ⟨c / 4 * (p / 2), by positivity, τε, hτε, mstar, ?_⟩
  intro m hm
  obtain ⟨hgap, hd_eq, hprob⟩ := hmstar m hm.le
  let k := s (τε m)
  refine ⟨hi k - c / 4, hi k - c / 8, ?_, by ring_nf; exact le_rfl, by dsimp [hi, k]; linarith, ?_⟩
  · change lo k < hi k - c / 4
    change c < hi k - lo k at hgap
    linarith
  intro i v hv
  have hSurplus : c / 4 ≤ v - d k := by
    change d k = hi k - c / 2 at hd_eq
    rw [hd_eq]
    linarith [hv.1]
  have hWin : p / 2 ≤ alloc k (V k) (E k) i (d k) :=
    (le_of_lt hprob).trans (hFact3 k i (d k) (hd k))
  calc
    _ ≤ (v - d k) * alloc k (V k) (E k) i (d k) :=
      mul_le_mul hSurplus hWin (by positivity) (by linarith)
    _ ≤ optUtility k (V k) (E k) i v :=
      deviation_le_optUtility k i v (d k) (hd k) (hAlloc k i)

end MultiUnitPoA

open MeasureTheory ProbabilityTheory
open LargeSupplyFPA.Asymptotic
open scoped BigOperators

set_option autoImplicit false


namespace Fact3

alias solution := _root_.LargeSupplyFPA.Asymptotic.fact_3


end Fact3

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics
open LargeSupplyFPA.Asymptotic

set_option autoImplicit false


namespace Lemma3

alias solution := _root_.LargeSupplyFPA.Asymptotic.lemma_3


end Lemma3

open MeasureTheory ProbabilityTheory Filter Topology
open LargeSupplyFPA.Asymptotic MultiUnitPoA

set_option autoImplicit false

namespace Lemma1

alias solution := _root_.LargeSupplyFPA.Asymptotic.lemma_1


end Lemma1

open MeasureTheory ProbabilityTheory Filter Topology
open LargeSupplyFPA.Asymptotic MultiUnitPoA

set_option autoImplicit false


theorem solution (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 0.5) (H κ : ℝ)
    (hH : 0 < H) (hκ : 0 < κ) (n : ℕ → ℕ)
    (V : ∀ k, Fin (n k) → Measure ℝ) (E : ∀ k, Fin (n k) → Kernel ℝ ℝ)
    (hseq : IsAuctionSequence n V E) (hA1 : ∀ k, Assumption1 H κ (V k))
    (hA3 : Assumption3 n V E) (hA4 : ∀ k, IsAtomless (V k) (E k))
    (s : ℕ → ℕ) (hs : StrictMono s) (c : ℝ) (hc : 0 < c)
    (hwide : ∀ (lo hi : ℕ → ℝ) (θ : ℕ → ℕ), StrictMono θ → IsExtremizing n V E lo hi (s ∘ θ) →
      ∀ L : ℝ, Tendsto (fun l => hi (s (θ l)) - lo (s (θ l))) atTop (𝓝 L) → c < L) :
    ∃ ubar : ℝ, 0 < ubar ∧ ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ mstar : ℕ, ∀ m : ℕ, mstar < m →
      ∃ a b : ℝ, lowThreshold δ (s (θ m)) (V (s (θ m))) (E (s (θ m))) < a ∧ a + c / 8 ≤ b ∧
        b < highThreshold δ (s (θ m)) (V (s (θ m))) (E (s (θ m))) ∧
        ∀ i : Fin (n (s (θ m))), ∀ v ∈ Set.Icc a b,
          ubar ≤ optUtility (s (θ m)) (V (s (θ m))) (E (s (θ m))) i v := by
  have hOrder : ∀ᶠ k in atTop, lowThreshold δ k (V k) (E k) ≤ highThreshold δ k (V k) (E k) := by
    filter_upwards [eventually_threshold_scale δ hδ] with k hk
    let (i : Fin (n k)) := marginalBid_probability (hseq.2.1 k) (hseq.2.2 k) i
    apply lowThreshold_le_highThreshold
    exact ⟨_, threshold_mem (continuous_expNumAbove (hA4 k)) tendsto_expNumAbove hk.2.2⟩
  let lo : ℕ → ℝ := fun k => lowThreshold δ k (V k) (E k)
  let hi : ℕ → ℝ := fun k => highThreshold δ k (V k) (E k)
  let lo' : ℕ → ℝ := fun k => min (lo k) (hi k)
  have hlo (k : ℕ) : 0 ≤ lo k := threshold_nonneg
  have hhi (k : ℕ) : 0 ≤ hi k := threshold_nonneg
  have hExt := Lemma1.solution δ hδ n V E hseq hA4 lo' hi
      (fun _ => min_le_right _ _)
      (fun k => ⟨le_min (hlo k) (hhi k), min_le_left _ _⟩) (fun _ => le_rfl)
  have hLo : Tendsto (fun k => kthBidCDF k (V k) (E k) (lo k)) atTop (𝓝 0) := by
    apply hExt.2.2.1.congr'
    filter_upwards [hOrder] with k hk
    change kthBidCDF k (V k) (E k) (min (lo k) (hi k)) = _
    rw [min_eq_left hk]
  apply positive_utility_interval δ H n V E s hs c hc hOrder
    (Lemma3.solution δ hδ H κ hH hκ n V E hseq hA1 hA3 hA4 1 one_pos)
    hLo hExt.2.2.2 _ _ _ hwide
  · intro k d
    let (i : Fin (n k)) := marginalBid_probability (hseq.2.1 k) (hseq.2.2 k) i
    exact ⟨measureReal_nonneg, measureReal_le_one⟩
  · intro k i d
    let (i : Fin (n k)) := marginalBid_probability (hseq.2.1 k) (hseq.2.2 k) i
    exact ⟨alloc_nonneg k i d, alloc_le_one k i d⟩
  · intro k i d hd
    exact (Fact3.solution k (V k) (E k) (hseq.2.1 k) (hseq.2.2 k) d hd i).2 (hA4 k)

#print axioms solution
