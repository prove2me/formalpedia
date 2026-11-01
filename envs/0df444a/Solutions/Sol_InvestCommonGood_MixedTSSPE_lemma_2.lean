-- Prove2me | solution 1 for InvestCommonGood.MixedTSSPE.lemma_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T15:43:36.474882+00:00
-- url     : https://prove2.me/submissions/ce617b5f-c1e6-4e6d-a601-066d938ec3ac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_InvestCommonGood_MixedTSSPE_Conditions
import Theorems.Thm_InvestCommonGood_MixedTSSPE_eq_B_20

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
open VarContrib.RegularMPE
open InvestCommonGood.MixedTSSPE

/-- A monotone sequence in an open interval `I` eventually exceeding every point of `I`. -/
lemma icg_l2_seq (I : Set ℝ) (hIo : IsOpen I) (hIc : I.OrdConnected) (c : ℝ) (hc : c ∈ I) :
    ∃ u : ℕ → ℝ, Monotone u ∧ (∀ n, u n ∈ I) ∧ ∀ y ∈ I, ∃ N, ∀ n ≥ N, y < u n := by
  by_cases hb : BddAbove I
  · set b := sSup I
    have hcb : ∀ y ∈ I, y < b := by
      intro y hy
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hIo y hy
      have : y + ε / 2 ∈ I := hball (by rw [Metric.mem_ball, Real.dist_eq]; rw [abs_lt]; constructor <;> linarith)
      have := le_csSup hb this
      linarith
    have hcb' := hcb c hc
    refine ⟨fun n => b - (b - c) / ((n : ℝ) + 1), ?_, ?_, ?_⟩
    · intro m n hmn
      simp only
      have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hmn
      have : (b - c) / ((n : ℝ) + 1) ≤ (b - c) / ((m : ℝ) + 1) :=
        div_le_div_of_nonneg_left (by linarith) hm hmn'
      linarith
    · intro n
      have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
      have hlt : b - (b - c) / ((n : ℝ) + 1) < b := by
        have : 0 < (b - c) / ((n : ℝ) + 1) := div_pos (by linarith) (by linarith)
        linarith
      obtain ⟨y, hy, hy'⟩ := exists_lt_of_lt_csSup ⟨c, hc⟩ hlt
      have hge : c ≤ b - (b - c) / ((n : ℝ) + 1) := by
        have : (b - c) / ((n : ℝ) + 1) ≤ b - c := div_le_self (by linarith) hn
        linarith
      exact hIc.out hc hy ⟨hge, hy'.le⟩
    · intro y hy
      have hyb := hcb y hy
      obtain ⟨N, hN⟩ := exists_nat_gt ((b - c) / (b - y))
      refine ⟨N, fun n hn => ?_⟩
      have hpos : 0 < b - y := by linarith
      have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
      have h1 : (b - c) / (b - y) < (n : ℝ) + 1 := by linarith
      have h2 : (b - c) / ((n : ℝ) + 1) < b - y := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hpos] at h1
        linarith
      linarith
  · refine ⟨fun n => c + n, ?_, ?_, ?_⟩
    · intro m n hmn
      simp only
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith
    · intro n
      rw [not_bddAbove_iff] at hb
      obtain ⟨y, hy, hy'⟩ := hb (c + n)
      exact hIc.out hc hy ⟨by simp, hy'.le⟩
    · intro y _
      obtain ⟨N, hN⟩ := exists_nat_gt (y - c)
      refine ⟨N, fun n hn => ?_⟩
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      simp only
      linarith

theorem solution {Ω : Type*} [MeasurableSpace Ω] (m : Model) (S : Setting Ω) (zs xs : ℝ)
    (hS : InvestCommonGood.MixedTSSPE.Standing m S) (hA1 : Assumption1 m S) (hA2 : Assumption2 m S zs)
    (hA4 : Assumption4 m S xs) :
    (∃ xh : ℝ, IsLemma2Point m S xh ∧ xh < min xs zs) ∧
      ∀ x ∈ m.I, (x < zs → Ifun m S x < 0) ∧ (zs < x → 0 < Ifun m S x) := by
  have hB20 := eq_B_20 m S zs xs hS hA1 hA2 hA4
  have hIo : IsOpen m.I := hS.I_open
  have hIc : m.I.OrdConnected := hS.I_ordConnected
  -- φ' < 0 on I
  have hφ'ne : ∀ x ∈ m.I, deriv S.φ x ≠ 0 := by
    intro x hx h0
    have hnp : ∀ y ∈ m.I, deriv S.φ y ≤ 0 := by
      intro y hy
      have := (hS.φ_strictAnti.antitoneOn).derivWithin_nonpos (x := y)
      rwa [derivWithin_of_isOpen hIo hy] at this
    have hmax : IsLocalMax (deriv S.φ) x := by
      have : ∀ᶠ y in 𝓝 x, deriv S.φ y ≤ deriv S.φ x := by
        filter_upwards [hIo.mem_nhds hx] with y hy
        rw [h0]; exact hnp y hy
      exact this
    have h2 := hmax.deriv_eq_zero
    have hode := hS.φ_ode x hx
    unfold gen at hode
    rw [h2, h0] at hode
    have := hS.φ_pos x hx
    have := hS.r_pos
    nlinarith
  have hφ'neg : ∀ x ∈ m.I, deriv S.φ x < 0 := by
    intro x hx
    have := (hS.φ_strictAnti.antitoneOn).derivWithin_nonpos (x := x)
    rw [derivWithin_of_isOpen hIo hx] at this
    exact lt_of_le_of_ne this (hφ'ne x hx)
  -- regularity
  have hφc : ContinuousOn S.φ m.I := hS.φ_C2.continuousOn
  have hφ'c : ContinuousOn (deriv S.φ) m.I :=
    hS.φ_C2.continuousOn_deriv_of_isOpen hIo (by norm_num)
  have hR'c : ContinuousOn (deriv (R m S m.π)) m.I :=
    hS.Rπ_C2.continuousOn_deriv_of_isOpen hIo (by norm_num)
  have hIfc : ContinuousOn (Ifun m S) m.I := by
    unfold Ifun
    exact (hR'c.sub continuousOn_const).div hφ'c hφ'ne
  have hμc : ContinuousOn m.μ m.I := by
    obtain ⟨L, hL1, -⟩ := hS.lipschitz; exact hL1.continuousOn
  have hσc : ContinuousOn m.σ m.I := by
    obtain ⟨L, -, hL2⟩ := hS.lipschitz; exact hL2.continuousOn
  have hσne : ∀ x ∈ m.I, m.σ x ^ 2 ≠ 0 := fun x hx => pow_ne_zero 2 (hS.σ_pos x hx).ne'
  set hh : ℝ → ℝ := fun y => 2 * m.μ y / m.σ y ^ 2 with hhh
  have hhc : ContinuousOn hh m.I :=
    (continuousOn_const.mul hμc).div (hσc.pow 2) hσne
  have hx0 := hS.x₀_mem
  have hSpd : ∀ x ∈ m.I, HasDerivAt (Sp m) (Sp m x * -(hh x)) x := by
    intro x hx
    have hint : HasDerivAt (fun u => ∫ y in m.x₀..u, hh y) (hh x) x :=
      intervalIntegral.integral_hasDerivAt_right
        (hhc.mono (hIc.uIcc_subset hx0 hx)).intervalIntegrable
        (hhc.stronglyMeasurableAtFilter hIo x hx) (hhc.continuousAt (hIo.mem_nhds hx))
    have := hint.neg.exp
    unfold Sp
    exact this
  have hSppos : ∀ x, 0 < Sp m x := fun x => Real.exp_pos _
  have hSpc : ContinuousOn (Sp m) m.I := fun x hx => (hSpd x hx).continuousAt.continuousWithinAt
  have hmpc : ContinuousOn (mp m) m.I := by
    unfold mp
    exact continuousOn_const.div ((hσc.pow 2).mul hSpc)
      (fun x hx => mul_ne_zero (hσne x hx) (hSppos x).ne')
  obtain ⟨hqC1, hxsI, hq'pos, hq'neg, hlimb, hgint, ⟨x1, hx1I, hLx1⟩⟩ := hA4
  have hqc : ContinuousOn (q m) m.I := hqC1.continuousOn
  set g : ℝ → ℝ := fun y => S.φ y * q m y * mp m y with hg
  have hgc : ContinuousOn g m.I := (hφc.mul hqc).mul hmpc
  set T : ℝ → ℝ := fun x => ∫ y in m.I ∩ Ioi x, g y with hT
  have hTsplit_le : ∀ c ∈ m.I, ∀ y ∈ m.I, c ≤ y → T y = T c - ∫ u in c..y, g u := by
    intro c hc y hy hcy
    have hsplit : m.I ∩ Ioi c = Ioc c y ∪ (m.I ∩ Ioi y) := by
      ext u; constructor
      · rintro ⟨hu, hcu⟩
        by_cases huy : u ≤ y
        · exact Or.inl ⟨hcu, huy⟩
        · exact Or.inr ⟨hu, lt_of_not_ge huy⟩
      · rintro (⟨hcu, huy⟩ | ⟨hu, hyu⟩)
        · exact ⟨hIc.out hc hy ⟨hcu.le, huy⟩, hcu⟩
        · exact ⟨hu, lt_of_le_of_lt hcy hyu⟩
    have hdisj : Disjoint (Ioc c y) (m.I ∩ Ioi y) := by
      rw [Set.disjoint_left]
      rintro u ⟨-, huy⟩ ⟨-, hyu⟩
      exact absurd huy (not_le.mpr hyu)
    have hint1 : IntegrableOn g (Ioc c y) := by
      have : ContinuousOn g (Icc c y) := hgc.mono (hIc.out hc hy)
      exact (this.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have hint2 : IntegrableOn g (m.I ∩ Ioi y) := hgint y hy
    simp only [hT]
    rw [hsplit, setIntegral_union hdisj (hIo.measurableSet.inter measurableSet_Ioi) hint1 hint2,
      intervalIntegral.integral_of_le hcy]
    ring
  have hTsplit : ∀ c ∈ m.I, ∀ y ∈ m.I, T y = T c - ∫ u in c..y, g u := by
    intro c hc y hy
    rcases le_total c y with hcy | hyc
    · exact hTsplit_le c hc y hy hcy
    · have := hTsplit_le y hy c hc hyc
      rw [intervalIntegral.integral_symm]
      linarith
  have hTd : ∀ x ∈ m.I, HasDerivAt T (-(g x)) x := by
    intro x hx
    have hint : HasDerivAt (fun u => ∫ y in x..u, g y) (g x) x :=
      intervalIntegral.integral_hasDerivAt_right (by simp)
        (hgc.stronglyMeasurableAtFilter hIo x hx) (hgc.continuousAt (hIo.mem_nhds hx))
    have h2 : HasDerivAt (fun u => T x - ∫ y in x..u, g y) (-(g x)) x := by
      simpa using hint.const_sub (T x)
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [hIo.mem_nhds hx] with y hy
    exact hTsplit x hx y hy
  have hLd : ∀ x ∈ m.I, HasDerivAt (Lfun m S) (-(deriv (q m) x * deriv S.φ x / Sp m x)) x := by
    intro x hx
    have hq : HasDerivAt (q m) (deriv (q m) x) x :=
      ((hqC1.differentiableOn (by norm_num)).differentiableAt (hIo.mem_nhds hx)).hasDerivAt
    have hφ1 : HasDerivAt (deriv S.φ) (deriv (deriv S.φ) x) x :=
      (((hS.φ_C2.deriv_of_isOpen hIo (m := 1) (by norm_num)).differentiableOn
        (by norm_num)).differentiableAt (hIo.mem_nhds hx)).hasDerivAt
    have hcomb := (((hq.mul hφ1).div (hSpd x hx) (hSppos x).ne').neg).sub ((hTd x hx).const_mul m.r)
    have hfun : Lfun m S = fun y => -((q m * deriv S.φ) y / Sp m y) - m.r * T y := by
      funext y; simp [Lfun, hT, hg]
    rw [hfun]
    refine hcomb.congr_deriv ?_
    have hode := hS.φ_ode x hx
    unfold gen at hode
    have hσ := hσne x hx
    have hσ1 : m.σ x ≠ 0 := (hS.σ_pos x hx).ne'
    have hSp := (hSppos x).ne'
    simp only [hg]
    unfold mp
    simp only [Pi.mul_apply, hhh]
    field_simp
    linear_combination (-2 * q m x) * hode
  have hLc : ContinuousOn (Lfun m S) m.I := fun x hx => (hLd x hx).continuousAt.continuousWithinAt
  have hIconv : Convex ℝ m.I := hIc.convex
  have hLdpos : ∀ x ∈ m.I, x < xs → 0 < deriv (Lfun m S) x := by
    intro x hx hxx
    rw [(hLd x hx).deriv]
    have h1 := hq'pos x hx hxx
    have h2 := hφ'neg x hx
    have h3 := hSppos x
    have : deriv (q m) x * deriv S.φ x < 0 := mul_neg_of_pos_of_neg h1 h2
    have : deriv (q m) x * deriv S.φ x / Sp m x < 0 := div_neg_of_neg_of_pos this h3
    linarith
  have hLdneg : ∀ x ∈ m.I, xs < x → deriv (Lfun m S) x < 0 := by
    intro x hx hxx
    rw [(hLd x hx).deriv]
    have h1 := hq'neg x hx hxx
    have h2 := hφ'neg x hx
    have h3 := hSppos x
    have : 0 < deriv (q m) x * deriv S.φ x := mul_pos_of_neg_of_neg h1 h2
    have : 0 < deriv (q m) x * deriv S.φ x / Sp m x := div_pos this h3
    linarith
  have hLmono : StrictMonoOn (Lfun m S) (m.I ∩ Iic xs) := by
    apply strictMonoOn_of_deriv_pos (hIconv.inter (convex_Iic xs)) (hLc.mono inter_subset_left)
    intro x hx
    rw [interior_inter, hIo.interior_eq, interior_Iic] at hx
    exact hLdpos x hx.1 hx.2
  have hLanti : StrictAntiOn (Lfun m S) (m.I ∩ Ici xs) := by
    apply strictAntiOn_of_deriv_neg (hIconv.inter (convex_Ici xs)) (hLc.mono inter_subset_left)
    intro x hx
    rw [interior_inter, hIo.interior_eq, interior_Ici] at hx
    exact hLdneg x hx.1 hx.2
  -- L ≥ 0 to the right of x*
  have hLnn : ∀ y ∈ m.I, xs ≤ y → 0 ≤ Lfun m S y := by
    intro y hy hxy
    obtain ⟨u, humono, humem, hufar⟩ := icg_l2_seq m.I hIo hIc xs hxsI
    have hut : Tendsto u atTop (upperEnd m.I) := by
      unfold upperEnd
      simp only [tendsto_iInf, tendsto_principal]
      intro c hc
      obtain ⟨N, hN⟩ := hufar c hc
      exact eventually_atTop.mpr ⟨N, fun n hn => ⟨humem n, hN n hn⟩⟩
    have hlim1 := hlimb.comp hut
    have hlim2 : Tendsto (fun n => T (u n)) atTop (𝓝 0) := by
      have hanti : Antitone (fun n => m.I ∩ Ioi (u n)) := by
        intro a b hab
        exact inter_subset_inter_right _ (Ioi_subset_Ioi (humono hab))
      have := tendsto_setIntegral_of_antitone (μ := volume) (f := g)
        (fun n => hIo.measurableSet.inter measurableSet_Ioi) hanti ⟨0, hgint (u 0) (humem 0)⟩
      have hempty : (⋂ n, m.I ∩ Ioi (u n)) = ∅ := by
        ext z
        simp only [mem_iInter, mem_inter_iff, mem_Ioi, mem_empty_iff_false, iff_false]
        intro hz
        obtain ⟨N, hN⟩ := hufar z (hz 0).1
        exact absurd (hz N).2 (not_lt.mpr (hN N le_rfl).le)
      rw [hempty, Measure.restrict_empty, integral_zero_measure] at this
      exact this
    have hlim : Tendsto (fun n => Lfun m S (u n)) atTop (𝓝 0) := by
      have := (hlim1.neg).sub (hlim2.const_mul m.r)
      simp only [neg_zero, mul_zero, sub_zero] at this
      refine this.congr (fun n => ?_)
      simp [Lfun, hT, hg, Function.comp]
    obtain ⟨N, hN⟩ := hufar y hy
    refine le_of_tendsto hlim (eventually_atTop.mpr ⟨N, fun n hn => ?_⟩)
    exact hLanti.antitoneOn ⟨hy, hxy⟩ ⟨humem n, hxy.trans (hN n hn).le⟩ (hN n hn).le
  have hright : ∀ x ∈ m.I, ∃ y ∈ m.I, x < y := by
    intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hIo x hx
    exact ⟨x + ε / 2, hball (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith),
      by linarith⟩
  have hLpos : ∀ x ∈ m.I, xs ≤ x → 0 < Lfun m S x := by
    intro x hx hxx
    obtain ⟨y, hy, hxy⟩ := hright x hx
    have := hLanti ⟨hx, hxx⟩ ⟨hy, hxx.trans hxy.le⟩ hxy
    linarith [hLnn y hy (hxx.trans hxy.le)]
  have hx1xs : x1 < xs := by
    by_contra hc; rw [not_lt] at hc
    linarith [hLpos x1 hx1I hc]
  have hsubI : Icc x1 xs ⊆ m.I := hIc.out hx1I hxsI
  obtain ⟨xh, hxhmem, hLxh⟩ := intermediate_value_Icc hx1xs.le (hLc.mono hsubI)
    (show (0 : ℝ) ∈ Icc (Lfun m S x1) (Lfun m S xs) from ⟨hLx1.le, (hLpos xs hxsI le_rfl).le⟩)
  have hxhI : xh ∈ m.I := hsubI hxhmem
  have hxhxs : xh < xs := lt_of_le_of_ne hxhmem.2 (by
    rintro rfl; linarith [hLpos xh hxsI le_rfl])
  have hLneg' : ∀ x ∈ m.I, x < xh → Lfun m S x < 0 := by
    intro x hx hxx
    have := hLmono ⟨hx, (hxx.trans hxhxs).le⟩ ⟨hxhI, hxhxs.le⟩ hxx
    linarith
  have hLpos' : ∀ x ∈ m.I, xh < x → 0 < Lfun m S x := by
    intro x hx hxx
    by_cases hxs' : x ≤ xs
    · have := hLmono ⟨hxhI, hxhxs.le⟩ ⟨hx, hxs'⟩ hxx
      linarith
    · exact hLpos x hx (le_of_not_ge hxs')
  have hcoef : ∀ x ∈ m.I, 0 < 2 * Sp m x / (m.σ x ^ 2 * deriv S.φ x ^ 2) := by
    intro x hx
    have := hSppos x
    have := hS.σ_pos x hx
    have := hφ'ne x hx
    positivity
  have hI'neg : ∀ x ∈ m.I, x < xh → deriv (Ifun m S) x < 0 := by
    intro x hx hxx
    rw [hB20 x hx]
    exact mul_neg_of_pos_of_neg (hcoef x hx) (hLneg' x hx hxx)
  have hI'pos : ∀ x ∈ m.I, xh < x → 0 < deriv (Ifun m S) x := by
    intro x hx hxx
    rw [hB20 x hx]
    exact mul_pos (hcoef x hx) (hLpos' x hx hxx)
  have hJ' : ∀ x ∈ m.I, deriv (Ifun m S) x ≠ 0 →
      deriv (Jfun m S) x = -(deriv (Ifun m S) x * S.φ x) := by
    intro x hx hne
    have hId : HasDerivAt (Ifun m S) (deriv (Ifun m S) x) x :=
      (differentiableAt_of_deriv_ne_zero hne).hasDerivAt
    have hRd : HasDerivAt (R m S m.π) (deriv (R m S m.π) x) x :=
      ((hS.Rπ_C2.differentiableOn (by norm_num)).differentiableAt (hIo.mem_nhds hx)).hasDerivAt
    have hφd : HasDerivAt S.φ (deriv S.φ x) x :=
      ((hS.φ_C2.differentiableOn (by norm_num)).differentiableAt (hIo.mem_nhds hx)).hasDerivAt
    have hJd := (hRd.sub ((hasDerivAt_id x).const_mul m.k)).sub (hId.mul hφd)
    have hfun : Jfun m S = (R m S m.π - fun y => m.k * id y) - Ifun m S * S.φ := by
      funext y; simp [Jfun]
    rw [hfun, hJd.deriv]
    have hIφ : Ifun m S x * deriv S.φ x = deriv (R m S m.π) x - m.k := by
      unfold Ifun; field_simp [hφ'ne x hx]
    linear_combination -hIφ
  have hxhpt : IsLemma2Point m S xh := by
    refine ⟨hxhI, fun x hx hxx => ?_, fun x hx hxx => ?_⟩
    · have h1 := hI'neg x hx hxx
      refine ⟨h1, ?_⟩
      rw [hJ' x hx h1.ne]
      have := hS.φ_pos x hx
      nlinarith
    · have h1 := hI'pos x hx hxx
      refine ⟨h1, ?_⟩
      rw [hJ' x hx h1.ne']
      have := hS.φ_pos x hx
      nlinarith
  -- part (ii)
  obtain ⟨hzsI, hA2s⟩ := hA2
  have hpart2 : ∀ x ∈ m.I, (x < zs → Ifun m S x < 0) ∧ (zs < x → 0 < Ifun m S x) := by
    intro x hx
    refine ⟨fun hxz => ?_, fun hxz => ?_⟩
    · unfold Ifun
      exact div_neg_of_pos_of_neg ((hA2s x hx).1 hxz) (hφ'neg x hx)
    · unfold Ifun
      exact div_pos_of_neg_of_neg ((hA2s x hx).2 hxz) (hφ'neg x hx)
  -- I(z*) = 0
  have hfz : deriv (R m S m.π) zs - m.k = 0 := by
    have hcont : ContinuousAt (fun y => deriv (R m S m.π) y - m.k) zs :=
      (hR'c.continuousAt (hIo.mem_nhds hzsI)).sub continuousAt_const
    rcases lt_trichotomy (deriv (R m S m.π) zs - m.k) 0 with h | h | h
    · obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
        ((hcont.eventually (gt_mem_nhds h)).and (hIo.mem_nhds hzsI))
      have := hball (y := zs - ε / 2) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
      have h2 := (hA2s _ this.2).1 (by linarith)
      linarith [this.1]
    · exact h
    · obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
        ((hcont.eventually (lt_mem_nhds h)).and (hIo.mem_nhds hzsI))
      have := hball (y := zs + ε / 2) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
      have h2 := (hA2s _ this.2).2 (by linarith)
      linarith [this.1]
  have hIzs : Ifun m S zs = 0 := by unfold Ifun; rw [hfz, zero_div]
  have hxhzs : xh < zs := by
    by_contra hc; rw [not_lt] at hc
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hIo zs hzsI
    have hxI : zs - ε / 2 ∈ m.I :=
      hball (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
    have hIanti : StrictAntiOn (Ifun m S) (m.I ∩ Iic xh) := by
      apply strictAntiOn_of_deriv_neg (hIconv.inter (convex_Iic xh)) (hIfc.mono inter_subset_left)
      intro x hx
      rw [interior_inter, hIo.interior_eq, interior_Iic] at hx
      exact hI'neg x hx.1 hx.2
    have h1 := hIanti ⟨hxI, show zs - ε / 2 ≤ xh by linarith⟩ ⟨hzsI, hc⟩ (by linarith)
    have h2 := (hpart2 _ hxI).1 (by linarith)
    linarith
  exact ⟨⟨xh, hxhpt, lt_min hxhxs hxhzs⟩, hpart2⟩
