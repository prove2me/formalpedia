-- Prove2me | solution 1 for MultiItemRev.Decomp.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T08:50:12.724635+00:00
-- url     : https://prove2.me/submissions/031f55c5-7742-408f-b786-05c594dd8a19

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace MultiItemRev.Decomp.T7Aux

open MultiItemRev.Decomp

lemma expRevenue_toENNReal_le {ι : Type*} (μ : Measure (ι → ℝ≥0)) (M : Mechanism ι) :
    (expRevenue μ M).toENNReal ≤ ∫⁻ x, ENNReal.ofReal (M.s x) ∂μ := by
  unfold expRevenue
  rw [EReal.toENNReal_sub (EReal.coe_ennreal_nonneg _), EReal.toENNReal_coe, EReal.toENNReal_coe]
  exact tsub_le_self

lemma rev_ge_of_nonneg {ι : Type*} [Fintype ι] (μ : Measure (ι → ℝ≥0)) (M : Mechanism ι)
    (hM : IsAdmissible M) (hs : ∀ x, 0 ≤ M.s x) :
    ∫⁻ x, ENNReal.ofReal (M.s x) ∂μ ≤ Rev μ := by
  have h0 : ∀ x, ENNReal.ofReal (-M.s x) = 0 :=
    fun x => ENNReal.ofReal_of_nonpos (by linarith [hs x])
  have hrev : expRevenue μ M = ((∫⁻ x, ENNReal.ofReal (M.s x) ∂μ : ℝ≥0∞) : EReal) := by
    unfold expRevenue
    simp [h0]
  have := le_iSup₂ (f := fun (M : Mechanism ι) (_ : IsAdmissible M) =>
    (expRevenue μ M).toENNReal) M hM
  rw [hrev, EReal.toENNReal_coe] at this
  exact this

/-- Posted bundle price `t`: `t * P(∑ y ≥ t) ≤ BRev`. -/
lemma bundle_price_le {ι : Type*} [Fintype ι] (μ : Measure (ι → ℝ≥0)) (t : ℝ≥0) :
    (t : ℝ≥0∞) * μ {y | t ≤ ∑ i, y i} ≤ BRev μ := by
  let M : Mechanism Unit :=
    ⟨fun x _ => if t ≤ x () then 1 else 0, fun x => if t ≤ x () then (t : ℝ) else 0⟩
  have hSm : MeasurableSet {x : Unit → ℝ≥0 | t ≤ x ()} :=
    measurableSet_le measurable_const (measurable_pi_apply ())
  have hadm : IsAdmissible M := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x i
      simp only [M]
      split_ifs <;> norm_num
    · intro x x'
      simp only [buyerPayoff, M, Finset.univ_unique, Finset.sum_singleton]
      split_ifs with h1 h2 h2
      · linarith
      · have := NNReal.coe_lt_coe.mpr (not_le.mp h2); linarith
      · have := NNReal.coe_le_coe.mpr h2; linarith
      · linarith
    · intro x
      simp only [buyerPayoff, M, Finset.univ_unique, Finset.sum_singleton]
      split_ifs with h1
      · have := NNReal.coe_le_coe.mpr h1; linarith
      · linarith
    · exact Measurable.ite hSm measurable_const measurable_const
  have hnn : ∀ x, 0 ≤ M.s x := by
    intro x; simp only [M]; split_ifs <;> simp
  have h := rev_ge_of_nonneg (oneGood (μ.map (fun x => ∑ i, x i))) M hadm hnn
  unfold BRev Rev1
  refine le_trans (le_of_eq ?_) h
  unfold oneGood
  have hsum : Measurable (fun x : ι → ℝ≥0 => ∑ i, x i) := by fun_prop
  have hc : Measurable (fun (t : ℝ≥0) (_ : Unit) => t) := by fun_prop
  have hMs : Measurable (fun x => ENNReal.ofReal (M.s x)) :=
    ENNReal.measurable_ofReal.comp hadm.2.2.2
  rw [lintegral_map hMs hc,
    lintegral_map (f := fun a : ℝ≥0 => ENNReal.ofReal (M.s fun _ => a)) (hMs.comp hc) hsum]
  have hS : MeasurableSet {y : ι → ℝ≥0 | t ≤ ∑ i, y i} := measurableSet_le measurable_const hsum
  rw [← lintegral_indicator_const hS]
  refine lintegral_congr fun y => ?_
  simp only [M, Set.indicator]
  split_ifs with h1 h2 <;> simp_all

/-- `BRev ≤ Rev`. -/
lemma brev_le_rev {ι : Type*} [Fintype ι] (μ : Measure (ι → ℝ≥0)) : BRev μ ≤ Rev μ := by
  have hsum : Measurable (fun x : ι → ℝ≥0 => ∑ i, x i) := by fun_prop
  have hc : Measurable (fun (t : ℝ≥0) (_ : Unit) => t) := by fun_prop
  unfold BRev Rev1 oneGood
  rw [Measure.map_map hc hsum]
  refine iSup₂_le fun M' hM' => ?_
  let φ : (ι → ℝ≥0) → (Unit → ℝ≥0) := (fun (t : ℝ≥0) (_ : Unit) => t) ∘ fun x => ∑ i, x i
  have hφ : Measurable φ := hc.comp hsum
  let M : Mechanism ι := ⟨fun x _ => M'.q (φ x) (), fun x => M'.s (φ x)⟩
  have hadm : IsAdmissible M := by
    refine ⟨fun x i => hM'.1 (φ x) (), ?_, ?_, hM'.2.2.2.comp hφ⟩
    · intro x x'
      have h := hM'.2.1 (φ x) (φ x')
      simpa [buyerPayoff, M, φ, Finset.mul_sum] using h
    · intro x
      have h := hM'.2.2.1 (φ x)
      simpa [buyerPayoff, M, φ, Finset.mul_sum] using h
  refine le_trans (le_of_eq ?_) (le_iSup₂ (f := fun (M : Mechanism ι) (_ : IsAdmissible M) =>
    (expRevenue μ M).toENNReal) M hadm)
  congr 1
  unfold expRevenue
  rw [lintegral_map (f := fun x => ENNReal.ofReal (M'.s x))
      (ENNReal.measurable_ofReal.comp hM'.2.2.2) hφ,
    lintegral_map (f := fun x => ENNReal.ofReal (-M'.s x))
      (ENNReal.measurable_ofReal.comp hM'.2.2.2.neg) hφ]

/-- Payoff is lower semicontinuous, hence measurable. -/
lemma payoff_measurable {ι : Type*} [Fintype ι] (M : Mechanism ι) (hIC : IsIC M) :
    Measurable (buyerPayoff M) := by
  apply LowerSemicontinuous.measurable
  intro x y hy
  have hg : Continuous fun x' : ι → ℝ≥0 => ∑ i, M.q x i * (x' i : ℝ) - M.s x := by fun_prop
  have h1 : ∀ᶠ x' in 𝓝 x, y < ∑ i, M.q x i * (x' i : ℝ) - M.s x :=
    (hg.tendsto x).eventually (lt_mem_nhds hy)
  exact h1.mono fun x' hx' => lt_of_lt_of_le hx' (hIC x' x)

/-- The key section bound: a "partial" mechanism on one block, with an outside payoff `r ≤ c`. -/
lemma section_bound {ι : Type*} [Fintype ι] (μ : Measure (ι → ℝ≥0))
    (q : (ι → ℝ≥0) → ι → ℝ) (r s : (ι → ℝ≥0) → ℝ) (c : ℝ≥0)
    (hq : ∀ y i, 0 ≤ q y i ∧ q y i ≤ 1) (hr : ∀ y, 0 ≤ r y ∧ r y ≤ c)
    (hIC : ∀ y y', ∑ i, q y' i * (y i : ℝ) + r y' - s y' ≤ ∑ i, q y i * (y i : ℝ) + r y - s y)
    (hIR : ∀ y, 0 ≤ ∑ i, q y i * (y i : ℝ) + r y - s y)
    (hu : Measurable fun y => ∑ i, q y i * (y i : ℝ) + r y - s y) :
    ∫⁻ y, Set.indicator {y | c ≤ ∑ i, y i} (fun y => ENNReal.ofReal (s y)) y ∂μ
      ≤ Rev μ + BRev μ := by
  obtain ⟨u, hu_eq⟩ : ∃ u : (ι → ℝ≥0) → ℝ, ∀ y, u y = ∑ i, q y i * (y i : ℝ) + r y - s y :=
    ⟨_, fun _ => rfl⟩
  have hum : Measurable u := by
    have : u = fun y => ∑ i, q y i * (y i : ℝ) + r y - s y := funext hu_eq
    rw [this]; exact hu
  have hsub : ∀ y y', u y + ∑ i, q y i * ((y' i : ℝ) - y i) ≤ u y' := by
    intro y y'
    have h := hIC y' y
    have e : ∑ i, q y i * ((y' i : ℝ) - y i)
        = ∑ i, q y i * (y' i : ℝ) - ∑ i, q y i * (y i : ℝ) := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [hu_eq, hu_eq, e]; linarith
  obtain ⟨yn, hyn, hynm⟩ : ∃ yn : (ι → ℝ≥0) → ℕ → (ι → ℝ≥0),
      (∀ y n i, ((yn y n i : ℝ≥0) : ℝ) = (y i : ℝ) * (1 + ((n : ℝ) + 1)⁻¹)) ∧
      ∀ n, Measurable fun y => yn y n :=
    ⟨fun y n i => y i * (1 + ((n : ℝ≥0) + 1)⁻¹),
      fun y n i => by
        simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_one, NNReal.coe_inv,
          NNReal.coe_natCast],
      fun n => by fun_prop⟩
  have hsum_yn : ∀ (h : ι → ℝ) y n,
      ∑ i, h i * ((yn y n i : ℝ) - y i) = (∑ i, h i * (y i : ℝ)) * ((n : ℝ) + 1)⁻¹ := by
    intro h y n
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [hyn]; ring
  obtain ⟨a, ha⟩ : ∃ a : (ι → ℝ≥0) → ℕ → ℝ,
      ∀ y n, a y n = (u (yn y n) - u y) * ((n : ℝ) + 1) :=
    ⟨fun y n => (u (yn y n) - u y) * ((n : ℝ) + 1), fun _ _ => rfl⟩
  have F1 : ∀ y (h : ι → ℝ), (∀ y', u y + ∑ i, h i * ((y' i : ℝ) - y i) ≤ u y') →
      ∀ n : ℕ, ∑ i, h i * (y i : ℝ) ≤ a y n := by
    intro y h hh n
    have k := hh (yn y n)
    rw [hsum_yn] at k
    rw [ha]
    have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have k2 := mul_le_mul_of_nonneg_right
      (show (∑ i, h i * (y i : ℝ)) * ((n : ℝ) + 1)⁻¹ ≤ u (yn y n) - u y by linarith) hp.le
    rwa [inv_mul_cancel_right₀ hp.ne'] at k2
  have F2 : ∀ y n, a y n ≤ ∑ i, q (yn y n) i * (y i : ℝ) := by
    intro y n
    have k := hsub (yn y n) y
    have hs : ∑ i, q (yn y n) i * ((y i : ℝ) - yn y n i)
        = -((∑ i, q (yn y n) i * (y i : ℝ)) * ((n : ℝ) + 1)⁻¹) := by
      rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [hyn]; ring
    rw [hs] at k
    rw [ha]
    have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have k2 := mul_le_mul_of_nonneg_right
      (show u (yn y n) - u y ≤ (∑ i, q (yn y n) i * (y i : ℝ)) * ((n : ℝ) + 1)⁻¹ by linarith)
      hp.le
    rwa [inv_mul_cancel_right₀ hp.ne'] at k2
  have F3 : ∀ (h : ι → ℝ), (∀ i, 0 ≤ h i ∧ h i ≤ 1) → ∀ y : ι → ℝ≥0,
      0 ≤ ∑ i, h i * (y i : ℝ) ∧ ∑ i, h i * (y i : ℝ) ≤ ∑ i, (y i : ℝ) := by
    intro h hh y
    exact ⟨Finset.sum_nonneg fun i _ => mul_nonneg (hh i).1 (NNReal.coe_nonneg _),
      Finset.sum_le_sum fun i _ => mul_le_of_le_one_left (NNReal.coe_nonneg _) (hh i).2⟩
  have key : ∀ y, ∃ g : ι → ℝ, (∀ i, 0 ≤ g i ∧ g i ≤ 1) ∧
      (∀ y', u y + ∑ i, g i * ((y' i : ℝ) - y i) ≤ u y') ∧
      ∑ i, g i * (y i : ℝ) = ⨅ n, a y n := by
    intro y
    have hK : IsCompact (Set.Icc (0 : ι → ℝ) 1) := isCompact_Icc
    have hmem : ∀ n, q (yn y n) ∈ Set.Icc (0 : ι → ℝ) 1 := fun n =>
      ⟨fun i => (hq _ i).1, fun i => (hq _ i).2⟩
    obtain ⟨g, hgK, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
    have hg01 : ∀ i, 0 ≤ g i ∧ g i ≤ 1 := fun i => ⟨hgK.1 i, hgK.2 i⟩
    have hcoord : ∀ i, Tendsto (fun k => q (yn y (φ k)) i) atTop (𝓝 (g i)) :=
      fun i => ((continuous_apply i).tendsto g).comp hlim
    have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
    have hε : Tendsto (fun k => ((φ k : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφt
      simp only [one_div] at this
      exact this
    have hyl : ∀ i, Tendsto (fun k => ((yn y (φ k) i : ℝ≥0) : ℝ)) atTop (𝓝 (y i : ℝ)) := by
      intro i
      simp only [hyn]
      have := (tendsto_const_nhds (x := (y i : ℝ))).mul (tendsto_const_nhds (x := (1 : ℝ)).add hε)
      simpa using this
    have hul : Tendsto (fun k => u (yn y (φ k))) atTop (𝓝 (u y)) := by
      have hlow : ∀ k, u y ≤ u (yn y (φ k)) := by
        intro k
        have h1 := F1 y (q y) (hsub y) (φ k)
        rw [ha] at h1
        have h0 := (F3 (q y) (hq y) y).1
        have hp : (0 : ℝ) < (φ k : ℝ) + 1 := by positivity
        nlinarith
      have hup : ∀ k, u (yn y (φ k)) ≤ u y + (∑ i, (y i : ℝ)) * ((φ k : ℝ) + 1)⁻¹ := by
        intro k
        have h2 := F2 y (φ k)
        rw [ha] at h2
        have h3 := (F3 _ (hq (yn y (φ k))) y).2
        have hp : (0 : ℝ) < (φ k : ℝ) + 1 := by positivity
        have : u (yn y (φ k)) - u y ≤ (∑ i, (y i : ℝ)) * ((φ k : ℝ) + 1)⁻¹ := by
          rw [le_mul_inv_iff₀ hp]; linarith
        linarith
      have htop : Tendsto (fun k => u y + (∑ i, (y i : ℝ)) * ((φ k : ℝ) + 1)⁻¹) atTop
          (𝓝 (u y)) := by
        simpa using (tendsto_const_nhds (x := u y)).add
          ((tendsto_const_nhds (x := ∑ i, (y i : ℝ))).mul hε)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htop hlow hup
    have hgsub : ∀ y', u y + ∑ i, g i * ((y' i : ℝ) - y i) ≤ u y' := by
      intro y'
      have hT : Tendsto (fun k => u (yn y (φ k)) +
          ∑ i, q (yn y (φ k)) i * ((y' i : ℝ) - yn y (φ k) i))
          atTop (𝓝 (u y + ∑ i, g i * ((y' i : ℝ) - y i))) :=
        hul.add (tendsto_finsetSum _ fun i _ =>
          (hcoord i).mul (tendsto_const_nhds.sub (hyl i)))
      exact le_of_tendsto' hT fun k => hsub _ y'
    refine ⟨g, hg01, hgsub, ?_⟩
    have hbdd : BddBelow (Set.range (a y)) :=
      ⟨∑ i, g i * (y i : ℝ), by rintro _ ⟨n, rfl⟩; exact F1 y g hgsub n⟩
    apply le_antisymm
    · exact le_ciInf fun n => F1 y g hgsub n
    · have hT : Tendsto (fun k => ∑ i, q (yn y (φ k)) i * (y i : ℝ)) atTop
          (𝓝 (∑ i, g i * (y i : ℝ))) :=
        tendsto_finsetSum _ fun i _ => (hcoord i).mul tendsto_const_nhds
      exact ge_of_tendsto' hT fun k => (ciInf_le hbdd (φ k)).trans (F2 y (φ k))
  choose g hg01 hgsub hgD using key
  have hDmeas : Measurable fun y => ⨅ n, a y n := by
    refine Measurable.iInf (f := fun n y => a y n) fun n => ?_
    have : (fun y => a y n) = fun y => (u (yn y n) - u y) * ((n : ℝ) + 1) :=
      funext fun y => ha y n
    rw [this]
    exact ((hum.comp (hynm n)).sub hum).mul_const _
  let Mt : Mechanism ι := ⟨g, fun y => (⨅ n, a y n) - u y + u 0⟩
  have hMt : IsAdmissible Mt := by
    refine ⟨fun y i => hg01 y i, ?_, ?_, ?_⟩
    · intro y y'
      simp only [buyerPayoff, Mt]
      rw [← hgD y, ← hgD y']
      have k := hgsub y' y
      have e : ∑ i, g y' i * ((y i : ℝ) - y' i)
          = ∑ i, g y' i * (y i : ℝ) - ∑ i, g y' i * (y' i : ℝ) := by
        rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
      linarith
    · intro y
      simp only [buyerPayoff, Mt]
      rw [← hgD y]
      have k := hsub 0 y
      have h0 : 0 ≤ ∑ i, q 0 i * ((y i : ℝ) - ((0 : ι → ℝ≥0) i : ℝ)) :=
        Finset.sum_nonneg fun i _ => mul_nonneg (hq 0 i).1 (by simp)
      linarith
    · exact (hDmeas.sub hum).add_const _
  have hMt_nonneg : ∀ y, 0 ≤ Mt.s y := by
    intro y
    simp only [Mt]
    rw [← hgD y]
    have k := hgsub y 0
    have e : ∑ i, g y i * (((0 : ι → ℝ≥0) i : ℝ) - y i) = -∑ i, g y i * (y i : ℝ) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ => by simp
    linarith
  have hpt : ∀ y, s y ≤ Mt.s y + c := by
    intro y
    simp only [Mt]
    have hD : ∑ i, q y i * (y i : ℝ) ≤ ⨅ n, a y n := le_ciInf fun n => F1 y (q y) (hsub y) n
    have hu0 : 0 ≤ u 0 := by rw [hu_eq]; exact hIR 0
    have := hu_eq y
    linarith [(hr y).2]
  have hS : MeasurableSet {y : ι → ℝ≥0 | c ≤ ∑ i, y i} :=
    measurableSet_le measurable_const (by fun_prop)
  have hMts : Measurable fun y => ENNReal.ofReal (Mt.s y) :=
    ENNReal.measurable_ofReal.comp hMt.2.2.2
  calc ∫⁻ y, Set.indicator {y | c ≤ ∑ i, y i} (fun y => ENNReal.ofReal (s y)) y ∂μ
      ≤ ∫⁻ y, (ENNReal.ofReal (Mt.s y) +
          Set.indicator {y | c ≤ ∑ i, y i} (fun _ => (c : ℝ≥0∞)) y) ∂μ := by
        refine lintegral_mono fun y => ?_
        by_cases hy : y ∈ {y : ι → ℝ≥0 | c ≤ ∑ i, y i}
        · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
          calc ENNReal.ofReal (s y) ≤ ENNReal.ofReal (Mt.s y + c) :=
                ENNReal.ofReal_le_ofReal (hpt y)
            _ = ENNReal.ofReal (Mt.s y) + (c : ℝ≥0∞) := by
                rw [ENNReal.ofReal_add (hMt_nonneg y) (NNReal.coe_nonneg c),
                  ENNReal.ofReal_coe_nnreal]
        · rw [Set.indicator_of_notMem hy]; exact zero_le'
    _ = ∫⁻ y, ENNReal.ofReal (Mt.s y) ∂μ + (c : ℝ≥0∞) * μ {y | c ≤ ∑ i, y i} := by
        rw [lintegral_add_left hMts, lintegral_indicator_const hS]
    _ ≤ Rev μ + BRev μ :=
        add_le_add (rev_ge_of_nonneg μ Mt hMt hMt_nonneg) (bundle_price_le μ c)

lemma sectionY {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] (μY : Measure (ι₁ → ℝ≥0))
    (M : Mechanism (ι₁ ⊕ ι₂)) (hM : IsAdmissible M) (z : ι₂ → ℝ≥0) :
    ∫⁻ y, Set.indicator {y : ι₁ → ℝ≥0 | ∑ j, z j ≤ ∑ i, y i}
      (fun y => ENNReal.ofReal (M.s ((MeasurableEquiv.sumPiEquivProdPi
        (fun _ : ι₁ ⊕ ι₂ => ℝ≥0)).symm (y, z)))) y ∂μY ≤ Rev μY + BRev μY := by
  obtain ⟨hF, hIC, hIR, hs⟩ := hM
  set e := (MeasurableEquiv.sumPiEquivProdPi (fun _ : ι₁ ⊕ ι₂ => ℝ≥0)).symm with he
  have h1 : ∀ (p : (ι₁ → ℝ≥0) × (ι₂ → ℝ≥0)) i, e p (Sum.inl i) = p.1 i := fun _ _ => rfl
  have h2 : ∀ (p : (ι₁ → ℝ≥0) × (ι₂ → ℝ≥0)) j, e p (Sum.inr j) = p.2 j := fun _ _ => rfl
  have hb := payoff_measurable M hIC
  refine section_bound μY (fun y i => M.q (e (y, z)) (Sum.inl i))
    (fun y => ∑ j, M.q (e (y, z)) (Sum.inr j) * (z j : ℝ)) (fun y => M.s (e (y, z)))
    (∑ j, z j) (fun y i => hF _ _) ?_ ?_ ?_ ?_
  · intro y
    refine ⟨Finset.sum_nonneg fun j _ => mul_nonneg (hF _ _).1 (NNReal.coe_nonneg _), ?_⟩
    rw [NNReal.coe_sum]
    exact Finset.sum_le_sum fun j _ => mul_le_of_le_one_left (NNReal.coe_nonneg _) (hF _ _).2
  · intro y y'
    have h := hIC (e (y, z)) (e (y', z))
    simp only [buyerPayoff, Fintype.sum_sum_type, h1, h2] at h
    beta_reduce
    linarith
  · intro y
    have h := hIR (e (y, z))
    simp only [buyerPayoff, Fintype.sum_sum_type, h1, h2] at h
    beta_reduce
    linarith
  · have hm : Measurable fun y : ι₁ → ℝ≥0 => buyerPayoff M (e (y, z)) :=
      hb.comp (e.measurable.comp (by fun_prop))
    convert hm using 1
    funext y
    simp only [buyerPayoff, Fintype.sum_sum_type, h1, h2]

lemma sectionZ {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] (μZ : Measure (ι₂ → ℝ≥0))
    (M : Mechanism (ι₁ ⊕ ι₂)) (hM : IsAdmissible M) (y : ι₁ → ℝ≥0) :
    ∫⁻ z, Set.indicator {z : ι₂ → ℝ≥0 | ∑ i, y i ≤ ∑ j, z j}
      (fun z => ENNReal.ofReal (M.s ((MeasurableEquiv.sumPiEquivProdPi
        (fun _ : ι₁ ⊕ ι₂ => ℝ≥0)).symm (y, z)))) z ∂μZ ≤ Rev μZ + BRev μZ := by
  obtain ⟨hF, hIC, hIR, hs⟩ := hM
  set e := (MeasurableEquiv.sumPiEquivProdPi (fun _ : ι₁ ⊕ ι₂ => ℝ≥0)).symm with he
  have h1 : ∀ (p : (ι₁ → ℝ≥0) × (ι₂ → ℝ≥0)) i, e p (Sum.inl i) = p.1 i := fun _ _ => rfl
  have h2 : ∀ (p : (ι₁ → ℝ≥0) × (ι₂ → ℝ≥0)) j, e p (Sum.inr j) = p.2 j := fun _ _ => rfl
  have hb := payoff_measurable M hIC
  refine section_bound μZ (fun z j => M.q (e (y, z)) (Sum.inr j))
    (fun z => ∑ i, M.q (e (y, z)) (Sum.inl i) * (y i : ℝ)) (fun z => M.s (e (y, z)))
    (∑ i, y i) (fun z j => hF _ _) ?_ ?_ ?_ ?_
  · intro z
    refine ⟨Finset.sum_nonneg fun j _ => mul_nonneg (hF _ _).1 (NNReal.coe_nonneg _), ?_⟩
    rw [NNReal.coe_sum]
    exact Finset.sum_le_sum fun j _ => mul_le_of_le_one_left (NNReal.coe_nonneg _) (hF _ _).2
  · intro z z'
    have h := hIC (e (y, z)) (e (y, z'))
    simp only [buyerPayoff, Fintype.sum_sum_type, h1, h2] at h
    beta_reduce
    linarith
  · intro z
    have h := hIR (e (y, z))
    simp only [buyerPayoff, Fintype.sum_sum_type, h1, h2] at h
    beta_reduce
    linarith
  · have hm : Measurable fun z : ι₂ → ℝ≥0 => buyerPayoff M (e (y, z)) :=
      hb.comp (e.measurable.comp (by fun_prop))
    convert hm using 1
    funext z
    simp only [buyerPayoff, Fintype.sum_sum_type, h1, h2]
    ring

theorem part1 {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (μY : Measure (ι₁ → ℝ≥0)) (μZ : Measure (ι₂ → ℝ≥0))
    [IsProbabilityMeasure μY] [IsProbabilityMeasure μZ] :
    Rev (jointLaw μY μZ) ≤ Rev μY + Rev μZ + BRev μY + BRev μZ := by
  refine iSup₂_le fun M hM => (expRevenue_toENNReal_le _ M).trans ?_
  unfold jointLaw
  rw [lintegral_map_equiv]
  set e := (MeasurableEquiv.sumPiEquivProdPi (fun _ : ι₁ ⊕ ι₂ => ℝ≥0)).symm with he
  set F : (ι₁ → ℝ≥0) × (ι₂ → ℝ≥0) → ℝ≥0∞ := fun p => ENNReal.ofReal (M.s (e p)) with hFdef
  have hFm : Measurable F := ENNReal.measurable_ofReal.comp (hM.2.2.2.comp e.measurable)
  set A := {p : (ι₁ → ℝ≥0) × (ι₂ → ℝ≥0) | ∑ j, p.2 j ≤ ∑ i, p.1 i} with hA
  set B := {p : (ι₁ → ℝ≥0) × (ι₂ → ℝ≥0) | ∑ i, p.1 i ≤ ∑ j, p.2 j} with hB
  have hAm : MeasurableSet A := measurableSet_le (by fun_prop) (by fun_prop)
  have hBm : MeasurableSet B := measurableSet_le (by fun_prop) (by fun_prop)
  calc ∫⁻ p, F p ∂(μY.prod μZ)
      ≤ ∫⁻ p, (A.indicator F p + B.indicator F p) ∂(μY.prod μZ) := by
        refine lintegral_mono fun p => ?_
        rcases le_total (∑ j, p.2 j) (∑ i, p.1 i) with h | h
        · rw [Set.indicator_of_mem (show p ∈ A from h)]
          exact le_self_add
        · rw [Set.indicator_of_mem (show p ∈ B from h)]
          exact le_add_self
    _ = ∫⁻ p, A.indicator F p ∂(μY.prod μZ) + ∫⁻ p, B.indicator F p ∂(μY.prod μZ) :=
        lintegral_add_left (hFm.indicator hAm) _
    _ ≤ (Rev μY + BRev μY) + (Rev μZ + BRev μZ) := by
        refine add_le_add ?_ ?_
        · rw [lintegral_prod_symm _ (hFm.indicator hAm).aemeasurable]
          calc _ ≤ ∫⁻ _z, (Rev μY + BRev μY) ∂μZ := lintegral_mono fun z => sectionY μY M hM z
            _ = _ := by rw [lintegral_const, measure_univ, mul_one]
        · rw [lintegral_prod _ (hFm.indicator hBm).aemeasurable]
          calc _ ≤ ∫⁻ _y, (Rev μZ + BRev μZ) ∂μY := lintegral_mono fun y => sectionZ μZ M hM y
            _ = _ := by rw [lintegral_const, measure_univ, mul_one]
    _ = Rev μY + Rev μZ + BRev μY + BRev μZ := by ring

end MultiItemRev.Decomp.T7Aux

open MeasureTheory MultiItemRev.Decomp NNReal ENNReal in
theorem solution {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [Nonempty ι₁] [Nonempty ι₂]
    (μY : Measure (ι₁ → ℝ≥0)) (μZ : Measure (ι₂ → ℝ≥0))
    [IsProbabilityMeasure μY] [IsProbabilityMeasure μZ] :
    Rev (jointLaw μY μZ) ≤ Rev μY + Rev μZ + BRev μY + BRev μZ ∧
      Rev μY + Rev μZ + BRev μY + BRev μZ ≤ 2 * (Rev μY + Rev μZ) := by
  refine ⟨MultiItemRev.Decomp.T7Aux.part1 μY μZ, ?_⟩
  have h1 := MultiItemRev.Decomp.T7Aux.brev_le_rev μY
  have h2 := MultiItemRev.Decomp.T7Aux.brev_le_rev μZ
  calc Rev μY + Rev μZ + BRev μY + BRev μZ ≤ Rev μY + Rev μZ + Rev μY + Rev μZ := by gcongr
    _ = 2 * (Rev μY + Rev μZ) := by ring
