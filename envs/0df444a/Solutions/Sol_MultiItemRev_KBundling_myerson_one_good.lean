-- Prove2me | solution 1 for MultiItemRev.KBundling.myerson_one_good
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T15:25:48.312931+00:00
-- url     : https://prove2.me/submissions/5e66b0b5-e80d-4bb1-9e4b-42d535de7a73

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace KBMyersonAux
open MultiItemRev.Decomp

/-- allocation and payment of a one-good mechanism at value `t`. -/
noncomputable def qq (M : Mechanism Unit) (t : ℝ≥0) : ℝ := M.q (fun _ => t) ()
noncomputable def ss (M : Mechanism Unit) (t : ℝ≥0) : ℝ := M.s (fun _ => t)

lemma ic_pair (M : Mechanism Unit) (hIC : IsIC M) (a b : ℝ≥0) :
    qq M b * a - ss M b ≤ qq M a * a - ss M a := by
  have := hIC (fun _ => a) (fun _ => b)
  simpa [buyerPayoff, qq, ss] using this

lemma q_mono (M : Mechanism Unit) (hIC : IsIC M) {a b : ℝ≥0} (hab : a ≤ b) :
    qq M a ≤ qq M b := by
  rcases eq_or_lt_of_le hab with h | h
  · rw [h]
  have h1 := ic_pair M hIC a b
  have h2 := ic_pair M hIC b a
  have hab' : (a : ℝ) < b := h
  nlinarith

lemma s_step (M : Mechanism Unit) (hIC : IsIC M) (a b : ℝ≥0) :
    ss M b - ss M a ≤ (qq M b - qq M a) * b := by
  have h2 := ic_pair M hIC b a
  linarith

lemma s_zero (M : Mechanism Unit) (hIR : IsIR M) : ss M 0 ≤ 0 := by
  have := hIR (fun _ => 0)
  simp [buyerPayoff] at this
  simpa [ss] using this

lemma q_le_one (M : Mechanism Unit) (hF : IsFeasible M) (t : ℝ≥0) : qq M t ≤ 1 := (hF _ _).2
lemma q_nonneg (M : Mechanism Unit) (hF : IsFeasible M) (t : ℝ≥0) : 0 ≤ qq M t := (hF _ _).1

/-- increments of the allocation along the grid of mesh `h`. -/
noncomputable def D (M : Mechanism Unit) (h : ℝ≥0) (j : ℕ) : ℝ :=
  qq M (((j : ℝ≥0) + 1) * h) - qq M ((j : ℝ≥0) * h)

lemma D_nonneg (M : Mechanism Unit) (hIC : IsIC M) (h : ℝ≥0) (j : ℕ) : 0 ≤ D M h j := by
  unfold D
  have : (j : ℝ≥0) * h ≤ ((j : ℝ≥0) + 1) * h := by gcongr; exact le_self_add
  linarith [q_mono M hIC this]

lemma chain (M : Mechanism Unit) (hIC : IsIC M) (hIR : IsIR M) (h : ℝ≥0) (J : ℕ) :
    ss M ((J : ℝ≥0) * h) ≤
      ∑ j ∈ Finset.range J, D M h j * (((j : ℝ≥0) + 1) * h : ℝ≥0) := by
  induction J with
  | zero => simpa using s_zero M hIR
  | succ J ih =>
    rw [Finset.sum_range_succ]
    have := s_step M hIC ((J : ℝ≥0) * h) (((J : ℝ≥0) + 1) * h)
    have hc : ((J + 1 : ℕ) : ℝ≥0) = (J : ℝ≥0) + 1 := by push_cast; ring
    rw [hc]
    have hD : D M h J = qq M (((J : ℝ≥0) + 1) * h) - qq M ((J : ℝ≥0) * h) := rfl
    rw [hD]
    linarith

lemma pointwise (M : Mechanism Unit) (hIC : IsIC M) (hIR : IsIR M) (hF : IsFeasible M)
    (h : ℝ≥0) (hh : 0 < h) (x : ℝ≥0) :
    ss M x ≤ ∑ j ∈ Finset.range (⌊x / h⌋₊ + 1), D M h j * (((j : ℝ≥0) + 1) * h : ℝ≥0) := by
  set J := ⌊x / h⌋₊
  have hJ1 : (J : ℝ≥0) * h ≤ x := by
    have := Nat.floor_le (a := x / h) (by positivity)
    rwa [le_div_iff₀ hh] at this
  have hJ2 : x < ((J : ℝ≥0) + 1) * h := by
    have := Nat.lt_floor_add_one (x / h)
    rwa [div_lt_iff₀ hh] at this
  rw [Finset.sum_range_succ]
  have hc := chain M hIC hIR h J
  have hs := s_step M hIC ((J : ℝ≥0) * h) x
  have hq1 := q_mono M hIC hJ1
  have hq2 := q_mono M hIC hJ2.le
  have hx2 : (x : ℝ) ≤ (((J : ℝ≥0) + 1) * h : ℝ≥0) := by exact_mod_cast hJ2.le
  have hx0 : (0 : ℝ) ≤ x := x.2
  have : (qq M x - qq M ((J : ℝ≥0) * h)) * x ≤ D M h J * (((J : ℝ≥0) + 1) * h : ℝ≥0) := by
    unfold D
    apply mul_le_mul (by linarith) hx2 hx0 (by linarith)
  linarith

/-- the pointwise majorant `G_h`. -/
noncomputable def G (M : Mechanism Unit) (h : ℝ≥0) (x : ℝ≥0) : ℝ≥0∞ :=
  ∑' j : ℕ, (Set.Ici ((j : ℝ≥0) * h)).indicator
    (fun _ => ENNReal.ofReal (D M h j * (((j : ℝ≥0) + 1) * h : ℝ≥0))) x

lemma ofReal_s_le_G (M : Mechanism Unit) (hIC : IsIC M) (hIR : IsIR M) (hF : IsFeasible M)
    (h : ℝ≥0) (hh : 0 < h) (x : ℝ≥0) :
    ENNReal.ofReal (ss M x) ≤ G M h x := by
  refine le_trans (ENNReal.ofReal_le_ofReal (pointwise M hIC hIR hF h hh x)) ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (D_nonneg M hIC h j) (by positivity))]
  refine le_trans (le_of_eq ?_) (ENNReal.sum_le_tsum (Finset.range (⌊x / h⌋₊ + 1)))
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Set.indicator_of_mem]
  show (j : ℝ≥0) * h ≤ x
  have hj' : j ≤ ⌊x / h⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have := Nat.floor_le (a := x / h) (by positivity)
  rw [le_div_iff₀ hh] at this
  calc (j : ℝ≥0) * h ≤ (⌊x / h⌋₊ : ℝ≥0) * h := by gcongr
    _ ≤ x := this

/-- Myerson's upper bound. -/
lemma rev1_le_sup (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] :
    Rev1 ν ≤ ⨆ p : ℝ≥0, (p : ℝ≥0∞) * ν {t | p ≤ t} := by
  set R := ⨆ p : ℝ≥0, (p : ℝ≥0∞) * ν {t | p ≤ t}
  unfold Rev1 Rev
  refine iSup₂_le fun M hM => ?_
  obtain ⟨hF, hIC, hIR, hm⟩ := hM
  have hle : (expRevenue (oneGood ν) M).toENNReal ≤ ∫⁻ x, ENNReal.ofReal (M.s x) ∂(oneGood ν) := by
    unfold expRevenue
    rw [EReal.toENNReal_sub (EReal.coe_ennreal_nonneg _), EReal.toENNReal_coe,
      EReal.toENNReal_coe]
    exact tsub_le_self
  refine le_trans hle ?_
  have hc : Measurable (fun (t : ℝ≥0) (_ : Unit) => t) := by fun_prop
  rw [oneGood, lintegral_map (f := fun x => ENNReal.ofReal (M.s x))
    (ENNReal.measurable_ofReal.comp hm) hc]
  refine ENNReal.le_of_forall_pos_le_add fun h hh _ => ?_
  calc ∫⁻ t, ENNReal.ofReal (M.s (fun _ => t)) ∂ν ≤ ∫⁻ t, G M h t ∂ν :=
        lintegral_mono fun t => ofReal_s_le_G M hIC hIR hF h hh t
    _ = ∑' j : ℕ, ENNReal.ofReal (D M h j * (((j : ℝ≥0) + 1) * h : ℝ≥0)) *
          ν (Set.Ici ((j : ℝ≥0) * h)) := by
        unfold G
        rw [lintegral_tsum (fun j => (Measurable.indicator measurable_const
          measurableSet_Ici).aemeasurable)]
        congr 1
        funext j
        rw [lintegral_indicator_const measurableSet_Ici]
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (D M h j) * (R + h) := by
        refine ENNReal.tsum_le_tsum fun j => ?_
        rw [ENNReal.ofReal_mul (D_nonneg M hIC h j), mul_assoc]
        gcongr
        rw [ENNReal.ofReal_coe_nnreal]
        calc ((((j : ℝ≥0) + 1) * h : ℝ≥0) : ℝ≥0∞) * ν (Set.Ici ((j : ℝ≥0) * h))
            = (((j : ℝ≥0) * h : ℝ≥0) : ℝ≥0∞) * ν (Set.Ici ((j : ℝ≥0) * h)) +
                (h : ℝ≥0∞) * ν (Set.Ici ((j : ℝ≥0) * h)) := by
              rw [add_mul, one_mul, ENNReal.coe_add, add_mul]
          _ ≤ R + h := by
              refine add_le_add ?_ ?_
              · exact le_iSup (fun p : ℝ≥0 => (p : ℝ≥0∞) * ν {t | p ≤ t}) ((j : ℝ≥0) * h)
              · calc (h : ℝ≥0∞) * ν (Set.Ici ((j : ℝ≥0) * h)) ≤ (h : ℝ≥0∞) * 1 := by
                      gcongr; exact prob_le_one
                  _ = h := mul_one _
    _ = (∑' j : ℕ, ENNReal.ofReal (D M h j)) * (R + h) := ENNReal.tsum_mul_right
    _ ≤ 1 * (R + h) := by
        gcongr
        refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => D_nonneg M hIC h j)]
        refine ENNReal.ofReal_le_one.mpr ?_
        have : ∑ j ∈ Finset.range n, D M h j = qq M ((n : ℝ≥0) * h) - qq M ((0 : ℕ) * h) := by
          unfold D
          have := Finset.sum_range_sub (fun j : ℕ => qq M ((j : ℝ≥0) * h)) n
          simpa [Nat.cast_add, Nat.cast_one] using this
        rw [this]
        linarith [q_le_one M hF ((n : ℝ≥0) * h), q_nonneg M hF ((0 : ℕ) * h)]
    _ = R + h := one_mul _

end KBMyersonAux

namespace KBMyersonAux
open MultiItemRev.Decomp

/-- Posted price `p` for one good: `p · P[X ≥ p] ≤ Rev(X)`. -/
lemma price_le_rev1 (ν : Measure ℝ≥0) (t : ℝ≥0) :
    (t : ℝ≥0∞) * ν {x | t ≤ x} ≤ Rev1 ν := by
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
  have hc : Measurable (fun (t : ℝ≥0) (_ : Unit) => t) := by fun_prop
  have hrev : expRevenue (oneGood ν) M = (((t : ℝ≥0∞) * ν {x | t ≤ x} : ℝ≥0∞) : EReal) := by
    unfold expRevenue oneGood
    have hMs : Measurable M.s := hadm.2.2.2
    rw [lintegral_map (f := fun x => ENNReal.ofReal (M.s x))
        (ENNReal.measurable_ofReal.comp hMs) hc,
      lintegral_map (f := fun x => ENNReal.ofReal (-M.s x))
        (ENNReal.measurable_ofReal.comp hMs.neg) hc]
    have h1 : (fun a : ℝ≥0 => ENNReal.ofReal (M.s fun _ => a)) =
        (Set.Ici t).indicator (fun _ => (t : ℝ≥0∞)) := by
      funext a
      simp only [M, Set.indicator, Set.mem_Ici]
      split_ifs <;> simp
    have h2 : (fun a : ℝ≥0 => ENNReal.ofReal (-M.s fun _ => a)) = fun _ => 0 := by
      funext a
      simp only [M]
      split_ifs <;> simp
    rw [h1, h2, lintegral_indicator_const measurableSet_Ici, lintegral_zero,
      EReal.coe_ennreal_zero, sub_zero]
    rfl
  unfold Rev1 Rev
  refine le_trans (le_of_eq ?_) (le_iSup₂ (f := fun (M : Mechanism Unit) (_ : IsAdmissible M) =>
    (expRevenue (oneGood ν) M).toENNReal) M hadm)
  rw [hrev, EReal.toENNReal_coe]

end KBMyersonAux

open KBMyersonAux in
theorem solution (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] :
    MultiItemRev.Decomp.Rev1 ν = ⨆ p : ℝ≥0, (p : ℝ≥0∞) * ν {t | p ≤ t} ∧
    MultiItemRev.Decomp.Rev1 ν = ⨆ p : ℝ≥0, (p : ℝ≥0∞) * ν {t | p < t} ∧
    MultiItemRev.Decomp.Rev1 ν = ⨆ p : ℝ≥0, (p : ℝ≥0∞) * (1 - ν {t | t ≤ p}) := by
  have h1 : MultiItemRev.Decomp.Rev1 ν = ⨆ p : ℝ≥0, (p : ℝ≥0∞) * ν {t | p ≤ t} :=
    le_antisymm (rev1_le_sup ν) (iSup_le fun p => price_le_rev1 ν p)
  have h23 : ∀ p : ℝ≥0, (p : ℝ≥0∞) * ν {t | p < t} = (p : ℝ≥0∞) * (1 - ν {t | t ≤ p}) := by
    intro p
    rw [show {t : ℝ≥0 | t ≤ p} = Set.Iic p from rfl, ← prob_compl_eq_one_sub measurableSet_Iic]
    congr 2
    ext t
    simp
  have h12 : (⨆ p : ℝ≥0, (p : ℝ≥0∞) * ν {t | p ≤ t}) =
      ⨆ p : ℝ≥0, (p : ℝ≥0∞) * ν {t | p < t} := by
    apply le_antisymm
    · refine iSup_le fun p => ?_
      refine ENNReal.le_of_forall_lt_one_mul_le fun c hc => ?_
      have hcne : c ≠ ∞ := (hc.trans ENNReal.one_lt_top).ne
      set p' : ℝ≥0 := c.toNNReal * p
      have hp' : (p' : ℝ≥0∞) = c * p := by
        simp [p', ENNReal.coe_mul, ENNReal.coe_toNNReal hcne]
      calc c * ((p : ℝ≥0∞) * ν {t | p ≤ t}) = (p' : ℝ≥0∞) * ν {t | p ≤ t} := by
            rw [hp', mul_assoc]
        _ ≤ (p' : ℝ≥0∞) * ν {t | p' < t} := by
            rcases eq_or_ne p 0 with hp | hp
            · simp [p', hp]
            · refine mul_le_mul_of_nonneg_left (measure_mono fun t ht => ?_) (by positivity)
              have : p' < p := by
                have hc1 : c.toNNReal < 1 := by
                  rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hcne]; simpa using hc
                calc p' = c.toNNReal * p := rfl
                  _ < 1 * p := mul_lt_mul_of_pos_right hc1 (pos_iff_ne_zero.mpr hp)
                  _ = p := one_mul p
              exact lt_of_lt_of_le this (show p ≤ t from ht)
        _ ≤ _ := le_iSup (fun p : ℝ≥0 => (p : ℝ≥0∞) * ν {t | p < t}) p'
    · exact iSup_mono fun p =>
        mul_le_mul_of_nonneg_left (measure_mono fun t (ht : p < t) => (le_of_lt ht : p ≤ t))
          (by positivity)
  refine ⟨h1, h1.trans h12, ?_⟩
  rw [h1, h12]
  exact iSup_congr h23
