-- Prove2me | solution 1 for HighDimProb.Chaining.dudley_integral_inequality
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T21:56:35.606716+00:00
-- url     : https://prove2.me/submissions/6edc9fb3-0e5d-4155-b30a-9fec5ea29574

import Mathlib
import Definitions.Def_HighDimProb_Concentration_SubgaussianNorm
import Definitions.Def_HighDimProb_Chaining_CoveringNumber
import Definitions.Def_HighDimProb_Chaining_ProcessESup

set_option autoImplicit false

open MeasureTheory

namespace Cex32e

/-- The probability space: Lebesgue measure on `(0,1]`. -/
noncomputable def P : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)

instance : IsProbabilityMeasure P := ⟨by simp [P, Real.volume_Ioc]⟩

/-- Mean-zero, integrable, NOT sub-gaussian random variable `ω ↦ ω^(-1/2) - 2`. -/
noncomputable def Y (ω : ℝ) : ℝ := ω ^ (-(1/2 : ℝ)) - 2

theorem rpow_integrableOn : IntegrableOn (fun x : ℝ => x ^ (-(1/2 : ℝ))) (Set.Ioc 0 1) := by
  have h := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := -(1/2 : ℝ))
    (by norm_num)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp h

theorem Y_integrable : Integrable Y P := by
  have h1 : Integrable (fun x : ℝ => x ^ (-(1/2 : ℝ))) P := rpow_integrableOn
  exact h1.sub (integrable_const 2)

theorem Y_mean : ∫ ω, Y ω ∂P = 0 := by
  have h1 : Integrable (fun x : ℝ => x ^ (-(1/2 : ℝ))) P := rpow_integrableOn
  unfold Y
  rw [integral_sub h1 (integrable_const 2)]
  have h2 : ∫ x, x ^ (-(1/2 : ℝ)) ∂P = 2 := by
    unfold P
    rw [← intervalIntegral.integral_of_le zero_le_one, integral_rpow (by norm_num)]
    norm_num
  rw [h2]
  simp

theorem Y_sq (x : ℝ) (hx : 0 < x) :
    Y x ^ 2 = x ^ (-1 : ℝ) - 4 * x ^ (-(1/2 : ℝ)) + 4 := by
  have ha : (x ^ (-(1/2 : ℝ))) ^ 2 = x ^ (-1 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num
  unfold Y
  nlinarith [ha]

theorem not_subG (t : ℝ) (ht : 0 < t)
    (hi : Integrable (fun ω => Real.exp (Y ω ^ 2 / t ^ 2)) P) : False := by
  have hY : Measurable Y := by
    unfold Y; exact (measurable_id.pow_const _).sub measurable_const
  have h2 : Integrable (fun ω => Y ω ^ 2 / t ^ 2) P := by
    refine hi.mono ((hY.pow_const 2).div_const _).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
    linarith [Real.add_one_le_exp (Y ω ^ 2 / t ^ 2)]
  have h3 : Integrable (fun ω => Y ω ^ 2) P := by
    have := h2.mul_const (t ^ 2)
    refine this.congr (Filter.Eventually.of_forall (fun ω => ?_))
    simp only
    field_simp
  have h4 : Integrable (fun ω => Y ω ^ 2 + 4 * ω ^ (-(1/2 : ℝ)) - 4) P :=
    (h3.add ((rpow_integrableOn : Integrable _ P).const_mul 4)).sub (integrable_const 4)
  have h5 : IntegrableOn (fun x : ℝ => x ^ (-1 : ℝ)) (Set.Ioc 0 1) := by
    refine (h4.congr ?_ : Integrable _ P)
    unfold P
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Y_sq x hx.1]; ring
  have h6 := h5.mono_set Set.Ioo_subset_Ioc_self
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff one_pos] at h6
  norm_num at h6

theorem sgn_le (f : ℝ → ℝ) (hf : ∀ ω, f ω ^ 2 = Y ω ^ 2) :
    HighDimProb.Concentration.subgaussianNorm P f ≤ 0 := by
  unfold HighDimProb.Concentration.subgaussianNorm
  have : {t : ℝ | 0 < t ∧ Integrable (fun ω => Real.exp ((f ω) ^ 2 / t ^ 2)) P ∧
      ∫ ω, Real.exp ((f ω) ^ 2 / t ^ 2) ∂P ≤ 2} = ∅ := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro ht hi
    simp only [hf] at hi
    exact (not_subG t ht hi).elim
  rw [this, Real.sInf_empty]

theorem sgn_zero : HighDimProb.Concentration.subgaussianNorm P (fun _ => (0 : ℝ)) ≤ 0 := by
  unfold HighDimProb.Concentration.subgaussianNorm
  apply le_of_forall_pos_le_add
  intro δ hδ
  rw [zero_add]
  apply csInf_le ⟨0, fun t ht => ht.1.le⟩
  refine ⟨hδ, ?_, ?_⟩
  · simp
  · simp

/-- The index space: the two-point metric space `{0, 1} ⊆ ℕ`. -/
abbrev T2 : Type := {n : ℕ // n < 2}

def a : T2 := ⟨0, by norm_num⟩

instance : Nonempty T2 := ⟨⟨0, by norm_num⟩⟩
def b : T2 := ⟨1, by norm_num⟩

theorem cases2 (t : T2) : t = a ∨ t = b := by
  obtain ⟨n, hn⟩ := t
  rcases (show n = 0 ∨ n = 1 by omega) with h | h
  · left; subst h; rfl
  · right; subst h; rfl

theorem dist_self' (t : T2) : dist t t = 0 := dist_self t

theorem dist_ab : dist a b = 1 := by
  rw [Subtype.dist_eq, Nat.dist_eq]; simp [a, b]

theorem dist_ba : dist b a = 1 := by rw [dist_comm]; exact dist_ab

theorem a_ne_b : a ≠ b := by
  intro h; have := congrArg Subtype.val h; simp [a, b] at this

/-- The process: `X a = 0`, `X b = Y`. -/
noncomputable def X (t : T2) (ω : ℝ) : ℝ := if t.1 = 0 then 0 else Y ω

theorem Xa : X a = fun _ => 0 := by funext ω; simp [X, a]
theorem Xb : X b = Y := by funext ω; simp [X, b]

theorem cov_lt (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (HighDimProb.Chaining.coveringNumber T2 ε).toNat = 2 := by
  have hle : HighDimProb.Chaining.coveringNumber T2 ε ≤ 2 := by
    unfold HighDimProb.Chaining.coveringNumber
    refine iInf_le_of_le ⟨{a, b}, fun t => ⟨t, ?_, by rw [dist_self]; exact hε.le⟩⟩ ?_
    · rcases cases2 t with h | h <;> simp [h]
    · rw [Finset.card_pair a_ne_b]; rfl
  have hge : 2 ≤ HighDimProb.Chaining.coveringNumber T2 ε := by
    unfold HighDimProb.Chaining.coveringNumber
    refine le_iInf (fun N => ?_)
    obtain ⟨s, hs⟩ := N
    have hmem : ∀ i : T2, i ∈ s := by
      intro i
      obtain ⟨j, hj, hd⟩ := hs i
      have : i = j := by
        by_contra hne
        rcases cases2 i with hi | hi <;> rcases cases2 j with hj' | hj' <;> subst hi <;> subst hj'
        · exact hne rfl
        · rw [dist_ab] at hd; linarith
        · rw [dist_ba] at hd; linarith
        · exact hne rfl
      rw [this]; exact hj
    have hsub : ({a, b} : Finset T2) ⊆ s := by
      intro i _; exact hmem i
    have := Finset.card_le_card hsub
    rw [Finset.card_pair a_ne_b] at this
    exact_mod_cast this
  rw [le_antisymm hle hge]
  rfl

theorem cov_ge (ε : ℝ) (hε1 : 1 ≤ ε) :
    (HighDimProb.Chaining.coveringNumber T2 ε).toNat = 1 := by
  have hle : HighDimProb.Chaining.coveringNumber T2 ε ≤ 1 := by
    unfold HighDimProb.Chaining.coveringNumber
    refine iInf_le_of_le ⟨{a}, fun t => ⟨a, Finset.mem_singleton_self _, ?_⟩⟩ ?_
    · rcases cases2 t with h | h <;> subst h
      · rw [dist_self]; linarith
      · rw [dist_ba]; exact hε1
    · simp
  have hge : 1 ≤ HighDimProb.Chaining.coveringNumber T2 ε := by
    unfold HighDimProb.Chaining.coveringNumber
    refine le_iInf (fun N => ?_)
    obtain ⟨s, hs⟩ := N
    obtain ⟨j, hj, -⟩ := hs a
    have : s.Nonempty := ⟨j, hj⟩
    have h1 : 1 ≤ s.card := Finset.card_pos.mpr this
    exact_mod_cast h1
  rw [le_antisymm hle hge]
  rfl

theorem cov_fin (ε : ℝ) (hε : 0 < ε) : HighDimProb.Chaining.coveringNumber T2 ε < ⊤ := by
  have net : ∀ t : T2, ∃ t' ∈ ({a, b} : Finset T2), dist t t' ≤ ε := by
    intro t
    refine ⟨t, ?_, by rw [dist_self]; exact hε.le⟩
    rcases cases2 t with h | h <;> subst h <;> simp
  unfold HighDimProb.Chaining.coveringNumber
  exact lt_of_le_of_lt (iInf_le _ ⟨{a, b}, net⟩) (ENat.coe_lt_top _)

theorem integrand_int :
    IntegrableOn (fun ε => Real.sqrt (Real.log ((HighDimProb.Chaining.coveringNumber T2 ε).toNat : ℝ)))
      (Set.Ioi (0 : ℝ)) volume := by
  have hc : IntegrableOn (fun _ : ℝ => Real.sqrt (Real.log 2)) (Set.Ioo (0 : ℝ) 1) volume :=
    integrableOn_const (by simp)
  have hind : IntegrableOn ((Set.Ioo (0 : ℝ) 1).indicator (fun _ => Real.sqrt (Real.log 2)))
      (Set.Ioi (0 : ℝ)) volume :=
    ((integrable_indicator_iff measurableSet_Ioo).mpr hc).integrableOn
  refine hind.congr_fun (fun ε hε => ?_) measurableSet_Ioi
  simp only [Set.mem_Ioi] at hε
  by_cases h1 : ε < 1
  · rw [Set.indicator_of_mem (show ε ∈ Set.Ioo (0:ℝ) 1 from ⟨hε, h1⟩), cov_lt ε hε h1]
    norm_num
  · rw [Set.indicator_of_notMem (fun h => h1 h.2), cov_ge ε (not_lt.mp h1)]
    simp

theorem pair_ne : ({a, b} : Finset T2).Nonempty := ⟨a, by simp⟩

theorem esup_pos : (0 : EReal) < HighDimProb.Chaining.processESup P X := by
  have hle : ((∫ ω, ({a, b} : Finset T2).sup' pair_ne (fun t => X t ω) ∂P : ℝ)
      : EReal) ≤ HighDimProb.Chaining.processESup P X := by
    unfold HighDimProb.Chaining.processESup
    exact le_iSup (fun T0 : {s : Finset T2 // s.Nonempty} =>
      ((∫ ω, T0.1.sup' T0.2 (fun t => X t ω) ∂P : ℝ) : EReal)) ⟨{a, b}, pair_ne⟩
  refine lt_of_lt_of_le ?_ hle
  rw [EReal.coe_pos]
  have hg : (fun ω => ({a, b} : Finset T2).sup' pair_ne (fun t => X t ω))
      = fun ω => max (Y ω) 0 := by
    funext ω
    apply le_antisymm
    · apply Finset.sup'_le
      intro t _
      rcases cases2 t with h | h <;> subst h
      · rw [Xa]; exact le_max_right _ _
      · rw [Xb]; exact le_max_left _ _
    · apply max_le
      · exact Finset.le_sup'_of_le _ (by simp : b ∈ ({a, b} : Finset T2)) (by rw [Xb])
      · exact Finset.le_sup'_of_le _ (by simp : a ∈ ({a, b} : Finset T2)) (by rw [Xa])
  rw [hg]
  have hint : Integrable (fun ω => max (Y ω) 0) P := Y_integrable.pos_part
  rw [integral_pos_iff_support_of_nonneg (f := fun ω => max (Y ω) 0) (fun ω => le_max_right _ _) hint]
  have hsub : Set.Ioo (0 : ℝ) (1/4) ⊆ Function.support (fun ω => max (Y ω) 0) := by
    intro x hx
    simp only [Function.mem_support]
    have hlt : (1/4 : ℝ) ^ (-(1/2 : ℝ)) < x ^ (-(1/2 : ℝ)) :=
      Real.rpow_lt_rpow_of_neg hx.1 hx.2 (by norm_num)
    have h4 : (1/4 : ℝ) ^ (-(1/2 : ℝ)) = 2 := by
      rw [show (1/4 : ℝ) = 2 ^ (-2 : ℝ) by norm_num [Real.rpow_neg]]
      rw [← Real.rpow_mul (by norm_num)]
      norm_num
    have : 0 < Y x := by unfold Y; linarith
    exact (lt_max_of_lt_left this).ne'
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  unfold P
  rw [Measure.restrict_apply measurableSet_Ioo,
    Set.inter_eq_left.mpr (Set.Ioo_subset_Ioc_self.trans (Set.Ioc_subset_Ioc_right (by norm_num))),
    Real.volume_Ioo]
  norm_num

end Cex32e

open MeasureTheory in
theorem solution : ¬ (∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {T : Type} [MetricSpace T] [Nonempty T] (X : T → Ω → ℝ)
        (K : ℝ), 0 ≤ K →
        (∀ t, Integrable (X t) P ∧ ∫ ω, X t ω ∂P = 0) →
        (∀ t s, HighDimProb.Concentration.subgaussianNorm P (fun ω => X t ω - X s ω) ≤
          K * dist t s) →
        (∀ ε : ℝ, 0 < ε → HighDimProb.Chaining.coveringNumber T ε < ⊤) →
        IntegrableOn (fun ε => Real.sqrt (Real.log ((HighDimProb.Chaining.coveringNumber T ε).toNat : ℝ)))
          (Set.Ioi (0 : ℝ)) volume →
        HighDimProb.Chaining.processESup P X ≤
          ((C * K *
              ∫ ε in Set.Ioi (0 : ℝ), Real.sqrt (Real.log ((HighDimProb.Chaining.coveringNumber T ε).toNat : ℝ))) :
            EReal)) := by
  rintro ⟨C, -, h⟩
  have key := h Cex32e.P (T := Cex32e.T2) Cex32e.X 0 le_rfl
    (fun t => by
      rcases Cex32e.cases2 t with ht | ht <;> subst ht
      · rw [Cex32e.Xa]; simp
      · rw [Cex32e.Xb]; exact ⟨Cex32e.Y_integrable, Cex32e.Y_mean⟩)
    (fun t s => by
      rw [zero_mul]
      rcases Cex32e.cases2 t with ht | ht <;> rcases Cex32e.cases2 s with hs | hs <;>
        subst ht <;> subst hs
      · simpa [Cex32e.Xa] using Cex32e.sgn_zero
      · exact Cex32e.sgn_le _ (fun ω => by rw [Cex32e.Xa, Cex32e.Xb]; ring)
      · exact Cex32e.sgn_le _ (fun ω => by rw [Cex32e.Xa, Cex32e.Xb]; ring)
      · simpa [Cex32e.Xb] using Cex32e.sgn_zero)
    Cex32e.cov_fin Cex32e.integrand_int
  simp only [EReal.coe_zero, mul_zero, zero_mul] at key
  exact absurd (lt_of_lt_of_le Cex32e.esup_pos key) (lt_irrefl _)
