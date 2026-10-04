-- Prove2me | solution 1 for MDPFinance.ConsumptionInvestment.regime_switching_structure_theorem
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:51:19.390606+00:00
-- url     : https://prove2.me/submissions/eb7c7c6b-c2a2-4b52-875b-726ad14eec65

import Mathlib
import Definitions.Def_MDPFinance_ConsumptionInvestment_RegimeMarket

open MeasureTheory ProbabilityTheory MDPFinance.ConsumptionInvestment

namespace RSSCex

/-- Two regimes, carrying the trivial σ-algebra. -/
def B2 : Type := Bool

instance : Fintype B2 := inferInstanceAs (Fintype Bool)
instance : DecidableEq B2 := inferInstanceAs (DecidableEq Bool)
instance : MeasurableSpace B2 := ⊥

def tt : B2 := (true : Bool)
def ff : B2 := (false : Bool)

theorem ff_ne_tt : ff ≠ tt := by decide
theorem tt_ne_ff : tt ≠ ff := by decide

def pt (r : ℝ) : Fin 1 → ℝ := fun _ => r

/-- The two-point law `½ δ_r + ½ δ_s`. -/
noncomputable def Q2 (r s : ℝ) : Measure (Fin 1 → ℝ) :=
  (1 / 2 : ENNReal) • Measure.dirac (pt r) + (1 / 2 : ENNReal) • Measure.dirac (pt s)

instance (r s : ℝ) : IsProbabilityMeasure (Q2 r s) := by
  constructor
  simp only [Q2, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.add_halves 1

theorem int_dirac (f : (Fin 1 → ℝ) → ℝ) (a : Fin 1 → ℝ) : Integrable f (Measure.dirac a) :=
  (integrable_const (f a)).congr (ae_eq_dirac f).symm

theorem int_Q2 (r s : ℝ) (f : (Fin 1 → ℝ) → ℝ) : Integrable f (Q2 r s) :=
  ((int_dirac f _).smul_measure (by simp)).add_measure ((int_dirac f _).smul_measure (by simp))

theorem ae_Q2_iff (r s : ℝ) (p : (Fin 1 → ℝ) → Prop) :
    (∀ᵐ z ∂(Q2 r s), p z) ↔ p (pt r) ∧ p (pt s) := by
  rw [ae_iff, Q2, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply, Measure.dirac_apply]
  by_cases h1 : p (pt r) <;> by_cases h2 : p (pt s) <;> simp [h1, h2]

theorem lint_Q2 (r s : ℝ) (f : (Fin 1 → ℝ) → ENNReal) :
    ∫⁻ z, f z ∂(Q2 r s) = (1 / 2 : ENNReal) * f (pt r) + (1 / 2 : ENNReal) * f (pt s) := by
  rw [Q2, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac, lintegral_dirac]
  simp only [smul_eq_mul]

theorem half_ofReal (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (1 / 2 : ENNReal) * ENNReal.ofReal a + (1 / 2 : ENNReal) * ENNReal.ofReal b =
      ENNReal.ofReal ((a + b) / 2) := by
  rw [show (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2) by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp]
  rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; ring

/-- `erealIntegral` against `½ δ_r + ½ δ_s` of a real-valued function. -/
theorem eI_Q2 (r s : ℝ) (f : (Fin 1 → ℝ) → ℝ) :
    erealIntegral (Q2 r s) (fun z => (f z : EReal)) = (((f (pt r) + f (pt s)) / 2 : ℝ) : EReal) := by
  unfold erealIntegral
  rw [lint_Q2, lint_Q2]
  have hp : ∀ x : ℝ, (((x : EReal) ⊔ 0).toENNReal) = ENNReal.ofReal (max x 0) := by
    intro x
    rw [show ((x : EReal) ⊔ 0) = ((max x 0 : ℝ) : EReal) by
      rw [Monotone.map_max EReal.coe_strictMono.monotone, EReal.coe_zero],
      EReal.real_coe_toENNReal]
  have hn : ∀ x : ℝ, (((-(x : EReal)) ⊔ 0).toENNReal) = ENNReal.ofReal (max (-x) 0) := by
    intro x
    rw [← EReal.coe_neg, hp]
  simp only [hp, hn]
  rw [half_ofReal _ _ (le_max_right _ _) (le_max_right _ _),
    half_ofReal _ _ (le_max_right _ _) (le_max_right _ _)]
  rw [EReal.coe_ennreal_ofReal, EReal.coe_ennreal_ofReal]
  rw [max_eq_left (by positivity : (0 : ℝ) ≤ (max (f (pt r)) 0 + max (f (pt s)) 0) / 2),
    max_eq_left (by positivity : (0 : ℝ) ≤ (max (-f (pt r)) 0 + max (-f (pt s)) 0) / 2)]
  rw [← EReal.coe_neg, ← EReal.coe_add]
  congr 1
  rcases le_total (f (pt r)) 0 with h1 | h1 <;> rcases le_total (f (pt s)) 0 with h2 | h2 <;>
    simp [max_eq_left, max_eq_right, h1, h2] <;> ring_nf <;>
    first
    | (rw [max_eq_right h1, max_eq_right h2]; ring)
    | skip

theorem eI_Q2_congr (r s : ℝ) (v w : (Fin 1 → ℝ) → EReal) (h1 : v (pt r) = w (pt r))
    (h2 : v (pt s) = w (pt s)) : erealIntegral (Q2 r s) v = erealIntegral (Q2 r s) w := by
  unfold erealIntegral
  rw [lint_Q2, lint_Q2, lint_Q2, lint_Q2, h1, h2]

theorem sum1 (α z : Fin 1 → ℝ) : ∑ k, α k * z k = α 0 * z 0 := by simp

theorem NA2 (r s : ℝ) (hr : r < 0) (hs : 0 < s) :
    ¬ ∃ a : Fin 1 → ℝ, (∀ᵐ z ∂(Q2 r s), 0 ≤ ∑ k, a k * z k) ∧
      Q2 r s {z | 0 < ∑ k, a k * z k} > 0 := by
  rintro ⟨a, ha, hpos⟩
  rw [ae_Q2_iff] at ha
  simp only [sum1, pt] at ha
  have ha0 : a 0 = 0 := by
    rcases lt_trichotomy (a 0) 0 with h | h | h
    · nlinarith [ha.2]
    · exact h
    · nlinarith [ha.1]
  simp only [sum1, ha0, zero_mul, lt_self_iff_false, Set.setOf_false, measure_empty] at hpos

noncomputable def QQ (j : B2) : Measure (Fin 1 → ℝ) := if j = tt then Q2 (-1) 8 else Q2 (-8) 1

theorem QQ_tt : QQ tt = Q2 (-1) 8 := by unfold QQ; rw [if_pos rfl]
theorem QQ_ff : QQ ff = Q2 (-8) 1 := by unfold QQ; rw [if_neg ff_ne_tt]

noncomputable def U (x : ℝ) : ℝ := 2 * Real.sqrt x

theorem U_mono : StrictMonoOn U (Set.Ici 0) := by
  intro a ha b _ hab
  unfold U
  have := Real.sqrt_lt_sqrt ha hab
  linarith

theorem U_conc : StrictConcaveOn ℝ (Set.Ici 0) U := by
  have h := Real.strictConcaveOn_sqrt
  refine ⟨convex_Ici 0, fun x hx y hy hxy a b ha hb hab => ?_⟩
  have := h.2 hx hy hxy ha hb hab
  simp only [smul_eq_mul, U] at *
  nlinarith

theorem U_cont : ContinuousOn U (Set.Ici 0) :=
  (continuous_const.mul Real.continuous_sqrt).continuousOn

noncomputable def M : RegimeSwitchingMarket B2 1 where
  i := 0
  hi_pos := by norm_num
  β := 1
  hβ_pos := by norm_num
  hβ_le_one := le_rfl
  p := fun j k => if j = k then 1 else 0
  hp_nonneg := fun j k => by split_ifs <;> norm_num
  hp_sum := fun j => by simp
  Q := QQ
  hQ_prob := fun j => by unfold QQ; split_ifs <;> infer_instance
  hNA := fun j => by
    unfold QQ; split_ifs
    · exact NA2 _ _ (by norm_num) (by norm_num)
    · exact NA2 _ _ (by norm_num) (by norm_num)
  hFM2 := fun j => by
    unfold QQ; split_ifs <;> exact int_Q2 _ _ _
  domU := Set.Ici 0
  hdomU := rfl
  Uc := U
  Up := U
  hUc_mono := U_mono
  hUc_concave := U_conc
  hUc_cont := U_cont
  hUp_mono := U_mono
  hUp_concave := U_conc
  hUp_cont := U_cont

theorem MQ (j : B2) : M.Q j = QQ j := rfl

/-- Measurable maps out of `ℝ × B2` (with `⊥` on `B2`) do not see the regime. -/
theorem meas_indep {β : Type*} [MeasurableSpace β] [MeasurableSingletonClass β]
    (f : ℝ × B2 → β) (hf : Measurable f) (x : ℝ) (j k : B2) : f (x, j) = f (x, k) := by
  have hS : MeasurableSet (f ⁻¹' {f (x, j)}) := hf (measurableSet_singleton _)
  have hprod : (Prod.instMeasurableSpace : MeasurableSpace (ℝ × B2)) =
      MeasurableSpace.comap Prod.fst inferInstance := by
    show MeasurableSpace.comap Prod.fst _ ⊔ MeasurableSpace.comap Prod.snd (⊥ : MeasurableSpace B2) = _
    rw [MeasurableSpace.comap_bot, sup_bot_eq]
  rw [hprod] at hS
  obtain ⟨t, -, ht⟩ := hS
  have hj : (x, j) ∈ f ⁻¹' {f (x, j)} := rfl
  rw [← ht] at hj
  have hk : (x, k) ∈ Prod.fst ⁻¹' t := hj
  rw [ht] at hk
  exact hk.symm

theorem psum (j : B2) (v : B2 → EReal) : ∑ k, ((M.p j k : ℝ) : EReal) * v k = v j := by
  rw [Fintype.sum_eq_single j]
  · show (((if j = j then (1 : ℝ) else 0) : ℝ) : EReal) * v j = v j
    simp
  · intro k hk
    show (((if j = k then (1 : ℝ) else 0) : ℝ) : EReal) * v k = 0
    rw [if_neg (Ne.symm hk)]; simp

theorem memD (x : ℝ) (j : B2) (ca : ℝ × (Fin 1 → ℝ)) :
    ca ∈ M.D x j ↔ 0 ≤ ca.1 ∧ ca.1 ≤ x ∧ ca.1 ∈ Set.Ici (0 : ℝ) ∧
      ∀ᵐ z ∂(QQ j), (1 + 0) * (x - ca.1 + ∑ k, ca.2 k * z k) ∈ Set.Ici (0 : ℝ) := Iff.rfl

/-- Upper bound for the value of any admissible (hence regime-blind) policy. -/
theorem J1_le : M.J 1 1 tt ≤ ((321 / 100 : ℝ) : EReal) := by
  refine iSup₂_le fun π hπ => ?_
  obtain ⟨hD, hm⟩ := hπ 0 (by norm_num)
  have hind := meas_indep (π 0) hm 1 tt ff
  have hDt := hD 1 (by norm_num : (1 : ℝ) ∈ Set.Ici 0) tt
  have hDf := hD 1 (by norm_num : (1 : ℝ) ∈ Set.Ici 0) ff
  rw [← hind] at hDf
  set c := (π 0 (1, tt)).1 with hc
  set a := (π 0 (1, tt)).2 0 with ha
  rw [memD, QQ_tt, ae_Q2_iff] at hDt
  rw [memD, QQ_ff, ae_Q2_iff] at hDf
  simp only [Set.mem_Ici, sum1, pt, add_zero, one_mul] at hDt hDf
  rw [← hc, ← ha] at hDt hDf
  obtain ⟨hc0, hc1, -, h1, h2⟩ := hDt
  obtain ⟨-, -, -, h3, h4⟩ := hDf
  -- evaluate the policy value
  show M.EFromToAcc π 1 1 tt 0 1 ≤ _
  simp only [RegimeSwitchingMarket.EFromToAcc]
  rw [psum, MQ, QQ_tt]
  rw [show (fun z : Fin 1 → ℝ => ((0 + 1 * M.Uc (π 0 (1, tt)).1 + 1 * M.β *
      M.Up ((1 + M.i) * (1 - (π 0 (1, tt)).1 + ∑ m, (π 0 (1, tt)).2 m * z m)) : ℝ) : EReal)) =
      fun z => ((U c + U (1 - c + a * z 0) : ℝ) : EReal) by
    funext z
    show ((0 + 1 * U (π 0 (1, tt)).1 + 1 * 1 *
      U ((1 + 0) * (1 - (π 0 (1, tt)).1 + ∑ m, (π 0 (1, tt)).2 m * z m)) : ℝ) : EReal) = _
    rw [sum1]; simp [hc, ha]]
  rw [eI_Q2]
  apply EReal.coe_le_coe_iff.mpr
  simp only [pt, U]
  set w := 1 - c
  have hw : 0 ≤ w := by linarith
  set s := Real.sqrt c
  set t := Real.sqrt w
  have hs2 : s ^ 2 = c := Real.sq_sqrt hc0
  have ht2 : t ^ 2 = w := Real.sq_sqrt hw
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  set u := Real.sqrt (1 - c + a * -1)
  set v := Real.sqrt (1 - c + a * 8)
  have hu2 : u ^ 2 = 1 - c + a * -1 := Real.sq_sqrt (by linarith)
  have hv2 : v ^ 2 = 1 - c + a * 8 := Real.sq_sqrt (by linarith)
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hau : u ≤ 107 / 100 * t := by nlinarith
  have hav : v ≤ 143 / 100 * t := by nlinarith
  have hst : s ^ 2 + t ^ 2 = 1 := by rw [hs2, ht2]; ring
  have key : 2 * s + 25 / 10 * t ≤ 321 / 100 := by
    nlinarith [sq_nonneg (25 / 10 * s - 2 * t)]
  linarith

end RSSCex

open RSSCex in
theorem solution : ¬ (∀ {EY : Type} [Fintype EY] [MeasurableSpace EY]
    {d : ℕ} (M : RegimeSwitchingMarket EY d) (N : ℕ),
    (∀ n ≤ N, ∀ j : EY, StrictMonoOn (fun x => M.J n x j) M.domU ∧
        StrictConcaveOnEReal M.domU (fun x => M.J n x j) ∧
        ContinuousOn (fun x => M.J n x j) M.domU) ∧
      (∀ x ∈ M.domU, ∀ j, M.J 0 x j = (M.Up x : EReal)) ∧
      (∀ n, ∀ x ∈ M.domU, ∀ j : EY,
        M.J (n + 1) x j = ⨆ ca ∈ M.D x j,
          (M.Uc ca.1 : EReal) + (M.β : EReal) * ∑ k, (M.p j k : EReal) *
            erealIntegral (M.Q j) (fun z => M.J n ((1 + M.i) * (x - ca.1 + ∑ m, ca.2 m * z m)) k)) ∧
      (∃ fstar : ℕ → ℝ × EY → ℝ × (Fin d → ℝ),
        (∀ n, 1 ≤ n → n ≤ N → (∀ x ∈ M.domU, ∀ j, fstar n (x, j) ∈ M.D x j) ∧
          Measurable (fstar n) ∧
          ∀ x ∈ M.domU, ∀ j : EY,
            (M.Uc (fstar n (x, j)).1 : EReal) + (M.β : EReal) * ∑ k, (M.p j k : EReal) *
              erealIntegral (M.Q j) (fun z => M.J (n - 1) ((1 + M.i) * (x - (fstar n (x, j)).1 +
                ∑ m, (fstar n (x, j)).2 m * z m)) k) = M.J n x j) ∧
        M.IsAdmissible N (fun l => fstar (N - l)) ∧
        ∀ x ∈ M.domU, ∀ j : EY, M.Jpi (fun l => fstar (N - l)) N x j = M.J N x j)) := by
  intro h
  obtain ⟨-, hJ0, hBell, -⟩ := h RSSCex.M 0
  have hB := hBell 0 1 (by norm_num : (1 : ℝ) ∈ Set.Ici 0) tt
  -- the action `c = 9/25`, `a = 16/25` is admissible in regime `tt`
  set ca0 : ℝ × (Fin 1 → ℝ) := (9 / 25, fun _ => 16 / 25) with hca0
  have hmem : ca0 ∈ RSSCex.M.D 1 tt := by
    rw [memD, QQ_tt, ae_Q2_iff]
    simp only [Set.mem_Ici, sum1, pt, hca0]
    norm_num
  have hval : (RSSCex.M.Uc ca0.1 : EReal) + (RSSCex.M.β : EReal) * ∑ k, (RSSCex.M.p tt k : EReal) *
      erealIntegral (RSSCex.M.Q tt) (fun z => RSSCex.M.J 0 ((1 + RSSCex.M.i) *
        (1 - ca0.1 + ∑ m, ca0.2 m * z m)) k) = ((18 / 5 : ℝ) : EReal) := by
    rw [psum, MQ, QQ_tt]
    rw [eI_Q2_congr (-1) 8 _ (fun z => ((U ((1 - 9 / 25) + 16 / 25 * z 0) : ℝ) : EReal))]
    · rw [eI_Q2]
      have e1 : U (9 / 25) = 6 / 5 := by
        unfold U; rw [show (9 / 25 : ℝ) = (3 / 5) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]; norm_num
      have e2 : U ((1 - 9 / 25) + 16 / 25 * pt (-1) 0) = 0 := by
        unfold U pt; norm_num
      have e3 : U ((1 - 9 / 25) + 16 / 25 * pt 8 0) = 24 / 5 := by
        unfold U pt
        rw [show (1 - 9 / 25 : ℝ) + 16 / 25 * 8 = (12 / 5) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        norm_num
      rw [e2, e3]
      show ((U (9 / 25) : ℝ) : EReal) + ((1 : ℝ) : EReal) * _ = _
      rw [e1, EReal.coe_one, one_mul, ← EReal.coe_add]
      norm_num
    · show RSSCex.M.J 0 ((1 + 0) * (1 - 9 / 25 + ∑ m, (fun _ => (16 / 25 : ℝ)) m * pt (-1) m)) tt = _
      rw [hJ0 _ (by show _ ∈ Set.Ici (0 : ℝ); simp only [sum1, pt, Set.mem_Ici]; norm_num) tt, sum1]
      simp [pt]; rfl
    · show RSSCex.M.J 0 ((1 + 0) * (1 - 9 / 25 + ∑ m, (fun _ => (16 / 25 : ℝ)) m * pt 8 m)) tt = _
      rw [hJ0 _ (by show _ ∈ Set.Ici (0 : ℝ); simp only [sum1, pt, Set.mem_Ici]; norm_num) tt, sum1]
      simp [pt]; rfl
  have hge : ((18 / 5 : ℝ) : EReal) ≤ RSSCex.M.J 1 1 tt := by
    rw [hB, ← hval]
    exact le_iSup₂_of_le ca0 hmem le_rfl
  have := hge.trans J1_le
  have := EReal.coe_le_coe_iff.mp this
  norm_num at this

#print axioms solution
