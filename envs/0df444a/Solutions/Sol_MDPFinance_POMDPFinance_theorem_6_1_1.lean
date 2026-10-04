-- Prove2me | solution 1 for MDPFinance.POMDPFinance.theorem_6_1_1
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T20:27:24.524383+00:00
-- url     : https://prove2.me/submissions/88fcc523-c4b7-4741-9968-a36b1db4aba6

import Mathlib
import Definitions.Def_MDPFinance_POMDPFinance_Filter
import Definitions.Def_MDPFinance_POMDPFinance_HistPolicy
import Definitions.Def_MDPFinance_POMDPFinance_TerminalWealth

open MeasureTheory ProbabilityTheory MDPFinance.POMDPFinance
open scoped ENNReal

namespace P611Cex

def pt (r : ℝ) : Fin 1 → ℝ := fun _ => r

/-- Reference measure `δ_{-1/2} + δ_1`. -/
noncomputable def lam : Measure (Fin 1 → ℝ) := Measure.dirac (pt (-1 / 2)) + Measure.dirac (pt 1)

/-- The return law `½ δ_{-1/2} + ½ δ_1`. -/
noncomputable def Qp : Measure (Fin 1 → ℝ) :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac (pt (-1 / 2)) + (1 / 2 : ℝ≥0∞) • Measure.dirac (pt 1)

theorem half_eq : ENNReal.ofReal (1 / 2) = (1 / 2 : ℝ≥0∞) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp

theorem wd : lam.withDensity (fun _ => ENNReal.ofReal (1 / 2)) = Qp := by
  rw [withDensity_const, half_eq, lam, smul_add]; rfl

instance : IsFiniteMeasure lam := by unfold lam; infer_instance

theorem ae_Qp (p : (Fin 1 → ℝ) → Prop) : (∀ᵐ z ∂Qp, p z) ↔ p (pt (-1 / 2)) ∧ p (pt 1) := by
  rw [ae_iff, Qp, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply, Measure.dirac_apply]
  by_cases h1 : p (pt (-1 / 2)) <;> by_cases h2 : p (pt 1) <;> simp [h1, h2]

theorem lint_Qp (f : (Fin 1 → ℝ) → ℝ≥0∞) :
    ∫⁻ z, f z ∂Qp = (1 / 2 : ℝ≥0∞) * f (pt (-1 / 2)) + (1 / 2 : ℝ≥0∞) * f (pt 1) := by
  rw [Qp, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac, lintegral_dirac]
  simp only [smul_eq_mul]

theorem half_ofReal (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (1 / 2 : ENNReal) * ENNReal.ofReal a + (1 / 2 : ENNReal) * ENNReal.ofReal b =
      ENNReal.ofReal ((a + b) / 2) := by
  rw [← half_eq]
  rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; ring

theorem eI_Qp (f : (Fin 1 → ℝ) → ℝ) :
    erealIntegral Qp (fun z => (f z : EReal)) = (((f (pt (-1 / 2)) + f (pt 1)) / 2 : ℝ) : EReal) := by
  unfold erealIntegral
  rw [lint_Qp, lint_Qp]
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
  rw [max_eq_left (by positivity : (0 : ℝ) ≤ (max (f (pt (-1 / 2))) 0 + max (f (pt 1)) 0) / 2),
    max_eq_left (by positivity : (0 : ℝ) ≤ (max (-f (pt (-1 / 2))) 0 + max (-f (pt 1)) 0) / 2)]
  rw [← EReal.coe_neg, ← EReal.coe_add]
  congr 1
  rcases le_total (f (pt (-1 / 2))) 0 with h1 | h1 <;> rcases le_total (f (pt 1)) 0 with h2 | h2 <;>
    simp [max_eq_left, max_eq_right, h1, h2] <;> ring_nf <;>
    first
    | (rw [max_eq_right h1, max_eq_right h2]; ring)
    | skip

noncomputable def FM : FilterMarket Unit 1 where
  lam := lam
  hlam_sigmaFinite := inferInstance
  qR := fun _ _ => 1 / 2
  hqR_meas := measurable_const
  hqR_nonneg := fun _ _ => by norm_num
  hqR_prob := fun _ => by
    rw [lintegral_const, half_eq, lam, Measure.add_apply, measure_univ, measure_univ]
    rw [← two_mul, ← mul_assoc, one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num),
      one_mul]
  hqR_supp := fun _ => by
    rw [wd, ae_Qp]; simp [pt]; norm_num
  QY := Kernel.const Unit (Measure.dirac ())
  isMarkovQY := inferInstance
  Q0 := Measure.dirac ()
  isProbQ0 := inferInstance

theorem law_eq (y : Unit) : FM.law y = Qp := wd

theorem pred_eq : FM.predictive (Measure.dirac ()) = Qp := by
  unfold FilterMarket.predictive
  rw [Measure.dirac_bind (measurable_of_countable _)]
  exact wd

noncomputable def Fd : FilterOp FM where
  Phi := fun _ _ => Measure.dirac ()
  hPhi_prob := fun _ _ _ => inferInstance
  hPhi_meas := measurable_const
  hPhi := by
    intro ρ z h0 htop C _
    show Measure.dirac () C = (∫⁻ y, ENNReal.ofReal (1 / 2) * Measure.dirac () C ∂ρ) /
      (∫⁻ y, ENNReal.ofReal (1 / 2) ∂ρ)
    rw [lintegral_mul_const' _ _ (measure_ne_top _ _)]
    rw [mul_comm, mul_div_assoc,
      ENNReal.div_self (a := ∫⁻ y, ENNReal.ofReal (1 / 2) ∂ρ) h0.ne' htop.ne, mul_one]

theorem logU_mono : StrictMonoOn Real.log (Set.Ioi 0) := Real.strictMonoOn_log

noncomputable def Mk : TerminalWealthMarket FM where
  domU := Set.Ioi 0
  hdomU := Or.inr rfl
  U := Real.log
  hU_mono := Real.strictMonoOn_log
  hU_concave := strictConcaveOn_log_Ioi
  hU_cont := Real.continuousOn_log.mono (fun x hx => ne_of_gt hx)
  i := 0
  hi_pos := by norm_num
  hNA := by
    intro y φ h
    rw [law_eq, ae_Qp] at h ⊢
    simp only [pt, Fin.sum_univ_one] at h ⊢
    exact ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩
  hsupp := fun y y' => by rw [law_eq]
  hmom := ⟨∫⁻ z, ‖z‖ₑ ∂Qp, by
      rw [lint_Qp]
      exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (by norm_num) enorm_lt_top,
        ENNReal.mul_lt_top (by norm_num) enorm_lt_top⟩,
    fun y => by rw [law_eq]⟩

/-- The value, over one period from `x0 = 1`, of the strategy whose time-0 action is `a`. -/
theorem value (fs : ℕ → ℝ × Measure Unit → Fin 1 → ℝ) (a : ℝ) (ha : ∀ p, fs 1 p = fun _ => a) :
    Vpi FM Fd (fun _ => Mk.i) Mk.U (ofMarkov FM Fd (fun _ => Mk.i) 1 fun k xy => fs (1 - k) xy)
      1 0 (fun _ => 0) 1 FM.Q0 =
      (((Real.log (1 + a * (-1 / 2)) + Real.log (1 + a * 1)) / 2 : ℝ) : EReal) := by
  rw [Vpi]
  simp only [Vpi, ofMarkov, Nat.sub_zero, ha]
  show erealIntegral (FM.predictive (Measure.dirac ())) _ = _
  rw [pred_eq]
  have := eI_Qp (fun z => Real.log ((1 + 0) * (1 + a * z 0)))
  simp only [pt] at this ⊢
  convert this using 2
  · funext z; simp [Mk]
  · simp

end P611Cex

open P611Cex in
theorem solution : ¬ (∀ {EY : Type} [MeasurableSpace EY] {d : ℕ} (M : FilterMarket EY d)
    (Fd : FilterOp M) (Mk : TerminalWealthMarket M) (N : ℕ),
    (∀ k ≤ N, ∀ ρ : Measure EY, IsProbabilityMeasure ρ →
        StrictMonoOn (fun x => Jsup M Fd (fun _ => Mk.i) Mk.U Mk.D k x ρ) Mk.domU ∧
          (∀ x ∈ Mk.domU, ∀ y ∈ Mk.domU, x ≠ y → ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 →
            (a : EReal) * Jsup M Fd (fun _ => Mk.i) Mk.U Mk.D k x ρ +
                (b : EReal) * Jsup M Fd (fun _ => Mk.i) Mk.U Mk.D k y ρ <
              Jsup M Fd (fun _ => Mk.i) Mk.U Mk.D k (a * x + b * y) ρ) ∧
          ContinuousOn (fun x => Jsup M Fd (fun _ => Mk.i) Mk.U Mk.D k x ρ) Mk.domU) ∧
      (∀ ρ : Measure EY, ∀ x, Jsup M Fd (fun _ => Mk.i) Mk.U Mk.D 0 x ρ = (Mk.U x : EReal)) ∧
      (∀ k < N, ∀ x ∈ Mk.domU, ∀ ρ : Measure EY, IsProbabilityMeasure ρ →
        Jsup M Fd (fun _ => Mk.i) Mk.U Mk.D (k + 1) x ρ =
        ⨆ a ∈ Mk.D x, erealIntegral (M.predictive ρ) fun z =>
          Jsup M Fd (fun _ => Mk.i) Mk.U Mk.D k ((1 + Mk.i) * (x + ∑ j, a j * z j)) (Fd.Phi ρ z)) ∧
      (∃ fs : ℕ → ℝ × Measure EY → Fin d → ℝ,
        ∀ k < N, Measurable (fs k) ∧ ∀ x ∈ Mk.domU, ∀ ρ : Measure EY, IsProbabilityMeasure ρ →
          fs k (x, ρ) ∈ Mk.D x ∧
          IsMaxOn (fun a => erealIntegral (M.predictive ρ) fun z =>
            Jsup M Fd (fun _ => Mk.i) Mk.U Mk.D k ((1 + Mk.i) * (x + ∑ j, a j * z j)) (Fd.Phi ρ z))
          (Mk.D x) (fs k (x, ρ))) ∧
      (∀ fs : ℕ → ℝ × Measure EY → Fin d → ℝ,
        (∀ k < N, Measurable (fs k) ∧ ∀ x ∈ Mk.domU, ∀ ρ : Measure EY, IsProbabilityMeasure ρ →
          fs k (x, ρ) ∈ Mk.D x ∧
          IsMaxOn (fun a => erealIntegral (M.predictive ρ) fun z =>
            Jsup M Fd (fun _ => Mk.i) Mk.U Mk.D k ((1 + Mk.i) * (x + ∑ j, a j * z j)) (Fd.Phi ρ z))
          (Mk.D x) (fs k (x, ρ))) →
        ∀ x0 ∈ Mk.domU, Vpi M Fd (fun _ => Mk.i) Mk.U
            (ofMarkov M Fd (fun _ => Mk.i) x0 fun k xy => fs (N - k) xy) N 0 (fun _ => 0) x0 M.Q0 =
          Jsup M Fd (fun _ => Mk.i) Mk.U Mk.D N x0 M.Q0)) := by
  intro h
  obtain ⟨-, -, -, ⟨fs, hfs⟩, hopt⟩ := h FM Fd Mk 1
  -- two strategies agreeing with `fs` at index `0` (the only one constrained), differing at `1`
  let fA : ℕ → ℝ × Measure Unit → Fin 1 → ℝ := fun k => if k = 1 then fun _ _ => 0 else fs k
  let fB : ℕ → ℝ × Measure Unit → Fin 1 → ℝ := fun k => if k = 1 then fun _ _ => 2 else fs k
  have hA : ∀ k < 1, _ := fun k hk => by
    have : k = 0 := by omega
    subst this
    exact hfs 0 hk
  have eA := hopt fA (fun k hk => by
    have h0 : k = 0 := by omega
    subst h0; simpa [fA] using hfs 0 hk) 1 (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
  have eB := hopt fB (fun k hk => by
    have h0 : k = 0 := by omega
    subst h0; simpa [fB] using hfs 0 hk) 1 (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
  rw [value fA 0 (fun p => by simp [fA])] at eA
  rw [value fB 2 (fun p => by simp [fB])] at eB
  rw [← eB] at eA
  have := EReal.coe_injective eA
  norm_num at this
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  linarith

#print axioms solution
