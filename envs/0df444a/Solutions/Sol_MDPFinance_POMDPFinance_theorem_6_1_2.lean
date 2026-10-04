-- Prove2me | solution 1 for MDPFinance.POMDPFinance.theorem_6_1_2
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T20:29:24.046311+00:00
-- url     : https://prove2.me/submissions/ff8d9cfe-6aeb-40d3-9cc0-1772b1e953d6

import Mathlib
import Definitions.Def_MDPFinance_POMDPFinance_Filter
import Definitions.Def_MDPFinance_POMDPFinance_HistPolicy
import Definitions.Def_MDPFinance_POMDPFinance_TerminalWealth
import Definitions.Def_MDPFinance_POMDPFinance_PowerLogValue

open MeasureTheory ProbabilityTheory MDPFinance.POMDPFinance
open scoped ENNReal

namespace P612Cex

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


noncomputable def U (x : ℝ) : ℝ := x ^ (1 / 2 : ℝ) / (1 / 2)

theorem U_mono : StrictMonoOn U (Set.Ici 0) := by
  intro a ha b hb hab
  exact div_lt_div_of_pos_right (Real.strictMonoOn_rpow_Ici_of_exponent_pos (by norm_num)
    ha hb hab) (by norm_num)

theorem U_conc : StrictConcaveOn ℝ (Set.Ici 0) U := by
  have h := Real.strictConcaveOn_rpow (p := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  refine ⟨convex_Ici 0, fun x hx y hy hxy a b ha hb hab => ?_⟩
  have := h.2 hx hy hxy ha hb hab
  simp only [smul_eq_mul, U] at *
  rw [show a * (x ^ (1 / 2 : ℝ) / (1 / 2)) + b * (y ^ (1 / 2 : ℝ) / (1 / 2)) =
    (a * x ^ (1 / 2 : ℝ) + b * y ^ (1 / 2 : ℝ)) / (1 / 2) by ring]
  exact div_lt_div_of_pos_right this (by norm_num)

theorem U_cont : ContinuousOn U (Set.Ici 0) :=
  ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).div_const _).continuousOn

noncomputable def Mk : TerminalWealthMarket FM where
  domU := Set.Ici 0
  hdomU := Or.inl rfl
  U := U
  hU_mono := U_mono
  hU_concave := U_conc
  hU_cont := U_cont
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

theorem int_dirac (f : (Fin 1 → ℝ) → ℝ) (a : Fin 1 → ℝ) : Integrable f (Measure.dirac a) :=
  (integrable_const (f a)).congr (ae_eq_dirac f).symm

theorem integral_Qp (f : (Fin 1 → ℝ) → ℝ) : ∫ z, f z ∂Qp = (f (pt (-1 / 2)) + f (pt 1)) / 2 := by
  have h1 := (int_dirac f (pt (-1 / 2))).smul_measure (c := (1 / 2 : ℝ≥0∞)) (by simp)
  have h2 := (int_dirac f (pt 1)).smul_measure (c := (1 / 2 : ℝ≥0∞)) (by simp)
  rw [Qp, integral_add_measure h1 h2, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac]
  simp only [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

theorem memA (a : Fin 1 → ℝ) : a ∈ AtildePow FM ↔ 0 ≤ 1 + a 0 * (-1 / 2) ∧ 0 ≤ 1 + a 0 * 1 := by
  show (∀ y : Unit, ∀ᵐ z ∂(lam.withDensity fun z => ENNReal.ofReal (1 / 2)), _) ↔ _
  rw [wd]
  constructor
  · intro h; have := (ae_Qp _).mp (h ()); simpa [pt] using this
  · intro h y; rw [ae_Qp]; simpa [pt] using h

theorem sq_half (x : ℝ) : x ^ (1 / 2 : ℝ) = Real.sqrt x := (Real.sqrt_eq_rpow x).symm

/-- `α ≡ 1` maximises the one-period objective with `d_0 = 1/γ = 2`. -/
theorem maxOn : IsMaxOn (fun a => ∫ z, dPow FM Fd (1 / 2) 0 (Fd.Phi (Measure.dirac ()) z) *
    (1 + ∑ j, a j * z j) ^ (1 / 2 : ℝ) ∂(FM.predictive (Measure.dirac ()))) (AtildePow FM)
    (fun _ => 1) := by
  intro a ha
  rw [memA] at ha
  simp only [Set.mem_setOf_eq]
  simp only [dPow, pred_eq, integral_Qp, pt, Fin.sum_univ_one, sq_half]
  set s := Real.sqrt (1 + a 0 * (-1 / 2))
  set t := Real.sqrt (1 + a 0 * 1)
  have hs : s ^ 2 = 1 + a 0 * (-1 / 2) := Real.sq_sqrt ha.1
  have ht : t ^ 2 = 1 + a 0 * 1 := Real.sq_sqrt ha.2
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  set r := Real.sqrt 2 with hr
  have hr2 : r ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg 2
  have e1 : Real.sqrt (1 + 1 * (-1 / 2)) = r / 2 := by
    rw [show (1 + 1 * (-1 / 2) : ℝ) = (r / 2) ^ 2 by rw [div_pow, hr2]; norm_num,
      Real.sqrt_sq (by positivity)]
  have e2 : Real.sqrt (1 + 1 * 1) = r := by norm_num [hr]
  rw [e1, e2]
  -- Cauchy–Schwarz: `(s + t)² ≤ (1/2 + 1)(2 s² + t²) = 9/2`
  have hst : (s + t) ^ 2 ≤ 9 / 2 := by nlinarith [sq_nonneg (2 * s - t)]
  have : s + t ≤ 3 / 2 * r := by
    have h92 : (3 / 2 * r) ^ 2 = 9 / 2 := by rw [mul_pow, hr2]; norm_num
    nlinarith [sq_nonneg (s + t - 3 / 2 * r)]
  nlinarith

theorem value (αs : ℕ → Measure Unit → Fin 1 → ℝ) (c : ℝ) (hc : ∀ ρ, αs 1 ρ = fun _ => c) :
    Vpi FM Fd (fun _ => Mk.i) Mk.U
      (ofMarkov FM Fd (fun _ => Mk.i) 1 fun k p => fun j => p.1 * αs (1 - k) p.2 j)
      1 0 (fun _ => 0) 1 FM.Q0 =
      (((U (1 + c * (-1 / 2)) + U (1 + c * 1)) / 2 : ℝ) : EReal) := by
  rw [Vpi]
  simp only [Vpi, ofMarkov, Nat.sub_zero, hc]
  show erealIntegral (FM.predictive (Measure.dirac ())) _ = _
  rw [pred_eq]
  have := eI_Qp (fun z => U ((1 + 0) * (1 + c * z 0)))
  simp only [pt] at this ⊢
  convert this using 2
  · funext z; simp [Mk, xOfMarkov]
  · simp

end P612Cex

open P612Cex in
theorem solution : ¬ (∀ {EY : Type} [MeasurableSpace EY] {d : ℕ} (M : FilterMarket EY d)
    (Fd : FilterOp M) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (Mk : TerminalWealthMarket M)
    (hU : Mk.U = fun x => x ^ γ / γ) (hdomU : Mk.domU = Set.Ici 0) (N : ℕ),
    (∀ k ≤ N, ∀ x ≥ (0 : ℝ), ∀ ρ : Measure EY, IsProbabilityMeasure ρ →
        Jsup M Fd (fun _ => Mk.i) Mk.U Mk.D k x ρ =
          (((x * (1 + Mk.i) ^ k) ^ γ * dPow M Fd γ k ρ : ℝ) : EReal)) ∧
      (∀ k < N, ∀ ρ : Measure EY, IsProbabilityMeasure ρ → ∀ α ∈ AtildePow M,
        IsMaxOn (fun a => ∫ z, dPow M Fd γ k (Fd.Phi ρ z) * (1 + ∑ j, a j * z j) ^ γ
            ∂(M.predictive ρ)) (AtildePow M) α →
        ∀ x ≥ (0 : ℝ), IsMaxOn
          (fun a => erealIntegral (M.predictive ρ) fun z =>
            Jsup M Fd (fun _ => Mk.i) Mk.U Mk.D k ((1 + Mk.i) * (x + ∑ j, a j * z j)) (Fd.Phi ρ z))
          (Mk.D x) (fun j => x * α j)) ∧
      (∀ αs : ℕ → Measure EY → Fin d → ℝ,
        (∀ k < N, Measurable (fun p : ℝ × Measure EY => fun j => p.1 * αs k p.2 j) ∧
          ∀ ρ : Measure EY, IsProbabilityMeasure ρ → αs k ρ ∈ AtildePow M ∧
            IsMaxOn (fun a => ∫ z, dPow M Fd γ k (Fd.Phi ρ z) * (1 + ∑ j, a j * z j) ^ γ
              ∂(M.predictive ρ)) (AtildePow M) (αs k ρ)) →
        ∀ x0 ≥ (0 : ℝ), Vpi M Fd (fun _ => Mk.i) Mk.U
            (ofMarkov M Fd (fun _ => Mk.i) x0 fun k p => fun j => p.1 * αs (N - k) p.2 j)
            N 0 (fun _ => 0) x0 M.Q0 =
          Jsup M Fd (fun _ => Mk.i) Mk.U Mk.D N x0 M.Q0)) := by
  intro h
  have hopt := (h FM Fd (1 / 2) (by norm_num) (by norm_num) Mk rfl rfl 1).2.2
  let αA : ℕ → Measure Unit → Fin 1 → ℝ := fun k => if k = 1 then fun _ _ => 0 else fun _ _ => 1
  let αB : ℕ → Measure Unit → Fin 1 → ℝ := fun k => if k = 1 then fun _ _ => 1 else fun _ _ => 1
  have hyp : ∀ α : ℕ → Measure Unit → Fin 1 → ℝ, (∀ ρ, α 0 ρ = fun _ => 1) → ∀ k < 1,
      Measurable (fun p : ℝ × Measure Unit => fun j => p.1 * α k p.2 j) ∧
        ∀ ρ : Measure Unit, IsProbabilityMeasure ρ → α k ρ ∈ AtildePow FM ∧
          IsMaxOn (fun a => ∫ z, dPow FM Fd (1 / 2) k (Fd.Phi ρ z) * (1 + ∑ j, a j * z j) ^ (1 / 2 : ℝ)
            ∂(FM.predictive ρ)) (AtildePow FM) (α k ρ) := by
    intro α hα k hk
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [hα]
    refine ⟨measurable_pi_lambda _ fun j => measurable_fst.mul_const _, fun ρ hρ => ?_⟩
    have hρ' : ρ = Measure.dirac () := by
      ext C hC
      rcases (Set.subsingleton_of_subsingleton (s := C)).eq_empty_or_singleton with h | h
      · simp [h]
      · obtain ⟨u, rfl⟩ := h
        rw [show ({u} : Set Unit) = Set.univ by ext; simp, measure_univ, measure_univ]
    subst hρ'
    exact ⟨by rw [memA]; norm_num, maxOn⟩
  have eA := hopt αA (hyp αA (fun ρ => by simp [αA])) 1 (by norm_num)
  have eB := hopt αB (hyp αB (fun ρ => by simp [αB])) 1 (by norm_num)
  rw [value αA 0 (fun ρ => by simp [αA])] at eA
  rw [value αB 1 (fun ρ => by simp [αB])] at eB
  rw [← eB] at eA
  have := EReal.coe_injective eA
  simp only [U, sq_half] at this
  have hr2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have e1 : Real.sqrt (1 + 1 * (-1 / 2)) = Real.sqrt 2 / 2 := by
    rw [show (1 + 1 * (-1 / 2) : ℝ) = (Real.sqrt 2 / 2) ^ 2 by rw [div_pow, hr2]; norm_num,
      Real.sqrt_sq (by positivity)]
  rw [e1] at this
  norm_num at this
  nlinarith

#print axioms solution
