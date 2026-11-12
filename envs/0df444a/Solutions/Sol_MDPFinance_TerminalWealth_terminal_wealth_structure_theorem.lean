-- Prove2me | solution 1 for MDPFinance.TerminalWealth.terminal_wealth_structure_theorem
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-12T02:21:07.060247+00:00
-- url     : https://prove2.me/submissions/86df55bc-764f-4a56-b574-58e0c20ae969

import Mathlib
import Definitions.Def_MDPFinance_TerminalWealth_Market

set_option autoImplicit false

open MeasureTheory ProbabilityTheory MDPFinance.TerminalWealth

namespace TwStructureCex

private def pt (r : ℝ) : Fin 1 → ℝ := fun _ => r

private noncomputable def Q2 (r s : ℝ) : Measure (Fin 1 → ℝ) :=
  (1 / 2 : ENNReal) • Measure.dirac (pt r) + (1 / 2 : ENNReal) • Measure.dirac (pt s)

private instance (r s : ℝ) : IsProbabilityMeasure (Q2 r s) := by
  constructor
  simp only [Q2, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.add_halves 1

private theorem int_dirac (f : (Fin 1 → ℝ) → ℝ) (a : Fin 1 → ℝ) :
    Integrable f (Measure.dirac a) :=
  (integrable_const (f a)).congr (ae_eq_dirac f).symm

private theorem int_Q2 (r s : ℝ) (f : (Fin 1 → ℝ) → ℝ) : Integrable f (Q2 r s) :=
  ((int_dirac f _).smul_measure (by simp)).add_measure ((int_dirac f _).smul_measure (by simp))

private theorem ae_Q2_iff (r s : ℝ) (p : (Fin 1 → ℝ) → Prop) :
    (∀ᵐ z ∂(Q2 r s), p z) ↔ p (pt r) ∧ p (pt s) := by
  rw [ae_iff, Q2, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply, Measure.dirac_apply]
  by_cases h1 : p (pt r) <;> by_cases h2 : p (pt s) <;> simp [h1, h2]

private theorem lint_Q2 (r s : ℝ) (f : (Fin 1 → ℝ) → ENNReal) :
    ∫⁻ z, f z ∂(Q2 r s) = (1 / 2 : ENNReal) * f (pt r) + (1 / 2 : ENNReal) * f (pt s) := by
  rw [Q2, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac, lintegral_dirac]
  simp only [smul_eq_mul]

private theorem half_ofReal (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (1 / 2 : ENNReal) * ENNReal.ofReal a + (1 / 2 : ENNReal) * ENNReal.ofReal b =
      ENNReal.ofReal ((a + b) / 2) := by
  rw [show (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2) by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp]
  rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; ring

private theorem eI_Q2 (r s : ℝ) (f : (Fin 1 → ℝ) → ℝ) :
    erealIntegral (Q2 r s) (fun z => (f z : EReal)) =
      (((f (pt r) + f (pt s)) / 2 : ℝ) : EReal) := by
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
  simp only [max_def]
  split_ifs <;> linarith

private theorem NA2 (r s : ℝ) (hr : r < 0) (hs : 0 < s) :
    NoArbitrageOnePeriod (Q2 r s) (fun z : Fin 1 → ℝ => z) := by
  rintro ⟨a, ha, hpos⟩
  rw [ae_Q2_iff] at ha
  simp only [Fin.sum_univ_one, pt] at ha
  have ha0 : a 0 = 0 := by
    rcases lt_trichotomy (a 0) 0 with h | h | h
    · nlinarith [ha.2]
    · exact h
    · nlinarith [ha.1]
  simp [ha0] at hpos

private noncomputable def ratUtil (x : ℝ) : ℝ :=
  x - 1 / (x + 1)

private theorem ratUtil_mono : StrictMonoOn ratUtil (Set.Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := hx
  have hy0 : 0 < y := hy
  have hdiv : 1 / (y + 1) < 1 / (x + 1) :=
    one_div_lt_one_div_of_lt (by linarith) (by linarith)
  dsimp [ratUtil]
  linarith

private theorem ratUtil_concave : StrictConcaveOn ℝ (Set.Ioi (0 : ℝ)) ratUtil := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hx0 : 0 < x := hx
  have hy0 : 0 < y := hy
  simp only [smul_eq_mul, ratUtil]
  have hx1 : 0 < x + 1 := by linarith
  have hy1 : 0 < y + 1 := by linarith
  have hxy1 : 0 < a * x + b * y + 1 := by nlinarith
  have hb_eq : b = 1 - a := by linarith
  have hdiff : (a * x + b * y - 1 / (a * x + b * y + 1)) -
      (a * (x - 1 / (x + 1)) + b * (y - 1 / (y + 1))) =
      a * b * (x - y) ^ 2 / ((x + 1) * (y + 1) * (a * x + b * y + 1)) := by
    subst hb_eq
    field_simp
    ring
  have hpos : 0 < a * b * (x - y) ^ 2 / ((x + 1) * (y + 1) * (a * x + b * y + 1)) :=
    div_pos (mul_pos (mul_pos ha hb) (sq_pos_of_ne_zero (sub_ne_zero.mpr hxy)))
      (mul_pos (mul_pos hx1 hy1) hxy1)
  linarith

private theorem ratUtil_diff (u v : ℝ) (hu : u + 1 ≠ 0) (hv : v + 1 ≠ 0) :
    ratUtil u - ratUtil v = (u - v) * (1 + 1 / ((u + 1) * (v + 1))) := by
  dsimp [ratUtil]
  field_simp
  ring

private theorem ratUtil_cont : ContinuousOn ratUtil (Set.Ioi (0 : ℝ)) :=
  continuousOn_id.sub (continuousOn_const.div (continuousOn_id.add continuousOn_const)
    (fun x hx => by linarith [Set.mem_Ioi.mp hx]))

private noncomputable def Mcex : TerminalWealthMarket (Fin 1 → ℝ) 1 where
  measIP := Q2 (-1) 4
  isProb := inferInstance
  N := 1
  i := fun _ => 0
  hi_pos := fun _ _ _ => by norm_num
  R := fun _ z => z
  hR_meas := fun _ _ _ => measurable_id
  hR_indep := iIndepFun.of_subsingleton
  hNA := fun _ _ _ => NA2 (-1) 4 (by norm_num) (by norm_num)
  domU := Set.Ioi (0 : ℝ)
  U := ratUtil
  hU_mono := ratUtil_mono
  hU_concave := ratUtil_concave
  hU_cont := ratUtil_cont

private theorem Vpi_Mcex_eq (σ : ℕ → ℝ → (Fin 1 → ℝ)) :
    Mcex.Vpi σ 0 1 =
      (((ratUtil (1 - σ 0 1 0) + ratUtil (1 + 4 * σ 0 1 0)) / 2 : ℝ) : EReal) := by
  unfold TerminalWealthMarket.Vpi
  have hEq : (fun z : Fin 1 → ℝ => (Mcex.U (Mcex.terminalWealth σ (Mcex.N - 0) 0 1 z) : EReal)) =
      (fun z : Fin 1 → ℝ => (ratUtil (1 + σ 0 1 0 * z 0) : EReal)) := by
    ext z
    simp [Mcex, TerminalWealthMarket.terminalWealth]
  rw [hEq]
  change erealIntegral (Q2 (-1) 4) (fun z => (ratUtil (1 + σ 0 1 0 * z 0) : EReal)) = _
  rw [eI_Q2]
  congr 2
  simp [pt]
  ring_nf

end TwStructureCex

open TwStructureCex in
theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] {d : ℕ}
    (M : TerminalWealthMarket Ω d),
    (M.domU = Set.Ici (0 : ℝ) ∨ M.domU = Set.Ioi (0 : ℝ)) →
    M.FM2 →
    (∀ n ≤ M.N, StrictMonoOn (M.V n) M.domU ∧ StrictConcaveOnEReal M.domU (M.V n) ∧
        ContinuousOn (M.V n) M.domU) ∧
      (∀ x ∈ M.domU, M.V M.N x = (M.U x : EReal)) ∧
      (∀ n < M.N, ∀ x ∈ M.domU,
        M.V n x = ⨆ a ∈ M.D n x, erealIntegral M.measIP (fun ω => M.V (n + 1)
          ((1 + M.i (n + 1)) * (x + ∑ k, a k * M.R (n + 1) ω k)))) ∧
      (∃ fstar : ℕ → ℝ → (Fin d → ℝ), M.IsAdmissible 0 fstar ∧
        (∀ n < M.N, ∀ x ∈ M.domU,
          erealIntegral M.measIP (fun ω => M.V (n + 1)
            ((1 + M.i (n + 1)) * (x + ∑ k, fstar n x k * M.R (n + 1) ω k))) = M.V n x) ∧
        ∀ x ∈ M.domU, M.Vpi fstar 0 x = M.V 0 x)) := by
  intro hAll
  have hFM2 : Mcex.FM2 := fun _ _ _ => int_Q2 (-1) 4 _
  obtain ⟨_, _, _, fstar, hf_adm, _, hf_opt⟩ := hAll Mcex (Or.inr rfl) hFM2
  have hx1 : (1 : ℝ) ∈ Mcex.domU := by change (0 : ℝ) < 1; exact zero_lt_one
  have hfD : fstar 0 1 ∈ Mcex.D 0 1 :=
    (hf_adm 0 le_rfl (by decide)).1 1 hx1
  change ∀ᵐ z ∂(Q2 (-1) 4), _ ∈ Set.Ioi (0 : ℝ) at hfD
  rw [ae_Q2_iff] at hfD
  simp only [Mcex, Fin.sum_univ_one, pt, Set.mem_Ioi] at hfD
  set a0 : ℝ := fstar 0 1 0
  have ha0_upper : a0 < 1 := by linarith [hfD.1]
  have ha0_lower : -1 / 4 < a0 := by linarith [hfD.2]
  set α : ℝ := (max a0 0 + 1) / 2
  have hα_pos : 0 < α := by
    have : 0 ≤ max a0 0 := le_max_right a0 0
    dsimp [α]; linarith
  have hα_lt1 : α < 1 := by
    have : max a0 0 < 1 := max_lt ha0_upper zero_lt_one
    dsimp [α]; linarith
  have ha0_lt_α : a0 < α := by
    have hle : a0 ≤ max a0 0 := le_max_left a0 0
    have hlt : max a0 0 < 1 := max_lt ha0_upper zero_lt_one
    dsimp [α]; linarith
  let π : ℕ → ℝ → (Fin 1 → ℝ) := fun _ x _ => α * x
  have hπ_adm : Mcex.IsAdmissible 0 π := by
    intro k _ hk
    have hk0 : k = 0 := Nat.lt_one_iff.mp hk
    subst hk0
    refine ⟨?_, measurable_pi_lambda _ (fun _ => measurable_const.mul measurable_id)⟩
    intro x hx
    have hx_pos : 0 < x := by exact hx
    change ∀ᵐ z ∂(Q2 (-1) 4), _ ∈ Set.Ioi (0 : ℝ)
    rw [ae_Q2_iff]
    simp only [Mcex, π, Fin.sum_univ_one, pt, Set.mem_Ioi]
    constructor <;> nlinarith
  have hlt_real :
      (ratUtil (1 - a0) + ratUtil (1 + 4 * a0)) / 2 <
        (ratUtil (1 - α) + ratUtil (1 + 4 * α)) / 2 := by
    have hd1 : 0 < (1 - α) + 1 := by linarith
    have hd2 : 0 < (1 - a0) + 1 := by linarith
    have hd3 : 0 < (1 + 4 * a0) + 1 := by linarith
    have hd4 : 0 < (1 + 4 * α) + 1 := by linarith
    have hprod_gt1 : 1 < ((1 - a0) + 1) * ((1 - α) + 1) := by nlinarith
    have hfrac_lt1 : 1 / (((1 - a0) + 1) * ((1 - α) + 1)) < 1 := by
      rw [div_lt_one (mul_pos hd2 hd1)]
      exact hprod_gt1
    have hfrac_pos : 0 < 1 / (((1 + 4 * α) + 1) * ((1 + 4 * a0) + 1)) := by positivity
    have hgain : 4 * (α - a0) < ratUtil (1 + 4 * α) - ratUtil (1 + 4 * a0) := by
      rw [ratUtil_diff (1 + 4 * α) (1 + 4 * a0) hd4.ne' hd3.ne']
      have : (1 + 4 * α) - (1 + 4 * a0) = 4 * (α - a0) := by ring
      rw [this]
      nlinarith
    have hloss : ratUtil (1 - a0) - ratUtil (1 - α) < 2 * (α - a0) := by
      rw [ratUtil_diff (1 - a0) (1 - α) hd2.ne' hd1.ne']
      have : (1 - a0) - (1 - α) = α - a0 := by ring
      rw [this]
      nlinarith
    linarith
  have hVpi_lt : Mcex.Vpi fstar 0 1 < Mcex.Vpi π 0 1 := by
    rw [Vpi_Mcex_eq fstar, Vpi_Mcex_eq π]
    change (((ratUtil (1 - a0) + ratUtil (1 + 4 * a0)) / 2 : ℝ) : EReal) <
      (((ratUtil (1 - α * 1) + ratUtil (1 + 4 * (α * 1))) / 2 : ℝ) : EReal)
    rw [mul_one, EReal.coe_lt_coe_iff]
    exact hlt_real
  have hVpi_le_V : Mcex.Vpi π 0 1 ≤ Mcex.V 0 1 :=
    le_biSup (fun σ => Mcex.Vpi σ 0 1) hπ_adm
  have hcontra : Mcex.V 0 1 < Mcex.V 0 1 := by
    calc Mcex.V 0 1 = Mcex.Vpi fstar 0 1 := (hf_opt 1 hx1).symm
      _ < Mcex.Vpi π 0 1 := hVpi_lt
      _ ≤ Mcex.V 0 1 := hVpi_le_V
  exact lt_irrefl _ hcontra
