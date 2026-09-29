-- Prove2me | solution 1 for HighDimStat.Minimax.estimation_to_testing
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T03:16:04.26995+00:00
-- url     : https://prove2.me/submissions/8e8f62d2-0ad6-422f-a0ea-a847abe29d15

import Mathlib
import Definitions.Def_HighDimStat_Minimax_MinimaxRisk
import Definitions.Def_HighDimStat_Minimax_IsSeparated
import Definitions.Def_HighDimStat_Minimax_IsJointTestingMeasure

/-! Disproof of 75c4df62 `HighDimStat.Minimax.estimation_to_testing`.

The statement only asks `Φ` to be monotone on `[0, ∞)` (`hΦ`) and puts no sign condition on
`δ`. For `δ < 0` the separation hypothesis `2δ ≤ ρ(θⱼ, θₖ)` is automatic (`ρ ≥ 0`), and `Φ δ` is
unconstrained, while the minimax risk only ever evaluates `Φ` on `ρ`-values in `[0, ∞)`.
Take everything trivial: `𝒳 = Ω = Unit`, `ρ ≡ 0`, `M = 2`, both hypotheses equal to `dirac ()`,
`Q = ½ δ_{(0,())} + ½ δ_{(1,())}`, `δ = -1`, and `Φ x = if x < 0 then 1 else 0`.
Then the minimax risk is `∫⁻ ofReal (Φ 0) = 0`, but every test errs with probability `½`,
so the left side is `ofReal 1 * ½ = ½ > 0`. -/

set_option autoImplicit false

open MeasureTheory

/-- The mixture used as the joint testing law. -/
noncomputable def ett_dp_Q : Measure (Fin 2 × Unit) :=
  (2⁻¹ : ENNReal) • Measure.dirac ((0 : Fin 2), ()) +
    (2⁻¹ : ENNReal) • Measure.dirac ((1 : Fin 2), ())

theorem ett_dp_Q_univ : ett_dp_Q Set.univ = 1 := by
  simp [ett_dp_Q, ENNReal.inv_two_add_inv_two]

instance ett_dp_Q_prob : IsProbabilityMeasure ett_dp_Q := ⟨ett_dp_Q_univ⟩

theorem ett_dp_Q_apply (s : Set (Fin 2 × Unit)) :
    ett_dp_Q s = 2⁻¹ * Measure.dirac ((0 : Fin 2), ()) s +
      2⁻¹ * Measure.dirac ((1 : Fin 2), ()) s := by
  simp [ett_dp_Q]

theorem ett_dp_Q_err (ψ : {f : Unit → Fin 2 // Measurable f}) :
    (2⁻¹ : ENNReal) ≤ ett_dp_Q {p : Fin 2 × Unit | ψ.1 p.2 ≠ p.1} := by
  rw [ett_dp_Q_apply]
  by_cases h : ψ.1 () = 0
  · have hm : ((1 : Fin 2), ()) ∈ {p : Fin 2 × Unit | ψ.1 p.2 ≠ p.1} := by
      simp [h]
    rw [Measure.dirac_apply_of_mem hm, mul_one]
    exact le_add_self
  · have hm : ((0 : Fin 2), ()) ∈ {p : Fin 2 × Unit | ψ.1 p.2 ≠ p.1} := by
      simpa using h
    rw [Measure.dirac_apply_of_mem hm, mul_one]
    exact le_self_add

theorem ett_dp_joint :
    HighDimStat.Minimax.IsJointTestingMeasure (fun _ : Unit => Measure.dirac ())
      (fun _ : Fin 2 => ()) ett_dp_Q := by
  intro j s _
  rw [ett_dp_Q_apply]
  rcases s.eq_empty_or_nonempty with hs | hs
  · subst hs
    simp
  · have hsu : s = Set.univ := Subsingleton.eq_univ_of_nonempty hs
    subst hsu
    fin_cases j <;> simp [Measure.dirac_apply, Set.indicator]

open HighDimStat.Minimax in
theorem solution : ¬ (∀ {𝒳 Ω Idx : Type} [MeasurableSpace 𝒳] [MeasurableSpace Ω]
    (measure : Idx → Measure 𝒳) [∀ p, IsProbabilityMeasure (measure p)]
    (θ : Idx → Ω) (ρ : Ω → Ω → ℝ)
    (hρ_nonneg : ∀ x y, 0 ≤ ρ x y) (hρ_refl : ∀ x, ρ x x = 0)
    (hρ_symm : ∀ x y, ρ x y = ρ y x) (hρ_tri : ∀ x y z, ρ x z ≤ ρ x y + ρ y z)
    (Φ : ℝ → ℝ) (hΦ : ∀ x y, 0 ≤ x → x ≤ y → Φ x ≤ Φ y)
    {M : ℕ} (θs : Fin M → Ω) (δ : ℝ) (hsep : IsSeparated ρ θs δ)
    (Prep : Fin M → Idx) (hPrep : ∀ j, θ (Prep j) = θs j)
    (Q : Measure (Fin M × 𝒳)) [IsProbabilityMeasure Q]
    (hQ : IsJointTestingMeasure measure Prep Q),
    ENNReal.ofReal (Φ δ) *
      (⨅ ψ : {f : 𝒳 → Fin M // Measurable f}, Q {p : Fin M × 𝒳 | ψ.1 p.2 ≠ p.1}) ≤
      minimaxRisk measure θ ρ Φ) := by
  intro H
  have key := H (𝒳 := Unit) (Ω := Unit) (Idx := Unit) (fun _ => Measure.dirac ())
    (fun _ => ()) (fun _ _ => (0 : ℝ))
    (fun _ _ => le_rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => by norm_num)
    (fun x => if x < 0 then 1 else 0)
    (by
      intro x y hx hxy
      have hy : 0 ≤ y := hx.trans hxy
      simp [not_lt.mpr hx, not_lt.mpr hy])
    (M := 2) (fun _ => ()) (-1)
    (by
      intro j k _
      norm_num)
    (fun _ => ()) (fun _ => rfl) ett_dp_Q ett_dp_joint
  have hrisk : minimaxRisk (fun _ : Unit => Measure.dirac ()) (fun _ : Unit => ())
      (fun _ _ : Unit => (0 : ℝ)) (fun x : ℝ => if x < 0 then (1 : ℝ) else 0) = 0 := by
    refine le_antisymm ?_ bot_le
    refine iInf_le_of_le ⟨fun _ => (), measurable_const⟩ ?_
    simp
  have hinf : (2⁻¹ : ENNReal) ≤
      ⨅ ψ : {f : Unit → Fin 2 // Measurable f},
        ett_dp_Q {p : Fin 2 × Unit | ψ.1 p.2 ≠ p.1} :=
    le_iInf ett_dp_Q_err
  rw [hrisk] at key
  have hΦ1 : ENNReal.ofReal (if (-1 : ℝ) < 0 then 1 else 0) = 1 := by norm_num
  rw [hΦ1, one_mul] at key
  have h2 : (2⁻¹ : ENNReal) ≤ 0 := hinf.trans key
  have h3 : (2⁻¹ : ENNReal) ≠ 0 := by simp
  exact h3 (le_antisymm h2 bot_le)
