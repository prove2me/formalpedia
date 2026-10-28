-- Prove2me | solution 1 for OAI.PiExponent.denominator_clearing_determinant_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T03:58:23.841325+00:00
-- url     : https://prove2.me/submissions/b79b09ae-8c62-4a6d-a264-e37d81815dd0

import Definitions.Def_PiExponent_DeterminantSetup
import Definitions.Def_PiExponent_FiniteMinorComparison
import Theorems.Thm_OAI_PiExponent_eventual_log_jets_give_cofinal_truncated_minors
import Theorems.Thm_OAI_PiExponent_finite_log_minor_arithmetic_controls
import Theorems.Thm_OAI_PiExponent_finite_approximation_minor_analytic_aggregate
import Theorems.Thm_OAI_PiExponent_finite_collision_rate_tendsto
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open OAI.PiExponent
open Filter Topology
open scoped BigOperators

/-- The strict error margin rules out the first conclusion branch. -/
lemma OAI.PiExponent.error_branch_impossible
    (nu : ℝ) (B : OAI.PiExponent.DeterminantBudget nu) :
    ¬ (nu * (B.A * (1 - B.eta) - (B.theta : ℝ)) -
        (1 - (B.theta : ℝ)) ≤ B.E) := by
  exact not_le_of_gt B.error_gap

/-- The strict collision margin rules out the second conclusion branch. -/
lemma OAI.PiExponent.collision_branch_impossible
    (nu : ℝ) (B : OAI.PiExponent.DeterminantBudget nu) :
    ¬ ((Real.log 2 / 4) *
        (B.eta ^ 2 * (B.K : ℝ) * (B.theta : ℝ) ^ B.m /
          (((B.m : ℝ) + 1) * (B.v0 : ℝ) * B.A ^ B.m)) ≤ 1 + B.E) := by
  exact not_le_of_gt B.collision_gap

/-- A purely numerical comparison, independent of interpolation and pi. -/
lemma OAI.PiExponent.finite_minor_bounds_inconsistent
    (nu theta C b Ea En eps c a : ℝ)
    (hnu : 1 ≤ nu) (hb0 : 0 ≤ b) (hbtheta : b ≤ theta)
    (hsmall : Ea + En + eps < nu * (C - theta) - (1 - theta))
    (hlarge : 1 + Ea + En + eps < c)
    (hlower : -(1 - b) - Ea ≤ a)
    (hupper : a ≤ En + eps + max (-c) (-nu * (C - b))) : False := by
  have hcombined :
      -(1 - b) - Ea - En - eps ≤ max (-c) (-nu * (C - b)) := by
    linarith only [hlower, hupper]
  rcases le_max_iff.mp hcombined with hcollision | herror
  · linarith only [hcollision, hlarge, hb0]
  · have hmonotone : 0 ≤ (nu - 1) * (theta - b) :=
      mul_nonneg (sub_nonneg.mpr hnu) (sub_nonneg.mpr hbtheta)
    nlinarith only [herror, hsmall, hmonotone]

theorem solution
    (nu : ℝ) (hnu : 2 < nu) (B : OAI.PiExponent.DeterminantBudget nu)
    (p : Fin B.m → ℤ) (q w : Fin B.m → ℕ)
    (hq : ∀ i, 2 ≤ q i) (hp : ∀ i, p i ≠ 0)
    (hw : ∀ i, w i = Nat.ceil (Real.log (q i : ℝ)))
    (hmin : ∀ i, B.wmin ≤ w i)
    (happrox : ∀ i,
      |Real.pi - (p i : ℝ) / (q i : ℝ)| ≤ (q i : ℝ) ^ (-nu))
    (hrank : ∀ c : Fin B.K → Fin B.m → ℂ,
      (∀ i : Fin B.m, Function.Injective (fun j : Fin B.K => c j i)) →
      OAI.PiExponent.eventualLogJetSurjective
        B.m B.K B.w0 B.v0 B.theta w c) :
    nu * (B.A * (1 - B.eta) - (B.theta : ℝ)) -
        (1 - (B.theta : ℝ)) ≤ B.E ∨
      (Real.log 2 / 4) *
        (B.eta ^ 2 * (B.K : ℝ) * (B.theta : ℝ) ^ B.m /
          (((B.m : ℝ) + 1) * (B.v0 : ℝ) * B.A ^ B.m)) ≤ 1 + B.E := by
  classical
  exfalso
  have hw0R : (0 : ℝ) < B.w0 := by exact_mod_cast B.w0_pos
  have hv0R : (0 : ℝ) < B.v0 := by exact_mod_cast B.v0_pos
  have hthetaR : (0 : ℝ) < B.theta := by exact_mod_cast B.theta_pos
  have hwminR : (0 : ℝ) < B.wmin := by exact_mod_cast B.wmin_pos
  have hwmin : ∀ i, (B.wmin : ℝ) ≤ MatrixArithmetic.logWeights q i := by
    intro i
    change (B.wmin : ℝ) ≤ (Nat.ceil (Real.log (q i : ℝ)) : ℝ)
    rw [← hw i]
    exact_mod_cast hmin i

  -- Nonzero numerators ensure that these actual rational centers are distinct.
  have hcenters : ∀ i : Fin B.m, Function.Injective
      (fun j : Fin B.K =>
        (j.val : ℂ) * MatrixArithmetic.rationalCenters p q i) := by
    intro i j k hjk
    have hpC : (p i : ℂ) ≠ 0 := by exact_mod_cast hp i
    have hqN : 0 < q i := lt_of_lt_of_le (by decide : 0 < 2) (hq i)
    have hqC : (q i : ℂ) ≠ 0 := by exact_mod_cast hqN.ne'
    have hr : MatrixArithmetic.rationalCenters p q i ≠ 0 := by
      dsimp [MatrixArithmetic.rationalCenters]
      exact div_ne_zero
        (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hpC) hqC
    have he : (j.val : ℂ) = (k.val : ℂ) := mul_right_cancel₀ hr hjk
    apply Fin.ext
    exact_mod_cast he
  have hjet := hrank
    (fun j i => (j.val : ℂ) * MatrixArithmetic.rationalCenters p q i) hcenters
  have hcofinal := OAI.PiExponent.eventual_log_jets_give_cofinal_truncated_minors
    B.m B.K B.w0 B.v0 B.theta B.F0 p q w
    B.K_pos B.w0_pos B.v0_pos B.theta_pos B.F0_pos B.F0_large hq hw hjet

  obtain ⟨error, herror, hupper⟩ :=
    OAI.PiExponent.finite_approximation_minor_analytic_aggregate
      B.m B.K B.w0 B.v0 B.theta nu B.A B.eta B.F0 (B.wmin : ℝ) p q
      B.m_pos B.K_pos B.w0_pos B.v0_pos B.theta_pos B.theta_lt_one
      (by linarith only [hnu]) B.A_pos B.A_lt_one B.eta_pos B.eta_lt_one
      B.F0_pos B.F0_large hwminR hq hwmin happrox

  let Ea : ℝ := FiniteMinorComparison.arithmeticError
    B.m (B.v0 : ℝ) (B.theta : ℝ) B.F0 (B.wmin : ℝ)
  let En : ℝ := FiniteMinorComparison.analyticError
    B.K nu B.F0 (B.v0 : ℝ) (B.w0 : ℝ) (B.wmin : ℝ)
  have herrsum : Ea + En = B.E := by
    dsimp [Ea, En, FiniteMinorComparison.arithmeticError,
      FiniteMinorComparison.analyticError]
    rw [B.E_eq]
    ring

  have hsmall : ∀ᶠ H : ℝ in atTop,
      B.E + error H <
        nu * (B.A * (1 - B.eta) - (B.theta : ℝ)) -
          (1 - (B.theta : ℝ)) := by
    have hs : Tendsto (fun H : ℝ => B.E + error H) atTop (𝓝 (B.E + 0)) :=
      tendsto_const_nhds.add herror
    exact hs.eventually (Iio_mem_nhds (by simpa only [add_zero] using B.error_gap))

  have hrate := OAI.PiExponent.finite_collision_rate_tendsto
    B.m B.K B.v0 B.theta B.A B.eta q B.v0_pos B.theta_pos B.A_pos hq
  have hlarge : ∀ᶠ H : ℝ in atTop,
      0 < FiniteMinorComparison.collisionRate
        B.K (B.v0 : ℝ) (B.theta : ℝ) B.A B.eta q H -
          (1 + B.E + error H) := by
    have hd : Tendsto
        (fun H : ℝ => FiniteMinorComparison.collisionRate
          B.K (B.v0 : ℝ) (B.theta : ℝ) B.A B.eta q H -
            (1 + B.E + error H)) atTop
        (𝓝 (FiniteMinorComparison.collisionLimit B.m B.K
          (B.v0 : ℝ) (B.theta : ℝ) B.A B.eta - (1 + B.E + 0))) :=
      hrate.sub (tendsto_const_nhds.add herror)
    apply hd.eventually (Ioi_mem_nhds ?_)
    have hh := B.collision_gap
    change 1 + B.E < FiniteMinorComparison.collisionLimit B.m B.K
      (B.v0 : ℝ) (B.theta : ℝ) B.A B.eta at hh
    linarith only [hh]

  have hcontradiction : ∀ᶠ H : ℝ in atTop,
      ∀ selection :
        InterpolationMatrix.Row B.K (B.v0 : ℝ) (B.theta : ℝ)
          (MatrixArithmetic.logWeights q) H →
        InterpolationMatrix.Column (B.w0 : ℝ)
          (MatrixArithmetic.logWeights q) H,
        (MatrixArithmetic.selectedMinor B.K (B.w0 : ℝ) (B.v0 : ℝ)
          (B.theta : ℝ) B.F0 H p q selection).det ≠ 0 → False := by
    filter_upwards [hsmall, hlarge, hupper,
      eventually_gt_atTop (0 : ℝ)] with H hs hl hu hH
    intro selection hdet
    obtain ⟨hb0, hbtheta, hlower⟩ :=
      OAI.PiExponent.finite_log_minor_arithmetic_controls
        B.m B.K (B.w0 : ℝ) (B.v0 : ℝ) (B.theta : ℝ) B.F0
        (B.wmin : ℝ) H p q B.K_pos hw0R hv0R hthetaR B.F0_pos.le
        hwminR hH hq hwmin selection hdet
    exact OAI.PiExponent.finite_minor_bounds_inconsistent
      nu (B.theta : ℝ) (B.A * (1 - B.eta))
      (MatrixArithmetic.meanRowWeight B.K (B.v0 : ℝ) (B.theta : ℝ) q H)
      Ea En (error H)
      (FiniteMinorComparison.collisionRate
        B.K (B.v0 : ℝ) (B.theta : ℝ) B.A B.eta q H)
      (Real.log ‖(MatrixArithmetic.selectedMinor B.K (B.w0 : ℝ) (B.v0 : ℝ)
        (B.theta : ℝ) B.F0 H p q selection).det‖ /
        ((Fintype.card (InterpolationMatrix.Row B.K (B.v0 : ℝ) (B.theta : ℝ)
          (MatrixArithmetic.logWeights q) H) : ℝ) * H))
      (by linarith only [hnu]) hb0 hbtheta
      (by linarith only [hs, herrsum])
      (by linarith only [hl, herrsum]) hlower (hu selection hdet)

  obtain ⟨L, hL⟩ := Filter.eventually_atTop.mp hcontradiction
  obtain ⟨H, hLH, _hH, selection, hdet⟩ := hcofinal L
  exact hL (H : ℝ) hLH selection hdet
