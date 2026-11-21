-- Prove2me | solution 1 for MasulloRH.theta_cutoff_tolerance_iff_finite_prime_certificates
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T03:29:52.51341+00:00
-- url     : https://prove2.me/submissions/7de7de14-233e-4cdc-b5df-04202d0cb51e

-- New bridge between the quantitative versions of the theta and prime frontiers.
import Theorems.Thm_MasulloRH_cofinal_prime_slack_iff_off_line_mass_le
import Theorems.Thm_MasulloRH_rational_theta_cutoff_trace_defect
import Theorems.Thm_MasulloRH_rational_theta_annihilator_jet_trace
import Theorems.Thm_MasulloRH_regularized_test_admissible
import Definitions.Def_MasulloRH_RationalThetaSpace
import Definitions.Def_MasulloRH_RegularizedTrace
import Definitions.Def_MasulloGRH_HilbertNuclear
open MasulloRH MasulloGRH Filter
open scoped Topology
open ArithmeticFunction

theorem solution (τ : ℝ) :
    let f := fun j : ℕ => vonMangoldt j/(j:ℝ)^(5/2:ℝ) - vonMangoldt j/(j:ℝ)^(3:ℝ)
    let C := Real.log 2/2 + Real.pi/4 - 37/30
    let Z := {z : ZetaZerosInTraceStrip (1/2) // z.val.re = 1/2}
    let M := fun F : Finset Z => ∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val.val:ℝ) *
      ((z.val.val.im^2-5)/(2*(z.val.val.im^2+25/4)*(z.val.val.im^2+4)))
    (∀ ε : ℝ, τ < ε → ∀ N : ℕ, ∃ n ≥ N,
      ∀ T : rationalThetaAnnihilator ((n:ℝ)+1) →L[ℂ] rationalThetaAnnihilator ((n:ℝ)+1),
        IsRationalThetaConvolution ((n:ℝ)+1) (regularizedTraceTest n 3) T →
        (cutoffPolar n 3 - (cutoffArch n 3 + cutoffPrime n 3)).re ≤ (operatorTrace T).re + ε) ↔ ∀ k : ℕ, ∃ N ≥ k, ∃ F : Finset Z,
      C + (∑ j ∈ Finset.range N,f j) ≤ M F + τ + 1/((k:ℝ)+1) := by
  classical
  dsimp only
  refine Iff.trans ?_ (cofinal_prime_slack_iff_off_line_mass_le τ)
  let D := ∑' z : {z : ZetaZerosInTraceStrip (1/2) // z.val.re ≠ 1/2},
    (zeroResolventTerm (1/2) 3 z.val).re
  let H := fun n : ℕ => rationalThetaAnnihilator ((n:ℝ)+1)
  let A := fun n : ℕ => H n →L[ℂ] H n
  let conv := fun (n : ℕ) (T : A n) =>
    IsRationalThetaConvolution ((n:ℝ)+1) (regularizedTraceTest n 3) T
  let err := fun (n : ℕ) (T : A n) =>
    (cutoffPolar n 3 - (cutoffArch n 3 + cutoffPrime n 3)).re - (operatorTrace T).re
  have hExists (n : ℕ) : ∃ T : A n, conv n T := by
    have ht := (rational_theta_annihilator_jet_trace ((n:ℝ)+1) (by linarith [Nat.cast_nonneg (α:=ℝ) n])).2
      (regularizedTraceTest n 3) (regularized_test_admissible n 3)
    obtain ⟨T,hT⟩ := ht.exists
    exact ⟨T,hT.1⟩
  constructor
  · intro hall
    by_contra! h
    change τ < D at h
    let ε := (τ+D)/2
    have hτε : τ < ε := by dsimp [ε]; linarith
    have hεD : ε < D := by dsimp [ε]; linarith
    choose T hT using hExists
    have ht : Tendsto (fun n => err n (T n)) atTop (𝓝 D) := (rational_theta_cutoff_trace_defect T hT).1
    obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (lt_mem_nhds hεD))
    obtain ⟨n,hn,halln⟩ := hall ε hτε N
    have ha := halln (T n) (hT n)
    have hb := hN n hn
    dsimp only [err] at hb
    linarith
  · intro h ε hε N
    change D ≤ τ at h
    have hex (n : ℕ) : ∃ T : A n, conv n T ∧
        ((∃ U : A n, conv n U ∧ ε < err n U) → ε < err n T) := by
      by_cases hh : ∃ U : A n, conv n U ∧ ε < err n U
      · obtain ⟨U,hu,hb⟩ := hh; exact ⟨U,hu,fun _ => hb⟩
      · obtain ⟨U,hu⟩ := hExists n; exact ⟨U,hu,fun h' => (hh h').elim⟩
    choose T hT hbad using hex
    have ht : Tendsto (fun n => err n (T n)) atTop (𝓝 D) := (rational_theta_cutoff_trace_defect T hT).1
    obtain ⟨m,hm⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds (h.trans_lt hε)))
    let n := max m N
    refine ⟨n,le_max_right _ _,?_⟩
    intro U hU
    have hu : err n U ≤ ε := le_of_not_gt (fun hb =>
      (not_lt_of_ge (hm n (le_max_left _ _)).le) (hbad n ⟨U,hU,hb⟩))
    dsimp only [err] at hu
    linarith
