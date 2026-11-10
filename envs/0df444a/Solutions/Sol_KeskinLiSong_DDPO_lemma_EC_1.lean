-- Prove2me | solution 1 for KeskinLiSong.DDPO.lemma_EC_1
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T13:27:49.204209+00:00
-- url     : https://prove2.me/submissions/0f7e5278-364f-42d5-afdc-650b865c4bb5

import Definitions.Def_KeskinLiSong_DDPO_TailEvents

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section

namespace KeskinLiSong.DDPO

private def diracZeroMGF : LocalMGF where
  law := Measure.dirac 0
  probability := inferInstance
  sigma := 1
  rho := 1
  radius := 1
  sigma_pos := by norm_num
  rho_pos := by norm_num
  radius_pos := by norm_num
  first_integrable := integrable_dirac (by simp)
  centered := by simp
  second_integrable := integrable_dirac (by simp)
  variance_bound := by simp
  exponential_integrable := fun _ _ => integrable_dirac (by simp)
  exponential_bound := by
    intro a _
    rw [integral_dirac]
    simp only [mul_zero, Real.exp_zero]
    exact Real.one_le_exp (by positivity)

private def counterModel : Model where
  pmin := 1
  pmax := 2
  ymin := 1
  ymax := 2
  alphaMin := 0
  alphaMax := 0
  betaMin := -1
  betaMax := -1
  lambdaMin := 1
  lambdaMax := 1
  nuMin := 1
  nuMax := 1
  h := 2
  b := 0
  w := 0
  c := 2
  g := fun _ => 0
  price_bounds := by norm_num
  stock_bounds := by norm_num
  demand_bounds := by norm_num
  perish_bounds := by norm_num
  costs_nonnegative := by norm_num
  cost_restriction := by
    intro p hp
    rcases hp with ⟨hp1, _⟩
    rw [sub_self, abs_zero]
    linarith
  increasing := monotone_const
  smooth := contDiff_const
  noise := diracZeroMGF
  changes := 0
  separation := 1
  separation_pos := by norm_num

private def theta0 : Vector 2 := !₂[0, -1]
private def xi0 : Vector 2 := !₂[1, 1]

private lemma ae_mem_Ioo_perishLaw : ∀ᵐ q ∂perishLaw xi0, q ∈ Ioo (0 : ℝ) 1 := by
  rw [ae_iff]
  change (perishLaw xi0) (Ioo (0 : ℝ) 1)ᶜ = 0
  rw [perishLaw, betaMeasure, withDensity_apply _ measurableSet_Ioo.compl]
  have hzero : ∀ q ∈ (Ioo (0 : ℝ) 1)ᶜ, betaPDF (xi0 0) (xi0 1) q = 0 := by
    intro q hq
    have hnot : ¬ (0 < q ∧ q < 1) := hq
    simp [betaPDF, betaPDFReal, hnot]
  exact setLIntegral_eq_zero measurableSet_Ioo.compl hzero

private lemma slope_false_pos (y : ℝ) : 0 ≤ slope false counterModel theta0 xi0 1 y := by
  unfold slope
  have hI1 : 0 ≤ ∫ q, (1 - q) * (if false = true then cdf counterModel.noise.law
      else leftCdf counterModel.noise.law)
      ((1 - q) * y - meanDemand counterModel theta0 1) ∂perishLaw xi0 := by
    refine integral_nonneg_of_ae (ae_mem_Ioo_perishLaw.mono fun q hq => ?_)
    have h1q : 0 ≤ 1 - q := by linarith [hq.2]
    have hcdf : 0 ≤ leftCdf counterModel.noise.law ((1 - q) * y - meanDemand counterModel theta0 1) :=
      ENNReal.toReal_nonneg
    simpa using mul_nonneg h1q hcdf
  have hI2 : 0 ≤ ∫ q, q ∂perishLaw xi0 := by
    refine integral_nonneg_of_ae (ae_mem_Ioo_perishLaw.mono fun q hq => ?_)
    show (0 : ℝ) ≤ q
    exact le_of_lt hq.1
  change (2 - 2 + 0 + 1) *
      (∫ q, (1 - q) * (if false = true then cdf counterModel.noise.law
        else leftCdf counterModel.noise.law)
        ((1 - q) * y - meanDemand counterModel theta0 1) ∂perishLaw xi0) -
    (0 + 1) * (1 - ∫ q, q ∂perishLaw xi0) +
    (0 * (∫ q, q ∂perishLaw xi0) + 2) ≥ 0
  linarith

private lemma leftSignSup_eq_bot : leftSignSup counterModel theta0 xi0 1 = ⊥ := by
  unfold leftSignSup
  have hempty : {y ∈ counterModel.Y | slope false counterModel theta0 xi0 1 y < 0} = ∅ := by
    ext y
    simp only [mem_empty_iff_false, iff_false]
    rintro ⟨_, hlt⟩
    exact not_lt_of_ge (slope_false_pos y) hlt
  rw [hempty, image_empty, sSup_empty]

end KeskinLiSong.DDPO

set_option linter.unusedVariables false in
theorem solution : ¬ (∀ (A : KeskinLiSong.DDPO.Model) (theta xi : KeskinLiSong.DDPO.Vector 2) (p : ℝ)
    (hp : p ∈ A.P) (htheta : theta ∈ A.Theta) (hxi : xi ∈ A.Xi),
    (∃ y, KeskinLiSong.DDPO.StockOptimum A A.noise.law theta xi p y ∧
      (y : EReal) = KeskinLiSong.DDPO.rightSignInf A theta xi p ∧
      (y : EReal) = KeskinLiSong.DDPO.leftSignSup A theta xi p) ∧
    (∀ y ∈ A.Y,
      HasDerivWithinAt (KeskinLiSong.DDPO.H A A.noise.law theta xi p)
        (KeskinLiSong.DDPO.slope true A theta xi p y) (Ici y) y ∧
      HasDerivWithinAt (KeskinLiSong.DDPO.H A A.noise.law theta xi p)
        (KeskinLiSong.DDPO.slope false A theta xi p y) (Iic y) y)) := by
  intro H_thm
  have hp : (1 : ℝ) ∈ KeskinLiSong.DDPO.counterModel.P := by
    simp [KeskinLiSong.DDPO.Model.P, KeskinLiSong.DDPO.counterModel]
  have htheta : KeskinLiSong.DDPO.theta0 ∈ KeskinLiSong.DDPO.counterModel.Theta := by
    simp [KeskinLiSong.DDPO.Model.Theta, KeskinLiSong.DDPO.counterModel, KeskinLiSong.DDPO.theta0]
  have hxi : KeskinLiSong.DDPO.xi0 ∈ KeskinLiSong.DDPO.counterModel.Xi := by
    simp [KeskinLiSong.DDPO.Model.Xi, KeskinLiSong.DDPO.counterModel, KeskinLiSong.DDPO.xi0]
  rcases H_thm KeskinLiSong.DDPO.counterModel KeskinLiSong.DDPO.theta0 KeskinLiSong.DDPO.xi0 1 hp htheta hxi with
    ⟨⟨y, _, _, hleft⟩, _⟩
  rw [KeskinLiSong.DDPO.leftSignSup_eq_bot] at hleft
  exact EReal.coe_ne_bot y hleft
