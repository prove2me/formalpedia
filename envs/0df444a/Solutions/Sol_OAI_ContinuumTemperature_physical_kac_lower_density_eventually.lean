-- Prove2me | solution 1 for OAI.ContinuumTemperature.physical_kac_lower_density_eventually
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:10:26.604842+00:00
-- url     : https://prove2.me/submissions/e3e0e5c3-ac77-4d5a-b0b6-427f484faa44

import Mathlib
import Definitions.Def_ContinuumTransition
import Definitions.Def_OAIQWCT000

section
-- module Solutions.OAIQW_ContinuumTemperature.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434
end

section
-- module Solutions.OAIQW_ContinuumTemperature.RadialKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set

namespace ContinuumTemperature

noncomputable section
open scoped ContDiff

theorem baseKernel_nonneg (x : Space) : 0 ≤ baseKernel x := Real.smoothTransition.nonneg _

theorem baseKernel_eq_one {x : Space} (hx : ‖x‖ ≤ 1 / 2) : baseKernel x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith

theorem baseKernel_eq_zero {x : Space} (hx : 1 ≤ ‖x‖) : baseKernel x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  linarith

theorem contDiff_baseKernel : ContDiff ℝ ∞ baseKernel := by
  have heq : baseKernel = fun x : Space =>
      (ContDiffBumpBase.ofInnerProductSpace Space).toFun 2 ((2 : ℝ) • x) := by
    funext x
    norm_num [baseKernel, ContDiffBumpBase.ofInnerProductSpace, norm_smul]
  rw [heq]
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hmem : ((2 : ℝ), (2 : ℝ) • x) ∈ Ioi (1 : ℝ) ×ˢ (Set.univ : Set Space) := by
    norm_num
  have hdiff := (ContDiffBumpBase.ofInnerProductSpace Space).smooth.contDiffAt
    ((isOpen_Ioi.prod isOpen_univ).mem_nhds hmem)
  have hcomp := hdiff.comp x (contDiffAt_const.prodMk
    (ContDiffAt.const_smul (2 : ℝ) contDiffAt_id) :
      ContDiffAt ℝ ∞ (fun y : Space => ((2 : ℝ), (2 : ℝ) • y)) x)
  exact hcomp

theorem hasCompactSupport_baseKernel : HasCompactSupport baseKernel := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Space) 1)
  intro x hx
  exact baseKernel_eq_zero (by simpa using (not_lt.mp (fun h => hx (by simpa using h.le))))

theorem integrable_baseKernel : Integrable baseKernel :=
  contDiff_baseKernel.continuous.integrable_of_hasCompactSupport hasCompactSupport_baseKernel

theorem integral_baseKernel_pos : 0 < ∫ x : Space, baseKernel x := by
  rw [integral_pos_iff_support_of_nonneg baseKernel_nonneg integrable_baseKernel]
  have hball : (Metric.ball (0 : Space) (1 / 2 : ℝ)).Nonempty := ⟨0, by norm_num⟩
  apply lt_of_lt_of_le (Metric.isOpen_ball.measure_pos volume hball)
  apply measure_mono
  intro x hx
  have hn : ‖x‖ < 1 / 2 := by simpa using hx
  rw [Function.mem_support, baseKernel_eq_one hn.le]
  norm_num

theorem kernel_eq (x : Space) : kernel x = baseKernel x / (∫ y : Space, baseKernel y) := rfl

theorem contDiff_kernel : ContDiff ℝ ∞ kernel := contDiff_baseKernel.div_const _

theorem integral_kernel : ∫ x : Space, kernel x = 1 := by
  simp_rw [kernel_eq]
  rw [integral_div, div_self integral_baseKernel_pos.ne']

theorem kernel_zero_outside {x : Space} (hx : 1 ≤ ‖x‖) : kernel x = 0 := by
  rw [kernel_eq, baseKernel_eq_zero hx, zero_div]

theorem kernelProfile_nonneg (r : ℝ) : 0 ≤ kernelProfile r :=
  div_nonneg (Real.smoothTransition.nonneg _) integral_baseKernel_pos.le

theorem kernelProfile_le (r : ℝ) : kernelProfile r ≤ 1 / (∫ x : Space, baseKernel x) := by
  exact div_le_div_of_nonneg_right (Real.smoothTransition.le_one _) integral_baseKernel_pos.le

theorem continuous_kernelProfile : Continuous kernelProfile := by
  unfold kernelProfile
  exact (Real.smoothTransition.continuous.comp (continuous_const.sub
    (continuous_const.mul continuous_id))).div_const _

theorem kernelProfile_zero {r : ℝ} (hr : 1 ≤ r) : kernelProfile r = 0 := by
  unfold kernelProfile
  rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_div]

theorem scaledKernelProfile_nonneg {R : ℝ} (hR : 0 < R) (r : ℝ) :
    0 ≤ scaledKernelProfile R r :=
  mul_nonneg (by positivity) (kernelProfile_nonneg _)

theorem scaledKernelProfile_le {R : ℝ} (hR : 0 < R) (r : ℝ) :
    scaledKernelProfile R r ≤ R⁻¹ ^ 3 / (∫ x : Space, baseKernel x) := by
  dsimp [scaledKernelProfile]
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left (kernelProfile_le (r / R))
    (by positivity : (0 : ℝ) ≤ R⁻¹ ^ 3)

theorem scaledKernelProfile_zero {R r : ℝ} (hR : 0 < R) (hr : R ≤ r) :
    scaledKernelProfile R r = 0 := by
  unfold scaledKernelProfile
  rw [kernelProfile_zero ((le_div_iff₀ hR).mpr (by simpa using hr)), mul_zero]

theorem continuous_scaledKernelProfile (R : ℝ) : Continuous (scaledKernelProfile R) := by
  exact continuous_const.mul (continuous_kernelProfile.comp (continuous_id.div_const _))

theorem kernelHeight_pos : 0 < kernelHeight := one_div_pos.mpr integral_baseKernel_pos

theorem scaledKernelProfile_le_height {R : ℝ} (hR : 1 ≤ R) (r : ℝ) :
    scaledKernelProfile R r ≤ kernelHeight := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  calc
    _ ≤ R⁻¹ ^ 3 / (∫ x : Space, baseKernel x) := scaledKernelProfile_le hRp r
    _ ≤ kernelHeight := by
      unfold kernelHeight
      apply div_le_div_of_nonneg_right _ integral_baseKernel_pos.le
      exact pow_le_one₀ (inv_nonneg.mpr hRp.le) (inv_le_one_of_one_le₀ hR)

end
end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ProfileTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature
noncomputable section
open scoped ContDiff

theorem summable_attraction_terms {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (hs : Summable σ) (r : ℝ) :
    Summable (fun j => σ j * scaledKernelProfile (R j) r) := by
  apply (hs.mul_right kernelHeight).of_norm_bounded
  intro j
  rw [Real.norm_of_nonneg (mul_nonneg (hσ j)
    (scaledKernelProfile_nonneg (lt_of_lt_of_le zero_lt_one (hR j)) r))]
  exact mul_le_mul_of_nonneg_left (scaledKernelProfile_le_height (hR j) r) (hσ j)

theorem attraction_nonneg {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (r : ℝ) :
    0 ≤ attraction t σ R r := by
  apply mul_nonneg ht
  exact tsum_nonneg (fun j => mul_nonneg (hσ j)
    (scaledKernelProfile_nonneg (lt_of_lt_of_le zero_lt_one (hR j)) r))

theorem attraction_le {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (hs : Summable σ) (r : ℝ) :
    attraction t σ R r ≤ t * (∑' j, σ j) * kernelHeight := by
  unfold attraction
  rw [mul_assoc, ← hs.tsum_mul_right]
  apply mul_le_mul_of_nonneg_left _ ht
  exact (summable_attraction_terms hσ hR hs r).tsum_le_tsum
    (fun j => mul_le_mul_of_nonneg_left (scaledKernelProfile_le_height (hR j) r) (hσ j))
    (hs.mul_right kernelHeight)

theorem continuous_attraction (t : ℝ) {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (hs : Summable σ) :
    Continuous (attraction t σ R) := by
  apply continuous_const.mul
  apply continuous_tsum (fun j => continuous_const.mul (continuous_scaledKernelProfile (R j)))
    (hs.mul_right kernelHeight)
  intro j r
  change ‖σ j * scaledKernelProfile (R j) r‖ ≤ σ j * kernelHeight
  rw [Real.norm_of_nonneg (mul_nonneg (hσ j)
    (scaledKernelProfile_nonneg (lt_of_lt_of_le zero_lt_one (hR j)) r))]
  exact mul_le_mul_of_nonneg_left (scaledKernelProfile_le_height (hR j) r) (hσ j)

theorem coreProfile_eq_zero {t r : ℝ} (ht : 1 < t) (hr : 1 ≤ r) :
    coreProfile t r = 0 := by
  have he : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hs : (1 + shellDelta) * Real.exp (-t) < 1 := by
    have ht' : Real.exp t > 1 + t := by simpa only [add_comm] using (Real.add_one_lt_exp (by linarith : t ≠ 0))
    rw [Real.exp_neg]
    unfold shellDelta
    apply (mul_inv_lt_iff₀ (Real.exp_pos t)).mpr
    linarith
  unfold coreProfile
  rw [ite_eq_right (by linarith), ite_eq_right (by linarith), ite_eq_right (not_lt.mpr hr)]

theorem physicalProfile_nonpos {t r : ℝ} (ht : 1 < t) {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (hr : 1 ≤ r) :
    physicalProfile t σ R r ≤ 0 := by
  rw [physicalProfile, coreProfile_eq_zero ht hr, zero_sub]
  exact neg_nonpos.mpr (attraction_nonneg (by linarith) hσ hR r)

end
end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ProfileBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature
noncomputable section
open scoped ContDiff

theorem measurable_coreProfile (t : ℝ) : Measurable (coreProfile t) := by
  unfold coreProfile
  apply Measurable.ite (measurableSet_lt measurable_id measurable_const)
    (measurable_const.add ((measurable_const.div measurable_id).pow_const 12))
  apply Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
    measurable_const measurable_const

theorem coreProfile_nonneg (t r : ℝ) : 0 ≤ coreProfile t r := by
  unfold coreProfile
  split_ifs <;> positivity

theorem coreProfile_le {a r : ℝ} (ha : 0 < a) (har : a ≤ r) (t : ℝ) :
    coreProfile t r ≤ t ^ 2 + (Real.exp (-t) / a) ^ 12 := by
  have hdiv : Real.exp (-t) / r ≤ Real.exp (-t) / a :=
    div_le_div_of_nonneg_left (Real.exp_pos _).le ha har
  have hp := pow_le_pow_left₀ (div_nonneg (Real.exp_pos _).le (ha.le.trans har)) hdiv 12
  unfold coreProfile
  split_ifs <;> nlinarith [sq_nonneg t, even_two_mul 6 |>.pow_nonneg (Real.exp (-t) / a)]

theorem measurable_physicalProfile (t : ℝ) {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (hs : Summable σ) :
    Measurable (physicalProfile t σ R) :=
  (measurable_coreProfile t).sub (continuous_attraction t hσ hR hs).measurable

theorem measurable_radialPotential {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Measurable (radialPotential φ) := by
  apply Measurable.ite (measurableSet_singleton (0 : Space)) measurable_const
  exact measurable_coe_real_ereal.comp (hφ.comp measurable_norm)

end
end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ShellGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature
noncomputable section
open scoped ContDiff

open scoped InnerProductSpace

theorem affineIndependent_of_sq_dist_close {E : Type u_1} {ι : Type u_2}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
    (v : ι → E) {a ε : ℝ} (hε : 0 ≤ ε)
    (hgap : ε * Fintype.card ι < a)
    (hdist : ∀ i j, i ≠ j → |‖v i - v j‖ ^ 2 - a| ≤ ε) :
    AffineIndependent ℝ v := by
  classical
  rw [affineIndependent_iff_of_fintype]
  intro w hw hv
  rw [Finset.univ.weightedVSub_eq_linear_combination hw] at hv
  have hid := inner_sum_smul_sum_smul_of_sum_eq_zero v hw v hw
  rw [hv, inner_zero_left] at hid
  have hzero : (∑ i, ∑ j, w i * w j * ‖v i - v j‖ ^ 2) = 0 := by
    simp only [← sq] at hid
    linarith
  have hpair (i j : ι) :
      w i * w j * ‖v i - v j‖ ^ 2 ≤
        a * w i * w j - (if i = j then a * w i ^ 2 else 0) +
          ε / 2 * (w i ^ 2 + w j ^ 2) := by
    by_cases hij : i = j
    · subst j
      simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, mul_zero, ↓reduceIte]
      nlinarith [mul_nonneg hε (sq_nonneg (w i))]
    · rw [ite_eq_right hij]
      have habs : w i * w j * (‖v i - v j‖ ^ 2 - a) ≤ |w i * w j| * ε := by
        calc
          _ ≤ |w i * w j * (‖v i - v j‖ ^ 2 - a)| := le_abs_self _
          _ = |w i * w j| * |‖v i - v j‖ ^ 2 - a| := abs_mul _ _
          _ ≤ |w i * w j| * ε := mul_le_mul_of_nonneg_left (hdist i j hij) (abs_nonneg _)
      have htwo : 2 * |w i * w j| ≤ w i ^ 2 + w j ^ 2 := by
        rw [abs_mul]
        nlinarith [sq_nonneg (|w i| - |w j|), sq_abs (w i), sq_abs (w j)]
      have := mul_le_mul_of_nonneg_left htwo hε
      nlinarith
  have htotal := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hpair i j))
  have hdiag : (∑ i, ∑ j, if i = j then a * w i ^ 2 else 0) = a * ∑ i, w i ^ 2 := by
    simp [← Finset.mul_sum]
  have hmain : (∑ i, ∑ j, a * w i * w j) = 0 := by
    simp only [← Finset.mul_sum, hw, mul_zero, Finset.sum_const_zero]
  have herror : (∑ i, ∑ j, ε / 2 * (w i ^ 2 + w j ^ 2)) =
      ε * (Fintype.card ι : ℝ) * ∑ i, w i ^ 2 := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, Finset.card_univ]
    ring
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at htotal
  rw [hzero, hmain, hdiag, herror] at htotal
  have hsnonneg : 0 ≤ ∑ i, w i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs0 : (∑ i, w i ^ 2) = 0 := by nlinarith
  intro i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
    sq_nonneg (w j))).mp hs0 i (Finset.mem_univ i)
  exact sq_eq_zero_iff.mp hi

theorem no_five_in_shell (v : Fin 5 → EuclideanSpace ℝ (Fin 3)) {r : ℝ}
    (hr : 0 < r)
    (hlow : ∀ i j, i ≠ j → r ≤ ‖v i - v j‖)
    (hupp : ∀ i j, i ≠ j → ‖v i - v j‖ ≤ (1 + shellDelta) * r) : False := by
  have hai : AffineIndependent ℝ v := by
    apply affineIndependent_of_sq_dist_close v
      (a := r ^ 2) (ε := (2 * shellDelta + shellDelta ^ 2) * r ^ 2)
    · dsimp [shellDelta]
      positivity
    · simp only [Fintype.card_fin]
      dsimp [shellDelta]
      nlinarith [sq_pos_of_pos hr]
    · intro i j hij
      have hlo := hlow i j hij
      have hup := hupp i j hij
      rw [abs_le]
      constructor
      · have hnorm := norm_nonneg (v i - v j)
        have hsq := sq_le_sq₀ hr.le hnorm |>.mpr hlo
        dsimp [shellDelta]
        nlinarith [sq_nonneg r]
      · have hnorm := norm_nonneg (v i - v j)
        have hsq := sq_le_sq₀ hnorm (by dsimp [shellDelta]; positivity) |>.mpr hup
        dsimp [shellDelta] at hsq ⊢
        nlinarith
  have hdim := hai.card_le_finrank_succ
  have hle := Submodule.finrank_le (vectorSpan ℝ (range v))
  have hthree : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  rw [hthree] at hle
  simp only [Fintype.card_fin] at hdim
  omega

theorem shellGraph_cliqueFree {ι : Type u_1} (v : ι → EuclideanSpace ℝ (Fin 3))
    {r : ℝ} (hr : 0 < r) : (shellGraph v r).CliqueFree 5 := by
  classical
  intro s hs
  let e : ↥s ≃ Fin 5 := Finset.equivFinOfCardEq hs.card_eq
  let q : Fin 5 → EuclideanSpace ℝ (Fin 3) := fun i => v (e.symm i)
  apply no_five_in_shell q hr
  · intro i j hij
    have hne : (e.symm i : ι) ≠ e.symm j := by
      intro he
      apply hij
      exact e.symm.injective (Subtype.ext he)
    exact (hs.isClique (e.symm i).property (e.symm j).property hne).2.1
  · intro i j hij
    have hne : (e.symm i : ι) ≠ e.symm j := by
      intro he
      apply hij
      exact e.symm.injective (Subtype.ext he)
    exact (hs.isClique (e.symm i).property (e.symm j).property hne).2.2

theorem shellGraph_edge_bound {ι : Type u_1} [Fintype ι]
    (v : ι → EuclideanSpace ℝ (Fin 3)) {r : ℝ} (hr : 0 < r) :
    letI := Classical.decRel (shellGraph v r).Adj
    8 * (shellGraph v r).edgeFinset.card ≤ 3 * (Fintype.card ι) ^ 2 := by
  classical
  have h := (shellGraph_cliqueFree v hr).card_edgeFinset_le (r := 4)
  simp only at h
  have hm : Fintype.card ι % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hle : (Fintype.card ι % 4) ^ 2 ≤ Fintype.card ι ^ 2 :=
    Nat.pow_le_pow_left (Nat.mod_le _ _) 2
  generalize Fintype.card ι % 4 = m at h hm hle
  generalize Fintype.card ι ^ 2 = N at h hle ⊢
  generalize (shellGraph v r).edgeFinset.card = E at h ⊢
  interval_cases m <;> simp at h hle ⊢ <;> omega

theorem coreProfile_ge_of_not_shell (t r : ℝ) (hr : r < 1)
    (hnot : ¬ (Real.exp (-t) ≤ r ∧ r ≤ (1 + shellDelta) * Real.exp (-t))) :
    t ^ 2 ≤ coreProfile t r := by
  unfold coreProfile
  split_ifs with hlow hhigh
  · have hp : 0 ≤ (Real.exp (-t) / r) ^ 12 := by positivity
    linarith
  · exact False.elim (hnot ⟨le_of_not_gt hlow, hhigh⟩)
  · rfl

end
end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.CellEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature
noncomputable section
open scoped ContDiff
open scoped InnerProductSpace

theorem two_mul_pairSum {ι : Type u_1} [Fintype ι] [LinearOrder ι]
    (f : ι → ι → ℝ) (hsym : ∀ i j, f i j = f j i) :
    2 * pairSum f = ∑ i, ∑ j, if i = j then 0 else f i j := by
  classical
  have hsplit (i j : ι) : (if i = j then 0 else f i j) =
      (if i < j then f i j else 0) + (if j < i then f j i else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · subst j; simp
    · simp [h, ne_of_gt h, not_lt_of_ge h.le, hsym i j]
  simp_rw [hsplit]
  simp_rw [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j : ι => if j < i then f j i else 0)]
  simp only [pairSum, Finset.sum_filter]
  ring

theorem sum_adjacency_indicator {ι : Type u_1} [Fintype ι] (G : SimpleGraph ι) :
    letI := Classical.decRel G.Adj
    (∑ i, ∑ j, if G.Adj i j then (1 : ℝ) else 0) = 2 * (G.edgeFinset.card : ℝ) := by
  classical
  have h := congrArg (fun n : ℕ => (n : ℝ)) G.two_mul_card_edgeFinset
  rw [Finset.card_filter] at h
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum, Nat.cast_ite] at h
  rw [Fintype.sum_prod_type] at h
  simpa only [Nat.cast_one, Nat.cast_zero] using h.symm

theorem core_one_cell_bound {ι : Type u_1} [Fintype ι] [LinearOrder ι]
    (v : ι → EuclideanSpace ℝ (Fin 3)) (t : ℝ)
    (hdiam : ∀ i j, ‖v i - v j‖ < 1) :
    t ^ 2 / 8 * (Fintype.card ι : ℝ) ^ 2 - t ^ 2 / 2 * Fintype.card ι ≤
      pairSum (fun i j => coreProfile t ‖v i - v j‖) := by
  classical
  let G := shellGraph v (Real.exp (-t))
  have hpoint (i j : ι) :
      t ^ 2 * (1 - (if G.Adj i j then 1 else 0) - (if i = j then 1 else 0)) ≤
        if i = j then 0 else coreProfile t ‖v i - v j‖ := by
    by_cases hij : i = j
    · subst j
      simp
    · simp only [ite_eq_right hij, sub_zero]
      by_cases hadj : G.Adj i j
      · simp only [ite_eq_left hadj, sub_self, mul_zero]
        exact coreProfile_nonneg _ _
      · simp only [ite_eq_right hadj, sub_zero, mul_one]
        apply coreProfile_ge_of_not_shell _ _ (hdiam i j)
        intro hshell
        exact hadj ⟨hij, hshell⟩
  have htotal := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hpoint i j))
  have horient := two_mul_pairSum (fun i j => coreProfile t ‖v i - v j‖)
    (fun i j => by rw [norm_sub_rev])
  have hadj := sum_adjacency_indicator G
  have hdiag : (∑ i : ι, ∑ j : ι, if i = j then (1 : ℝ) else 0) = Fintype.card ι := by simp
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib] at htotal
  rw [hadj, hdiag, ← horient] at htotal
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at htotal
  have hedge := shellGraph_edge_bound v (Real.exp_pos (-t))
  have hedger : 8 * (G.edgeFinset.card : ℝ) ≤ 3 * (Fintype.card ι : ℝ) ^ 2 := by exact_mod_cast hedge
  nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hedger)]

theorem row_sum_quadratic_bound {ι : Type u_1} [Fintype ι]
    (J : ι → ι → ℝ) (n : ι → ℝ) (M : ℝ)
    (hJ : ∀ i j, 0 ≤ J i j) (hsym : ∀ i j, J i j = J j i)
    (hrow : ∀ i, ∑ j, J i j ≤ M) :
    ∑ i, ∑ j, J i j * n i * n j ≤ M * ∑ i, n i ^ 2 := by
  have hYoung (i j : ι) : 2 * (J i j * n i * n j) ≤
      J i j * n i ^ 2 + J i j * n j ^ 2 := by
    nlinarith [mul_nonneg (hJ i j) (sq_nonneg (n i - n j))]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hYoung i j))
  simp_rw [Finset.sum_add_distrib] at hs
  simp only [← Finset.mul_sum] at hs
  have hswap : (∑ i, ∑ j, J i j * n j ^ 2) = ∑ i, ∑ j, J i j * n i ^ 2 := by
    rw [Finset.sum_comm]
    congr 1
    funext i
    congr 1
    funext j
    rw [hsym j i]
  rw [hswap] at hs
  have hr : (∑ i, ∑ j, J i j * n i ^ 2) ≤ M * ∑ i, n i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _)
  linarith

theorem superstable_algebra {ι : Type u_1} [Fintype ι]
    (J : ι → ι → ℝ) (n : ι → ℝ) (M t N Ucore Uattr : ℝ)
    (hJ : ∀ i j, 0 ≤ J i j) (hsym : ∀ i j, J i j = J j i)
    (hrow : ∀ i, ∑ j, J i j ≤ M)
    (hcore : t ^ 2 / 8 * (∑ i, n i ^ 2) - t ^ 2 / 2 * N ≤ Ucore)
    (hattr : Uattr ≤ (1 / 2 : ℝ) * ∑ i, ∑ j, J i j * n i * n j) :
    (t ^ 2 / 8 - M / 2) * (∑ i, n i ^ 2) - t ^ 2 / 2 * N ≤ Ucore - Uattr := by
  have hq := row_sum_quadratic_bound J n M hJ hsym hrow
  nlinarith

theorem sum_subtype_le_of_nonneg {ι : Type u_1} [Fintype ι]
    (p : ι → Prop) [DecidablePred p] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ i : {i // p i}, f i ≤ ∑ i, f i := by
  have h := Fintype.sum_subtype_add_sum_subtype p f
  have hp : 0 ≤ ∑ i : {i // ¬ p i}, f i := Finset.sum_nonneg (fun i _ => hf i)
  linarith

theorem core_partition_bound {ι : Type u_1} {κ : Type u_2} [Fintype ι] [LinearOrder ι]
    [Fintype κ] [DecidableEq κ] (c : ι → κ) (v : ι → EuclideanSpace ℝ (Fin 3)) (t : ℝ)
    (hdiam : ∀ i j, c i = c j → ‖v i - v j‖ < 1) :
    t ^ 2 / 8 * (∑ k, (Fintype.card {i // c i = k} : ℝ) ^ 2) -
      t ^ 2 / 2 * Fintype.card ι ≤ pairSum (fun i j => coreProfile t ‖v i - v j‖) := by
  classical
  let f (i j : ι) : ℝ := if i = j then 0 else coreProfile t ‖v i - v j‖
  have hf (i j : ι) : 0 ≤ f i j := by
    dsimp [f]
    split_ifs
    · rfl
    · exact coreProfile_nonneg _ _
  let U (k : κ) : ℝ := pairSum (fun i j : {i // c i = k} => coreProfile t ‖v i - v j‖)
  have htwocell (k : κ) : 2 * U k = ∑ i : {i // c i = k}, ∑ j : {j // c j = k}, f i j := by
    dsimp [U]
    rw [two_mul_pairSum _ (fun i j => by rw [norm_sub_rev])]
    simp only [f, Subtype.ext_iff]
  have htwototal : 2 * pairSum (fun i j => coreProfile t ‖v i - v j‖) = ∑ i, ∑ j, f i j :=
    two_mul_pairSum _ (fun i j => by rw [norm_sub_rev])
  have hu : 2 * (∑ k, U k) ≤ 2 * pairSum (fun i j => coreProfile t ‖v i - v j‖) := by
    rw [Finset.mul_sum, htwototal]
    simp_rw [htwocell]
    calc
      _ ≤ ∑ k : κ, ∑ i : {i // c i = k}, ∑ j : ι, f i j := by
        apply Finset.sum_le_sum
        intro k _
        apply Finset.sum_le_sum
        intro i _
        exact sum_subtype_le_of_nonneg (fun j => c j = k) (f i) (hf i)
      _ = _ := Fintype.sum_fiberwise c (fun i => ∑ j, f i j)
  have hs (k : κ) : t ^ 2 / 8 * (Fintype.card {i // c i = k} : ℝ) ^ 2 -
      t ^ 2 / 2 * Fintype.card {i // c i = k} ≤ U k := by
    apply core_one_cell_bound
    intro i j
    exact hdiam i j (i.property.trans j.property.symm)
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset κ)) => hs k)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  have hcard : (∑ k, (Fintype.card {i // c i = k} : ℝ)) = Fintype.card ι := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
      Fintype.sum_fiberwise c (fun _ => (1 : ℝ))
  rw [hcard] at hsum
  linarith

end
end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.LatticeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature
noncomputable section
open scoped ContDiff
open scoped InnerProductSpace

theorem dist_lt_one_of_cellIndex_eq {x y : EuclideanSpace ℝ (Fin 3)}
    (h : cellIndex x = cellIndex y) : ‖x - y‖ < 1 := by
  have hcoord (k : Fin 3) : |x k - y k| < (1 / 4 : ℝ) := by
    have heq : ⌊4 * x k⌋ = ⌊4 * y k⌋ := congrFun h k
    have hxlo := Int.floor_le (4 * x k)
    have hxhi := Int.lt_floor_add_one (4 * x k)
    have hylo := Int.floor_le (4 * y k)
    have hyhi := Int.lt_floor_add_one (4 * y k)
    rw [heq] at hxlo hxhi
    rw [abs_lt]
    constructor <;> linarith
  have hsq (k : Fin 3) : (x k - y k) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
    have hc := (hcoord k).le
    have := sq_le_sq₀ (abs_nonneg (x k - y k)) (by norm_num : (0 : ℝ) ≤ 1 / 4) |>.mpr hc
    simpa only [sq_abs] using this
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 3))) => hsq k)
  have hnorm : ‖x - y‖ ^ 2 ≤ 3 * (1 / 4 : ℝ) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa only [PiLp.sub_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat] using hsum
  nlinarith [norm_nonneg (x-y)]

theorem mem_nearCells_iff {R : ℝ} {i j : Lattice} :
    j ∈ nearCells R i ↔ ∀ k, |j k - i k| ≤ cellRadius R := by
  simp only [nearCells, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]
  refine forall_congr' (fun k => ?_)
  omega

theorem nearCells_symm {R : ℝ} {i j : Lattice} :
    j ∈ nearCells R i ↔ i ∈ nearCells R j := by
  simp only [mem_nearCells_iff, abs_sub_comm]

theorem cellRadius_nonneg {R : ℝ} (hR : 0 ≤ R) : 0 ≤ cellRadius R :=
  Int.ceil_nonneg (by linarith)

theorem cellRadius_le {R : ℝ} (hR : 1 ≤ R) : (cellRadius R : ℝ) ≤ 6 * R := by
  have h := Int.ceil_lt_add_one (4 * R + 1)
  dsimp [cellRadius]
  linarith

theorem card_nearCells {R : ℝ} (hR : 0 ≤ R) (i : Lattice) :
    ((nearCells R i).card : ℝ) = (2 * (cellRadius R : ℝ) + 1) ^ 3 := by
  have hn := cellRadius_nonneg hR
  have hc (k : Fin 3) : ((Finset.Icc (i k - cellRadius R) (i k + cellRadius R)).card : ℝ) =
      2 * (cellRadius R : ℝ) + 1 := by
    have h := Int.card_Icc_of_le (i k - cellRadius R) (i k + cellRadius R) (by omega)
    exact_mod_cast h.trans (by ring)
  rw [nearCells, Fintype.card_piFinset, Nat.cast_prod]
  simp only [hc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem card_nearCells_le {R : ℝ} (hR : 1 ≤ R) (i : Lattice) :
    ((nearCells R i).card : ℝ) ≤ 2197 * R ^ 3 := by
  rw [card_nearCells (by linarith)]
  have hn := cellRadius_nonneg (show 0 ≤ R by linarith)
  have hn' : (0 : ℝ) ≤ cellRadius R := by exact_mod_cast hn
  have h : 2 * (cellRadius R : ℝ) + 1 ≤ 13 * R := by
    have := cellRadius_le hR
    linarith
  have hp := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 2 * cellRadius R + 1) h 3
  nlinarith only [hp]

theorem cellIndex_mem_nearCells {x y : EuclideanSpace ℝ (Fin 3)} {R : ℝ}
    (hd : ‖x - y‖ ≤ R) : cellIndex y ∈ nearCells R (cellIndex x) := by
  rw [mem_nearCells_iff]
  intro k
  have hx1 := Int.floor_le (4 * x k)
  have hx2 := Int.lt_floor_add_one (4 * x k)
  have hy1 := Int.floor_le (4 * y k)
  have hy2 := Int.lt_floor_add_one (4 * y k)
  have hcoord : |x k - y k| ≤ R := by
    have h := PiLp.norm_apply_le (x - y) k
    have hc : |x k - y k| ≤ ‖x - y‖ := by
      simpa only [PiLp.sub_apply, Real.norm_eq_abs] using h
    exact hc.trans hd
  have hceil : 4 * R + 1 ≤ (cellRadius R : ℝ) := Int.le_ceil _
  have habs : |((cellIndex y k : ℤ) : ℝ) - (cellIndex x k : ℝ)| ≤
      (cellRadius R : ℝ) := by
    dsimp [cellIndex]
    rw [abs_le] at hcoord ⊢
    constructor <;> linarith
  exact_mod_cast habs

theorem latticeEnvelope_nonneg {R : ℝ} (hR : 0 ≤ R) (i j : Lattice) :
    0 ≤ latticeEnvelope R i j := by
  unfold latticeEnvelope
  split_ifs <;> positivity

theorem latticeEnvelope_symm (R : ℝ) (i j : Lattice) :
    latticeEnvelope R i j = latticeEnvelope R j i := by
  simp only [latticeEnvelope, nearCells_symm (i := i) (j := j)]

theorem latticeEnvelope_le {R : ℝ} (hR : 0 ≤ R) (i j : Lattice) :
    latticeEnvelope R i j ≤ R⁻¹ ^ 3 := by
  unfold latticeEnvelope
  split_ifs
  · rfl
  · positivity

theorem sum_latticeEnvelope_le {κ : Type u_1} [Fintype κ] (f : κ → Lattice)
    (hf : Function.Injective f) {R : ℝ} (hR : 1 ≤ R) (i : Lattice) :
    ∑ j, latticeEnvelope R i (f j) ≤ 2197 := by
  classical
  let s := Finset.univ.filter (fun j : κ => f j ∈ nearCells R i)
  have hcard : s.card ≤ (nearCells R i).card :=
    Finset.card_le_card_of_injOn f (by
      intro j hj
      exact (Finset.mem_filter.mp hj).2) hf.injOn
  have hsum : (∑ j, latticeEnvelope R i (f j)) = (s.card : ℝ) * R⁻¹ ^ 3 := by
    simp only [latticeEnvelope, ← Finset.sum_filter, s, Finset.sum_const, nsmul_eq_mul]
  rw [hsum]
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  calc
    _ ≤ ((nearCells R i).card : ℝ) * R⁻¹ ^ 3 := mul_le_mul_of_nonneg_right
      (by exact_mod_cast hcard) (by positivity)
    _ ≤ (2197 * R ^ 3) * R⁻¹ ^ 3 := mul_le_mul_of_nonneg_right
      (card_nearCells_le hR i) (by positivity)
    _ = 2197 := by field_simp

theorem kernel_le_latticeEnvelope (w : ℝ → ℝ) (H R : ℝ)
    (hheight : ∀ r, w r ≤ R⁻¹ ^ 3 * H) (hsupport : ∀ r, R < r → w r = 0)
    (x y : EuclideanSpace ℝ (Fin 3)) :
    w ‖x - y‖ ≤ H * latticeEnvelope R (cellIndex x) (cellIndex y) := by
  by_cases h : cellIndex y ∈ nearCells R (cellIndex x)
  · simpa only [latticeEnvelope, ite_eq_left h, mul_comm H] using hheight ‖x - y‖
  · have hd : R < ‖x - y‖ := lt_of_not_ge (fun hle => h (cellIndex_mem_nearCells hle))
    rw [hsupport _ hd, latticeEnvelope, ite_eq_right h, mul_zero]

theorem summable_mixedEnvelope_terms {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ) (i j : Lattice) :
    Summable (fun n => σ n * latticeEnvelope (R n) i j) := by
  apply hs.of_norm_bounded
  intro n
  have hRp : 0 ≤ R n := le_trans zero_le_one (hR n)
  rw [Real.norm_of_nonneg (mul_nonneg (hσ n) (latticeEnvelope_nonneg hRp i j))]
  have he : latticeEnvelope (R n) i j ≤ 1 :=
    (latticeEnvelope_le hRp i j).trans
      (pow_le_one₀ (inv_nonneg.mpr hRp) (inv_le_one_of_one_le₀ (hR n)))
  simpa using mul_le_mul_of_nonneg_left he (hσ n)

theorem mixedEnvelope_nonneg {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 0 ≤ R n) (i j : Lattice) :
    0 ≤ mixedEnvelope σ R i j :=
  tsum_nonneg (fun n => mul_nonneg (hσ n) (latticeEnvelope_nonneg (hR n) i j))

theorem mixedEnvelope_symm (σ R : ℕ → ℝ) (i j : Lattice) :
    mixedEnvelope σ R i j = mixedEnvelope σ R j i := by
  unfold mixedEnvelope
  congr 1
  funext n
  rw [latticeEnvelope_symm]

theorem sum_mixedEnvelope_le {κ : Type u_1} [Fintype κ] (f : κ → Lattice)
    (hf : Function.Injective f) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ) (i : Lattice) :
    ∑ j, mixedEnvelope σ R i (f j) ≤ 2197 * ∑' n, σ n := by
  have hsum : Summable (fun n => ∑ j, σ n * latticeEnvelope (R n) i (f j)) := by
    apply Summable.of_nonneg_of_le (fun n => Finset.sum_nonneg (fun j _ =>
      mul_nonneg (hσ n) (latticeEnvelope_nonneg (le_trans zero_le_one (hR n)) i (f j)))) _
      (hs.mul_left 2197)
    intro n
    rw [← Finset.mul_sum]
    have hh := mul_le_mul_of_nonneg_left (sum_latticeEnvelope_le f hf (hR n) i) (hσ n)
    nlinarith only [hh]
  unfold mixedEnvelope
  rw [← Summable.tsum_finsetSum (fun j _ => summable_mixedEnvelope_terms hσ hR hs i (f j)),
    ← hs.tsum_mul_left]
  apply hsum.tsum_le_tsum _ (hs.mul_left 2197)
  intro n
  rw [← Finset.mul_sum]
  have hh := mul_le_mul_of_nonneg_left (sum_latticeEnvelope_le f hf (hR n) i) (hσ n)
  nlinarith only [hh]

theorem attraction_le_mixedEnvelope {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (x y : Space) :
    attraction t σ R ‖x - y‖ ≤
      (t * kernelHeight) * mixedEnvelope σ R (cellIndex x) (cellIndex y) := by
  unfold attraction mixedEnvelope
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ ht
  rw [← tsum_mul_left]
  apply (summable_attraction_terms hσ hR hs _).tsum_le_tsum _
    ((summable_mixedEnvelope_terms hσ hR hs _ _).mul_left kernelHeight)
  intro n
  have hh := kernel_le_latticeEnvelope (scaledKernelProfile (R n)) kernelHeight (R n)
    (fun r => by simpa only [kernelHeight, div_eq_mul_inv, one_mul] using
      scaledKernelProfile_le (lt_of_lt_of_le zero_lt_one (hR n)) r)
    (fun r hr => scaledKernelProfile_zero (lt_of_lt_of_le zero_lt_one (hR n)) hr.le) x y
  have hh' := mul_le_mul_of_nonneg_left hh (hσ n)
  nlinarith only [hh']

end
end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.Stability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature
noncomputable section
open scoped ContDiff
open scoped InnerProductSpace

theorem sum_comp_eq_sum_fibres {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (c : ι → κ) (f : κ → ℝ) :
    (∑ i, f (c i)) = ∑ k, (Fintype.card {i // c i = k} : ℝ) * f k := by
  symm
  calc
    _ = ∑ k, ∑ _i : {i // c i = k}, f k := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ∑ k, ∑ i : {i // c i = k}, f (c i) := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      rw [i.property]
    _ = _ := Fintype.sum_fiberwise c (fun i => f (c i))

theorem pairSum_le_cell_quadratic {ι : Type u_1} {κ : Type u_2} [Fintype ι] [LinearOrder ι]
    [Fintype κ] [DecidableEq κ] (c : ι → κ) (J : κ → κ → ℝ) (F : ι → ι → ℝ)
    (hJ : ∀ k l, 0 ≤ J k l) (hsym : ∀ i j, F i j = F j i)
    (hF : ∀ i j, F i j ≤ J (c i) (c j)) :
    pairSum F ≤ (1 / 2 : ℝ) * ∑ k, ∑ l,
      J k l * (Fintype.card {i // c i = k} : ℝ) * (Fintype.card {i // c i = l} : ℝ) := by
  classical
  have hh (i j : ι) : (if i = j then 0 else F i j) ≤ J (c i) (c j) := by
    split_ifs
    · exact hJ _ _
    · exact hF _ _
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hh i j))
  rw [← two_mul_pairSum F hsym] at hs
  have hsum : (∑ i, ∑ j, J (c i) (c j)) = ∑ k, ∑ l,
      J k l * (Fintype.card {i // c i = k} : ℝ) * (Fintype.card {i // c i = l} : ℝ) := by
    calc
      _ = ∑ i, ∑ l, (Fintype.card {j // c j = l} : ℝ) * J (c i) l := by
        apply Finset.sum_congr rfl
        intro i _
        exact sum_comp_eq_sum_fibres c (fun l => J (c i) l)
      _ = ∑ k, (Fintype.card {i // c i = k} : ℝ) *
          (∑ l, (Fintype.card {j // c j = l} : ℝ) * J k l) :=
        sum_comp_eq_sum_fibres c (fun k => ∑ l, (Fintype.card {j // c j = l} : ℝ) * J k l)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
  rw [hsum] at hs
  linarith

theorem physicalProfile_pairSum_lower {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197 * t * kernelHeight * (∑' n, σ n) / 2 ≤ t ^ 2 / 8)
    {ι : Type u_1} [Fintype ι] [LinearOrder ι] (x : ι → Space) :
    -(t ^ 2 / 2) * Fintype.card ι ≤ pairSum (fun i j => physicalProfile t σ R ‖x i - x j‖) := by
  classical
  let s := Finset.univ.image (fun i : ι => cellIndex (x i))
  let c (i : ι) : s := ⟨cellIndex (x i), Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  let J (k l : s) := (t * kernelHeight) * mixedEnvelope σ R k l
  let M := 2197 * t * kernelHeight * (∑' n, σ n)
  have hJ (k l : s) : 0 ≤ J k l := mul_nonneg (mul_nonneg ht kernelHeight_pos.le)
    (mixedEnvelope_nonneg hσ (fun n => le_trans zero_le_one (hR n)) k l)
  have hJsym (k l : s) : J k l = J l k := by simp only [J, mixedEnvelope_symm]
  have hrow (k : s) : ∑ l, J k l ≤ M := by
    have hh := mul_le_mul_of_nonneg_left
      (sum_mixedEnvelope_le (fun l : s => (l : Lattice)) Subtype.val_injective hσ hR hs k)
      (mul_nonneg ht kernelHeight_pos.le)
    simpa only [J, M, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] using hh
  have hcore := core_partition_bound c x t (fun i j hij =>
    dist_lt_one_of_cellIndex_eq (congrArg Subtype.val hij))
  have hattr := pairSum_le_cell_quadratic c J (fun i j => attraction t σ R ‖x i - x j‖)
    hJ (fun i j => by rw [norm_sub_rev]) (fun i j => attraction_le_mixedEnvelope ht hσ hR hs _ _)
  have hb := superstable_algebra J (fun k : s => (Fintype.card {i // c i = k} : ℝ)) M t
    (Fintype.card ι) _ _ hJ hJsym hrow hcore hattr
  have hn : 0 ≤ ∑ k : s, (Fintype.card {i // c i = k} : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hm : 0 ≤ t ^ 2 / 8 - M / 2 := sub_nonneg.mpr hsmall
  have hp := mul_nonneg hm hn
  have heq : pairSum (fun i j => physicalProfile t σ R ‖x i - x j‖) =
      pairSum (fun i j => coreProfile t ‖x i - x j‖) -
      pairSum (fun i j => attraction t σ R ‖x i - x j‖) := by
    simp only [pairSum, physicalProfile, Finset.sum_sub_distrib]
  rw [heq]
  linarith

theorem ereal_coe_sum {ι : Type u_1} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simpa only [Finset.sum_insert hi, EReal.coe_add] using congrArg (fun z => (f i : EReal) + z) ih

theorem coe_pairSum_le_energy (φ : ℝ → ℝ) {N : ℕ} (x : Fin N → Space) :
    ((pairSum (fun i j => φ ‖x i - x j‖) : ℝ) : EReal) ≤ energy φ x := by
  classical
  simp only [pairSum, energy, ereal_coe_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  unfold radialPotential
  split_ifs
  · exact le_top
  · rfl

theorem physicalProfile_stable {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197 * t * kernelHeight * (∑' n, σ n) / 2 ≤ t ^ 2 / 8)
    (N : ℕ) (x : Fin N → Space) :
    ((-(t ^ 2 / 2) * (N : ℝ) : ℝ) : EReal) ≤ energy (physicalProfile t σ R) x := by
  apply le_trans _ (coe_pairSum_le_energy _ x)
  apply EReal.coe_le_coe_iff.mpr
  simpa only [Fintype.card_fin] using physicalProfile_pairSum_lower ht hσ hR hs hsmall x

theorem physicalProfile_superstable {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    {ι : Type u_1} {κ : Type u_2} [Fintype ι] [LinearOrder ι] [Fintype κ] [DecidableEq κ]
    (x : ι → Space) (c : ι → κ) (e : κ → Lattice) (he : Function.Injective e)
    (hc : ∀ i, cellIndex (x i) = e (c i)) :
    (t ^ 2 / 8 - 2197 * t * kernelHeight * (∑' n, σ n) / 2) *
      (∑ k, (Fintype.card {i // c i = k} : ℝ) ^ 2) -
      t ^ 2 / 2 * Fintype.card ι ≤
      pairSum (fun i j => physicalProfile t σ R ‖x i - x j‖) := by
  classical
  let J (k l : κ) := (t * kernelHeight) * mixedEnvelope σ R (e k) (e l)
  let M := 2197 * t * kernelHeight * (∑' n, σ n)
  have hJ (k l : κ) : 0 ≤ J k l := mul_nonneg (mul_nonneg ht kernelHeight_pos.le)
    (mixedEnvelope_nonneg hσ (fun n => le_trans zero_le_one (hR n)) (e k) (e l))
  have hJsym (k l : κ) : J k l = J l k := by simp only [J, mixedEnvelope_symm]
  have hrow (k : κ) : ∑ l, J k l ≤ M := by
    have hh := mul_le_mul_of_nonneg_left (sum_mixedEnvelope_le e he hσ hR hs (e k))
      (mul_nonneg ht kernelHeight_pos.le)
    simpa only [J, M, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] using hh
  have hcore := core_partition_bound c x t (fun i j hij =>
    dist_lt_one_of_cellIndex_eq ((hc i).trans ((congrArg e hij).trans (hc j).symm)))
  have hattr := pairSum_le_cell_quadratic c J (fun i j => attraction t σ R ‖x i - x j‖)
    hJ (fun i j => by rw [norm_sub_rev]) (fun i j => by
      have hh := attraction_le_mixedEnvelope ht hσ hR hs (x i) (x j)
      simpa only [hc, J] using hh)
  have hb := superstable_algebra J (fun k : κ => (Fintype.card {i // c i = k} : ℝ)) M t
    (Fintype.card ι) _ _ hJ hJsym hrow hcore hattr
  simpa only [pairSum, physicalProfile, Finset.sum_sub_distrib] using hb

end
end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.CubeCoercivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature
noncomputable section
open scoped ContDiff
open scoped InnerProductSpace

theorem cellIndex_mem_cubeCells {L : ℝ} {x : Space} (hx : x ∈ cube L) :
    cellIndex x ∈ cubeCells L := by
  classical
  simp only [cubeCells, Fintype.mem_piFinset, Finset.mem_Icc, cellIndex]
  intro k
  constructor
  · apply Int.floor_mono
    have h := (hx k).1
    linarith
  · apply Int.floor_mono
    have h := (hx k).2
    linarith

theorem card_cubeCells_le {L : ℝ} (hL : 0 ≤ L) :
    ((cubeCells L).card : ℝ) ≤ (4 * L + 2) ^ 3 := by
  classical
  let m := (Finset.Icc ⌊-2 * L⌋ ⌊2 * L⌋).card
  have horder : ⌊-2 * L⌋ ≤ ⌊2 * L⌋ + 1 := by
    have hh := Int.floor_mono (show -2 * L ≤ 2 * L by linarith)
    omega
  have hcInt := Int.card_Icc_of_le ⌊-2 * L⌋ ⌊2 * L⌋ horder
  have hcReal : (m : ℝ) = (⌊2 * L⌋ : ℝ) + 1 - (⌊-2 * L⌋ : ℝ) := by
    dsimp only [m]
    exact_mod_cast hcInt
  have hm : (m : ℝ) ≤ 4 * L + 2 := by
    rw [hcReal]
    have hu := Int.floor_le (2 * L)
    have hl := Int.lt_floor_add_one (-2 * L)
    linarith
  have hc : ((cubeCells L).card : ℝ) = (m : ℝ) ^ 3 := by
    simp [cubeCells, Fintype.card_piFinset, m]
  rw [hc]
  exact pow_le_pow_left₀ (Nat.cast_nonneg m) hm 3

theorem physicalProfile_energy_coercive {t L : ℝ} (ht : 0 ≤ t) (hL : 0 ≤ L)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197 * t * kernelHeight * (∑' n, σ n) / 2 ≤ t ^ 2 / 8)
    (N : ℕ) (x : Fin N → Space) (hx : ∀ i, x i ∈ cube L) :
    (((t ^ 2 / 8 - 2197 * t * kernelHeight * (∑' n, σ n) / 2) *
      ((N : ℝ) ^ 2 / (4 * L + 2) ^ 3) - t ^ 2 / 2 * N : ℝ) : EReal) ≤
      energy (physicalProfile t σ R) x := by
  classical
  let κ := (cubeCells L : Type)
  let c (i : Fin N) : κ := ⟨cellIndex (x i), cellIndex_mem_cubeCells (hx i)⟩
  let n (k : κ) : ℝ := Fintype.card {i // c i = k}
  have hsN : (∑ k : κ, n k) = N := by
    have hh := sum_comp_eq_sum_fibres c (fun _ => (1 : ℝ))
    simpa only [n, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] using hh.symm
  have hquad : (N : ℝ) ^ 2 ≤ (Fintype.card κ : ℝ) * ∑ k, n k ^ 2 := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset κ) (fun _ => (1 : ℝ)) n
    simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, hsN] using hh
  have hquad' : (N : ℝ) ^ 2 ≤ (4 * L + 2) ^ 3 * ∑ k, n k ^ 2 := by
    apply hquad.trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    simpa only [κ, Fintype.card_coe] using card_cubeCells_le hL
  have hden : 0 < (4 * L + 2) ^ 3 := by positivity
  have hquot : (N : ℝ) ^ 2 / (4 * L + 2) ^ 3 ≤ ∑ k, n k ^ 2 := by
    apply (div_le_iff₀ hden).mpr
    simpa only [mul_comm] using hquad'
  have hsuper := physicalProfile_superstable ht hσ hR hs x c
    (fun k : κ => (k : Lattice)) Subtype.val_injective (fun _ => rfl)
  have he := coe_pairSum_le_energy (physicalProfile t σ R) x
  apply le_trans _ he
  apply EReal.coe_le_coe_iff.mpr
  have hm := mul_le_mul_of_nonneg_left hquot (sub_nonneg.mpr hsmall)
  simp only [Fintype.card_fin] at hsuper
  exact (sub_le_sub_right hm _).trans hsuper

end

end ContinuumTemperature

end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.CanonicalIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set

namespace ContinuumTemperature

theorem ereal_sum_ne_bot {α : Type u_1} (s : Finset α) (f : α → EReal)
    (hf : ∀ i ∈ s, f i ≠ ⊥) : ∑ i ∈ s, f i ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, EReal.add_ne_bot_iff]
    exact ⟨hf i (Finset.mem_insert_self i s), ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))⟩

theorem measurable_energy {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    (N : ℕ) : Measurable (fun x : Fin N → Space => energy φ x) := by
  classical
  unfold energy
  fun_prop

theorem measurable_boltzmann {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    (β : ℝ) (N : ℕ) : Measurable (fun x : Fin N → Space => boltzmann φ β x) := by
  have hE := measurable_energy hφ N
  exact Measurable.ite (hE (measurableSet_singleton ⊤)) measurable_const
    ((measurable_const.mul hE.ereal_toReal).exp)

theorem boltzmann_nonneg (φ : ℝ → ℝ) (β : ℝ) {N : ℕ} (x : Fin N → Space) :
    0 ≤ boltzmann φ β x := by
  unfold boltzmann
  split_ifs
  · rfl
  · exact (Real.exp_pos _).le

theorem boltzmann_le_of_stable {φ : ℝ → ℝ} {β B : ℝ} (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    {N : ℕ} (x : Fin N → Space) :
    boltzmann φ β x ≤ Real.exp (β * B * N) := by
  unfold boltzmann
  split_ifs with htop
  · exact (Real.exp_pos _).le
  · apply Real.exp_le_exp.mpr
    have he := EReal.toReal_le_toReal (hstable N x) (EReal.coe_ne_bot _) htop
    simp only [EReal.toReal_coe] at he
    nlinarith [mul_le_mul_of_nonneg_left he hβ]

theorem isCompact_cube (L : ℝ) : IsCompact (cube L) := by
  have h := isCompact_pi_infinite (fun _ : Fin 3 => isCompact_Icc (a := -L / 2) (b := L / 2))
  exact (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).isCompact_preimage.mpr h

theorem isCompact_configurations (L : ℝ) (N : ℕ) :
    IsCompact {x : Fin N → Space | ∀ i, x i ∈ cube L} :=
  isCompact_pi_infinite (fun _ => isCompact_cube L)

theorem integrableOn_boltzmann {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B : ℝ} (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (L : ℝ) (N : ℕ) :
    IntegrableOn (fun x : Fin N → Space => boltzmann φ β x)
      {x : Fin N → Space | ∀ i, x i ∈ cube L} := by
  have hK := isCompact_configurations L N
  have : IsFiniteMeasure (volume.restrict {x : Fin N → Space | ∀ i, x i ∈ cube L}) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top (μ := volume)⟩
  apply (integrable_const (Real.exp (β * B * N))).mono'
    (measurable_boltzmann hφ β N).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (boltzmann_nonneg φ β x)]
  exact boltzmann_le_of_stable hβ hstable x

theorem energy_eq_real_of_injective (φ : ℝ → ℝ) {N : ℕ} {x : Fin N → Space}
    (hx : Function.Injective x) :
    energy φ x = ((∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i < j),
      φ ‖x i - x j‖ : ℝ) : EReal) := by
  classical
  unfold energy
  simp only [ereal_coe_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j hj
  have hij : i ≠ j := ne_of_lt (Finset.mem_filter.mp hj).2
  exact ite_eq_right (sub_ne_zero.mpr (hx.ne hij))

theorem boltzmann_pos_of_injective (φ : ℝ → ℝ) (β : ℝ) {N : ℕ}
    {x : Fin N → Space} (hx : Function.Injective x) : 0 < boltzmann φ β x := by
  unfold boltzmann
  rw [ite_eq_right (by rw [energy_eq_real_of_injective φ hx]; exact EReal.coe_ne_top _)]
  exact Real.exp_pos _

theorem isOpen_openConfigurations (L : ℝ) (N : ℕ) :
    IsOpen (openConfigurations L N) := by
  have hbox : IsOpen {x : Fin N → Space | ∀ i k, x i k ∈ Ioo (-L / 2) (L / 2)} := by
    simp only [ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro k
    exact isOpen_Ioo.preimage ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) k).comp
      (continuous_apply i))
  have hinj : IsOpen {x : Fin N → Space | Function.Injective x} := by
    have heq : {x : Fin N → Space | Function.Injective x} =
        ⋂ i, ⋂ j, ⋂ (_ : i ≠ j), {x | x i ≠ x j} := by
      ext x
      simp only [mem_ofPred_eq, mem_iInter]
      exact ⟨fun h i j hij => h.ne hij, fun h i j hij => by_contra fun hij' => h i j hij' hij⟩
    rw [heq]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro _
    exact (isClosed_eq (continuous_apply i) (continuous_apply j)).isOpen_compl
  exact hbox.inter hinj

theorem openConfigurations_nonempty {L : ℝ} (hL : 0 < L) (N : ℕ) :
    (openConfigurations L N).Nonempty := by
  let c : ℝ := L / (4 * ((N : ℝ) + 1))
  have hc : 0 < c := by dsimp [c]; positivity
  let x : Fin N → Space := fun i => WithLp.toLp 2 (fun _ : Fin 3 => (i : ℝ) * c)
  refine ⟨x, ?_, ?_⟩
  · intro i k
    change -L / 2 < (i : ℝ) * c ∧ (i : ℝ) * c < L / 2
    have hi : (i : ℝ) < N := by exact_mod_cast i.isLt
    have hinonneg : 0 ≤ (i : ℝ) := by positivity
    constructor
    · nlinarith [mul_nonneg hinonneg hc.le]
    · dsimp [c]
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
      nlinarith [mul_pos hL (by exact_mod_cast Nat.zero_lt_succ N : 0 < (N : ℝ) + 1)]
  · intro i j he
    have hij := congrArg (fun y : Space => y 0) he
    change (i : ℝ) * c = (j : ℝ) * c at hij
    have hij' := mul_right_cancel₀ hc.ne' hij
    exact Fin.ext (by exact_mod_cast hij')

theorem partition_pos {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {β B L : ℝ} (hβ : 0 ≤ β) (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (N : ℕ) : 0 < partition φ β L N := by
  classical
  unfold partition
  split_ifs
  · norm_num
  · apply mul_pos (by positivity)
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (ae_of_all _ (boltzmann_nonneg φ β)) (integrableOn_boltzmann hφ hβ hstable L N)]
    apply lt_of_lt_of_le ((isOpen_openConfigurations L N).measure_pos volume
      (openConfigurations_nonempty hL N))
    apply measure_mono
    intro x hx
    exact ⟨(boltzmann_pos_of_injective φ β hx.2).ne',
      fun i k => ⟨(hx.1 i k).1.le, (hx.1 i k).2.le⟩⟩

theorem volume_cube (L : ℝ) : volume (cube L) = (ENNReal.ofReal L) ^ 3 := by
  have heq : cube L = (@WithLp.ofLp 2 (Fin 3 → ℝ)) ⁻¹'
      (Set.pi Set.univ (fun _ : Fin 3 => Icc (-L / 2) (L / 2))) := by
    ext x
    simp only [cube, mem_preimage, mem_ofPred_eq, Set.mem_pi, mem_univ, forall_const]
  rw [heq, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    ((MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc)).nullMeasurableSet)]
  change (Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))) _ = _
  rw [Measure.pi_pi]
  simp only [Real.volume_Icc]
  have ha : L / 2 - -L / 2 = L := by ring
  simp [ha]

theorem volume_configurations (L : ℝ) (N : ℕ) :
    volume {x : Fin N → Space | ∀ i, x i ∈ cube L} = (ENNReal.ofReal L) ^ (3 * N) := by
  have heq : {x : Fin N → Space | ∀ i, x i ∈ cube L} =
      Set.pi Set.univ (fun _ : Fin N => cube L) := by ext x; simp
  rw [heq]
  change (Measure.pi (fun _ : Fin N => (volume : Measure Space))) _ = _
  rw [Measure.pi_pi]
  simp only [volume_cube, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]

theorem partition_nonneg (φ : ℝ → ℝ) (β L : ℝ) (N : ℕ) :
    0 ≤ partition φ β L N := by
  unfold partition
  split_ifs
  · norm_num
  · apply mul_nonneg (by positivity)
    exact integral_nonneg (boltzmann_nonneg φ β)

theorem partition_le_exp_of_stable {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B L : ℝ} (hβ : 0 ≤ β) (hL : 0 ≤ L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) (N : ℕ) :
    partition φ β L N ≤ (L ^ 3 * Real.exp (β * B)) ^ N / (N.factorial : ℝ) := by
  by_cases hN : N = 0
  · simp [hN, partition]
  · have : IsFiniteMeasure (volume.restrict {x : Fin N → Space | ∀ i, x i ∈ cube L}) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using
        (isCompact_configurations L N).measure_lt_top (μ := volume)⟩
    have hi := integral_mono_ae (integrableOn_boltzmann hφ hβ hstable L N)
      (integrable_const (Real.exp (β * B * N)))
      (ae_of_all _ (boltzmann_le_of_stable hβ hstable (N := N)))
    rw [integral_const] at hi
    simp only [Measure.real, Measure.restrict_apply_univ, volume_configurations,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal hL, smul_eq_mul] at hi
    unfold partition
    rw [ite_eq_right hN]
    have hfac : 0 ≤ (1 / (N.factorial : ℝ)) := by positivity
    apply (mul_le_mul_of_nonneg_left hi hfac).trans_eq
    rw [show β * B * (N : ℝ) = (N : ℝ) * (β * B) by ring, Real.exp_nat_mul,
      mul_pow, pow_mul]
    ring

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GrandPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem summable_grandPartition {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B L : ℝ} (hβ : 0 ≤ β) (hL : 0 ≤ L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) (t h : ℝ) :
    Summable (fun N : ℕ => Real.exp (t * h * N) * partition φ β L N) := by
  apply Summable.of_nonneg_of_le (fun N => mul_nonneg (Real.exp_pos _).le
    (partition_nonneg φ β L N)) _
    (Real.summable_pow_div_factorial (Real.exp (t * h) * (L ^ 3 * Real.exp (β * B))))
  intro N
  have hb := mul_le_mul_of_nonneg_left (partition_le_exp_of_stable hφ hβ hL hstable N)
    (Real.exp_pos (t * h * N)).le
  apply hb.trans_eq
  rw [show t * h * (N : ℝ) = (N : ℝ) * (t * h) by ring, Real.exp_nat_mul, mul_pow]
  ring

theorem grandPartition_le_exp {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B L : ℝ} (hβ : 0 ≤ β) (hL : 0 ≤ L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) (t h : ℝ) :
    grandPartition φ t β h L ≤ Real.exp (L ^ 3 * Real.exp (t * h + β * B)) := by
  let z := L ^ 3 * Real.exp (t * h + β * B)
  have hz : HasSum (fun N : ℕ => z ^ N / (N.factorial : ℝ)) (Real.exp z) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp z
  unfold grandPartition
  rw [← hz.tsum_eq]
  apply (summable_grandPartition hφ hβ hL hstable t h).tsum_le_tsum _ hz.summable
  intro N
  apply (mul_le_mul_of_nonneg_left (partition_le_exp_of_stable hφ hβ hL hstable N)
    (Real.exp_pos _).le).trans_eq
  dsimp [z]
  rw [show t * h * (N : ℝ) = (N : ℝ) * (t * h) by ring, Real.exp_nat_mul,
    Real.exp_add, mul_pow, mul_pow]
  ring

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.FiniteBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem log_factorial_lower (N : ℕ) :
    (N : ℝ) * Real.log N - N ≤ Real.log (N.factorial : ℝ) := by
  by_cases hN : N = 0
  · simp [hN]
  · have hpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    have hf : (0 : ℝ) < N.factorial := Nat.cast_pos.mpr (Nat.factorial_pos N)
    have hh := Real.pow_div_factorial_le_exp (N : ℝ) hpos.le N
    have hl := Real.log_le_log (div_pos (pow_pos hpos _) hf) hh
    rw [Real.log_div (pow_ne_zero _ hpos.ne') hf.ne', Real.log_pow, Real.log_exp] at hl
    linarith

theorem boltzmann_le_of_energy_lower {φ : ℝ → ℝ} {β E : ℝ} (hβ : 0 ≤ β)
    {N : ℕ} {x : Fin N → Space} (hE : (E : EReal) ≤ energy φ x) :
    boltzmann φ β x ≤ Real.exp (-β * E) := by
  unfold boltzmann
  split_ifs with htop
  · exact (Real.exp_pos _).le
  · apply Real.exp_le_exp.mpr
    have he := EReal.toReal_le_toReal hE (EReal.coe_ne_bot _) htop
    simp only [EReal.toReal_coe] at he
    exact mul_le_mul_of_nonpos_left he (neg_nonpos.mpr hβ)

theorem partition_le_factorial_of_energy_bound {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B L E : ℝ} (hβ : 0 ≤ β) (hL : 0 ≤ L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) {N : ℕ} (hN : N ≠ 0)
    (hE : ∀ x : Fin N → Space, (∀ i, x i ∈ cube L) → (E : EReal) ≤ energy φ x) :
    partition φ β L N ≤ (L ^ 3) ^ N / (N.factorial : ℝ) * Real.exp (-β * E) := by
  let S := {x : Fin N → Space | ∀ i, x i ∈ cube L}
  have hS : MeasurableSet S := (isCompact_configurations L N).measurableSet
  have hfin : IsFiniteMeasure (volume.restrict S) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (isCompact_configurations L N).measure_lt_top (μ := volume)⟩
  have hh : ∀ᵐ x ∂volume.restrict S, boltzmann φ β x ≤ Real.exp (-β * E) := by
    apply (ae_restrict_iff' hS).mpr
    exact ae_of_all _ (fun x hx => boltzmann_le_of_energy_lower hβ (hE x hx))
  have hi := integral_mono_ae (integrableOn_boltzmann hφ hβ hstable L N)
    (integrable_const (Real.exp (-β * E))) hh
  have hc : (∫ x in S, Real.exp (-β * E)) = L ^ (3 * N) * Real.exp (-β * E) := by
    rw [setIntegral_const, Measure.real, volume_configurations, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hL, smul_eq_mul]
  rw [hc] at hi
  unfold partition
  rw [ite_eq_right hN]
  calc
    _ ≤ (1 / (N.factorial : ℝ)) * (L ^ (3 * N) * Real.exp (-β * E)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by rw [pow_mul]; ring

theorem neg_log_partition_lower {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B L E : ℝ} (hβ : 0 ≤ β) (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) {N : ℕ} (hN : N ≠ 0)
    (hE : ∀ x : Fin N → Space, (∀ i, x i ∈ cube L) → (E : EReal) ≤ energy φ x) :
    β * E + N * Real.log ((N : ℝ) / L ^ 3) - N ≤ -Real.log (partition φ β L N) := by
  have hnpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hfp : (0 : ℝ) < N.factorial := Nat.cast_pos.mpr (Nat.factorial_pos N)
  have hLp : 0 < L ^ 3 := pow_pos hL _
  have hZ := partition_pos hφ hβ hL hstable N
  have hu := partition_le_factorial_of_energy_bound hφ hβ hL.le hstable hN hE
  have hl := Real.log_le_log hZ hu
  rw [Real.log_mul (div_pos (pow_pos hLp _) hfp).ne' (Real.exp_pos _).ne',
    Real.log_div (pow_pos hLp _).ne' hfp.ne', Real.log_pow, Real.log_exp] at hl
  rw [Real.log_div hnpos.ne' hLp.ne']
  have hf := log_factorial_lower N
  nlinarith

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PairEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem ereal_sum_eq_top_of_exists {α : Type u_1} (s : Finset α) (f : α → EReal)
    (hf : ∀ i ∈ s, f i ≠ ⊥) (ht : ∃ i ∈ s, f i = ⊤) : ∑ i ∈ s, f i = ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at ht
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    obtain ⟨j, hj, hjt⟩ := ht
    rcases Finset.mem_insert.mp hj with rfl | hj
    · rw [hjt]
      exact EReal.top_add_of_ne_bot (ereal_sum_ne_bot s f
        (fun k hk => hf k (Finset.mem_insert_of_mem hk)))
    · rw [ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)) ⟨j, hj, hjt⟩]
      exact EReal.add_top_of_ne_bot (hf i (Finset.mem_insert_self _ _))

theorem energy_eq_top_iff (φ : ℝ → ℝ) {N : ℕ} (x : Fin N → Space) :
    energy φ x = ⊤ ↔ ¬Function.Injective x := by
  constructor
  · intro he hx
    rw [energy_eq_real_of_injective φ hx] at he
    exact EReal.coe_ne_top _ he
  · intro hx
    have hh : ∃ i j, i ≠ j ∧ x i = x j := by
      by_contra hc
      apply hx
      intro i j heq
      by_contra hne
      exact hc ⟨i, j, hne, heq⟩
    obtain ⟨i, j, hij, he⟩ := hh
    have hpair {i j : Fin N} (hij : i < j) (he : x i = x j) : energy φ x = ⊤ := by
      apply ereal_sum_eq_top_of_exists _ _
        (fun i _ => ereal_sum_ne_bot _ _ (fun j _ => radialPotential_ne_bot _ _))
      refine ⟨i, Finset.mem_univ _, ?_⟩
      apply ereal_sum_eq_top_of_exists _ _ (fun j _ => radialPotential_ne_bot _ _)
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, by
        simp [he, radialPotential]⟩
    rcases lt_or_gt_of_ne hij with h | h
    · exact hpair h he
    · exact hpair h he.symm

theorem realPairEnergy_eq_ordered (φ : ℝ → ℝ) {ι : Type u_1} [Fintype ι] [LinearOrder ι]
    (x : ι → Space) :
    realPairEnergy φ x = ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), φ ‖x i - x j‖ := by
  classical
  have hsplit (i j : ι) : (if i = j then 0 else φ ‖x i - x j‖) =
      (if i < j then φ ‖x i - x j‖ else 0) +
      (if j < i then φ ‖x j - x i‖ else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · subst j; simp
    · simp [h, ne_of_gt h, not_lt_of_ge h.le, norm_sub_rev]
  calc
    realPairEnergy φ x = (1/2 : ℝ) * ∑ i, ∑ j,
        ((if i < j then φ ‖x i - x j‖ else 0) +
          (if j < i then φ ‖x j - x i‖ else 0)) := by
      unfold realPairEnergy
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i = j
      · simpa only [ite_eq_left hij] using hsplit i j
      · simpa only [ite_eq_right hij] using hsplit i j
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j : ι => if j < i then φ ‖x j - x i‖ else 0)]
      simp only [Finset.sum_filter]
      ring

theorem boltzmann_eq_symmetricWeight (φ : ℝ → ℝ) (β : ℝ)
    {N : ℕ} (x : Fin N → Space) : boltzmann φ β x = symmetricWeight φ β x := by
  classical
  by_cases hx : Function.Injective x
  · simp only [boltzmann, energy_eq_real_of_injective φ hx, EReal.coe_ne_top,
      ite_false, EReal.toReal_coe, symmetricWeight, ite_eq_left hx, realPairEnergy_eq_ordered]
  · simp only [boltzmann, (energy_eq_top_iff φ x).2 hx, ite_true, symmetricWeight, ite_eq_right hx]

theorem realPairEnergy_relabel (φ : ℝ → ℝ) {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (x : κ → Space) : realPairEnergy φ (x ∘ e) = realPairEnergy φ x := by
  classical
  unfold realPairEnergy
  simp only [Function.comp_apply, ← e.injective.eq_iff]
  congr 1
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro i _
  exact Equiv.sum_comp e (fun j => if e i = j then 0 else φ ‖x (e i) - x j‖)

theorem symmetricWeight_relabel (φ : ℝ → ℝ) (β : ℝ) {ι : Type u_1} {κ : Type u_2}
    [Fintype ι] [Fintype κ] (e : ι ≃ κ) (x : κ → Space) :
    symmetricWeight φ β (x ∘ e) = symmetricWeight φ β x := by
  classical
  have hh : Function.Injective (x ∘ e) ↔ Function.Injective x :=
    by
      constructor
      · intro hx i j hij
        obtain ⟨i, rfl⟩ := e.surjective i
        obtain ⟨j, rfl⟩ := e.surjective j
        exact congrArg e (hx hij)
      · exact fun hx => hx.comp e.injective
  simp only [symmetricWeight, hh, realPairEnergy_relabel]

theorem symmetric_matrix_split {ι : Type u_1} [Fintype ι] (p : ι → Prop)
    [DecidablePred p] (F : ι → ι → ℝ) (hsym : ∀ i j, F i j = F j i) :
    (∑ i, ∑ j, F i j) =
      (∑ i : {i // p i}, ∑ j : {j // p j}, F i j) +
      (∑ i : {i // ¬p i}, ∑ j : {j // ¬p j}, F i j) +
      2 * (∑ i : {i // p i}, ∑ j : {j // ¬p j}, F i j) := by
  classical
  have houter := Fintype.sum_subtype_add_sum_subtype p (fun i => ∑ j, F i j)
  have hinner (i : ι) := Fintype.sum_subtype_add_sum_subtype p (F i)
  rw [← houter]
  simp_rw [← hinner, Finset.sum_add_distrib]
  have hh : (∑ i : {i // ¬p i}, ∑ j : {j // p j}, F i j) =
      ∑ i : {i // p i}, ∑ j : {j // ¬p j}, F i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact hsym _ _
  rw [hh]
  ring

theorem realPairEnergy_split (φ : ℝ → ℝ) {ι : Type u_1} [Fintype ι]
    (p : ι → Prop) [DecidablePred p] (x : ι → Space) :
    realPairEnergy φ x =
      realPairEnergy φ (fun i : {i // p i} => x i) +
      realPairEnergy φ (fun i : {i // ¬p i} => x i) +
      ∑ i : {i // p i}, ∑ j : {j // ¬p j}, φ ‖x i - x j‖ := by
  classical
  have heq := symmetric_matrix_split p (fun i j => if i = j then 0 else φ ‖x i - x j‖)
    (fun i j => by by_cases h : i = j <;> simp [h, eq_comm, norm_sub_rev])
  have hcross (i : {i // p i}) (j : {i // ¬p i}) : (i : ι) ≠ j := by
    intro h
    exact j.property (h ▸ i.property)
  have hself (a b : {i // p i}) : ((a : ι) = b) ↔ a = b := Subtype.coe_inj
  have hself' (a b : {i // ¬p i}) : ((a : ι) = b) ↔ a = b := Subtype.coe_inj
  unfold realPairEnergy
  rw [heq]
  simp only [hself, hself', hcross, ite_false]
  ring

theorem symmetricWeight_nonneg (φ : ℝ → ℝ) (β : ℝ) {ι : Type u_1} [Fintype ι]
    (x : ι → Space) : 0 ≤ symmetricWeight φ β x := by
  unfold symmetricWeight
  split_ifs
  · positivity
  · rfl

theorem symmetricWeight_separated (φ : ℝ → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    {ι : Type u_1} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    {A B : Set Space} (hd : Disjoint A B)
    (hφ : ∀ a ∈ A, ∀ b ∈ B, φ ‖a - b‖ ≤ 0)
    (x : ι → Space) (hA : ∀ i, p i → x i ∈ A) (hB : ∀ i, ¬p i → x i ∈ B) :
    symmetricWeight φ β (fun i : {i // p i} => x i) *
      symmetricWeight φ β (fun i : {i // ¬p i} => x i) ≤ symmetricWeight φ β x := by
  classical
  by_cases ha : Function.Injective (fun i : {i // p i} => x i)
  swap
  · simpa only [symmetricWeight, ite_eq_right ha, zero_mul] using symmetricWeight_nonneg φ β x
  by_cases hb : Function.Injective (fun i : {i // ¬p i} => x i)
  swap
  · simpa only [symmetricWeight, ite_eq_right hb, mul_zero] using symmetricWeight_nonneg φ β x
  have hx : Function.Injective x := by
    intro i j hij
    by_cases hi : p i <;> by_cases hj : p j
    · exact congrArg Subtype.val (ha (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) hij)
    · exact False.elim (Set.disjoint_left.mp hd (hA i hi) (hij ▸ hB j hj))
    · exact False.elim (Set.disjoint_left.mp hd (hA j hj) (hij ▸ hB i hi))
    · exact congrArg Subtype.val (hb (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) hij)
  have hc : (∑ i : {i // p i}, ∑ j : {j // ¬p j}, φ ‖x i - x j‖) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    exact Finset.sum_nonpos (fun j _ => hφ _ (hA i i.property) _ (hB j j.property))
  simp only [symmetricWeight, ite_eq_left ha, ite_eq_left hb, ite_eq_left hx, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [realPairEnergy_split φ p x]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hβ hc]

theorem realPairEnergy_translate (φ : ℝ → ℝ) {ι : Type u_1} [Fintype ι]
    (x : ι → Space) (v : Space) :
    realPairEnergy φ (fun i => x i + v) = realPairEnergy φ x := by
  classical
  simp only [realPairEnergy, add_sub_add_right_eq_sub]

theorem symmetricWeight_translate (φ : ℝ → ℝ) (β : ℝ) {ι : Type u_1} [Fintype ι]
    (x : ι → Space) (v : Space) :
    symmetricWeight φ β (fun i => x i + v) = symmetricWeight φ β x := by
  classical
  have hh : Function.Injective (fun i => x i + v) ↔ Function.Injective x := by
    simp only [Function.Injective, add_left_inj]
  simp only [symmetricWeight, hh, realPairEnergy_translate]

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.Assignments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

section Assignments
variable {X : Type u_1} [MeasurableSpace X] {ι : Type u_2} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem measurableSet_assignmentRegion {B : ι → Set X} (hB : ∀ i, MeasurableSet (B i))
    (e : Equiv.Perm ι) : MeasurableSet (assignmentRegion B e) := by
  convert MeasurableSet.iInter (fun i => (hB (e i)).preimage (measurable_pi_apply i)) using 1
  ext x
  simp [assignmentRegion]

omit [MeasurableSpace X] in
theorem assignmentRegion_pairwiseDisjoint {B : ι → Set X}
    (hB : Pairwise (fun i j => Disjoint (B i) (B j))) :
    Pairwise (fun e f : Equiv.Perm ι => Disjoint (assignmentRegion B e) (assignmentRegion B f)) := by
  intro e f hef
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hne : ∃ i, e i ≠ f i := by
    by_contra! h
    exact hef (Equiv.ext h)
  obtain ⟨i, hi⟩ := hne
  exact Set.disjoint_left.mp (hB hi) (hx i) (hy i)

theorem measure_assignment_union (μ : Measure X) [SigmaFinite μ] {B : ι → Set X}
    (hB : ∀ i, MeasurableSet (B i))
    (hd : Pairwise (fun i j => Disjoint (B i) (B j))) :
    (Measure.pi (fun _ : ι => μ)) (⋃ e : Equiv.Perm ι, assignmentRegion B e) =
      (Fintype.card ι).factorial * ∏ i, μ (B i) := by
  rw [measure_iUnion (assignmentRegion_pairwiseDisjoint hd)
    (measurableSet_assignmentRegion hB), tsum_fintype]
  have hh (e : Equiv.Perm ι) :
      (Measure.pi (fun _ : ι => μ)) (assignmentRegion B e) = ∏ i, μ (B i) := by
    have heq : assignmentRegion B e = Set.univ.pi (fun i => B (e i)) := by
      ext x
      simp [assignmentRegion]
    rw [heq, Measure.pi_pi, Equiv.prod_comp e (fun i => μ (B i))]
  simp_rw [hh]
  simp [Fintype.card_perm]

theorem integral_lower_of_disjoint_assignments (μ : Measure X) [SigmaFinite μ]
    {B : ι → Set X} (hB : ∀ i, MeasurableSet (B i))
    (hd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hfinite : ∀ i, μ (B i) ≠ ⊤) {Ω : Set (ι → X)} {F : (ι → X) → ℝ}
    (hF : IntegrableOn F Ω (Measure.pi (fun _ : ι => μ)))
    (hF0 : ∀ x, 0 ≤ F x) {c : ℝ}
    (hinc : ∀ e, assignmentRegion B e ⊆ Ω)
    (hbound : ∀ e, ∀ x ∈ assignmentRegion B e, c ≤ F x) :
    (Fintype.card ι).factorial * (∏ i, (μ (B i)).toReal) * c ≤
      ∫ x in Ω, F x ∂(Measure.pi (fun _ : ι => μ)) := by
  let S := ⋃ e : Equiv.Perm ι, assignmentRegion B e
  have hS : MeasurableSet S := MeasurableSet.iUnion (measurableSet_assignmentRegion hB)
  have hsub : S ⊆ Ω := iUnion_subset hinc
  have hmass := measure_assignment_union μ hB hd
  have hSfin : (Measure.pi (fun _ : ι => μ)) S ≠ ⊤ := by
    rw [hmass]
    exact ENNReal.mul_ne_top (by simp) (ENNReal.prod_ne_top (fun i _ => hfinite i))
  have hconst : IntegrableOn (fun _ : ι → X => c) S (Measure.pi (fun _ : ι => μ)) :=
    integrableOn_const hSfin
  have hle : (∫ x in S, c ∂(Measure.pi (fun _ : ι => μ))) ≤
      ∫ x in S, F x ∂(Measure.pi (fun _ : ι => μ)) := by
    apply setIntegral_mono_on hconst (hF.mono_set hsub) hS
    intro x hx
    obtain ⟨e, he⟩ := mem_iUnion.mp hx
    exact hbound e x he
  have hle' := setIntegral_mono_set hF (Filter.Eventually.of_forall hF0)
    (Filter.Eventually.of_forall hsub)
  have hval : (∫ x in S, c ∂(Measure.pi (fun _ : ι => μ))) =
      (Fintype.card ι).factorial * (∏ i, (μ (B i)).toReal) * c := by
    rw [setIntegral_const, Measure.real, hmass, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_prod, smul_eq_mul]
  rw [hval] at hle
  exact hle.trans hle'

omit [DecidableEq ι] in

theorem setIntegral_coordinatePerm (μ : Measure X) [SigmaFinite μ]
    (e : Equiv.Perm ι) (S : Set (ι → X)) (F : (ι → X) → ℝ)
    (hsym : ∀ x, F (x ∘ e) = F x) :
    (∫ x in {x | (x ∘ e) ∈ S}, F x ∂(Measure.pi (fun _ : ι => μ))) =
      ∫ x in S, F x ∂(Measure.pi (fun _ : ι => μ)) := by
  let p : (ι → X) ≃ᵐ (ι → X) := MeasurableEquiv.piCongrLeft (fun _ : ι => X) e.symm
  have hpx (x : ι → X) : p x = x ∘ e := by
    ext i
    simpa only [p, Equiv.symm_apply_apply, Function.comp_apply] using
      (MeasurableEquiv.piCongrLeft_apply_apply e.symm (β := fun _ : ι => X) x (e i))
  have hp : MeasurePreserving p (Measure.pi (fun _ : ι => μ))
      (Measure.pi (fun _ : ι => μ)) := measurePreserving_piCongrLeft (fun _ : ι => μ) e.symm
  have heq := hp.setIntegral_preimage_emb p.measurableEmbedding F S
  simpa only [hpx, hsym, Set.preimage] using heq

theorem measurableSet_binaryRegion {A B : Set X} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (s : Finset ι) : MeasurableSet (binaryRegion A B s) := by
  have hh (i : ι) : MeasurableSet ((fun x : ι → X => x i) ⁻¹' (if i ∈ s then A else B)) := by
    by_cases hi : i ∈ s
    · simpa only [ite_eq_left hi] using hA.preimage (measurable_pi_apply i)
    · simpa only [ite_eq_right hi] using hB.preimage (measurable_pi_apply i)
  convert MeasurableSet.iInter hh using 1
  ext x
  simp only [binaryRegion, mem_ofPred_eq, mem_iInter, mem_preimage]
  apply forall_congr'
  intro i
  split_ifs <;> rfl

omit [MeasurableSpace X] [Fintype ι] in
theorem binaryRegion_pairwiseDisjoint {A B : Set X} (hd : Disjoint A B) :
    Pairwise (fun s t : Finset ι => Disjoint (binaryRegion A B s) (binaryRegion A B t)) := by
  intro s t hst
  apply Set.disjoint_left.mpr
  intro x hx hy
  apply hst
  ext i
  constructor
  · intro hi
    by_contra ht
    exact Set.disjoint_left.mp hd (by simpa only [ite_eq_left hi] using hx i)
      (by simpa only [ite_eq_right ht] using hy i)
  · intro hi
    by_contra hs
    exact Set.disjoint_left.mp hd (by simpa only [ite_eq_left hi] using hy i)
      (by simpa only [ite_eq_right hs] using hx i)

theorem setIntegral_binaryRegion_eq (μ : Measure X) [SigmaFinite μ]
    {A B : Set X} {s t : Finset ι} (hst : s.card = t.card) (F : (ι → X) → ℝ)
    (hsym : ∀ (e : Equiv.Perm ι) x, F (x ∘ e) = F x) :
    (∫ x in binaryRegion A B s, F x ∂(Measure.pi (fun _ : ι => μ))) =
      ∫ x in binaryRegion A B t, F x ∂(Measure.pi (fun _ : ι => μ)) := by
  obtain ⟨e, he⟩ := Equiv.Perm.exists_map_finset_eq s t hst
  have hmem (i : ι) : e i ∈ t ↔ i ∈ s := by
    rw [← he]
    simp only [Finset.mem_map, Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨j, hj, hji⟩
      exact e.injective hji ▸ hj
    · exact fun hi => ⟨i, hi, rfl⟩
  have hpre : {x : ι → X | (x ∘ e) ∈ binaryRegion A B s} = binaryRegion A B t := by
    ext x
    change (∀ i, if i ∈ s then x (e i) ∈ A else x (e i) ∈ B) ↔
      (∀ i, if i ∈ t then x i ∈ A else x i ∈ B)
    simp_rw [← hmem]
    constructor
    · intro hh j
      obtain ⟨i, rfl⟩ := e.surjective j
      exact hh i
    · intro hh i
      exact hh (e i)
  have hh := setIntegral_coordinatePerm μ e (binaryRegion A B s) F (hsym e)
  rw [hpre] at hh
  exact hh.symm

theorem integral_lower_binary_assignments (μ : Measure X) [SigmaFinite μ]
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B)
    (s : Finset ι) {Ω : Set (ι → X)} {F : (ι → X) → ℝ}
    (hF : IntegrableOn F Ω (Measure.pi (fun _ : ι => μ)))
    (hF0 : ∀ x, 0 ≤ F x)
    (hsym : ∀ (e : Equiv.Perm ι) x, F (x ∘ e) = F x)
    (hinc : ∀ t : Finset ι, t.card = s.card → binaryRegion A B t ⊆ Ω) :
    (Fintype.card ι).choose s.card *
        (∫ x in binaryRegion A B s, F x ∂(Measure.pi (fun _ : ι => μ))) ≤
      ∫ x in Ω, F x ∂(Measure.pi (fun _ : ι => μ)) := by
  classical
  let T := (Finset.univ : Finset ι).powersetCard s.card
  have hcard (t : Finset ι) (ht : t ∈ T) : t.card = s.card := (Finset.mem_powersetCard.mp ht).2
  have hsub : (⋃ t ∈ T, binaryRegion A B t) ⊆ Ω := by
    intro x hx
    obtain ⟨t, ht, hx⟩ := mem_iUnion₂.mp hx
    exact hinc t (hcard t ht) hx
  have hh := integral_biUnion_finset T (fun t _ => measurableSet_binaryRegion hA hB t)
    (fun _ _ _ _ hne => binaryRegion_pairwiseDisjoint hd hne)
    (fun t ht => hF.mono_set (hinc t (hcard t ht)))
  have hEq : (∫ x in ⋃ t ∈ T, binaryRegion A B t, F x ∂(Measure.pi (fun _ : ι => μ))) =
      (Fintype.card ι).choose s.card *
        (∫ x in binaryRegion A B s, F x ∂(Measure.pi (fun _ : ι => μ))) := by
    rw [hh]
    calc
      _ = ∑ _t ∈ T, ∫ x in binaryRegion A B s, F x ∂(Measure.pi (fun _ : ι => μ)) := by
        apply Finset.sum_congr rfl
        intro t ht
        exact setIntegral_binaryRegion_eq μ (hcard t ht) F hsym
      _ = _ := by simp [T]
  rw [← hEq]
  exact setIntegral_mono_set hF (Filter.Eventually.of_forall hF0)
    (Filter.Eventually.of_forall hsub)

theorem setIntegral_binary_product (μ : Measure X) [SigmaFinite μ]
    (A B : Set X) (s : Finset ι)
    (f : ({i : ι // i ∈ s} → X) → ℝ) (g : ({i : ι // i ∉ s} → X) → ℝ) :
    (∫ x in binaryRegion A B s,
      f (fun i : {i : ι // i ∈ s} => x i) * g (fun i : {i : ι // i ∉ s} => x i)
      ∂(Measure.pi (fun _ : ι => μ))) =
    (∫ x in {x : {i : ι // i ∈ s} → X | ∀ i, x i ∈ A}, f x ∂(Measure.pi (fun _ : {i : ι // i ∈ s} => μ))) *
    (∫ x in {x : {i : ι // i ∉ s} → X | ∀ i, x i ∈ B}, g x
      ∂(Measure.pi (fun _ : {i : ι // i ∉ s} => μ))) := by
  let p := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => X) (fun i => i ∈ s)
  let SA := {x : {i : ι // i ∈ s} → X | ∀ i, x i ∈ A}
  let SB := {x : {i : ι // i ∉ s} → X | ∀ i, x i ∈ B}
  have hp := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) (fun i => i ∈ s)
  have hfi : Subtype.fintype (fun i : ι => i ∈ s) = Finset.Subtype.fintype s :=
    Subsingleton.elim _ _
  rw [hfi] at hp
  have hpre : p ⁻¹' (SA ×ˢ SB) = binaryRegion A B s := by
    ext x
    change ((∀ i : {i : ι // i ∈ s}, x i ∈ A) ∧ (∀ i : {i : ι // i ∉ s}, x i ∈ B)) ↔
      (∀ i, if i ∈ s then x i ∈ A else x i ∈ B)
    constructor
    · rintro ⟨ha, hb⟩ i
      split_ifs with hi
      · exact ha ⟨i, hi⟩
      · exact hb ⟨i, hi⟩
    · intro hh
      constructor
      · intro i
        simpa only [ite_eq_left i.property] using hh i
      · intro i
        simpa only [ite_eq_right i.property] using hh i
  have heq := hp.setIntegral_preimage_emb p.measurableEmbedding
    (fun z => f z.1 * g z.2) (SA ×ˢ SB)
  rw [hpre, setIntegral_prod_mul] at heq
  exact heq

theorem integrableOn_binary_product (μ : Measure X) [SigmaFinite μ]
    (A B : Set X) (s : Finset ι)
    {f : ({i : ι // i ∈ s} → X) → ℝ} {g : ({i : ι // i ∉ s} → X) → ℝ}
    (hf : IntegrableOn f {x | ∀ i, x i ∈ A} (Measure.pi (fun _ : {i : ι // i ∈ s} => μ)))
    (hg : IntegrableOn g {x | ∀ i, x i ∈ B}
      (Measure.pi (fun _ : {i : ι // i ∉ s} => μ))) :
    IntegrableOn (fun x : ι → X =>
      f (fun i : {i : ι // i ∈ s} => x i) * g (fun i : {i : ι // i ∉ s} => x i))
      (binaryRegion A B s) (Measure.pi (fun _ : ι => μ)) := by
  let p := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => X) (fun i => i ∈ s)
  let SA := {x : {i : ι // i ∈ s} → X | ∀ i, x i ∈ A}
  let SB := {x : {i : ι // i ∉ s} → X | ∀ i, x i ∈ B}
  have hp := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) (fun i => i ∈ s)
  have hfi : Subtype.fintype (fun i : ι => i ∈ s) = Finset.Subtype.fintype s :=
    Subsingleton.elim _ _
  rw [hfi] at hp
  have hpre : p ⁻¹' (SA ×ˢ SB) = binaryRegion A B s := by
    ext x
    change ((∀ i : {i : ι // i ∈ s}, x i ∈ A) ∧ (∀ i : {i : ι // i ∉ s}, x i ∈ B)) ↔
      (∀ i, if i ∈ s then x i ∈ A else x i ∈ B)
    constructor
    · rintro ⟨ha, hb⟩ i
      split_ifs with hi
      · exact ha ⟨i, hi⟩
      · exact hb ⟨i, hi⟩
    · intro hh
      constructor
      · intro i
        simpa only [ite_eq_left i.property] using hh i
      · intro i
        simpa only [ite_eq_right i.property] using hh i
  have hprod : IntegrableOn (fun z => f z.1 * g z.2) (SA ×ˢ SB)
      ((Measure.pi (fun _ : {i : ι // i ∈ s} => μ)).prod
      (Measure.pi (fun _ : {i : ι // i ∉ s} => μ))) := by
    rw [IntegrableOn, ← Measure.prod_restrict]
    exact hf.mul_prod hg
  have hh := (hp.integrableOn_comp_preimage p.measurableEmbedding).2 hprod
  rw [hpre] at hh
  exact hh

theorem integral_lower_separated_product (μ : Measure X) [SigmaFinite μ]
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B)
    (s : Finset ι) {Ω : Set (ι → X)} {F : (ι → X) → ℝ}
    (hF : IntegrableOn F Ω (Measure.pi (fun _ : ι => μ)))
    (hF0 : ∀ x, 0 ≤ F x)
    (hsym : ∀ (e : Equiv.Perm ι) x, F (x ∘ e) = F x)
    (hinc : ∀ t : Finset ι, t.card = s.card → binaryRegion A B t ⊆ Ω)
    {f : ({i : ι // i ∈ s} → X) → ℝ} {g : ({i : ι // i ∉ s} → X) → ℝ}
    (hf : IntegrableOn f {x | ∀ i, x i ∈ A} (Measure.pi (fun _ : {i : ι // i ∈ s} => μ)))
    (hg : IntegrableOn g {x | ∀ i, x i ∈ B}
      (Measure.pi (fun _ : {i : ι // i ∉ s} => μ)))
    (hbound : ∀ x ∈ binaryRegion A B s,
      f (fun i : {i : ι // i ∈ s} => x i) * g (fun i : {i : ι // i ∉ s} => x i) ≤ F x) :
    (Fintype.card ι).choose s.card *
      ((∫ x in {x : {i : ι // i ∈ s} → X | ∀ i, x i ∈ A}, f x ∂(Measure.pi (fun _ : {i : ι // i ∈ s} => μ))) *
      (∫ x in {x : {i : ι // i ∉ s} → X | ∀ i, x i ∈ B}, g x
        ∂(Measure.pi (fun _ : {i : ι // i ∉ s} => μ)))) ≤
      ∫ x in Ω, F x ∂(Measure.pi (fun _ : ι => μ)) := by
  have hle := setIntegral_mono_on (integrableOn_binary_product μ A B s hf hg)
    (hF.mono_set (hinc s rfl)) (measurableSet_binaryRegion hA hB s) hbound
  rw [setIntegral_binary_product] at hle
  exact (mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _)).trans
    (integral_lower_binary_assignments μ hA hB hd s hF hF0 hsym hinc)

omit [MeasurableSpace X] [Fintype ι] [DecidableEq ι] in

theorem binomial_factorial_cancel {n k : ℕ} (hk : k ≤ n) {a b I : ℝ}
    (h : (n.choose k : ℝ) * (a * b) ≤ I) :
    (a / (k.factorial : ℝ)) * (b / ((n-k).factorial : ℝ)) ≤ I / (n.factorial : ℝ) := by
  have hn : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  apply (le_div_iff₀ hn).2
  rw [Nat.cast_choose ℝ hk] at h
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using h

end Assignments

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GeneralLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

section GeneralLabels
variable {ι : Type u_1} [Fintype ι]

theorem measurable_symmetricWeight {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) (β : ℝ) :
    Measurable (fun x : ι → Space => symmetricWeight φ β x) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hm : Measurable (fun x : ι → Space => x ∘ e) := by
    apply Measurable.of_eval
    intro i
    exact measurable_pi_apply (e i)
  have hh := (measurable_boltzmann hφ β (Fintype.card ι)).comp hm
  change Measurable (fun x => boltzmann φ β (x ∘ e)) at hh
  simpa only [boltzmann_eq_symmetricWeight, symmetricWeight_relabel] using hh

theorem symmetricWeight_le_of_stable {φ : ℝ → ℝ} {β B : ℝ} (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) (x : ι → Space) :
    symmetricWeight φ β x ≤ Real.exp (β * B * Fintype.card ι) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hh := boltzmann_le_of_stable hβ hstable (x ∘ e)
  simpa only [boltzmann_eq_symmetricWeight, symmetricWeight_relabel] using hh

theorem integrableOn_symmetricWeight {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B : ℝ} (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    {Ω : Set (ι → Space)} (hΩ : volume Ω ≠ ⊤) :
    IntegrableOn (fun x : ι → Space => symmetricWeight φ β x) Ω := by
  have : IsFiniteMeasure (volume.restrict Ω) := ⟨by
    simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hΩ⟩
  apply (integrable_const (Real.exp (β * B * Fintype.card ι))).mono'
    (measurable_symmetricWeight hφ β).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (symmetricWeight_nonneg φ β x)]
  exact symmetricWeight_le_of_stable hβ hstable x

theorem generalPartition_nonneg (φ : ℝ → ℝ) (β : ℝ) (A : Set Space) :
    0 ≤ generalPartition φ β A ι := by
  apply div_nonneg
  · apply integral_nonneg
    exact symmetricWeight_nonneg φ β
  · positivity

theorem generalPartition_eq_partition (φ : ℝ → ℝ) (β L : ℝ) (N : ℕ) :
    generalPartition φ β (cube L) (Fin N) = partition φ β L N := by
  classical
  by_cases hN : N = 0
  · subst N
    have hinj (x : Fin 0 → Space) : Function.Injective x := Function.injective_of_subsingleton x
    have hv : volume.real (Set.univ : Set (Fin 0 → Space)) = 1 := by
      simp [Measure.real, volume_pi]
    simp [generalPartition, partition, symmetricWeight, realPairEnergy, hinj, hv]
  · simp only [generalPartition, partition, hN, ite_false, Fintype.card_fin,
      ← boltzmann_eq_symmetricWeight, div_eq_mul_inv, one_mul]
    ring

theorem volume_generalConfigurations (A : Set Space) :
    volume {x : ι → Space | ∀ i, x i ∈ A} = (volume A) ^ Fintype.card ι := by
  have heq : {x : ι → Space | ∀ i, x i ∈ A} = Set.univ.pi (fun _ : ι => A) := by
    ext x
    simp
  rw [heq, volume_pi_pi]
  simp

theorem generalPartition_binary_lower [DecidableEq ι] {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B₀ : ℝ} (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B₀ * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    {A B C : Set Space} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : volume C ≠ ⊤) (hd : Disjoint A B) (haC : A ⊆ C) (hbC : B ⊆ C)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, φ ‖a - b‖ ≤ 0)
    (s : Finset ι) :
    generalPartition φ β A {i : ι // i ∈ s} *
      generalPartition φ β B {i : ι // i ∉ s} ≤ generalPartition φ β C ι := by
  classical
  have hΩ : volume {x : ι → Space | ∀ i, x i ∈ C} ≠ ⊤ := by
    rw [volume_generalConfigurations]
    exact ENNReal.pow_ne_top hC
  have hmA : volume A ≠ ⊤ := ne_top_of_le_ne_top hC (measure_mono haC)
  have hmB : volume B ≠ ⊤ := ne_top_of_le_ne_top hC (measure_mono hbC)
  have hΩA : volume {x : {i : ι // i ∈ s} → Space | ∀ i, x i ∈ A} ≠ ⊤ := by
    rw [volume_generalConfigurations]
    exact ENNReal.pow_ne_top hmA
  have hΩB : volume {x : {i : ι // i ∉ s} → Space | ∀ i, x i ∈ B} ≠ ⊤ := by
    rw [volume_generalConfigurations]
    exact ENNReal.pow_ne_top hmB
  have hInt := integral_lower_separated_product volume hA hB hd s
    (integrableOn_symmetricWeight hφ hβ hstable hΩ)
    (symmetricWeight_nonneg φ β)
    (symmetricWeight_relabel φ β)
    (fun t _ x hx i => by
      by_cases hi : i ∈ t
      · exact haC (by simpa only [ite_eq_left hi] using hx i)
      · exact hbC (by simpa only [ite_eq_right hi] using hx i))
    (integrableOn_symmetricWeight hφ hβ hstable hΩA)
    (integrableOn_symmetricWeight hφ hβ hstable hΩB)
    (fun x hx => by
      have hh := symmetricWeight_separated φ hβ (fun i => i ∈ s) hd hcross x
        (fun i hi => by simpa only [ite_eq_left hi] using hx i)
        (fun i hi => by simpa only [ite_eq_right hi] using hx i)
      have hfi : Subtype.fintype (fun i : ι => i ∈ s) = Finset.Subtype.fintype s :=
        Subsingleton.elim _ _
      rw [hfi] at hh
      exact hh)
  have hh := binomial_factorial_cancel (Finset.card_le_univ s) hInt
  simpa only [generalPartition, Fintype.card_subtype_compl,
    Fintype.card_coe, volume_pi] using hh

end GeneralLabels

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.TrialConfigurations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

noncomputable section

theorem trialBall_coord {q : ℝ} {i : Lattice} {x : Space} (hx : x ∈ trialBall q i)
    (k : Fin 3) : |x k - q * (i k : ℝ)| < q / 8 := by
  have hh := PiLp.norm_apply_le (x - gridPoint q i) k
  have hd : ‖x - gridPoint q i‖ < q / 8 := by
    simpa only [trialBall, Metric.mem_ball, dist_eq_norm] using hx
  have hc : |x k - q * (i k : ℝ)| ≤ ‖x - gridPoint q i‖ := by
    simpa [gridPoint] using hh
  exact hc.trans_lt hd

theorem trialBall_separation {q : ℝ} (hq : 0 < q) {i j : Lattice} (hij : i ≠ j)
    {x y : Space} (hx : x ∈ trialBall q i) (hy : y ∈ trialBall q j) :
    3 * q / 4 < ‖x - y‖ := by
  obtain ⟨k, hk⟩ : ∃ k, i k ≠ j k := by
    by_contra! h
    exact hij (funext h)
  have hxk := trialBall_coord hx k
  have hyk := trialBall_coord hy k
  have hc : |x k - y k| ≤ ‖x - y‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (x-y) k
  rw [abs_lt] at hxk hyk
  rw [abs_le] at hc
  rcases lt_or_gt_of_ne hk with h | h
  · have hh : (i k : ℝ) + 1 ≤ (j k : ℝ) := by exact_mod_cast h
    nlinarith
  · have hh : (j k : ℝ) + 1 ≤ (i k : ℝ) := by exact_mod_cast h
    nlinarith

theorem trialBall_disjoint {q : ℝ} (hq : 0 < q) :
    Pairwise (fun i j : Lattice => Disjoint (trialBall q i) (trialBall q j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  have hh := trialBall_separation hq hij hi hj
  simp only [sub_self, norm_zero] at hh
  linarith

theorem mem_gridNeighbors_iff {q : ℝ} {i j : Lattice} :
    j ∈ gridNeighbors q i ↔ ∀ k, |j k - i k| ≤ gridRadius q := by
  simp only [gridNeighbors, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]
  constructor <;> intro h k <;> have hh := h k <;> constructor <;> omega

theorem trialBall_close_mem {q : ℝ} (hq : 0 < q) {i j : Lattice} {x y : Space}
    (hx : x ∈ trialBall q i) (hy : y ∈ trialBall q j) (hxy : ‖x-y‖ < 1) :
    j ∈ gridNeighbors q i := by
  rw [mem_gridNeighbors_iff]
  intro k
  have hxk := trialBall_coord hx k
  have hyk := trialBall_coord hy k
  have hn : |x k - y k| ≤ ‖x-y‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (x-y) k
  have hc : |x k - y k| < 1 := hn.trans_lt hxy
  have hceil : q⁻¹ + 1 ≤ (gridRadius q : ℝ) := Int.le_ceil _
  have hmul := mul_le_mul_of_nonneg_left hceil hq.le
  have hcancel : q * (q⁻¹ + 1) = 1 + q := by field_simp
  rw [hcancel] at hmul
  have hh : |((j k : ℤ) : ℝ) - (i k : ℝ)| ≤ (gridRadius q : ℝ) := by
    rw [abs_lt] at hxk hyk hc
    rw [abs_le]
    constructor <;> nlinarith
  exact_mod_cast hh

theorem gridRadius_nonneg {q : ℝ} (hq : 0 < q) : 0 ≤ gridRadius q := by
  exact Int.ceil_nonneg (by positivity)

theorem card_gridNeighbors {q : ℝ} (hq : 0 < q) (i : Lattice) :
    (gridNeighbors q i).card = (2 * (gridRadius q).toNat + 1) ^ 3 := by
  have hr := gridRadius_nonneg hq
  simp only [gridNeighbors, Fintype.card_piFinset, Int.card_Icc]
  have hh (k : Fin 3) : (i k + gridRadius q + 1 - (i k - gridRadius q)).toNat =
      2 * (gridRadius q).toNat + 1 := by omega
  simp only [hh, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem grid_close_card_le {ι : Type u_1} [Fintype ι] {q : ℝ} (hq : 0 < q)
    (f : ι → Lattice) (hf : Function.Injective f) (x : ι → Space)
    (hx : ∀ i, x i ∈ trialBall q (f i)) (i : ι) :
    ((Finset.univ.filter fun j => ‖x i - x j‖ < 1).card : ℕ) ≤
      (2 * (gridRadius q).toNat + 1)^3 := by
  classical
  rw [← card_gridNeighbors hq (f i)]
  apply Finset.card_le_card_of_injOn f
  · intro j hj
    exact trialBall_close_mem hq (hx i) (hx j) (Finset.mem_filter.mp hj).2
  · exact hf.injOn

theorem trialEnergyConstant_nonneg (t q : ℝ) : 0 ≤ trialEnergyConstant t q := by
  unfold trialEnergyConstant
  positivity

theorem trial_core_row_le {ι : Type u_1} [Fintype ι] [DecidableEq ι] {q t : ℝ} (hq : 0 < q) (ht : 1 < t)
    (f : ι → Lattice) (hf : Function.Injective f) (x : ι → Space)
    (hx : ∀ i, x i ∈ trialBall q (f i)) (i : ι) :
    ∑ j, (if i = j then 0 else coreProfile t ‖x i-x j‖) ≤ trialEnergyConstant t q := by
  classical
  let C := t^2 + (Real.exp (-t) / (3*q/4))^12
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsum : (∑ j, (if i = j then 0 else coreProfile t ‖x i-x j‖)) ≤
      ∑ j, (if ‖x i-x j‖ < 1 then C else 0) := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hij : i = j
    · simp only [ite_eq_left hij]
      split_ifs <;> positivity
    · rw [ite_eq_right hij]
      by_cases hdist : ‖x i-x j‖ < 1
      · rw [ite_eq_left hdist]
        exact coreProfile_le (by linarith : 0 < 3*q/4)
          (trialBall_separation hq (fun h => hij (hf h)) (hx i) (hx j)).le t
      · rw [ite_eq_right hdist, coreProfile_eq_zero ht (le_of_not_gt hdist)]
  have hh := grid_close_card_le hq f hf x hx i
  have hcard : ((Finset.univ.filter fun j => ‖x i - x j‖ < 1).card : ℝ) ≤
      (2 * (gridRadius q).toNat + 1 : ℝ)^3 := by exact_mod_cast hh
  calc
    _ ≤ _ := hsum
    _ = ((Finset.univ.filter fun j => ‖x i - x j‖ < 1).card : ℝ) * C := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ (2 * (gridRadius q).toNat + 1 : ℝ)^3 * C := mul_le_mul_of_nonneg_right hcard hC
    _ = trialEnergyConstant t q := rfl

theorem interiorGrid_ball_subset {q L : ℝ} (hq : 0 < q) (hL : 2*q ≤ L)
    {i : Lattice} (hi : i ∈ interiorGrid q L) : trialBall q i ⊆ cube L := by
  intro x hx k
  have hk : -(⌊L/(2*q)-1⌋₊ : ℤ) ≤ i k ∧ i k ≤ (⌊L/(2*q)-1⌋₊ : ℤ) := by
    have hh : ∀ k, -(⌊L/(2*q)-1⌋₊ : ℤ) ≤ i k ∧ i k ≤ (⌊L/(2*q)-1⌋₊ : ℤ) := by
      simpa only [interiorGrid, Fintype.mem_piFinset, Finset.mem_Icc] using hi
    exact hh k
  have hk1 : -(⌊L/(2*q)-1⌋₊ : ℝ) ≤ (i k : ℝ) := by exact_mod_cast hk.1
  have hk2 : (i k : ℝ) ≤ (⌊L/(2*q)-1⌋₊ : ℝ) := by exact_mod_cast hk.2
  have hnonneg : 0 ≤ L/(2*q)-1 := by
    have : 1 ≤ L/(2*q) := (le_div_iff₀ (by positivity)).2 (by nlinarith)
    linarith
  have hn := Nat.floor_le hnonneg
  have heq : (L/(2*q)-1)*(2*q) = L-2*q := by field_simp
  have hmul := mul_le_mul_of_nonneg_right hn (by positivity : 0 ≤ 2*q)
  rw [heq] at hmul
  have hxk := trialBall_coord hx k
  rw [abs_lt] at hxk
  constructor <;> nlinarith

theorem card_interiorGrid (q L : ℝ) :
    (interiorGrid q L).card = (2*⌊L/(2*q)-1⌋₊+1)^3 := by
  simp only [interiorGrid, Fintype.card_piFinset, Int.card_Icc]
  have hh : ((⌊L/(2*q)-1⌋₊ : ℤ) + 1 - -(⌊L/(2*q)-1⌋₊ : ℤ)).toNat =
      2*⌊L/(2*q)-1⌋₊+1 := by omega
  simp only [hh, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem card_interiorGrid_lower {q L : ℝ} (hq : 0 < q) (hL : 8*q ≤ L) :
    (L/(2*q))^3 ≤ ((interiorGrid q L).card : ℝ) := by
  rw [card_interiorGrid]
  push_cast
  have hh := Nat.lt_floor_add_one (L/(2*q)-1)
  have heq : (L/(2*q))*(2*q) = L := by field_simp
  have hmul := mul_lt_mul_of_pos_right hh (by positivity : 0 < 2*q)
  have hL0 : 0 ≤ L := by linarith
  have hden : 0 ≤ L/(2*q) := div_nonneg hL0 (by positivity)
  have hle : L/(2*q) ≤ 2*(⌊L/(2*q)-1⌋₊ : ℝ)+1 := by nlinarith
  exact pow_le_pow_left₀ hden hle 3

theorem exists_trial_sites {q L D : ℝ} (hq : 0 < q) (hL : 8*q ≤ L)
    (hD : D ≤ (2*q)⁻¹ ^ 3) {N : ℕ} (hN : (N : ℝ) ≤ D*L^3) :
    ∃ f : Fin N → Lattice, Function.Injective f ∧
      ∀ i, trialBall q (f i) ⊆ cube L := by
  have hL0 : 0 ≤ L := by linarith
  have hc : (N : ℝ) ≤ ((interiorGrid q L).card : ℝ) := calc
    _ ≤ D*L^3 := hN
    _ ≤ (2*q)⁻¹ ^ 3 * L^3 := mul_le_mul_of_nonneg_right hD (by positivity)
    _ = (L/(2*q))^3 := by ring
    _ ≤ _ := card_interiorGrid_lower hq hL
  have hcard : Fintype.card (Fin N) ≤ Fintype.card (interiorGrid q L) := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using (show N ≤ (interiorGrid q L).card by exact_mod_cast hc)
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine ⟨fun i => (e i).val, Subtype.val_injective.comp e.injective, ?_⟩
  intro i
  exact interiorGrid_ball_subset hq (by linarith) (e i).property

theorem trialVolume_pos {q : ℝ} (hq : 0 < q) : 0 < trialVolume q := by
  unfold trialVolume
  positivity

theorem real_volume_trialBall {q : ℝ} (hq : 0 < q) (i : Lattice) :
    (volume (trialBall q i)).toReal = trialVolume q := by
  simp only [trialBall, EuclideanSpace.volume_ball_fin_three, trialVolume,
    ENNReal.toReal_mul, ENNReal.toReal_pow]
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ q/8),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi*4/3)]

theorem symmetricWeight_grid_lower {ι : Type u_1} [Fintype ι] {q t β : ℝ}
    (hq : 0 < q) (ht : 1 < t) (hβ : 0 ≤ β) {φ : ℝ → ℝ}
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r)
    (f : ι → Lattice) (hf : Function.Injective f) (x : ι → Space)
    (hx : ∀ i, x i ∈ trialBall q (f i)) :
    Real.exp (-β * (trialEnergyConstant t q * Fintype.card ι)) ≤ symmetricWeight φ β x := by
  classical
  have hdist (i j : ι) (hij : i ≠ j) : 0 < ‖x i-x j‖ :=
    lt_trans (by linarith) (trialBall_separation hq (fun h => hij (hf h)) (hx i) (hx j))
  have hinj : Function.Injective x := by
    intro i j hij
    by_contra hne
    have hh := hdist i j hne
    simp only [hij, sub_self, norm_zero, lt_self_iff_false] at hh
  have hrow (i : ι) : (∑ j, if i = j then 0 else φ ‖x i-x j‖) ≤ trialEnergyConstant t q := by
    apply le_trans _ (trial_core_row_le hq ht f hf x hx i)
    apply Finset.sum_le_sum
    intro j _
    by_cases hij : i = j
    · simp only [ite_eq_left hij, le_refl]
    · simp only [ite_eq_right hij]
      exact hcore _ (hdist i j hij)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hrow i)
  have hsum' : (∑ i, ∑ j, if i = j then 0 else φ ‖x i-x j‖) ≤
      trialEnergyConstant t q * (Fintype.card ι : ℝ) := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using hsum
  have hpos : 0 ≤ trialEnergyConstant t q * (Fintype.card ι : ℝ) :=
    mul_nonneg (trialEnergyConstant_nonneg t q) (Nat.cast_nonneg _)
  have he : realPairEnergy φ x ≤ trialEnergyConstant t q * Fintype.card ι := by
    unfold realPairEnergy
    nlinarith only [hsum', hpos]
  rw [symmetricWeight, ite_eq_left hinj]
  apply Real.exp_le_exp.mpr
  nlinarith only [he, hβ]

theorem partition_grid_lower {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {q t β B L : ℝ} (hq : 0 < q) (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B*(N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r)
    {N : ℕ} (f : Fin N → Lattice) (hf : Function.Injective f)
    (hinc : ∀ i, trialBall q (f i) ⊆ cube L) :
    trialVolume q ^ N * Real.exp (-β*(trialEnergyConstant t q * N)) ≤ partition φ β L N := by
  classical
  let Bs := fun i : Fin N => trialBall q (f i)
  have hm : ∀ i, MeasurableSet (Bs i) := fun _ => measurableSet_ball
  have hd : Pairwise (fun i j => Disjoint (Bs i) (Bs j)) :=
    fun _ _ hij => trialBall_disjoint hq (fun h => hij (hf h))
  have hfin : ∀ i, volume (Bs i) ≠ ⊤ := fun _ => measure_ball_ne_top
  have hΩ : volume {x : Fin N → Space | ∀ i, x i ∈ cube L} ≠ ⊤ := by
    exact (isCompact_configurations L N).measure_lt_top.ne
  have hi := integral_lower_of_disjoint_assignments volume hm hd hfin
    (show IntegrableOn (fun x : Fin N → Space => symmetricWeight φ β x)
      {x | ∀ i, x i ∈ cube L} (Measure.pi fun _ => volume) by
      simpa only [← volume_pi] using integrableOn_symmetricWeight hφ hβ hstable hΩ)
    (symmetricWeight_nonneg φ β)
    (fun e x hx i => hinc (e i) (hx i))
    (fun e x hx => symmetricWeight_grid_lower hq ht hβ hcore (f ∘ e)
      (hf.comp e.injective) x hx)
  have hv : (∏ i : Fin N, (volume (Bs i)).toReal) = trialVolume q ^ N := by
    simp only [Bs, real_volume_trialBall hq, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  rw [hv, Fintype.card_fin] at hi
  have hn : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  rw [← generalPartition_eq_partition, generalPartition, Fintype.card_fin]
  apply (le_div_iff₀ hn).2
  simpa only [mul_comm, mul_assoc, mul_left_comm, volume_pi] using hi

theorem partition_trial_lower {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {q t β B L D : ℝ} (hq : 0 < q) (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B*(N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r)
    (hL : 8*q ≤ L) (hD : D ≤ (2*q)⁻¹ ^ 3) {N : ℕ} (hN : (N : ℝ) ≤ D*L^3) :
    trialVolume q ^ N * Real.exp (-β*(trialEnergyConstant t q * N)) ≤ partition φ β L N := by
  obtain ⟨f, hf, hinc⟩ := exists_trial_sites hq hL hD hN
  exact partition_grid_lower hφ hq ht hβ hstable hcore f hf hinc

end

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.SpatialProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem generalPartition_relabel {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ]
    (φ : ℝ → ℝ) (β : ℝ) (A : Set Space) (e : ι ≃ κ) :
    generalPartition φ β A ι = generalPartition φ β A κ := by
  let p : (ι → Space) ≃ᵐ (κ → Space) := MeasurableEquiv.piCongrLeft (fun _ : κ => Space) e
  have hp : MeasurePreserving p volume volume := by
    simpa only [volume_pi] using measurePreserving_piCongrLeft (fun _ : κ => volume) e
  have hpx (x : ι → Space) : p x = x ∘ e.symm := by
    funext i
    simpa only [p, Equiv.apply_symm_apply, Function.comp_apply] using
      (MeasurableEquiv.piCongrLeft_apply_apply e (β := fun _ : κ => Space) x (e.symm i))
  have heq := hp.setIntegral_preimage_emb p.measurableEmbedding (symmetricWeight φ β)
    {x : κ → Space | ∀ i, x i ∈ A}
  have hpre : p ⁻¹' {x : κ → Space | ∀ i, x i ∈ A} =
      {x : ι → Space | ∀ i, x i ∈ A} := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq, hpx, Function.comp_apply]
    constructor
    · intro h i
      simpa only [Equiv.symm_apply_apply] using h (e i)
    · intro h i
      exact h (e.symm i)
  rw [hpre] at heq
  simp only [hpx, symmetricWeight_relabel] at heq
  unfold generalPartition
  rw [Fintype.card_congr e, heq]

theorem generalPartition_eq_setPartition {ι : Type u_1} [Fintype ι]
    (φ : ℝ → ℝ) (β : ℝ) (A : Set Space) :
    generalPartition φ β A ι = setPartition φ β A (Fintype.card ι) :=
  generalPartition_relabel φ β A (Fintype.equivFin ι)

theorem setPartition_zero (φ : ℝ → ℝ) (β : ℝ) (A : Set Space) :
    setPartition φ β A 0 = 1 := by
  have hinj (x : Fin 0 → Space) : Function.Injective x := Function.injective_of_subsingleton x
  simp [setPartition, generalPartition, symmetricWeight, realPairEnergy, hinj,
    Measure.real, volume_pi]

theorem setPartition_nonneg (φ : ℝ → ℝ) (β : ℝ) (A : Set Space) (N : ℕ) :
    0 ≤ setPartition φ β A N := generalPartition_nonneg φ β A

theorem setPartition_translate (φ : ℝ → ℝ) (β : ℝ) (A : Set Space) (N : ℕ) (a : Space) :
    setPartition φ β ((fun x => x+a) '' A) N = setPartition φ β A N := by
  let p : (Fin N → Space) ≃ᵐ (Fin N → Space) := MeasurableEquiv.addRight (fun _ => a)
  have hp : MeasurePreserving p volume volume := measurePreserving_add_right volume (fun _ => a)
  have heq := hp.setIntegral_preimage_emb p.measurableEmbedding (symmetricWeight φ β)
    {x : Fin N → Space | ∀ i, x i ∈ (fun x => x+a) '' A}
  have hpre : p ⁻¹' {x : Fin N → Space | ∀ i, x i ∈ (fun x => x+a) '' A} =
      {x : Fin N → Space | ∀ i, x i ∈ A} := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq]
    apply forall_congr'
    intro i
    change x i + a ∈ (fun y => y+a) '' A ↔ x i ∈ A
    simp only [mem_image, add_left_inj, exists_eq_right]
  have hsym (x : Fin N → Space) : symmetricWeight φ β (p x) = symmetricWeight φ β x :=
    symmetricWeight_translate φ β x a
  rw [hpre] at heq
  simp only [hsym] at heq
  simpa only [setPartition, generalPartition, Fintype.card_fin] using
    congrArg (fun z : ℝ => z / (N.factorial : ℝ)) heq.symm

theorem setPartition_binary_lower {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B₀ : ℝ} (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B₀ * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    {A B C : Set Space} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : volume C ≠ ⊤) (hd : Disjoint A B) (haC : A ⊆ C) (hbC : B ⊆ C)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, φ ‖a-b‖ ≤ 0) (n m : ℕ) :
    setPartition φ β A n * setPartition φ β B m ≤ setPartition φ β C (n+m) := by
  classical
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
    (show n ≤ (Finset.univ : Finset (Fin (n+m))).card by simp)
  have hh := generalPartition_binary_lower hφ hβ hstable hA hB hC hd haC hbC hcross s
  simpa only [generalPartition_eq_setPartition, Fintype.card_coe, Fintype.card_subtype_compl,
    Fintype.card_fin, hs, Nat.add_sub_cancel_left] using hh

theorem setPartition_product_lower {κ : Type u_1} {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B₀ : ℝ} (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B₀ * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (A : κ → Set Space) (n : κ → ℕ) (s : Finset κ)
    (hA : ∀ i ∈ s, MeasurableSet (A i))
    (hd : (s : Set κ).Pairwise (fun i j => Disjoint (A i) (A j)))
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, φ ‖a-b‖ ≤ 0)
    {C : Set Space} (hC : volume C ≠ ⊤) (hinc : ∀ i ∈ s, A i ⊆ C) :
    (∏ i ∈ s, setPartition φ β (A i) (n i)) ≤ setPartition φ β C (∑ i ∈ s, n i) := by
  classical
  induction s using Finset.induction_on generalizing C with
  | empty => simp [setPartition_zero]
  | @insert i s hi ih =>
    let U := ⋃ j ∈ s, A j
    have hU : MeasurableSet U := MeasurableSet.biUnion s.finite_toSet.countable (fun j hj =>
      hA j (Finset.mem_insert_of_mem hj))
    have hUC : U ⊆ C := iUnion₂_subset (fun j hj => hinc j (Finset.mem_insert_of_mem hj))
    have hUf : volume U ≠ ⊤ := ne_top_of_le_ne_top hC (measure_mono hUC)
    have hsub : ∀ j ∈ s, A j ⊆ U := fun j hj => subset_iUnion₂_of_subset j hj Subset.rfl
    have ih' := ih (fun j hj => hA j (Finset.mem_insert_of_mem hj))
      (hd.mono (Finset.subset_insert _ _))
      (fun j hj k hk => hcross j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)) hUf hsub
    have hdis : Disjoint (A i) U := by
      apply Set.disjoint_iUnion₂_right.mpr
      intro j hj
      exact hd (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hj) (fun h => hi (h ▸ hj))
    have henergy : ∀ a ∈ A i, ∀ b ∈ U, φ ‖a-b‖ ≤ 0 := by
      intro a ha b hb
      obtain ⟨j, hj, hjb⟩ := mem_iUnion₂.mp hb
      exact hcross i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        (fun h => hi (h ▸ hj)) a ha b hjb
    have hbin := setPartition_binary_lower hφ hβ hstable
      (hA i (Finset.mem_insert_self _ _)) hU hC hdis
      (hinc i (Finset.mem_insert_self _ _)) hUC henergy (n i) (∑ j ∈ s, n j)
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (mul_le_mul_of_nonneg_left ih' (setPartition_nonneg φ β (A i) (n i))).trans hbin

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.BoxTiling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem isCompact_tileBox (ℓ L : ℝ) {k : ℕ} (i : Fin 3 → Fin k) :
    IsCompact (tileBox ℓ L i) :=
  (isCompact_cube ℓ).image (continuous_id.add continuous_const)

theorem tileBox_subset {ℓ L : ℝ} {k : ℕ} (hℓ : 0 ≤ ℓ)
    (hk : (k : ℝ)*(ℓ+2) ≤ L) (i : Fin 3 → Fin k) : tileBox ℓ L i ⊆ cube L := by
  rintro x ⟨y, hy, rfl⟩ j
  have hyj := hy j
  have hij : (i j : ℝ)+1 ≤ k := by exact_mod_cast (i j).isLt
  have h0 : (0 : ℝ) ≤ (i j : ℝ) := Nat.cast_nonneg _
  change y j + ((ℓ+2)*((i j : ℝ)+1/2)-L/2) ∈ Icc (-L/2) (L/2)
  constructor <;> nlinarith [hyj.1, hyj.2]

theorem tileBox_separation {ℓ L : ℝ} {k : ℕ} (hℓ : 0 ≤ ℓ)
    {i j : Fin 3 → Fin k} (hij : i ≠ j) {x y : Space}
    (hx : x ∈ tileBox ℓ L i) (hy : y ∈ tileBox ℓ L j) : 2 ≤ ‖x-y‖ := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  obtain ⟨r, hr⟩ : ∃ r, i r ≠ j r := by
    by_contra! h
    exact hij (funext h)
  have har := ha r
  have hbr := hb r
  have hnorm : |(a+tileCenter ℓ L i) r - (b+tileCenter ℓ L j) r| ≤
      ‖(a+tileCenter ℓ L i)-(b+tileCenter ℓ L j)‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using
      PiLp.norm_apply_le ((a+tileCenter ℓ L i)-(b+tileCenter ℓ L j)) r
  change |a r + ((ℓ+2)*((i r : ℝ)+1/2)-L/2) -
    (b r + ((ℓ+2)*((j r : ℝ)+1/2)-L/2))| ≤
      ‖(a+tileCenter ℓ L i)-(b+tileCenter ℓ L j)‖ at hnorm
  rw [abs_le] at hnorm
  rcases lt_or_gt_of_ne hr with h | h
  · have hh : (i r : ℝ)+1 ≤ (j r : ℝ) := by exact_mod_cast h
    have hmul := mul_le_mul_of_nonneg_left hh (by linarith : 0 ≤ ℓ+2)
    nlinarith [har.1, har.2, hbr.1, hbr.2]
  · have hh : (j r : ℝ)+1 ≤ (i r : ℝ) := by exact_mod_cast h
    have hmul := mul_le_mul_of_nonneg_left hh (by linarith : 0 ≤ ℓ+2)
    nlinarith [har.1, har.2, hbr.1, hbr.2]

theorem tileBox_pairwiseDisjoint {ℓ L : ℝ} {k : ℕ} (hℓ : 0 ≤ ℓ) :
    Pairwise (fun i j : Fin 3 → Fin k => Disjoint (tileBox ℓ L i) (tileBox ℓ L j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hh := tileBox_separation hℓ hij hx hy
  simp only [sub_self, norm_zero] at hh
  norm_num at hh

theorem partition_tiling_lower {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {β B ℓ L : ℝ} (hβ : 0 ≤ β) (hℓ : 0 ≤ ℓ) (hL : 0 ≤ L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hsign : ∀ r, 1 ≤ r → φ r ≤ 0)
    (n : (Fin 3 → Fin ⌊L/(ℓ+2)⌋₊) → ℕ) :
    (∏ i, partition φ β ℓ (n i)) ≤ partition φ β L (∑ i, n i) := by
  classical
  have hden : 0 < ℓ+2 := by linarith
  have hk : (⌊L/(ℓ+2)⌋₊ : ℝ)*(ℓ+2) ≤ L := by
    apply (le_div_iff₀ hden).mp
    exact Nat.floor_le (div_nonneg hL hden.le)
  have hh := setPartition_product_lower hφ hβ hstable (tileBox ℓ L) n Finset.univ
    (fun i _ => (isCompact_tileBox ℓ L i).measurableSet)
    (fun i _ j _ hij => tileBox_pairwiseDisjoint hℓ hij)
    (fun i _ j _ hij a ha b hb => hsign _ (le_trans (by norm_num)
      (tileBox_separation hℓ hij ha hb)))
    (isCompact_cube L).measure_lt_top.ne (fun i _ => tileBox_subset hℓ hk i)
  have hv (i : Fin 3 → Fin ⌊L/(ℓ+2)⌋₊) :
      setPartition φ β (tileBox ℓ L i) (n i) = partition φ β ℓ (n i) := by
    rw [tileBox, setPartition_translate, setPartition, generalPartition_eq_partition]
  simp_rw [hv] at hh
  simpa only [setPartition, generalPartition_eq_partition] using hh

theorem exists_concentrated_counts (K H N : ℕ) (hN : N ≤ K*H) :
    ∃ r : Fin K → ℕ, (∑ i, r i) = N ∧ (∀ i, r i ≤ H) ∧
      (∑ i, if r i = 0 then 0 else 1) * H ≤ N+H := by
  induction K generalizing N with
  | zero =>
    have hzero : N = 0 := by omega
    subst N
    exact ⟨Fin.elim0, by simp, (fun i => Fin.elim0 i), by simp⟩
  | succ K ih =>
    by_cases hh : N ≤ H
    · refine ⟨Fin.cons N (fun _ => 0), ?_, ?_, ?_⟩
      · simp [Fin.sum_univ_succ]
      · intro i
        refine Fin.cases hh (fun _ => Nat.zero_le _) i
      · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ite_true, Finset.sum_const_zero,
          add_zero]
        split_ifs <;> omega
    · have hHK : N-H ≤ K*H := by
        rw [Nat.succ_mul] at hN
        omega
      obtain ⟨r, hr, hbound, hc⟩ := ih (N-H) hHK
      have hH : 0 < H := by
        by_contra hzero
        have hz : H = 0 := by omega
        simp only [hz, Nat.mul_zero, Nat.le_zero] at hN
        omega
      refine ⟨Fin.cons H r, ?_, ?_, ?_⟩
      · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hr]
        omega
      · intro i
        exact Fin.cases (le_refl H) hbound i
      · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ite_eq_right hH.ne']
        have hsub := Nat.sub_add_cancel (show H ≤ N by omega)
        nlinarith

theorem exists_adjusted_counts (K b H N : ℕ) (hb : 0 < b) (hH : 2*b ≤ H)
    (hN : N ≤ K*H) :
    ∃ r : Fin K → ℕ, (∑ i, r i) = N ∧ (∀ i, r i ≤ H) ∧
      ((∑ i, if r i = b then 0 else 1 : ℕ) : ℝ) * b ≤
        |(N : ℝ) - (K : ℝ)*b| + H := by
  have hbH : b ≤ H := by omega
  by_cases hNb : K*b ≤ N
  · have hdel : N-K*b ≤ K*(H-b) := by
      rw [Nat.mul_sub_left_distrib]
      omega
    obtain ⟨d, hsum, hbound, hc⟩ := exists_concentrated_counts K (H-b) (N-K*b) hdel
    refine ⟨fun i => b+d i, ?_, ?_, ?_⟩
    · simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, hsum]
      omega
    · intro i
      change b+d i ≤ H
      have hh := hbound i
      omega
    · have heq : (∑ i, if b+d i = b then 0 else 1 : ℕ) =
          ∑ i, if d i = 0 then 0 else 1 := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [Nat.add_eq_left]
      rw [heq]
      have hineq : (∑ i, if d i = 0 then 0 else 1) * b ≤ (N-K*b)+H := by
        have hh := Nat.mul_le_mul_left (∑ i, if d i = 0 then 0 else 1) (show b ≤ H-b by omega)
        omega
      have hsub : ((N-K*b : ℕ) : ℝ) = (N : ℝ)-(K : ℝ)*b := by
        rw [Nat.cast_sub hNb, Nat.cast_mul]
      have hsgn : 0 ≤ (N : ℝ)-(K : ℝ)*b := by
        have hh : (K : ℝ)*b ≤ (N : ℝ) := by exact_mod_cast hNb
        linarith
      rw [abs_of_nonneg hsgn]
      have hh : ((∑ i, if d i = 0 then 0 else 1 : ℕ) : ℝ)*b ≤ ((N-K*b : ℕ) : ℝ)+H := by
        exact_mod_cast hineq
      rwa [hsub] at hh
  · have hNb' : N ≤ K*b := by omega
    obtain ⟨d, hsum, hbound, hc⟩ := exists_concentrated_counts K b (K*b-N) (Nat.sub_le _ _)
    refine ⟨fun i => b-d i, ?_, ?_, ?_⟩
    · have hh : (∑ i : Fin K, (b - d i)) + (∑ i : Fin K, d i) = K*b := by
        rw [← Finset.sum_add_distrib]
        simp only [Nat.sub_add_cancel (hbound _), Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul]
      change (∑ i : Fin K, (b - d i)) = N
      rw [hsum] at hh
      omega
    · intro i
      exact (Nat.sub_le b _).trans hbH
    · have heq : (∑ i, if b-d i = b then 0 else 1 : ℕ) =
          ∑ i, if d i = 0 then 0 else 1 := by
        apply Finset.sum_congr rfl
        intro i _
        have hh : b-d i = b ↔ d i = 0 := by omega
        simp only [hh]
      rw [heq]
      have hineq : (∑ i, if d i = 0 then 0 else 1) * b ≤ (K*b-N)+H := by omega
      have hsub : ((K*b-N : ℕ) : ℝ) = (K : ℝ)*b-N := by
        rw [Nat.cast_sub hNb', Nat.cast_mul]
      have hsgn : (N : ℝ)-(K : ℝ)*b ≤ 0 := by
        have hh : (N : ℝ) ≤ (K : ℝ)*b := by exact_mod_cast hNb'
        linarith
      rw [abs_of_nonpos hsgn]
      have hh : ((∑ i, if d i = 0 then 0 else 1 : ℕ) : ℝ)*b ≤ ((K*b-N : ℕ) : ℝ)+H := by
        exact_mod_cast hineq
      rw [hsub] at hh
      linarith

theorem sum_baseline_le {K b H : ℕ} {r : Fin K → ℕ} {a : ℕ → ℝ} {M : ℝ}
    (hr : ∀ i, r i ≤ H) (ha : ∀ n, n ≤ H → a n ≤ M) (hb : -M ≤ a b) :
    ∑ i, a (r i) ≤ K*a b + 2*M*(∑ i, if r i = b then 0 else 1 : ℕ) := by
  classical
  calc
    ∑ i, a (r i) ≤ ∑ i, (a b + 2*M*(if r i = b then 0 else 1 : ℕ)) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hh : r i = b
      · simp [hh]
      · simp only [ite_eq_right hh, Nat.cast_one, mul_one]
        linarith [ha (r i) (hr i)]
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.mul_sum, Nat.cast_sum]

theorem adjusted_box_comparison (a : ℝ → ℕ → ℝ) {ℓ L M : ℝ} {b H N : ℕ}
    (hℓ : 0 < ℓ) (hL : 0 < L) (hM : 0 ≤ M) (hb : 0 < b) (hH : 2*b ≤ H)
    (hN : N ≤ tileCount ℓ L * H)
    (hbox : ∀ r : Fin (tileCount ℓ L) → ℕ, (∑ i, r i) = N →
      a L N ≤ ℓ^3/L^3 * ∑ i, a ℓ (r i))
    (hbound : ∀ n, n ≤ H → a ℓ n ≤ M) (hbase : -M ≤ a ℓ b) :
    a L N ≤ ((tileCount ℓ L : ℝ)/L^3)*ℓ^3*a ℓ b +
      (2*M*ℓ^3/(b : ℝ)) * (|(N : ℝ)/L^3 - ((tileCount ℓ L : ℝ)/L^3)*b| + H/L^3) := by
  classical
  obtain ⟨r, hr, hcounts, hchange⟩ := exists_adjusted_counts (tileCount ℓ L) b H N hb hH hN
  have hs := sum_baseline_le hcounts hbound hbase
  have hm : 0 ≤ ℓ^3/L^3 := div_nonneg (pow_nonneg hℓ.le _) (pow_nonneg hL.le _)
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hc : (∑ i, if r i = b then 0 else 1 : ℕ) ≤
      (|(N : ℝ) - (tileCount ℓ L : ℝ)*b|+H)/(b : ℝ) :=
    (le_div_iff₀ hbR).2 hchange
  calc
    a L N ≤ ℓ^3/L^3 * ∑ i, a ℓ (r i) := hbox r hr
    _ ≤ ℓ^3/L^3 * ((tileCount ℓ L : ℝ)*a ℓ b +
        2*M*((|(N : ℝ)-(tileCount ℓ L : ℝ)*b|+H)/(b : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ hm
      exact hs.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hc (show 0 ≤ 2*M by positivity)))
    _ = _ := by
      have heq : (N : ℝ)/L^3 - ((tileCount ℓ L : ℝ)/L^3)*b =
          ((N : ℝ)-(tileCount ℓ L : ℝ)*b)/L^3 := by ring
      rw [heq, abs_div, abs_of_pos (pow_pos hL 3)]
      ring

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.DensityLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem densityFilter_length (d : ℝ) :
    Tendsto (fun p : ℝ × ℕ => p.1) (densityFilter d) atTop := by
  have h : Tendsto (fun p : ℝ × ℕ => (p.1, (p.2 : ℝ)/p.1^3))
      (densityFilter d) (atTop ×ˢ 𝓝 d) := Filter.tendsto_comap
  simpa only [Function.comp_def] using
    (tendsto_fst : Tendsto (Prod.fst : ℝ × ℝ → ℝ) (atTop ×ˢ 𝓝 d) atTop).comp h

theorem densityFilter_density (d : ℝ) :
    Tendsto (fun p : ℝ × ℕ => (p.2 : ℝ)/p.1^3) (densityFilter d) (𝓝 d) :=
  tendsto_snd.comp (Filter.tendsto_comap : Tendsto _ (densityFilter d) _)

theorem tendsto_densityFilter_iff {α : Type u_1} {l : Filter α} {d : ℝ} {p : α → ℝ × ℕ} :
    Tendsto p l (densityFilter d) ↔
      Tendsto (fun x => (p x).1) l atTop ∧
      Tendsto (fun x => ((p x).2 : ℝ)/(p x).1^3) l (𝓝 d) := by
  rw [densityFilter, tendsto_comap_iff, tendsto_prod_iff']
  rfl

theorem floor_density_tendsto {d : ℝ} (hd : 0 ≤ d) :
    Tendsto (fun L : ℝ => (L, ⌊d*L^3⌋₊)) atTop (densityFilter d) := by
  apply tendsto_densityFilter_iff.2
  exact ⟨tendsto_id, (tendsto_nat_floor_mul_div_atTop hd).comp
    (tendsto_pow_atTop (by norm_num : 3 ≠ 0))⟩

instance densityFilter_neBot (d : ℝ) [Fact (0 ≤ d)] : (densityFilter d).NeBot :=
  (floor_density_tendsto (Fact.out : 0 ≤ d)).neBot

theorem tileCount_asymptotic {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    Tendsto (fun L : ℝ => (tileCount ℓ L : ℝ)/L^3) atTop (𝓝 ((ℓ+2)⁻¹^3)) := by
  have hh : 0 ≤ (ℓ+2)⁻¹ := inv_nonneg.mpr (by linarith)
  have ht := (tendsto_nat_floor_mul_div_atTop hh).pow 3
  simpa only [tileCount, Nat.cast_pow, div_pow, div_eq_mul_inv, mul_comm,
    mul_pow, inv_pow] using ht

theorem length_inv_cube_tendsto (d : ℝ) :
    Tendsto (fun p : ℝ × ℕ => (p.1^3)⁻¹) (densityFilter d) (𝓝 0) := by
  simpa only [Function.comp_def, ← inv_pow, zero_pow (by norm_num : 3 ≠ 0)] using
    (tendsto_inv_atTop_zero.pow 3).comp (densityFilter_length d)

theorem density_eventually_bounded {a : ℝ → ℕ → ℝ} (ha : DensityBounded a)
    {d : ℝ} (hd : 0 ≤ d) :
    ∃ M : ℝ, ∀ᶠ p in densityFilter d, |a p.1 p.2| ≤ M := by
  obtain ⟨M, R, -, hR, hb⟩ := ha (d+1) (by linarith)
  refine ⟨M, ?_⟩
  filter_upwards [(densityFilter_length d).eventually (eventually_ge_atTop R),
    (densityFilter_density d).eventually (eventually_le_nhds (by linarith : d < d+1))] with p hp hpd
  exact hb p.1 hp p.2 ((div_le_iff₀ (pow_pos (hR.trans_le hp) 3)).1 hpd)

theorem densityFilter_bounded {a : ℝ → ℕ → ℝ} (ha : DensityBounded a)
    {d : ℝ} (hd : 0 ≤ d) :
    (densityFilter d).IsBoundedUnder (· ≤ ·) (fun p => a p.1 p.2) ∧
    (densityFilter d).IsBoundedUnder (· ≥ ·) (fun p => a p.1 p.2) := by
  obtain ⟨M, hM⟩ := density_eventually_bounded ha hd
  exact ⟨⟨M, hM.mono (fun _ h => (abs_le.mp h).2)⟩,
    ⟨-M, hM.mono (fun _ h => (abs_le.mp h).1)⟩⟩

theorem limsup_box_comparison {a : ℝ → ℕ → ℝ} (ha : DensityBounded a)
    (hbox : HasBoxInequality a) {d ℓ M : ℝ} {b H : ℕ}
    (hd : 0 ≤ d) (hℓ : 0 < ℓ) (hM : 0 ≤ M) (hb : 0 < b) (hH : 2*b ≤ H)
    (hcap : d < (ℓ+2)⁻¹^3 * H)
    (hbound : ∀ n, n ≤ H → a ℓ n ≤ M) (hbase : -M ≤ a ℓ b) :
    limsup (fun p : ℝ × ℕ => a p.1 p.2) (densityFilter d) ≤
      (ℓ+2)⁻¹^3 * ℓ^3 * a ℓ b + (2*M*ℓ^3/(b : ℝ)) * |d-(ℓ+2)⁻¹^3*b| := by
  let : Fact (0 ≤ d) := ⟨hd⟩
  have ht := (tileCount_asymptotic hℓ.le).comp (densityFilter_length d)
  have hcap' := (densityFilter_density d).eventually_lt (ht.mul_const (H : ℝ)) hcap
  have hcomp : (fun p : ℝ × ℕ => a p.1 p.2) ≤ᶠ[densityFilter d]
      (fun p : ℝ × ℕ => ((tileCount ℓ p.1 : ℝ)/p.1^3)*ℓ^3*a ℓ b +
        (2*M*ℓ^3/(b : ℝ)) * (|(p.2 : ℝ)/p.1^3 - ((tileCount ℓ p.1 : ℝ)/p.1^3)*b| + H/p.1^3)) := by
    filter_upwards [(densityFilter_length d).eventually (eventually_gt_atTop 0), hcap'] with p hp hc
    have hnc : p.2 ≤ tileCount ℓ p.1 * H := by
      have hh : (p.2 : ℝ) < (tileCount ℓ p.1 : ℝ)*H := by
        apply (div_lt_div_iff_of_pos_right (pow_pos hp 3)).mp
        simpa only [div_mul_eq_mul_div, Function.comp_def] using hc
      exact_mod_cast hh.le
    exact adjusted_box_comparison a hℓ hp hM hb hH hnc
      (fun r hr => hr ▸ hbox ℓ p.1 hℓ hp r) hbound hbase
  have htail : Tendsto (fun p : ℝ × ℕ => (H : ℝ)/p.1^3) (densityFilter d) (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using (length_inv_cube_tendsto d).const_mul (H : ℝ)
  have hlim := ((ht.mul_const (ℓ^3)).mul_const (a ℓ b)).add
    ((((densityFilter_density d).sub (ht.mul_const (b : ℝ))).abs.add htail).const_mul (2*M*ℓ^3/(b : ℝ)))
  simp only [add_zero, Function.comp_def] at hlim
  have hle := limsup_le_limsup hcomp (densityFilter_bounded ha hd).2.isCobounded_le hlim.isBoundedUnder_le
  rwa [hlim.limsup_eq] at hle

 theorem dilution_tendsto_one :
    Tendsto (fun L : ℝ => (L+2)⁻¹^3*L^3) atTop (𝓝 1) := by
  have hh : Tendsto (fun L : ℝ => 1/(1+2*L⁻¹)) atTop (𝓝 1) := by
    have hh := ((tendsto_const_nhds (x := (1 : ℝ))).div
      (tendsto_const_nhds.add (tendsto_inv_atTop_zero.const_mul 2))
        (by norm_num : (1 : ℝ)+2*0 ≠ 0))
    change Tendsto (fun L : ℝ => 1/(1+2*L⁻¹)) atTop (𝓝 (1/(1+2*0))) at hh
    simpa only [mul_zero, add_zero, div_one] using hh
  have hpow : Tendsto (fun L : ℝ => (1/(1+2*L⁻¹))^3) atTop (𝓝 1) := by
    simpa only [one_pow] using hh.pow 3
  apply hpow.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have h1 : 1+2*L⁻¹ ≠ 0 := by positivity
  have h2 : L+2 ≠ 0 := by linarith
  field_simp

theorem exists_density_limit {a : ℝ → ℕ → ℝ} (ha : DensityBounded a)
    (hbox : HasBoxInequality a) {d : ℝ} (hd : 0 < d) :
    ∃ I : ℝ, Tendsto (fun p : ℝ × ℕ => a p.1 p.2) (densityFilter d) (𝓝 I) := by
  let : Fact (0 ≤ d) := ⟨hd.le⟩
  obtain ⟨hbup, hbdown⟩ := densityFilter_bounded ha hd.le
  obtain ⟨p, hpA, hp⟩ := exists_seq_tendsto_liminf hbup.isCobounded_ge hbdown
  obtain ⟨hpL, hpd⟩ := tendsto_densityFilter_iff.mp hp
  let D : ℝ := 4*d+4
  have hD : 0 < D := by dsimp [D]; linarith
  obtain ⟨M, R, hM, hR, hbound⟩ := ha D hD
  let H : ℕ → ℕ := fun j => ⌊D*(p j).1^3⌋₊
  have hα : Tendsto (fun j => ((p j).1+2)⁻¹^3*(p j).1^3) atTop (𝓝 1) := by
    simpa only [Function.comp_def] using dilution_tendsto_one.comp hpL
  have hHratio : Tendsto (fun j => (H j : ℝ)/(p j).1^3) atTop (𝓝 D) := by
    exact (tendsto_nat_floor_mul_div_atTop hD.le).comp
      ((tendsto_pow_atTop (by norm_num : 3 ≠ 0)).comp hpL)
  have hbd : Tendsto (fun j => ((p j).1+2)⁻¹^3*((p j).2 : ℝ)) atTop (𝓝 d) := by
    have hh : Tendsto (fun j => (((p j).1+2)⁻¹^3*(p j).1^3)*
        ((p j).2 : ℝ)/(p j).1^3) atTop (𝓝 d) := by
      simpa only [one_mul, mul_div_assoc] using hα.mul hpd
    apply hh.congr'
    filter_upwards [hpL.eventually (eventually_gt_atTop 0)] with j hj
    field_simp
  have hHd : Tendsto (fun j => ((p j).1+2)⁻¹^3*(H j : ℝ)) atTop (𝓝 D) := by
    have hh := hα.mul hHratio
    simp only [one_mul] at hh
    apply hh.congr'
    filter_upwards [hpL.eventually (eventually_gt_atTop 0)] with j hj
    field_simp
  have hcoef : Tendsto (fun j => 2*M*(p j).1^3/((p j).2 : ℝ)) atTop (𝓝 (2*M/d)) := by
    have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => 2*M) atTop (𝓝 (2*M))).div hpd hd.ne'
    change Tendsto (fun j => (2*M)/(((p j).2 : ℝ)/(p j).1^3)) atTop (𝓝 (2*M/d)) at hh
    simpa only [div_div_eq_mul_div] using hh
  have hfit : ∀ᶠ j in atTop, 2*(p j).2 ≤ H j := by
    have hh := (hpd.const_mul 2).eventually_lt hHratio (show 2*d < D by dsimp [D]; linarith)
    filter_upwards [hh, hpL.eventually (eventually_gt_atTop 0)] with j hj hL
    have hh' : (2 : ℝ)*(p j).2 < H j := by
      apply (div_lt_div_iff_of_pos_right (pow_pos hL 3)).mp
      simpa only [mul_div_assoc] using hj
    exact_mod_cast hh'.le
  have hpositive : ∀ᶠ j in atTop, 0 < (p j).2 := by
    filter_upwards [hpd.eventually (eventually_gt_nhds hd),
      hpL.eventually (eventually_gt_atTop 0)] with j hj hL
    have hh : (0 : ℝ) < (p j).2 := (div_pos_iff_of_pos_right (pow_pos hL 3)).1 hj
    exact_mod_cast hh
  have hcomp : ∀ᶠ j in atTop,
      limsup (fun p : ℝ × ℕ => a p.1 p.2) (densityFilter d) ≤
        ((p j).1+2)⁻¹^3 * (p j).1^3 * a (p j).1 (p j).2 +
        (2*M*(p j).1^3/((p j).2 : ℝ)) * |d-((p j).1+2)⁻¹^3*(p j).2| := by
    filter_upwards [hpL.eventually (eventually_ge_atTop R), hfit, hpositive,
      hHd.eventually (eventually_gt_nhds (show d < D by dsimp [D]; linarith))] with j hL hfit hb hcap
    have hLpos := hR.trans_le hL
    have hHle : (H j : ℝ) ≤ D*(p j).1^3 := Nat.floor_le (by positivity)
    apply limsup_box_comparison ha hbox hd.le hLpos hM.le hb hfit hcap
    · intro n hn
      exact (abs_le.mp (hbound (p j).1 hL n ((by exact_mod_cast hn : (n : ℝ) ≤ H j).trans hHle))).2
    · have hn : (p j).2 ≤ H j := by omega
      exact (abs_le.mp (hbound (p j).1 hL (p j).2
        ((by exact_mod_cast hn : ((p j).2 : ℝ) ≤ H j).trans hHle))).1
  have hlim := (hα.mul hpA).add (hcoef.mul (((tendsto_const_nhds (x := d)).sub hbd).abs))
  simp only [one_mul, sub_self, abs_zero, mul_zero, add_zero, Function.comp_def] at hlim
  have hle := le_of_tendsto_of_tendsto tendsto_const_nhds hlim hcomp
  exact ⟨liminf (fun p : ℝ × ℕ => a p.1 p.2) (densityFilter d),
    tendsto_of_le_liminf_of_limsup_le le_rfl hle hbup hbdown⟩

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.CanonicalLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem finiteCanonical_lower_constant {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {β B L : ℝ} (hβ : 0 ≤ β) (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B*(N : ℝ) : ℝ) : EReal) ≤ energy φ x) (N : ℕ) :
    -Real.exp (β*B) ≤ finiteCanonical φ β L N := by
  have hc := (summable_grandPartition hφ hβ hL.le hstable 1 0).le_tsum N
    (fun n _ => mul_nonneg (Real.exp_pos _).le (partition_nonneg φ β L n))
  have hc' : partition φ β L N ≤ grandPartition φ 1 β 0 L := by
    simpa only [mul_zero, zero_mul, Real.exp_zero, one_mul, grandPartition] using hc
  have hZ := hc'.trans (grandPartition_le_exp hφ hβ hL.le hstable 1 0)
  simp only [mul_zero, zero_add] at hZ
  have hlog := Real.log_le_log (partition_pos hφ hβ hL hstable N) hZ
  rw [Real.log_exp] at hlog
  unfold finiteCanonical
  apply (le_div_iff₀ (pow_pos hL 3)).2
  nlinarith only [hlog]

theorem finiteCanonical_upper_trial {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {q t β B L D : ℝ} (hq : 0 < q) (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B*(N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r)
    (hL : 8*q ≤ L) (hD : D ≤ (2*q)⁻¹^3) {N : ℕ} (hN : (N : ℝ) ≤ D*L^3) :
    finiteCanonical φ β L N ≤ (β*trialEnergyConstant t q-Real.log (trialVolume q)) * (N : ℝ)/L^3 := by
  have hpos : 0 < trialVolume q ^ N * Real.exp (-β*(trialEnergyConstant t q*N)) := by
    exact mul_pos (pow_pos (trialVolume_pos hq) N) (Real.exp_pos _)
  have hlow := partition_trial_lower hφ hq ht hβ hstable hcore hL hD hN
  have hlog := Real.log_le_log hpos hlow
  rw [Real.log_mul (pow_pos (trialVolume_pos hq) N).ne' (Real.exp_pos _).ne',
    Real.log_pow, Real.log_exp] at hlog
  unfold finiteCanonical
  apply div_le_div_of_nonneg_right _ (pow_nonneg (by linarith : 0 ≤ L) 3)
  nlinarith only [hlog]

theorem finiteCanonical_densityBounded {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {t β B : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B*(N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    DensityBounded (finiteCanonical φ β) := by
  intro D hD
  let q : ℝ := (2*(D+1))⁻¹
  have hq : 0 < q := by dsimp [q]; positivity
  have hdmesh : D ≤ (2*q)⁻¹^3 := by
    have hh : (2*q)⁻¹ = D+1 := by dsimp [q]; field_simp
    rw [hh]
    nlinarith [sq_nonneg D]
  let C : ℝ := |β*trialEnergyConstant t q-Real.log (trialVolume q)|
  refine ⟨Real.exp (β*B)+C*D+1, 8*q, by dsimp [C]; positivity, by positivity, ?_⟩
  intro L hL N hN
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hlo := finiteCanonical_lower_constant hφ hβ hLpos hstable N
  have hup := finiteCanonical_upper_trial hφ hq ht hβ hstable hcore hL hdmesh hN
  have hup' : finiteCanonical φ β L N ≤ C*D := by
    calc
      _ ≤ (β*trialEnergyConstant t q-Real.log (trialVolume q)) * ((N : ℝ)/L^3) := by
        simpa only [mul_div_assoc] using hup
      _ ≤ C*((N : ℝ)/L^3) := mul_le_mul_of_nonneg_right (le_abs_self _)
        (div_nonneg (Nat.cast_nonneg _) (pow_nonneg hLpos.le 3))
      _ ≤ C*D := mul_le_mul_of_nonneg_left ((div_le_iff₀ (pow_pos hLpos 3)).2 hN) (abs_nonneg _)
  apply abs_le.mpr
  have hCD : 0 ≤ C*D := mul_nonneg (abs_nonneg _) hD.le
  have he := (Real.exp_pos (β*B)).le
  constructor <;> linarith

theorem finiteCanonical_hasBoxInequality {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {β B : ℝ} (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B*(N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hsign : ∀ r, 1 ≤ r → φ r ≤ 0) : HasBoxInequality (finiteCanonical φ β) := by
  intro ℓ L hℓ hL r
  classical
  let e : (Fin 3 → Fin ⌊L/(ℓ+2)⌋₊) ≃ Fin (tileCount ℓ L) :=
    Fintype.equivFinOfCardEq (by simp [tileCount])
  have htile := partition_tiling_lower hφ hβ hℓ.le hL.le hstable hsign (fun i => r (e i))
  rw [e.sum_comp] at htile
  have hprod := e.prod_comp (fun i => partition φ β ℓ (r i))
  rw [hprod] at htile
  have hlog := Real.log_le_log (Finset.prod_pos (fun i _ => partition_pos hφ hβ hℓ hstable (r i))) htile
  rw [Real.log_prod (fun i _ => (partition_pos hφ hβ hℓ hstable (r i)).ne')] at hlog
  unfold finiteCanonical
  calc
    -Real.log (partition φ β L (∑ i, r i))/L^3 ≤ -(∑ i, Real.log (partition φ β ℓ (r i)))/L^3 :=
      div_le_div_of_nonneg_right (neg_le_neg hlog) (pow_nonneg hL.le 3)
    _ = ℓ^3/L^3 * ∑ i, -Real.log (partition φ β ℓ (r i))/ℓ^3 := by
      rw [← Finset.sum_div, Finset.sum_neg_distrib]
      field_simp

theorem exists_canonical_density_limit {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {t β B : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B*(N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) {d : ℝ} (hd : 0 < d) :
    ∃ I : ℝ, Tendsto (fun p : ℝ × ℕ => finiteCanonical φ β p.1 p.2) (densityFilter d) (𝓝 I) := by
  apply exists_density_limit (finiteCanonical_densityBounded hφ ht hβ hstable hcore)
    (finiteCanonical_hasBoxInequality hφ hβ hstable _) hd
  intro r hr
  exact (hcore r (lt_of_lt_of_le (by norm_num) hr)).trans_eq (coreProfile_eq_zero ht hr)

theorem finiteCanonical_lower_entropy {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B L : ℝ} (hβ : 0 ≤ β) (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) (N : ℕ) :
    -β * B * ((N : ℝ) / L ^ 3) + ((N : ℝ) / L ^ 3) * Real.log ((N : ℝ) / L ^ 3)
      - (N : ℝ) / L ^ 3 ≤ finiteCanonical φ β L N := by
  by_cases hN : N = 0
  · simp [hN]
  have hh := neg_log_partition_lower hφ hβ hL hstable hN
    (fun x _ => hstable N x)
  have hh' := div_le_div_of_nonneg_right hh (pow_pos hL 3).le
  unfold finiteCanonical
  calc
    _ = (β * (-B * (N : ℝ)) + N * Real.log ((N : ℝ) / L ^ 3) - N) / L ^ 3 := by ring
    _ ≤ _ := hh'

theorem finiteCanonical_tendsto_zero_density {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    Tendsto (fun p : ℝ × ℕ => finiteCanonical φ β p.1 p.2) (densityFilter 0) (𝓝 0) := by
  have hden := densityFilter_density 0
  have hlo : Tendsto (fun p : ℝ × ℕ =>
      -β * B * ((p.2 : ℝ) / p.1 ^ 3) + ((p.2 : ℝ) / p.1 ^ 3) *
        Real.log ((p.2 : ℝ) / p.1 ^ 3) - (p.2 : ℝ) / p.1 ^ 3)
      (densityFilter 0) (𝓝 0) := by
    simpa only [mul_zero, Real.log_zero, add_zero, sub_zero, Function.comp_def] using
      ((hden.const_mul (-β * B)).add (Real.continuous_mul_log.tendsto 0 |>.comp hden)).sub hden
  let C := β * trialEnergyConstant t (1/2) - Real.log (trialVolume (1/2))
  have hup : Tendsto (fun p : ℝ × ℕ => C * ((p.2 : ℝ) / p.1 ^ 3))
      (densityFilter 0) (𝓝 0) := by
    simpa only [mul_zero] using hden.const_mul C
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup
  · filter_upwards [(densityFilter_length 0).eventually (eventually_gt_atTop 0)] with p hp
    exact finiteCanonical_lower_entropy hφ hβ hp hstable p.2
  · filter_upwards [(densityFilter_length 0).eventually (eventually_ge_atTop 4),
      hden.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))] with p hp hpd
    have hL : 0 < p.1 := by linarith
    have hh := finiteCanonical_upper_trial hφ (by norm_num : (0 : ℝ) < 1 / 2)
      ht hβ hstable hcore (by linarith : 8*(1/2 : ℝ) ≤ p.1)
      (by norm_num : (1 : ℝ) ≤ (2*(1/2))⁻¹^3)
      ((div_le_iff₀ (pow_pos hL 3)).1 hpd)
    simpa only [C, mul_div_assoc] using hh

theorem finiteCanonical_tendsto {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B d : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) (hd : 0 ≤ d) :
    Tendsto (fun p : ℝ × ℕ => finiteCanonical φ β p.1 p.2)
      (densityFilter d) (𝓝 (canonicalDensity φ β d)) := by
  let : Fact (0 ≤ d) := ⟨hd⟩
  obtain hzero | hpos := hd.eq_or_lt
  · subst d
    have hz := finiteCanonical_tendsto_zero_density hφ ht hβ hstable hcore
    simpa only [canonicalDensity, hz.liminf_eq] using hz
  · obtain ⟨I, hI⟩ := exists_canonical_density_limit hφ ht hβ hstable hcore hpos
    simpa only [canonicalDensity, hI.liminf_eq] using hI

@[simp] theorem canonicalDensity_zero {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) : canonicalDensity φ β 0 = 0 := by
  let : Fact (0 ≤ (0 : ℝ)) := ⟨le_rfl⟩
  exact (finiteCanonical_tendsto_zero_density hφ ht hβ hstable hcore).liminf_eq

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.LaplaceBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Filter Set

namespace ContinuumTemperature

theorem tsum_le_low_sector_add_tail {w b : ℕ → ℝ} (hw : Summable w) (hb : Summable b)
    (hb0 : ∀ n, 0 ≤ b n) {M : ℕ} {A : ℝ}
    (hlow : ∀ n, n < M → w n ≤ A) (hhigh : ∀ n, M ≤ n → w n ≤ b n) :
    ∑' n, w n ≤ (M : ℝ)*A + ∑' n, b n := by
  have hst : Summable (fun n : ℕ => w (n+M)) :=
    hw.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hbt : Summable (fun n : ℕ => b (n+M)) :=
    hb.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have ht : (∑' n : ℕ, w (n+M)) ≤ ∑' n : ℕ, b (n+M) :=
    hst.tsum_le_tsum (fun n => hhigh _ (Nat.le_add_left M n)) hbt
  have htail : (∑' n : ℕ, b (n+M)) ≤ ∑' n, b n := by
    rw [← hb.sum_add_tsum_nat_add M]
    exact le_add_of_nonneg_left (Finset.sum_nonneg (fun n _ => hb0 n))
  have hsum : (∑ n ∈ Finset.range M, w n) ≤ (M : ℝ)*A := by
    calc
      (∑ n ∈ Finset.range M, w n) ≤ ∑ n ∈ Finset.range M, A :=
        Finset.sum_le_sum (fun n hn => hlow n (Finset.mem_range.mp hn))
      _ = _ := by simp
  rw [← hw.sum_add_tsum_nat_add M]
  exact add_le_add hsum (ht.trans htail)

theorem log_affine_cube_div_tendsto_zero {D C : ℝ} (hD : 0 < D) :
    Tendsto (fun L : ℝ => Real.log (D*L^3+C)/L^3) atTop (𝓝 0) := by
  have hv : Tendsto (fun L : ℝ => L^3) atTop atTop := tendsto_pow_atTop (by norm_num)
  have hz : Tendsto (fun L : ℝ => D*L^3+C) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop C (hv.const_mul_atTop hD)
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hz
  have hi : Tendsto (fun L : ℝ => (L^3)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hv
  have hr : Tendsto (fun L : ℝ => D+C*(L^3)⁻¹) atTop (𝓝 D) := by
    simpa only [mul_zero, add_zero] using tendsto_const_nhds.add (hi.const_mul C)
  have hh := hlog.mul hr
  simp only [zero_mul] at hh
  apply hh.congr'
  filter_upwards [hv.eventually (eventually_gt_atTop 0), hz.eventually (eventually_gt_atTop 0)] with L hL hzL
  change Real.log (D*L^3+C)/(D*L^3+C)*(D+C*(L^3)⁻¹) = _
  have hn : L ≠ 0 := by rintro rfl; simp at hL
  field_simp [hn, ne_of_gt hzL]

theorem log_tsum_div_le {w b : ℕ → ℝ} (hw : Summable w) (hb : Summable b)
    (hb0 : ∀ n, 0 ≤ b n) (hpos : 0 < ∑' n, w n) {M : ℕ} (hM : 0 < M)
    {V c : ℝ} (hV : 0 < V) (hc : 0 ≤ c)
    (hlow : ∀ n, n < M → w n ≤ Real.exp (V*c))
    (hhigh : ∀ n, M ≤ n → w n ≤ b n) :
    Real.log (∑' n, w n)/V ≤ c + Real.log ((M : ℝ)+∑' n, b n)/V := by
  have hbS : 0 ≤ ∑' n, b n := tsum_nonneg hb0
  have he : 1 ≤ Real.exp (V*c) := Real.one_le_exp (mul_nonneg hV.le hc)
  have hbound := tsum_le_low_sector_add_tail hw hb hb0 hlow hhigh
  have hbound' : ∑' n, w n ≤ ((M : ℝ)+∑' n, b n)*Real.exp (V*c) := by
    have hh := mul_le_mul_of_nonneg_left he hbS
    nlinarith only [hbound, hh]
  have hp : 0 < (M : ℝ)+∑' n, b n := by positivity
  have hlog := Real.log_le_log hpos hbound'
  rw [Real.log_mul hp.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  calc
    Real.log (∑' n, w n)/V ≤ (Real.log ((M : ℝ)+∑' n, b n)+V*c)/V :=
      div_le_div_of_nonneg_right hlog hV.le
    _ = _ := by field_simp; ring

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.LaplacePrinciple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem density_compact_eventually {K : Set ℝ} (hK : IsCompact K)
    {P : ℝ × ℕ → Prop} (hP : ∀ d ∈ K, ∀ᶠ p in densityFilter d, P p) :
    ∀ᶠ L in atTop, ∀ n : ℕ, (n : ℝ)/L^3 ∈ K → P (L,n) := by
  have hp : ∀ᶠ p in Filter.comap
      (fun p : ℝ × ℕ => (p.1, (p.2 : ℝ)/p.1^3)) (atTop ×ˢ 𝓝ˢ K), P p := by
    rw [hK.prod_nhdsSet_eq_biSup, comap_iSup]
    simp only [comap_iSup, eventually_iSup]
    exact hP
  obtain ⟨S, hS, hsub⟩ := Filter.mem_comap.mp hp
  obtain ⟨T, hT, U, hU, hTU⟩ := Filter.mem_prod_iff.mp hS
  filter_upwards [hT] with L hL
  intro n hn
  exact hsub (hTU ⟨hL, (subset_of_mem_nhdsSet hU) hn⟩)

theorem canonicalDensity_lower_entropy {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B d : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) (hd : 0 ≤ d) :
    d*Real.log d-(β*B+1)*d ≤ canonicalDensity φ β d := by
  let : Fact (0 ≤ d) := ⟨hd⟩
  have hlim := finiteCanonical_tendsto hφ ht hβ hstable hcore hd
  have he := ((Real.continuous_mul_log.continuousAt.tendsto).comp
    (densityFilter_density d)).sub ((densityFilter_density d).const_mul (β*B+1))
  apply le_of_tendsto_of_tendsto he hlim
  filter_upwards [(densityFilter_length d).eventually (eventually_gt_atTop 0)] with p hp
  have hh := finiteCanonical_lower_entropy hφ hβ hp hstable p.2
  dsimp only [Function.comp_def] at *
  nlinarith only [hh]

theorem entropy_dual_bound (c : ℝ) {d : ℝ} (hd : 0 ≤ d) :
    (c+1)*d-d*Real.log d ≤ Real.exp c := by
  obtain rfl | hd := hd.eq_or_lt
  · simp only [mul_zero, zero_mul, sub_self]
    exact (Real.exp_pos c).le
  have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (c-Real.log d)) hd.le
  rw [Real.exp_sub, Real.exp_log hd, div_mul_cancel₀ _ hd.ne'] at hh
  nlinarith only [hh]

theorem canonicalPressure_bddAbove {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B μ : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    BddAbove ((fun d : ℝ => μ*d-canonicalDensity φ β d) '' Ici 0) := by
  refine ⟨Real.exp (μ+β*B), ?_⟩
  rintro _ ⟨d, hd, rfl⟩
  have hh := canonicalDensity_lower_entropy hφ ht hβ hstable hcore hd
  have he := entropy_dual_bound (μ+β*B) hd
  linarith

theorem laplace_low_sector {w : ℝ → ℕ → ℝ} {F : ℝ → ℝ} {D S ε : ℝ}
    (hw : ∀ L > 0, ∀ n, 0 < w L n) (hD : 0 < D) (hε : 0 < ε)
    (hF : ∀ d, 0 ≤ d → F d ≤ S)
    (hlim : ∀ d, 0 ≤ d → Tendsto (fun p : ℝ × ℕ => Real.log (w p.1 p.2)/p.1^3)
      (densityFilter d) (𝓝 (F d))) :
    ∀ᶠ L in atTop, ∀ n : ℕ, n < ⌊D*L^3⌋₊+1 →
      w L n ≤ Real.exp (L^3*(S+ε)) := by
  have he : ∀ᶠ L in atTop, ∀ n : ℕ, (n : ℝ)/L^3 ∈ Icc 0 D →
      Real.log (w L n)/L^3 < S+ε := by
    apply density_compact_eventually (K := Icc 0 D)
      (P := fun p => Real.log (w p.1 p.2)/p.1^3 < S+ε) isCompact_Icc
    intro d hd
    apply (hlim d hd.1).eventually_lt_const
    linarith [hF d hd.1]
  filter_upwards [he, eventually_gt_atTop 0] with L hL hp
  intro n hn
  have hn' : (n : ℝ) ≤ D*L^3 :=
    (Nat.cast_le.mpr (Nat.lt_succ_iff.mp hn)).trans (Nat.floor_le (by positivity))
  have hr : (n : ℝ)/L^3 ∈ Icc 0 D :=
    ⟨div_nonneg (Nat.cast_nonneg n) (pow_pos hp 3).le, (div_le_iff₀ (pow_pos hp 3)).2 hn'⟩
  apply (Real.log_le_iff_le_exp (hw L hp n)).1
  have hh := (div_lt_iff₀ (pow_pos hp 3)).1 (hL n hr)
  nlinarith only [hh]

theorem laplace_upper_eventually {w : ℝ → ℕ → ℝ} {F : ℝ → ℝ} {b : ℕ → ℝ}
    {D S : ℝ}
    (hw : ∀ L > 0, ∀ n, 0 < w L n) (hsum : ∀ L > 0, Summable (w L))
    (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n) (hD : 0 < D) (hS : 0 ≤ S)
    (hF : ∀ d, 0 ≤ d → F d ≤ S)
    (hlim : ∀ d, 0 ≤ d → Tendsto (fun p : ℝ × ℕ => Real.log (w p.1 p.2)/p.1^3)
      (densityFilter d) (𝓝 (F d)))
    (htail : ∀ᶠ L in atTop, ∀ n : ℕ, D ≤ (n : ℝ)/L^3 → w L n ≤ b n) :
    ∀ q > S, ∀ᶠ L in atTop, Real.log (∑' n, w L n)/L^3 < q := by
  intro q hq
  let ε := (q-S)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hlog := log_affine_cube_div_tendsto_zero (C := 1+∑' n, b n) hD
  have he := hlog.eventually_lt_const hε
  filter_upwards [laplace_low_sector hw hD hε hF hlim, htail, he,
    eventually_gt_atTop 0] with L hlow hhigh hsmall hL
  let M : ℕ := ⌊D*L^3⌋₊+1
  have hV : 0 < L^3 := pow_pos hL 3
  have hpos : 0 < ∑' n, w L n :=
    (hw L hL 0).trans_le ((hsum L hL).le_tsum 0 (fun n _ => (hw L hL n).le))
  have hh := log_tsum_div_le (hsum L hL) hb hb0 hpos (Nat.succ_pos _ : 0 < M)
    hV (show 0 ≤ S+ε by linarith) hlow (fun n hn => hhigh n (by
      apply (le_div_iff₀ hV).2
      have hm : D*L^3 < (M : ℝ) := by simpa [M] using Nat.lt_floor_add_one (D*L^3)
      exact hm.le.trans (Nat.cast_le.mpr hn)))
  have hbS : 0 ≤ ∑' n, b n := tsum_nonneg hb0
  have hM : (M : ℝ)+∑' n, b n ≤ D*L^3+(1+∑' n, b n) := by
    have hf := Nat.floor_le (mul_nonneg hD.le hV.le)
    dsimp [M]
    push_cast
    linarith
  have hMpos : 0 < (M : ℝ)+∑' n, b n := by
    have hp : 0 < (M : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos _)
    linarith
  have hl := div_le_div_of_nonneg_right (Real.log_le_log hMpos hM) hV.le
  dsimp [ε] at *
  linarith only [hh, hl, hsmall]

theorem laplace_principle {w : ℝ → ℕ → ℝ} {F : ℝ → ℝ} {b : ℕ → ℝ} {D : ℝ}
    (hw : ∀ L > 0, ∀ n, 0 < w L n) (hsum : ∀ L > 0, Summable (w L))
    (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n) (hD : 0 < D) (hF0 : F 0 = 0)
    (hbdd : BddAbove (F '' Ici 0))
    (hlim : ∀ d, 0 ≤ d → Tendsto (fun p : ℝ × ℕ => Real.log (w p.1 p.2)/p.1^3)
      (densityFilter d) (𝓝 (F d)))
    (htail : ∀ᶠ L in atTop, ∀ n : ℕ, D ≤ (n : ℝ)/L^3 → w L n ≤ b n) :
    Tendsto (fun L => Real.log (∑' n, w L n)/L^3) atTop (𝓝 (sSup (F '' Ici 0))) := by
  have hnon : (F '' Ici 0).Nonempty := ⟨F 0, ⟨0, by simp, rfl⟩⟩
  have hF : ∀ d, 0 ≤ d → F d ≤ sSup (F '' Ici 0) :=
    fun d hd => le_csSup hbdd ⟨d, hd, rfl⟩
  have hS : 0 ≤ sSup (F '' Ici 0) := by simpa [hF0] using hF 0 le_rfl
  apply tendsto_order.2
  constructor
  · intro q hq
    obtain ⟨_, ⟨d, hd, rfl⟩, hqd⟩ := exists_lt_of_lt_csSup hnon hq
    have hdlim := (hlim d hd).comp (floor_density_tendsto hd)
    filter_upwards [hdlim.eventually_const_lt hqd, eventually_gt_atTop 0] with L hL hp
    have hh := (hsum L hp).le_tsum ⌊d*L^3⌋₊ (fun n _ => (hw L hp n).le)
    exact hL.trans_le (div_le_div_of_nonneg_right (Real.log_le_log (hw L hp _) hh)
      (pow_pos hp 3).le)
  · exact laplace_upper_eventually hw hsum hb hb0 hD hS hF hlim htail

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PhysicalPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem log_grand_weight_div {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B L μ : ℝ} (hβ : 0 ≤ β) (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) (N : ℕ) :
    Real.log (Real.exp (μ*N)*partition φ β L N)/L^3 =
      μ*((N : ℝ)/L^3)-finiteCanonical φ β L N := by
  rw [Real.log_mul (Real.exp_pos _).ne' (partition_pos hφ hβ hL hstable N).ne',
    Real.log_exp]
  unfold finiteCanonical
  ring

theorem grand_weight_high_density {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B L μ : ℝ} (hβ : 0 ≤ β) (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) {N : ℕ}
    (hN : Real.exp (μ+β*B+2) ≤ (N : ℝ)/L^3) :
    Real.exp (μ*N)*partition φ β L N ≤ (Real.exp (-1))^N := by
  have hden : 0 ≤ (N : ℝ)/L^3 := div_nonneg (Nat.cast_nonneg _) (pow_pos hL 3).le
  have hlog := Real.log_le_log (Real.exp_pos (μ+β*B+2)) hN
  rw [Real.log_exp] at hlog
  have he := finiteCanonical_lower_entropy hφ hβ hL hstable N
  have hm := mul_le_mul_of_nonneg_right hlog hden
  have hbound : μ*((N : ℝ)/L^3)-finiteCanonical φ β L N ≤ -((N : ℝ)/L^3) := by
    nlinarith only [he, hm]
  rw [← log_grand_weight_div hφ hβ hL hstable N, ← neg_div] at hbound
  have hh := (div_le_div_iff_of_pos_right (pow_pos hL 3)).1 hbound
  have hw : 0 < Real.exp (μ*N)*partition φ β L N :=
    mul_pos (Real.exp_pos _) (partition_pos hφ hβ hL hstable N)
  rw [← Real.exp_nat_mul]
  apply (Real.log_le_iff_le_exp hw).1
  simpa using hh

theorem grandPartition_pressure_tendsto {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B μ : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    Tendsto (fun L => Real.log (grandPartition φ 1 β μ L)/L^3) atTop
      (𝓝 (canonicalPressure φ β μ)) := by
  have hw : ∀ L > 0, ∀ N : ℕ, 0 < Real.exp (μ*N)*partition φ β L N :=
    fun L hL N => mul_pos (Real.exp_pos _) (partition_pos hφ hβ hL hstable N)
  have hs : ∀ L > 0, Summable (fun N : ℕ => Real.exp (μ*N)*partition φ β L N) := by
    intro L hL
    simpa only [one_mul] using summable_grandPartition hφ hβ hL.le hstable 1 μ
  have hb : Summable (fun n : ℕ => (Real.exp (-1))^n) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (by simp)
  have hz : μ*0-canonicalDensity φ β 0 = 0 := by
    rw [canonicalDensity_zero hφ ht hβ hstable hcore]; ring
  have hlim : ∀ d, 0 ≤ d →
      Tendsto (fun p : ℝ × ℕ => Real.log (Real.exp (μ*p.2)*partition φ β p.1 p.2)/p.1^3)
        (densityFilter d) (𝓝 (μ*d-canonicalDensity φ β d)) := by
    intro d hd
    have hh := ((densityFilter_density d).const_mul μ).sub
      (finiteCanonical_tendsto hφ ht hβ hstable hcore hd)
    apply hh.congr'
    filter_upwards [(densityFilter_length d).eventually (eventually_gt_atTop 0)] with p hp
    exact (log_grand_weight_div hφ hβ hp hstable p.2).symm
  have ht' : ∀ᶠ L in atTop, ∀ N : ℕ, Real.exp (μ+β*B+2) ≤ (N : ℝ)/L^3 →
      Real.exp (μ*N)*partition φ β L N ≤ (Real.exp (-1))^N := by
    filter_upwards [eventually_gt_atTop 0] with L hL
    exact fun _ hN => grand_weight_high_density hφ hβ hL hstable hN
  have hh := laplace_principle hw hs hb (fun n => (pow_pos (Real.exp_pos _) n).le)
    (Real.exp_pos (μ+β*B+2)) hz (canonicalPressure_bddAbove hφ ht hβ hstable hcore) hlim ht'
  simpa only [grandPartition, one_mul, canonicalPressure] using hh

theorem physicalPressure_tendsto {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B h : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    Tendsto (fun L => Real.log (grandPartition φ t β h L)/(t*L^3)) atTop
      (𝓝 (physicalPressure φ t (β,h))) := by
  change Tendsto _ atTop (𝓝 (canonicalPressure φ β (t*h)/t))
  have hh := (grandPartition_pressure_tendsto hφ ht hβ hstable hcore (μ := t*h)).div_const t
  convert hh using 1
  ext L
  simp only [grandPartition, one_mul]
  ring

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ExactAssignments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
section
variable {X : Type u_1} [MeasurableSpace X] {ι : Type u_2} [Fintype ι] [DecidableEq ι]

omit [MeasurableSpace X] [Fintype ι] in
theorem binaryRegion_subset_union (A B : Set X) (s : Finset ι) :
    binaryRegion A B s ⊆ {x : ι → X | ∀ i, x i ∈ A ∪ B} := by
  intro x hx i
  by_cases hi : i ∈ s
  · exact Or.inl (by simpa only [ite_eq_left hi] using hx i)
  · exact Or.inr (by simpa only [ite_eq_right hi] using hx i)

omit [MeasurableSpace X] in

theorem iUnion_binaryRegion (A B : Set X) :
    (⋃ s : Finset ι, binaryRegion A B s) = {x : ι → X | ∀ i, x i ∈ A ∪ B} := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs⟩ := mem_iUnion.mp hx
    exact binaryRegion_subset_union A B s hs
  · intro hx
    refine mem_iUnion.mpr ⟨Finset.univ.filter (fun i => x i ∈ A), ?_⟩
    intro i
    by_cases hi : x i ∈ A
    · simpa only [Finset.mem_filter, Finset.mem_univ, true_and, ite_eq_left hi] using hi
    · simpa only [Finset.mem_filter, Finset.mem_univ, true_and, ite_eq_right hi] using
        (hx i).resolve_left hi

theorem integral_binary_assignments_eq (μ : Measure X) [SigmaFinite μ]
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B)
    {F : (ι → X) → ℝ}
    (hF : IntegrableOn F {x : ι → X | ∀ i, x i ∈ A ∪ B} (Measure.pi (fun _ : ι => μ))) :
    (∫ x in {x : ι → X | ∀ i, x i ∈ A ∪ B}, F x ∂(Measure.pi (fun _ : ι => μ))) =
      ∑ s : Finset ι, ∫ x in binaryRegion A B s, F x ∂(Measure.pi (fun _ : ι => μ)) := by
  have hh := integral_biUnion_finset (Finset.univ : Finset (Finset ι))
    (fun s _ => measurableSet_binaryRegion hA hB s)
    (fun _ _ _ _ hne => binaryRegion_pairwiseDisjoint hd hne)
    (fun s _ => hF.mono_set (binaryRegion_subset_union A B s))
  simpa only [Finset.mem_univ, iUnion_true, iUnion_binaryRegion] using hh

end
end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GeneralGrand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem familyIntegral_relabel (F : ConfigFamily) (hF : RelabelInvariant F)
    (A : Set Space) {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) :
    familyIntegral F A ι = familyIntegral F A κ := by
  let p : (ι → Space) ≃ᵐ (κ → Space) := MeasurableEquiv.piCongrLeft (fun _ : κ => Space) e
  have hp : MeasurePreserving p volume volume := by
    simpa only [volume_pi] using measurePreserving_piCongrLeft (fun _ : κ => volume) e
  have hpx (x : ι → Space) : p x = x ∘ e.symm := by
    funext i
    simpa only [p, Equiv.apply_symm_apply, Function.comp_apply] using
      (MeasurableEquiv.piCongrLeft_apply_apply e (β := fun _ : κ => Space) x (e.symm i))
  have heq := hp.setIntegral_preimage_emb p.measurableEmbedding (F κ)
    {x : κ → Space | ∀ i, x i ∈ A}
  have hpre : p ⁻¹' {x : κ → Space | ∀ i, x i ∈ A} =
      {x : ι → Space | ∀ i, x i ∈ A} := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq, hpx, Function.comp_apply]
    constructor
    · intro hh i
      simpa only [Equiv.symm_apply_apply] using hh (e i)
    · intro hh i
      exact hh (e.symm i)
  rw [hpre] at heq
  simpa only [familyIntegral, hpx, hF κ ι e.symm] using heq

theorem familyIntegral_eq_Fin (F : ConfigFamily) (hF : RelabelInvariant F)
    (A : Set Space) (ι : Type) [Fintype ι] :
    familyIntegral F A ι = familyIntegral F A (Fin (Fintype.card ι)) :=
  familyIntegral_relabel F hF A (Fintype.equivFin ι)

theorem integral_binary_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    {A B : Set Space} (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B)
    {F : (ι → Space) → ℝ} (a b : ℕ → ℝ)
    (hF : IntegrableOn F {x : ι → Space | ∀ i, x i ∈ A ∪ B})
    (hbound : ∀ s : Finset ι, (∫ x in binaryRegion A B s, F x) ≤
      a s.card*b (Fintype.card ι-s.card)) :
    (∫ x in {x : ι → Space | ∀ i, x i ∈ A ∪ B}, F x) ≤
      ∑ k ∈ Finset.range (Fintype.card ι+1),
        ((Fintype.card ι).choose k : ℝ)*a k*b (Fintype.card ι-k) := by
  rw [show volume = Measure.pi (fun _ : ι => (volume : Measure Space)) by exact volume_pi]
  rw [integral_binary_assignments_eq volume hA hB hd (by simpa only [← volume_pi] using hF)]
  calc
    _ ≤ ∑ s : Finset ι, a s.card*b (Fintype.card ι-s.card) := by
      apply Finset.sum_le_sum
      intro s _
      simpa only [← volume_pi] using hbound s
    _ = _ := by
      have hh := Finset.sum_powerset_apply_card (fun k => a k*b (Fintype.card ι-k))
        (x := (Finset.univ : Finset ι))
      simpa only [Finset.powerset_univ, Finset.card_univ, nsmul_eq_mul, mul_assoc] using hh

theorem factorial_binomial_sum (a b : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range (N+1), (N.choose k : ℝ)*a k*b (N-k))/(N.factorial : ℝ) =
      ∑ k ∈ Finset.range (N+1), (a k/(k.factorial : ℝ))*(b (N-k)/((N-k).factorial : ℝ)) := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.cast_choose ℝ (by have := Finset.mem_range.mp hk; omega)]
  have hN : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
  field_simp

theorem familyTerm_nonneg (F : ConfigFamily) (A : Set Space)
    (hF : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x) (n : ℕ) :
    0 ≤ familyTerm F A n := by
  apply div_nonneg (integral_nonneg (hF (Fin n)))
  positivity

theorem integrableOn_family_of_bound (F : ConfigFamily) {A : Set Space}
    (hA : volume A ≠ ⊤) {ι : Type} [Fintype ι]
    (hFm : Measurable (F ι)) (hF0 : ∀ x, 0 ≤ F ι x)
    {C : ℝ} (hbound : ∀ x, F ι x ≤ C) :
    IntegrableOn (F ι) {x : ι → Space | ∀ i, x i ∈ A} := by
  have hvol : volume {x : ι → Space | ∀ i, x i ∈ A} ≠ ⊤ := by
    rw [volume_generalConfigurations]
    exact ENNReal.pow_ne_top hA
  let : IsFiniteMeasure (volume.restrict {x : ι → Space | ∀ i, x i ∈ A}) := ⟨by
    simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hvol⟩
  apply (integrable_const C).mono' hFm.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (hF0 x)]
  exact hbound x

theorem familyTerm_le_exponential (F : ConfigFamily) {A : Set Space}
    (hA : volume A ≠ ⊤) {d : ℝ}
    (hFm : ∀ (ι : Type) [Fintype ι], Measurable (F ι))
    (hF0 : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (hbound : ∀ (ι : Type) [Fintype ι] (x : ι → Space),
      F ι x ≤ Real.exp (d*Fintype.card ι)) (n : ℕ) :
    familyTerm F A n ≤ (volume.real A*Real.exp d)^n/(n.factorial : ℝ) := by
  have hvol : volume {x : Fin n → Space | ∀ i, x i ∈ A} ≠ ⊤ := by
    rw [volume_generalConfigurations]
    exact ENNReal.pow_ne_top hA
  let : IsFiniteMeasure (volume.restrict {x : Fin n → Space | ∀ i, x i ∈ A}) := ⟨by
    simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hvol⟩
  have hh := integral_mono (integrableOn_family_of_bound F hA (hFm (Fin n))
    (hF0 (Fin n)) (hbound (Fin n))) (integrable_const _) (hbound (Fin n))
  have hn : (0 : ℝ) ≤ n.factorial := Nat.cast_nonneg _
  apply (div_le_div_of_nonneg_right hh hn).trans_eq
  rw [setIntegral_const, Measure.real, volume_generalConfigurations, ENNReal.toReal_pow,
    Fintype.card_fin, smul_eq_mul, mul_comm d (n : ℝ), Real.exp_nat_mul, mul_pow]
  rfl

theorem summable_familyTerm_of_bound (F : ConfigFamily) {A : Set Space}
    (hA : volume A ≠ ⊤) {d : ℝ}
    (hFm : ∀ (ι : Type) [Fintype ι], Measurable (F ι))
    (hF0 : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (hbound : ∀ (ι : Type) [Fintype ι] (x : ι → Space),
      F ι x ≤ Real.exp (d*Fintype.card ι)) : Summable (familyTerm F A) :=
  Summable.of_nonneg_of_le (familyTerm_nonneg F A hF0)
    (familyTerm_le_exponential F hA hFm hF0 hbound)
    (Real.summable_pow_div_factorial _)

theorem tsum_le_convolution {f a b : ℕ → ℝ} (hf : Summable f)
    (ha : Summable a) (hb : Summable b)
    (hle : ∀ n, f n ≤ ∑ k ∈ Finset.range (n+1), a k*b (n-k)) :
    (∑' n, f n) ≤ (∑' n, a n)*(∑' n, b n) := by
  have hab : Summable (fun p : ℕ × ℕ => a p.1*b p.2) :=
    summable_mul_of_summable_norm (summable_norm_iff.mpr ha) (summable_norm_iff.mpr hb)
  rw [ha.tsum_mul_tsum_eq_tsum_sum_range hb hab]
  exact hf.tsum_le_tsum hle (summable_sum_mul_range_of_summable_mul hab)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GenericGibbs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem occupation_eq_sum {ι : Type} [Fintype ι] (C : Set Space) (x : ι → Space) :
    occupation C x = ∑ i, if x i ∈ C then (1 : ℝ) else 0 := by
  classical
  simp only [occupation, ← Finset.sum_boole, Fintype.card_subtype]

theorem measurable_occupation {ι : Type} [Fintype ι] {C : Set Space} (hC : MeasurableSet C) :
    Measurable (fun x : ι → Space => occupation C x) := by
  classical
  simp_rw [occupation_eq_sum]
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite (hC.preimage (measurable_pi_apply i)) measurable_const measurable_const

theorem occupation_relabel {ι κ : Type} [Fintype ι] [Fintype κ]
    (C : Set Space) (e : ι ≃ κ) (x : κ → Space) : occupation C (x ∘ e) = occupation C x := by
  classical
  simp_rw [occupation_eq_sum, Function.comp_apply]
  exact Equiv.sum_comp e (fun i => if x i ∈ C then (1 : ℝ) else 0)

theorem occupation_subtype_compl {ι : Type} [Fintype ι] (C : Set Space)
    (s : Finset ι) (x : ι → Space) (h : ∀ i ∈ s, x i ∉ C) :
    occupation C (fun i : {i // i ∉ s} => x i) = occupation C x := by
  classical
  rw [occupation_eq_sum, occupation_eq_sum]
  have hh := Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ s)
    (fun i => if x i ∈ C then (1 : ℝ) else 0)
  have hz : (∑ i : {i // i ∈ s}, if x i ∈ C then (1 : ℝ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact ite_eq_right (h i i.property)
  have hfi : Subtype.fintype (fun i : ι => i ∈ s) = Finset.Subtype.fintype s :=
    Subsingleton.elim _ _
  rw [hfi] at hh
  simpa only [hz, zero_add] using hh

theorem gibbsEnergy_relabel (V : Space → Space → ℝ) {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (x : κ → Space) : gibbsEnergy V (x ∘ e) = gibbsEnergy V x := by
  classical
  unfold gibbsEnergy
  simp only [Function.comp_apply, ← e.injective.eq_iff]
  congr 1
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro i _
  exact Equiv.sum_comp e (fun j => if e i = j then 0 else V (x (e i)) (x j))

theorem gibbsFamily_relabel (V : Space → Space → ℝ) (β h : ℝ) :
    RelabelInvariant (gibbsFamily V β h) := by
  intro ι κ _ _ e x
  have hh : Function.Injective (x ∘ e) ↔ Function.Injective x := by
    constructor
    · intro hx i j hij
      obtain ⟨i, rfl⟩ := e.surjective i
      obtain ⟨j, rfl⟩ := e.surjective j
      exact congrArg e (hx hij)
    · exact fun hx => hx.comp e.injective
  simp only [gibbsFamily, hh, gibbsEnergy_relabel, Fintype.card_congr e]

theorem gibbsFamily_nonneg (V : Space → Space → ℝ) (β h : ℝ) (ι : Type) [Fintype ι]
    (x : ι → Space) : 0 ≤ gibbsFamily V β h ι x := by
  unfold gibbsFamily
  split_ifs
  · exact (Real.exp_pos _).le
  · rfl

theorem gibbsEnergy_split (V : Space → Space → ℝ) (hsym : ∀ x y, V x y = V y x)
    {ι : Type} [Fintype ι] (p : ι → Prop) [DecidablePred p] (x : ι → Space) :
    gibbsEnergy V x = gibbsEnergy V (fun i : {i // p i} => x i) +
      gibbsEnergy V (fun i : {i // ¬p i} => x i) +
      ∑ i : {i // p i}, ∑ j : {j // ¬p j}, V (x i) (x j) := by
  classical
  have heq := symmetric_matrix_split p (fun i j => if i = j then 0 else V (x i) (x j))
    (fun i j => by by_cases hh : i = j <;> simp [hh, eq_comm, hsym])
  have hcross (i : {i // p i}) (j : {j // ¬p j}) : (i : ι) ≠ j := by
    intro hh
    exact j.property (hh ▸ i.property)
  have hself (a b : {i // p i}) : ((a : ι) = b) ↔ a = b := Subtype.coe_inj
  have hself' (a b : {i // ¬p i}) : ((a : ι) = b) ↔ a = b := Subtype.coe_inj
  unfold gibbsEnergy
  rw [heq]
  simp only [hself, hself', hcross, ite_false]
  ring

theorem measurable_gibbsEnergy {V : Space → Space → ℝ}
    (hV : Measurable (Function.uncurry V)) {ι : Type} [Fintype ι] :
    Measurable (fun x : ι → Space => gibbsEnergy V x) := by
  unfold gibbsEnergy
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  by_cases hij : i = j
  · simp only [ite_eq_left hij]
    exact measurable_const
  · simp only [ite_eq_right hij]
    have hp : Measurable (fun x : ι → Space => (x i, x j)) :=
      (measurable_pi_apply i).prodMk (measurable_pi_apply j)
    exact hV.comp hp

theorem measurableSet_injective_config (ι : Type) [Fintype ι] :
    MeasurableSet {x : ι → Space | Function.Injective x} := by
  have he : {x : ι → Space | Function.Injective x} =
      ⋂ i : ι, ⋂ j : ι, {x : ι → Space | x i = x j → i = j} := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter, Function.Injective]
  rw [he]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  by_cases hij : i = j
  · simp only [hij, implies_true, ofPred_true]
    exact MeasurableSet.univ
  · have hm : MeasurableSet {x : ι → Space | x i = x j} :=
      measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)
    convert hm.compl using 1
    ext x
    simp [hij]

theorem measurable_gibbsFamily {V : Space → Space → ℝ}
    (hV : Measurable (Function.uncurry V)) (β h : ℝ) (ι : Type) [Fintype ι] :
    Measurable (gibbsFamily V β h ι) := by
  apply Measurable.ite (measurableSet_injective_config ι) _ measurable_const
  exact (measurable_const.sub (measurable_const.mul (measurable_gibbsEnergy hV))).exp

theorem momentFamily_nonneg (F : ConfigFamily)
    (hF : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (C : Set Space) (c : ℝ) (ι : Type) [Fintype ι] (x : ι → Space) :
    0 ≤ momentFamily F C c ι x := mul_nonneg (hF ι x) (Real.exp_pos _).le

theorem measurable_momentFamily (F : ConfigFamily) {C : Set Space} (hC : MeasurableSet C)
    (c : ℝ) {ι : Type} [Fintype ι] (hF : Measurable (F ι)) :
    Measurable (momentFamily F C c ι) :=
  hF.mul ((measurable_occupation hC).pow_const 2 |>.const_mul c |>.exp)

theorem gibbs_moment_stable_bound (V : Space → Space → ℝ) (β h B c : ℝ)
    (C : Set Space) {ι : Type} [Fintype ι] (x : ι → Space)
    (hbound : c*(occupation C x)^2 ≤ β*gibbsEnergy V x+β*B*Fintype.card ι) :
    momentFamily (gibbsFamily V β h) C c ι x ≤
      Real.exp ((h+β*B)*Fintype.card ι) := by
  by_cases hx : Function.Injective x
  · simp only [momentFamily, gibbsFamily, ite_eq_left hx, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [hbound]
  · simp only [momentFamily, gibbsFamily, ite_eq_right hx, zero_mul]
    exact (Real.exp_pos _).le

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.MomentEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem measurable_cellIndex : Measurable cellIndex := by
  apply Measurable.of_eval
  intro k
  exact ((EuclideanSpace.proj k).continuous.measurable.const_mul 4).floor

theorem measurableSet_latticeCell (z : Lattice) : MeasurableSet (latticeCell z) :=
  measurable_cellIndex (measurableSet_singleton z)

theorem gibbsEnergy_eq_pairSum (V : Space → Space → ℝ)
    (hV : ∀ x y, V x y = V y x) {ι : Type} [Fintype ι] [LinearOrder ι] (x : ι → Space) :
    gibbsEnergy V x = pairSum (fun i j => V (x i) (x j)) := by
  have hh := two_mul_pairSum (fun i j => V (x i) (x j)) (fun i j => hV (x i) (x j))
  unfold gibbsEnergy
  apply (div_eq_iff (by norm_num : (2 : ℝ) ≠ 0)).2
  rw [mul_comm]
  convert hh.symm using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j <;> simp only [hij, ite_eq_left, ite_false]

theorem gibbsEnergy_sub (U W : Space → Space → ℝ) {ι : Type} [Fintype ι] (x : ι → Space) :
    gibbsEnergy (fun x y => U x y-W x y) x = gibbsEnergy U x-gibbsEnergy W x := by
  unfold gibbsEnergy
  have he (i j : ι) : (if i = j then 0 else U (x i) (x j)-W (x i) (x j)) =
      (if i = j then 0 else U (x i) (x j))-(if i = j then 0 else W (x i) (x j)) := by
    split_ifs <;> ring
  simp_rw [he, Finset.sum_sub_distrib]
  ring

theorem physical_gibbs_moment_energy {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n) ≤ (t^2/8)/8)
    {ι : Type} [Fintype ι] (x : ι → Space) (z : Lattice) :
    (t^2/8)/4*(occupation (latticeCell z) x)^2 ≤
      gibbsEnergy (fun x y => physicalProfile t σ R ‖x-y‖) x+t^2/2*Fintype.card ι := by
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  let S : Finset Lattice := insert z (Finset.univ.image (fun i => cellIndex (x i)))
  let c (i : ι) : S := ⟨cellIndex (x i), Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨i, Finset.mem_univ i, rfl⟩)⟩
  let k : S := ⟨z, Finset.mem_insert_self _ _⟩
  have hcard : (Fintype.card {i : ι // c i = k} : ℝ) = occupation (latticeCell z) x := by
    unfold occupation
    congr 1
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun i => by simp only [Subtype.ext_iff, c, k, latticeCell,
      mem_ofPred_eq])
  have hsq : (occupation (latticeCell z) x)^2 ≤
      ∑ j : S, (Fintype.card {i : ι // c i = j} : ℝ)^2 := by
    rw [← hcard]
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun j : S => (Fintype.card {i : ι // c i = j} : ℝ)^2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ k)
  have hp := physicalProfile_superstable ht hσ hR hs x c
    (fun j : S => (j : Lattice)) Subtype.val_injective (fun _ => rfl)
  rw [← gibbsEnergy_eq_pairSum (fun x y => physicalProfile t σ R ‖x-y‖)
    (fun x y => by rw [norm_sub_rev]) x] at hp
  have hcoef : (t^2/8)/4 ≤ t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2 := by
    nlinarith only [hsmall, sq_nonneg t]
  have h0 : 0 ≤ (t^2/8)/4 := by positivity
  have hb := (mul_le_mul_of_nonneg_left hsq h0).trans
    (mul_le_mul_of_nonneg_right hcoef (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  linarith only [hb, hp]

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ModifiedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem gibbsEnergy_mono {U V : Space → Space → ℝ} {ι : Type} [Fintype ι]
    (x : ι → Space) (h : ∀ i j, U (x i) (x j) ≤ V (x i) (x j)) :
    gibbsEnergy U x ≤ gibbsEnergy V x := by
  unfold gibbsEnergy
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · rfl
  · exact h i j

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GibbsBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem gibbsEnergy_radial (φ : ℝ → ℝ) {ι : Type} [Fintype ι] (x : ι → Space) :
    gibbsEnergy (fun x y => φ ‖x-y‖) x = realPairEnergy φ x := by
  unfold gibbsEnergy realPairEnergy
  ring

theorem gibbsFamily_radial (φ : ℝ → ℝ) (β h : ℝ) (ι : Type) [Fintype ι] (x : ι → Space) :
    gibbsFamily (fun x y => φ ‖x-y‖) β h ι x =
      Real.exp (h*Fintype.card ι)*symmetricWeight φ β x := by
  unfold gibbsFamily symmetricWeight
  split_ifs
  · rw [gibbsEnergy_radial, ← Real.exp_add]
    congr 1
    ring
  · simp

theorem familyTerm_radial (φ : ℝ → ℝ) (β h L : ℝ) (n : ℕ) :
    familyTerm (gibbsFamily (fun x y => φ ‖x-y‖) β h) (cube L) n =
      Real.exp (h*n)*partition φ β L n := by
  unfold familyTerm familyIntegral
  simp_rw [gibbsFamily_radial, Fintype.card_fin]
  rw [integral_const_mul, mul_div_assoc]
  simpa only [generalPartition, Fintype.card_fin] using
    congrArg (fun a : ℝ => Real.exp (h*n)*a) (generalPartition_eq_partition φ β L n)

theorem grandIntegral_radial (φ : ℝ → ℝ) (t β h L : ℝ) :
    grandIntegral (gibbsFamily (fun x y => φ ‖x-y‖) β (t*h)) (cube L) =
      grandPartition φ t β h L := by
  unfold grandIntegral grandPartition
  simp_rw [familyTerm_radial]

theorem CellLowerBound.mono {t : ℝ} {σ R : ℕ → ℝ} {U V : Space → Space → ℝ}
    (hU : CellLowerBound t σ R U) (hUV : ∀ x y, U x y ≤ V x y) : CellLowerBound t σ R V :=
  fun x y => (hU x y).trans (hUV x y)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PhysicalPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem physicalProfile_le_core {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (r : ℝ) :
    physicalProfile t σ R r ≤ coreProfile t r :=
  sub_le_self _ (attraction_nonneg ht hσ hR r)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.CoerciveCanonical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem finiteCanonical_lower_coercive {t β L : ℝ} (ht : 0 ≤ t) (hβ : 0 ≤ β) (hL : 0 < L)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8) (N : ℕ) :
    β*((t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/(4+2/L)^3)*((N : ℝ)/L^3)^2 +
      ((N : ℝ)/L^3)*Real.log ((N : ℝ)/L^3)-(β*t^2/2+1)*((N : ℝ)/L^3) ≤
      finiteCanonical (physicalProfile t σ R) β L N := by
  by_cases hN : N = 0
  · simp [hN]
  have hφ := measurable_radialPotential (measurable_physicalProfile t hσ hR hs)
  have hst := physicalProfile_stable ht hσ hR hs hsmall
  have hh := neg_log_partition_lower hφ hβ hL hst hN
    (physicalProfile_energy_coercive ht hL.le hσ hR hs hsmall N)
  have hd := div_le_div_of_nonneg_right hh (pow_pos hL 3).le
  unfold finiteCanonical
  convert hd using 1; try rfl
  field_simp
  ring

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.QuadraticGrand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem quadraticGrandTerm_pos {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {β B L : ℝ} (hβ : 0 ≤ β) (hL : 0 < L)
    (hst : ∀ (n : ℕ) (x : Fin n → Space), ((-B*n : ℝ) : EReal) ≤ energy φ x)
    (μ a : ℝ) (n : ℕ) : 0 < quadraticGrandTerm φ β μ a L n :=
  mul_pos (Real.exp_pos _) (partition_pos hφ hβ hL hst n)

theorem log_quadraticGrandTerm {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {β B L : ℝ} (hβ : 0 ≤ β) (hL : 0 < L)
    (hst : ∀ (n : ℕ) (x : Fin n → Space), ((-B*n : ℝ) : EReal) ≤ energy φ x)
    (μ a : ℝ) (n : ℕ) :
    Real.log (quadraticGrandTerm φ β μ a L n)/L^3 =
      μ*((n : ℝ)/L^3)+a*((n : ℝ)/L^3)^2-finiteCanonical φ β L n := by
  rw [quadraticGrandTerm, Real.log_mul (Real.exp_pos _).ne' (partition_pos hφ hβ hL hst n).ne',
    Real.log_exp]
  unfold finiteCanonical
  ring

theorem quadraticGrandTerm_high_density {t β L μ a : ℝ} (ht : 0 ≤ t) (hβ : 0 ≤ β) (hL : 0 < L)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8)
    (ha : a ≤ β*(t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/(4+2/L)^3) {n : ℕ}
    (hn : Real.exp (μ+β*t^2/2+2) ≤ (n : ℝ)/L^3) :
    quadraticGrandTerm (physicalProfile t σ R) β μ a L n ≤ (Real.exp (-1))^n := by
  have hφ := measurable_radialPotential (measurable_physicalProfile t hσ hR hs)
  have hst := physicalProfile_stable ht hσ hR hs hsmall
  have he := finiteCanonical_lower_coercive ht hβ hL hσ hR hs hsmall n
  have hd : 0 ≤ (n : ℝ)/L^3 := div_nonneg (Nat.cast_nonneg _) (pow_pos hL 3).le
  have hl := Real.log_le_log (Real.exp_pos (μ+β*t^2/2+2)) hn
  rw [Real.log_exp] at hl
  have hm := mul_le_mul_of_nonneg_right hl hd
  have hq := mul_le_mul_of_nonneg_right ha (sq_nonneg ((n : ℝ)/L^3))
  have hb : μ*((n : ℝ)/L^3)+a*((n : ℝ)/L^3)^2-
      finiteCanonical (physicalProfile t σ R) β L n ≤ -((n : ℝ)/L^3) := by
    rw [mul_div_assoc] at hq
    nlinarith only [he, hm, hq]
  rw [← log_quadraticGrandTerm hφ hβ hL hst μ a n, ← neg_div] at hb
  have hh := (div_le_div_iff_of_pos_right (pow_pos hL 3)).1 hb
  rw [← Real.exp_nat_mul]
  apply (Real.log_le_iff_le_exp (quadraticGrandTerm_pos hφ hβ hL hst μ a n)).1
  simpa using hh

theorem summable_quadraticGrandTerm {t β L μ a : ℝ} (ht : 0 ≤ t) (hβ : 0 ≤ β) (hL : 0 < L)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8)
    (ha : a ≤ β*(t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/(4+2/L)^3) :
    Summable (quadraticGrandTerm (physicalProfile t σ R) β μ a L) := by
  have hb : Summable (fun n : ℕ => (Real.exp (-1))^n) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (by simp)
  apply hb.of_norm_bounded_eventually_nat
  have hn := ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).atTop_div_const
    (pow_pos hL 3)).eventually (eventually_ge_atTop (Real.exp (μ+β*t^2/2+2)))
  filter_upwards [hn] with n hn
  have hφ := measurable_radialPotential (measurable_physicalProfile t hσ hR hs)
  have hst := physicalProfile_stable ht hσ hR hs hsmall
  rw [Real.norm_eq_abs, abs_of_pos (quadraticGrandTerm_pos hφ hβ hL hst μ a n)]
  exact quadraticGrandTerm_high_density ht hβ hL hσ hR hs hsmall ha hn

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GrandLinearity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem grandIntegral_mono (F G : ConfigFamily) {A : Set Space} (hA : MeasurableSet A)
    (hFi : ∀ n, IntegrableOn (F (Fin n)) {x | ∀ i, x i ∈ A})
    (hGi : ∀ n, IntegrableOn (G (Fin n)) {x | ∀ i, x i ∈ A})
    (hFs : Summable (familyTerm F A)) (hGs : Summable (familyTerm G A))
    (hbound : ∀ n (x : Fin n → Space), (∀ i, x i ∈ A) → F (Fin n) x ≤ G (Fin n) x) :
    grandIntegral F A ≤ grandIntegral G A := by
  apply hFs.tsum_le_tsum _ hGs
  intro n
  change familyIntegral F A (Fin n)/(n.factorial : ℝ) ≤
    familyIntegral G A (Fin n)/(n.factorial : ℝ)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  unfold familyIntegral
  apply setIntegral_mono_on (hFi n) (hGi n)
  · convert MeasurableSet.iInter (fun i : Fin n => hA.preimage
      (measurable_pi_apply i : Measurable (fun x : Fin n → Space => x i))) using 1
    ext x
    simp
  · exact hbound n

theorem grandIntegral_mono_set (F : ConfigFamily) {A B : Set Space} (hAB : A ⊆ B)
    (hF0 : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (hFi : ∀ n, IntegrableOn (F (Fin n)) {x | ∀ i, x i ∈ B})
    (hAs : Summable (familyTerm F A)) (hBs : Summable (familyTerm F B)) :
    grandIntegral F A ≤ grandIntegral F B := by
  apply hAs.tsum_le_tsum _ hBs
  intro n
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply setIntegral_mono_set (hFi n) (Filter.Eventually.of_forall (hF0 (Fin n)))
  exact Filter.Eventually.of_forall (fun x hx i => hAB (hx i))

theorem familyTerm_const_mul (F : ConfigFamily) (A : Set Space) (c : ℝ) (n : ℕ) :
    familyTerm (fun ι _ x => c*F ι x) A n = c*familyTerm F A n := by
  unfold familyTerm familyIntegral
  rw [integral_const_mul]
  ring

theorem grandIntegral_const_mul (F : ConfigFamily) (A : Set Space) (c : ℝ) :
    grandIntegral (fun ι _ x => c*F ι x) A = c*grandIntegral F A := by
  unfold grandIntegral
  simp_rw [familyTerm_const_mul]
  exact tsum_mul_left

theorem familyTerm_add (F G : ConfigFamily) (A : Set Space) (n : ℕ)
    (hFi : IntegrableOn (F (Fin n)) {x | ∀ i, x i ∈ A})
    (hGi : IntegrableOn (G (Fin n)) {x | ∀ i, x i ∈ A}) :
    familyTerm (fun ι _ x => F ι x+G ι x) A n = familyTerm F A n+familyTerm G A n := by
  unfold familyTerm familyIntegral
  rw [integral_add hFi hGi, add_div]

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GrandFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem GrandFinite.of_bound (F : ConfigFamily) {D : Set Space} (hD : volume D ≠ ⊤)
    {d : ℝ} (hm : ∀ (ι : Type) [Fintype ι], Measurable (F ι))
    (h0 : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (hb : ∀ (ι : Type) [Fintype ι] (x : ι → Space), F ι x ≤ Real.exp (d*Fintype.card ι)) :
    GrandFinite F D where
  integrable := fun ι _ => integrableOn_family_of_bound F hD (hm ι) (h0 ι) (hb ι)
  summable := summable_familyTerm_of_bound F hD hm h0 hb

theorem GrandFinite.const_mul {F : ConfigFamily} {D : Set Space}
    (hF : GrandFinite F D) (c : ℝ) : GrandFinite (fun ι _ x => c*F ι x) D where
  integrable := fun ι _ => (hF.integrable ι).const_mul c
  summable := by
    change Summable (fun n => familyTerm (fun ι _ x => c*F ι x) D n)
    simp_rw [familyTerm_const_mul]
    exact hF.summable.mul_left c

theorem GrandFinite.add {F G : ConfigFamily} {D : Set Space}
    (hF : GrandFinite F D) (hG : GrandFinite G D) :
    GrandFinite (fun ι _ x => F ι x+G ι x) D where
  integrable := fun ι _ => (hF.integrable ι).add (hG.integrable ι)
  summable := by
    change Summable (fun n => familyTerm (fun ι _ x => F ι x+G ι x) D n)
    simp_rw [familyTerm_add F G D _ (hF.integrable _) (hG.integrable _)]
    exact hF.summable.add hG.summable

theorem GrandFinite.mono_set {F : ConfigFamily} {A D : Set Space}
    (hF : GrandFinite F D) (hAD : A ⊆ D)
    (h0 : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x) : GrandFinite F A where
  integrable := fun ι _ => (hF.integrable ι).mono_set (fun _ hx i => hAD (hx i))
  summable := by
    apply Summable.of_nonneg_of_le (familyTerm_nonneg F A h0) _ hF.summable
    intro n
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply setIntegral_mono_set (hF.integrable (Fin n)) (Filter.Eventually.of_forall (h0 (Fin n)))
    exact Filter.Eventually.of_forall (fun _ hx i => hAD (hx i))

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GrandDomination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem GrandFinite.of_le {F G : ConfigFamily} {D : Set Space} (hG : GrandFinite G D)
    (hm : ∀ (ι : Type) [Fintype ι], Measurable (F ι))
    (h0 : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (hFG : ∀ (ι : Type) [Fintype ι] (x : ι → Space), F ι x ≤ G ι x) : GrandFinite F D := by
  have hi (ι : Type) [Fintype ι] : IntegrableOn (F ι) {x | ∀ i, x i ∈ D} := by
    apply (hG.integrable ι).mono' (hm ι).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (h0 ι x)] using hFG ι x)
  refine ⟨fun ι _ => hi ι, ?_⟩
  apply Summable.of_nonneg_of_le (familyTerm_nonneg F D h0) _ hG.summable
  intro n
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact integral_mono (hi (Fin n)) (hG.integrable (Fin n)) (hFG (Fin n))

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GrandOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem measurableSet_generalConfigurations {D : Set Space} (hD : MeasurableSet D)
    (ι : Type) [Fintype ι] : MeasurableSet {x : ι → Space | ∀ i, x i ∈ D} := by
  convert MeasurableSet.iInter (fun i : ι => hD.preimage
    (measurable_pi_apply i : Measurable (fun x : ι → Space => x i))) using 1
  ext x
  simp

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GrandProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem grandIntegral_product_bound (F G H : ConfigFamily)
    (hG : RelabelInvariant G) (hH : RelabelInvariant H) {A B : Set Space}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B)
    (hF : GrandFinite F (A ∪ B)) (hGF : GrandFinite G A) (hHF : GrandFinite H B)
    (hbound : ∀ (n : ℕ) (s : Finset (Fin n)) (x : Fin n → Space),
      x ∈ binaryRegion A B s → F (Fin n) x ≤
        G {i : Fin n // i ∈ s} (fun i => x i)*H {i : Fin n // i ∉ s} (fun i => x i)) :
    grandIntegral F (A ∪ B) ≤ grandIntegral G A*grandIntegral H B := by
  apply tsum_le_convolution hF.summable hGF.summable hHF.summable
  intro n
  have hb := integral_binary_bound hA hB hd
    (fun k => familyIntegral G A (Fin k)) (fun k => familyIntegral H B (Fin k))
    (hF.integrable (Fin n)) ?_
  swap
  · intro s
    have hprod := integrableOn_binary_product volume A B s
      (by simpa only [← volume_pi] using hGF.integrable {i : Fin n // i ∈ s})
      (by simpa only [← volume_pi] using hHF.integrable {i : Fin n // i ∉ s})
    have hi := setIntegral_mono_on
      ((hF.integrable (Fin n)).mono_set (binaryRegion_subset_union A B s))
      (by simpa only [← volume_pi] using hprod)
      (measurableSet_binaryRegion hA hB s) (hbound n s)
    rw [show volume = Measure.pi (fun _ : Fin n => (volume : Measure Space)) by exact volume_pi,
      setIntegral_binary_product volume A B s (G {i : Fin n // i ∈ s})
        (H {i : Fin n // i ∉ s})] at hi
    simp only [← volume_pi] at hi
    have heg := familyIntegral_eq_Fin G hG A {i : Fin n // i ∈ s}
    have heh := familyIntegral_eq_Fin H hH B {i : Fin n // i ∉ s}
    have hc : Fintype.card {i : Fin n // i ∈ s} = s.card := Fintype.card_coe s
    rw [hc] at heg
    have hcc : Fintype.card {i : Fin n // i ∉ s} = n-s.card := by
      have hh := Fintype.card_subtype_compl (fun i : Fin n => i ∈ s)
      simpa only [Fintype.card_fin, hc] using hh
    rw [hcc] at heh
    change (∫ x in binaryRegion A B s, F (Fin n) x) ≤ _
    calc
      _ ≤ familyIntegral G A {i : Fin n // i ∈ s}*
          familyIntegral H B {i : Fin n // i ∉ s} := hi
      _ = _ := by rw [heg, heh, Fintype.card_fin]
  have hh := div_le_div_of_nonneg_right hb (Nat.cast_nonneg (n.factorial) : (0 : ℝ) ≤ n.factorial)
  rw [Fintype.card_fin, factorial_binomial_sum
    (fun k => familyIntegral G A (Fin k)) (fun k => familyIntegral H B (Fin k)) n] at hh
  exact hh

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GibbsIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem gibbsFamily_term_zero (V : Space → Space → ℝ) (β h : ℝ) (D : Set Space) :
    familyTerm (gibbsFamily V β h) D 0 = 1 := by
  have hf : gibbsFamily V β h (Fin 0) = fun _ => 1 := by
    funext x
    simp only [gibbsFamily, ite_eq_left (Function.injective_of_subsingleton x),
      gibbsEnergy, Fintype.card_fin, Nat.cast_zero, mul_zero, Finset.univ_eq_empty,
      Finset.sum_empty, zero_div, sub_zero, Real.exp_zero]
  dsimp only [familyTerm, familyIntegral]
  rw [hf, setIntegral_const, Measure.real, volume_generalConfigurations]
  norm_num

theorem physical_gibbs_moment_finite {t β : ℝ} (ht : 0 ≤ t) (hβ : 0 ≤ β)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n) ≤ (t^2/8)/8)
    {D : Set Space} (hDfin : volume D ≠ ⊤) (h : ℝ) (z : Lattice)
    {c : ℝ} (hc : c ≤ β*(t^2/8)/4) :
    GrandFinite (momentFamily
      (gibbsFamily (fun x y => physicalProfile t σ R ‖x-y‖) β h) (latticeCell z) c) D := by
  have hm : Measurable (Function.uncurry (fun x y : Space => physicalProfile t σ R ‖x-y‖)) :=
    (measurable_physicalProfile t hσ hR hs).comp ((measurable_fst.sub measurable_snd).norm)
  apply GrandFinite.of_bound _ hDfin
    (fun ι _ => measurable_momentFamily _ (measurableSet_latticeCell z) c (measurable_gibbsFamily hm β h ι))
    (momentFamily_nonneg _ (gibbsFamily_nonneg _ β h) _ _)
  intro ι _ x
  apply gibbs_moment_stable_bound _ β h (t^2/2) c _ x
  have he := mul_le_mul_of_nonneg_left (physical_gibbs_moment_energy ht hσ hR hs hsmall x z) hβ
  have hcc := mul_le_mul_of_nonneg_right hc (sq_nonneg (occupation (latticeCell z) x))
  nlinarith only [he, hcc]

theorem physical_gibbs_finite {t β : ℝ} (ht : 0 ≤ t) (hβ : 0 ≤ β)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n) ≤ (t^2/8)/8)
    {D : Set Space} (hDfin : volume D ≠ ⊤) (h : ℝ) :
    GrandFinite (gibbsFamily (fun x y => physicalProfile t σ R ‖x-y‖) β h) D := by
  have h0 : (0 : ℝ) ≤ β*(t^2/8)/4 := by positivity
  have hh := physical_gibbs_moment_finite ht hβ hσ hR hs hsmall hDfin h (fun _ => 0) h0
  have he : momentFamily (gibbsFamily (fun x y => physicalProfile t σ R ‖x-y‖) β h)
      (latticeCell (fun _ => 0)) 0 = gibbsFamily (fun x y => physicalProfile t σ R ‖x-y‖) β h := by
    funext ι inst x
    simp only [momentFamily, zero_mul, Real.exp_zero, mul_one]
  rw [he] at hh
  exact hh

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ProductEquality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem grandIntegral_product_lower (F G H : ConfigFamily)
    (hG : RelabelInvariant G) (hH : RelabelInvariant H) {A B : Set Space}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B)
    (hF : GrandFinite F (A ∪ B)) (hGF : GrandFinite G A) (hHF : GrandFinite H B)
    (hbound : ∀ (n : ℕ) (s : Finset (Fin n)) (x : Fin n → Space),
      x ∈ binaryRegion A B s →
        G {i : Fin n // i ∈ s} (fun i => x i)*H {i : Fin n // i ∉ s} (fun i => x i) ≤ F (Fin n) x) :
    grandIntegral G A*grandIntegral H B ≤ grandIntegral F (A ∪ B) := by
  have hG' : RelabelInvariant (fun ι _ x => (-1 : ℝ)*G ι x) := by
    intro ι κ _ _ e x
    change (-1 : ℝ)*G ι (x ∘ e) = (-1 : ℝ)*G κ x
    rw [hG ι κ e x]
  have hh := grandIntegral_product_bound (fun ι _ x => (-1 : ℝ)*F ι x)
    (fun ι _ x => (-1 : ℝ)*G ι x) H hG' hH hA hB hd (hF.const_mul (-1))
    (hGF.const_mul (-1)) hHF (fun n s x hx => by
      have hh := neg_le_neg (hbound n s x hx)
      simpa only [neg_one_mul, neg_mul, one_mul] using hh)
  rw [grandIntegral_const_mul, grandIntegral_const_mul] at hh
  linarith

theorem grandIntegral_product_eq (F G H : ConfigFamily)
    (hG : RelabelInvariant G) (hH : RelabelInvariant H) {A B : Set Space}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B)
    (hF : GrandFinite F (A ∪ B)) (hGF : GrandFinite G A) (hHF : GrandFinite H B)
    (hbound : ∀ (n : ℕ) (s : Finset (Fin n)) (x : Fin n → Space),
      x ∈ binaryRegion A B s → F (Fin n) x =
        G {i : Fin n // i ∈ s} (fun i => x i)*H {i : Fin n // i ∉ s} (fun i => x i)) :
    grandIntegral F (A ∪ B) = grandIntegral G A*grandIntegral H B :=
  le_antisymm (grandIntegral_product_bound F G H hG hH hA hB hd hF hGF hHF
    (fun n s x hx => (hbound n s x hx).le))
    (grandIntegral_product_lower F G H hG hH hA hB hd hF hGF hHF
      (fun n s x hx => (hbound n s x hx).ge))

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GrandBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem gibbsFamily_binary_le {U : Space → Space → ℝ} (hU : ∀ x y, U x y = U y x)
    {β h : ℝ} (hβ : 0 ≤ β) {A B : Set Space}
    (hcross : ∀ x ∈ A, ∀ y ∈ B, 0 ≤ U x y)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : Finset ι) {x : ι → Space} (hx : x ∈ binaryRegion A B s) :
    gibbsFamily U β h ι x ≤ gibbsFamily U β h {i : ι // i ∈ s} (fun i => x i)*
      gibbsFamily U β h {i : ι // i ∉ s} (fun i => x i) := by
  by_cases hinj : Function.Injective x
  · have hi : Function.Injective (fun i : {i : ι // i ∈ s} => x i) := hinj.comp Subtype.val_injective
    have hj : Function.Injective (fun i : {i : ι // i ∉ s} => x i) := hinj.comp Subtype.val_injective
    simp only [gibbsFamily, ite_eq_left hinj, ite_eq_left hi, ite_eq_left hj, ← Real.exp_add, Real.exp_le_exp]
    have he : gibbsEnergy U x = gibbsEnergy U (fun i : {i : ι // i ∈ s} => x i)+
        gibbsEnergy U (fun i : {i : ι // i ∉ s} => x i)+
        ∑ i : {i : ι // i ∈ s}, ∑ j : {j : ι // j ∉ s}, U (x i) (x j) := by
      convert gibbsEnergy_split U hU (fun i => i ∈ s) x using 1
      congr! 5
    have hc : (Fintype.card {i : ι // i ∈ s} : ℝ)+Fintype.card {i : ι // i ∉ s} = Fintype.card ι := by
      have hh := Fintype.card_subtype_compl (fun i : ι => i ∈ s)
      have hl := Fintype.card_subtype_le (fun i : ι => i ∈ s)
      have he : Fintype.card {i : ι // i ∈ s}+Fintype.card {i : ι // i ∉ s} = Fintype.card ι := by omega
      exact_mod_cast he
    have hz : 0 ≤ ∑ i : {i : ι // i ∈ s}, ∑ j : {i : ι // i ∉ s}, U (x i) (x j) := by
      apply Finset.sum_nonneg
      intro i _
      apply Finset.sum_nonneg
      intro j _
      exact hcross (x i) (by simpa only [ite_eq_left i.property] using hx i)
        (x j) (by simpa only [ite_eq_right j.property] using hx j)
    rw [he, ← hc]
    nlinarith only [mul_nonneg hβ hz]
  · rw [gibbsFamily, ite_eq_right hinj]
    exact mul_nonneg (gibbsFamily_nonneg _ _ _ _ _) (gibbsFamily_nonneg _ _ _ _ _)

theorem grandIntegral_gibbs_empty (U : Space → Space → ℝ) (β h : ℝ) :
    grandIntegral (gibbsFamily U β h) ∅ = 1 := by
  rw [grandIntegral, tsum_eq_single 0, gibbsFamily_term_zero]
  intro n hn
  have hn' : 0 < n := Nat.pos_of_ne_zero hn
  have he : {x : Fin n → Space | ∀ i, x i ∈ (∅ : Set Space)} = ∅ := by
    ext x
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall]
    exact ⟨⟨0, hn'⟩, not_false⟩
  simp only [familyTerm, familyIntegral, he, setIntegral_empty, zero_div]

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.FixedOccupation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem countFamily_relabel (F : ConfigFamily) (hF : RelabelInvariant F) (n : ℕ) :
    RelabelInvariant (countFamily F n) := by
  intro ι κ _ _ e x
  simp only [countFamily, Fintype.card_congr e, hF ι κ e x]

theorem fixedOccupationFamily_relabel {κ : Type u_1} (A : κ → Set Space) (s : Finset κ)
    (n : κ → ℕ) (F : ConfigFamily) (hF : RelabelInvariant F) :
    RelabelInvariant (fixedOccupationFamily A s n F) := by
  intro ι τ _ _ e x
  simp only [fixedOccupationFamily, occupation_relabel, hF ι τ e x]

theorem GrandFinite.count {F : ConfigFamily} {D : Set Space} (hF : GrandFinite F D) (n : ℕ) :
    GrandFinite (countFamily F n) D := by
  refine ⟨fun ι _ => ?_, ?_⟩
  · change IntegrableOn (fun x : ι → Space => if Fintype.card ι = n then F ι x else 0) _
    split_ifs
    · exact hF.integrable ι
    · exact integrableOn_zero
  · have he (j : ℕ) : familyTerm (countFamily F n) D j = if j = n then familyTerm F D j else 0 := by
      unfold familyTerm familyIntegral countFamily
      simp only [Fintype.card_fin]
      split_ifs <;> simp
    change Summable (fun j => familyTerm (countFamily F n) D j)
    simp_rw [he]
    exact summable_of_ne_finset_zero (s := {n}) (fun j hj => ite_eq_right (by simpa only [Finset.mem_singleton] using hj))

theorem grandIntegral_countFamily (F : ConfigFamily) (D : Set Space) (n : ℕ) :
    grandIntegral (countFamily F n) D = familyTerm F D n := by
  have he (j : ℕ) : familyTerm (countFamily F n) D j = if j = n then familyTerm F D j else 0 := by
    unfold familyTerm familyIntegral countFamily
    simp only [Fintype.card_fin]
    split_ifs <;> simp
  simp only [grandIntegral, he, tsum_ite_eq]

theorem fixedOccupationFamily_nonneg {κ : Type u_1} (A : κ → Set Space) (s : Finset κ)
    (n : κ → ℕ) (F : ConfigFamily)
    (hF : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (ι : Type) [Fintype ι] (x : ι → Space) : 0 ≤ fixedOccupationFamily A s n F ι x := by
  unfold fixedOccupationFamily
  split_ifs
  · exact hF ι x
  · rfl

theorem GrandFinite.fixedOccupation {κ : Type u_1} {A : κ → Set Space} {s : Finset κ}
    (n : κ → ℕ) (hA : ∀ k ∈ s, MeasurableSet (A k)) {F : ConfigFamily} {D : Set Space}
    (hF : GrandFinite F D) (hm : ∀ (ι : Type) [Fintype ι], Measurable (F ι))
    (h0 : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x) :
    GrandFinite (fixedOccupationFamily A s n F) D := by
  refine hF.of_le (fun ι _ => ?_) (fixedOccupationFamily_nonneg A s n F h0) ?_
  · apply Measurable.ite ?_ (hm ι) measurable_const
    have hh := MeasurableSet.biInter s.finite_toSet.countable (fun k hk =>
      measurableSet_eq_fun (measurable_occupation (ι := ι) (hA k hk))
        (show Measurable (fun _ : ι → Space => (n k : ℝ)) from measurable_const))
    convert hh using 1
    ext x
    simp only [mem_ofPred_eq, mem_iInter, Finset.mem_coe]
  · intro ι _ x
    unfold fixedOccupationFamily
    split_ifs
    · rfl
    · exact h0 ι x

theorem occupation_binary_left {ι : Type} [Fintype ι] [DecidableEq ι] {A B : Set Space}
    (hd : Disjoint A B) (s : Finset ι) {x : ι → Space} (hx : x ∈ binaryRegion A B s) :
    occupation A x = (Fintype.card {i : ι // i ∈ s} : ℝ) := by
  rw [occupation_eq_sum]
  have he (i : ι) : x i ∈ A ↔ i ∈ s := by
    constructor
    · intro hi
      by_contra his
      exact Set.disjoint_left.mp hd hi (by simpa only [ite_eq_right his] using hx i)
    · intro hi
      simpa only [ite_eq_left hi] using hx i
  simp only [he]
  simp only [Fintype.card_subtype, ← Finset.sum_boole]

theorem occupation_binary_right {ι : Type} [Fintype ι] [DecidableEq ι] {A B C : Set Space}
    (hd : Disjoint A C) (s : Finset ι) {x : ι → Space} (hx : x ∈ binaryRegion A B s) :
    occupation C x = occupation C (fun i : {i : ι // i ∉ s} => x i) := by
  have hh := (occupation_subtype_compl C s x (fun i hi hc =>
    Set.disjoint_left.mp hd (by simpa only [ite_eq_left hi] using hx i) hc)).symm
  convert hh using 1
  congr! 3

theorem injective_binary_iff {ι : Type} [Fintype ι] [DecidableEq ι] {A B : Set Space}
    (hd : Disjoint A B) (s : Finset ι) {x : ι → Space} (hx : x ∈ binaryRegion A B s) :
    Function.Injective x ↔ Function.Injective (fun i : {i : ι // i ∈ s} => x i) ∧
      Function.Injective (fun i : {i : ι // i ∉ s} => x i) := by
  constructor
  · intro hh
    exact ⟨hh.comp Subtype.val_injective, hh.comp Subtype.val_injective⟩
  · rintro ⟨h₁,h₂⟩ i j hij
    by_cases hi : i ∈ s <;> by_cases hj : j ∈ s
    · exact congrArg Subtype.val (h₁ (a₁ := ⟨i,hi⟩) (a₂ := ⟨j,hj⟩) hij)
    · have hia : x i ∈ A := by simpa only [ite_eq_left hi] using hx i
      have hjb : x j ∈ B := by simpa only [ite_eq_right hj] using hx j
      exact False.elim (Set.disjoint_left.mp hd hia (hij.symm ▸ hjb))
    · have hja : x j ∈ A := by simpa only [ite_eq_left hj] using hx j
      have hib : x i ∈ B := by simpa only [ite_eq_right hi] using hx i
      exact False.elim (Set.disjoint_left.mp hd hja (hij ▸ hib))
    · exact congrArg Subtype.val (h₂ (a₁ := ⟨i,hi⟩) (a₂ := ⟨j,hj⟩) hij)

theorem gibbsFamily_binary_eq {U : Space → Space → ℝ} (hU : ∀ x y, U x y = U y x)
    (β h : ℝ) {A B : Set Space} (hd : Disjoint A B)
    (hcross : ∀ x ∈ A, ∀ y ∈ B, U x y = 0)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : Finset ι) {x : ι → Space} (hx : x ∈ binaryRegion A B s) :
    gibbsFamily U β h ι x = gibbsFamily U β h {i : ι // i ∈ s} (fun i => x i)*
      gibbsFamily U β h {i : ι // i ∉ s} (fun i => x i) := by
  have he : gibbsEnergy U x = gibbsEnergy U (fun i : {i : ι // i ∈ s} => x i)+
      gibbsEnergy U (fun i : {i : ι // i ∉ s} => x i) := by
    have hh := gibbsEnergy_split U hU (fun i => i ∈ s) x
    have hz : (∑ i : {i : ι // i ∈ s}, ∑ j : {j : ι // j ∉ s}, U (x i) (x j)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j _
      exact hcross (x i) (by simpa only [ite_eq_left i.property] using hx i)
        (x j) (by simpa only [ite_eq_right j.property] using hx j)
    have he' : gibbsEnergy U x = gibbsEnergy U (fun i : {i : ι // i ∈ s} => x i)+
        gibbsEnergy U (fun i : {i : ι // i ∉ s} => x i)+
        ∑ i : {i : ι // i ∈ s}, ∑ j : {j : ι // j ∉ s}, U (x i) (x j) := by
      convert hh using 1
      congr! 5
    simpa only [hz, add_zero] using he'
  have hc : (Fintype.card {i : ι // i ∈ s} : ℝ)+Fintype.card {i : ι // i ∉ s} = Fintype.card ι := by
    have hh := Fintype.card_subtype_compl (fun i : ι => i ∈ s)
    have hl := Fintype.card_subtype_le (fun i : ι => i ∈ s)
    have hh' : Fintype.card {i : ι // i ∈ s}+Fintype.card {i : ι // i ∉ s} = Fintype.card ι := by omega
    exact_mod_cast hh'
  simp only [gibbsFamily, injective_binary_iff hd s hx]
  split_ifs <;> try simp_all only [zero_mul, mul_zero, and_false, false_and, not_false_eq_true, and_self, not_true_eq_false]
  rw [← Real.exp_add, ← hc]
  congr 1
  ring

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.OccupationProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem fixedOccupation_binary_eq {κ : Type u_1} (A : κ → Set Space) (n : κ → ℕ)
    {s : Finset κ} {i : κ} (hi : i ∉ s)
    (hd : (↑(insert i s) : Set κ).Pairwise (fun j k => Disjoint (A j) (A k)))
    {U : Space → Space → ℝ} (hU : ∀ x y, U x y = U y x) (β h : ℝ)
    (hcross : ∀ j ∈ insert i s, ∀ k ∈ insert i s, j ≠ k →
      ∀ a ∈ A j, ∀ b ∈ A k, U a b = 0)
    {ι : Type} [Fintype ι] [DecidableEq ι] (r : Finset ι) {x : ι → Space}
    (hx : x ∈ binaryRegion (A i) (⋃ k ∈ s, A k) r) :
    fixedOccupationFamily A (insert i s) n (gibbsFamily U β h) ι x =
      countFamily (gibbsFamily U β h) (n i) {j : ι // j ∈ r} (fun j => x j)*
      fixedOccupationFamily A s n (gibbsFamily U β h) {j : ι // j ∉ r} (fun j => x j) := by
  have hid (k : κ) (hk : k ∈ s) : Disjoint (A i) (A k) :=
    hd (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hk) (fun hh => hi (hh ▸ hk))
  have hdU : Disjoint (A i) (⋃ k ∈ s, A k) := Set.disjoint_iUnion₂_right.mpr hid
  have hcrossU : ∀ a ∈ A i, ∀ b ∈ (⋃ k ∈ s, A k), U a b = 0 := by
    intro a ha b hb
    obtain ⟨k,hk,hbk⟩ := mem_iUnion₂.mp hb
    exact hcross i (Finset.mem_insert_self _ _) k (Finset.mem_insert_of_mem hk)
      (fun hh => hi (hh ▸ hk)) a ha b hbk
  have hp : (∀ k ∈ insert i s, occupation (A k) x = (n k : ℝ)) ↔
      Fintype.card {j : ι // j ∈ r} = n i ∧
        ∀ k ∈ s, occupation (A k) (fun j : {j : ι // j ∉ r} => x j) = (n k : ℝ) := by
    rw [Finset.forall_mem_insert, occupation_binary_left hdU r hx]
    simp only [Nat.cast_inj]
    apply and_congr_right
    intro _
    apply forall_congr'
    intro k
    apply forall_congr'
    intro hk
    rw [occupation_binary_right (hid k hk) r hx]
  unfold fixedOccupationFamily countFamily
  simp only [hp, gibbsFamily_binary_eq hU β h hdU hcrossU r hx]
  split_ifs <;> simp_all

theorem grandIntegral_fixedOccupation_product {κ : Type u_1}
    {U : Space → Space → ℝ} (hm : Measurable (Function.uncurry U))
    (hU : ∀ x y, U x y = U y x) (β h : ℝ)
    (A : κ → Set Space) (n : κ → ℕ) (s : Finset κ)
    (hA : ∀ k ∈ s, MeasurableSet (A k))
    (hd : (s : Set κ).Pairwise (fun j k => Disjoint (A j) (A k)))
    (hcross : ∀ j ∈ s, ∀ k ∈ s, j ≠ k → ∀ a ∈ A j, ∀ b ∈ A k, U a b = 0)
    (hF : GrandFinite (gibbsFamily U β h) (⋃ k ∈ s, A k)) :
    grandIntegral (fixedOccupationFamily A s n (gibbsFamily U β h)) (⋃ k ∈ s, A k) =
      ∏ k ∈ s, familyTerm (gibbsFamily U β h) (A k) (n k) := by
  induction s using Finset.induction_on with
  | empty =>
    have he : fixedOccupationFamily A ∅ n (gibbsFamily U β h) = gibbsFamily U β h := by
      funext ι inst x
      simp [fixedOccupationFamily]
    rw [he]
    simpa using grandIntegral_gibbs_empty U β h
  | @insert i s hi ih =>
    have hAi := hA i (Finset.mem_insert_self _ _)
    have hAs (k : κ) (hk : k ∈ s) := hA k (Finset.mem_insert_of_mem hk)
    have hB : MeasurableSet (⋃ k ∈ s, A k) := MeasurableSet.biUnion s.finite_toSet.countable hAs
    have hdU : Disjoint (A i) (⋃ k ∈ s, A k) := by
      apply Set.disjoint_iUnion₂_right.mpr
      intro k hk
      exact hd (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hk) (fun hh => hi (hh ▸ hk))
    have hfi := hF.mono_set (subset_iUnion₂_of_subset i (Finset.mem_insert_self i s) Subset.rfl)
      (gibbsFamily_nonneg U β h)
    have hfs := hF.mono_set (iUnion₂_subset (fun k hk =>
      subset_iUnion₂_of_subset k (Finset.mem_insert_of_mem hk) Subset.rfl)) (gibbsFamily_nonneg U β h)
    have hmF := measurable_gibbsFamily hm β h
    have hfull := hF.fixedOccupation n hA (fun ι _ => hmF ι) (gibbsFamily_nonneg U β h)
    have htail := hfs.fixedOccupation n hAs (fun ι _ => hmF ι) (gibbsFamily_nonneg U β h)
    have hbin := grandIntegral_product_eq
      (fixedOccupationFamily A (insert i s) n (gibbsFamily U β h))
      (countFamily (gibbsFamily U β h) (n i))
      (fixedOccupationFamily A s n (gibbsFamily U β h))
      (countFamily_relabel _ (gibbsFamily_relabel U β h) (n i))
      (fixedOccupationFamily_relabel A s n _ (gibbsFamily_relabel U β h))
      hAi hB hdU (by simpa only [Finset.set_biUnion_insert] using hfull) (hfi.count (n i)) htail
      (fun _ r x hx => fixedOccupation_binary_eq A n hi hd hU β h hcross r hx)
    rw [Finset.set_biUnion_insert, hbin, grandIntegral_countFamily, Finset.prod_insert hi]
    rw [ih hAs (hd.mono (Finset.subset_insert _ _))
      (fun j hj k hk => hcross j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)) hfs]

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.KacKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem hasCompactSupport_kernel : HasCompactSupport kernel := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Space) 1)
  intro x hx
  have hx' : ¬ ‖x‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  exact kernel_zero_outside (lt_of_not_ge hx').le

theorem scaledKernel_eq {R : ℝ} (hR : 0 < R) (x : Space) :
    scaledKernel R x = R⁻¹^3*kernel (R⁻¹ • x) := by
  simp only [scaledKernel, scaledKernelProfile, kernel, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hR), div_eq_mul_inv, mul_comm R⁻¹ ‖x‖]

theorem scaledKernel_nonneg {R : ℝ} (hR : 0 < R) (x : Space) : 0 ≤ scaledKernel R x :=
  scaledKernelProfile_nonneg hR ‖x‖

theorem scaledKernel_zero {R : ℝ} (hR : 0 < R) {x : Space} (hx : R ≤ ‖x‖) :
    scaledKernel R x = 0 := scaledKernelProfile_zero hR hx

theorem integrable_scaledKernel {R : ℝ} (hR : 0 < R) : Integrable (scaledKernel R) := by
  change Integrable (fun x => scaledKernel R x)
  simp_rw [scaledKernel_eq hR]
  exact ((integrable_comp_smul_iff volume kernel (inv_ne_zero hR.ne')).2
    (contDiff_kernel.continuous.integrable_of_hasCompactSupport hasCompactSupport_kernel)).const_mul _

theorem integral_scaledKernel {R : ℝ} (hR : 0 < R) : ∫ x, scaledKernel R x = 1 := by
  simp_rw [scaledKernel_eq hR]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume kernel hR.le,
    integral_kernel]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul, mul_one]
  field_simp

theorem scaledKernel_oscillation {C : NNReal} (hC : LipschitzWith C kernel)
    {R : ℝ} (hR : 0 < R) (x y : Space) :
    |scaledKernel R x-scaledKernel R y| ≤ (C : ℝ)/R^4*‖x-y‖ := by
  have hh := hC.norm_sub_le (R⁻¹ • x) (R⁻¹ • y)
  rw [← smul_sub, norm_smul] at hh
  simp only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)] at hh
  simp_rw [scaledKernel_eq hR]
  rw [← mul_sub, abs_mul, abs_of_pos (pow_pos (inv_pos.mpr hR) 3)]
  have hm := mul_le_mul_of_nonneg_left hh (pow_pos (inv_pos.mpr hR) 3).le
  convert hm using 1; try rfl
  field_simp

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.KacGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem measurableSet_gridBox (u : ℝ) (k : Lattice) : MeasurableSet (gridBox u k) := by
  have heq : gridBox u k = (@WithLp.ofLp 2 (Fin 3 → ℝ)) ⁻¹'
      (Set.pi Set.univ (fun i => Ico (u*(k i : ℝ)) (u*((k i : ℝ)+1)))) := by
    ext x
    simp only [gridBox, mem_preimage, mem_ofPred_eq, Set.mem_pi, mem_univ, forall_const, mem_Ico]
  rw [heq]
  exact (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ico)).preimage
    (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).continuous.measurable

theorem mem_gridBox_iff {u : ℝ} (hu : 0 < u) (k : Lattice) (x : Space) :
    x ∈ gridBox u k ↔ gridIndex u x = k := by
  simp only [gridBox, mem_ofPred_eq, gridIndex, funext_iff]
  apply forall_congr'
  intro i
  rw [Int.floor_eq_iff, le_div_iff₀ hu, div_lt_iff₀ hu]
  simp only [mul_comm u]

theorem mem_gridBox {u : ℝ} (hu : 0 < u) (x : Space) : x ∈ gridBox u (gridIndex u x) :=
  (mem_gridBox_iff hu _ _).2 rfl

theorem gridBox_disjoint {u : ℝ} (hu : 0 < u) {k l : Lattice} (hkl : k ≠ l) :
    Disjoint (gridBox u k) (gridBox u l) := by
  apply Set.disjoint_left.2
  intro x hx hy
  exact hkl (((mem_gridBox_iff hu _ _).1 hx).symm.trans ((mem_gridBox_iff hu _ _).1 hy))

theorem volume_gridBox {u : ℝ} (hu : 0 ≤ u) (k : Lattice) :
    volume (gridBox u k) = ENNReal.ofReal (u^3) := by
  have heq : gridBox u k = (@WithLp.ofLp 2 (Fin 3 → ℝ)) ⁻¹'
      (Set.pi Set.univ (fun i => Ico (u*(k i : ℝ)) (u*((k i : ℝ)+1)))) := by
    ext x
    simp only [gridBox, mem_preimage, mem_ofPred_eq, Set.mem_pi, mem_univ, forall_const, mem_Ico]
  rw [heq, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    ((MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ico)).nullMeasurableSet)]
  change (Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))) _ = _
  rw [Measure.pi_pi]
  simp only [Real.volume_Ico]
  simp only [show ∀ i, u*((k i : ℝ)+1)-u*(k i : ℝ)=u by intro i; ring]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.ofReal_pow hu]

theorem gridBox_center_distance {u : ℝ} (hu : 0 < u) {k : Lattice} {x : Space}
    (hx : x ∈ gridBox u k) : ‖x-gridCenter u k‖ ≤ 2*u := by
  have hc (i : Fin 3) : |x i-gridCenter u k i| ≤ u := by
    have hxi := hx i
    change |x i-u*((k i : ℝ)+1/2)| ≤ u
    rw [abs_le]
    constructor <;> linarith
  have hs (i : Fin 3) : (x i-gridCenter u k i)^2 ≤ u^2 :=
    by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hu.le).2 (hc i)
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => hs i)
  have hn : ‖x-gridCenter u k‖^2 ≤ 3*u^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa only [PiLp.sub_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
      using hh
  nlinarith [norm_nonneg (x-gridCenter u k)]

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GridBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem card_indexInterval (m q : ℕ) : (indexInterval m q).card = 2*m*q+1 := by
  unfold indexInterval
  rw [Int.card_Icc]
  have he : (m : ℤ)*(q : ℤ)+1-(-(m : ℤ)*(q : ℤ)) = ((2*m*q+1 : ℕ) : ℤ) := by push_cast; ring
  rw [he, Int.toNat_natCast]

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.CubeBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem card_gridIndices (m q : ℕ) : (gridIndices m q).card = (2*m*q+1)^3 := by
  simp only [gridIndices, Fintype.card_piFinset, card_indexInterval, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.MaskedReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem measurable_gridIndex (u : ℝ) : Measurable (gridIndex u) := by
  apply Measurable.of_eval
  intro i
  exact ((EuclideanSpace.proj i).continuous.measurable.div_const u).floor

theorem measurable_blockCut (q : ℕ) {V : Space → Space → ℝ}
    (hV : Measurable (Function.uncurry V)) : Measurable (Function.uncurry (blockCut q V)) := by
  apply hV.ite ?_ measurable_const
  exact measurableSet_eq_fun ((measurable_gridIndex _).comp measurable_fst)
    ((measurable_gridIndex _).comp measurable_snd)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GridVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem volume_real_gridBox {u : ℝ} (hu : 0 ≤ u) (k : Lattice) :
    volume.real (gridBox u k) = u^3 := by
  rw [measureReal_def, volume_gridBox hu, ENNReal.toReal_ofReal (pow_nonneg hu 3)]

theorem gridBox_union_volume {u : ℝ} (hu : 0 < u) (s : Finset Lattice) :
    volume.real (⋃ k ∈ s, gridBox u k) = s.card*u^3 := by
  rw [measureReal_biUnion_finset (fun _ _ _ _ hkl => gridBox_disjoint hu hkl)
    (fun _ _ => measurableSet_gridBox _ _) (fun k _ => by
      rw [volume_gridBox hu.le]; exact ENNReal.ofReal_ne_top)]
  simp only [volume_real_gridBox hu.le, Finset.sum_const, nsmul_eq_mul]

theorem norm_le_cube {x : Space} {D : ℝ} (h : ‖x‖ ≤ D) : x ∈ cube (2*D) := by
  intro i
  have hc : |x i| ≤ D := (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i :
    |x i| ≤ ‖x‖).trans h
  rw [abs_le] at hc
  dsimp only [mem_Icc]
  constructor <;> linarith [hc.1, hc.2]

theorem card_grid_near_bound {u D : ℝ} (hu : 0 < u) (hD : 0 ≤ D) (c : Space)
    (s : Finset Lattice) (hs : ∀ k ∈ s, ‖gridCenter u k-c‖ ≤ D) :
    (s.card : ℝ)*u^3 ≤ (2*(D+2*u))^3 := by
  have hsub : (⋃ k ∈ s, gridBox u k) ⊆ (fun x : Space => x-c) ⁻¹' cube (2*(D+2*u)) := by
    intro x hx
    obtain ⟨k, hk, hx⟩ := Set.mem_iUnion₂.mp hx
    apply norm_le_cube
    calc
      ‖x-c‖ ≤ ‖x-gridCenter u k‖+‖gridCenter u k-c‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2*u+D := add_le_add (gridBox_center_distance hu hx) (hs k hk)
      _ = D+2*u := add_comm _ _
  have hm : volume ((fun x : Space => x-c) ⁻¹' cube (2*(D+2*u))) =
      ENNReal.ofReal ((2*(D+2*u))^3) := by
    rw [show (fun x : Space => x-c) = (fun x => x+(-c)) by funext; rw [sub_eq_add_neg],
      measure_preimage_add_right, volume_cube, ENNReal.ofReal_pow (by positivity)]
  have hh := measureReal_mono hsub (by rw [hm]; exact ENNReal.ofReal_ne_top)
  rw [gridBox_union_volume hu, measureReal_def, hm,
    ENNReal.toReal_ofReal (by positivity)] at hh
  exact hh

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.KacRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Filter MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem kernel_pair_oscillation {C : NNReal} (hC : LipschitzWith C kernel)
    {R u : ℝ} (hR : 0 < R) {c d x y : Space} (hx : ‖x-c‖ ≤ 2*u) (hy : ‖y-d‖ ≤ 2*u) :
    |scaledKernel R (x-y)-scaledKernel R (c-d)| ≤ 4*(C : ℝ)*u/R^4 := by
  have hn : ‖(x-y)-(c-d)‖ ≤ 4*u := by
    rw [show (x-y)-(c-d)=(x-c)-(y-d) by abel]
    exact (norm_sub_le _ _).trans (by linarith)
  have hh := (scaledKernel_oscillation hC hR (x-y) (c-d)).trans
    (mul_le_mul_of_nonneg_left hn (by positivity))
  calc
    _ ≤ (C : ℝ)/R^4*(4*u) := hh
    _ = _ := by ring

theorem kac_pair_bounds {C : NNReal} (hC : LipschitzWith C kernel)
    {R u : ℝ} (hR : 0 < R) {c d x y : Space} (hx : ‖x-c‖ ≤ 2*u) (hy : ‖y-d‖ ≤ 2*u) :
    kacLower C R u c d ≤ scaledKernel R (x-y) ∧ scaledKernel R (x-y) ≤ kacUpper C R u c d := by
  have he := (abs_le.mp (kernel_pair_oscillation hC hR hx hy))
  constructor
  · exact max_le (scaledKernel_nonneg hR _) (by linarith [he.1])
  · unfold kacUpper
    split_ifs with hn
    · linarith [he.2]
    · have hc' : ‖c-d‖ ≤ 4*u+‖x-y‖ := by
        calc
          ‖c-d‖ ≤ ‖c-x‖+‖x-d‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ ‖c-x‖+(‖x-y‖+‖y-d‖) := add_le_add le_rfl (norm_sub_le_norm_sub_add_norm_sub x y d)
          _ ≤ 4*u+‖x-y‖ := by rw [norm_sub_rev c x]; linarith
      rw [scaledKernel_zero hR (by linarith [lt_of_not_ge hn])]

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.LowerRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Filter MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem kernel_box_integral_lower {C : NNReal} (hC : LipschitzWith C kernel)
    {R u : ℝ} (hR : 0 < R) (hu : 0 < u) (c : Space) (k : Lattice) :
    (∫ y in gridBox u k, scaledKernel R (c-y)) ≤
      kacLower C R u c (gridCenter u k)*u^3+6*(C : ℝ)*u/R^4*u^3 := by
  have hfin : volume (gridBox u k) ≠ ⊤ := by rw [volume_gridBox hu.le]; exact ENNReal.ofReal_ne_top
  have hfun : Integrable (fun y : Space => scaledKernel R (c-y)) := (integrable_scaledKernel hR).comp_sub_left c
  have hmono := setIntegral_mono_on hfun.integrableOn
    (integrableOn_const (C := kacLower C R u c (gridCenter u k)+6*(C : ℝ)*u/R^4) hfin)
    (measurableSet_gridBox u k) ?_
  swap
  · intro y hy
    have hh := scaledKernel_oscillation hC hR (c-y) (c-gridCenter u k)
    rw [show (c-y)-(c-gridCenter u k)=-(y-gridCenter u k) by abel, norm_neg] at hh
    have he := hh.trans (mul_le_mul_of_nonneg_left (gridBox_center_distance hu hy) (by positivity))
    have he' := (abs_le.mp he).2
    have hk : scaledKernel R (c-gridCenter u k)-4*(C : ℝ)*u/R^4 ≤
        kacLower C R u c (gridCenter u k) := le_max_right _ _
    ring_nf at he' hk ⊢
    linarith only [he', hk]
  rw [setIntegral_const, volume_real_gridBox hu.le, smul_eq_mul] at hmono
  nlinarith only [hmono]

theorem kacLower_row {C : NNReal} (hC : LipschitzWith C kernel)
    {R u : ℝ} (hR : 0 < R) (hu : 0 < u) (c : Space) (s : Finset Lattice)
    (hcover : ∀ y : Space, ‖c-y‖ < R → ∃ k ∈ s, y ∈ gridBox u k) :
    1-(6*(C : ℝ)*u/R^4)*(2*(R+6*u))^3 ≤
      u^3*(∑ k ∈ s, kacLower C R u c (gridCenter u k)) := by
  let near := s.filter (fun k => ‖c-gridCenter u k‖ ≤ R+4*u)
  have hnvol := card_grid_near_bound hu (show 0 ≤ R+4*u by positivity) c near (fun k hk => by
    have hh := (Finset.mem_filter.mp hk).2
    rwa [norm_sub_rev] at hh)
  have herr := mul_le_mul_of_nonneg_left hnvol (show 0 ≤ 6*(C : ℝ)*u/R^4 by positivity)
  have harg : 2*(R+4*u+2*u)=2*(R+6*u) := by ring
  rw [harg] at herr
  have hsums : (∑ k ∈ near, kacLower C R u c (gridCenter u k)) ≤
      ∑ k ∈ s, kacLower C R u c (gridCenter u k) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro k _ _
    exact le_max_left _ _
  have hsums' := mul_le_mul_of_nonneg_left hsums (pow_pos hu 3).le
  have hb := Finset.sum_le_sum (fun k (_ : k ∈ near) => kernel_box_integral_lower hC hR hu c k)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul] at hb
  have hfun : Integrable (fun y : Space => scaledKernel R (c-y)) := (integrable_scaledKernel hR).comp_sub_left c
  have hi := integral_biUnion_finset near (fun _ _ => measurableSet_gridBox _ _)
    (fun _ _ _ _ hkl => gridBox_disjoint hu hkl) (fun _ _ => hfun.integrableOn)
  have hsum : (∑ k ∈ near, ∫ y in gridBox u k, scaledKernel R (c-y)) = 1 := by
    rw [← hi, setIntegral_eq_integral_of_forall_compl_eq_zero ?_, integral_sub_left_eq_self,
      integral_scaledKernel hR]
    intro y hy
    apply scaledKernel_zero hR
    by_contra! hh
    obtain ⟨k, hk, hyk⟩ := hcover y hh
    have hnear : k ∈ near := by
      apply Finset.mem_filter.mpr ⟨hk, ?_⟩
      have hl := norm_sub_le_norm_sub_add_norm_sub c y (gridCenter u k)
      have hd := gridBox_center_distance hu hyk
      linarith
    exact hy (Set.mem_iUnion₂.mpr ⟨k, hnear, hyk⟩)
  rw [hsum] at hb
  nlinarith only [hb, herr, hsums']

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.KacEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem double_sum_comp_eq {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (c : ι → κ) (J : κ → κ → ℝ) :
    (∑ i, ∑ j, J (c i) (c j)) = ∑ k, ∑ l,
      J k l*(Fintype.card {i // c i = k} : ℝ)*(Fintype.card {i // c i = l} : ℝ) := by
  calc
    _ = ∑ i, ∑ l, (Fintype.card {j // c j = l} : ℝ)*J (c i) l := by
      apply Finset.sum_congr rfl
      intro i _
      exact sum_comp_eq_sum_fibres c (fun l => J (c i) l)
    _ = ∑ k, (Fintype.card {i // c i = k} : ℝ)*
        (∑ l, (Fintype.card {j // c j = l} : ℝ)*J k l) :=
      sum_comp_eq_sum_fibres c (fun k => ∑ l, (Fintype.card {j // c j = l} : ℝ)*J k l)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring

theorem gibbsEnergy_eq_sum_sub_diag (V : Space → Space → ℝ)
    {ι : Type} [Fintype ι] (x : ι → Space) :
    gibbsEnergy V x = ((∑ i, ∑ j, V (x i) (x j))-(∑ i, V (x i) (x i)))/2 := by
  have he (i j : ι) : (if i = j then 0 else V (x i) (x j)) =
      V (x i) (x j)-(if i = j then V (x i) (x j) else 0) := by
    split_ifs <;> ring
  simp only [gibbsEnergy, he, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem kac_energy_lower {C : NNReal} (hC : LipschitzWith C kernel)
    {R u : ℝ} (hR : 0 < R) {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (c : ι → κ) (centers : κ → Space) (x : ι → Space)
    (hx : ∀ i, ‖x i-centers (c i)‖ ≤ 2*u) :
    ((∑ k, ∑ l, kacLower C R u (centers k) (centers l)*
      (Fintype.card {i // c i = k} : ℝ)*(Fintype.card {i // c i = l} : ℝ))-
      (Fintype.card ι : ℝ)*scaledKernel R 0)/2 ≤
        gibbsEnergy (fun x y => scaledKernel R (x-y)) x := by
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
      (kac_pair_bounds hC hR (hx i) (hx j)).1))
  rw [double_sum_comp_eq c (fun k l => kacLower C R u (centers k) (centers l))] at hh
  rw [gibbsEnergy_eq_sum_sub_diag]
  simp only [sub_self, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  linarith only [hh]

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.FiniteProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem familyTerm_product_bound (F G H : ConfigFamily)
    (hG : RelabelInvariant G) (hH : RelabelInvariant H) {A B : Set Space}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B)
    (hGF : GrandFinite G A) (hHF : GrandFinite H B) (n : ℕ)
    (hFi : IntegrableOn (F (Fin n)) {x | ∀ i, x i ∈ A ∪ B})
    (hbound : ∀ (s : Finset (Fin n)) (x : Fin n → Space),
      x ∈ binaryRegion A B s → F (Fin n) x ≤
        G {i : Fin n // i ∈ s} (fun i => x i)*H {i : Fin n // i ∉ s} (fun i => x i)) :
    familyTerm F (A ∪ B) n ≤ ∑ k ∈ Finset.range (n+1), familyTerm G A k*familyTerm H B (n-k) := by
  have hb := integral_binary_bound hA hB hd
    (fun k => familyIntegral G A (Fin k)) (fun k => familyIntegral H B (Fin k))
    hFi ?_
  swap
  · intro s
    have hprod := integrableOn_binary_product volume A B s
      (by simpa only [← volume_pi] using hGF.integrable {i : Fin n // i ∈ s})
      (by simpa only [← volume_pi] using hHF.integrable {i : Fin n // i ∉ s})
    have hi := setIntegral_mono_on
      (hFi.mono_set (binaryRegion_subset_union A B s))
      (by simpa only [← volume_pi] using hprod)
      (measurableSet_binaryRegion hA hB s) (hbound s)
    rw [show volume = Measure.pi (fun _ : Fin n => (volume : Measure Space)) by exact volume_pi,
      setIntegral_binary_product volume A B s (G {i : Fin n // i ∈ s})
        (H {i : Fin n // i ∉ s})] at hi
    simp only [← volume_pi] at hi
    have heg := familyIntegral_eq_Fin G hG A {i : Fin n // i ∈ s}
    have heh := familyIntegral_eq_Fin H hH B {i : Fin n // i ∉ s}
    have hc : Fintype.card {i : Fin n // i ∈ s} = s.card := Fintype.card_coe s
    rw [hc] at heg
    have hcc : Fintype.card {i : Fin n // i ∉ s} = n-s.card := by
      have hh := Fintype.card_subtype_compl (fun i : Fin n => i ∈ s)
      simpa only [Fintype.card_fin, hc] using hh
    rw [hcc] at heh
    change (∫ x in binaryRegion A B s, F (Fin n) x) ≤ _
    calc
      _ ≤ familyIntegral G A {i : Fin n // i ∈ s}*
          familyIntegral H B {i : Fin n // i ∉ s} := hi
      _ = _ := by rw [heg, heh, Fintype.card_fin]
  have hh := div_le_div_of_nonneg_right hb (Nat.cast_nonneg (n.factorial) : (0 : ℝ) ≤ n.factorial)
  rw [Fintype.card_fin, factorial_binomial_sum
    (fun k => familyIntegral G A (Fin k)) (fun k => familyIntegral H B (Fin k)) n] at hh
  exact hh

theorem GrandFinite.union_product {F G H : ConfigFamily}
    (hG : RelabelInvariant G) (hH : RelabelInvariant H) {A B : Set Space}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B)
    (hGF : GrandFinite G A) (hHF : GrandFinite H B)
    (hFi : ∀ (ι : Type) [Fintype ι], IntegrableOn (F ι) {x | ∀ i, x i ∈ A ∪ B})
    (h0 : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (hbound : ∀ (n : ℕ) (s : Finset (Fin n)) (x : Fin n → Space),
      x ∈ binaryRegion A B s → F (Fin n) x ≤
        G {i : Fin n // i ∈ s} (fun i => x i)*H {i : Fin n // i ∉ s} (fun i => x i)) :
    GrandFinite F (A ∪ B) := by
  refine ⟨hFi, ?_⟩
  have hab : Summable (fun p : ℕ × ℕ => familyTerm G A p.1*familyTerm H B p.2) :=
    summable_mul_of_summable_norm (summable_norm_iff.mpr hGF.summable)
      (summable_norm_iff.mpr hHF.summable)
  exact Summable.of_nonneg_of_le (familyTerm_nonneg F (A ∪ B) h0)
    (fun n => familyTerm_product_bound F G H hG hH hA hB hd hGF hHF n (hFi (Fin n)) (hbound n))
    (summable_sum_mul_range_of_summable_mul hab)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.FiniteBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem familyTerm_gibbs_empty_ne_zero (U : Space → Space → ℝ) (β h : ℝ) {n : ℕ} (hn : n ≠ 0) :
    familyTerm (gibbsFamily U β h) ∅ n = 0 := by
  have hp : 0 < n := Nat.pos_of_ne_zero hn
  have he : {x : Fin n → Space | ∀ i, x i ∈ (∅ : Set Space)} = ∅ := by
    ext x
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall]
    exact ⟨⟨0, hp⟩, not_false⟩
  simp only [familyTerm, familyIntegral, he, setIntegral_empty, zero_div]

theorem grandFinite_gibbs_blocks {κ : Type u_1} {U : Space → Space → ℝ}
    (hU : ∀ x y, U x y = U y x) {β h : ℝ} (hβ : 0 ≤ β)
    (A : κ → Set Space) (s : Finset κ)
    (hA : ∀ i ∈ s, MeasurableSet (A i))
    (hd : (s : Set κ).Pairwise (fun i j => Disjoint (A i) (A j)))
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x ∈ A i, ∀ y ∈ A j, 0 ≤ U x y)
    (hFi : ∀ (ι : Type) [Fintype ι], IntegrableOn (gibbsFamily U β h ι)
      {x | ∀ i, x i ∈ ⋃ j ∈ s, A j})
    (hFA : ∀ i ∈ s, GrandFinite (gibbsFamily U β h) (A i)) :
    GrandFinite (gibbsFamily U β h) (⋃ i ∈ s, A i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty] at hFi ⊢
    refine ⟨hFi, ?_⟩
    apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    exact familyTerm_gibbs_empty_ne_zero U β h (by simpa only [Finset.mem_singleton] using hn)
  | @insert i s hi ih =>
    let B := ⋃ j ∈ s, A j
    have hB : MeasurableSet B := MeasurableSet.biUnion s.finite_toSet.countable
      (fun j hj => hA j (Finset.mem_insert_of_mem hj))
    have hAi := hA i (Finset.mem_insert_self _ _)
    have hAB : Disjoint (A i) B := by
      apply Set.disjoint_iUnion₂_right.mpr
      intro j hj
      exact hd (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hj) (fun hh => hi (hh ▸ hj))
    have hieq : (⋃ j ∈ insert i s, A j) = A i ∪ B := by simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left]; rfl
    have hFiB (ι : Type) [Fintype ι] : IntegrableOn (gibbsFamily U β h ι)
        {x | ∀ a, x a ∈ B} := by
      apply (hFi ι).mono_set
      intro x hx a
      rw [hieq]
      exact Or.inr (hx a)
    have hFB := ih (fun j hj => hA j (Finset.mem_insert_of_mem hj))
      (hd.mono (Finset.subset_insert _ _))
      (fun j hj k hk => hcross j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk))
      hFiB (fun j hj => hFA j (Finset.mem_insert_of_mem hj))
    rw [hieq] at hFi ⊢
    apply GrandFinite.union_product (gibbsFamily_relabel U β h) (gibbsFamily_relabel U β h)
      hAi hB hAB (hFA i (Finset.mem_insert_self _ _)) hFB hFi (gibbsFamily_nonneg U β h)
    intro n r x hx
    apply gibbsFamily_binary_le hU hβ ?_ r hx
    intro a ha b hb
    obtain ⟨j, hj, hjb⟩ := mem_iUnion₂.mp hb
    exact hcross i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
      (fun hh => hi (hh ▸ hj)) a ha b hjb

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GibbsQuadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem gibbsEnergy_const (c : ℝ) {ι : Type} [Fintype ι] (x : ι → Space) :
    gibbsEnergy (fun _ _ => c) x = c*((Fintype.card ι : ℝ)^2-Fintype.card ι)/2 := by
  rw [gibbsEnergy_eq_sum_sub_diag]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

theorem gibbsEnergy_congr {V W : Space → Space → ℝ} {ι : Type} [Fintype ι]
    (x : ι → Space) (h : ∀ i j, V (x i) (x j) = W (x i) (x j)) :
    gibbsEnergy V x = gibbsEnergy W x := by
  unfold gibbsEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [h]

theorem gibbsFamily_shift (φ : ℝ → ℝ) (β μ γ : ℝ) (ι : Type) [Fintype ι] (x : ι → Space) :
    gibbsFamily (fun x y => φ ‖x-y‖-γ) β (μ+β*γ/2) ι x =
      Real.exp (μ*Fintype.card ι+β*γ/2*(Fintype.card ι : ℝ)^2)*symmetricWeight φ β x := by
  unfold gibbsFamily symmetricWeight
  split_ifs
  · rw [gibbsEnergy_sub, gibbsEnergy_radial, gibbsEnergy_const, ← Real.exp_add]
    congr 1
    ring
  · simp

theorem familyTerm_shift (φ : ℝ → ℝ) (β μ γ : ℝ) (A : Set Space) (n : ℕ) :
    familyTerm (gibbsFamily (fun x y => φ ‖x-y‖-γ) β (μ+β*γ/2)) A n =
      Real.exp (μ*n+β*γ/2*(n : ℝ)^2)*setPartition φ β A n := by
  unfold familyTerm familyIntegral
  simp_rw [gibbsFamily_shift, Fintype.card_fin]
  rw [integral_const_mul, mul_div_assoc]
  simp only [setPartition, generalPartition, Fintype.card_fin]

theorem integrableOn_gibbs_of_lower {V : Space → Space → ℝ}
    (hVm : Measurable (Function.uncurry V)) {C β h : ℝ} (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (hV : ∀ x y, -C ≤ V x y) {D : Set Space} (hD : volume D ≠ ⊤)
    (ι : Type) [Fintype ι] : IntegrableOn (gibbsFamily V β h ι) {x | ∀ i, x i ∈ D} := by
  let n : ℝ := Fintype.card ι
  apply integrableOn_family_of_bound (gibbsFamily V β h) hD
    (measurable_gibbsFamily hVm β h ι) (gibbsFamily_nonneg V β h ι)
    (C := Real.exp ((h+β*C*n/2)*n))
  intro x
  unfold gibbsFamily
  split_ifs
  · apply Real.exp_le_exp.mpr
    have he := gibbsEnergy_mono (U := fun _ _ => -C) (V := V) x (fun i j => hV (x i) (x j))
    rw [gibbsEnergy_const] at he
    have hn : 0 ≤ n := Nat.cast_nonneg _
    have hh := mul_le_mul_of_nonneg_left he hβ
    change -C*(n^2-n)/2 ≤ gibbsEnergy V x at he
    change h*n-β*gibbsEnergy V x ≤ (h+β*C*n/2)*n
    nlinarith only [hh, mul_nonneg (mul_nonneg hβ hC) hn]
  · exact (Real.exp_pos _).le

theorem measurable_quadraticBlock (q : ℕ) {φ : ℝ → ℝ} (hφ : Measurable φ) (γ : ℝ) :
    Measurable (Function.uncurry (quadraticBlock q φ γ)) :=
  measurable_blockCut q ((hφ.comp ((measurable_fst.sub measurable_snd).norm)).sub_const γ)

theorem quadraticBlock_symm (q : ℕ) (φ : ℝ → ℝ) (γ : ℝ) (x y : Space) :
    quadraticBlock q φ γ x y = quadraticBlock q φ γ y x := by
  simp only [quadraticBlock, blockCut]
  rw [norm_sub_rev y x]
  congr 1
  exact propext eq_comm

theorem quadraticBlock_on {q : ℕ} (hq : 0 < q) (φ : ℝ → ℝ) (γ : ℝ) {k : Lattice}
    {x y : Space} (hx : x ∈ gridBox ((q : ℝ)/4) k) (hy : y ∈ gridBox ((q : ℝ)/4) k) :
    quadraticBlock q φ γ x y = φ ‖x-y‖-γ := by
  have hu : 0 < (q : ℝ)/4 := by positivity
  simp only [quadraticBlock, blockCut, (mem_gridBox_iff hu _ _).1 hx,
    (mem_gridBox_iff hu _ _).1 hy, ite_true]

theorem quadraticBlock_cross {q : ℕ} (hq : 0 < q) (φ : ℝ → ℝ) (γ : ℝ) {k l : Lattice}
    (hkl : k ≠ l) {x y : Space} (hx : x ∈ gridBox ((q : ℝ)/4) k)
    (hy : y ∈ gridBox ((q : ℝ)/4) l) : quadraticBlock q φ γ x y = 0 := by
  have hu : 0 < (q : ℝ)/4 := by positivity
  simp only [quadraticBlock, blockCut, (mem_gridBox_iff hu _ _).1 hx,
    (mem_gridBox_iff hu _ _).1 hy, ite_eq_right hkl]

theorem familyTerm_quadraticBlock {q : ℕ} (hq : 0 < q) (φ : ℝ → ℝ) (β μ γ : ℝ)
    (k : Lattice) (n : ℕ) :
    familyTerm (gibbsFamily (quadraticBlock q φ γ) β (μ+β*γ/2)) (gridBox ((q : ℝ)/4) k) n =
      Real.exp (μ*n+β*γ/2*(n : ℝ)^2)*setPartition φ β (gridBox ((q : ℝ)/4) k) n := by
  rw [← familyTerm_shift]
  unfold familyTerm familyIntegral
  congr 1
  apply setIntegral_congr_fun (measurableSet_generalConfigurations (measurableSet_gridBox _ _) (Fin n))
  intro x hx
  unfold gibbsFamily
  rw [gibbsEnergy_congr (W := fun x y => φ ‖x-y‖-γ) x (fun i j => quadraticBlock_on hq φ γ (hx i) (hx j))]

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.BlockEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem gibbsEnergy_mul_left (V : Space → Space → ℝ) (a : ℝ) {ι : Type} [Fintype ι] (x : ι → Space) :
    gibbsEnergy (fun x y => a*V x y) x = a*gibbsEnergy V x := by
  have he (i j : ι) : (if i = j then 0 else a*V (x i) (x j)) =
      a*(if i = j then 0 else V (x i) (x j)) := by split_ifs <;> ring
  simp only [gibbsEnergy, he, ← Finset.mul_sum]
  ring

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.BlockPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem gridBox_subset_translate_cube {u : ℝ} (_hu : 0 < u) (k : Lattice) :
    gridBox u k ⊆ (fun x : Space => x+gridCenter u k) '' cube u := by
  intro x hx
  refine ⟨x-gridCenter u k, ?_, sub_add_cancel _ _⟩
  intro i
  have hxi := hx i
  change -u/2 ≤ x i-u*((k i : ℝ)+1/2) ∧ x i-u*((k i : ℝ)+1/2) ≤ u/2
  constructor <;> linarith [hxi.1, hxi.2]

theorem volume_translate (A : Set Space) (a : Space) :
    volume ((fun x : Space => x+a) '' A) = volume A := by
  have he : (fun x : Space => x+a) '' A = (fun x : Space => x-a) ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [mem_preimage, add_sub_cancel_right] using hy
    · intro hx
      exact ⟨x-a, hx, sub_add_cancel _ _⟩
  rw [he, show (fun x : Space => x-a) = (fun x => x+(-a)) by funext; rw [sub_eq_add_neg],
    measure_preimage_add_right]

theorem setPartition_mono {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {β B : ℝ} (hβ : 0 ≤ β)
    (hst : ∀ (n : ℕ) (x : Fin n → Space), ((-B*n : ℝ) : EReal) ≤ energy φ x)
    {A D : Set Space} (hD : volume D ≠ ⊤) (hAD : A ⊆ D) (n : ℕ) :
    setPartition φ β A n ≤ setPartition φ β D n := by
  unfold setPartition generalPartition
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  refine setIntegral_mono_set (integrableOn_symmetricWeight hφ hβ hst ?_)
    (Filter.Eventually.of_forall (symmetricWeight_nonneg φ β)) ?_
  · rw [volume_generalConfigurations]
    exact ENNReal.pow_ne_top hD
  · exact Filter.Eventually.of_forall (fun _ hx i => hAD (hx i))

theorem setPartition_gridBox_le {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {β B u : ℝ} (hβ : 0 ≤ β) (hu : 0 < u)
    (hst : ∀ (n : ℕ) (x : Fin n → Space), ((-B*n : ℝ) : EReal) ≤ energy φ x)
    (k : Lattice) (n : ℕ) : setPartition φ β (gridBox u k) n ≤ partition φ β u n := by
  have hfin : volume ((fun x : Space => x+gridCenter u k) '' cube u) ≠ ⊤ := by
    rw [volume_translate, volume_cube]
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hh := setPartition_mono hφ hβ hst hfin (gridBox_subset_translate_cube hu k) n
  rw [setPartition_translate] at hh
  simp only [setPartition, generalPartition_eq_partition] at hh
  exact hh

theorem physicalProfile_ge_constant {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ) (r : ℝ) :
    -(t*(∑' n, σ n)*kernelHeight) ≤ physicalProfile t σ R r := by
  have ha := attraction_le ht hσ hR hs r
  have hc := coreProfile_nonneg t r
  change _ ≤ coreProfile t r-attraction t σ R r
  linarith

theorem quadraticBlock_lower {φ : ℝ → ℝ} {C γ : ℝ} (hC : 0 ≤ C) (hγ : 0 ≤ γ)
    (hφ : ∀ r, -C ≤ φ r) (q : ℕ) (x y : Space) :
    -(C+γ) ≤ quadraticBlock q φ γ x y := by
  unfold quadraticBlock blockCut
  split_ifs
  · linarith [hφ ‖x-y‖]
  · linarith

theorem volume_gridBlocks_ne_top {u : ℝ} (hu : 0 ≤ u) (s : Finset Lattice) :
    volume (⋃ k ∈ s, gridBox u k) ≠ ⊤ := by
  apply ne_top_of_le_ne_top ?_ (measure_biUnion_finset_le s (gridBox u))
  apply ENNReal.sum_ne_top.mpr
  intro k _
  rw [volume_gridBox hu]
  exact ENNReal.ofReal_ne_top

theorem quadraticBlock_familyTerm_le {t β μ γ : ℝ} (ht : 0 ≤ t) (hβ : 0 ≤ β)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8)
    {q : ℕ} (hq : 0 < q) (k : Lattice) (n : ℕ) :
    familyTerm (gibbsFamily (quadraticBlock q (physicalProfile t σ R) γ) β (μ+β*γ/2))
      (gridBox ((q : ℝ)/4) k) n ≤
    quadraticGrandTerm (physicalProfile t σ R) β μ (β*γ/2*((q : ℝ)/4)^3) ((q : ℝ)/4) n := by
  have hu : 0 < (q : ℝ)/4 := by positivity
  rw [familyTerm_quadraticBlock hq]
  unfold quadraticGrandTerm
  rw [show β*γ/2*((q : ℝ)/4)^3*(n : ℝ)^2/((q : ℝ)/4)^3 = β*γ/2*(n : ℝ)^2 by field_simp]
  exact mul_le_mul_of_nonneg_left
    (setPartition_gridBox_le (measurable_radialPotential (measurable_physicalProfile t hσ hR hs))
      hβ hu (physicalProfile_stable ht hσ hR hs hsmall) k n) (Real.exp_pos _).le

theorem grandFinite_quadraticBlock_box {t β μ γ : ℝ} (ht : 0 ≤ t) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8) {q : ℕ} (hq : 0 < q)
    (hcoeff : β*γ/2*((q : ℝ)/4)^3 ≤
      β*(t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/(4+2/((q : ℝ)/4))^3) (k : Lattice) :
    GrandFinite (gibbsFamily (quadraticBlock q (physicalProfile t σ R) γ) β (μ+β*γ/2))
      (gridBox ((q : ℝ)/4) k) := by
  have hu : 0 < (q : ℝ)/4 := by positivity
  have hC : 0 ≤ t*(∑' n, σ n)*kernelHeight :=
    mul_nonneg (mul_nonneg ht (tsum_nonneg hσ)) kernelHeight_pos.le
  refine ⟨fun ι _ => integrableOn_gibbs_of_lower
    (measurable_quadraticBlock q (measurable_physicalProfile t hσ hR hs) γ)
    (add_nonneg hC hγ) hβ
    (quadraticBlock_lower hC hγ (physicalProfile_ge_constant ht hσ hR hs) q) ?_ ι, ?_⟩
  · rw [volume_gridBox hu.le]; exact ENNReal.ofReal_ne_top
  · exact Summable.of_nonneg_of_le (familyTerm_nonneg _ _ (gibbsFamily_nonneg _ _ _))
      (quadraticBlock_familyTerm_le ht hβ hσ hR hs hsmall hq k)
      (summable_quadraticGrandTerm ht hβ hu hσ hR hs hsmall hcoeff)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.QuadraticBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem grandFinite_quadraticBlocks {t β μ γ : ℝ} (ht : 0 ≤ t) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8) {q : ℕ} (hq : 0 < q)
    (hcoeff : β*γ/2*((q : ℝ)/4)^3 ≤
      β*(t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/(4+2/((q : ℝ)/4))^3) (s : Finset Lattice) :
    GrandFinite (gibbsFamily (quadraticBlock q (physicalProfile t σ R) γ) β (μ+β*γ/2))
      (⋃ k ∈ s, gridBox ((q : ℝ)/4) k) := by
  have hu : 0 < (q : ℝ)/4 := by positivity
  have hC : 0 ≤ t*(∑' n, σ n)*kernelHeight :=
    mul_nonneg (mul_nonneg ht (tsum_nonneg hσ)) kernelHeight_pos.le
  apply grandFinite_gibbs_blocks (quadraticBlock_symm q (physicalProfile t σ R) γ) hβ
    (gridBox ((q : ℝ)/4)) s (fun k _ => measurableSet_gridBox _ k)
    (fun _ _ _ _ hkl => gridBox_disjoint hu hkl)
    (fun _ _ _ _ hkl _ hx _ hy => (quadraticBlock_cross hq (physicalProfile t σ R) γ hkl hx hy).ge)
  · intro ι _
    exact integrableOn_gibbs_of_lower
      (measurable_quadraticBlock q (measurable_physicalProfile t hσ hR hs) γ)
      (add_nonneg hC hγ) hβ
      (quadraticBlock_lower hC hγ (physicalProfile_ge_constant ht hσ hR hs) q)
      (volume_gridBlocks_ne_top hu.le s) ι
  · exact fun k _ => grandFinite_quadraticBlock_box ht hβ hγ hσ hR hs hsmall hq hcoeff k

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GridCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem cube_subset_gridBlocks {u : ℝ} (hu : 0 < u) (m : ℕ) :
    cube (2*(m : ℝ)*u) ⊆ ⋃ k ∈ gridIndices m 1, gridBox u k := by
  intro x hx
  apply mem_iUnion₂.mpr
  refine ⟨gridIndex u x, ?_, mem_gridBox hu x⟩
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_Icc.mpr
  have hxi := hx i
  change -(m : ℤ)*1 ≤ ⌊x i/u⌋ ∧ ⌊x i/u⌋ ≤ (m : ℤ)*1
  simp only [mul_one]
  constructor
  · apply Int.le_floor.mpr
    rw [le_div_iff₀ hu]
    push_cast
    exact (by linarith [hxi.1])
  · apply Int.floor_le_iff.mpr
    rw [div_lt_iff₀ hu]
    push_cast
    nlinarith [hxi.2]

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.AppendAttraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem summable_prepend (a : ℝ) {σ : ℕ → ℝ} (hs : Summable σ) : Summable (prepend a σ) := by
  exact (summable_nat_add_iff 1).mp hs

theorem tsum_prepend (a : ℝ) {σ : ℕ → ℝ} (hs : Summable σ) :
    ∑' n, prepend a σ n = a+∑' n, σ n := by
  exact (summable_prepend a hs).tsum_eq_zero_add

theorem prepend_nonneg {a : ℝ} {σ : ℕ → ℝ} (ha : 0 ≤ a) (hσ : ∀ n, 0 ≤ σ n) :
    ∀ n, 0 ≤ prepend a σ n
  | 0 => ha
  | n+1 => hσ n

theorem prepend_ge_one {a : ℝ} {σ : ℕ → ℝ} (ha : 1 ≤ a) (hσ : ∀ n, 1 ≤ σ n) :
    ∀ n, 1 ≤ prepend a σ n
  | 0 => ha
  | n+1 => hσ n

theorem attraction_prepend (t : ℝ) {a S : ℝ} {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ) (r : ℝ) :
    attraction t (prepend a σ) (prepend S R) r = t*a*scaledKernelProfile S r+attraction t σ R r := by
  unfold attraction
  have he : (fun n => prepend a σ n*scaledKernelProfile (prepend S R n) r) =
      prepend (a*scaledKernelProfile S r) (fun n => σ n*scaledKernelProfile (R n) r) := by
    funext n; cases n <;> rfl
  rw [he, tsum_prepend _ (summable_attraction_terms hσ hR hs r)]
  ring

theorem physicalProfile_prepend (t : ℝ) {a S : ℝ} {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ) (r : ℝ) :
    physicalProfile t (prepend a σ) (prepend S R) r = physicalProfile t σ R r-t*a*scaledKernelProfile S r := by
  unfold physicalProfile
  rw [attraction_prepend t hσ hR hs]
  ring

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.KacBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Filter
namespace ContinuumTemperature

theorem kacRowError_sq_tendsto (C : NNReal) :
    Tendsto (fun u : ℝ => kacRowError C (u^2) u) atTop (𝓝 0) := by
  have hi : Tendsto (fun u : ℝ => u⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hh := (hi.const_mul (48*(C : ℝ))).mul (((tendsto_const_nhds (x := (1 : ℝ))).add (hi.const_mul 6)).pow 3)
  have hh' : Tendsto (fun u : ℝ => 48*(C : ℝ)*u⁻¹*(1+6*u⁻¹)^3) atTop (𝓝 0) := by
    simpa using hh
  apply hh'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  unfold kacRowError
  field_simp
  ring

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.InnerGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem measurableSet_innerGridBox (u : ℝ) (k : Lattice) : MeasurableSet (innerGridBox u k) :=
  ((isCompact_cube (u-2)).image (continuous_id.add continuous_const)).measurableSet

theorem innerGridBox_subset_gridBox (u : ℝ) (k : Lattice) : innerGridBox u k ⊆ gridBox u k := by
  rintro x ⟨a,ha,rfl⟩ i
  have hi := ha i
  change u*(k i : ℝ) ≤ a i+u*((k i : ℝ)+1/2) ∧ a i+u*((k i : ℝ)+1/2) < u*((k i : ℝ)+1)
  constructor <;> linarith [hi.1,hi.2]

theorem innerGridBox_disjoint {u : ℝ} (hu : 0 < u) {k l : Lattice} (hkl : k ≠ l) :
    Disjoint (innerGridBox u k) (innerGridBox u l) :=
  (gridBox_disjoint hu hkl).mono (innerGridBox_subset_gridBox u k) (innerGridBox_subset_gridBox u l)

theorem innerGridBox_separation {u : ℝ} (hu : 2 ≤ u) {k l : Lattice} (hkl : k ≠ l)
    {x y : Space} (hx : x ∈ innerGridBox u k) (hy : y ∈ innerGridBox u l) : 2 ≤ ‖x-y‖ := by
  obtain ⟨a,ha,rfl⟩ := hx
  obtain ⟨b,hb,rfl⟩ := hy
  obtain ⟨i,hi⟩ : ∃ i, k i ≠ l i := by
    by_contra! hh
    exact hkl (funext hh)
  have hai := ha i
  have hbi := hb i
  have hh : |(a+gridCenter u k) i-(b+gridCenter u l) i| ≤
      ‖(a+gridCenter u k)-(b+gridCenter u l)‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using
      PiLp.norm_apply_le ((a+gridCenter u k)-(b+gridCenter u l)) i
  change |a i+u*((k i : ℝ)+1/2)-(b i+u*((l i : ℝ)+1/2))| ≤ _ at hh
  rw [abs_le] at hh
  rcases lt_or_gt_of_ne hi with hk | hl
  · have hlk : (k i : ℝ)+1 ≤ (l i : ℝ) := by exact_mod_cast (Int.add_one_le_iff.mpr hk)
    have hm := mul_le_mul_of_nonneg_left hlk (by linarith : 0 ≤ u)
    nlinarith [hai.1,hai.2,hbi.1,hbi.2]
  · have hlk : (l i : ℝ)+1 ≤ (k i : ℝ) := by exact_mod_cast (Int.add_one_le_iff.mpr hl)
    have hm := mul_le_mul_of_nonneg_left hlk (by linarith : 0 ≤ u)
    nlinarith [hai.1,hai.2,hbi.1,hbi.2]

theorem gridIndices_mono {m n : ℕ} (h : m ≤ n) : gridIndices m 1 ⊆ gridIndices n 1 := by
  intro k hk
  apply Fintype.mem_piFinset.mpr
  intro i
  have hi := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hk i)
  apply Finset.mem_Icc.mpr
  change -(n : ℤ)*1 ≤ k i ∧ k i ≤ (n : ℤ)*1
  change -(m : ℤ)*1 ≤ k i ∧ k i ≤ (m : ℤ)*1 at hi
  have hn : (m : ℤ) ≤ n := Int.ofNat_le.mpr h
  constructor <;> omega

theorem gridIndex_coordinate_bounds {m : ℕ} {k : Lattice} (hk : k ∈ gridIndices m 1) (i : Fin 3) :
    -(m : ℝ) ≤ k i ∧ (k i : ℝ) ≤ m := by
  have hi := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hk i)
  change -(m : ℤ)*1 ≤ k i ∧ k i ≤ (m : ℤ)*1 at hi
  exact_mod_cast (by simpa only [mul_one] using hi)

theorem innerGridBox_subset_cube {u : ℝ} (hu : 0 ≤ u) {m : ℕ} {k : Lattice}
    (hk : k ∈ gridIndices m 1) : innerGridBox u k ⊆ cube (2*((m : ℝ)+1)*u) := by
  rintro x ⟨a,ha,rfl⟩ i
  have hi := ha i
  have hk' := gridIndex_coordinate_bounds hk i
  have hl := mul_le_mul_of_nonneg_left hk'.1 hu
  have hr := mul_le_mul_of_nonneg_left hk'.2 hu
  change -(2*((m : ℝ)+1)*u)/2 ≤ a i+u*((k i : ℝ)+1/2) ∧
    a i+u*((k i : ℝ)+1/2) ≤ (2*((m : ℝ)+1)*u)/2
  constructor <;> linarith [hi.1,hi.2]

theorem interior_grid_cover {u R : ℝ} (hu : 0 < u) {N m : ℕ} (hN : R+u ≤ (N : ℝ)*u)
    {k : Lattice} (hk : k ∈ gridIndices m 1) (y : Space) (hy : ‖gridCenter u k-y‖ < R) :
    ∃ l ∈ gridIndices (m+N) 1, y ∈ gridBox u l := by
  suffices hy' : y ∈ ⋃ l ∈ gridIndices (m+N) 1, gridBox u l by
    obtain ⟨l,hl,hyl⟩ := mem_iUnion₂.mp hy'
    exact ⟨l,hl,hyl⟩
  apply cube_subset_gridBlocks hu (m+N)
  intro i
  have hk' := gridIndex_coordinate_bounds hk i
  have hl := mul_le_mul_of_nonneg_left hk'.1 hu.le
  have hr := mul_le_mul_of_nonneg_left hk'.2 hu.le
  have hi : |u*((k i : ℝ)+1/2)-y i| < R := by
    have hh := PiLp.norm_apply_le (gridCenter u k-y) i
    change |u*((k i : ℝ)+1/2)-y i| ≤ ‖gridCenter u k-y‖ at hh
    exact hh.trans_lt hy
  rw [abs_lt] at hi
  change -(2*((m+N : ℕ) : ℝ)*u)/2 ≤ y i ∧ y i ≤ 2*((m+N : ℕ) : ℝ)*u/2
  push_cast
  constructor <;> linarith [hi.1,hi.2]

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.InnerGrand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem familyTerm_innerBlock {q : ℕ} (hq : 0 < q) (φ : ℝ → ℝ) (β μ : ℝ)
    (k : Lattice) (n : ℕ) :
    familyTerm (gibbsFamily (quadraticBlock q φ 0) β μ) (innerGridBox ((q : ℝ)/4) k) n =
      Real.exp (μ*n)*partition φ β ((q : ℝ)/4-2) n := by
  have he : familyTerm (gibbsFamily (quadraticBlock q φ 0) β μ) (innerGridBox ((q : ℝ)/4) k) n =
      familyTerm (gibbsFamily (fun x y => φ ‖x-y‖-0) β (μ+β*0/2))
        (innerGridBox ((q : ℝ)/4) k) n := by
    simp only [mul_zero, zero_div, add_zero]
    unfold familyTerm familyIntegral
    congr 1
    apply setIntegral_congr_fun
      (measurableSet_generalConfigurations (measurableSet_innerGridBox _ _) (Fin n))
    intro x hx
    unfold gibbsFamily
    rw [gibbsEnergy_congr (W := fun x y => φ ‖x-y‖-0) x (fun i j =>
      quadraticBlock_on hq φ 0 (innerGridBox_subset_gridBox _ _ (hx i))
        (innerGridBox_subset_gridBox _ _ (hx j)))]
  rw [he, familyTerm_shift]
  simp only [mul_zero, zero_div, zero_mul, add_zero, innerGridBox]
  rw [setPartition_translate, setPartition, generalPartition_eq_partition]

theorem grandFinite_innerBlocks {t β μ : ℝ} (ht : 0 ≤ t) (hβ : 0 ≤ β)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8) {q : ℕ} (hq : 0 < q)
    (s : Finset Lattice) :
    GrandFinite (gibbsFamily (quadraticBlock q (physicalProfile t σ R) 0) β μ)
      (⋃ k ∈ s, innerGridBox ((q : ℝ)/4) k) := by
  have hcoeff : β*0/2*((q : ℝ)/4)^3 ≤
      β*(t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/(4+2/((q : ℝ)/4))^3 := by
    have ha : 0 ≤ t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2 := sub_nonneg.mpr hsmall
    simp only [mul_zero, zero_div, zero_mul]
    positivity
  have hh := grandFinite_quadraticBlocks (μ := μ) ht hβ (le_refl 0) hσ hR hs hsmall hq hcoeff s
  simp only [mul_zero, zero_div, add_zero] at hh
  apply hh.mono_set _ (gibbsFamily_nonneg _ _ _)
  exact iUnion₂_mono (fun k _ => innerGridBox_subset_gridBox _ k)

theorem grandFinite_fixedInnerBlocks {t β μ : ℝ} (ht : 0 ≤ t) (hβ : 0 ≤ β)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8) {q : ℕ} (hq : 0 < q)
    (s : Finset Lattice) (n : ℕ) :
    GrandFinite (fixedOccupationFamily (innerGridBox ((q : ℝ)/4)) s (fun _ => n)
      (gibbsFamily (quadraticBlock q (physicalProfile t σ R) 0) β μ))
      (⋃ k ∈ s, innerGridBox ((q : ℝ)/4) k) := by
  exact (grandFinite_innerBlocks ht hβ hσ hR hs hsmall hq s).fixedOccupation
    (A := innerGridBox ((q : ℝ)/4)) (s := s) (fun _ => n)
    (fun k _ => measurableSet_innerGridBox _ k)
    (fun ι _ => measurable_gibbsFamily
      (measurable_quadraticBlock q (measurable_physicalProfile t hσ hR hs) 0) β μ ι)
    (gibbsFamily_nonneg _ _ _)

theorem grandIntegral_fixedInnerBlocks {t β μ : ℝ} (ht : 0 ≤ t) (hβ : 0 ≤ β)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8) {q : ℕ} (hq : 0 < q)
    (s : Finset Lattice) (n : ℕ) :
    grandIntegral (fixedOccupationFamily (innerGridBox ((q : ℝ)/4)) s (fun _ => n)
      (gibbsFamily (quadraticBlock q (physicalProfile t σ R) 0) β μ))
      (⋃ k ∈ s, innerGridBox ((q : ℝ)/4) k) =
        (Real.exp (μ*n)*partition (physicalProfile t σ R) β ((q : ℝ)/4-2) n)^s.card := by
  have hu : 0 < (q : ℝ)/4 := by positivity
  rw [grandIntegral_fixedOccupation_product
    (measurable_quadraticBlock q (measurable_physicalProfile t hσ hR hs) 0)
    (quadraticBlock_symm q (physicalProfile t σ R) 0) β μ _ _ s
    (fun k _ => measurableSet_innerGridBox _ k)
    (fun _ _ _ _ hkl => innerGridBox_disjoint hu hkl)
    (fun _ _ _ _ hkl _ hx _ hy => quadraticBlock_cross hq _ 0 hkl
      (innerGridBox_subset_gridBox _ _ hx) (innerGridBox_subset_gridBox _ _ hy))
    (grandFinite_innerBlocks ht hβ hσ hR hs hsmall hq s)]
  simp only [familyTerm_innerBlock hq, Finset.prod_const]

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.LowerEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem occupation_disjoint_eq_fiber {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : κ → Set Space) (hd : Pairwise (fun k l => Disjoint (A k) (A l)))
    (c : ι → κ) (x : ι → Space) (hx : ∀ i, x i ∈ A (c i)) (k : κ) :
    occupation (A k) x = (Fintype.card {i // c i = k} : ℝ) := by
  unfold occupation
  congr 1
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro i
  constructor
  · intro hik
    by_contra hne
    exact Set.disjoint_left.mp (hd hne) (hx i) hik
  · intro he
    simpa only [he] using hx i

theorem card_eq_sum_fibers {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] (c : ι → κ) :
    (Fintype.card ι : ℝ) = ∑ k, (Fintype.card {i // c i = k} : ℝ) := by
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
    sum_comp_eq_sum_fibres c (fun _ => (1 : ℝ))

theorem kacLower_grid_double_lower {C : NNReal} (hC : LipschitzWith C kernel)
    {R u : ℝ} (hR : 0 < R) (hu : 0 < u) {N m : ℕ} (hN : R+u ≤ (N : ℝ)*u) :
    (gridIndices m 1).card*((1-kacRowError C R u)/u^3) ≤
      ∑ k ∈ gridIndices (m+N) 1, ∑ l ∈ gridIndices (m+N) 1,
        kacLower C R u (gridCenter u k) (gridCenter u l) := by
  have hrow (k : Lattice) (hk : k ∈ gridIndices m 1) :
      (1-kacRowError C R u)/u^3 ≤
        ∑ l ∈ gridIndices (m+N) 1, kacLower C R u (gridCenter u k) (gridCenter u l) := by
    apply (div_le_iff₀ (pow_pos hu 3)).2
    have hh := kacLower_row hC hR hu (gridCenter u k) (gridIndices (m+N) 1)
      (interior_grid_cover hu hN hk)
    simpa only [kacRowError, mul_comm] using hh
  have hs := Finset.sum_le_sum hrow
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  apply hs.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg (gridIndices_mono (Nat.le_add_right m N))
  intro k _ _
  exact Finset.sum_nonneg (fun l _ => le_max_left _ _)

theorem kac_energy_lower_fixed {C : NNReal} (hC : LipschitzWith C kernel)
    {R u : ℝ} (hR : 0 < R) (hu : 0 < u) {N m : ℕ} (hN : R+u ≤ (N : ℝ)*u)
    {ι : Type} [Fintype ι] (x : ι → Space) (n : ℕ)
    (hx : ∀ i, x i ∈ ⋃ k ∈ gridIndices (m+N) 1, innerGridBox u k)
    (hn : ∀ k ∈ gridIndices (m+N) 1, occupation (innerGridBox u k) x = (n : ℝ)) :
    ((gridIndices m 1).card*(n : ℝ)^2*((1-kacRowError C R u)/u^3)-
      (gridIndices (m+N) 1).card*n*scaledKernel R 0)/2 ≤
        gibbsEnergy (fun x y => scaledKernel R (x-y)) x := by
  let s := gridIndices (m+N) 1
  have hchoice (i : ι) : ∃ k : s, x i ∈ innerGridBox u k := by
    obtain ⟨k,hk,hxk⟩ := mem_iUnion₂.mp (hx i)
    exact ⟨⟨k,hk⟩,hxk⟩
  choose c hc using hchoice
  have hcard (k : s) : (Fintype.card {i // c i = k} : ℝ) = n := by
    rw [← occupation_disjoint_eq_fiber (fun k : s => innerGridBox u k)
      (fun k l hkl => innerGridBox_disjoint hu (fun h => hkl (Subtype.ext h))) c x hc k]
    exact hn k k.property
  have htotal : (Fintype.card ι : ℝ) = s.card*n := by
    calc
      (Fintype.card ι : ℝ) = ∑ k : s, (Fintype.card {i // c i = k} : ℝ) := card_eq_sum_fibers c
      _ = s.card*n := by simp only [hcard, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
  have hbound := kac_energy_lower hC hR c (fun k : s => gridCenter u k) x
    (fun i => gridBox_center_distance hu (innerGridBox_subset_gridBox _ _ (hc i)))
  have hsum : (∑ k : s, ∑ l : s, kacLower C R u (gridCenter u k) (gridCenter u l)*
      (Fintype.card {i // c i = k} : ℝ)*(Fintype.card {i // c i = l} : ℝ)) =
      (∑ k ∈ s, ∑ l ∈ s, kacLower C R u (gridCenter u k) (gridCenter u l))*(n : ℝ)^2 := by
    simp only [hcard]
    simp_rw [mul_assoc, ← pow_two]
    simp_rw [← Finset.sum_mul]
    congr 1
    calc
      _ = ∑ k ∈ s, ∑ l : s, kacLower C R u (gridCenter u k) (gridCenter u l) :=
        Finset.sum_coe_sort s (fun k => ∑ l : s, kacLower C R u (gridCenter u k) (gridCenter u l))
      _ = _ := Finset.sum_congr rfl (fun k _ =>
        Finset.sum_coe_sort s (fun l => kacLower C R u (gridCenter u k) (gridCenter u l)))
  rw [hsum, htotal] at hbound
  have hr := mul_le_mul_of_nonneg_right (kacLower_grid_double_lower (m := m) hC hR hu hN) (sq_nonneg (n : ℝ))
  change (gridIndices m 1).card*((1-kacRowError C R u)/u^3)*(n : ℝ)^2 ≤ _ at hr
  dsimp only [s] at hbound
  nlinarith only [hbound,hr]

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.LowerGibbs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem physicalProfile_le_innerBlock {t : ℝ} (ht : 1 < t)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n)
    {q : ℕ} (hq : 0 < q) (hu : 2 ≤ (q : ℝ)/4) (s : Finset Lattice)
    {x y : Space} (hx : x ∈ ⋃ k ∈ s, innerGridBox ((q : ℝ)/4) k)
    (hy : y ∈ ⋃ k ∈ s, innerGridBox ((q : ℝ)/4) k) :
    physicalProfile t σ R ‖x-y‖ ≤ quadraticBlock q (physicalProfile t σ R) 0 x y := by
  obtain ⟨k,_,hxk⟩ := mem_iUnion₂.mp hx
  obtain ⟨l,_,hyl⟩ := mem_iUnion₂.mp hy
  by_cases hkl : k = l
  · rw [quadraticBlock_on hq _ 0 (innerGridBox_subset_gridBox _ _ hxk)
      (hkl ▸ innerGridBox_subset_gridBox _ _ hyl), sub_zero]
  · rw [quadraticBlock_cross hq _ 0 hkl (innerGridBox_subset_gridBox _ _ hxk)
      (innerGridBox_subset_gridBox _ _ hyl)]
    exact physicalProfile_nonpos ht hσ hR ((by norm_num : (1 : ℝ) ≤ 2).trans
      (innerGridBox_separation hu hkl hxk hyl))

theorem kac_gibbsFamily_lower_fixed {C : NNReal} (hC : LipschitzWith C kernel)
    {t β a S μ : ℝ} (ht : 1 < t) (hβ : 0 ≤ β) (ha : 0 ≤ a) (hS : 0 < S)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    {q : ℕ} (hq : 0 < q) (hu : 2 ≤ (q : ℝ)/4) {N m : ℕ}
    (hN : S+(q : ℝ)/4 ≤ (N : ℝ)*((q : ℝ)/4)) (n : ℕ)
    {ι : Type} [Fintype ι] (x : ι → Space)
    (hx : ∀ i, x i ∈ ⋃ k ∈ gridIndices (m+N) 1, innerGridBox ((q : ℝ)/4) k) :
    Real.exp (β*(t*a)*kacLowerGain C S ((q : ℝ)/4) m N n)*
      fixedOccupationFamily (innerGridBox ((q : ℝ)/4)) (gridIndices (m+N) 1) (fun _ => n)
        (gibbsFamily (quadraticBlock q (physicalProfile t σ R) 0) β μ) ι x ≤
      gibbsFamily (fun x y => physicalProfile t (prepend a σ) (prepend S R) ‖x-y‖) β μ ι x := by
  have ht0 : 0 ≤ t := (lt_trans zero_lt_one ht).le
  have hu0 : 0 < (q : ℝ)/4 := by positivity
  unfold fixedOccupationFamily
  split_ifs with hn
  · have hgain := kac_energy_lower_fixed hC hS hu0 hN x n hx hn
    have href := gibbsEnergy_mono (U := fun x y => physicalProfile t σ R ‖x-y‖)
      (V := quadraticBlock q (physicalProfile t σ R) 0) x (fun i j => physicalProfile_le_innerBlock ht hσ hR hq hu
      (gridIndices (m+N) 1) (hx i) (hx j))
    have heq : (fun x y => physicalProfile t (prepend a σ) (prepend S R) ‖x-y‖) =
        (fun x y : Space => physicalProfile t σ R ‖x-y‖-(t*a)*scaledKernel S (x-y)) := by
      funext x y
      exact physicalProfile_prepend t hσ hR hs ‖x-y‖
    rw [heq]
    unfold gibbsFamily
    split_ifs
    · rw [← Real.exp_add, gibbsEnergy_sub, gibbsEnergy_mul_left]
      apply Real.exp_le_exp.mpr
      change kacLowerGain C S ((q : ℝ)/4) m N n ≤ _ at hgain
      have hg := mul_le_mul_of_nonneg_left hgain (mul_nonneg hβ (mul_nonneg ht0 ha))
      have hr := mul_le_mul_of_nonneg_left href hβ
      nlinarith only [hg,hr]
    · simp only [mul_zero, le_refl]
  · simp only [mul_zero]
    exact gibbsFamily_nonneg _ _ _ ι x

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.LowerComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem kac_grandIntegral_lower {C : NNReal} (hC : LipschitzWith C kernel)
    {t β a S : ℝ} (ht : 1 < t) (hβ : 0 ≤ β) (ha : 0 ≤ a) (hS : 0 < S)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    {q : ℕ} (hq : 0 < q) (hu : 2 ≤ (q : ℝ)/4) {N m : ℕ}
    (hN : S+(q : ℝ)/4 ≤ (N : ℝ)*((q : ℝ)/4)) (n : ℕ) (h : ℝ)
    (hF : GrandFinite (fixedOccupationFamily (innerGridBox ((q : ℝ)/4))
      (gridIndices (m+N) 1) (fun _ => n)
      (gibbsFamily (quadraticBlock q (physicalProfile t σ R) 0) β (t*h)))
      (⋃ k ∈ gridIndices (m+N) 1, innerGridBox ((q : ℝ)/4) k))
    (hG : GrandFinite
      (gibbsFamily (fun x y => physicalProfile t (prepend a σ) (prepend S R) ‖x-y‖) β (t*h))
      (cube (2*((m+N : ℕ)+1)*((q : ℝ)/4)))) :
    Real.exp (β*(t*a)*kacLowerGain C S ((q : ℝ)/4) m N n)*
      grandIntegral (fixedOccupationFamily (innerGridBox ((q : ℝ)/4))
        (gridIndices (m+N) 1) (fun _ => n)
        (gibbsFamily (quadraticBlock q (physicalProfile t σ R) 0) β (t*h)))
        (⋃ k ∈ gridIndices (m+N) 1, innerGridBox ((q : ℝ)/4) k) ≤
      grandPartition (physicalProfile t (prepend a σ) (prepend S R)) t β h
        (2*((m+N : ℕ)+1)*((q : ℝ)/4)) := by
  have hu0 : 0 < (q : ℝ)/4 := by positivity
  let D := ⋃ k ∈ gridIndices (m+N) 1, innerGridBox ((q : ℝ)/4) k
  let L := 2*((m+N : ℕ)+1)*((q : ℝ)/4)
  have hD : MeasurableSet D := MeasurableSet.biUnion (Finset.finite_toSet _).countable
    (fun k _ => measurableSet_innerGridBox _ k)
  have hsub : D ⊆ cube L := iUnion₂_subset (fun k hk => innerGridBox_subset_cube hu0.le hk)
  let F : ConfigFamily := fixedOccupationFamily (innerGridBox ((q : ℝ)/4))
    (gridIndices (m+N) 1) (fun _ => n)
    (gibbsFamily (quadraticBlock q (physicalProfile t σ R) 0) β (t*h))
  let G : ConfigFamily := gibbsFamily
    (fun x y => physicalProfile t (prepend a σ) (prepend S R) ‖x-y‖) β (t*h)
  let c : ℝ := Real.exp (β*(t*a)*kacLowerGain C S ((q : ℝ)/4) m N n)
  have hFc : GrandFinite (fun ι _ x => c*F ι x) D := hF.const_mul c
  have hGd : GrandFinite G D := hG.mono_set hsub (gibbsFamily_nonneg _ _ _)
  have hpoint : ∀ j (x : Fin j → Space), (∀ i, x i ∈ D) →
      c*F (Fin j) x ≤ G (Fin j) x := by
    intro j x hx
    exact kac_gibbsFamily_lower_fixed hC ht hβ ha hS hσ hR hs hq hu (m := m) hN n x hx
  have hb : grandIntegral (fun ι _ x => c*F ι x) D ≤ grandIntegral G D :=
    grandIntegral_mono (fun ι _ x => c*F ι x) G hD
      (fun j => hFc.integrable (Fin j)) (fun j => hGd.integrable (Fin j))
      hFc.summable hGd.summable hpoint
  have hb' := hb.trans (grandIntegral_mono_set _ hsub (gibbsFamily_nonneg _ _ _)
    (fun j => hG.integrable (Fin j)) hGd.summable hG.summable)
  rw [grandIntegral_const_mul] at hb'
  change c*grandIntegral F D ≤ grandIntegral G (cube L) at hb'
  rw [show grandIntegral G (cube L) = grandPartition (physicalProfile t (prepend a σ)
      (prepend S R)) t β h L from grandIntegral_radial _ _ _ _ _] at hb'
  exact hb'

theorem physical_kac_grand_lower {C : NNReal} (hC : LipschitzWith C kernel)
    {t β a S : ℝ} (ht : 1 < t) (hβ : 0 < β) (ha : 0 ≤ a) (hS : 1 ≤ S)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(a+∑' j, σ j) ≤ (t^2/8)/8)
    {q : ℕ} (hq : 0 < q) (hu : 2 < (q : ℝ)/4) {N m : ℕ}
    (hN : S+(q : ℝ)/4 ≤ (N : ℝ)*((q : ℝ)/4)) (n : ℕ) (h : ℝ) :
    Real.exp (β*(t*a)*kacLowerGain C S ((q : ℝ)/4) m N n)*
      (Real.exp (t*h*n)*partition (physicalProfile t σ R) β ((q : ℝ)/4-2) n)^
        (gridIndices (m+N) 1).card ≤
      grandPartition (physicalProfile t (prepend a σ) (prepend S R)) t β h
        (2*((m+N : ℕ)+1)*((q : ℝ)/4)) := by
  have ht0 := lt_trans zero_lt_one ht
  have hK := kernelHeight_pos.le
  have hta : 0 ≤ 2197*t*kernelHeight*a := by positivity
  have hsm : 2197*t*kernelHeight*(∑' j, σ j)/2 ≤ t^2/8 := by
    nlinarith only [hsmall, hta, sq_nonneg t]
  have hF := grandFinite_fixedInnerBlocks (μ := t*h) ht0.le hβ.le hσ hR hs hsm hq
    (gridIndices (m+N) 1) n
  have hsm' : 2197*t*kernelHeight*(∑' j, prepend a σ j) ≤ (t^2/8)/8 := by
    rw [tsum_prepend a hs]; exact hsmall
  have hG := physical_gibbs_finite ht0.le hβ.le (prepend_nonneg ha hσ)
    (prepend_ge_one hS hR) (summable_prepend a hs) hsm'
    (show volume (cube (2*((m+N : ℕ)+1)*((q : ℝ)/4))) ≠ ⊤ by rw [volume_cube]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (t*h)
  have hb := kac_grandIntegral_lower hC ht hβ.le ha (zero_lt_one.trans_le hS) hσ hR hs hq
    hu.le hN n h hF hG
  rw [grandIntegral_fixedInnerBlocks ht0.le hβ.le hσ hR hs hsm hq] at hb
  exact hb

theorem physical_kac_log_lower {C : NNReal} (hC : LipschitzWith C kernel)
    {t β a S : ℝ} (ht : 1 < t) (hβ : 0 < β) (ha : 0 ≤ a) (hS : 1 ≤ S)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(a+∑' j, σ j) ≤ (t^2/8)/8)
    {q : ℕ} (hq : 0 < q) (hu : 2 < (q : ℝ)/4) {N m : ℕ}
    (hN : S+(q : ℝ)/4 ≤ (N : ℝ)*((q : ℝ)/4)) (n : ℕ) (h : ℝ) :
    β*(t*a)*kacLowerGain C S ((q : ℝ)/4) m N n+
      (gridIndices (m+N) 1).card*(t*h*n+Real.log (partition (physicalProfile t σ R) β ((q : ℝ)/4-2) n)) ≤
      Real.log (grandPartition (physicalProfile t (prepend a σ) (prepend S R)) t β h
        (2*((m+N : ℕ)+1)*((q : ℝ)/4))) := by
  have ht0 := lt_trans zero_lt_one ht
  have hK := kernelHeight_pos.le
  have hta : 0 ≤ 2197*t*kernelHeight*a := by positivity
  have hsm : 2197*t*kernelHeight*(∑' j, σ j)/2 ≤ t^2/8 := by
    nlinarith only [hsmall, hta, sq_nonneg t]
  have hb' := physical_kac_grand_lower hC ht hβ ha hS hσ hR hs hsmall hq hu (m := m) hN n h
  have hz := partition_pos (measurable_radialPotential (measurable_physicalProfile t hσ hR hs))
    hβ.le (sub_pos.mpr hu) (physicalProfile_stable ht0.le hσ hR hs hsm) n
  have hp : 0 < Real.exp (β*(t*a)*kacLowerGain C S ((q : ℝ)/4) m N n)*
      (Real.exp (t*h*n)*partition (physicalProfile t σ R) β ((q : ℝ)/4-2) n)^
        (gridIndices (m+N) 1).card := mul_pos (Real.exp_pos _) (pow_pos (mul_pos (Real.exp_pos _) hz) _)
  have hl := Real.log_le_log hp hb'
  rw [Real.log_mul (Real.exp_pos _).ne' (pow_pos (mul_pos (Real.exp_pos _) hz) _).ne',
    Real.log_exp, Real.log_pow, Real.log_mul (Real.exp_pos _).ne' hz.ne', Real.log_exp] at hl
  exact hl

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.LowerBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Filter
namespace ContinuumTemperature

theorem grid_card_outer_ratio_tendsto {u : ℝ} (hu : 0 < u) (K N : ℕ) :
    Tendsto (fun m : ℕ => ((gridIndices (m+K) 1).card : ℝ)/(2*((m+N : ℕ)+1)*u)^3)
      atTop (𝓝 (1/u^3)) := by
  have hi : Tendsto (fun m : ℕ => (m : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hn := ((hi.const_mul (2*(K : ℝ)+1)).const_add 2).pow 3
  have hd := (((hi.const_mul ((N : ℝ)+1)).const_add 1).const_mul (2*u)).pow 3
  have hz : (2*u*(1+((N : ℝ)+1)*0))^3 ≠ 0 := by positivity
  have hh := hn.div hd hz
  have hh' : Tendsto (fun m : ℕ => (2+(2*(K : ℝ)+1)*(m : ℝ)⁻¹)^3/
      (2*u*(1+((N : ℝ)+1)*(m : ℝ)⁻¹))^3) atTop (𝓝 (1/u^3)) := by
    have he : (2 : ℝ)^3/(2*u)^3 = 1/u^3 := by
      field_simp
    simpa only [Pi.div_def, mul_zero, add_zero, mul_one, he] using hh
  apply hh'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hmn : (m : ℝ)+(N : ℝ)+1 ≠ 0 := by positivity
  rw [card_gridIndices]
  push_cast
  field_simp
  ring

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.LowerPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem physical_kac_pressure_lower {C : NNReal} (hC : LipschitzWith C kernel)
    {t β a S : ℝ} (ht : 1 < t) (hβ : 0 < β) (ha : 0 ≤ a) (hS : 1 ≤ S)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(a+∑' j, σ j) ≤ (t^2/8)/8)
    {q : ℕ} (hq : 0 < q) (hu : 2 < (q : ℝ)/4) (n : ℕ) (h : ℝ) :
    (t*h*((n : ℝ)/((q : ℝ)/4)^3)+
      Real.log (partition (physicalProfile t σ R) β ((q : ℝ)/4-2) n)/((q : ℝ)/4)^3+
      β*(t*a)/2*(((n : ℝ)/((q : ℝ)/4)^3)^2*(1-kacRowError C S ((q : ℝ)/4))-
        ((n : ℝ)/((q : ℝ)/4)^3)*scaledKernel S 0))/t ≤
      physicalPressure (physicalProfile t (prepend a σ) (prepend S R)) t (β,h) := by
  have ht0 := lt_trans zero_lt_one ht
  have hu0 : 0 < (q : ℝ)/4 := by positivity
  obtain ⟨N, hN'⟩ := exists_nat_ge ((S+(q : ℝ)/4)/((q : ℝ)/4))
  have hN : S+(q : ℝ)/4 ≤ (N : ℝ)*((q : ℝ)/4) := (div_le_iff₀ hu0).1 hN'
  have hσ' := prepend_nonneg ha hσ
  have hR' := prepend_ge_one hS hR
  have hs' := summable_prepend a hs
  have hsm : 2197*t*kernelHeight*(∑' j, prepend a σ j)/2 ≤ t^2/8 := by
    rw [tsum_prepend a hs]
    nlinarith only [hsmall, sq_nonneg t]
  have hL : Tendsto (fun m : ℕ => 2*((m+N : ℕ)+1)*((q : ℝ)/4)) atTop atTop := by
    have hh := (((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat (N+1))).const_mul_atTop
      (by norm_num : (0 : ℝ) < 2))).atTop_mul_const hu0
    simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, add_assoc] using hh
  have hright := (physicalPressure_tendsto
    (measurable_radialPotential (measurable_physicalProfile t hσ' hR' hs')) ht hβ.le
    (physicalProfile_stable ht0.le hσ' hR' hs' hsm)
    (fun r _ => physicalProfile_le_core ht0.le hσ' hR' r) (h := h)).comp hL
  let u := (q : ℝ)/4
  let A := (t*h*n+Real.log (partition (physicalProfile t σ R) β (u-2) n))
  let B := (n : ℝ)^2*((1-kacRowError C S u)/u^3)
  let D := (n : ℝ)*scaledKernel S 0
  have hrat₀ := grid_card_outer_ratio_tendsto hu0 0 N
  have hratN := grid_card_outer_ratio_tendsto hu0 N N
  have hleft := (((hrat₀.const_mul B).sub (hratN.const_mul D)).const_mul (β*(t*a)/2)).add
    (hratN.const_mul A)
  have hb := le_of_tendsto_of_tendsto (hleft.div_const t) hright
    (Filter.Eventually.of_forall (fun m : ℕ => ?_))
  · refine le_trans ?_ hb
    apply le_of_eq
    dsimp only [A,B,D,u]
    ring
  have hh := physical_kac_log_lower hC ht hβ ha hS hσ hR hs hsmall hq hu (m := m) hN n h
  have hv : 0 < t*(2*((m+N : ℕ)+1)*u)^3 := by dsimp only [u]; positivity
  have hd := div_le_div_of_nonneg_right hh hv.le
  convert hd using 1 <;> simp only [Function.comp_apply, Nat.add_zero, kacLowerGain, A, B, D, u,
    div_eq_mul_inv, mul_inv_rev]
  ring

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.LowerKac
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Filter
namespace ContinuumTemperature

theorem kacTrialValue_tendsto {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {t β B : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hst : ∀ (n : ℕ) (x : Fin n → Space), ((-B*n : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r)
    (C : NNReal) (a h : ℝ) {d : ℝ} (hd : 0 ≤ d) :
    Tendsto (kacTrialValue φ C t β a h d) atTop
      (𝓝 ((t*h*d-canonicalDensity φ β d+β*(t*a)/2*d^2)/t)) := by
  have hi : Tendsto (fun u : ℝ => u⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hℓ : Tendsto (fun u : ℝ => u-2) atTop atTop := by
    simpa only [id_eq, sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-2 : ℝ) tendsto_id
  have hr : Tendsto (fun u : ℝ => (u-2)^3/u^3) atTop (𝓝 1) := by
    have hh := ((hi.const_mul 2).const_sub 1).pow 3
    have he : Tendsto (fun u : ℝ => (1-2*u⁻¹)^3) atTop (𝓝 1) := by simpa using hh
    apply he.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    field_simp
  have hden := ((tendsto_densityFilter_iff.mp (floor_density_tendsto hd)).2).comp hℓ
  have hn : Tendsto (fun u : ℝ => (⌊d*(u-2)^3⌋₊ : ℝ)/u^3) atTop (𝓝 d) := by
    have hh : Tendsto (fun u : ℝ => ((⌊d*(u-2)^3⌋₊ : ℝ)/(u-2)^3)*((u-2)^3/u^3))
        atTop (𝓝 d) := by simpa only [mul_one, Function.comp_apply] using hden.mul hr
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with u hu
    have hne : u-2 ≠ 0 := (sub_pos.mpr hu).ne'
    field_simp
  have hc := (finiteCanonical_tendsto hφ ht hβ hst hcore hd).comp ((floor_density_tendsto hd).comp hℓ)
  have hz : Tendsto (fun u : ℝ => Real.log (partition φ β (u-2) ⌊d*(u-2)^3⌋₊)/u^3)
      atTop (𝓝 (-canonicalDensity φ β d)) := by
    have hh : Tendsto (fun u : ℝ => -finiteCanonical φ β (u-2) ⌊d*(u-2)^3⌋₊*((u-2)^3/u^3))
        atTop (𝓝 (-canonicalDensity φ β d)) := by
      simpa only [mul_one, Function.comp_apply] using hc.neg.mul hr
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with u hu
    have hne : u-2 ≠ 0 := (sub_pos.mpr hu).ne'
    unfold finiteCanonical
    field_simp
  have hw : Tendsto (fun u : ℝ => scaledKernel (u^2) 0) atTop (𝓝 0) := by
    simpa [scaledKernel, scaledKernelProfile] using ((hi.pow 2).pow 3).mul_const (kernelProfile 0)
  have he := (((hn.const_mul (t*h)).add hz).add
    ((((hn.pow 2).mul ((kacRowError_sq_tendsto C).const_sub 1)).sub
      (hn.mul hw)).const_mul (β*(t*a)/2))).div_const t
  convert he using 1 <;> first | rfl | (congr 1; ring)

theorem physical_kac_lower_density_eventually_oai {C : NNReal} (hC : LipschitzWith C kernel)
    {t β a : ℝ} (ht : 1 < t) (hβ : 0 < β) (ha : 0 ≤ a)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(a+∑' j, σ j) ≤ (t^2/8)/8)
    (h : ℝ) {d : ℝ} (hd : 0 ≤ d) {c : ℝ}
    (hc : c < (t*h*d-canonicalDensity (physicalProfile t σ R) β d+β*(t*a)/2*d^2)/t) :
    ∀ᶠ q : ℕ in atTop, c <
      physicalPressure (physicalProfile t (prepend a σ) (prepend (((q : ℝ)/4)^2) R)) t (β,h) := by
  have ht0 := lt_trans zero_lt_one ht
  have hK := kernelHeight_pos.le
  have hta : 0 ≤ 2197*t*kernelHeight*a := by positivity
  have hsm : 2197*t*kernelHeight*(∑' j, σ j)/2 ≤ t^2/8 := by
    nlinarith only [hsmall, hta, sq_nonneg t]
  have hh := (kacTrialValue_tendsto
    (measurable_radialPotential (measurable_physicalProfile t hσ hR hs)) ht hβ.le
    (physicalProfile_stable ht0.le hσ hR hs hsm)
    (fun r _ => physicalProfile_le_core ht0.le hσ hR r) C a h hd).comp
      (tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 4))
  filter_upwards [hh.eventually_const_lt hc, eventually_ge_atTop (12 : ℕ)] with q hq hq12
  have hq0 : 0 < q := by omega
  have hu : 2 < (q : ℝ)/4 := by
    have hq' : (12 : ℝ) ≤ q := by exact_mod_cast hq12
    linarith
  have hS : 1 ≤ ((q : ℝ)/4)^2 := by nlinarith
  exact hq.trans_le (physical_kac_pressure_lower hC ht hβ ha hS hσ hR hs hsmall hq0 hu _ h)

end ContinuumTemperature
end

end OAI
end

theorem solution : type_of% @OAI.ContinuumTemperature.physical_kac_lower_density_eventually_oai := @OAI.ContinuumTemperature.physical_kac_lower_density_eventually_oai
