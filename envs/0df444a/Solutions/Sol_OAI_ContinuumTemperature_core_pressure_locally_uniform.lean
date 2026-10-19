-- Prove2me | solution 1 for OAI.ContinuumTemperature.core_pressure_locally_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:06:03.988254+00:00
-- url     : https://prove2.me/submissions/21daa630-9c72-4883-bc3a-b0235c6d87b7

import Mathlib
import Definitions.Def_ContinuumTransition
import Definitions.Def_OAIQWCT000
import Theorems.Thm_OAI_ContinuumTemperature_convex_pointwise_locally_uniform

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
alias Finset.prod_le_prod₀ := Finset.prod_le_prod
end OAICompat434
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

theorem measurableSet_cube (L : ℝ) : MeasurableSet (cube L) :=
  (isCompact_cube L).measurableSet

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

theorem boltzmann_add (φ : ℝ → ℝ) (β γ : ℝ) {N : ℕ} (x : Fin N → Space) :
    boltzmann φ (β + γ) x = boltzmann φ β x * boltzmann φ γ x := by
  unfold boltzmann
  split_ifs
  · ring
  · rw [← Real.exp_add]
    congr 1
    ring

theorem boltzmann_rpow (φ : ℝ → ℝ) (β : ℝ) {p : ℝ} (hp : 0 < p)
    {N : ℕ} (x : Fin N → Space) :
    boltzmann φ β x ^ p = boltzmann φ (p * β) x := by
  unfold boltzmann
  split_ifs
  · exact Real.zero_rpow hp.ne'
  · rw [← Real.exp_mul]
    congr 1
    ring

theorem integral_boltzmann_logconvex {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {B : ℝ}
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (L : ℝ) (N : ℕ) {β γ a b : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    (∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ (a * β + b * γ) x) ≤
      (∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ β x) ^ a *
      (∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ γ x) ^ b := by
  let μ : Measure (Fin N → Space) :=
    volume.restrict {x : Fin N → Space | ∀ i, x i ∈ cube L}
  have hp (c u : ℝ) (hc : 0 < c) (x : Fin N → Space) :
      ‖boltzmann φ (c * u) x‖ ^ (1 / c) = boltzmann φ u x := by
    rw [Real.norm_eq_abs, abs_of_nonneg (boltzmann_nonneg φ (c * u) x),
      boltzmann_rpow φ (c * u) (one_div_pos.mpr hc)]
    congr 1
    field_simp
  have hLp (c u : ℝ) (hc : 0 < c) (hu : 0 < u) :
      MemLp (fun x : Fin N → Space => boltzmann φ (c * u) x) (ENNReal.ofReal (1 / c)) μ := by
    have A : ENNReal.ofReal (1 / c) ≠ 0 := by positivity
    have B' : ENNReal.ofReal (1 / c) ≠ ∞ := ENNReal.ofReal_ne_top
    rw [← memLp_norm_rpow_iff _ A B', ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / c),
      ENNReal.div_self A B', memLp_one_iff_integrable]
    · apply (integrableOn_boltzmann hφ hu.le hstable L N).congr
      exact ae_of_all _ (fun x => (hp c u hc x).symm)
    · exact (measurable_boltzmann hφ (c * u) N).aestronglyMeasurable
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (Real.holderConjugate_one_div ha hb hab)
    (ae_of_all μ (boltzmann_nonneg φ (a * β)))
    (ae_of_all μ (boltzmann_nonneg φ (b * γ)))
    (hLp a β ha hβ) (hLp b γ hb hγ)
  simp only [one_div_one_div] at hHolder
  convert hHolder using 1
  · exact integral_congr_ae (ae_of_all μ (boltzmann_add φ (a * β) (b * γ)))
  · congr 2
    · apply integral_congr_ae
      filter_upwards [] with x
      simpa only [Real.norm_eq_abs, abs_of_nonneg (boltzmann_nonneg φ (a * β) x)]
        using (hp a β ha x).symm
    · apply integral_congr_ae
      filter_upwards [] with x
      simpa only [Real.norm_eq_abs, abs_of_nonneg (boltzmann_nonneg φ (b * γ) x)]
        using (hp b γ hb x).symm

theorem integral_boltzmann_pos {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {β B L : ℝ} (hβ : 0 ≤ β) (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (N : ℕ) :
    0 < ∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ β x := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ (boltzmann_nonneg φ β)) (integrableOn_boltzmann hφ hβ hstable L N)]
  apply lt_of_lt_of_le ((isOpen_openConfigurations L N).measure_pos volume
    (openConfigurations_nonempty hL N))
  apply measure_mono
  intro x hx
  exact ⟨(boltzmann_pos_of_injective φ β hx.2).ne',
    fun i k => ⟨(hx.1 i k).1.le, (hx.1 i k).2.le⟩⟩

theorem convexOn_log_integral_boltzmann {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {B L : ℝ} (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (N : ℕ) : ConvexOn ℝ (Ioi 0) (fun β => Real.log
      (∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ β x)) := by
  refine convexOn_iff_forall_pos.mpr ⟨convex_Ioi _, ?_⟩
  intro β hβ γ hγ a b ha hb hab
  simp only [smul_eq_mul]
  have hβ' := integral_boltzmann_pos hφ hβ.le hL hstable N
  have hγ' := integral_boltzmann_pos hφ hγ.le hL hstable N
  have hac : 0 < a * β + b * γ := add_pos (mul_pos ha hβ) (mul_pos hb hγ)
  have hc := integral_boltzmann_pos hφ hac.le hL hstable N
  have hHolder := integral_boltzmann_logconvex hφ hstable L N hβ hγ ha hb hab
  calc
    _ ≤ Real.log ((∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ β x) ^ a *
          (∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ γ x) ^ b) :=
      Real.log_le_log hc hHolder
    _ = _ := by rw [Real.log_mul (Real.rpow_pos_of_pos hβ' a).ne' (Real.rpow_pos_of_pos hγ' b).ne',
      Real.log_rpow hβ', Real.log_rpow hγ']

theorem convexOn_log_partition {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {B L : ℝ} (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (N : ℕ) : ConvexOn ℝ (Ioi 0) (fun β => Real.log (partition φ β L N)) := by
  by_cases hN : N = 0
  · simp only [hN, partition, ↓reduceIte, Real.log_one]
    exact convexOn_const _ (convex_Ioi _)
  · have hlog (β : ℝ) (hβ : 0 < β) : Real.log (partition φ β L N) =
        Real.log (1 / (N.factorial : ℝ)) + Real.log
          (∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ β x) := by
      unfold partition
      rw [ite_eq_right hN, Real.log_mul (one_div_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)))
        (integral_boltzmann_pos hφ hβ.le hL hstable N).ne']
    have hc := convexOn_log_integral_boltzmann hφ hL hstable N
    refine convexOn_iff_forall_pos.mpr ⟨convex_Ioi _, ?_⟩
    intro β hβ γ hγ a b ha hb hab
    simp only [smul_eq_mul]
    rw [hlog _ (add_pos (mul_pos ha hβ) (mul_pos hb hγ)), hlog β hβ, hlog γ hγ]
    have hi := hc.2 hβ hγ ha.le hb.le hab
    simp only [smul_eq_mul] at hi
    have hcst : a * Real.log (1 / (N.factorial : ℝ)) +
        b * Real.log (1 / (N.factorial : ℝ)) = Real.log (1 / (N.factorial : ℝ)) := by
      rw [← add_mul, hab, one_mul]
    nlinarith only [hi, hcst]

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

theorem tsum_logconvex_bound {f g k : ℕ → ℝ} {a b : ℝ}
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (hk : Summable k)
    (hfS : Summable f) (hgS : Summable g) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) (hbound : ∀ n, k n ≤ f n ^ a * g n ^ b) :
    (∑' n, k n) ≤ (∑' n, f n) ^ a * (∑' n, g n) ^ b := by
  have heq (x c : ℝ) (hx : 0 ≤ x) (hc : 0 < c) : (x ^ c) ^ (1 / c) = x := by
    rw [← Real.rpow_mul hx, mul_one_div_cancel hc.ne', Real.rpow_one]
  have hu : Summable (fun n => (f n ^ a) ^ (1 / a)) := by
    simpa only [heq _ a (hf _) ha] using hfS
  have hv : Summable (fun n => (g n ^ b) ^ (1 / b)) := by
    simpa only [heq _ b (hg _) hb] using hgS
  obtain ⟨hS, hH⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    (Real.holderConjugate_one_div ha hb hab)
    (fun n => Real.rpow_nonneg (hf n) a) (fun n => Real.rpow_nonneg (hg n) b) hu hv
  simp only [heq _ a (hf _) ha, heq _ b (hg _) hb, one_div_one_div] at hH
  exact (hk.tsum_le_tsum hbound hS).trans hH

theorem convexOn_log_tsum {E : Type u_1} [AddCommGroup E] [Module ℝ E]
    {s : Set E} (hs : Convex ℝ s) (F : ℕ → E → ℝ)
    (hpos : ∀ n x, x ∈ s → 0 < F n x)
    (hconv : ∀ n, ConvexOn ℝ s (fun x => Real.log (F n x)))
    (hS : ∀ x, x ∈ s → Summable (fun n => F n x)) :
    ConvexOn ℝ s (fun x => Real.log (∑' n, F n x)) := by
  have hp (x : E) (hx : x ∈ s) : 0 < ∑' n, F n x :=
    (hpos 0 x hx).trans_le ((hS x hx).le_tsum 0 (fun n _ => (hpos n x hx).le))
  refine convexOn_iff_forall_pos.mpr ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz := hs hx hy ha.le hb.le hab
  have hbnd (n : ℕ) : F n (a • x + b • y) ≤ F n x ^ a * F n y ^ b := by
    have hc := (hconv n).2 hx hy ha.le hb.le hab
    simp only [smul_eq_mul] at hc
    apply (Real.log_le_log_iff (hpos n _ hz) (mul_pos
      (Real.rpow_pos_of_pos (hpos n x hx) a) (Real.rpow_pos_of_pos (hpos n y hy) b))).mp
    rw [Real.log_mul (Real.rpow_pos_of_pos (hpos n x hx) a).ne'
      (Real.rpow_pos_of_pos (hpos n y hy) b).ne', Real.log_rpow (hpos n x hx),
      Real.log_rpow (hpos n y hy)]
    exact hc
  have hHolder := tsum_logconvex_bound (fun n => (hpos n x hx).le)
    (fun n => (hpos n y hy).le) (hS _ hz) (hS x hx) (hS y hy) ha hb hab hbnd
  calc
    _ ≤ Real.log ((∑' n, F n x) ^ a * (∑' n, F n y) ^ b) :=
      Real.log_le_log (hp _ hz) hHolder
    _ = _ := by rw [Real.log_mul (Real.rpow_pos_of_pos (hp x hx) a).ne'
      (Real.rpow_pos_of_pos (hp y hy) b).ne',
      Real.log_rpow (hp x hx), Real.log_rpow (hp y hy)]; rfl

theorem convexOn_log_grandPartition {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {B L : ℝ} (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) (t : ℝ) :
    ConvexOn ℝ {x : ℝ × ℝ | 0 < x.1}
      (fun x => Real.log (grandPartition φ t x.1 x.2 L)) := by
  have hdomain : Convex ℝ {x : ℝ × ℝ | 0 < x.1} := by
    intro x hx y hy a b ha hb hab
    change 0 < a * x.1 + b * y.1
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have hb' : b = 1 := by simpa using hab
      simpa [hb'] using hy
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' hx) (mul_nonneg hb hy.le)
  apply convexOn_log_tsum hdomain
    (fun N x => Real.exp (t * x.2 * N) * partition φ x.1 L N)
  · intro N x hx
    exact mul_pos (Real.exp_pos _) (partition_pos hφ hx.le hL hstable N)
  · intro N
    have hc := convexOn_log_partition hφ hL hstable N
    refine convexOn_iff_forall_pos.mpr ⟨hdomain, ?_⟩
    intro x hx y hy a b ha hb hab
    have hz := hdomain hx hy ha.le hb.le hab
    have log_eq (z : ℝ × ℝ) (hz : 0 < z.1) :
        Real.log (Real.exp (t * z.2 * N) * partition φ z.1 L N) =
          t * z.2 * N + Real.log (partition φ z.1 L N) := by
      rw [Real.log_mul (Real.exp_pos _).ne'
        (partition_pos hφ hz.le hL hstable N).ne', Real.log_exp]
    rw [log_eq _ hz, log_eq _ hx, log_eq _ hy]
    simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    have hi := hc.2 hx hy ha.le hb.le hab
    simp only [smul_eq_mul] at hi
    nlinarith only [hi]
  · intro x hx
    exact summable_grandPartition hφ hx.le hL.le hstable t x.2

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
-- module Solutions.OAIQW_ContinuumTemperature.PressureDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem canonicalPressure_nonneg {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B μ : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    0 ≤ canonicalPressure φ β μ := by
  have hh := le_csSup (canonicalPressure_bddAbove hφ ht hβ hstable hcore (μ := μ))
    (mem_image_of_mem (fun d : ℝ => μ*d-canonicalDensity φ β d) (show 0 ∈ Ici (0 : ℝ) by simp))
  simpa only [canonicalDensity_zero hφ ht hβ hstable hcore, mul_zero, sub_zero,
    canonicalPressure] using hh

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PressureRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem convexOn_physicalPressure {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t B : ℝ} (ht : 1 < t)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    ConvexOn ℝ pressureDomain (physicalPressure φ t) := by
  have hcD : Convex ℝ pressureDomain :=
    (convexOn_log_grandPartition hφ (by norm_num : (0 : ℝ) < 1) hstable t).1
  refine ⟨hcD, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz := hcD hx hy ha hb hab
  have hl := physicalPressure_tendsto hφ ht (le_of_lt hz) hstable hcore (h := (a • x+b • y).2)
  have hr := ((physicalPressure_tendsto hφ ht (le_of_lt hx) hstable hcore (h := x.2)).const_mul a).add
    ((physicalPressure_tendsto hφ ht (le_of_lt hy) hstable hcore (h := y.2)).const_mul b)
  simp only [smul_eq_mul]
  apply le_of_tendsto_of_tendsto hl hr
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have hh := (convexOn_log_grandPartition hφ hL hstable t).2 hx hy ha hb hab
  simp only [smul_eq_mul] at hh
  have hV : 0 ≤ t*L^3 := mul_nonneg (by linarith) (pow_pos hL 3).le
  have hbound := div_le_div_of_nonneg_right hh hV
  simpa only [add_div, mul_div_assoc] using hbound

theorem isOpen_pressureDomain : IsOpen pressureDomain :=
  isOpen_lt continuous_const continuous_fst

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PackingGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology BigOperators
open Filter MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem isPacking_zero (L : ℝ) : IsPacking L 0 := by
  refine ⟨Fin.elim0, ?_, ?_⟩ <;> intro i <;> exact Fin.elim0 i

theorem packing_card_cubeCells {ι : Type u_1} [Fintype ι] {L : ℝ}
    (x : ι → Space) (hx : ∀ i, x i ∈ cube L)
    (hsep : ∀ i j, i ≠ j → 1 ≤ ‖x i-x j‖) : Fintype.card ι ≤ (cubeCells L).card := by
  let f : ι → {k // k ∈ cubeCells L} := fun i =>
    ⟨cellIndex (x i), cellIndex_mem_cubeCells (hx i)⟩
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hh := dist_lt_one_of_cellIndex_eq (congrArg Subtype.val hij)
    exact (not_lt_of_ge (hsep i j hne)) hh
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

theorem IsPacking.card_bound {L : ℝ} {n : ℕ} (h : IsPacking L n) :
    n ≤ (cubeCells L).card := by
  obtain ⟨x,hx,hs⟩ := h
  simpa only [Fintype.card_fin] using packing_card_cubeCells x hx hs

theorem packingNumber_realized (L : ℝ) : IsPacking L (packingNumber L) := by
  exact Nat.findGreatest_spec (show 0 ≤ (cubeCells L).card from Nat.zero_le _)
    (isPacking_zero L)

theorem IsPacking.le_packingNumber {L : ℝ} {n : ℕ} (h : IsPacking L n) :
    n ≤ packingNumber L := by
  exact Nat.le_findGreatest h.card_bound h

theorem card_le_packingNumber {ι : Type u_1} [Fintype ι] {L : ℝ}
    (x : ι → Space) (hx : ∀ i, x i ∈ cube L)
    (hsep : ∀ i j, i ≠ j → 1 ≤ ‖x i-x j‖) : Fintype.card ι ≤ packingNumber L := by
  let e := Fintype.equivFin ι
  apply IsPacking.le_packingNumber
  exact ⟨fun i => x (e.symm i), fun i => hx _, fun i j hij => hsep _ _ (fun h => hij (e.symm.injective h))⟩

theorem packingNumber_bound {L : ℝ} (hL : 0 ≤ L) :
    (packingNumber L : ℝ) ≤ (4*L+2)^3 :=
  (Nat.cast_le.mpr (packingNumber_realized L).card_bound).trans (card_cubeCells_le hL)

theorem dilate_packing {ι : Type u_1} [Fintype ι] {L η : ℝ} (hη : 0 ≤ η)
    (x : ι → Space) (hx : ∀ i, x i ∈ cube L)
    (hsep : ∀ i j, i ≠ j → 1 ≤ ‖x i-x j‖) :
    (∀ i, (1+η) • x i ∈ cube ((1+η)*L)) ∧
      ∀ i j, i ≠ j → 1+η ≤ ‖(1+η) • x i-(1+η) • x j‖ := by
  have he : 0 ≤ 1+η := by linarith
  constructor
  · intro i k
    have hi := hx i k
    change (1+η)*x i k ∈ Icc (-((1+η)*L)/2) (((1+η)*L)/2)
    have hlo := mul_le_mul_of_nonneg_left hi.1 he
    have hup := mul_le_mul_of_nonneg_left hi.2 he
    constructor <;> nlinarith only [hlo,hup]
  · intro i j hij
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg he]
    nlinarith only [mul_le_mul_of_nonneg_left (hsep i j hij) he]

theorem packingNumber_tiling {ℓ L : ℝ} (hℓ : 0 ≤ ℓ) (hL : 0 ≤ L) :
    tileCount ℓ L*packingNumber ℓ ≤ packingNumber L := by
  let κ := (Fin 3 → Fin ⌊L/(ℓ+2)⌋₊)
  obtain ⟨x,hx,hsep⟩ := packingNumber_realized ℓ
  let y : κ × Fin (packingNumber ℓ) → Space := fun i => x i.2+tileCenter ℓ L i.1
  have hy : ∀ i, y i ∈ cube L := by
    intro i
    have hk : (⌊L/(ℓ+2)⌋₊ : ℝ)*(ℓ+2) ≤ L :=
      (le_div_iff₀ (by linarith : 0 < ℓ+2)).1 (Nat.floor_le (div_nonneg hL (by linarith)))
    exact tileBox_subset hℓ hk i.1 ⟨_,hx _,rfl⟩
  have hs : ∀ i j, i ≠ j → 1 ≤ ‖y i-y j‖ := by
    intro i j hij
    by_cases he : i.1 = j.1
    · have hine : i.2 ≠ j.2 := fun h => hij (Prod.ext he h)
      simpa only [y, he, add_sub_add_right_eq_sub] using hsep i.2 j.2 hine
    · exact (by norm_num : (1 : ℝ) ≤ 2).trans (tileBox_separation hℓ he
        (show y i ∈ tileBox ℓ L i.1 from ⟨_,hx _,rfl⟩)
        (show y j ∈ tileBox ℓ L j.1 from ⟨_,hx _,rfl⟩))
  have hh := card_le_packingNumber y hy hs
  simpa only [Fintype.card_prod, Fintype.card_pi, Fintype.card_fin,
    Finset.prod_const, Finset.card_univ, tileCount, κ] using hh

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.FreeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped BigOperators
open Set
namespace ContinuumTemperature
open Classical

theorem freeConfig_injective {ι : Type u_1} {t : ℝ} {x : ι → Space}
    (hx : FreeConfig t x) : Function.Injective x := by
  intro i j hij
  by_contra hne
  have hh := (hx i j hne (by rw [hij, sub_self, norm_zero]; norm_num)).1
  rw [hij,sub_self,norm_zero] at hh
  exact (not_le_of_gt (Real.exp_pos _)) hh

theorem mem_freeCluster {ι : Type u_1} [Fintype ι] {x : ι → Space} {i j : ι} :
    j ∈ freeCluster x i ↔ ‖x i-x j‖ < 1 := by simp [freeCluster]

theorem freeCluster_card_le_four {ι : Type u_1} [Fintype ι] {t : ℝ} {x : ι → Space}
    (ht : 2*(1+shellDelta)*Real.exp (-t) < 1) (hx : FreeConfig t x) (i : ι) :
    (freeCluster x i).card ≤ 4 := by
  have hc : (shellGraph x (Real.exp (-t))).IsClique (freeCluster x i : Set ι) := by
    intro j hj k hk hjk
    have hi : ‖x j-x i‖ < 1 := by simpa only [norm_sub_rev] using mem_freeCluster.mp hj
    have hh := freeConfig_close_trans ht hx hi (mem_freeCluster.mp hk)
    exact ⟨hjk,hx j k hjk hh⟩
  have hcf := shellGraph_cliqueFree x (Real.exp_pos (-t))
  by_contra hn
  obtain ⟨s,hs,hcard⟩ := Finset.exists_subset_card_eq (by omega : 5 ≤ (freeCluster x i).card)
  exact hcf s ⟨hc.subset (by exact_mod_cast hs), hcard⟩

theorem freeCluster_close_root {ι : Type u_1} [Fintype ι] {t : ℝ} {x : ι → Space}
    (hx : FreeConfig t x) {i j : ι} (hj : j ∈ freeCluster x i) :
    ‖x i-x j‖ ≤ (1+shellDelta)*Real.exp (-t) := by
  by_cases he : i=j
  · rw [he,sub_self,norm_zero]
    unfold shellDelta
    positivity
  exact (hx i j he (mem_freeCluster.mp hj)).2

theorem free_component_card_le_packing {ι : Type u_1} [Fintype ι] {t L : ℝ} {x : ι → Space}
    (ht : 2*(1+shellDelta)*Real.exp (-t) < 1) (hx : FreeConfig t x)
    (hL : ∀ i, x i ∈ cube L) :
    Fintype.card (Quotient (freeSetoid ht hx)) ≤ packingNumber L := by
  let f : Quotient (freeSetoid ht hx) → Space := fun c => x c.out
  apply card_le_packingNumber f (fun c => hL c.out)
  intro a b hab
  by_contra hlt
  have hh : (freeSetoid ht hx).r a.out b.out := lt_of_not_ge hlt
  have he := Quotient.sound hh
  exact hab (by simpa only [Quotient.out_eq] using he)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.FreeRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open Set
namespace ContinuumTemperature
open Classical

theorem freeConfig_roots {ι : Type} [Fintype ι] {t L : ℝ} {x : ι → Space}
    (ht : 2*(1+shellDelta)*Real.exp (-t) < 1) (hx : FreeConfig t x)
    (hL : ∀ i, x i ∈ cube L) :
    ∃ s : Finset ι, s.card ≤ packingNumber L ∧ Fintype.card ι ≤ 4*s.card ∧
      ∀ j, ∃ i ∈ s, ‖x j-x i‖ ≤ (1+shellDelta)*Real.exp (-t) := by
  let Q := Quotient (freeSetoid ht hx)
  let s : Finset ι := Finset.univ.image (fun c : Q => c.out)
  have ho : Function.Injective (fun c : Q => c.out) := by
    intro a b hab
    have he := congrArg (Quotient.mk (freeSetoid ht hx)) hab
    simpa only [Quotient.out_eq] using he
  have hs : s.card = Fintype.card Q := by
    exact (Finset.card_image_of_injective _ ho).trans (Finset.card_univ)
  have hc (j : ι) : ∃ i ∈ s, j ∈ freeCluster x i := by
    refine ⟨(Quotient.mk (freeSetoid ht hx) j).out, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨Quotient.mk (freeSetoid ht hx) j, Finset.mem_univ _, rfl⟩
    · apply mem_freeCluster.mpr
      exact Quotient.exact (Quotient.out_eq (Quotient.mk (freeSetoid ht hx) j))
  refine ⟨s, ?_, ?_, ?_⟩
  · rw [hs]
    exact free_component_card_le_packing ht hx hL
  · have hu : Finset.univ ⊆ s.biUnion (freeCluster x) := by
      intro j _
      obtain ⟨i,hi,hj⟩ := hc j
      exact Finset.mem_biUnion.mpr ⟨i,hi,hj⟩
    calc
      Fintype.card ι = (Finset.univ : Finset ι).card := Finset.card_univ.symm
      _ ≤ (s.biUnion (freeCluster x)).card := Finset.card_le_card hu
      _ ≤ ∑ i ∈ s, (freeCluster x i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ s, 4 := Finset.sum_le_sum (fun i _ => freeCluster_card_le_four ht hx i)
      _ = 4*s.card := by simp only [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  · intro j
    obtain ⟨i,hi,hj⟩ := hc j
    exact ⟨i,hi,by simpa only [norm_sub_rev] using freeCluster_close_root hx hj⟩

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.RootVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped BigOperators ENNReal
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

lemma volume_rootNeighborhood {ι : Type} [Fintype ι] (a : ι → Space) (r : ℝ) :
    volume (rootNeighborhood a r) ≤ (Fintype.card ι : ℝ≥0∞)*volume (Metric.closedBall (0 : Space) r) := by
  calc
    _ ≤ ∑' i, volume (Metric.closedBall (a i) r) := measure_iUnion_le _
    _ = _ := by simp only [Measure.addHaar_closedBall_center, tsum_fintype, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]

lemma measurableSet_forall_labels {X : Type u_1} [MeasurableSpace X] {ι : Type u_2} [Countable ι]
    {P : X → ι → Prop} (hP : ∀ i, MeasurableSet {x | P x i}) : MeasurableSet {x | ∀ i, P x i} := by
  have he : {x | ∀ i, P x i} = ⋂ i, {x | P x i} := by ext x; simp only [mem_ofPred_eq, mem_iInter]
  rw [he]
  exact MeasurableSet.iInter hP

lemma measurableSet_exists_labels {X : Type u_1} [MeasurableSpace X] {ι : Type u_2} [Countable ι]
    {P : X → ι → Prop} (hP : ∀ i, MeasurableSet {x | P x i}) : MeasurableSet {x | ∃ i, P x i} := by
  have he : {x | ∃ i, P x i} = ⋃ i, {x | P x i} := by ext x; simp only [mem_ofPred_eq, mem_iUnion]
  rw [he]
  exact MeasurableSet.iUnion hP

lemma rootCover_volume {ι : Type} [Fintype ι] (s : Finset ι) (r L : ℝ) :
    volume ({x : ι → Space | ∀ i, x i ∈ cube L} ∩ rootCover s r) ≤
      (volume (cube L))^s.card *
        ((s.card : ℝ≥0∞)*volume (Metric.closedBall (0 : Space) r))^(Fintype.card ι-s.card) := by
  let I := {i : ι // i ∈ s}
  let J := {i : ι // i ∉ s}
  let p := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => Space) (fun i => i ∈ s)
  let SA : Set (I → Space) := {a | ∀ i, a i ∈ cube L}
  let T : Set ((I → Space) × (J → Space)) :=
    {z | z.1 ∈ SA ∧ ∀ j, z.2 j ∈ cube L ∩ rootNeighborhood z.1 r}
  have hSA : MeasurableSet SA := measurableSet_forall_labels
    (fun i => (measurableSet_cube L).preimage (measurable_pi_apply i))
  have hT : MeasurableSet T := by
    apply (hSA.preimage measurable_fst).inter
    apply measurableSet_forall_labels
    intro j
    apply ((measurableSet_cube L).preimage ((measurable_pi_apply j).comp measurable_snd)).inter
    change MeasurableSet {z : (I → Space) × (J → Space) | z.2 j ∈ rootNeighborhood z.1 r}
    have he : {z : (I → Space) × (J → Space) | z.2 j ∈ rootNeighborhood z.1 r} =
        {z | ∃ i : I, ‖z.2 j-z.1 i‖ ≤ r} := by
      ext z
      simp only [mem_ofPred_eq, rootNeighborhood, mem_iUnion, Metric.mem_closedBall, dist_eq_norm]
    rw [he]
    apply measurableSet_exists_labels
    intro i
    exact measurableSet_le
      (((measurable_pi_apply j).comp measurable_snd).sub
        ((measurable_pi_apply i).comp measurable_fst)).norm measurable_const

  have hp := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => (volume : Measure Space))
    (fun i => i ∈ s)
  have hfi : Subtype.fintype (fun i : ι => i ∈ s) = Finset.Subtype.fintype s := Subsingleton.elim _ _
  rw [hfi] at hp
  have hpre : p ⁻¹' T = {x : ι → Space | ∀ i, x i ∈ cube L} ∩ rootCover s r := by
    ext x
    change ((∀ i : I, x i ∈ cube L) ∧
      ∀ j : J, x j ∈ cube L ∩ ⋃ i : I, Metric.closedBall (x i) r) ↔
      (∀ i, x i ∈ cube L) ∧ ∀ j : J, ∃ i : I, ‖x j-x i‖ ≤ r
    simp only [mem_inter_iff, mem_iUnion, Metric.mem_closedBall, dist_eq_norm]
    constructor
    · rintro ⟨ha,hb⟩
      refine ⟨?_,fun j => (hb j).2⟩
      intro i
      by_cases hi : i ∈ s
      · exact ha ⟨i,hi⟩
      · exact (hb ⟨i,hi⟩).1
    · rintro ⟨ha,hb⟩
      exact ⟨fun i => ha i, fun j => ⟨ha j,hb j⟩⟩
  have he := hp.measure_preimage hT.nullMeasurableSet
  rw [hpre] at he
  simp only [← volume_pi] at he
  rw [he, Measure.prod_apply hT]
  let C : ℝ≥0∞ := ((s.card : ℝ≥0∞)*volume (Metric.closedBall (0 : Space) r))^(Fintype.card ι-s.card)
  calc
    _ ≤ ∫⁻ a, SA.indicator (fun _ => C) a := by
      apply lintegral_mono
      intro a
      dsimp only
      by_cases ha : a ∈ SA
      · rw [Set.indicator_of_mem ha]
        have hf : Prod.mk a ⁻¹' T = {b : J → Space | ∀ j, b j ∈ cube L ∩ rootNeighborhood a r} := by
          ext b
          simp only [T, mem_preimage, mem_ofPred_eq, ha, true_and]
        rw [hf, volume_generalConfigurations]
        have hJ : Fintype.card J = Fintype.card ι-s.card := by
          rw [Fintype.card_subtype_compl, Fintype.card_coe]
        rw [hJ]
        apply pow_le_pow_left'
        exact (measure_mono inter_subset_right).trans (by
          simpa only [I, Fintype.card_coe] using volume_rootNeighborhood a r)
      · rw [Set.indicator_of_notMem ha]
        have hf : Prod.mk a ⁻¹' T = ∅ := by ext b; simp [T, ha]
        simp only [hf, measure_empty, le_refl]
    _ = _ := by
      rw [lintegral_indicator_const hSA, volume_generalConfigurations]
      simp only [I, Fintype.card_coe, C, mul_comm]

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.FreeFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators ENNReal
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

lemma measurableSet_freeConfig {ι : Type} [Fintype ι] (t : ℝ) :
    MeasurableSet {x : ι → Space | FreeConfig t x} := by
  apply measurableSet_forall_labels
  intro i
  apply measurableSet_forall_labels
  intro j
  by_cases hij : i = j
  · simp only [hij, ne_eq, not_true_eq_false, false_implies, ofPred_true, MeasurableSet.univ]
  have hm : Measurable (fun x : ι → Space => ‖x i-x j‖) :=
    ((measurable_pi_apply i).sub (measurable_pi_apply j)).norm
  have he : {x : ι → Space | i ≠ j → ‖x i-x j‖ < 1 →
      Real.exp (-t) ≤ ‖x i-x j‖ ∧ ‖x i-x j‖ ≤ (1+shellDelta)*Real.exp (-t)} =
      {x | 1 ≤ ‖x i-x j‖} ∪
      ({x | Real.exp (-t) ≤ ‖x i-x j‖} ∩ {x | ‖x i-x j‖ ≤ (1+shellDelta)*Real.exp (-t)}) := by
    ext x
    simp only [mem_ofPred_eq, mem_union, mem_inter_iff, ne_eq, hij, not_false_eq_true, imp_iff_not_or, not_lt, not_true_eq_false, false_or]
  rw [he]
  exact (measurableSet_le measurable_const hm).union
    ((measurableSet_le measurable_const hm).inter (measurableSet_le hm measurable_const))

lemma freeFamily_relabel (t d : ℝ) : RelabelInvariant (freeFamily t d) := by
  intro ι κ _ _ e x
  have he : FreeConfig t (x ∘ e) ↔ FreeConfig t x := by
    constructor
    · intro hh i j hij hdist
      have hn : e.symm i ≠ e.symm j := fun he => hij (e.symm.injective he)
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
        hh (e.symm i) (e.symm j) hn (by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hdist)
    · intro hh i j hij hdist
      exact hh (e i) (e j) (fun he => hij (e.injective he)) hdist
  simp only [freeFamily, he, Fintype.card_congr e]

lemma freeFamily_measurable (t d : ℝ) (ι : Type) [Fintype ι] : Measurable (freeFamily t d ι) :=
  Measurable.ite (measurableSet_freeConfig t) measurable_const measurable_const

lemma freeFamily_nonneg (t d : ℝ) (ι : Type) [Fintype ι] (x : ι → Space) :
    0 ≤ freeFamily t d ι x := by
  unfold freeFamily
  split_ifs <;> positivity

lemma freeFamily_le_exp (t d : ℝ) (ι : Type) [Fintype ι] (x : ι → Space) :
    freeFamily t d ι x ≤ Real.exp (d*Fintype.card ι) := by
  unfold freeFamily
  split_ifs
  · exact le_rfl
  · exact (Real.exp_pos _).le

lemma freeFamily_summable (t d L : ℝ) : Summable (familyTerm (freeFamily t d) (cube L)) :=
  summable_familyTerm_of_bound _ (isCompact_cube L).measure_lt_top.ne (freeFamily_measurable t d)
    (freeFamily_nonneg t d) (freeFamily_le_exp t d)

lemma rootCover_volume_real {ι : Type} [Fintype ι] (s : Finset ι) (r L : ℝ) :
    volume.real ({x : ι → Space | ∀ i, x i ∈ cube L} ∩ rootCover s r) ≤
      (volume.real (cube L))^s.card *
        ((s.card : ℝ)*volume.real (Metric.closedBall (0 : Space) r))^(Fintype.card ι-s.card) := by
  have hh := ENNReal.toReal_mono (show
    (volume (cube L))^s.card *
      ((s.card : ℝ≥0∞)*volume (Metric.closedBall (0 : Space) r))^(Fintype.card ι-s.card) ≠ ⊤ by
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (isCompact_cube L).measure_lt_top.ne)
      (ENNReal.pow_ne_top (ENNReal.mul_ne_top (by simp) (measure_closedBall_lt_top.ne)))) (rootCover_volume s r L)
  simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast] using hh

lemma freeConfig_volume_le {ι : Type} [Fintype ι] {t : ℝ}
    (ht : 2*(1+shellDelta)*Real.exp (-t) < 1) (L : ℝ) :
    volume.real ({x : ι → Space | ∀ i, x i ∈ cube L} ∩ {x | FreeConfig t x}) ≤
      ∑ k ∈ Finset.range (Fintype.card ι+1),
        if k ≤ packingNumber L ∧ Fintype.card ι ≤ 4*k then
          ((Fintype.card ι).choose k : ℝ)*(volume.real (cube L))^k *
            ((k : ℝ)*volume.real (Metric.closedBall (0 : Space) ((1+shellDelta)*Real.exp (-t))))^(Fintype.card ι-k)
        else 0 := by
  let T : Finset (Finset ι) := Finset.univ.filter (fun s => s.card ≤ packingNumber L ∧ Fintype.card ι ≤ 4*s.card)
  let A : Finset ι → Set (ι → Space) := fun s =>
    {x | ∀ i, x i ∈ cube L} ∩ rootCover s ((1+shellDelta)*Real.exp (-t))
  have hsub : ({x : ι → Space | ∀ i, x i ∈ cube L} ∩ {x | FreeConfig t x}) ⊆ ⋃ s ∈ T, A s := by
    intro x hx
    obtain ⟨s,hs,hn,hc⟩ := freeConfig_roots ht hx.2 hx.1
    apply mem_iUnion₂.mpr
    refine ⟨s,by simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hs,hn⟩,hx.1,?_⟩
    intro j
    obtain ⟨i,hi,hij⟩ := hc j
    exact ⟨⟨i,hi⟩,hij⟩
  have hfin : volume (⋃ s ∈ T, A s) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (show volume {x : ι → Space | ∀ i, x i ∈ cube L} ≠ ⊤ by
      rw [volume_generalConfigurations]; exact ENNReal.pow_ne_top (isCompact_cube L).measure_lt_top.ne)
    apply measure_mono
    intro x hx
    obtain ⟨s,_,hs⟩ := mem_iUnion₂.mp hx
    exact hs.1
  calc
    _ ≤ volume.real (⋃ s ∈ T, A s) := measureReal_mono hsub hfin
    _ ≤ ∑ s ∈ T, volume.real (A s) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ s ∈ T, (volume.real (cube L))^s.card *
        ((s.card : ℝ)*volume.real (Metric.closedBall (0 : Space) ((1+shellDelta)*Real.exp (-t))))^(Fintype.card ι-s.card) := by
      exact Finset.sum_le_sum (fun s _ => rootCover_volume_real s _ L)
    _ = _ := by
      rw [Finset.sum_filter]
      have hh := Finset.sum_powerset_apply_card
        (fun k => if k ≤ packingNumber L ∧ Fintype.card ι ≤ 4*k then
          (volume.real (cube L))^k *
            ((k : ℝ)*volume.real (Metric.closedBall (0 : Space) ((1+shellDelta)*Real.exp (-t))))^(Fintype.card ι-k) else 0)
        (x := (Finset.univ : Finset ι))
      simp only [Finset.powerset_univ, Finset.card_univ, nsmul_eq_mul] at hh
      rw [hh]
      apply Finset.sum_congr rfl
      intro k hk
      split_ifs <;> simp [mul_assoc]

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.FreeGrand
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

lemma freeFamily_integral (t d L : ℝ) (ι : Type) [Fintype ι] :
    familyIntegral (freeFamily t d) (cube L) ι =
      volume.real ({x : ι → Space | ∀ i, x i ∈ cube L} ∩ {x | FreeConfig t x})*
        (Real.exp d)^Fintype.card ι := by
  have he : freeFamily t d ι = {x : ι → Space | FreeConfig t x}.indicator
      (fun _ => Real.exp (d*Fintype.card ι)) := by
    funext x
    simp only [freeFamily, indicator_apply, mem_ofPred_eq]
  rw [familyIntegral, he, setIntegral_indicator (measurableSet_freeConfig t), setIntegral_const,
    smul_eq_mul, mul_comm d, Real.exp_nat_mul]

lemma power_trunc_bound {w : ℝ} (hw : 0 ≤ w) {j k : ℕ} (hjk : j ≤ 3*k) :
    w^j ≤ (max 1 w)^ (3*k) := by
  exact (pow_le_pow_left₀ hw (le_max_right 1 w) j).trans
    (pow_le_pow_right₀ (le_max_left 1 w) hjk)

theorem free_grand_upper {t : ℝ} (ht : 2*(1+shellDelta)*Real.exp (-t) < 1) (d L : ℝ) :
    grandIntegral (freeFamily t d) (cube L) ≤
      (∑ k ∈ Finset.range (packingNumber L+1),
        ((volume.real (cube L))*Real.exp d*
          (max 1 (volume.real (Metric.closedBall (0 : Space) ((1+shellDelta)*Real.exp (-t)))*Real.exp d))^3)^k /
            (k.factorial : ℝ))*Real.exp (packingNumber L) := by
  let V := volume.real (cube L)
  let z := Real.exp d
  let w := volume.real (Metric.closedBall (0 : Space) ((1+shellDelta)*Real.exp (-t)))
  let M := packingNumber L
  let D := max 1 (w*z)
  let a : ℕ → ℝ := fun k => if k ≤ M then (V*z*D^3)^k/(k.factorial : ℝ) else 0
  let b : ℕ → ℝ := fun j => (M : ℝ)^j/(j.factorial : ℝ)
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hz : 0 ≤ z := (Real.exp_pos _).le
  have hw : 0 ≤ w := ENNReal.toReal_nonneg
  have hD : 1 ≤ D := le_max_left _ _
  have ha : Summable a := summable_of_ne_finset_zero (s := Finset.range (M+1)) (by
    intro k hk
    have hh : ¬k ≤ M := by simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hk
    simp only [a, ite_eq_right hh])
  have hb : HasSum b (Real.exp (M : ℝ)) := by
    simpa only [b, Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (M : ℝ)
  have hea : (∑' k, a k) = ∑ k ∈ Finset.range (M+1), (V*z*D^3)^k/(k.factorial : ℝ) := by
    rw [tsum_eq_sum (s := Finset.range (M+1)) (by
      intro k hk
      have hh : ¬k ≤ M := by simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hk
      simp only [a, ite_eq_right hh])]
    apply Finset.sum_congr rfl
    intro k hk
    exact ite_eq_left (by have := Finset.mem_range.mp hk; omega)
  rw [show (∑ k ∈ Finset.range (packingNumber L+1), _) = ∑' k, a k by exact hea.symm,
    ← hb.tsum_eq]
  apply tsum_le_convolution (freeFamily_summable t d L) ha hb.summable
  intro n
  have hv := freeConfig_volume_le (ι := Fin n) ht L
  rw [Fintype.card_fin] at hv
  have hh := mul_le_mul_of_nonneg_right hv (pow_nonneg hz n)
  have hh' := div_le_div_of_nonneg_right hh (Nat.cast_nonneg n.factorial : (0 : ℝ) ≤ n.factorial)
  rw [familyTerm, freeFamily_integral, Fintype.card_fin]
  apply hh'.trans
  rw [Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_le_sum
  intro k hk
  have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
  by_cases hc : k ≤ M ∧ n ≤ 4*k
  · simp only [show packingNumber L = M from rfl, ite_eq_left hc, a, ite_eq_left hc.1, b]
    rw [Nat.cast_choose ℝ hkn]
    have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have he : (((n.factorial : ℝ)/((k.factorial : ℝ)*((n-k).factorial : ℝ)))*V^k*
        ((k : ℝ)*w)^(n-k)*z^n)/(n.factorial : ℝ) =
        (V*z)^k/(k.factorial : ℝ)*((k : ℝ)^(n-k)*(w*z)^(n-k)/((n-k).factorial : ℝ)) := by
      have hzpow : z^n = z^k*z^(n-k) := by rw [← pow_add, Nat.add_sub_of_le hkn]
      rw [hzpow, mul_pow]
      field_simp
      ring
    change (((n.factorial : ℝ)/((k.factorial : ℝ)*((n-k).factorial : ℝ)))*V^k*
        ((k : ℝ)*w)^(n-k)*z^n)/(n.factorial : ℝ) ≤ _
    rw [he]
    have hkM : (k : ℝ) ≤ M := by exact_mod_cast hc.1
    have hp := power_trunc_bound (mul_nonneg hw hz) (show n-k ≤ 3*k by omega)
    have hpow : (k : ℝ)^(n-k)*(w*z)^(n-k) ≤ (M : ℝ)^(n-k)*D^(3*k) :=
      mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg k) hkM _) hp
        (pow_nonneg (mul_nonneg hw hz) _) (pow_nonneg (Nat.cast_nonneg M) _)
    have hm := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hpow (Nat.cast_nonneg (n-k).factorial))
      (div_nonneg (pow_nonneg (mul_nonneg hV hz) k) (Nat.cast_nonneg k.factorial))
    apply hm.trans_eq
    rw [mul_pow, pow_mul]
    ring
  · simp only [show packingNumber L = M from rfl, ite_eq_right hc, zero_mul, zero_div]
    apply mul_nonneg
    · dsimp only [a]
      split_ifs <;> positivity
    · dsimp only [b]
      positivity

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.BadEndpoints
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

lemma badEndpoints_complement_free {ι : Type} [Fintype ι] [DecidableEq ι] (t : ℝ) (x : ι → Space) :
    FreeConfig t (fun i : {i : ι // i ∉ badEndpoints t x} => x i) := by
  intro i j hij hd
  by_contra hh
  apply i.property
  simp only [badEndpoints, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨j,fun he => hij (Subtype.ext he),hd,hh⟩

lemma badEndpoints_energy {ι : Type} [Fintype ι] (t : ℝ) (x : ι → Space) :
    t^2/2*(badEndpoints t x).card ≤ gibbsEnergy (fun x y => coreProfile t ‖x-y‖) x := by
  have hn (i j : ι) : 0 ≤ if i=j then (0 : ℝ) else coreProfile t ‖x i-x j‖ := by
    split_ifs
    · rfl
    · exact coreProfile_nonneg _ _
  have hr (i : ι) : (if i ∈ badEndpoints t x then t^2 else 0) ≤
      ∑ j, if i=j then (0 : ℝ) else coreProfile t ‖x i-x j‖ := by
    split_ifs with hi
    · obtain ⟨j,hij,hd,hs⟩ := (Finset.mem_filter.mp hi).2
      calc
        _ ≤ coreProfile t ‖x i-x j‖ := coreProfile_ge_of_not_shell t _ hd hs
        _ = (if i=j then (0 : ℝ) else coreProfile t ‖x i-x j‖) := by rw [ite_eq_right hij]
        _ ≤ _ := Finset.single_le_sum (fun j _ => hn i j) (Finset.mem_univ j)
    · exact Finset.sum_nonneg (fun j _ => hn i j)
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hr i)
  have he : (∑ i : ι, if i ∈ badEndpoints t x then t^2 else 0) =
      ((badEndpoints t x).card : ℝ)*t^2 := by
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  rw [he] at hh
  unfold gibbsEnergy
  linarith only [hh]

lemma idealFamily_nonneg (d : ℝ) (ι : Type) [Fintype ι] (x : ι → Space) :
    0 ≤ idealFamily d ι x := (Real.exp_pos _).le

lemma idealFamily_relabel (d : ℝ) : RelabelInvariant (idealFamily d) := by
  intro ι κ _ _ e x
  simp only [idealFamily, Fintype.card_congr e]

theorem core_gibbs_bad_endpoints {ι : Type} [Fintype ι] [DecidableEq ι] (t d : ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (x : ι → Space) :
    gibbsFamily (fun x y => coreProfile t ‖x-y‖) β d ι x ≤
      ∑ s : Finset ι, idealFamily (d-β*t^2/2) {i : ι // i ∈ s} (fun i => x i)*
        freeFamily t d {i : ι // i ∉ s} (fun i => x i) := by
  let s := badEndpoints t x
  have hterm : gibbsFamily (fun x y => coreProfile t ‖x-y‖) β d ι x ≤
      idealFamily (d-β*t^2/2) {i : ι // i ∈ s} (fun i => x i)*
        freeFamily t d {i : ι // i ∉ s} (fun i => x i) := by
    have hsfree : FreeConfig t (fun i : {i : ι // i ∉ s} => x i) := badEndpoints_complement_free t x
    simp only [idealFamily, freeFamily, ite_eq_left hsfree, Fintype.card_coe]
    have he : (Fintype.card ι : ℝ) = (s.card : ℝ)+(Fintype.card {i : ι // i ∉ s} : ℝ) := by
      have hh := Fintype.card_subtype_compl (fun i : ι => i ∈ s)
      rw [Fintype.card_coe] at hh
      have hh' : Fintype.card ι = s.card+Fintype.card {i : ι // i ∉ s} := by
        rw [hh]; exact (Nat.add_sub_of_le (Finset.card_le_univ s)).symm
      exact_mod_cast hh'
    unfold gibbsFamily
    split_ifs with hinj
    · rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left (badEndpoints_energy t x) hβ
      rw [he]
      dsimp only [s] at hh ⊢
      nlinarith only [hh]
    · positivity
  exact hterm.trans (Finset.single_le_sum
    (fun r _ => mul_nonneg
      (idealFamily_nonneg (d-β*t^2/2) {i : ι // i ∈ r} (fun i => x i))
      (freeFamily_nonneg t d {i : ι // i ∉ r} (fun i => x i))) (Finset.mem_univ s))

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
-- module Solutions.OAIQW_ContinuumTemperature.LabelConvolution
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

lemma binaryRegion_same {ι : Type} [Fintype ι] [DecidableEq ι] (A : Set Space) (s : Finset ι) :
    binaryRegion A A s = {x : ι → Space | ∀ i, x i ∈ A} := by
  ext x
  simp only [binaryRegion, mem_ofPred_eq, ite_self]

theorem grandIntegral_label_convolution (F G H : ConfigFamily)
    (hG : RelabelInvariant G) (hH : RelabelInvariant H) {A : Set Space}
    (hA : MeasurableSet A) (hF : GrandFinite F A) (hGF : GrandFinite G A) (hHF : GrandFinite H A)
    (hbound : ∀ (n : ℕ) (x : Fin n → Space), (∀ i, x i ∈ A) →
      F (Fin n) x ≤ ∑ s : Finset (Fin n),
        G {i : Fin n // i ∈ s} (fun i => x i)*H {i : Fin n // i ∉ s} (fun i => x i)) :
    grandIntegral F A ≤ grandIntegral G A*grandIntegral H A := by
  apply tsum_le_convolution hF.summable hGF.summable hHF.summable
  intro n
  have hi (s : Finset (Fin n)) : IntegrableOn
      (fun x : Fin n → Space => G {i : Fin n // i ∈ s} (fun i => x i)*
        H {i : Fin n // i ∉ s} (fun i => x i)) {x | ∀ i, x i ∈ A} := by
    have hh := integrableOn_binary_product volume A A s
      (by simpa only [← volume_pi] using hGF.integrable {i : Fin n // i ∈ s})
      (by simpa only [← volume_pi] using hHF.integrable {i : Fin n // i ∉ s})
    simpa only [← volume_pi, binaryRegion, ite_self] using hh
  have hle := setIntegral_mono_on (hF.integrable (Fin n))
    (integrable_finsetSum _ (fun s _ => hi s)) (measurableSet_generalConfigurations hA (Fin n)) (hbound n)
  rw [integral_finsetSum _ (fun s _ => hi s)] at hle
  have he (s : Finset (Fin n)) :
      (∫ x in {x : Fin n → Space | ∀ i, x i ∈ A},
        G {i : Fin n // i ∈ s} (fun i => x i)*H {i : Fin n // i ∉ s} (fun i => x i)) =
      familyIntegral G A (Fin s.card)*familyIntegral H A (Fin (n-s.card)) := by
    rw [← binaryRegion_same A s,
      show volume = Measure.pi (fun _ : Fin n => (volume : Measure Space)) by exact volume_pi,
      setIntegral_binary_product volume A A s (G {i : Fin n // i ∈ s}) (H {i : Fin n // i ∉ s})]
    simp only [← volume_pi]
    have hg := familyIntegral_eq_Fin G hG A {i : Fin n // i ∈ s}
    have hh := familyIntegral_eq_Fin H hH A {i : Fin n // i ∉ s}
    rw [Fintype.card_coe] at hg
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe] at hh
    exact congrArg₂ (·*·) hg hh
  simp_rw [he] at hle
  have hs := Finset.sum_powerset_apply_card
    (fun k => familyIntegral G A (Fin k)*familyIntegral H A (Fin (n-k)))
    (x := (Finset.univ : Finset (Fin n)))
  simp only [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc] at hs
  rw [hs] at hle
  have hh := div_le_div_of_nonneg_right hle (Nat.cast_nonneg n.factorial : (0 : ℝ) ≤ n.factorial)
  rw [factorial_binomial_sum (fun k => familyIntegral G A (Fin k))
    (fun k => familyIntegral H A (Fin k)) n] at hh
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

theorem grandIntegral_gibbs_pos (V : Space → Space → ℝ) (β h : ℝ) (D : Set Space)
    (hs : Summable (familyTerm (gibbsFamily V β h) D)) :
    0 < grandIntegral (gibbsFamily V β h) D := by
  have hh := hs.le_tsum 0 (fun n _ => familyTerm_nonneg _ D (gibbsFamily_nonneg V β h) n)
  rw [gibbsFamily_term_zero] at hh
  exact lt_of_lt_of_le zero_lt_one hh

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.FreeUpper
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

theorem idealFamily_finite (d : ℝ) {D : Set Space} (hD : volume D ≠ ⊤) :
    GrandFinite (idealFamily d) D :=
  GrandFinite.of_bound _ hD (fun _ _ => measurable_const)
    (idealFamily_nonneg d) (fun _ _ _ => le_refl _)

theorem grandIntegral_ideal (d : ℝ) (D : Set Space) :
    grandIntegral (idealFamily d) D = Real.exp (volume.real D*Real.exp d) := by
  have he (n : ℕ) : familyTerm (idealFamily d) D n =
      (volume.real D*Real.exp d)^n/(n.factorial : ℝ) := by
    simp only [familyTerm, familyIntegral, idealFamily, Fintype.card_fin,
      setIntegral_const, smul_eq_mul, Measure.real, volume_generalConfigurations,
      ENNReal.toReal_pow, mul_pow, mul_comm d, Real.exp_nat_mul]
  simp_rw [grandIntegral, he]
  simpa only [Real.exp_eq_exp_ℝ] using
    (NormedSpace.expSeries_div_hasSum_exp (volume.real D*Real.exp d)).tsum_eq

theorem core_gibbs_finite (t d : ℝ) {β : ℝ} (hβ : 0 ≤ β)
    {D : Set Space} (hD : volume D ≠ ⊤) :
    GrandFinite (gibbsFamily (fun x y => coreProfile t ‖x-y‖) β d) D := by
  apply GrandFinite.of_bound _ hD
    (fun ι _ => measurable_gibbsFamily (V := fun x y : Space => coreProfile t ‖x-y‖) ((measurable_coreProfile t).comp
      ((measurable_fst.sub measurable_snd).norm)) β d ι)
    (gibbsFamily_nonneg _ β d)
  intro ι _ x
  unfold gibbsFamily
  split_ifs
  · apply Real.exp_le_exp.mpr
    have he : 0 ≤ gibbsEnergy (fun x y => coreProfile t ‖x-y‖) x := by
      unfold gibbsEnergy
      apply div_nonneg _ (by norm_num)
      apply Finset.sum_nonneg
      intro i _
      apply Finset.sum_nonneg
      intro j _
      split_ifs
      · rfl
      · exact coreProfile_nonneg _ _
    exact sub_le_self _ (mul_nonneg hβ he)
  · exact (Real.exp_pos _).le

theorem core_grand_bad_bound (t d L : ℝ) {β : ℝ} (hβ : 0 ≤ β) :
    grandIntegral (gibbsFamily (fun x y => coreProfile t ‖x-y‖) β d) (cube L) ≤
      Real.exp (volume.real (cube L)*Real.exp (d-β*t^2/2))*
        grandIntegral (freeFamily t d) (cube L) := by
  rw [← grandIntegral_ideal]
  exact grandIntegral_label_convolution _ _ _ (idealFamily_relabel _) (freeFamily_relabel t d)
    (measurableSet_cube L) (core_gibbs_finite t d hβ (isCompact_cube L).measure_lt_top.ne)
    (idealFamily_finite _ (isCompact_cube L).measure_lt_top.ne)
    (GrandFinite.of_bound _ (isCompact_cube L).measure_lt_top.ne
      (freeFamily_measurable t d) (freeFamily_nonneg t d) (freeFamily_le_exp t d))
    (fun _ x _ => core_gibbs_bad_endpoints t d hβ x)

lemma truncated_exp_poly_bound {V θ : ℝ} (hV : 0 ≤ V) (hθ : 0 ≤ θ) (M : ℕ) :
    (∑ k ∈ Finset.range (M+1), (V*θ)^k/(k.factorial : ℝ)) ≤
      (M+1)*Real.exp V*(max 1 θ)^M := by
  have hs : HasSum (fun k : ℕ => V^k/(k.factorial : ℝ)) (Real.exp V) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp V
  calc
    _ ≤ ∑ _k ∈ Finset.range (M+1), Real.exp V*(max 1 θ)^M := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn : k ≤ M := by have := Finset.mem_range.mp hk; omega
      have hp : V^k/(k.factorial : ℝ) ≤ Real.exp V :=
        hs.summable.le_tsum k (fun j _ => by positivity) |>.trans_eq hs.tsum_eq
      rw [mul_pow, mul_div_right_comm]
      exact mul_le_mul hp
        ((pow_le_pow_left₀ hθ (le_max_right 1 θ) k).trans
          (pow_le_pow_right₀ (le_max_left 1 θ) hkn))
        (pow_nonneg hθ k) (Real.exp_pos V).le
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
        Nat.cast_one]; ring

theorem core_grand_upper {t : ℝ} (ht : 2*(1+shellDelta)*Real.exp (-t) < 1)
    (d L : ℝ) {β : ℝ} (hβ : 0 ≤ β) :
    grandIntegral (gibbsFamily (fun x y => coreProfile t ‖x-y‖) β d) (cube L) ≤
      Real.exp (volume.real (cube L)*(1+Real.exp (d-β*t^2/2))+(packingNumber L : ℝ))*
        ((packingNumber L : ℝ)+1)*(max 1 (clusterActivity t d))^(packingNumber L) := by
  have h1 := core_grand_bad_bound t d L hβ
  have h2 := free_grand_upper ht d L
  have h3 := truncated_exp_poly_bound (V := volume.real (cube L)) ENNReal.toReal_nonneg
    (θ := clusterActivity t d) (by unfold clusterActivity; positivity) (packingNumber L)
  have he : volume.real (cube L)*Real.exp d*
      (max 1 (volume.real (Metric.closedBall (0 : Space) ((1+shellDelta)*Real.exp (-t)))*Real.exp d))^3 =
      volume.real (cube L)*clusterActivity t d := by unfold clusterActivity; ring
  rw [he] at h2
  apply h1.trans
  apply (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le).trans
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le)
    (Real.exp_pos _).le).trans_eq
  rw [show volume.real (cube L)*(1+Real.exp (d-β*t^2/2))+(packingNumber L : ℝ) =
    volume.real (cube L)*Real.exp (d-β*t^2/2)+volume.real (cube L)+(packingNumber L : ℝ) by ring,
    Real.exp_add, Real.exp_add]
  ring

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PackingLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Filter Set
namespace ContinuumTemperature

theorem packing_fractions_bddAbove :
    BddAbove ((fun L : ℝ => (packingNumber L : ℝ)/(L+2)^3) '' Ici 0) := by
  refine ⟨64, ?_⟩
  rintro _ ⟨L,hL,rfl⟩
  change 0 ≤ L at hL
  apply (div_le_iff₀ (pow_pos (by linarith : 0 < L+2) 3)).2
  have hh := pow_le_pow_left₀ (by linarith : 0 ≤ 4*L+2)
    (by linarith : 4*L+2 ≤ 4*(L+2)) 3
  have hp := packingNumber_bound hL
  nlinarith only [hp,hh]

theorem packing_fraction_le {L : ℝ} (hL : 0 ≤ L) :
    (packingNumber L : ℝ)/(L+2)^3 ≤ packingDensity :=
  le_csSup packing_fractions_bddAbove ⟨L,hL,rfl⟩

theorem packingDensity_pos : 0 < packingDensity := by
  have hp : IsPacking 0 1 := by
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro i j; simp
    · intro i j hij
      exact (hij (Subsingleton.elim _ _)).elim
  have hn : (1 : ℝ) ≤ packingNumber 0 := by exact_mod_cast hp.le_packingNumber
  have hh := packing_fraction_le (L := 0) (le_refl 0)
  norm_num at hh
  linarith

theorem packingNumber_tendsto :
    Tendsto (fun L : ℝ => (packingNumber L : ℝ)/L^3) atTop (𝓝 packingDensity) := by
  refine tendsto_order.2 ⟨?_,?_⟩
  · intro c hc
    obtain ⟨v,⟨ℓ,hℓ,rfl⟩,hv⟩ := exists_lt_of_lt_csSup
      (Set.Nonempty.image _ (nonempty_Ici : (Ici (0 : ℝ)).Nonempty)) hc
    have ht : Tendsto (fun L : ℝ => ((tileCount ℓ L : ℝ)/L^3)*(packingNumber ℓ : ℝ))
        atTop (𝓝 ((packingNumber ℓ : ℝ)/(ℓ+2)^3)) := by
      simpa only [div_eq_mul_inv, inv_pow, mul_comm] using
        (tileCount_asymptotic hℓ).mul_const (packingNumber ℓ : ℝ)
    filter_upwards [ht.eventually_const_lt hv, eventually_gt_atTop (0 : ℝ)] with L hc hL
    apply hc.trans_le
    have hi := packingNumber_tiling hℓ hL.le
    have hh := div_le_div_of_nonneg_right (Nat.cast_le.mpr hi :
        ((tileCount ℓ L*packingNumber ℓ : ℕ) : ℝ) ≤ packingNumber L) (pow_pos hL 3).le
    simpa only [Nat.cast_mul, div_mul_eq_mul_div] using hh
  · intro c hc
    have hi : Tendsto (fun L : ℝ => L⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    have ht : Tendsto (fun L : ℝ => packingDensity*(1+2/L)^3) atTop (𝓝 packingDensity) := by
      simpa only [mul_zero, add_zero, one_pow, mul_one, div_eq_mul_inv] using
        (((hi.const_mul 2).const_add 1).pow 3).const_mul packingDensity
    filter_upwards [ht.eventually_lt_const hc, eventually_gt_atTop (0 : ℝ)] with L hc hL
    apply lt_of_le_of_lt _ hc
    have hh := mul_le_mul_of_nonneg_right (packing_fraction_le hL.le)
      (show 0 ≤ ((L+2)^3/L^3) by positivity)
    have he : ((packingNumber L : ℝ)/(L+2)^3)*((L+2)^3/L^3) =
        (packingNumber L : ℝ)/L^3 := by
      have hn : L+2 ≠ 0 := by positivity
      field_simp
    rw [he] at hh
    convert hh using 1
    field_simp

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PackingUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Filter MeasureTheory Set
namespace ContinuumTemperature

lemma coreProfile_stable_zero (t : ℝ) (n : ℕ) (x : Fin n → Space) :
    ((-(0 : ℝ)*n : ℝ) : EReal) ≤ energy (coreProfile t) x := by
  apply le_trans _ (coe_pairSum_le_energy _ x)
  apply EReal.coe_le_coe_iff.mpr
  simp only [neg_zero,zero_mul]
  unfold pairSum
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact coreProfile_nonneg _ _

lemma core_log_upper {t : ℝ} (ht : 2*(1+shellDelta)*Real.exp (-t) < 1)
    (d L : ℝ) {β : ℝ} (hβ : 0 ≤ β) :
    Real.log (grandIntegral (gibbsFamily (fun x y => coreProfile t ‖x-y‖) β d) (cube L)) ≤
      volume.real (cube L)*(1+Real.exp (d-β*t^2/2))+
        (packingNumber L : ℝ)*(2+Real.log (max 1 (clusterActivity t d))) := by
  have hfin := core_gibbs_finite t d hβ (isCompact_cube L).measure_lt_top.ne
  have hz := grandIntegral_gibbs_pos _ β d (cube L) hfin.summable
  have hh := Real.log_le_log hz (core_grand_upper ht d L hβ)
  have hM : 0 < (packingNumber L : ℝ)+1 := by positivity
  have hθ : 0 < max 1 (clusterActivity t d) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [Real.log_mul (mul_pos (Real.exp_pos _) hM).ne' (pow_pos hθ _).ne',
    Real.log_mul (Real.exp_pos _).ne' hM.ne',Real.log_exp,Real.log_pow] at hh
  have hl := Real.log_le_sub_one_of_pos hM
  linarith only [hh,hl]

theorem core_pressure_upper {t β : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hsep : 2*(1+shellDelta)*Real.exp (-t) < 1) (h : ℝ) :
    physicalPressure (coreProfile t) t (β,h) ≤
      (1+Real.exp (t*h-β*t^2/2)+packingDensity*(2+Real.log (max 1 (clusterActivity t (t*h)))))/t := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hlim := physicalPressure_tendsto
    (measurable_radialPotential (measurable_coreProfile t)) ht hβ
    (coreProfile_stable_zero t) (fun _ _ => le_refl _) (h := h)
  have hl := (((packingNumber_tendsto.mul_const
    (2+Real.log (max 1 (clusterActivity t (t*h))))).const_add
      (1+Real.exp (t*h-β*t^2/2))).div_const t)
  apply le_of_tendsto_of_tendsto hlim hl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have hh := div_le_div_of_nonneg_right (core_log_upper hsep (t*h) L hβ)
    (show 0 ≤ t*L^3 by positivity)
  rw [grandIntegral_radial,Measure.real,volume_cube,ENNReal.toReal_pow,ENNReal.toReal_ofReal hL.le] at hh
  convert hh using 1; field_simp

lemma log_max_one {x : ℝ} (hx : 0 < x) : Real.log (max 1 x) = max 0 (Real.log x) := by
  by_cases h : 1 ≤ x
  · rw [max_eq_right h,max_eq_right (Real.log_nonneg h)]
  · have h' := le_of_not_ge h
    rw [max_eq_left h',Real.log_one,max_eq_left (Real.log_nonpos hx.le h')]

lemma volume_shellBall (t : ℝ) :
    volume.real (Metric.closedBall (0 : Space) ((1+shellDelta)*Real.exp (-t))) =
      ((1+shellDelta)^3*volume.real (Metric.ball (0 : Space) 1))*Real.exp (-3*t) := by
  rw [Measure.addHaar_real_closedBall volume _ (by unfold shellDelta; positivity)]
  have hd : Module.finrank ℝ Space = 3 := by simp [Space]
  rw [hd,mul_pow,← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show (3 : ℝ)*(-t) = -3*t by ring]
  ring

lemma shellVolumeConstant_pos : 0 < shellVolumeConstant := by
  unfold shellVolumeConstant
  apply mul_pos (by unfold shellDelta; positivity)
  exact ENNReal.toReal_pos (Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr zero_lt_one)).ne' measure_ball_lt_top.ne

lemma log_clusterActivity (t d : ℝ) :
    Real.log (max 1 (clusterActivity t d)) =
      max 0 (d+3*max 0 (Real.log shellVolumeConstant-3*t+d)) := by
  have hw : 0 < volume.real (Metric.closedBall (0 : Space) ((1+shellDelta)*Real.exp (-t))) := by
    rw [volume_shellBall]
    exact mul_pos shellVolumeConstant_pos (Real.exp_pos _)
  have hθ : 0 < clusterActivity t d := by
    unfold clusterActivity
    exact mul_pos (Real.exp_pos _) (pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) 3)
  rw [log_max_one hθ]
  congr 1
  unfold clusterActivity
  rw [Real.log_mul (Real.exp_pos _).ne' (pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))),
    Real.log_exp,Real.log_pow,log_max_one (mul_pos hw (Real.exp_pos _)),
    Real.log_mul hw.ne' (Real.exp_pos _).ne',Real.log_exp,volume_shellBall]
  change d+(3 : ℝ)*max 0 (Real.log (shellVolumeConstant*Real.exp (-3*t))+d) = _
  rw [Real.log_mul shellVolumeConstant_pos.ne' (Real.exp_pos _).ne',Real.log_exp]
  ring_nf

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.UpperLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Filter
namespace ContinuumTemperature

lemma idealCorePressure_eq (h : ℝ) :
    packingDensity*max 0 (h+3*max 0 (h-3)) = idealCorePressure h := by
  unfold idealCorePressure
  have hp := packingDensity_pos
  by_cases h3 : 3 ≤ h
  · rw [max_eq_right (sub_nonneg.mpr h3)]
    rw [max_eq_right (by linarith : 0 ≤ h+3*(h-3))]
    rw [max_eq_right (by nlinarith : packingDensity*h ≤ 4*packingDensity*h-9*packingDensity)]
    rw [max_eq_right (by nlinarith : 0 ≤ 4*packingDensity*h-9*packingDensity)]
    ring
  · have h3' : h ≤ 3 := (lt_of_not_ge h3).le
    rw [max_eq_left (sub_nonpos.mpr h3'), mul_zero,add_zero]
    rw [max_eq_left (by nlinarith : 4*packingDensity*h-9*packingDensity ≤ packingDensity*h)]
    simpa only [mul_zero] using mul_max_of_nonneg (0 : ℝ) h hp.le

lemma bad_activity_div_tendsto {β : ℝ} (hβ : 0 < β) (h : ℝ) :
    Tendsto (fun t : ℝ => Real.exp (t*h-β*t^2/2)/t) atTop (𝓝 0) := by
  have hi : Tendsto (fun t : ℝ => 1/t) atTop (𝓝 0) := by simpa using tendsto_inv_atTop_zero (𝕜 := ℝ)
  apply squeeze_zero' _ _ hi
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    positivity
  · filter_upwards [eventually_ge_atTop (max 1 (2*h/β))] with t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans ht)
    have hh : 2*h ≤ β*t := by
      have hh := (div_le_iff₀ hβ).mp ((le_max_right _ _).trans ht)
      nlinarith
    have hex : t*h-β*t^2/2 ≤ 0 := by nlinarith [mul_le_mul_of_nonneg_left hh ht0.le]
    apply div_le_div_of_nonneg_right _ ht0.le
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hex

lemma log_clusterActivity_scaled_tendsto (h : ℝ) :
    Tendsto (fun t : ℝ => Real.log (max 1 (clusterActivity t (t*h)))/t)
      atTop (𝓝 (max 0 (h+3*max 0 (h-3)))) := by
  have hi : Tendsto (fun t : ℝ => Real.log shellVolumeConstant/t) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (Real.log shellVolumeConstant)
  have hh := (tendsto_const_nhds (x := (0 : ℝ))).max (((tendsto_const_nhds (x := h)).add
    (((tendsto_const_nhds (x := (0 : ℝ))).max
      ((hi.sub_const 3).add_const h)).const_mul 3)))
  have heq : max (0 : ℝ) (h+3*max 0 (0-3+h)) = max 0 (h+3*max 0 (h-3)) := by ring_nf
  rw [heq] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [log_clusterActivity]
  have he : max 0 (t*h+3*max 0 (Real.log shellVolumeConstant-3*t+t*h))/t =
      max 0 (h+3*max 0 (Real.log shellVolumeConstant/t-3+h)) := by
    rw [← max_div_div_right ht.le,zero_div,add_div,
      mul_div_assoc 3, ← max_div_div_right ht.le,zero_div,add_div,sub_div]
    field_simp
  simpa only [sub_zero,zero_sub,zero_add] using he.symm

lemma core_upper_bound_tendsto {β : ℝ} (hβ : 0 < β) (h : ℝ) :
    Tendsto (fun t : ℝ =>
      (1+Real.exp (t*h-β*t^2/2)+packingDensity*(2+Real.log (max 1 (clusterActivity t (t*h)))))/t)
      atTop (𝓝 (idealCorePressure h)) := by
  have hi : Tendsto (fun t : ℝ => 1/t) atTop (𝓝 0) := by simpa using tendsto_inv_atTop_zero (𝕜 := ℝ)
  have hh := (hi.add (bad_activity_div_tendsto hβ h)).add
    (((hi.const_mul 2).add (log_clusterActivity_scaled_tendsto h)).const_mul packingDensity)
  simp only [mul_zero,zero_add,idealCorePressure_eq] at hh
  convert hh using 1
  funext t
  ring

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PackingBalls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped BigOperators
open Set
namespace ContinuumTemperature

lemma closedBall_subset_cube {L r : ℝ} {c : Space} (hc : c ∈ cube L) :
    Metric.closedBall c r ⊆ cube (L+2*r) := by
  intro x hx k
  rw [Metric.mem_closedBall,dist_eq_norm] at hx
  have hd : |x k-c k| ≤ r := by
    exact (show |x k-c k| ≤ ‖x-c‖ from PiLp.norm_apply_le (x-c) k).trans hx
  have hh := abs_le.mp hd
  have hk : -L/2 ≤ c k ∧ c k ≤ L/2 := hc k
  constructor <;> dsimp only [Set.mem_Icc] <;> linarith

lemma closedBall_cross_sep {η r : ℝ} (_hη : 0 ≤ η) (hr : 2*r ≤ η)
    {a b : Space} (hab : 1+η ≤ ‖a-b‖)
    {x y : Space} (hx : x ∈ Metric.closedBall a r) (hy : y ∈ Metric.closedBall b r) :
    1 ≤ ‖x-y‖ := by
  rw [Metric.mem_closedBall,dist_eq_norm] at hx hy
  have h1 := norm_sub_le_norm_sub_add_norm_sub a x y
  have h2 := norm_sub_le_norm_sub_add_norm_sub a y b
  rw [norm_sub_rev a x] at h1
  linarith

lemma packingBalls_disjoint {ι : Type u_1} {η r : ℝ} (hη : 0 ≤ η) (hr : 2*r ≤ η)
    {c : ι → Space} (hsep : ∀ i j, i ≠ j → 1+η ≤ ‖c i-c j‖) {i j : ι} (hij : i ≠ j) :
    Disjoint (Metric.closedBall (c i) r) (Metric.closedBall (c j) r) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hh := closedBall_cross_sep hη hr (hsep i j hij) hx hy
  simp only [sub_self,norm_zero] at hh
  linarith

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
-- module Solutions.OAIQW_ContinuumTemperature.Tetrahedron
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

lemma tetraRaw_zero : tetraRaw 0 = 0 := by ext k; fin_cases k <;> simp [tetraRaw]

lemma tetraRaw_dist {i j : Fin 4} (hij : i ≠ j) : ‖tetraRaw i-tetraRaw j‖ = Real.sqrt 2 := by
  have he : ‖tetraRaw i-tetraRaw j‖^2 = 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    fin_cases i <;> fin_cases j <;> norm_num [tetraRaw, Fin.sum_univ_succ] at *
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn := norm_nonneg (tetraRaw i-tetraRaw j)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  nlinarith only [he,hs,hn,hp]

lemma tetraVertex_zero : tetraVertex 0 = 0 := by rw [tetraVertex, tetraRaw_zero, smul_zero]

lemma tetraVertex_dist {i j : Fin 4} (hij : i ≠ j) :
    ‖tetraVertex i-tetraVertex j‖ = 1+shellDelta/2 := by
  rw [tetraVertex, tetraVertex, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by unfold shellDelta; positivity), tetraRaw_dist hij]
  exact div_mul_cancel₀ _ (Real.sqrt_pos.2 (by norm_num)).ne'

lemma tetraVertex_norm (i : Fin 4) : ‖tetraVertex i‖ ≤ 1+shellDelta/2 := by
  by_cases hi : i=0
  · rw [hi,tetraVertex_zero,norm_zero]
    unfold shellDelta
    norm_num
  · simpa only [tetraVertex_zero,sub_zero] using (tetraVertex_dist hi).le

lemma clusterRadius_pos (t : ℝ) : 0 < clusterRadius t := by unfold clusterRadius shellDelta; positivity

lemma tetraCluster_free {t : ℝ} {x : Fin 4 → Space} (hx : TetraCluster t x) : FreeConfig t x := by
  intro i j hij _
  let a := x i-x j
  let b := Real.exp (-t) • (tetraVertex i-tetraVertex j)
  have he : a-b = ((x i-x 0)-Real.exp (-t) • tetraVertex i)-
      ((x j-x 0)-Real.exp (-t) • tetraVertex j) := by dsimp only [a,b]; module
  have hd : ‖a-b‖ ≤ 2*clusterRadius t := by
    rw [he]
    exact (norm_sub_le _ _).trans (by linarith only [hx i,hx j])
  have hb : ‖b‖ = Real.exp (-t)*(1+shellDelta/2) := by
    dsimp only [b]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),tetraVertex_dist hij]
  have hnorm := abs_norm_sub_norm_le a b
  have hlo := (abs_le.mp (hnorm.trans hd)).1
  have hup := (abs_le.mp (hnorm.trans hd)).2
  rw [hb] at hlo hup
  change Real.exp (-t) ≤ ‖a‖ ∧ ‖a‖ ≤ (1+shellDelta)*Real.exp (-t)
  dsimp only [clusterRadius] at hlo hup
  have hδ : 0 ≤ shellDelta*Real.exp (-t) := by unfold shellDelta; positivity
  constructor <;> linarith

lemma tetraCluster_norm_le {t : ℝ} {x : Fin 4 → Space} (hx : TetraCluster t x) (i : Fin 4) :
    ‖x i-x 0‖ ≤ 2*Real.exp (-t) := by
  have hh := norm_le_norm_add_norm_sub (Real.exp (-t) • tetraVertex i) (x i-x 0)
  rw [norm_sub_rev (Real.exp (-t) • tetraVertex i),norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] at hh
  have hmul := mul_le_mul_of_nonneg_left (tetraVertex_norm i) (Real.exp_pos (-t)).le
  have hd := hx i
  dsimp only [clusterRadius] at hd
  have he : 0 < Real.exp (-t) := Real.exp_pos _
  unfold shellDelta at hmul hd
  linarith

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.TetraVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators ENNReal
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

lemma measurableSet_tetraTrial (t r : ℝ) (c : Space) : MeasurableSet (tetraTrial t r c) := by
  apply ((measurableSet_closedBall).preimage (measurable_pi_apply 0)).inter
  apply measurableSet_forall_labels
  intro j
  change MeasurableSet {x : Fin 4 → Space | ‖x j.succ-(x 0+Real.exp (-t) • tetraVertex j.succ)‖ ≤ clusterRadius t}
  exact measurableSet_le
    (((measurable_pi_apply j.succ : Measurable (fun x : Fin 4 → Space => x j.succ)).sub
      ((measurable_pi_apply 0).add measurable_const)).norm) measurable_const

lemma tetraTrial_cluster {t r : ℝ} {c : Space} {x : Fin 4 → Space}
    (hx : x ∈ tetraTrial t r c) : TetraCluster t x := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [sub_self,tetraVertex_zero,smul_zero,norm_zero]
    exact (clusterRadius_pos t).le
  · have hh := hx.2 j
    rw [Metric.mem_closedBall,dist_eq_norm] at hh
    have he : (x j.succ-x 0)-Real.exp (-t) • tetraVertex j.succ =
        x j.succ-(x 0+Real.exp (-t) • tetraVertex j.succ) := by module
    rw [he]
    exact hh

lemma tetraTrial_subset {t r : ℝ} {c : Space} (ht : 2*Real.exp (-t) ≤ r/2) :
    tetraTrial t r c ⊆ {x | ∀ i, x i ∈ Metric.closedBall c r} := by
  intro x hx i
  rw [Metric.mem_closedBall,dist_eq_norm]
  have hi := tetraCluster_norm_le (tetraTrial_cluster hx) i
  have h0 := hx.1
  rw [Metric.mem_closedBall,dist_eq_norm] at h0
  have hh := norm_sub_le_norm_sub_add_norm_sub (x i) (x 0) c
  linarith

lemma volume_tetraTrial (t r : ℝ) (c : Space) :
    volume (tetraTrial t r c) = volume (Metric.closedBall c (r/2))*
      (volume (Metric.closedBall (0 : Space) (clusterRadius t)))^3 := by
  let T : Set (Space × (Fin 3 → Space)) := {z | z.1 ∈ Metric.closedBall c (r/2) ∧
    ∀ j, z.2 j ∈ Metric.closedBall (z.1+Real.exp (-t) • tetraVertex j.succ) (clusterRadius t)}
  have hm : MeasurableSet T := by
    apply (measurableSet_closedBall.preimage measurable_fst).inter
    apply measurableSet_forall_labels
    intro j
    change MeasurableSet {z : Space × (Fin 3 → Space) |
      ‖z.2 j-(z.1+Real.exp (-t) • tetraVertex j.succ)‖ ≤ clusterRadius t}
    exact measurableSet_le
      ((((measurable_pi_apply j : Measurable (fun x : Fin 3 → Space => x j)).comp measurable_snd).sub
        (measurable_fst.add measurable_const)).norm) measurable_const
  have hp := volume_preserving_piFinSuccAbove (fun _ : Fin 4 => Space) 0
  have hpre : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => Space) 0) ⁻¹' T =
      tetraTrial t r c := by
    ext x
    rfl
  have he := hp.measure_preimage hm.nullMeasurableSet
  rw [hpre] at he
  rw [he]
  change (volume.prod volume) T = _
  rw [Measure.prod_apply hm]
  have hf (a : Space) : volume (Prod.mk a ⁻¹' T) =
      (Metric.closedBall c (r/2)).indicator
        (fun _ => (volume (Metric.closedBall (0 : Space) (clusterRadius t)))^3) a := by
    by_cases ha : a ∈ Metric.closedBall c (r/2)
    · rw [indicator_of_mem ha]
      have he : Prod.mk a ⁻¹' T = Set.pi Set.univ
          (fun j : Fin 3 => Metric.closedBall (a+Real.exp (-t) • tetraVertex j.succ) (clusterRadius t)) := by
        ext b
        simp only [T, mem_preimage, mem_ofPred_eq, ha, true_and, mem_pi, mem_univ, forall_true_left]
      rw [he, volume_pi, Measure.pi_pi]
      simp only [Measure.addHaar_closedBall_center, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    · rw [indicator_of_notMem ha]
      have he : Prod.mk a ⁻¹' T = ∅ := by
        ext b
        simp only [T, mem_preimage, mem_ofPred_eq, mem_empty_iff_false]
        exact iff_false_intro (fun hh => ha hh.1)
      rw [he,measure_empty]
  simp_rw [hf]
  rw [lintegral_indicator_const measurableSet_closedBall]
  exact mul_comm _ _

lemma freeConfig_core_energy {ι : Type} [Fintype ι] {t : ℝ} (ht : 1 < t)
    {x : ι → Space} (hx : FreeConfig t x) :
    gibbsEnergy (fun x y => coreProfile t ‖x-y‖) x = 0 := by
  unfold gibbsEnergy
  have he (i j : ι) : (if i=j then 0 else coreProfile t ‖x i-x j‖) = 0 := by
    split_ifs with hij
    · rfl
    · by_cases hd : ‖x i-x j‖ < 1
      · obtain ⟨hlo,hup⟩ := hx i j hij hd
        simp only [coreProfile, ite_eq_right (not_lt_of_ge hlo), ite_eq_left hup]
      · exact coreProfile_eq_zero ht (le_of_not_gt hd)
  simp_rw [he]
  simp

lemma tetraTrial_gibbs {t r β d : ℝ} (ht : 1 < t) {c : Space} {x : Fin 4 → Space}
    (hx : x ∈ tetraTrial t r c) :
    gibbsFamily (fun x y => coreProfile t ‖x-y‖) β d (Fin 4) x = Real.exp (4*d) := by
  have hf := tetraCluster_free (tetraTrial_cluster hx)
  simp only [gibbsFamily,ite_eq_left (freeConfig_injective hf),freeConfig_core_energy ht hf,
    Fintype.card_fin,Nat.cast_ofNat,mul_zero,sub_zero,mul_comm d]

lemma tetraTrial_term_lower {t β r : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hr : 2*Real.exp (-t) ≤ r/2) (d : ℝ) (c : Space) :
    volume.real (Metric.closedBall c (r/2))*(volume.real (Metric.closedBall (0 : Space) (clusterRadius t)))^3*
      Real.exp (4*d)/24 ≤ familyTerm (gibbsFamily (fun x y => coreProfile t ‖x-y‖) β d)
        (Metric.closedBall c r) 4 := by
  have hi := (core_gibbs_finite t d hβ (measure_closedBall_lt_top.ne) (D := Metric.closedBall c r)).integrable (Fin 4)
  have hs := tetraTrial_subset (c := c) hr
  have he : (∫ x in tetraTrial t r c, gibbsFamily (fun x y => coreProfile t ‖x-y‖) β d (Fin 4) x) =
      volume.real (tetraTrial t r c)*Real.exp (4*d) := by
    rw [setIntegral_congr_fun (measurableSet_tetraTrial t r c) (fun x hx => tetraTrial_gibbs ht hx),
      setIntegral_const,smul_eq_mul]
  have hh := setIntegral_mono_set hi
    (Filter.Eventually.of_forall (gibbsFamily_nonneg (fun x y => coreProfile t ‖x-y‖) β d (Fin 4)))
    (Filter.Eventually.of_forall hs)
  change (∫ x in tetraTrial t r c, gibbsFamily (fun x y => coreProfile t ‖x-y‖) β d (Fin 4) x) ≤ _ at hh
  rw [he,Measure.real,volume_tetraTrial,ENNReal.toReal_mul,ENNReal.toReal_pow] at hh
  have hd := div_le_div_of_nonneg_right hh (show (0 : ℝ) ≤ 24 by norm_num)
  simpa [familyTerm, familyIntegral, Nat.factorial, Measure.real] using hd

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PackingLower
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

lemma core_one_term (t β d r : ℝ) (c : Space) :
    familyTerm (gibbsFamily (fun x y => coreProfile t ‖x-y‖) β d)
      (Metric.closedBall c r) 1 = volume.real (Metric.closedBall (0 : Space) r)*Real.exp d := by
  have he (x : Fin 1 → Space) :
      gibbsFamily (fun x y => coreProfile t ‖x-y‖) β d (Fin 1) x = Real.exp d := by
    have hi : Function.Injective x := fun i j _ => Subsingleton.elim _ _
    simp [gibbsFamily, hi, gibbsEnergy]
  simp only [familyTerm, familyIntegral, he, setIntegral_const, smul_eq_mul,
    Measure.real, volume_generalConfigurations, Fintype.card_fin, pow_one]
  simp [Measure.addHaar_closedBall_center]

theorem core_grand_packing_lower {t β η r B : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hη : 0 ≤ η) (hr : 2*r ≤ η) (hB : 0 ≤ B) (d L : ℝ) (n : ℕ)
    (hterm : ∀ c : Space, B ≤ familyTerm
      (gibbsFamily (fun x y => coreProfile t ‖x-y‖) β d) (Metric.closedBall c r) n) :
    B^(packingNumber L) ≤ grandIntegral
      (gibbsFamily (fun x y => coreProfile t ‖x-y‖) β d) (cube ((1+η)*L+2*r)) := by
  obtain ⟨x,hx,hs⟩ := packingNumber_realized L
  obtain ⟨hc,hsep⟩ := dilate_packing hη x hx hs
  let A : Fin (packingNumber L) → Set Space := fun i => Metric.closedBall ((1+η) • x i) r
  let U : Space → Space → ℝ := fun x y => coreProfile t ‖x-y‖
  let F := gibbsFamily U β d
  let s : Finset (Fin (packingNumber L)) := Finset.univ
  have hAU : (⋃ i ∈ s, A i) ⊆ cube ((1+η)*L+2*r) := by
    apply iUnion₂_subset
    intro i _
    exact closedBall_subset_cube (hc i)
  have hfin : GrandFinite F (cube ((1+η)*L+2*r)) :=
    core_gibbs_finite t d hβ (isCompact_cube _).measure_lt_top.ne
  have hfinU := hfin.mono_set hAU (gibbsFamily_nonneg U β d)
  have hm : Measurable (Function.uncurry U) :=
    (measurable_coreProfile t).comp ((measurable_fst.sub measurable_snd).norm)
  have hA (i : Fin (packingNumber L)) (_ : i ∈ s) : MeasurableSet (A i) := measurableSet_closedBall
  have hFU := hfinU.fixedOccupation (fun _ => n) hA
    (fun ι _ => measurable_gibbsFamily hm β d ι) (gibbsFamily_nonneg U β d)
  have he := grandIntegral_fixedOccupation_product hm
    (fun a b => congrArg (coreProfile t) (norm_sub_rev a b)) β d A (fun _ => n) s hA
    (fun _ _ _ _ hij => packingBalls_disjoint hη hr hsep hij)
    (fun _ _ _ _ hij _ ha _ hb => coreProfile_eq_zero ht
      (closedBall_cross_sep hη hr (hsep _ _ hij) ha hb)) hfinU
  calc
    B^(packingNumber L) = ∏ _i ∈ s, B := by simp [s]
    _ ≤ ∏ i ∈ s, familyTerm F (A i) n :=
      Finset.prod_le_prod₀ (fun _ _ => hB) (fun i _ => hterm ((1+η) • x i))
    _ = grandIntegral (fixedOccupationFamily A s (fun _ => n) F) (⋃ i ∈ s, A i) := he.symm
    _ ≤ grandIntegral F (⋃ i ∈ s, A i) := by
      apply grandIntegral_mono _ _ (MeasurableSet.biUnion s.finite_toSet.countable hA)
        (fun _ => hFU.integrable _) (fun _ => hfinU.integrable _) hFU.summable hfinU.summable
      intro n x _
      unfold fixedOccupationFamily
      split_ifs
      · rfl
      · exact gibbsFamily_nonneg U β d (Fin n) x
    _ ≤ _ := grandIntegral_mono_set F hAU (gibbsFamily_nonneg U β d)
      (fun _ => hfin.integrable _) hfinU.summable hfin.summable

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PackingPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Filter MeasureTheory Set
namespace ContinuumTemperature

lemma packing_ratio_affine_tendsto {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun L : ℝ => (packingNumber L : ℝ)/(a*L+b)^3) atTop (𝓝 (packingDensity/a^3)) := by
  have hf := (((tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul b).const_add a).pow 3
  simp only [mul_zero,add_zero] at hf
  apply (packingNumber_tendsto.div hf (pow_ne_zero 3 ha.ne')).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have he : (a+b*L⁻¹) = (a*L+b)/L := by field_simp
  dsimp only [Pi.div_apply]
  rw [he,div_pow,div_div_div_cancel_right₀ (pow_ne_zero 3 hL.ne')]

theorem core_pressure_packing_lower {t β η r B : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hη : 0 ≤ η) (hr : 2*r ≤ η) (hB : 0 < B) (h : ℝ) (n : ℕ)
    (hterm : ∀ c : Space, B ≤ familyTerm
      (gibbsFamily (fun x y => coreProfile t ‖x-y‖) β (t*h)) (Metric.closedBall c r) n) :
    (packingDensity/(1+η)^3)*(Real.log B/t) ≤ physicalPressure (coreProfile t) t (β,h) := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have ha : 0 < 1+η := by linarith
  have hL : Tendsto (fun L : ℝ => (1+η)*L+2*r) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop ((b-2*r)/(1+η))] with L hL
    have hh := (div_le_iff₀ ha).mp hL
    nlinarith
  have hright := (physicalPressure_tendsto
    (measurable_radialPotential (measurable_coreProfile t)) ht hβ
    (coreProfile_stable_zero t) (fun _ _ => le_refl _) (h := h)).comp hL
  have hleft := (packing_ratio_affine_tendsto ha (2*r)).mul_const (Real.log B/t)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [hL.eventually (eventually_gt_atTop (0 : ℝ))] with L hpositive
  have hh := core_grand_packing_lower ht hβ hη hr hB.le (t*h) L n hterm
  have hlog := Real.log_le_log (pow_pos hB _) hh
  rw [Real.log_pow,grandIntegral_radial] at hlog
  have hd := div_le_div_of_nonneg_right hlog (show 0 ≤ t*((1+η)*L+2*r)^3 by positivity)
  convert hd using 1
  · simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · rfl

lemma core_pressure_one_lower {t β η : ℝ} (ht : 1 < t) (hβ : 0 ≤ β) (hη : 0 < η) (h : ℝ) :
    (packingDensity/(1+η)^3)*(h+Real.log (volume.real (Metric.closedBall (0 : Space) (η/4)))/t) ≤
      physicalPressure (coreProfile t) t (β,h) := by
  have hv : 0 < volume.real (Metric.closedBall (0 : Space) (η/4)) :=
    ENNReal.toReal_pos (Metric.measure_closedBall_pos volume _ (by positivity)).ne' measure_closedBall_lt_top.ne
  have hh := core_pressure_packing_lower ht hβ hη.le (r := η/4) (by linarith)
    (mul_pos hv (Real.exp_pos (t*h))) h 1 (fun c => (core_one_term t β (t*h) (η/4) c).ge)
  rw [Real.log_mul hv.ne' (Real.exp_pos _).ne', Real.log_exp] at hh
  convert hh using 1
  congr 1
  field_simp
  ring

lemma core_pressure_tetra_lower {t β η : ℝ} (ht : 1 < t) (hβ : 0 ≤ β) (hη : 0 < η)
    (hfit : 2*Real.exp (-t) ≤ η/8) (h : ℝ) :
    (packingDensity/(1+η)^3)*
      (Real.log (volume.real (Metric.closedBall (0 : Space) (η/8))*
        (volume.real (Metric.closedBall (0 : Space) (clusterRadius t)))^3*Real.exp (4*(t*h))/24)/t) ≤
      physicalPressure (coreProfile t) t (β,h) := by
  have hv : 0 < volume.real (Metric.closedBall (0 : Space) (η/8)) :=
    ENNReal.toReal_pos (Metric.measure_closedBall_pos volume _ (by positivity)).ne' measure_closedBall_lt_top.ne
  have hw : 0 < volume.real (Metric.closedBall (0 : Space) (clusterRadius t)) :=
    ENNReal.toReal_pos (Metric.measure_closedBall_pos volume _ (clusterRadius_pos t)).ne' measure_closedBall_lt_top.ne
  apply core_pressure_packing_lower ht hβ hη.le (r := η/4) (by linarith)
    (by positivity) h 4
  intro c
  have hh := tetraTrial_term_lower (r := η/4) ht hβ (by simpa only [div_div,show (4:ℝ)*2=8 by norm_num] using hfit) (t*h) c
  simpa only [Measure.real, Measure.addHaar_closedBall_center,div_div,show (4:ℝ)*2=8 by norm_num] using hh

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.LowerLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Filter MeasureTheory Set
namespace ContinuumTemperature

lemma cluster_ball_volume (t : ℝ) :
    volume.real (Metric.closedBall (0 : Space) (clusterRadius t)) =
      ((shellDelta/8)^3*volume.real (Metric.ball (0 : Space) 1))*Real.exp (-3*t) := by
  rw [Measure.addHaar_real_closedBall volume _ (clusterRadius_pos t).le]
  have hd : Module.finrank ℝ Space = 3 := by simp [Space]
  rw [hd]
  unfold clusterRadius
  rw [mul_pow,← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show (3 : ℝ)*(-t) = -3*t by ring]
  ring

lemma cluster_ball_constant_pos : 0 < (shellDelta/8)^3*volume.real (Metric.ball (0 : Space) 1) := by
  apply mul_pos (by unfold shellDelta; positivity)
  exact ENNReal.toReal_pos (Metric.measure_ball_pos volume _ zero_lt_one).ne' measure_ball_lt_top.ne

lemma tetra_log_scaled_tendsto {η : ℝ} (hη : 0 < η) (h : ℝ) :
    Tendsto (fun t : ℝ =>
      Real.log (volume.real (Metric.closedBall (0 : Space) (η/8))*
        (volume.real (Metric.closedBall (0 : Space) (clusterRadius t)))^3*Real.exp (4*(t*h))/24)/t)
      atTop (𝓝 (4*h-9)) := by
  let C := (shellDelta/8)^3*volume.real (Metric.ball (0 : Space) 1)
  let V := volume.real (Metric.closedBall (0 : Space) (η/8))
  have hC : 0 < C := cluster_ball_constant_pos
  have hV : 0 < V := ENNReal.toReal_pos (Metric.measure_closedBall_pos volume _ (by positivity)).ne' measure_closedBall_lt_top.ne
  have hi := ((tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul
    (Real.log V+3*Real.log C-Real.log 24)).const_add (4*h-9)
  simp only [mul_zero,add_zero] at hi
  apply hi.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [cluster_ball_volume]
  change 4*h-9+(Real.log V+3*Real.log C-Real.log 24)*t⁻¹ =
    Real.log (V*(C*Real.exp (-3*t))^3*Real.exp (4*(t*h))/24)/t
  rw [Real.log_div (mul_pos (mul_pos hV (pow_pos (mul_pos hC (Real.exp_pos _)) 3)) (Real.exp_pos _)).ne' (by norm_num),
    Real.log_mul (mul_pos hV (pow_pos (mul_pos hC (Real.exp_pos _)) 3)).ne' (Real.exp_pos _).ne',
    Real.log_exp, Real.log_mul hV.ne' (pow_ne_zero 3 (mul_pos hC (Real.exp_pos _)).ne'),
    Real.log_pow, Real.log_mul hC.ne' (Real.exp_pos _).ne',Real.log_exp]
  field_simp
  ring

lemma core_one_lower_eventually {β η : ℝ} (hβ : 0 ≤ β) (hη : 0 < η) (h : ℝ) {c : ℝ}
    (hc : c < (packingDensity/(1+η)^3)*h) :
    ∀ᶠ t : ℝ in atTop, c < physicalPressure (coreProfile t) t (β,h) := by
  have hi := (((tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul
    (Real.log (volume.real (Metric.closedBall (0 : Space) (η/4))))).const_add h).const_mul
    (packingDensity/(1+η)^3)
  simp only [mul_zero,add_zero] at hi
  filter_upwards [hi.eventually_const_lt hc,eventually_gt_atTop (1 : ℝ)] with t ht h1
  apply ht.trans_le
  simpa only [div_eq_mul_inv] using core_pressure_one_lower h1 hβ hη h

lemma core_tetra_lower_eventually {β η : ℝ} (hβ : 0 ≤ β) (hη : 0 < η) (h : ℝ) {c : ℝ}
    (hc : c < (packingDensity/(1+η)^3)*(4*h-9)) :
    ∀ᶠ t : ℝ in atTop, c < physicalPressure (coreProfile t) t (β,h) := by
  have hi := (tetra_log_scaled_tendsto hη h).const_mul (packingDensity/(1+η)^3)
  have hfit : ∀ᶠ t : ℝ in atTop, 2*Real.exp (-t) < η/8 := by
    have hh := (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul 2
    simp only [mul_zero] at hh
    exact hh.eventually_lt_const (by positivity)
  filter_upwards [hi.eventually_const_lt hc,eventually_gt_atTop (1 : ℝ),hfit] with t ht h1 hf
  exact ht.trans_le (core_pressure_tetra_lower h1 hβ hη hf.le h)

lemma packing_dilate_tendsto (a : ℝ) :
    Tendsto (fun η : ℝ => (packingDensity/(1+η)^3)*a) (𝓝[>] 0) (𝓝 (packingDensity*a)) := by
  have hh : Tendsto (fun η : ℝ => (packingDensity/(1+η)^3)*a) (𝓝 0)
      (𝓝 ((packingDensity/(1+(0 : ℝ))^3)*a)) :=
    (tendsto_const_nhds.div ((tendsto_id.const_add 1).pow 3) (by norm_num)).mul_const a
  simpa only [add_zero,one_pow,div_one] using hh.mono_left (nhdsWithin_le_nhds (s := Ioi 0))

lemma exists_packing_dilate_lt {c a : ℝ} (hc : c < packingDensity*a) :
    ∃ η : ℝ, 0 < η ∧ c < (packingDensity/(1+η)^3)*a := by
  have hh := (packing_dilate_tendsto a).eventually_const_lt hc
  obtain ⟨η,hη,he⟩ := (hh.and self_mem_nhdsWithin).exists
  exact ⟨η,he,hη⟩

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.FreeLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Filter Set
namespace ContinuumTemperature

lemma core_pressure_nonneg {t β : ℝ} (ht : 1 < t) (hβ : 0 ≤ β) (h : ℝ) :
    0 ≤ physicalPressure (coreProfile t) t (β,h) := by
  exact div_nonneg (canonicalPressure_nonneg
    (measurable_radialPotential (measurable_coreProfile t)) ht hβ
    (coreProfile_stable_zero t) (fun _ _ => le_refl _)) (by linarith)

theorem core_pressure_tendsto {β : ℝ} (hβ : 0 < β) (h : ℝ) :
    Tendsto (fun t : ℝ => physicalPressure (coreProfile t) t (β,h))
      atTop (𝓝 (idealCorePressure h)) := by
  refine tendsto_order.2 ⟨?_,?_⟩
  · intro c hc
    unfold idealCorePressure at hc
    rcases lt_max_iff.mp hc with hc | hc
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
      exact hc.trans_le (core_pressure_nonneg ht hβ.le h)
    · rcases lt_max_iff.mp hc with hc | hc
      · obtain ⟨η,hη,he⟩ := exists_packing_dilate_lt hc
        exact core_one_lower_eventually hβ.le hη h he
      · have hc' : c < packingDensity*(4*h-9) := by nlinarith only [hc]
        obtain ⟨η,hη,he⟩ := exists_packing_dilate_lt hc'
        exact core_tetra_lower_eventually hβ.le hη h he
  · intro c hc
    have hsep : ∀ᶠ t : ℝ in atTop, 2*(1+shellDelta)*Real.exp (-t) < 1 := by
      have hh := (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul (2*(1+shellDelta))
      simp only [mul_zero] at hh
      exact hh.eventually_lt_const zero_lt_one
    filter_upwards [(core_upper_bound_tendsto hβ h).eventually_lt_const hc,
      eventually_gt_atTop (1 : ℝ),hsep] with t ht h1 hs
    exact (core_pressure_upper h1 hβ.le hs h).trans_lt ht

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PhysicalUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter
namespace ContinuumTemperature

 theorem core_pressure_locally_uniform_oai :
    TendstoLocallyUniformlyOn (fun t : ℝ => physicalPressure (coreProfile t) t)
      (fun x : Parameter => idealCorePressure x.2) atTop pressureDomain := by
  apply convex_pointwise_locally_uniform isOpen_pressureDomain
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    exact convexOn_physicalPressure (measurable_radialPotential (measurable_coreProfile t)) ht
      (coreProfile_stable_zero t) (fun _ _ => le_refl _)
  · intro x hx
    exact core_pressure_tendsto hx x.2

end ContinuumTemperature
end

end OAI
end

theorem solution : type_of% @OAI.ContinuumTemperature.core_pressure_locally_uniform_oai := @OAI.ContinuumTemperature.core_pressure_locally_uniform_oai
