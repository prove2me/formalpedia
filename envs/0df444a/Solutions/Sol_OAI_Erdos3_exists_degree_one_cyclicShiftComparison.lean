-- Prove2me | solution 1 for OAI.Erdos3.exists_degree_one_cyclicShiftComparison
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T04:11:55.743091+00:00
-- url     : https://prove2.me/submissions/3bf331f9-2a91-4768-b4e9-5032ca4c3d21

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B039
import Theorems.Thm_OAI_Erdos3_CellRefinement_exists_refinement_matching_geometry
import Theorems.Thm_OAI_Erdos3_CellRefinement_normalized_bilinear_refinement_step

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComplexFiniteMeans
namespace OAI

section

open scoped BigOperators

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem bilinear_shift_identity (a J : G → ℝ) (E : Finset G) (c : ℝ) :
    realBilinearAverage a (fun x => c * J x) (fun y => if -y ∈ E then 1 else 0) =
      c * (𝔼 h, if h ∈ E then realShiftCorrelation a J h else 0) := by
  have hy (x : G) :
      (𝔼 y, (c * J x) * (if -y ∈ E then 1 else 0) * a (x + y)) =
        c * (𝔼 h, if h ∈ E then J x * a (x - h) else 0) := by
    calc
      _ = 𝔼 h, (c * J x) * (if h ∈ E then 1 else 0) * a (x - h) := by
        apply Fintype.expect_equiv (Equiv.neg G)
        intro y
        simp
      _ = _ := by
        rw [Finset.mul_expect]
        apply Finset.expect_congr rfl
        intro h _
        by_cases hh : h ∈ E <;> simp [hh, mul_assoc]
  unfold realBilinearAverage
  simp_rw [hy]
  rw [← Finset.mul_expect, Finset.expect_comm]
  congr 1
  apply Finset.expect_congr rfl
  intro h _
  by_cases hh : h ∈ E
  · simp only [hh, ite_true, realShiftCorrelation]
    symm
    apply Fintype.expect_equiv (Equiv.addRight h)
    intro n
    simp [mul_comm]
  · simp [hh]

theorem bilinear_bound_bad_shift_density (a J : G → ℝ) {M δ ε : ℝ}
    (hM : 0 < M) (hδ : 0 < δ)
    (hJ : ∀ x, 0 ≤ J x ∧ J x ≤ M)
    (hbilinear : ∀ H W : G → ℝ, (∀ x, 0 ≤ H x ∧ H x ≤ 1) →
      (∀ x, 0 ≤ W x ∧ W x ≤ 1) → realBilinearAverage a H W ≤ ε) :
    let E := Finset.univ.filter (fun h => δ < realShiftCorrelation a J h)
    (E.card : ℝ) / Fintype.card G ≤ M * ε / δ := by
  classical
  intro E
  let H : G → ℝ := fun x => M⁻¹ * J x
  let W : G → ℝ := fun y => if -y ∈ E then 1 else 0
  have hH : ∀ x, 0 ≤ H x ∧ H x ≤ 1 := by
    intro x
    constructor
    · exact mul_nonneg (inv_nonneg.mpr hM.le) (hJ x).1
    · dsimp [H]
      calc
        M⁻¹ * J x ≤ M⁻¹ * M := mul_le_mul_of_nonneg_left (hJ x).2 (inv_nonneg.mpr hM.le)
        _ = 1 := inv_mul_cancel₀ hM.ne'
  have hW : ∀ x, 0 ≤ W x ∧ W x ≤ 1 := by
    intro x
    dsimp [W]
    split_ifs <;> norm_num
  have hb := hbilinear H W hH hW
  rw [bilinear_shift_identity] at hb
  have hsum : (E.card : ℝ) * δ ≤ ∑ h ∈ E, realShiftCorrelation a J h := by
    calc
      _ = ∑ _h ∈ E, δ := by simp
      _ ≤ _ := Finset.sum_le_sum (fun h hh => (Finset.mem_filter.mp hh).2.le)
  have hcard : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hlower : δ * ((E.card : ℝ) / Fintype.card G) ≤
      𝔼 h, if h ∈ E then realShiftCorrelation a J h else 0 := by
    rw [Fintype.expect_eq_sum_div_card]
    simp only [Finset.sum_ite_mem, Finset.univ_inter]
    have := div_le_div_of_nonneg_right hsum hcard.le
    simpa only [mul_div_assoc, mul_comm] using this
  have hupper : (𝔼 h, if h ∈ E then realShiftCorrelation a J h else 0) ≤ M * ε := by
    have h := mul_le_mul_of_nonneg_left hb hM.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hM.ne', one_mul] using h
  exact (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using hlower.trans hupper)

theorem exists_small_bad_shift_set (a J : G → ℝ) {p : ℝ} (hp : 0 ≤ p)
    (hJ : ∀ x, 0 ≤ J x ∧ J x ≤ Real.exp p)
    (hbilinear : ∀ H W : G → ℝ, (∀ x, 0 ≤ H x ∧ H x ≤ 1) →
      (∀ x, 0 ≤ W x ∧ W x ≤ 1) → realBilinearAverage a H W ≤ Real.exp (-4 * p)) :
    ∃ E : Finset G, (E.card : ℝ) ≤ Real.exp (-p) * Fintype.card G ∧
      ∀ h ∉ E, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        realShiftCorrelation a J h * t ≤ Real.exp (-p) := by
  classical
  let E := Finset.univ.filter (fun h => Real.exp (-p) < realShiftCorrelation a J h)
  have h := bilinear_bound_bad_shift_density a J (Real.exp_pos p) (Real.exp_pos (-p)) hJ hbilinear
  change (E.card : ℝ) / Fintype.card G ≤ _ at h
  have hexp : Real.exp p * Real.exp (-4 * p) / Real.exp (-p) ≤ Real.exp (-p) := by
    rw [← Real.exp_add, ← Real.exp_sub]
    apply Real.exp_le_exp.mpr
    linarith
  have hcard : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  refine ⟨E, (div_le_iff₀ hcard).mp (h.trans hexp), ?_⟩
  intro k hk t ht ht1
  have hk' : realShiftCorrelation a J k ≤ Real.exp (-p) := by
    simpa only [E, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hk
  exact (mul_le_mul_of_nonneg_right hk' ht).trans
    (mul_le_of_le_one_right (Real.exp_nonneg _) ht1)

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*}

variable [Fintype G] [DecidableEq G]

variable [AddCommGroup G]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalizedAverageScaleOrder
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem localizedAverageScale_spec (rank : ℕ) {R epsilon : ℝ}
    (hR : 0 ≤ R) (hepsilon : 0 < epsilon) :
    0 < localizedAverageScale rank R epsilon ∧
      localizedAverageScale rank R epsilon ≤ 1 / (100 * (2 * max rank 1 : ℕ) : ℝ≥0) ∧
      R * (400 * (max rank 1 : ℕ) * (localizedAverageScale rank R epsilon : ℝ)) ≤ epsilon := by
  let d : ℝ := (max rank 1 : ℕ)
  let r : ℝ := min (1 / (200 * d)) (epsilon / (400 * d * (R + 1)))
  have hd : 0 < d := by dsimp [d]; positivity
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hcast : (localizedAverageScale rank R epsilon : ℝ) = r := Real.coe_toNNReal r hr.le
  refine ⟨Real.toNNReal_pos.mpr hr, ?_, ?_⟩
  · apply NNReal.coe_le_coe.mp
    push_cast
    rw [hcast]
    have hdcast : max (rank : ℝ) 1 = d := by simp [d]
    rw [hdcast]
    have h : r ≤ 1 / (200 * d) := min_le_left _ _
    convert h using 1
    ring
  · rw [hcast]
    change R * (400 * d * r) ≤ epsilon
    have h : r * (400 * d * (R + 1)) ≤ epsilon :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    nlinarith [mul_nonneg hr.le hd.le]

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.LocalizedAverageScaleBudget
namespace OAI

section

namespace Erdos3

theorem localizedAverageScale_exp_lower (rank : ℕ) {W A E : ℝ}
    (hW : 0 ≤ W) (hWA : W ≤ Real.exp A) (hA : 0 ≤ A) (hE : 0 ≤ E) :
    Real.exp (-((rank : ℝ) + A + E + 1600)) ≤
      (localizedAverageScale rank W (Real.exp (-E) / 2) : ℝ) := by
  let m : ℝ := (max rank 1 : ℕ)
  have hm : 0 < m := by dsimp [m]; positivity
  have hmexp : m ≤ Real.exp (rank : ℝ) := by
    apply le_trans _ (Real.add_one_le_exp (rank : ℝ))
    dsimp [m]
    exact_mod_cast (show max rank 1 ≤ rank + 1 by omega)
  have hWexp : W + 1 ≤ 2 * Real.exp A := by
    linarith [Real.one_le_exp hA]
  have hden : 800 * m * (W + 1) ≤ Real.exp ((rank : ℝ) + A + 1600) := by
    calc
      _ ≤ 800 * Real.exp (rank : ℝ) * (2 * Real.exp A) := by gcongr
      _ = 1600 * Real.exp ((rank : ℝ) + A) := by rw [Real.exp_add]; ring
      _ ≤ Real.exp 1600 * Real.exp ((rank : ℝ) + A) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        linarith [Real.add_one_le_exp 1600]
      _ = Real.exp ((rank : ℝ) + A + 1600) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hscaled : Real.exp (-((rank : ℝ) + A + E + 1600)) *
      (800 * m * (W + 1)) ≤ Real.exp (-E) := by
    calc
      _ ≤ Real.exp (-((rank : ℝ) + A + E + 1600)) *
          Real.exp ((rank : ℝ) + A + 1600) :=
        mul_le_mul_of_nonneg_left hden (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hmin : 0 ≤ min (1 / (200 * m)) ((Real.exp (-E) / 2) / (400 * m * (W + 1))) := by
    exact le_of_lt (lt_min (by positivity) (by positivity))
  change Real.exp (-((rank : ℝ) + A + E + 1600)) ≤
    ((min (1 / (200 * m)) ((Real.exp (-E) / 2) / (400 * m * (W + 1)))).toNNReal : ℝ)
  rw [Real.coe_toNNReal _ hmin]
  apply le_min
  · apply (le_div_iff₀ (by positivity : 0 < 200 * m)).mpr
    have hsmall : 200 * m ≤ 800 * m * (W + 1) := by nlinarith
    exact (mul_le_mul_of_nonneg_left hsmall (Real.exp_nonneg _)).trans
      (hscaled.trans (Real.exp_le_one_iff.mpr (by linarith)))
  · rw [div_div, show 2 * (400 * m * (W + 1)) = 800 * m * (W + 1) by ring]
    exact (le_div_iff₀ (by positivity)).mpr hscaled

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FlatWeightedComparison
namespace OAI

namespace Erdos3

open scoped BigOperators

variable {ι : Type*}

end Erdos3

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

end Erdos3.LocalConvolution

namespace Erdos3

open scoped BigOperators

variable {ι : Type*}

end Erdos3

namespace Erdos3.LocalConvolution

open scoped BigOperators

theorem momentAmplificationFactor_pos (delta : ℝ) : 0 < momentAmplificationFactor delta := by
  unfold momentAmplificationFactor
  omega

theorem momentAmplificationGain_pos (delta : ℝ) : 0 < momentAmplificationGain delta := by
  have hR : (0 : ℝ) < momentAmplificationFactor delta := by
    exact_mod_cast momentAmplificationFactor_pos delta
  have h := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) (by positivity : 0 < 1 / (momentAmplificationFactor delta : ℝ))
  unfold momentAmplificationGain
  linarith

theorem momentAmplificationGain_le_one (delta : ℝ) : momentAmplificationGain delta ≤ 1 := by
  have hR : (1 : ℝ) ≤ momentAmplificationFactor delta := by
    exact_mod_cast momentAmplificationFactor_pos delta
  have hinv : 1 / (momentAmplificationFactor delta : ℝ) ≤ 1 :=
    (div_le_one (by linarith)).mpr hR
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hinv
  rw [Real.rpow_one] at h
  unfold momentAmplificationGain
  linarith

end Erdos3.LocalConvolution

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

end Erdos3.LocalConvolution

namespace Erdos3

open scoped BigOperators

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PeelingDecomposition
namespace OAI

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

end Erdos3.Peeling

namespace Erdos3

open scoped BigOperators

namespace Peeling

end Peeling

namespace CellRefinement

variable {G : Type*} [AddCommGroup G]

theorem bilinearIntegral_le (A B : Finset G) (a f g : G → ℝ) {M : ℝ}
    (ha : ∀ x, a x ≤ M) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    bilinearIntegral A B a f g ≤ M * (𝔼 x ∈ A, f x) * (𝔼 y ∈ B, g y) := by
  calc
    _ ≤ 𝔼 x ∈ A, 𝔼 y ∈ B, f x * g y * M := by
      apply Finset.expect_le_expect
      intro x _
      apply Finset.expect_le_expect
      intro y _
      exact mul_le_mul_of_nonneg_left (ha _) (mul_nonneg (hf x) (hg y))
    _ = _ := by
      simp_rw [← Finset.expect_mul]
      rw [← Finset.expect_mul_expect]
      ring

variable [Fintype G] [DecidableEq G]

end CellRefinement
end Erdos3

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

end Erdos3.LocalConvolution

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

namespace Chain

variable {B : Finset G} {Admissible : Finset G → Prop} {K kappa : ℝ}
  {f g : G → ℝ} {cs : List (Finset G)}

end Chain
end Erdos3.Peeling

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

end Erdos3.Peeling

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

end Erdos3.Peeling

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalMomentScale
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace LocalConvolution

variable {G : Type*} [AddCommGroup G] [Fintype G]

variable [DecidableEq G]

end LocalConvolution
end Erdos3

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

variable [DecidableEq G]

end Erdos3.LocalConvolution

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

variable [AddCommGroup G]

end Erdos3

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators

theorem localMomentExponentFactor_pos (delta : ℝ) : 0 < localMomentExponentFactor delta :=
  momentAmplificationFactor_pos _

theorem localMomentGain_pos (delta : ℝ) : 0 < localMomentGain delta :=
  div_pos (momentAmplificationGain_pos _) (by norm_num)

theorem localMomentGain_le_half (delta : ℝ) : localMomentGain delta ≤ 1 / 2 :=
  div_le_div_of_nonneg_right (momentAmplificationGain_le_one _) (by norm_num)

variable {G : Type*} [AddCommGroup G] [Fintype G]

end Erdos3.LocalConvolution

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

end Erdos3

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

variable [DecidableEq G]

variable [Fintype G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped NNReal

end Erdos3.LocalConvolution

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ExponentialBohrVolume
namespace OAI

section

namespace Erdos3

open AddChar _root_.Finset
open scoped BigOperators

namespace CyclicBohr

variable {N : ℕ} [NeZero N]

namespace Set

lemma carrier_eq_univ_of_two_le_radius (B : Set N) (hB : 2 ≤ B.radius) :
    B.carrier = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro x
  rw [mem_carrier]
  intro r hr
  calc
    ‖1 - character r x‖ ≤ ‖(1 : ℂ)‖ + ‖character r x‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_character]; norm_num
    _ ≤ B.radius := hB

end Set
end CyclicBohr
end Erdos3

end

section

namespace Erdos3

open AddChar _root_.Finset
open scoped BigOperators

namespace CyclicBohr

variable {N : ℕ} [NeZero N]

end CyclicBohr
end Erdos3

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr

end Erdos3.CyclicBohr

end

section

namespace Erdos3.CyclicBohr

open _root_.Finset
open scoped BigOperators

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicBohr

end

section

namespace Erdos3.CyclicBohr

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicBohr

end

section

namespace Erdos3.CyclicBohr.Set

end Erdos3.CyclicBohr.Set

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BohrTorusApproximation
namespace OAI

section

namespace Erdos3.CyclicBohr.Set

open _root_.Finset
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

end Erdos3

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CyclicBohr.Set

open scoped NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped NNReal

variable {N : ℕ} [NeZero N]

theorem carrier_eq_univ_of_rank_zero (B : Set N) (hB : B.rank = 0) :
    B.carrier = Finset.univ := by
  have hfreq : B.frequencies = ∅ := Finset.card_eq_zero.mp hB
  apply Finset.eq_univ_of_forall
  intro x
  simp [mem_carrier, hfreq]

theorem exists_bounded_presentation (B : Set N) (hB : B.IsRankRegular)
    (hBpos : 0 < B.radius) {d : ℕ} (hd : 1 ≤ d) (hrank : B.rank ≤ d)
    {w : ℝ} (hw : w ≤ 1) (hwidth : w ≤ B.radius) :
    ∃ C : Set N, C.carrier = B.carrier ∧ C.IsRankRegular ∧
      0 < C.radius ∧ 1 ≤ C.rank ∧ C.rank ≤ d ∧ w ≤ C.radius ∧ C.radius ≤ 2 := by
  by_cases hwhole : B.rank = 0 ∨ 2 ≤ B.radius
  · have hcarrier : B.carrier = Finset.univ := hwhole.elim
      (carrier_eq_univ_of_rank_zero B) (carrier_eq_univ_of_two_le_radius B)
    refine ⟨whole, ?_, isRankRegular_whole, ?_, ?_, ?_, ?_, ?_⟩
    · rw [carrier_whole, hcarrier]
    · norm_num
    · norm_num
    · simpa only [rank_whole] using hd
    · simpa only [radius_whole] using hw
    · norm_num
  · push Not at hwhole
    exact ⟨B, rfl, hB, hBpos, by omega, hrank, hwidth, hwhole.2.le⟩

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicBohr.Set

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteCellRefinement
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

end Erdos3

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

variable [Fintype G] [DecidableEq G]

end Erdos3.CellRefinement

end

section

namespace Erdos3

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

end Erdos3

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

variable [DecidableEq G]

variable [Fintype G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G]

variable [Fintype G] [DecidableEq G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G]

variable [DecidableEq G]

variable [Fintype G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

variable [Fintype G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

theorem CellBilinearBound.mono {C : Finset G} {a : G → ℝ} {T U : ℝ}
    (h : CellBilinearBound C a T) (hTU : T ≤ U) : CellBilinearBound C a U := by
  intro origin f g hf hg hfs hgs
  exact (h origin f g hf hg hfs hgs).trans (mul_le_mul_of_nonneg_right hTU
    (Real.rpow_nonneg (mul_nonneg (Finset.expect_nonneg (fun x _ => (hf x).1))
      (Finset.expect_nonneg (fun x _ => (hg x).1))) _))

theorem cellBilinearBound_of_upper (C : Finset G) (hC : C.Nonempty)
    (a : G → ℝ) {M : ℝ} (hM : 0 ≤ M) (ha : ∀ x, a x ≤ M) :
    CellBilinearBound C a M := by
  intro origin f g hf hg _ _
  have hu : 0 ≤ 𝔼 x ∈ C, f x := Finset.expect_nonneg (fun x _ => (hf x).1)
  have hv : 0 ≤ 𝔼 x ∈ C, g x := Finset.expect_nonneg (fun x _ => (hg x).1)
  have hu1 : (𝔼 x ∈ C, f x) ≤ 1 :=
    (Finset.expect_le_expect (fun x (_ : x ∈ C) => (hf x).2)).trans_eq (Finset.expect_const hC 1)
  have hv1 : (𝔼 x ∈ C, g x) ≤ 1 :=
    (Finset.expect_le_expect (fun x (_ : x ∈ C) => (hg x).2)).trans_eq (Finset.expect_const hC 1)
  have hprod : (𝔼 x ∈ C, f x) * (𝔼 x ∈ C, g x) ≤ 1 := by nlinarith
  have hpower := Real.self_le_rpow_of_le_one (mul_nonneg hu hv) hprod (by norm_num : (1 / 4 : ℝ) ≤ 1)
  have h := bilinearIntegral_le C C (fun x => a (origin + x)) f g
    (fun x => ha (origin + x)) (fun x => (hf x).1) (fun x => (hg x).1)
  exact h.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpower hM)

variable [DecidableEq G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] {I : Type*}

theorem finite_cell_refinement (carrier : I → Finset G) (family : ℕ → I → Prop)
    (a : G → ℝ) (n : ℕ) {W rho error : ℝ}
    (hW : 0 ≤ W) (hrho : 0 ≤ rho) (hrho1 : rho < 1) (herror : 0 ≤ error)
    (ha : ∀ r, a r ≤ W)
    (hnonempty : ∀ j C, family j C → (carrier C).Nonempty)
    (hstep : ∀ j, j < n → ∀ T : ℝ, 0 ≤ T →
      (∀ C, family (j + 1) C → CellBilinearBound (carrier C) a T) →
      ∀ C, family j C → CellBilinearBound (carrier C) a (rho * T + error)) :
    ∀ C, family 0 C →
      CellBilinearBound (carrier C) a (rho ^ n * W + error / (1 - rho)) := by
  have hgap : 0 < 1 - rho := by linarith
  have herr : 0 ≤ error / (1 - rho) := div_nonneg herror hgap.le
  have aux : ∀ k j : ℕ, j + k ≤ n → ∀ C, family j C →
      CellBilinearBound (carrier C) a (rho ^ k * W + error / (1 - rho)) := by
    intro k
    induction k with
    | zero =>
      intro j _ C hC
      apply (cellBilinearBound_of_upper (carrier C) (hnonempty j C hC) a hW ha).mono
      simpa only [pow_zero, one_mul] using le_add_of_nonneg_right herr
    | succ k ih =>
      intro j hj C hC
      have hT : 0 ≤ rho ^ k * W + error / (1 - rho) :=
        add_nonneg (mul_nonneg (pow_nonneg hrho _) hW) herr
      have h := hstep j (by omega) _ hT
        (fun D hD => ih (j + 1) (by omega) D hD) C hC
      apply h.mono
      apply le_of_eq
      rw [pow_succ]
      field_simp
      ring
  exact aux n 0 (by omega)

theorem refinement_coefficient_le {rho W error Q R : ℝ} {n : ℕ}
    (hrho : 0 ≤ rho) (hrho1 : rho < 1) (hW : 0 ≤ W) (hWcap : W ≤ Real.exp Q)
    (hdepth : Q + R ≤ (1 - rho) * n)
    (herror : error ≤ (1 - rho) * Real.exp (-R)) :
    rho ^ n * W + error / (1 - rho) ≤ 2 * Real.exp (-R) := by
  have hgap : 0 < 1 - rho := by linarith
  have hrhoExp : rho ≤ Real.exp (-(1 - rho)) := by
    linarith [Real.add_one_le_exp (-(1 - rho))]
  have hdecay : rho ^ n * W ≤ Real.exp (-R) := by
    calc
      _ ≤ (Real.exp (-(1 - rho))) ^ n * Real.exp Q :=
        mul_le_mul (pow_le_pow_left₀ hrho hrhoExp _) hWcap hW (by positivity)
      _ = Real.exp ((n : ℝ) * (-(1 - rho)) + Q) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have hnoise : error / (1 - rho) ≤ Real.exp (-R) :=
    (div_le_iff₀ hgap).mpr (by simpa only [mul_comm] using herror)
  linarith

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndependentReturnScale
namespace OAI

section

namespace Erdos3

theorem localizedAverageScale_mono_error (rank : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    Monotone (fun epsilon : ℝ => localizedAverageScale rank R epsilon) := by
  intro a b hab
  unfold localizedAverageScale
  apply Real.toNNReal_mono
  exact min_le_min le_rfl (div_le_div_of_nonneg_right hab (by positivity))

theorem localizedAverageScale_exp_lower_of_error (rank : ℕ) {W A E epsilon : ℝ}
    (hW : 0 ≤ W) (hWA : W ≤ Real.exp A) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hepsilon : Real.exp (-E) / 2 ≤ epsilon) :
    Real.exp (-((rank : ℝ) + A + E + 1600)) ≤ (localizedAverageScale rank W epsilon : ℝ) := by
  apply (localizedAverageScale_exp_lower rank hW hWA hA hE).trans
  exact_mod_cast localizedAverageScale_mono_error rank hW hepsilon

end Erdos3

end

section

namespace Erdos3.CellRefinement

open scoped NNReal

end Erdos3.CellRefinement

end

section

namespace Erdos3.LocalConvolution

open scoped NNReal

theorem localMomentErrorBudget_spec {delta : ℝ} (hdelta : 0 < delta) :
    0 ≤ localMomentErrorBudget delta ∧
      Real.exp (-localMomentErrorBudget delta) / 2 = min (delta / 2) (localMomentGain delta) / 3 := by
  have hc : 0 < min (delta / 2) (localMomentGain delta) :=
    lt_min (by positivity) (localMomentGain_pos delta)
  have hc1 : min (delta / 2) (localMomentGain delta) ≤ 1 / 2 :=
    (min_le_right _ _).trans (localMomentGain_le_half delta)
  unfold localMomentErrorBudget
  constructor
  · exact neg_nonneg.mpr (Real.log_nonpos (by positivity) (by linarith))
  · rw [neg_neg, Real.exp_log (by positivity)]
    ring

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SiftingDensityBudget
namespace OAI

section

namespace Erdos3.LocalConvolution

theorem exists_moment_separation {alpha threshold epsilon : ℝ}
    (halpha : 0 < alpha) (hthreshold : 0 ≤ threshold) (hgap : threshold < alpha)
    (hepsilon : 0 < epsilon) :
    ∃ q₀ : ℕ, ∀ q ≥ q₀, threshold ^ q ≤ epsilon / 2 * alpha ^ q := by
  have hr0 : 0 ≤ threshold / alpha := div_nonneg hthreshold halpha.le
  have hr1 : threshold / alpha < 1 := (div_lt_one halpha).mpr hgap
  obtain ⟨q₀, hq₀⟩ := exists_pow_lt_of_lt_one (show 0 < epsilon / 2 by positivity) hr1
  refine ⟨q₀, ?_⟩
  intro q hq
  have h : (threshold / alpha) ^ q ≤ epsilon / 2 :=
    (pow_le_pow_of_le_one hr0 hr1.le hq).trans hq₀.le
  rw [div_pow] at h
  exact (div_le_iff₀ (pow_pos halpha q)).mp h

end Erdos3.LocalConvolution

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MatchedFlatDecay
namespace OAI

section

namespace Erdos3

theorem flatComparisonDelta_spec {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < flatComparisonDelta epsilon ∧ flatComparisonDelta epsilon ≤ 1 / 4 ∧
      1 + 2 * flatComparisonDelta epsilon ≤
        (1 + epsilon) * (1 - 2 * flatComparisonDelta epsilon) := by
  have hden : 0 < 4 * (2 + epsilon) := by positivity
  have hprod : flatComparisonDelta epsilon * (4 * (2 + epsilon)) = epsilon :=
    div_mul_cancel₀ _ hden.ne'
  refine ⟨div_pos hepsilon hden, ?_, ?_⟩
  · unfold flatComparisonDelta
    apply (div_le_iff₀ hden).mpr
    linarith
  · nlinarith

theorem exists_flat_moment_slope {A B D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ p : ℝ, 1 ≤ p → ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ C * p ∧
      (A + B + D + Real.log 3) * p ≤ ((2 * m : ℕ) : ℝ) * Real.log 2 := by
  let R : ℝ := (A + B + D + Real.log 3) / (2 * Real.log 2)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hR : 0 ≤ R := div_nonneg (by positivity) (by positivity)
  have hRprod : R * (2 * Real.log 2) = A + B + D + Real.log 3 :=
    div_mul_cancel₀ _ (by positivity)
  refine ⟨R + 2, by linarith, ?_⟩
  intro p hp
  let m : ℕ := ⌈(R + 1) * p⌉₊
  have hp0 : 0 ≤ p := by linarith
  have hlow : (R + 1) * p ≤ (m : ℝ) := Nat.le_ceil _
  have hhigh : (m : ℝ) < (R + 1) * p + 1 := Nat.ceil_lt_add_one (by positivity)
  have hmreal : 0 < (m : ℝ) := by nlinarith [mul_nonneg hR hp0]
  have hm : 0 < m := by exact_mod_cast hmreal
  refine ⟨m, hm, by nlinarith, ?_⟩
  have hmul := mul_le_mul_of_nonneg_right hlow (show 0 ≤ 2 * Real.log 2 by positivity)
  have heq : (R + 1) * p * (2 * Real.log 2) =
      (A + B + D + Real.log 3) * p + p * (2 * Real.log 2) := by
    calc
      _ = R * (2 * Real.log 2) * p + p * (2 * Real.log 2) := by ring
      _ = _ := by rw [hRprod]
  rw [heq] at hmul
  push_cast
  nlinarith [mul_nonneg hp0 hlog2.le]

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.LocalConvolution

theorem exists_unbalanced_moment_threshold {c : ℝ} (hc : 0 < c) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m ≥ m₀, ∀ m' ≥ m,
      (1 + c / 4) ^ (2 * m') ≤ (c / 64) / 2 * (1 + c / 2) ^ (2 * m') := by
  obtain ⟨q₀, hq₀⟩ := exists_moment_separation
    (show 0 < 1 + c / 2 by linarith) (show 0 ≤ 1 + c / 4 by linarith)
    (show 1 + c / 4 < 1 + c / 2 by linarith) (show 0 < c / 64 by positivity)
  refine ⟨q₀ + 1, by omega, ?_⟩
  intro m hm m' hm'
  exact hq₀ (2 * m') (by omega)

end Erdos3.LocalConvolution

end

section

namespace Erdos3

theorem exists_joint_moment_orders {A B D c : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hD : 0 ≤ D) (hc : 0 < c) (R : ℕ) (hR : 0 < R) :
    ∃ C H : ℝ, 1 ≤ C ∧ 0 ≤ H ∧ ∀ p : ℝ, 1 ≤ p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ C * p ∧
        (A + B + D + Real.log 3) * p ≤ ((2 * m : ℕ) : ℝ) * Real.log 2 ∧
        ∀ m' : ℕ, m ≤ m' → m' ≤ R * m →
          ((2 * m' : ℕ) : ℝ) ≤ H * p ∧
          (1 + c / 4) ^ (2 * m') ≤ (c / 64) / 2 * (1 + c / 2) ^ (2 * m') := by
  obtain ⟨C₀, hC₀, hflat⟩ := exists_flat_moment_slope hA hB hD
  obtain ⟨m₀, _, hsep⟩ := LocalConvolution.exists_unbalanced_moment_threshold hc
  let C := C₀ + (m₀ : ℝ)
  let H := 2 * (R : ℝ) * C
  have hC : 1 ≤ C := by
    dsimp [C]
    have hm₀ : (0 : ℝ) ≤ m₀ := Nat.cast_nonneg m₀
    linarith
  have hH : 0 ≤ H := by dsimp [H]; positivity
  refine ⟨C, H, hC, hH, ?_⟩
  intro p hp
  obtain ⟨m₁, hm₁, hm₁C, horder⟩ := hflat p hp
  let m := m₁ + m₀
  have hm : 0 < m := by dsimp [m]; omega
  have hmC : (m : ℝ) ≤ C * p := by
    have hmul := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg m₀ : (0 : ℝ) ≤ m₀)
    dsimp [m, C]
    push_cast
    nlinarith
  refine ⟨m, hm, hmC, ?_, ?_⟩
  · apply horder.trans
    apply mul_le_mul_of_nonneg_right _ (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
    exact_mod_cast (show 2 * m₁ ≤ 2 * m by dsimp [m]; omega)
  · intro m' hmm' hm'R
    refine ⟨?_, hsep m (by dsimp [m]; omega) m' hmm'⟩
    have hm'Rreal : (m' : ℝ) ≤ (R : ℝ) * m := by exact_mod_cast hm'R
    have hmul := mul_le_mul_of_nonneg_left hmC (Nat.cast_nonneg R : (0 : ℝ) ≤ R)
    dsimp [H]
    push_cast
    nlinarith

end Erdos3

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.UnbalancedWidthBudget
namespace OAI

section

namespace Erdos3.LocalConvolution

open CyclicCrootSisask

theorem unbalancedErrorBudget_spec {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    0 ≤ unbalancedErrorBudget c ∧ Real.exp (-unbalancedErrorBudget c) / 2 = c / 64 := by
  constructor
  · unfold unbalancedErrorBudget
    apply neg_nonneg.mpr
    exact Real.log_nonpos (by positivity) (by linarith)
  · unfold unbalancedErrorBudget
    rw [neg_neg, Real.exp_log (by positivity)]
    ring

end Erdos3.LocalConvolution

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ParentControlledMatching
namespace OAI

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

theorem matchingWidthLoss_outer (rank : ℕ) (P A E T delta c : ℝ) :
    matchingWidthLoss rank P (outerMatchingScaleLoss rank A E T) delta c =
      2 * T + 3 * rank + 2 * A + 2 * E + 2 * P +
        localMomentErrorBudget delta + unbalancedErrorBudget c + 4820 := by
  unfold matchingWidthLoss coordinatedMatchingScaleLoss outerMatchingScaleLoss
  ring

variable {N : ℕ} [NeZero N]

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.UnbalancedPolynomialBudget
namespace OAI

section

namespace Erdos3.LocalConvolution

open CyclicCrootSisask

theorem unbalancedRankExtra_le {c p H : ℝ} (hc : 0 < c) :
    (unbalancedRankExtra c p H : ℝ) ≤
      almostPeriodicityWidthConstant (c / 64) * (1 + (3 * H + 1) * p ^ 2) ^ 4 + 1 := by
  have hK := (almostPeriodicityWidthConstant_pos (show 0 < c / 64 by positivity)).le
  unfold unbalancedRankExtra
  exact (Nat.ceil_lt_add_one (by positivity)).le

theorem unbalancedWidthLoss_nonneg (rank : ℕ) {c p H : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hp : 0 ≤ p) (hH : 0 ≤ H) :
    0 ≤ unbalancedWidthLoss rank c p H := by
  have hK := (almostPeriodicityWidthConstant_pos (show 0 < c / 64 by positivity)).le
  have hE := (unbalancedErrorBudget_spec hc hc1).1
  have hlog : 0 ≤ Real.log (2 + (rank : ℝ)) :=
    Real.log_nonneg (by have hr : (0 : ℝ) ≤ (rank : ℝ) := Nat.cast_nonneg rank; linarith)
  unfold unbalancedWidthLoss
  positivity

theorem unbalancedWidthLoss_le_polynomial (rank : ℕ) {c p H : ℝ} (hc : 0 < c) :
    unbalancedWidthLoss rank c p H ≤
      2 * (rank : ℝ) +
        almostPeriodicityWidthConstant (c / 64) * (1 + (3 * H + 1) * p ^ 2) ^ 4 +
        2 * H * p ^ 2 + 2 * p + 2 * unbalancedErrorBudget c + 3209 +
        almostPeriodicityWidthConstant (c / 64) * (3 + (3 * H + 1) * p ^ 2 + rank) := by
  have hK := (almostPeriodicityWidthConstant_pos (show 0 < c / 64 by positivity)).le
  have hR := unbalancedRankExtra_le (p := p) (H := H) hc
  have hlog : Real.log (2 + (rank : ℝ)) ≤ (rank : ℝ) + 2 := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 + (rank : ℝ))
    linarith
  have hmul := mul_le_mul_of_nonneg_left hlog hK
  unfold unbalancedWidthLoss
  push_cast
  nlinarith

end Erdos3.LocalConvolution

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearParameterBudget
namespace OAI

section

namespace Erdos3

theorem exists_natPolynomial_affine_budget (P : Polynomial ℕ) (A : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      P.eval₂ (Nat.castRingHom ℝ) ((A : ℝ) * (p + 1)) ≤ (p + 2) ^ C := by
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget
    (P.comp (Polynomial.C A * (Polynomial.X + 1)))
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [Polynomial.eval₂_comp] using hbound p hp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} [Fintype σ] {w : σ → ℕ}

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial Module
open scoped NNReal TensorProduct

variable {σ : Type*} [Fintype σ] (w : σ → ℕ)

variable [Fintype (PolynomialShearIndex w)]

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {σ : Type*} [Fintype σ] (w : σ → ℕ) [Fintype (PolynomialShearIndex w)]
  [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]
  [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped NNReal

namespace PolynomialSlots

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s d : ℕ}

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3.PolynomialPatch

open NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {σ : Type*} {s d : ℕ} (A : PolynomialPatch σ s d)
  [Fintype (PolynomialShearIndex A.weight)]

variable [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
  [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]

end Erdos3.PolynomialPatch

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.IdealInvariantNiltestBudget
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

end RationalFilteredNilmanifold.Niltest

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d n : ℕ}
  (D : RationalFilteredNilmanifold L s d) (I : LieIdeal ℚ L)
  (hI : D.filtration.layer (t + 1) ≤ I.toSubmodule)
  (Q : RationalFilteredNilmanifold (L ⧸ I) t n)
  (hQF : Q.filtration = D.filtration.quotientLie I hI)

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ I))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ I))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ I))] [T2Space (ℝ ⊗[ℚ] (L ⧸ I))]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

variable {σ K Ξ : Type*} [LieRing K] [LieAlgebra ℚ K] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)]
  (D : RationalFilteredNilmanifold K s d) {w : σ → ℕ}

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem cyclicNiltestShiftBound_zero_of_constants.{u} {N : ℕ} [NeZero N]
    (a J : ZMod N → ℝ) (E : Finset (ZMod N)) {p error : ℝ}
    (hbound : ∀ h ∉ E, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → realShiftCorrelation a J h * t ≤ error) :
    CyclicNiltestShiftBound.{u} 0 N p error a J E := by
  intro h hh L _ _ s dim _ _ _ _ D hs T hT _
  have hs0 : s = 0 := by omega
  subst s
  let t := (T.observable (QuotientGroup.mk (1 : D.RealGroup))).re
  have ht : 0 ≤ t ∧ t ≤ 1 := (hT _).2
  have heval (x : ZMod N) : (T.evalCyclic N (fun _ => x)).re = t := by
    exact congrArg Complex.re (RationalFilteredNilmanifold.Niltest.eval_step_zero D T _)
  simp_rw [heval]
  rw [← Finset.expect_mul]
  exact hbound h hh t ht.1 ht.2

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  (T : D.Niltest w) (hT : T.UnitIntervalValued)
  (psi : D.Space → ℝ) (hpsi : ∀ z, 0 ≤ psi z ∧ psi z ≤ 1)
  (K : ℝ≥0) (hLip : letI := D.metricSpace; LipschitzWith K psi)

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RefinementEnlargement
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

theorem exists_refinement_moment_orders {D : ℝ} (hD : 0 ≤ D) :
    ∃ C H : ℝ, 1 ≤ C ∧ 0 ≤ H ∧ ∀ p : ℝ, 1 ≤ p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ C * p ∧
        (1 + 1 + (D + 1) + Real.log 3) * p ≤ ((2 * m : ℕ) : ℝ) * Real.log 2 ∧
        ∀ m' : ℕ, m ≤ m' → m' ≤ localMomentExponentFactor δ * m →
          ((2 * m' : ℕ) : ℝ) ≤ H * p ∧
          (1 + γ / 4) ^ (2 * m') ≤ (γ / 64) / 2 * (1 + γ / 2) ^ (2 * m') := by
  exact exists_joint_moment_orders (by norm_num) (by norm_num) (by linarith)
    (localMomentGain_pos δ) (localMomentExponentFactor δ) (localMomentExponentFactor_pos δ)

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

theorem admissible_child_bound_of_bounded_shapes
    (B₀ : CyclicBohr.Set N) {scale : ℝ≥0} {extra : ℕ} {minimumWidth T : ℝ}
    {a : ZMod N → ℝ} (hminimumWidth : 0 < minimumWidth)
    (hminimumWidth1 : minimumWidth ≤ 1) (hrank : 1 ≤ B₀.rank + extra)
    (hbounded : ∀ C : CyclicBohr.Set N, C.IsRankRegular → 0 < C.radius →
      1 ≤ C.rank → C.rank ≤ B₀.rank + extra → minimumWidth ≤ C.radius → C.radius ≤ 2 →
      CellBilinearBound C.carrier a T) :
    ∀ C, Peeling.admissibleBohrShape B₀ scale extra minimumWidth C →
      CellBilinearBound C.carrier a T := by
  intro C hC
  obtain ⟨hCreg, _, hCrank, hCwidth⟩ := hC
  obtain ⟨C', hcarrier, hreg, hpos, hrank1, hrankMax, hwidthMin, hwidthMax⟩ :=
    CyclicBohr.Set.exists_bounded_presentation C hCreg (hminimumWidth.trans_le hCwidth)
      hrank hCrank hminimumWidth1 hCwidth
  rw [← hcarrier]
  exact hbounded C' hreg hpos hrank1 hrankMax hwidthMin hwidthMax

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution

theorem fixed_refinement_thresholds :
    2 ≤ (1 / 4 : ℝ) * (16 : ℝ) ^ (3 / 4 : ℝ) ∧
      ((1 / 256 : ℝ) * 16) ^ (1 / 4 : ℝ) ≤ 1 / 2 := by
  have hK := Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2) 4 (3 / 4 : ℝ)
  have hc := Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1 / 2) 4 (1 / 4 : ℝ)
  norm_num at hK hc ⊢

theorem refinementContraction_eq (epsilon : ℝ) :
    refinementContraction epsilon =
      (1 + (1 - localMomentGain (flatComparisonDelta epsilon) /
        (128 * (1 + Real.sqrt ((16 : ℝ) / (1 / 256))) ^ 2))) / 2 := by
  norm_num [refinementContraction]
  ring

theorem refinementContraction_bounds (epsilon : ℝ) :
    0 ≤ refinementContraction epsilon ∧ refinementContraction epsilon < 1 := by
  have hc := localMomentGain_pos (flatComparisonDelta epsilon)
  have hc1 := localMomentGain_le_half (flatComparisonDelta epsilon)
  unfold refinementContraction
  constructor <;> linarith

theorem refinement_cap_cutoff {p : ℝ} (hp : 512 ≤ p) :
    1 ≤ Real.exp p * ((1 / 256 : ℝ) * Real.exp (-p / 2)) := by
  have h : 256 ≤ Real.exp (p / 2) := by
    linarith [Real.add_one_le_exp (p / 2)]
  calc
    1 ≤ Real.exp (p / 2) / 256 := by linarith
    _ = _ := by
      rw [mul_left_comm, ← Real.exp_add]
      ring_nf

theorem refinement_tiny_cutoff {p W : ℝ} (hW : W ≤ Real.exp (p / 8)) :
    W * (Real.exp (-p / 2)) ^ (3 / 4 : ℝ) ≤ Real.exp (-((1 / 4 : ℝ) * p)) := by
  calc
    _ ≤ Real.exp (p / 8) * (Real.exp (-p / 2)) ^ (3 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_right hW (Real.rpow_nonneg (Real.exp_nonneg _) _)
    _ = _ := by
      rw [← Real.exp_mul, ← Real.exp_add]
      congr 1
      ring

theorem refinement_return_error {p : ℝ} (hp : 0 ≤ p) :
    (Real.exp (-(2 * p)) + Real.exp (-(2 * p))) / (Real.exp (-p / 2)) ^ 2 ≤
      2 * Real.exp (-p / 4) := by
  have heq : (Real.exp (-(2 * p)) + Real.exp (-(2 * p))) / (Real.exp (-p / 2)) ^ 2 =
      2 * Real.exp (-p) := by
    rw [← Real.exp_nat_mul]
    rw [show Real.exp (-(2 * p)) + Real.exp (-(2 * p)) = 2 * Real.exp (-(2 * p)) by ring]
    rw [mul_div_assoc, ← Real.exp_sub]
    congr 2
    norm_num
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)

theorem refinement_peeling_error {p loss : ℝ} (hp : 0 ≤ p)
    (hloss : loss ≤ Real.exp (-(3 * p))) :
    2 * loss / (16 * (Real.exp (-p / 2)) ^ 3) ≤ Real.exp (-p / 4) := by
  calc
    _ ≤ 2 * Real.exp (-(3 * p)) / (16 * (Real.exp (-p / 2)) ^ 3) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hloss (by norm_num))
        (by positivity)
    _ = Real.exp (-(3 * p / 2)) / 8 := by
      rw [← Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      rw [show 2 * Real.exp (-(3 * p)) / (16 * Real.exp (3 * (-p / 2))) =
        (Real.exp (-(3 * p)) / Real.exp (3 * (-p / 2))) / 8 by ring]
      rw [← Real.exp_sub]
      congr 2
      ring
    _ ≤ Real.exp (-(3 * p / 2)) := by nlinarith [Real.exp_pos (-(3 * p / 2))]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem refinement_total_error {p loss : ℝ} (hp : 0 ≤ p)
    (hloss : loss ≤ Real.exp (-(3 * p))) :
    Real.exp (-((1 / 4 : ℝ) * p)) +
      (Real.exp (-(2 * p)) + Real.exp (-(2 * p))) / (Real.exp (-p / 2)) ^ 2 +
      2 * loss / (16 * (Real.exp (-p / 2)) ^ 3) ≤ 4 * Real.exp (-p / 4) := by
  have hreturn := refinement_return_error hp
  have hpeeling := refinement_peeling_error hp hloss
  rw [show -((1 / 4 : ℝ) * p) = -p / 4 by ring]
  linarith

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

theorem refinement_enlargement_bounds {p : ℝ} (hp : 0 ≤ p) {A : ℕ} (hA : 512 ≤ A) :
    512 ≤ (A : ℝ) * (p + 1) ∧ p ≤ (A : ℝ) * (p + 1) ∧
      (A : ℝ) ≤ (A : ℝ) * (p + 1) := by
  have hAR : (512 : ℝ) ≤ A := by exact_mod_cast hA
  have hm := mul_le_mul_of_nonneg_right hAR (by linarith : 0 ≤ p + 1)
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg _
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem refinement_enlargement_amplitude {p : ℝ} (hp : 0 ≤ p) {A : ℕ} (hA : 40 ≤ A) :
    2 * Real.exp p ≤ Real.exp (((A : ℝ) * (p + 1)) / 8) := by
  have hAR : (40 : ℝ) ≤ A := by exact_mod_cast hA
  have hm := mul_le_mul_of_nonneg_right hAR (by linarith : 0 ≤ p + 1)
  calc
    _ ≤ Real.exp 1 * Real.exp p := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_nonneg _)
    _ = Real.exp (1 + p) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

theorem refinement_enlargement_error {p : ℝ} (hp : 0 ≤ p) {A : ℕ} (hA : 40 ≤ A) :
    2 * Real.exp (-((A : ℝ) * (p + 1)) / 8) ≤ Real.exp (-4 * p) := by
  have hAR : (40 : ℝ) ≤ A := by exact_mod_cast hA
  have hm := mul_le_mul_of_nonneg_right hAR (by linarith : 0 ≤ p + 1)
  calc
    _ ≤ Real.exp 1 * Real.exp (-((A : ℝ) * (p + 1)) / 8) := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_nonneg _)
    _ = Real.exp (1 + -((A : ℝ) * (p + 1)) / 8) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

theorem signed_comparison_amplitude {a b p epsilon : ℝ}
    (ha : 0 ≤ a ∧ a ≤ Real.exp p) (hb : 0 ≤ b ∧ b ≤ Real.exp p)
    (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) :
    |a - (1 + epsilon) * b| ≤ 2 * Real.exp p := by
  have hlo := mul_nonneg (show 0 ≤ 1 + epsilon by linarith) hb.1
  have hhi := mul_le_mul_of_nonneg_right (show 1 + epsilon ≤ 2 by linarith) hb.1
  exact abs_le.mpr ⟨by nlinarith, by nlinarith [Real.exp_pos p]⟩

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FixedRefinementBudget
namespace OAI

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped NNReal

theorem refinementMatchingLoss_eq (rank : ℕ) (p epsilon : ℝ) :
    matchingWidthLoss rank p (outerMatchingScaleLoss rank (p / 8) (2 * p)
      (refinementScaleLoss rank p)) (flatComparisonDelta epsilon)
        (localMomentGain (flatComparisonDelta epsilon)) = refinementMatchingLoss rank p epsilon := by
  rw [matchingWidthLoss_outer]
  unfold refinementScaleLoss refinementMatchingLoss
  ring

theorem refinementRoundLoss_eq (rank : ℕ) (p H epsilon : ℝ) :
    refinementMatchingWidthLoss rank p H (p / 8) (2 * p) (2 * p)
      (refinementScaleLoss rank p) (flatComparisonDelta epsilon) =
        refinementRoundLoss rank p H epsilon := by
  unfold refinementMatchingWidthLoss refinementRoundLoss
  rw [refinementMatchingLoss_eq]

theorem refinementMatchingLoss_nonneg (rank : ℕ) {p epsilon : ℝ}
    (hp : 0 ≤ p) (hepsilon : 0 < epsilon) : 0 ≤ refinementMatchingLoss rank p epsilon := by
  have hdelta := (flatComparisonDelta_spec hepsilon).1
  have hc := localMomentGain_pos (flatComparisonDelta epsilon)
  have hc1 := (localMomentGain_le_half (flatComparisonDelta epsilon)).trans (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hEd := (localMomentErrorBudget_spec hdelta).1
  have hEc := (unbalancedErrorBudget_spec hc hc1).1
  unfold refinementMatchingLoss
  positivity

theorem two_le_refinementRoundLoss (rank : ℕ) {p H epsilon : ℝ}
    (hp : 0 ≤ p) (hH : 0 ≤ H) (hepsilon : 0 < epsilon) :
    2 ≤ refinementRoundLoss rank p H epsilon := by
  have hm := refinementMatchingLoss_nonneg rank hp hepsilon
  have hc := localMomentGain_pos (flatComparisonDelta epsilon)
  have hc1 := (localMomentGain_le_half (flatComparisonDelta epsilon)).trans (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hu := unbalancedWidthLoss_nonneg rank hc hc1 hp hH
  have hrank : (0 : ℝ) ≤ rank := Nat.cast_nonneg rank
  unfold refinementRoundLoss unbalancedReturnWidthLoss
  linarith

theorem refinementMatchingLoss_mono_rank {r d : ℕ} (hrd : r ≤ d) (p epsilon : ℝ) :
    refinementMatchingLoss r p epsilon ≤ refinementMatchingLoss d p epsilon := by
  have hrdR : (r : ℝ) ≤ d := by exact_mod_cast hrd
  unfold refinementMatchingLoss
  linarith

theorem refinementRoundLoss_mono_rank {r d : ℕ} (hrd : r ≤ d) (p H epsilon : ℝ) :
    refinementRoundLoss r p H epsilon ≤ refinementRoundLoss d p H epsilon := by
  have hrdR : (r : ℝ) ≤ d := by exact_mod_cast hrd
  have hm := refinementMatchingLoss_mono_rank hrd p epsilon
  have hc := localMomentGain_pos (flatComparisonDelta epsilon)
  have hK := CyclicCrootSisask.almostPeriodicityWidthConstant_pos (show 0 <
    localMomentGain (flatComparisonDelta epsilon) / 64 by positivity)
  have hlog : Real.log (2 + (r : ℝ)) ≤ Real.log (2 + (d : ℝ)) :=
    Real.log_le_log (by positivity) (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hlog hK.le
  unfold refinementRoundLoss unbalancedReturnWidthLoss unbalancedWidthLoss
  push_cast
  nlinarith

theorem fixed_refinement_scale_spec (rank : ℕ) {p W : ℝ} (hp : 0 ≤ p)
    (hW : 0 ≤ W) (hWcap : W ≤ Real.exp (p / 8)) :
    let scale := localizedAverageScale rank W (Real.exp (-(3 * p)))
    0 < scale ∧ scale ≤ 1 / (100 * (2 * max rank 1 : ℕ) : ℝ≥0) ∧
      W * (400 * (max rank 1 : ℕ) * (scale : ℝ)) ≤ Real.exp (-(3 * p)) ∧
      Real.exp (-refinementScaleLoss rank p) ≤ (scale : ℝ) := by
  intro scale
  obtain ⟨hs, hlim, herr⟩ := localizedAverageScale_spec rank hW (Real.exp_pos (-(3 * p)))
  refine ⟨hs, hlim, herr, ?_⟩
  exact localizedAverageScale_exp_lower_of_error rank hW hWcap (by positivity) (by positivity)
    (by nlinarith [Real.exp_pos (-(3 * p))])

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FixedBilinearRefinement
namespace OAI

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

theorem fixed_bilinear_refinement_step
    (B₀ : CyclicBohr.Set N) (hB₀ : B₀.IsRankRegular)
    (hBpos : 0 < B₀.radius) (hBwidth : B₀.radius ≤ 2) (hBrank : 1 ≤ B₀.rank)
    {p R H P W : ℝ} (hepsilon : 0 < epsilon) (hp : 512 ≤ p) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hBwide : Real.exp (-R) ≤ B₀.radius)
    (A B : ZMod N → ℝ)
    (hA : ∀ r, 0 ≤ A r ∧ A r ≤ Real.exp p) (hB : ∀ r, 0 ≤ B r ∧ B r ≤ Real.exp p)
    (hW : 0 ≤ W) (hWcap : W ≤ Real.exp (p / 8))
    (ha : ∀ r, |A r - (1 + epsilon) * B r| ≤ W)
    (hcompare : CyclicNiltestUpperComparison.{0} 1 N P (Real.exp (-P)) A B)
    (hbudget : refinementComparisonBudget B₀.rank p R epsilon ≤ P)
    (m : ℕ) (hm : 0 < m)
    (horder : (1 + 1 + ((1 / 4 : ℝ) + 1) + Real.log 3) * p ≤
      ((2 * m : ℕ) : ℝ) * Real.log 2)
    (horders : ∀ m' : ℕ, m ≤ m' → m' ≤ localMomentExponentFactor δ * m →
      ((2 * m' : ℕ) : ℝ) ≤ H * p ∧
      (1 + γ / 4) ^ (2 * m') ≤ (γ / 64) / 2 * (1 + γ / 2) ^ (2 * m'))
    {T : ℝ} (hT : 0 ≤ T)
    (hchildren : ∀ C : CyclicBohr.Set N, C.IsRankRegular → 0 < C.radius →
      1 ≤ C.rank → C.rank ≤ B₀.rank + unbalancedRankExtra γ p H →
      Real.exp (-(R + refinementRoundLoss B₀.rank p H epsilon)) ≤ C.radius → C.radius ≤ 2 →
      CellBilinearBound C.carrier (fun r => A r - (1 + epsilon) * B r) T) :
    CellBilinearBound B₀.carrier (fun r => A r - (1 + epsilon) * B r)
      (refinementContraction epsilon * T + 4 * Real.exp (-p / 4)) := by
  have hp0 : 0 ≤ p := by linarith
  have hp1 : 1 ≤ p := by linarith
  let scale := localizedAverageScale B₀.rank W (Real.exp (-(3 * p)))
  obtain ⟨_, hscale, hscaleError, hscaleLog⟩ := fixed_refinement_scale_spec B₀.rank hp0 hW hWcap
  have hscaleLoss : 0 ≤ refinementScaleLoss B₀.rank p := by
    unfold refinementScaleLoss
    positivity
  obtain ⟨hRD, L, S, hLfreq, hSfreq, hLreg, hSreg, hLpos, hSpos, hSLwidth, hSwidth,
      hSrank, hLshape, hSB, hrank, hwidth, hSwide, hSL, hmoment, hkappa, herror, hmatching⟩ :=
    exists_refinement_matching_geometry B₀ hBpos hB₀ hBwidth hBrank
      (E := 2 * p) (J := 2 * p) (M := Real.exp p) (p := p) (R := R)
      (T := refinementScaleLoss B₀.rank p) hW hWcap (by positivity) (by positivity)
      (Real.exp_nonneg p) le_rfl hp1 hH (by positivity) hscaleLoss hR
      (flatComparisonDelta_spec hepsilon).1 hBwide hscaleLog
  simp only [refinementMatchingLoss_eq, refinementRoundLoss_eq] at hRD hLshape hwidth hSwide
  have hSrankEq : S.rank = B₀.rank := congrArg Finset.card (hSfreq.trans hLfreq)
  let w := B₀.radius * Real.exp (-refinementRoundLoss B₀.rank p H epsilon)
  have hwpos : 0 < w := mul_pos hBpos (Real.exp_pos _)
  have hround := two_le_refinementRoundLoss B₀.rank hp0 hH hepsilon
  have hexp : Real.exp (-refinementRoundLoss B₀.rank p H epsilon) ≤ 1 / 2 := by
    calc
      _ ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ _ := by
        rw [Real.exp_neg]
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num)
          (show (2 : ℝ) ≤ Real.exp 2 by linarith [Real.add_one_le_exp 2])
  have hw1 : w ≤ 1 := by
    have h := mul_le_mul hBwidth hexp (Real.exp_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    dsimp only [w]
    linarith
  have hwlower : Real.exp (-(R + refinementRoundLoss B₀.rank p H epsilon)) ≤ w := by
    rw [neg_add, Real.exp_add]
    exact mul_le_mul_of_nonneg_right hBwide (Real.exp_nonneg _)
  have hchild : ∀ C, Peeling.admissibleBohrShape B₀ scale (unbalancedRankExtra γ p H) w C →
      CellBilinearBound C.carrier (fun r => A r - (1 + epsilon) * B r) T := by
    apply admissible_child_bound_of_bounded_shapes B₀ hwpos hw1 (by omega)
    intro C hCreg hCpos hCrank hCsize hCwidth hCwide
    exact hchildren C hCreg hCpos hCrank hCsize (hwlower.trans hCwidth) hCwide
  have hbud := max_le_iff.mp hbudget
  have hcomplexity : 2 * (S.rank : ℝ) + p + ((1 / 4 : ℝ) + 2) * p +
      (R + refinementMatchingLoss B₀.rank p epsilon) + 1612 ≤ P := by
    simpa only [hSrankEq] using hbud.1
  have hprecision : ((1 / 4 : ℝ) + 2) * p + 2 + (S.rank : ℝ) *
      (R + refinementMatchingLoss B₀.rank p epsilon + 10) ≤ P := by
    simpa only [hSrankEq] using hbud.2
  have h := normalized_bilinear_refinement_step B₀ L S hB₀ hLreg hSpos hSwidth hSreg hSrank
    hSfreq hSLwidth hepsilon hp1 (by norm_num : (0 : ℝ) ≤ 1 / 4) hRD hH
    hSL hkappa hscale hSB hrank hwidth hLshape A B hA hB
    (by norm_num : (0 : ℝ) < 1 / 256) (by norm_num : (0 : ℝ) < 16)
    (Real.exp_pos (-p / 2)) fixed_refinement_thresholds.1 fixed_refinement_thresholds.2
    (Real.exp_pos p) le_rfl (refinement_cap_cutoff hp) (refinement_tiny_cutoff hWcap)
    hmoment herror hSwide hcomplexity hprecision hcompare hW hWcap (by positivity) (by positivity) ha
    (fun origin f g hf hg => hmatching (fun r => A (origin + r) - (1 + epsilon) * B (origin + r))
      f g (fun r => ha (origin + r)) hf hg) m hm horder horders hT hchild
  apply h.mono
  have herr := refinement_total_error hp0 hscaleError
  rw [← refinementContraction_eq]
  nlinarith only [herr]

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.QuantitativeBohrBound
namespace OAI

section

namespace Erdos3.CellRefinement

open LocalConvolution

theorem refinementComparisonBudget_mono {r d : ℕ} {p R R' epsilon : ℝ}
    (hrd : r ≤ d) (hp : 0 ≤ p) (hR : 0 ≤ R) (hRR' : R ≤ R')
    (hepsilon : 0 < epsilon) :
    refinementComparisonBudget r p R epsilon ≤ refinementComparisonBudget d p R' epsilon := by
  have hr : (r : ℝ) ≤ d := by exact_mod_cast hrd
  have hm := refinementMatchingLoss_mono_rank hrd p epsilon
  have hm0 := refinementMatchingLoss_nonneg r hp hepsilon
  have hi : R + refinementMatchingLoss r p epsilon + 10 ≤
      R' + refinementMatchingLoss d p epsilon + 10 := by linarith
  have hprod := mul_le_mul hr hi (by positivity : 0 ≤ R + refinementMatchingLoss r p epsilon + 10)
    (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  unfold refinementComparisonBudget
  apply max_le_max <;> linarith

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

theorem bohr_refinement_iteration
    (B₀ : CyclicBohr.Set N) (hB₀ : B₀.IsRankRegular)
    (hBpos : 0 < B₀.radius) (hBwidth : B₀.radius ≤ 2) (hBrank : 1 ≤ B₀.rank)
    {p R H P W : ℝ} (hepsilon : 0 < epsilon) (hp : 512 ≤ p) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hBwide : Real.exp (-R) ≤ B₀.radius) (n : ℕ)
    (A B : ZMod N → ℝ)
    (hA : ∀ r, 0 ≤ A r ∧ A r ≤ Real.exp p) (hB : ∀ r, 0 ≤ B r ∧ B r ≤ Real.exp p)
    (hW : 0 ≤ W) (hWcap : W ≤ Real.exp (p / 8))
    (ha : ∀ r, |A r - (1 + epsilon) * B r| ≤ W)
    (hcompare : CyclicNiltestUpperComparison.{0} 1 N P (Real.exp (-P)) A B)
    (m : ℕ) (hm : 0 < m)
    (horder : (1 + 1 + ((1 / 4 : ℝ) + 1) + Real.log 3) * p ≤
      ((2 * m : ℕ) : ℝ) * Real.log 2)
    (horders : ∀ m' : ℕ, m ≤ m' → m' ≤ localMomentExponentFactor δ * m →
      ((2 * m' : ℕ) : ℝ) ≤ H * p ∧
      (1 + γ / 4) ^ (2 * m') ≤ (γ / 64) / 2 * (1 + γ / 2) ^ (2 * m'))
    (hbudget : let d := B₀.rank + n * unbalancedRankExtra γ p H
      let loss := refinementRoundLoss d p H epsilon
      refinementComparisonBudget d p (R + n * loss) epsilon ≤ P) :
    CellBilinearBound B₀.carrier (fun r => A r - (1 + epsilon) * B r)
      ((refinementContraction epsilon) ^ n * W +
        (4 * Real.exp (-p / 4)) / (1 - refinementContraction epsilon)) := by
  let extra := unbalancedRankExtra γ p H
  let d := B₀.rank + n * extra
  let loss := refinementRoundLoss d p H epsilon
  let family : ℕ → CyclicBohr.Set N → Prop := fun j C =>
    C.IsRankRegular ∧ 0 < C.radius ∧ C.radius ≤ 2 ∧ 1 ≤ C.rank ∧
      C.rank ≤ B₀.rank + j * extra ∧ Real.exp (-(R + (j : ℝ) * loss)) ≤ C.radius
  have hp0 : 0 ≤ p := by linarith
  have hloss : 0 ≤ loss := (by linarith : (0 : ℝ) ≤ 2).trans
    (two_le_refinementRoundLoss d hp0 hH hepsilon)
  have hroot : family 0 B₀ := by
    refine ⟨hB₀, hBpos, hBwidth, hBrank, ?_, ?_⟩
    · simp
    · simpa only [Nat.cast_zero, zero_mul, add_zero] using hBwide
  apply finite_cell_refinement CyclicBohr.Set.carrier family
    (fun r => A r - (1 + epsilon) * B r) n hW
    (refinementContraction_bounds epsilon).1 (refinementContraction_bounds epsilon).2
    (by positivity) (fun r => (le_abs_self _).trans (ha r))
    (fun _ C _ => C.carrier_nonempty) ?_ B₀ hroot
  intro j hj T hT hchildren C hC
  obtain ⟨hCreg, hCpos, hCwidth, hCrank, hCsize, hCwide⟩ := hC
  have hjn : j ≤ n := Nat.le_of_lt hj
  have hjnR : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hjn
  have hCtotal : C.rank ≤ d := hCsize.trans (Nat.add_le_add_left (Nat.mul_le_mul_right extra hjn) _)
  have hCround : refinementRoundLoss C.rank p H epsilon ≤ loss :=
    refinementRoundLoss_mono_rank hCtotal p H epsilon
  have hRj : 0 ≤ R + (j : ℝ) * loss := by positivity
  have hRjn : R + (j : ℝ) * loss ≤ R + (n : ℝ) * loss := by
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hjnR hloss)
  have hCbudget : refinementComparisonBudget C.rank p (R + (j : ℝ) * loss) epsilon ≤ P :=
    (refinementComparisonBudget_mono hCtotal hp0 hRj hRjn hepsilon).trans hbudget
  apply fixed_bilinear_refinement_step C hCreg hCpos hCwidth hCrank hepsilon hp hRj hH hCwide
    A B hA hB hW hWcap ha hcompare hCbudget m hm horder horders hT
  intro D hDreg hDpos hDrank hDsize hDwide hDwidth
  apply hchildren D
  refine ⟨hDreg, hDpos, hDwidth, hDrank, ?_, ?_⟩
  · change D.rank ≤ C.rank + extra at hDsize
    rw [Nat.add_mul, Nat.one_mul]
    omega
  · have hnext : R + (j : ℝ) * loss + refinementRoundLoss C.rank p H epsilon ≤
        R + ((j + 1 : ℕ) : ℝ) * loss := by
      push_cast
      nlinarith
    exact (Real.exp_le_exp.mpr (neg_le_neg hnext)).trans hDwide

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution

theorem refinement_error_small {p gap : ℝ} (hgap : 0 < gap) (hp : 32 / gap ≤ p) :
    4 * Real.exp (-p / 4) ≤ gap * Real.exp (-p / 8) := by
  have hp' : 32 ≤ p * gap := (div_le_iff₀ hgap).mp hp
  have hscaled := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (p / 8)) hgap.le
  have hfour : 4 ≤ gap * Real.exp (p / 8) := by nlinarith
  calc
    _ ≤ (gap * Real.exp (p / 8)) * Real.exp (-p / 4) :=
      mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem exists_quantitative_bohr_bound {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (N : ℕ) [NeZero N] (B₀ : CyclicBohr.Set N) (p R P W : ℝ),
      B₀.IsRankRegular → 0 < B₀.radius → B₀.radius ≤ 2 → 1 ≤ B₀.rank →
      512 ≤ p → 32 / (1 - refinementContraction epsilon) ≤ p → 0 ≤ R →
      Real.exp (-R) ≤ B₀.radius →
      ∀ A B : ZMod N → ℝ,
      (∀ r, 0 ≤ A r ∧ A r ≤ Real.exp p) → (∀ r, 0 ≤ B r ∧ B r ≤ Real.exp p) →
      0 ≤ W → W ≤ Real.exp (p / 8) → (∀ r, |A r - (1 + epsilon) * B r| ≤ W) →
      CyclicNiltestUpperComparison.{0} 1 N P (Real.exp (-P)) A B →
      (let n := ⌈(p / 4) / (1 - refinementContraction epsilon)⌉₊
       let d := B₀.rank + n * unbalancedRankExtra (localMomentGain (flatComparisonDelta epsilon)) p H
       let loss := refinementRoundLoss d p H epsilon
       refinementComparisonBudget d p (R + n * loss) epsilon ≤ P) →
      CellBilinearBound B₀.carrier (fun r => A r - (1 + epsilon) * B r)
        (2 * Real.exp (-p / 8)) := by
  obtain ⟨C, H, _, hH, hmoment⟩ :=
    exists_refinement_moment_orders (epsilon := epsilon) (D := 1 / 4) (by norm_num)
  refine ⟨H, hH, ?_⟩
  intro N hN B₀ p R P W hB₀ hBpos hBwidth hBrank hp hplarge hR hBwide
    A B hA hB hW hWcap ha hcompare hbudget
  obtain ⟨m, hm, _, horder, horders⟩ := hmoment p (by linarith)
  let rho := refinementContraction epsilon
  let n := ⌈(p / 4) / (1 - rho)⌉₊
  have hrho : 0 ≤ rho := (refinementContraction_bounds epsilon).1
  have hrho1 : rho < 1 := (refinementContraction_bounds epsilon).2
  have hgap : 0 < 1 - rho := by linarith
  have hdepth : p / 8 + p / 8 ≤ (1 - rho) * (n : ℝ) := by
    have h := (div_le_iff₀ hgap).mp (Nat.le_ceil ((p / 4) / (1 - rho)))
    dsimp only [n]
    nlinarith
  have hnoise : 4 * Real.exp (-p / 4) ≤ (1 - rho) * Real.exp (-(p / 8)) := by
    simpa only [neg_div] using refinement_error_small hgap hplarge
  have h := bohr_refinement_iteration B₀ hB₀ hBpos hBwidth hBrank
    hepsilon hp hR hH hBwide n A B hA hB hW hWcap ha hcompare m hm horder horders hbudget
  apply h.mono
  simpa only [neg_div] using refinement_coefficient_le hrho hrho1 hW hWcap hdepth hnoise

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RefinementPolynomialBound
namespace OAI

section

namespace Erdos3.CellRefinement

open LocalConvolution Polynomial

theorem refinementRankPolynomial_eval (C : ℕ) (p : ℝ) :
    (refinementRankPolynomial C).eval₂ (Nat.castRingHom ℝ) p =
      (C : ℝ) * (1 + (3 * (C : ℝ) + 1) * p ^ 2) ^ 4 + 1 := by
  simp [refinementRankPolynomial, Polynomial.eval₂_pow]

theorem refinementDepthPolynomial_eval (C : ℕ) (p : ℝ) :
    (refinementDepthPolynomial C).eval₂ (Nat.castRingHom ℝ) p = (C : ℝ) * p + 1 := by
  simp [refinementDepthPolynomial]

theorem refinementFinalRankPolynomial_eval (C : ℕ) (p : ℝ) :
    (refinementFinalRankPolynomial C).eval₂ (Nat.castRingHom ℝ) p =
      1 + (refinementDepthPolynomial C).eval₂ (Nat.castRingHom ℝ) p *
        (refinementRankPolynomial C).eval₂ (Nat.castRingHom ℝ) p := by
  simp [refinementFinalRankPolynomial]

theorem refinementMatchPolynomial_eval (C : ℕ) (p : ℝ) :
    (refinementMatchPolynomial C).eval₂ (Nat.castRingHom ℝ) p =
      5 * (refinementFinalRankPolynomial C).eval₂ (Nat.castRingHom ℝ) p +
        13 * p + 2 * (C : ℝ) + 8020 := by
  simp [refinementMatchPolynomial]

theorem refinementUnbalancedPolynomial_eval (C : ℕ) (p : ℝ) :
    (refinementUnbalancedPolynomial C).eval₂ (Nat.castRingHom ℝ) p =
      2 * (refinementFinalRankPolynomial C).eval₂ (Nat.castRingHom ℝ) p +
        (C : ℝ) * (1 + (3 * (C : ℝ) + 1) * p ^ 2) ^ 4 +
        2 * (C : ℝ) * p ^ 2 + 2 * p + 2 * (C : ℝ) + 3209 +
        (C : ℝ) * (3 + (3 * (C : ℝ) + 1) * p ^ 2 +
          (refinementFinalRankPolynomial C).eval₂ (Nat.castRingHom ℝ) p) := by
  simp [refinementUnbalancedPolynomial, Polynomial.eval₂_pow]

theorem refinementRoundPolynomial_eval (C : ℕ) (p : ℝ) :
    (refinementRoundPolynomial C).eval₂ (Nat.castRingHom ℝ) p =
      (refinementMatchPolynomial C).eval₂ (Nat.castRingHom ℝ) p +
        (refinementFinalRankPolynomial C).eval₂ (Nat.castRingHom ℝ) p + 3 * p + 1602 +
          (refinementUnbalancedPolynomial C).eval₂ (Nat.castRingHom ℝ) p := by
  simp [refinementRoundPolynomial]

theorem refinementWidthPolynomial_eval (C : ℕ) (p : ℝ) :
    (refinementWidthPolynomial C).eval₂ (Nat.castRingHom ℝ) p =
      (refinementDepthPolynomial C).eval₂ (Nat.castRingHom ℝ) p *
        (refinementRoundPolynomial C).eval₂ (Nat.castRingHom ℝ) p := by
  simp [refinementWidthPolynomial]

theorem refinementCostPolynomial_eval (C : ℕ) (p : ℝ) :
    (refinementCostPolynomial C).eval₂ (Nat.castRingHom ℝ) p =
      (2 * (refinementFinalRankPolynomial C).eval₂ (Nat.castRingHom ℝ) p + 4 * p +
        (refinementWidthPolynomial C).eval₂ (Nat.castRingHom ℝ) p +
          (refinementMatchPolynomial C).eval₂ (Nat.castRingHom ℝ) p + 1612) +
      (3 * p + 2 + (refinementFinalRankPolynomial C).eval₂ (Nat.castRingHom ℝ) p *
        ((refinementWidthPolynomial C).eval₂ (Nat.castRingHom ℝ) p +
          (refinementMatchPolynomial C).eval₂ (Nat.castRingHom ℝ) p + 10)) := by
  simp [refinementCostPolynomial]

theorem refinement_cost_le_polynomial {epsilon H p : ℝ} (hepsilon : 0 < epsilon)
    (hH : 0 ≤ H) (hp : 0 ≤ p) (C : ℕ)
    (hHC : H ≤ C)
    (hKC : CyclicCrootSisask.almostPeriodicityWidthConstant
      (localMomentGain (flatComparisonDelta epsilon) / 64) ≤ C)
    (hDC : localMomentErrorBudget (flatComparisonDelta epsilon) ≤ C)
    (hEC : unbalancedErrorBudget (localMomentGain (flatComparisonDelta epsilon)) ≤ C)
    (hgapC : 1 / (1 - refinementContraction epsilon) ≤ C) :
    let n := ⌈(p / 4) / (1 - refinementContraction epsilon)⌉₊
    let d := 1 + n * unbalancedRankExtra (localMomentGain (flatComparisonDelta epsilon)) p H
    refinementComparisonBudget d p (n * refinementRoundLoss d p H epsilon) epsilon ≤
      (refinementCostPolynomial C).eval₂ (Nat.castRingHom ℝ) p := by
  intro n d
  let ev := fun Q : Polynomial ℕ => Q.eval₂ (Nat.castRingHom ℝ) p
  have hev (Q : Polynomial ℕ) : 0 ≤ ev Q := natPolynomial_eval_nonneg Q hp
  have hc := localMomentGain_pos (flatComparisonDelta epsilon)
  have hgap : 0 < 1 - refinementContraction epsilon := by
    linarith [(refinementContraction_bounds epsilon).2]
  have hK : 0 ≤ CyclicCrootSisask.almostPeriodicityWidthConstant
      (localMomentGain (flatComparisonDelta epsilon) / 64) :=
    (CyclicCrootSisask.almostPeriodicityWidthConstant_pos (by positivity)).le
  have haeq : ev (refinementRankPolynomial C) =
      (C : ℝ) * (1 + (3 * (C : ℝ) + 1) * p ^ 2) ^ 4 + 1 := by
    exact refinementRankPolynomial_eval C p
  have hneq : ev (refinementDepthPolynomial C) = (C : ℝ) * p + 1 := by
    exact refinementDepthPolynomial_eval C p
  have hdeq : ev (refinementFinalRankPolynomial C) =
      1 + ev (refinementDepthPolynomial C) * ev (refinementRankPolynomial C) := by
    exact refinementFinalRankPolynomial_eval C p
  have hmeq : ev (refinementMatchPolynomial C) =
      5 * ev (refinementFinalRankPolynomial C) + 13 * p + 2 * (C : ℝ) + 8020 := by
    exact refinementMatchPolynomial_eval C p
  have hueq : ev (refinementUnbalancedPolynomial C) =
      2 * ev (refinementFinalRankPolynomial C) +
        (C : ℝ) * (1 + (3 * (C : ℝ) + 1) * p ^ 2) ^ 4 +
        2 * (C : ℝ) * p ^ 2 + 2 * p + 2 * (C : ℝ) + 3209 +
        (C : ℝ) * (3 + (3 * (C : ℝ) + 1) * p ^ 2 + ev (refinementFinalRankPolynomial C)) := by
    exact refinementUnbalancedPolynomial_eval C p
  have hleq : ev (refinementRoundPolynomial C) =
      ev (refinementMatchPolynomial C) + ev (refinementFinalRankPolynomial C) +
        3 * p + 1602 + ev (refinementUnbalancedPolynomial C) := by
    exact refinementRoundPolynomial_eval C p
  have hreq : ev (refinementWidthPolynomial C) =
      ev (refinementDepthPolynomial C) * ev (refinementRoundPolynomial C) := by
    exact refinementWidthPolynomial_eval C p
  have hqeq : ev (refinementCostPolynomial C) =
      (2 * ev (refinementFinalRankPolynomial C) + 4 * p + ev (refinementWidthPolynomial C) +
        ev (refinementMatchPolynomial C) + 1612) +
      (3 * p + 2 + ev (refinementFinalRankPolynomial C) *
        (ev (refinementWidthPolynomial C) + ev (refinementMatchPolynomial C) + 10)) := by
    exact refinementCostPolynomial_eval C p
  have ha : (unbalancedRankExtra (localMomentGain (flatComparisonDelta epsilon)) p H : ℝ) ≤
      ev (refinementRankPolynomial C) := by
    apply (unbalancedRankExtra_le (p := p) (H := H) hc).trans
    rw [haeq]
    gcongr
  have hn : (n : ℝ) ≤ ev (refinementDepthPolynomial C) := by
    have hceil := (Nat.ceil_lt_add_one (show 0 ≤ (p / 4) / (1 - refinementContraction epsilon)
      by positivity)).le
    have hmul := mul_le_mul_of_nonneg_right hgapC hp
    have hscale : (p / 4) / (1 - refinementContraction epsilon) ≤ (C : ℝ) * p := by
      rw [show (p / 4) / (1 - refinementContraction epsilon) =
        (1 / (1 - refinementContraction epsilon) * p) / 4 by ring]
      have hprod : 0 ≤ 1 / (1 - refinementContraction epsilon) * p := by positivity
      linarith
    rw [hneq]
    exact hceil.trans (add_le_add hscale le_rfl)
  have hd : (d : ℝ) ≤ ev (refinementFinalRankPolynomial C) := by
    rw [hdeq]
    change ((1 + n * unbalancedRankExtra (localMomentGain (flatComparisonDelta epsilon)) p H : ℕ) : ℝ) ≤ _
    push_cast
    exact add_le_add le_rfl (mul_le_mul hn ha (Nat.cast_nonneg _) (hev _))
  have hm : refinementMatchingLoss d p epsilon ≤ ev (refinementMatchPolynomial C) := by
    rw [hmeq]
    unfold refinementMatchingLoss
    linarith only [hd, hDC, hEC, hp]
  have hu : unbalancedWidthLoss d (localMomentGain (flatComparisonDelta epsilon)) p H ≤
      ev (refinementUnbalancedPolynomial C) := by
    apply (unbalancedWidthLoss_le_polynomial d (p := p) (H := H) hc).trans
    rw [hueq]
    gcongr
  have hl : refinementRoundLoss d p H epsilon ≤ ev (refinementRoundPolynomial C) := by
    rw [hleq]
    unfold refinementRoundLoss unbalancedReturnWidthLoss
    linarith only [hm, hd, hu, hp]
  have hl0 : 0 ≤ refinementRoundLoss d p H epsilon :=
    (by norm_num : (0 : ℝ) ≤ 2).trans (two_le_refinementRoundLoss d hp hH hepsilon)
  have hr : (n : ℝ) * refinementRoundLoss d p H epsilon ≤ ev (refinementWidthPolynomial C) := by
    rw [hreq]
    exact mul_le_mul hn hl hl0 (hev _)
  have hm0 := refinementMatchingLoss_nonneg d hp hepsilon
  have hD0 := hev (refinementFinalRankPolynomial C)
  have hR0 := hev (refinementWidthPolynomial C)
  have hM0 := hev (refinementMatchPolynomial C)
  have hprod : (d : ℝ) * ((n : ℝ) * refinementRoundLoss d p H epsilon +
      refinementMatchingLoss d p epsilon + 10) ≤ ev (refinementFinalRankPolynomial C) *
        (ev (refinementWidthPolynomial C) + ev (refinementMatchPolynomial C) + 10) := by
    gcongr
  change refinementComparisonBudget d p (n * refinementRoundLoss d p H epsilon) epsilon ≤
    ev (refinementCostPolynomial C)
  rw [hqeq]
  unfold refinementComparisonBudget
  have hprod0 : 0 ≤ ev (refinementFinalRankPolynomial C) *
      (ev (refinementWidthPolynomial C) + ev (refinementMatchPolynomial C) + 10) := by positivity
  apply max_le <;> nlinarith only [hd, hm, hr, hprod, hp, hD0, hR0, hM0, hprod0]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution

theorem exists_refinement_cost_polynomial {epsilon H : ℝ}
    (hepsilon : 0 < epsilon) (hH : 0 ≤ H) :
    ∃ Q : Polynomial ℕ, ∀ p : ℝ, 0 ≤ p →
      let n := ⌈(p / 4) / (1 - refinementContraction epsilon)⌉₊
      let d := 1 + n * unbalancedRankExtra (localMomentGain (flatComparisonDelta epsilon)) p H
      refinementComparisonBudget d p (n * refinementRoundLoss d p H epsilon) epsilon ≤
        Q.eval₂ (Nat.castRingHom ℝ) p := by
  let c := localMomentGain (flatComparisonDelta epsilon)
  let K := CyclicCrootSisask.almostPeriodicityWidthConstant (c / 64)
  let D := localMomentErrorBudget (flatComparisonDelta epsilon)
  let E := unbalancedErrorBudget c
  let r := 1 / (1 - refinementContraction epsilon)
  have hc : 0 < c := localMomentGain_pos _
  have hc1 : c ≤ 1 := (localMomentGain_le_half _).trans (by norm_num)
  have hK : 0 ≤ K := (CyclicCrootSisask.almostPeriodicityWidthConstant_pos (by positivity)).le
  have hD : 0 ≤ D := (localMomentErrorBudget_spec (flatComparisonDelta_spec hepsilon).1).1
  have hE : 0 ≤ E := (unbalancedErrorBudget_spec hc hc1).1
  have hr : 0 ≤ r := by
    have hgap : 0 < 1 - refinementContraction epsilon := by
      linarith [(refinementContraction_bounds epsilon).2]
    exact (one_div_pos.mpr hgap).le
  obtain ⟨C, hC⟩ := exists_nat_ge (H + K + D + E + r)
  refine ⟨refinementCostPolynomial C, ?_⟩
  intro p hp
  exact refinement_cost_le_polynomial hepsilon hH hp C
    (by linarith) (by change K ≤ C; linarith) (by change D ≤ C; linarith)
    (by change E ≤ C; linarith) (by change r ≤ C; linarith)

theorem exists_rescaled_refinement_budget {epsilon H : ℝ}
    (hepsilon : 0 < epsilon) (hH : 0 ≤ H) (A : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let q := (A : ℝ) * (p + 1)
      let n := ⌈(q / 4) / (1 - refinementContraction epsilon)⌉₊
      let d := 1 + n * unbalancedRankExtra (localMomentGain (flatComparisonDelta epsilon)) q H
      refinementComparisonBudget d q (n * refinementRoundLoss d q H epsilon) epsilon ≤
        (p + 2) ^ C := by
  obtain ⟨Q, hQ⟩ := exists_refinement_cost_polynomial hepsilon hH
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_affine_budget Q A
  refine ⟨C, hC, ?_⟩
  intro p hp
  exact (hQ ((A : ℝ) * (p + 1)) (by positivity)).trans (hbound p hp)

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicBilinearBound
namespace OAI

section

namespace Erdos3.CellRefinement

open scoped BigOperators

theorem realBilinearAverage_le_of_cellBilinearBound
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {a : G → ℝ} {T : ℝ} (hT : 0 ≤ T) (hbound : CellBilinearBound Finset.univ a T)
    (f g : G → ℝ) (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) (hg : ∀ r, 0 ≤ g r ∧ g r ≤ 1) :
    realBilinearAverage a f g ≤ T := by
  have h := hbound 0 f g hf hg (by simp) (by simp)
  have hu : 0 ≤ 𝔼 r, f r := Finset.expect_nonneg (fun r _ => (hf r).1)
  have hv : 0 ≤ 𝔼 r, g r := Finset.expect_nonneg (fun r _ => (hg r).1)
  have hu1 : (𝔼 r, f r) ≤ 1 :=
    (Finset.expect_le_expect (fun r (_ : r ∈ Finset.univ) => (hf r).2)).trans_eq
      (Finset.expect_const Finset.univ_nonempty 1)
  have hv1 : (𝔼 r, g r) ≤ 1 :=
    (Finset.expect_le_expect (fun r (_ : r ∈ Finset.univ) => (hg r).2)).trans_eq
      (Finset.expect_const Finset.univ_nonempty 1)
  have hPhi : ((𝔼 r, f r) * (𝔼 r, g r)) ^ (1 / 4 : ℝ) ≤ 1 :=
    Real.rpow_le_one (mul_nonneg hu hv) (by nlinarith) (by norm_num)
  have h' := h.trans (mul_le_mul_of_nonneg_left hPhi hT)
  simpa only [zero_add, mul_one, realBilinearAverage, bilinearIntegral] using h'

theorem exists_degree_one_bilinear_bound {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (p : ℝ), 2 ≤ p →
      ∀ A B : ZMod N → ℝ,
      (∀ r, 0 ≤ A r ∧ A r ≤ Real.exp p) → (∀ r, 0 ≤ B r ∧ B r ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} 1 N ((p + 2) ^ C) (Real.exp (-((p + 2) ^ C))) A B →
      ∀ f g : ZMod N → ℝ, (∀ r, 0 ≤ f r ∧ f r ≤ 1) → (∀ r, 0 ≤ g r ∧ g r ≤ 1) →
      realBilinearAverage (fun r => A r - (1 + epsilon) * B r) f g ≤ Real.exp (-4 * p) := by
  obtain ⟨H, hH, hquant⟩ := exists_quantitative_bohr_bound hepsilon
  have hgap : 0 < 1 - refinementContraction epsilon := by
    linarith [(refinementContraction_bounds epsilon).2]
  have hinv : 0 ≤ 32 / (1 - refinementContraction epsilon) := by positivity
  obtain ⟨K, hK⟩ := exists_nat_ge (512 + 32 / (1 - refinementContraction epsilon))
  have hK512 : 512 ≤ K := by
    have h : (512 : ℝ) ≤ K := by linarith
    exact_mod_cast h
  have hKgap : 32 / (1 - refinementContraction epsilon) ≤ (K : ℝ) := by linarith
  obtain ⟨C, hC, hcost⟩ := exists_rescaled_refinement_budget hepsilon hH K
  refine ⟨C, hC, ?_⟩
  intro N hN p hp A B hA hB hcompare f g hf hg
  have hp0 : 0 ≤ p := by linarith
  let q := (K : ℝ) * (p + 1)
  obtain ⟨hq512, hpq, hKq⟩ := refinement_enlargement_bounds hp0 hK512
  have hqgap : 32 / (1 - refinementContraction epsilon) ≤ q := hKgap.trans hKq
  have hAq : ∀ r, 0 ≤ A r ∧ A r ≤ Real.exp q := fun r =>
    ⟨(hA r).1, (hA r).2.trans (Real.exp_le_exp.mpr hpq)⟩
  have hBq : ∀ r, 0 ≤ B r ∧ B r ≤ Real.exp q := fun r =>
    ⟨(hB r).1, (hB r).2.trans (Real.exp_le_exp.mpr hpq)⟩
  have hWcap : 2 * Real.exp p ≤ Real.exp (q / 8) :=
    refinement_enlargement_amplitude hp0 (by omega)
  have ha : ∀ r, |A r - (1 + epsilon) * B r| ≤ 2 * Real.exp p := fun r =>
    signed_comparison_amplitude (hA r) (hB r) hepsilon.le hepsilon1.le
  have hcell := hquant N CyclicBohr.Set.whole q 0 ((p + 2) ^ C) (2 * Real.exp p)
    CyclicBohr.Set.isRankRegular_whole (by norm_num) (by norm_num) (by norm_num)
    hq512 hqgap (by norm_num) (by norm_num) A B hAq hBq (by positivity) hWcap ha hcompare
    (by simpa only [CyclicBohr.Set.rank_whole, zero_add] using hcost p hp0)
  have hwhole : CellBilinearBound Finset.univ (fun r => A r - (1 + epsilon) * B r)
      (2 * Real.exp (-q / 8)) := by
    simpa only [CyclicBohr.Set.carrier_whole] using hcell
  exact (realBilinearAverage_le_of_cellBilinearBound (by positivity) hwhole f g hf hg).trans
    (refinement_enlargement_error hp0 (by omega))

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DegreeOneShiftComparison
namespace OAI

section

namespace Erdos3

theorem exists_degree_one_shift_comparison {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (p : ℝ), 2 ≤ p →
      ∀ A B J : ZMod N → ℝ,
      (∀ r, 0 ≤ A r ∧ A r ≤ Real.exp p) → (∀ r, 0 ≤ B r ∧ B r ≤ Real.exp p) →
      (∀ r, 0 ≤ J r ∧ J r ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} 1 N ((p + 2) ^ C) (Real.exp (-((p + 2) ^ C))) A B →
      ∃ E : Finset (ZMod N), (E.card : ℝ) ≤ Real.exp (-p) * N ∧
        CyclicNiltestShiftBound.{0} 0 N p (Real.exp (-p))
          (fun r => A r - (1 + epsilon) * B r) J E := by
  obtain ⟨C, hC, hbilinear⟩ := CellRefinement.exists_degree_one_bilinear_bound hepsilon hepsilon1
  refine ⟨C, hC, ?_⟩
  intro N hN p hp A B J hA hB hJ hcompare
  obtain ⟨E, hE, hshifts⟩ := exists_small_bad_shift_set
    (fun r => A r - (1 + epsilon) * B r) J (by linarith) hJ
    (hbilinear N p hp A B hA hB hcompare)
  refine ⟨E, ?_, cyclicNiltestShiftBound_zero_of_constants _ _ E hshifts⟩
  simpa using hE

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FactoredPositiveShiftContradiction
namespace OAI

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

end Erdos3

namespace Erdos3

open scoped BigOperators

universe u

end Erdos3

namespace Erdos3.RationalFilteredNilmanifold

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3

theorem exists_degree_one_cyclicShiftComparison {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    ∃ c : ℕ, 2 ≤ c ∧ CyclicShiftComparison.{0} 1 epsilon c := by
  obtain ⟨c, hc, hbound⟩ := exists_degree_one_shift_comparison hepsilon hepsilon1
  refine ⟨c, hc, ?_⟩
  intro N hN p hp _ _ f g J hf hg hJ hcompare
  exact hbound N p hp f g J hf hg hJ hcompare

end Erdos3

namespace Erdos3

open scoped BigOperators

universe u v

end Erdos3

section

universe u v

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

universe u v

namespace Erdos3

open scoped TensorProduct BigOperators

end Erdos3

end

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance_reducible] optionLieSpace

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance_reducible] optionLieSpace

end Erdos3.PositiveShiftBasis

end OAI

end

theorem solution : type_of% @OAI.Erdos3.exists_degree_one_cyclicShiftComparison := @OAI.Erdos3.exists_degree_one_cyclicShiftComparison
