-- Prove2me | solution 1 for OAI.Erdos3.CellRefinement.exists_quantitative_bohr_bound_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T10:59:40.757933+00:00
-- url     : https://prove2.me/submissions/a99be6d9-7705-4c8e-a554-7b80c09b5b69

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B124
import Definitions.Def_OAIE3v2B130
import Theorems.Thm_OAI_Erdos3_CellRefinement_exists_refinement_matching_geometry_s2
import Theorems.Thm_OAI_Erdos3_CellRefinement_normalized_bilinear_refinement_step_s2

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


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PeelingDecomposition
namespace OAI


namespace Erdos3

open scoped BigOperators

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

end CellRefinement
end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalMomentScale
namespace OAI

section

namespace Erdos3.LocalConvolution

open scoped BigOperators

theorem localMomentExponentFactor_pos (delta : ℝ) : 0 < localMomentExponentFactor delta :=
  momentAmplificationFactor_pos _

theorem localMomentGain_pos (delta : ℝ) : 0 < localMomentGain delta :=
  div_pos (momentAmplificationGain_pos _) (by norm_num)

theorem localMomentGain_le_half (delta : ℝ) : localMomentGain delta ≤ 1 / 2 :=
  div_le_div_of_nonneg_right (momentAmplificationGain_le_one _) (by norm_num)

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BohrTorusApproximation
namespace OAI

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteCellRefinement
namespace OAI

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

theorem unbalancedWidthLoss_nonneg (rank : ℕ) {c p H : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hp : 0 ≤ p) (hH : 0 ≤ H) :
    0 ≤ unbalancedWidthLoss rank c p H := by
  have hK := (almostPeriodicityWidthConstant_pos (show 0 < c / 64 by positivity)).le
  have hE := (unbalancedErrorBudget_spec hc hc1).1
  have hlog : 0 ≤ Real.log (2 + (rank : ℝ)) :=
    Real.log_nonneg (by have hr : (0 : ℝ) ≤ (rank : ℝ) := Nat.cast_nonneg rank; linarith)
  unfold unbalancedWidthLoss
  positivity

end Erdos3.LocalConvolution

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RefinementEnlargement
namespace OAI

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
    exists_refinement_matching_geometry_s2 B₀ hBpos hB₀ hBwidth hBrank
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
  have h := normalized_bilinear_refinement_step_s2 B₀ L S hB₀ hLreg hSpos hSwidth hSreg hSrank
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

theorem exists_quantitative_bohr_bound_s2_oai {epsilon : ℝ} (hepsilon : 0 < epsilon) :
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

theorem solution : type_of% @OAI.Erdos3.CellRefinement.exists_quantitative_bohr_bound_s2_oai := @OAI.Erdos3.CellRefinement.exists_quantitative_bohr_bound_s2_oai
