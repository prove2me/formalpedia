-- Prove2me | solution 1 for OAI.Erdos3.exists_polynomial_scored_crt_representative_patch
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T19:26:49.285443+00:00
-- url     : https://prove2.me/submissions/6050574d-091a-41ab-a170-de4c1bbb4ebf

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B026
import Theorems.Thm_OAI_Erdos3_RepresentativeWindow_crtPatch_value_residues

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InteriorIntervalCutoff
namespace OAI

section

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

theorem residue_fraction_mem_unit_interval {N : ℕ} [NeZero N] (x : ZMod N) :
    0 ≤ (x.val : ℝ) / N ∧ (x.val : ℝ) / N ≤ 1 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  exact ⟨by positivity, (div_le_one hN).mpr (by exact_mod_cast x.val_lt.le)⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem interiorIntervalCutoff_one (eta : ℝ≥0) (heta : 0 < eta) {x : ℝ}
    (hx : 2 * (eta : ℝ) ≤ x ∧ x ≤ 1 - 2 * eta) : interiorIntervalCutoff eta x = 1 := by
  apply linearCutoff_eq_one _ _ heta
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem interiorIntervalCutoff_cyclic_loss {N : ℕ} [NeZero N]
    (eta : ℝ≥0) (heta : 0 < eta) :
    (𝔼 x : ZMod N, |1 - interiorIntervalCutoff eta ((x.val : ℝ) / N)|) ≤
      12 * (eta : ℝ) + 3 / N := by
  let E := cyclicWrapExceptional (0 : ZMod N) (2 * eta)
  have hcap (x : ZMod N) : |1 - interiorIntervalCutoff eta ((x.val : ℝ) / N)| ≤ 1 := by
    have h := interiorIntervalCutoff_range eta ((x.val : ℝ) / N)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hgood (x : ZMod N) (hx : x ∉ E) :
      |1 - interiorIntervalCutoff eta ((x.val : ℝ) / N)| ≤ 0 := by
    obtain ⟨h0, h1, _⟩ := outside_cyclicWrapExceptional (0 : ZMod N) x hx
    rw [interiorIntervalCutoff_one eta heta ⟨h0.le, h1.le⟩]
    norm_num
  have h := expect_abs_le_of_exceptional_set E _ (by norm_num : (0 : ℝ) ≤ 0) hcap hgood
  simp only [zero_add, one_mul, ZMod.card] at h
  apply h.trans
  calc
    _ ≤ 6 * (2 * (eta : ℝ)) + 3 / N :=
      cyclicWrapExceptional_density_le (0 : ZMod N) (show 0 ≤ 2 * (eta : ℝ) by positivity)
    _ = _ := by ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.CyclicInteriorScore
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem bounded_cutoff_score_lower {X : Type*} [Fintype X]
    (f b : X → ℝ) {M epsilon sigma : ℝ} (hM : 0 ≤ M)
    (hf : ∀ x, |f x| ≤ M) (hb : (𝔼 x, |1 - b x|) ≤ epsilon)
    (hscore : sigma ≤ 𝔼 x, f x) :
    sigma - M * epsilon ≤ 𝔼 x, f x * b x := by
  have hloss : (𝔼 x, f x * (1 - b x)) ≤ M * epsilon := by
    calc
      _ ≤ 𝔼 x, M * |1 - b x| := by
        apply Finset.expect_le_expect
        intro x _
        exact (le_abs_self _).trans (by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hf x) (abs_nonneg _))
      _ = M * (𝔼 x, |1 - b x|) := (Finset.mul_expect ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hb hM
  have he : (𝔼 x, f x) = (𝔼 x, f x * b x) + (𝔼 x, f x * (1 - b x)) := by
    rw [← Finset.expect_add_distrib]
    apply Finset.expect_congr rfl
    intro x _
    ring
  linarith

theorem interiorIntervalCutoff_score {N : ℕ} [NeZero N] (f : ZMod N → ℝ)
    {M sigma : ℝ} (hM : 0 < M) (hsigma : 0 < sigma)
    (hf : ∀ x, |f x| ≤ M) (hscore : sigma ≤ 𝔼 x, f x)
    (eta : ℝ≥0) (heta : 0 < eta) (hwidth : (eta : ℝ) ≤ sigma / (100 * M))
    (hN : 1 / (N : ℝ) ≤ sigma / (100 * M)) :
    3 * sigma / 4 ≤ 𝔼 x, f x * interiorIntervalCutoff eta ((x.val : ℝ) / N) := by
  have h := bounded_cutoff_score_lower f
    (fun x => interiorIntervalCutoff eta ((x.val : ℝ) / N)) hM.le hf
    (interiorIntervalCutoff_cyclic_loss eta heta) hscore
  have he : M * (sigma / (100 * M)) = sigma / 100 := by field_simp [hM.ne']
  have hw := mul_le_mul_of_nonneg_left hwidth hM.le
  have hrec := mul_le_mul_of_nonneg_left hN hM.le
  have hthree : (3 : ℝ) / N = 3 * (1 / N) := by ring
  rw [he] at hw hrec
  rw [hthree] at h
  nlinarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PositivePartitionScore
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_weighted_partition_score {Ω ι : Type*} [Fintype Ω] [Fintype ι] [Nonempty ι]
    (a : Ω → ℝ) (w : ι → Ω → ℝ) (hsum : ∀ x, ∑ i, w i x = 1)
    {S : ℝ} (hS : S ≤ 𝔼 x, a x) :
    ∃ i, S / Fintype.card ι ≤ 𝔼 x, a x * w i x := by
  have htotal : (∑ i, 𝔼 x, a x * w i x) = 𝔼 x, a x := by
    rw [← Finset.expect_sum_comm]
    apply Finset.expect_congr rfl
    intro x _
    rw [← Finset.mul_sum, hsum, mul_one]
  have hmean : (𝔼 i, 𝔼 x, a x * w i x) = (𝔼 x, a x) / Fintype.card ι := by
    rw [Fintype.expect_eq_sum_div_card, htotal]
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty
    (show S / Fintype.card ι ≤ 𝔼 i, 𝔼 x, a x * w i x from
      hmean.symm ▸ div_le_div_of_nonneg_right hS (Nat.cast_nonneg _))
  exact ⟨i, hi⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RepresentativeWindowPatch
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {X I : Type*} [PseudoMetricSpace X] [Fintype I]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem intervalSiteWeight_sum {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (x : ℝ) (hx : |x| ≤ B) :
    ∑ i, intervalSiteWeight B r i x = 1 := by
  apply regularizedTentPartition_sum _ hr
  obtain ⟨i, hi⟩ := exists_uniformIntervalGrid_approx hB (boxCoverMeshCount_pos B 1 r) x hx
  refine ⟨i, ?_⟩
  have he := boxCoverMeshCount_error (1 : ℝ≥0) hr (B := B)
  simp only [NNReal.coe_one, one_mul] at he
  exact (show dist x (intervalSiteCenter B r i) ≤ 2 * B / boxCoverMeshCount B 1 r from hi).trans he

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {X I : Type*} [PseudoMetricSpace X] [Fintype I]

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped NNReal

namespace FiniteProbabilityWeights

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem representativeWindowCount_pos : 0 < representativeWindowCount := by
  unfold representativeWindowCount intervalSiteCount
  omega

theorem exists_localizedRepresentativeWindow_score {N : ℕ} [NeZero N]
    (f : ZMod N → ℝ) {M sigma : ℝ} (hM : 0 < M) (hsigma : 0 < sigma)
    (hf : ∀ x, |f x| ≤ M) (hscore : sigma ≤ 𝔼 x, f x)
    (eta : ℝ≥0) (heta : 0 < eta) (hwidth : (eta : ℝ) ≤ sigma / (100 * M))
    (hN : 1 / (N : ℝ) ≤ sigma / (100 * M)) :
    ∃ i : Fin representativeWindowCount, 3 * sigma / (4 * representativeWindowCount) ≤
      𝔼 x, f x * (localizedRepresentativeWindow eta heta i).value ((x.val : ℝ) / N) := by
  let : Nonempty (Fin representativeWindowCount) := ⟨⟨0, representativeWindowCount_pos⟩⟩
  have hs := interiorIntervalCutoff_score f hM hsigma hf hscore eta heta hwidth hN
  have hsum (x : ZMod N) : (∑ i : Fin representativeWindowCount,
      intervalSiteWeight 1 (1 / 16) i ((x.val : ℝ) / N)) = 1 :=
    intervalSiteWeight_sum (by norm_num) (by norm_num) _
      (by rw [abs_of_nonneg (residue_fraction_mem_unit_interval x).1]
          exact (residue_fraction_mem_unit_interval x).2)
  obtain ⟨i, hi⟩ := exists_weighted_partition_score (ι := Fin representativeWindowCount)
    (fun x : ZMod N => f x * interiorIntervalCutoff eta ((x.val : ℝ) / N))
    (fun i x => intervalSiteWeight 1 (1 / 16) i ((x.val : ℝ) / N)) hsum hs
  refine ⟨i, ?_⟩
  simpa only [Fintype.card_fin, div_div, mul_assoc, localizedRepresentativeWindow] using hi

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped NNReal

namespace RepresentativeWindow

end RepresentativeWindow
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CRTWindowScore
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

variable {J : Type*} [Fintype J] [DecidableEq J] (N : J → ℕ)
  [∀ j, NeZero (N j)] [NeZero (∏ j, N j)]
  (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))

theorem crt_representative_patch_score (s : ℕ) (hs : 1 ≤ s)
    (f : ZMod (∏ j, N j) → ℝ) (w : RepresentativeWindow) :
    (𝔼 u : (j : J) → ZMod (N j),
      f ((ZMod.prodEquivPi N hN).symm u) *
        (w.crtPatch N hN s hs).value (fun j => ((u j).val : ℝ))) =
      𝔼 x, f x * w.value ((x.val : ℝ) / (∏ j, N j : ℕ)) := by
  apply Fintype.expect_equiv (ZMod.prodEquivPi N hN).symm.toEquiv
  intro u
  rw [w.crtPatch_value_residues N hN s hs]
  rfl

theorem exists_scored_crt_representative_patch (s : ℕ) (hs : 1 ≤ s)
    (f : ZMod (∏ j, N j) → ℝ) {M sigma : ℝ} (hM : 0 < M) (hsigma : 0 < sigma)
    (hf : ∀ x, |f x| ≤ M) (hscore : sigma ≤ 𝔼 x, f x)
    (hsize : 1 / ((∏ j, N j : ℕ) : ℝ) ≤ sigma / (100 * M)) :
    ∃ w : RepresentativeWindow,
      (w.lip : ℝ) = 100 * M / sigma + representativeWindowPartitionLip ∧
      3 * sigma / (4 * representativeWindowCount) ≤
        𝔼 u : (j : J) → ZMod (N j),
          f ((ZMod.prodEquivPi N hN).symm u) *
            (w.crtPatch N hN s hs).value (fun j => ((u j).val : ℝ)) := by
  let eta : ℝ≥0 := ⟨sigma / (100 * M), by positivity⟩
  have heta : 0 < eta := by change 0 < sigma / (100 * M); positivity
  obtain ⟨i, hi⟩ := exists_localizedRepresentativeWindow_score f hM hsigma hf hscore
    eta heta le_rfl hsize
  let w := localizedRepresentativeWindow eta heta i
  refine ⟨w, ?_, ?_⟩
  · change (sigma / (100 * M))⁻¹ + (representativeWindowPartitionLip : ℝ) = _
    rw [inv_div]
  · rw [crt_representative_patch_score N hN s hs]
    exact hi

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.RepresentativeWindowBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem exists_representativeWindow_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p M sigma : ℝ, 0 ≤ p → 0 < M → M ≤ Real.exp p →
      Real.exp (-p) ≤ sigma →
      Real.log (2 + 100 * M / sigma + representativeWindowPartitionLip) ≤ (p + 2) ^ C ∧
      Real.exp (-((p + 2) ^ C)) ≤ 3 * sigma / (4 * representativeWindowCount) := by
  obtain ⟨a, ha⟩ := exists_nat_ge
    (Real.log (102 + (representativeWindowPartitionLip : ℝ)))
  obtain ⟨b, hb⟩ := exists_nat_ge (Real.log (4 * (representativeWindowCount : ℝ)))
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget
    (2 * Polynomial.X + Polynomial.C (a + b))
  refine ⟨C, hC, ?_⟩
  intro p M sigma hp hM hMexp hsigma
  have hspos : 0 < sigma := lt_of_lt_of_le (Real.exp_pos _) hsigma
  have hbudget : 2 * p + a + b ≤ (p + 2) ^ C := by
    simpa [Nat.cast_add, add_assoc] using hbound p hp
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hK : 0 ≤ (representativeWindowPartitionLip : ℝ) := NNReal.coe_nonneg _
  have hdiv : M / sigma ≤ Real.exp (2 * p) := by
    calc
      _ ≤ Real.exp p / Real.exp (-p) :=
        div_le_div₀ (Real.exp_pos _).le hMexp (Real.exp_pos _) hsigma
      _ = Real.exp (2 * p) := by rw [← Real.exp_sub]; congr 1; ring
  have he : 1 ≤ Real.exp (2 * p) := Real.one_le_exp (by positivity)
  have hlip : 2 + 100 * M / sigma + representativeWindowPartitionLip ≤
      (102 + (representativeWindowPartitionLip : ℝ)) * Real.exp (2 * p) := by
    have hscaled := mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 100)
    have hrest := mul_le_mul_of_nonneg_left he (show 0 ≤ 2 +
      (representativeWindowPartitionLip : ℝ) by positivity)
    rw [mul_div_assoc]
    nlinarith
  have hcount : 0 < (4 * (representativeWindowCount : ℝ)) := by
    have : (0 : ℝ) < representativeWindowCount := by exact_mod_cast representativeWindowCount_pos
    positivity
  constructor
  · apply (Real.log_le_iff_le_exp (by positivity)).mpr
    calc
      _ ≤ (102 + (representativeWindowPartitionLip : ℝ)) * Real.exp (2 * p) := hlip
      _ = Real.exp (Real.log (102 + (representativeWindowPartitionLip : ℝ)) + 2 * p) := by
        rw [Real.exp_add, Real.exp_log (by positivity)]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  · calc
      _ ≤ Real.exp (-p - Real.log (4 * (representativeWindowCount : ℝ))) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (-p) / (4 * representativeWindowCount) := by
        rw [Real.exp_sub, Real.exp_log hcount]
      _ ≤ 3 * sigma / (4 * representativeWindowCount) :=
        div_le_div_of_nonneg_right (by linarith) hcount.le

theorem exists_polynomial_scored_crt_representative_patch :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {J : Type*} [Fintype J] [DecidableEq J]
      (N : J → ℕ) [∀ j, NeZero (N j)] [NeZero (∏ j, N j)]
      (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j))) (s : ℕ) (hs : 1 ≤ s)
      (f : ZMod (∏ j, N j) → ℝ) {p M sigma : ℝ},
      0 ≤ p → 0 < M → M ≤ Real.exp p → Real.exp (-p) ≤ sigma →
      (∀ x, |f x| ≤ M) → sigma ≤ (𝔼 x, f x) →
      1 / ((∏ j, N j : ℕ) : ℝ) ≤ sigma / (100 * M) →
      ∃ w : RepresentativeWindow,
        Real.log (2 + ((w.crtPatch N hN s hs).kernel.lip : ℝ)) ≤ (p + 2) ^ C ∧
        Real.exp (-((p + 2) ^ C)) ≤
          𝔼 u : (j : J) → ZMod (N j), f ((ZMod.prodEquivPi N hN).symm u) *
            (w.crtPatch N hN s hs).value (fun j => ((u j).val : ℝ)) := by
  obtain ⟨C, hC, hbudget⟩ := exists_representativeWindow_budget
  refine ⟨C, hC, ?_⟩
  intro J _ _ N _ _ hN s hs f p M sigma hp hM hMexp hsigma hf hscore hsize
  obtain ⟨w, hw, hws⟩ := exists_scored_crt_representative_patch N hN s hs f hM
    (lt_of_lt_of_le (Real.exp_pos _) hsigma) hf hscore hsize
  have hb := hbudget p M sigma hp hM hMexp hsigma
  refine ⟨w, ?_, hb.2.trans hws⟩
  rw [RepresentativeWindow.crtPatch_lip, hw]
  simpa only [add_assoc] using hb.1

end Erdos3

end

end OAI

end

theorem solution.{u_1} : type_of% @OAI.Erdos3.exists_polynomial_scored_crt_representative_patch.{u_1} := @OAI.Erdos3.exists_polynomial_scored_crt_representative_patch.{u_1}
