-- Prove2me | solution 1 for OAI.C0Absorption.one_class_detects
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:44:44.32065+00:00
-- url     : https://prove2.me/submissions/29cb8d98-ffcb-4e31-8f38-a349f0971f5e

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Pairings.lean:L273-L294
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.one_class_detects. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Theorems.Thm_OAI_C0Absorption_exists_uniform_lp_detector
import Theorems.Thm_OAI_C0Absorption_seminorm_sign_pair

-- ---- from OAI.Analysis.C0Absorption.Norm ----
namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

section SelectedNorm

variable {S : Type*} [MetricSpace S]

theorem listExponent_toReal (n : ℕ) :
    (listExponent n).toReal = 1 + 1 / ((triple n).2.2 + 1 : ℝ) := by
  simp [listExponent, ENNReal.toReal_add, one_div]

end SelectedNorm

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Completion ----
namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

section CompletedSeminorms

open UniformSpace Completion

variable {X : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]

theorem completedSeminorm_continuous (q : Seminorm ℝ X) (C : ℝ≥0)
    (h : ∀ x, q x ≤ C * ‖x‖) : Continuous (completedSeminorm q C h) :=
  Completion.continuous_extension

end CompletedSeminorms

section SelectedCompletion

open UniformSpace Completion

variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

theorem normCoordinates_continuous : Continuous (normCoordinates L o) :=
  Completion.continuous_extension

theorem normCoordinates_norm (z : TestSpace L o) : ‖normCoordinates L o z‖ = ‖z‖ := by
  induction z using Completion.induction_on with
  | hp => exact isClosed_eq (normCoordinates_continuous L o).norm continuous_norm
  | ih m =>
    change ‖normCoordinates L o (toTestSpace L o m)‖ = ‖toTestSpace L o m‖
    rw [normCoordinates_coe, norm_toTestSpace]
    rfl

theorem completedCoordinate_continuous (n : ℕ) : Continuous (completedCoordinate L o n) :=
  completedSeminorm_continuous _ _ _

theorem normCoordinates_apply (z : TestSpace L o) (n : ℕ) :
    normCoordinates L o z n = completedCoordinate L o n z := by
  induction z using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((lp.lipschitzWith_one_eval 2 n).continuous.comp (normCoordinates_continuous L o))
      (completedCoordinate_continuous L o n)
  | ih m =>
    change normCoordinates L o (toTestSpace L o m) n =
      completedCoordinate L o n (toTestSpace L o m)
    rw [normCoordinates_coe, completedCoordinate_coe]
    rfl

theorem completedCoordinate_summable (z : TestSpace L o) :
    Summable (fun n => (completedCoordinate L o n z) ^ 2) := by
  have h := (lp.memℓp (normCoordinates L o z)).summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
    normCoordinates_apply] using h

theorem completedNorm_sq (z : TestSpace L o) :
    ‖z‖ ^ 2 = ∑' n, (completedCoordinate L o n z) ^ 2 := by
  have h := lp.norm_rpow_eq_tsum
    (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (normCoordinates L o z)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
    normCoordinates_norm, normCoordinates_apply] using h

end SelectedCompletion

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Signs ----
namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

section Signs

theorem sum_sign_seminorm_sq_ge {X : Type*} [AddCommGroup X] [Module ℝ X]
    (q : Seminorm ℝ X) {n : ℕ} (m : Fin n → X) (i : Fin n) :
    (2 : ℝ) ^ n * (q (m i)) ^ 2 ≤
      ∑ ε : Fin n → Bool, (q (∑ j, realSign (ε j) • m j)) ^ 2 := by
  classical
  have h := Finset.sum_le_sum (s := Finset.univ) (fun ε _ => seminorm_sign_pair q m ε i)
  rw [Finset.sum_add_distrib] at h
  have heq : (∑ ε : Fin n → Bool, (q (∑ j, realSign (flipSign i ε j) • m j)) ^ 2) =
      ∑ ε : Fin n → Bool, (q (∑ j, realSign (ε j) • m j)) ^ 2 :=
    Fintype.sum_equiv (flipSign i) _ _ (fun _ => rfl)
  rw [heq] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at h
  linarith

theorem sum_coordinate_choice_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (q : ℕ → Seminorm ℝ X)
    (hdom : ∀ (s : Finset ℕ) x, ∑ d ∈ s, (q d x) ^ 2 ≤ ‖x‖ ^ 2)
    (m : ℕ → X) (M : ℝ)
    (hsum : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M)
    (s : Finset ℕ) (index : ℕ → ℕ) :
    ∑ d ∈ s, (q d (m (index d))) ^ 2 ≤ M ^ 2 := by
  classical
  let n := s.sup index + 1
  have hlt (d : ℕ) (hd : d ∈ s) : index d < n :=
    Nat.lt_succ_of_le (Finset.le_sup hd)
  have hmain : (2 : ℝ) ^ n * (∑ d ∈ s, (q d (m (index d))) ^ 2) ≤
      (2 : ℝ) ^ n * M ^ 2 := by
    calc
      (2 : ℝ) ^ n * (∑ d ∈ s, (q d (m (index d))) ^ 2) =
          ∑ d ∈ s, (2 : ℝ) ^ n * (q d (m (index d))) ^ 2 := Finset.mul_sum _ _ _
      _ ≤ ∑ d ∈ s, ∑ ε : Fin n → Bool,
          (q d (∑ i : Fin n, realSign (ε i) • m i)) ^ 2 := by
        apply Finset.sum_le_sum
        intro d hd
        exact sum_sign_seminorm_sq_ge (q d) (fun i : Fin n => m i) ⟨index d, hlt d hd⟩
      _ = ∑ ε : Fin n → Bool, ∑ d ∈ s,
          (q d (∑ i : Fin n, realSign (ε i) • m i)) ^ 2 := Finset.sum_comm
      _ ≤ ∑ ε : Fin n → Bool, M ^ 2 := by
        apply Finset.sum_le_sum
        intro ε hε
        exact (hdom s _).trans (pow_le_pow_left₀ (norm_nonneg _) (hsum n ε) 2)
      _ = (2 : ℝ) ^ n * M ^ 2 := by simp
  exact le_of_mul_le_mul_left hmain (by positivity)

theorem sum_ciSup_le_of_forall_choice {ι κ : Type*} [Nonempty κ]
    (a : ι → κ → ℝ) (s : Finset ι) (K : ℝ)
    (h : ∀ f : ι → κ, ∑ d ∈ s, a d (f d) ≤ K) :
    ∑ d ∈ s, ⨆ k, a d k ≤ K := by
  classical
  induction s using Finset.induction_on generalizing K with
  | empty => simpa using h (fun _ => Classical.choice (inferInstance : Nonempty κ))
  | @insert d s hd ih =>
    rw [Finset.sum_insert hd]
    rw [← le_sub_iff_add_le]
    apply ciSup_le
    intro k
    have ht : (∑ e ∈ s, ⨆ j, a e j) ≤ K - a d k := by
      apply ih
      intro f
      have hf := h (Function.update f d k)
      rw [Finset.sum_insert hd, Function.update_self] at hf
      have heq : (∑ e ∈ s, a e (Function.update f d k e)) = ∑ e ∈ s, a e (f e) := by
        apply Finset.sum_congr rfl
        intro e he
        rw [Function.update_of_ne (by intro heq; subst e; exact hd he)]
      rw [heq] at hf
      linarith
    linarith

theorem coordinate_envelope_summable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (q : ℕ → Seminorm ℝ X)
    (hdom : ∀ (s : Finset ℕ) x, ∑ d ∈ s, (q d x) ^ 2 ≤ ‖x‖ ^ 2)
    (m : ℕ → X) (M : ℝ)
    (hsum : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M) :
    Summable (fun d => ⨆ i : ℕ, (q d (m i)) ^ 2) ∧
      (∀ d i, (q d (m i)) ^ 2 ≤ ⨆ j : ℕ, (q d (m j)) ^ 2) := by
  have hb (d : ℕ) : BddAbove (Set.range (fun i : ℕ => (q d (m i)) ^ 2)) := by
    refine ⟨M ^ 2, ?_⟩
    rintro _ ⟨i, rfl⟩
    simpa using sum_coordinate_choice_le q hdom m M hsum {d} (fun _ => i)
  have hle (d i : ℕ) : (q d (m i)) ^ 2 ≤ ⨆ j : ℕ, (q d (m j)) ^ 2 :=
    le_ciSup (hb d) i
  constructor
  · apply summable_of_sum_le (c := M ^ 2)
    · intro d
      exact (sq_nonneg _).trans (hle d 0)
    · intro s
      apply sum_ciSup_le_of_forall_choice (fun d i => (q d (m i)) ^ 2)
      exact fun f => sum_coordinate_choice_le q hdom m M hsum s f
  · exact hle

theorem square_norm_tendsto_zero {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (q : ℕ → Seminorm ℝ X)
    (hq : ∀ x, Summable (fun d => (q d x) ^ 2))
    (hnorm : ∀ x, ‖x‖ ^ 2 = ∑' d, (q d x) ^ 2)
    (m : ℕ → X) (M : ℝ)
    (hsum : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M)
    (hzero : ∀ d, Filter.Tendsto (fun i => q d (m i)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun i => ‖m i‖ ^ 2) Filter.atTop (nhds 0) := by
  have hdom (s : Finset ℕ) (x : X) : ∑ d ∈ s, (q d x) ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [hnorm]
    exact Summable.sum_le_tsum s (fun _ _ => sq_nonneg _) (hq x)
  obtain ⟨hb, hle⟩ := coordinate_envelope_summable q hdom m M hsum
  have hp (d : ℕ) : Filter.Tendsto (fun i => (q d (m i)) ^ 2) Filter.atTop (nhds 0) := by
    simpa using (hzero d).pow 2
  have ht := tendsto_tsum_of_dominated_convergence hb hp
    (Filter.Eventually.of_forall fun i d => by
      simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hle d i)
  simpa only [← hnorm, tsum_zero] using ht

theorem exists_nonzero_coordinate {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (q : ℕ → Seminorm ℝ X)
    (hq : ∀ x, Summable (fun d => (q d x) ^ 2))
    (hnorm : ∀ x, ‖x‖ ^ 2 = ∑' d, (q d x) ^ 2)
    (m : ℕ → X) (M r : ℝ) (hr : 0 < r)
    (hlower : ∀ i, r ≤ ‖m i‖)
    (hsum : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M) :
    ∃ d, ¬ Filter.Tendsto (fun i => q d (m i)) Filter.atTop (nhds 0) := by
  by_contra! h
  have ht := square_norm_tendsto_zero q hq hnorm m M hsum h
  have hl : r ^ 2 ≤ (0 : ℝ) := ge_of_tendsto ht
    (Filter.Eventually.of_forall fun i => pow_le_pow_left₀ hr.le (hlower i) 2)
  nlinarith [sq_pos_of_pos hr]

end Signs

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Lists ----
namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

section CompletedLists

open UniformSpace Completion
variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

theorem completedSigma_continuous (n : ℕ) : Continuous (completedSigma L o n) :=
  continuous_const.mul (completedCoordinate_continuous L o n)

theorem completedSigma_le (n : ℕ) (z : TestSpace L o) :
    completedSigma L o n z ≤ (squareWeight n : ℝ)⁻¹ * ‖z‖ := by
  induction z using Completion.induction_on with
  | hp => exact isClosed_le (completedSigma_continuous L o n) (by fun_prop)
  | ih m =>
    change completedSigma L o n (toTestSpace L o m) ≤
      (squareWeight n : ℝ)⁻¹ * ‖toTestSpace L o m‖
    rw [completedSigma_coe, norm_toTestSpace]
    exact sigma_le_preNorm L o n m

theorem completedList_le_sigma (n : ℕ)
    (l : AdmissibleList (L (triple n).1) (listConstant n)) (z : TestSpace L o) :
    ‖completedList L o n l z‖ ≤ completedSigma L o n z := by
  induction z using Completion.induction_on with
  | hp =>
    exact isClosed_le (completedList L o n l).continuous.norm
      (completedSigma_continuous L o n)
  | ih m =>
    change ‖completedList L o n l (toTestSpace L o m)‖ ≤
      completedSigma L o n (toTestSpace L o m)
    rw [completedList_coe, completedSigma_coe]
    exact list_le_sigma _ _ _ o l m

theorem completedListNorm_bddAbove (n : ℕ) :
    BddAbove (Set.range (completedListNorm L o n)) := by
  refine ⟨completedSigma L o n, ?_⟩
  rintro _ ⟨l, rfl⟩ z
  exact completedList_le_sigma L o n l z

theorem sigmaFromLists_le (n : ℕ) (z : TestSpace L o) :
    sigmaFromLists L o n z ≤ (squareWeight n : ℝ)⁻¹ * ‖z‖ := by
  rw [sigmaFromLists, Seminorm.iSup_apply (completedListNorm_bddAbove L o n)]
  exact ciSup_le fun l => (completedList_le_sigma L o n l z).trans
    (completedSigma_le L o n z)

theorem sigmaFromLists_eq (n : ℕ) (z : TestSpace L o) :
    sigmaFromLists L o n z = completedSigma L o n z := by
  induction z using Completion.induction_on with
  | hp =>
    exact isClosed_eq (seminorm_lipschitz (sigmaFromLists L o n) ((squareWeight n)⁻¹)
      (sigmaFromLists_le L o n)).continuous (completedSigma_continuous L o n)
  | ih m =>
    change sigmaFromLists L o n (toTestSpace L o m) =
      completedSigma L o n (toTestSpace L o m)
    rw [sigmaFromLists, Seminorm.iSup_apply (completedListNorm_bddAbove L o n),
      completedSigma_coe]
    refine Eq.trans ?_ (sigma_apply _ _ _ o (show Molecule S from m)).symm
    apply congrArg iSup
    funext l
    exact congrArg norm (completedList_coe L o n l m)

theorem completedSigma_eq_iSup (n : ℕ) (z : TestSpace L o) :
    completedSigma L o n z =
      ⨆ l : AdmissibleList (L (triple n).1) (listConstant n), ‖completedList L o n l z‖ := by
  rw [← sigmaFromLists_eq, sigmaFromLists,
    Seminorm.iSup_apply (completedListNorm_bddAbove L o n)]
  rfl

end CompletedLists

section InterpolationAndDenseLimits

end InterpolationAndDenseLimits

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Pairings ----
namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

section CompletedPairings

open UniformSpace Completion
variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

theorem list_test_pairing_bound (n : ℕ)
    (l : AdmissibleList (L (triple n).1) (listConstant n)) (i : Fin l.length)
    (m : PreSpace L o) : |pairing S (l.test i) m| ≤ (squareWeight n)⁻¹ * ‖m‖ := by
  have h := PiLp.norm_apply_le (l.eval (listExponent n) (show Molecule S from m)) i
  change |pairing S (l.test i) m| ≤ ‖l.eval (listExponent n) m‖ at h
  exact h.trans ((list_le_sigma _ _ _ o l m).trans (sigma_le_preNorm L o n m))

theorem completedList_apply (n : ℕ)
    (l : AdmissibleList (L (triple n).1) (listConstant n)) (z : TestSpace L o) (i : Fin l.length) :
    completedList L o n l z i = completedPairing L o (l.test i) z := by
  induction z using Completion.induction_on with
  | hp =>
    exact isClosed_eq ((PiLp.proj (listExponent n) (𝕜 := ℝ) (fun _ : Fin l.length => ℝ) i).continuous.comp
      (completedList L o n l).continuous) Completion.continuous_extension
  | ih m =>
    change completedList L o n l (toTestSpace L o m) i =
      completedPairing L o (l.test i) (toTestSpace L o m)
    rw [completedList_coe, completedPairing_coe L o (l.test i) ((squareWeight n)⁻¹)
      (list_test_pairing_bound L o n l i)]
    rfl

theorem listExponent_toReal_pos (n : ℕ) : 0 < (listExponent n).toReal := by
  rw [listExponent_toReal]
  positivity

theorem exists_smaller_exponent (n : ℕ) :
    ∃ n', (triple n').1 = (triple n).1 ∧ listConstant n' = listConstant n ∧
      (listExponent n').toReal < (listExponent n).toReal := by
  obtain ⟨n', hn'⟩ := triple_surjective ((triple n).1, (triple n).2.1, (triple n).2.2 + 1)
  refine ⟨n', by rw [hn'], by simp [listConstant, hn'], ?_⟩
  rw [listExponent_toReal, listExponent_toReal, hn']
  simp only [Nat.cast_add, Nat.cast_one]
  have hh : 1 / ((triple n).2.2 + 1 + 1 : ℝ) < 1 / ((triple n).2.2 + 1 : ℝ) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  linarith

theorem fixed_sigma_detector (n : ℕ) (a M : ℝ) (ha : 0 < a) (hM : 0 < M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : TestSpace L o,
      a ≤ completedSigma L o n z → ‖z‖ ≤ M →
      ∃ f ∈ L (triple n).1, δ ≤ |completedPairing L o f z| := by
  obtain ⟨n', hL, hC, hp⟩ := exists_smaller_exponent n
  let B := (squareWeight n' : ℝ)⁻¹ * M + 1
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨δ, hδ, hdetect⟩ := exists_uniform_lp_detector (listExponent n) (listExponent n')
    (listExponent_toReal_pos n) (listExponent_toReal_pos n') hp (a / 2) B (by positivity) hB
  refine ⟨δ, hδ, ?_⟩
  intro z hsig hz
  have hex : ∃ l : AdmissibleList (L (triple n).1) (listConstant n),
      a / 2 < ‖completedList L o n l z‖ := by
    by_contra! hl
    have hs : completedSigma L o n z ≤ a / 2 := by
      rw [completedSigma_eq_iSup]
      exact ciSup_le hl
    linarith
  obtain ⟨l, hl⟩ := hex
  let l' := transferredList L n n' hL hC l
  let x : Fin l.length → ℝ := fun i => completedPairing L o (l.test i) z
  have heq : completedList L o n l z = WithLp.toLp (listExponent n) x := by
    apply PiLp.ext
    intro i
    exact completedList_apply L o n l z i
  have heq' : completedList L o n' l' z = WithLp.toLp (listExponent n') x := by
    apply PiLp.ext
    intro i
    exact completedList_apply L o n' l' z i
  have hu : ‖WithLp.toLp (listExponent n') x‖ ≤ B := by
    rw [← heq']
    calc
      ‖completedList L o n' l' z‖ ≤ completedSigma L o n' z := completedList_le_sigma L o n' l' z
      _ ≤ (squareWeight n' : ℝ)⁻¹ * ‖z‖ := completedSigma_le L o n' z
      _ ≤ (squareWeight n' : ℝ)⁻¹ * M :=
        mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr (squareWeight n').coe_nonneg)
      _ ≤ B := by dsimp [B]; linarith
  rw [heq] at hl
  obtain ⟨i, hi⟩ := hdetect l.length x hl.le hu
  exact ⟨l.test i, l.mem i, hi.le⟩

end CompletedPairings

section FurtherDetectors

 theorem nonnegative_has_positive_subsequence (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hn : ¬ Filter.Tendsto f Filter.atTop (nhds 0)) :
    ∃ a : ℝ, 0 < a ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, a ≤ f (φ i) := by
  rw [Metric.tendsto_nhds] at hn
  push Not at hn
  obtain ⟨a, ha, hfrequent⟩ := hn
  have hf' : ∃ᶠ i in Filter.atTop, a ≤ f i := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (hf _)] using hfrequent
  obtain ⟨φ, hm, hl⟩ := Filter.extraction_of_frequently_atTop hf'
  exact ⟨a, ha, φ, hm, hl⟩

theorem bounded_signs_norm_each {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (m : ℕ → X) (M : ℝ)
    (hsum : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M) (i : ℕ) :
    ‖m i‖ ≤ M := by
  have hM : 0 ≤ M := by simpa using hsum 0 Fin.elim0
  let ε : Fin (i+1) → Bool := fun _ => true
  let j : Fin (i+1) := ⟨i, Nat.lt_succ_self i⟩
  have h := seminorm_sign_pair (normSeminorm ℝ X) (fun j : Fin (i+1) => m j) ε j
  have h₁ := pow_le_pow_left₀ (norm_nonneg _) (hsum (i+1) ε) 2
  have h₂ := pow_le_pow_left₀ (norm_nonneg _) (hsum (i+1) (flipSign j ε)) 2
  change 2 * ‖m i‖ ^ 2 ≤ ‖∑ k : Fin (i+1), realSign (ε k) • m k‖ ^ 2 +
    ‖∑ k : Fin (i+1), realSign (flipSign j ε k) • m k‖ ^ 2 at h
  nlinarith [norm_nonneg (m i)]

variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

theorem completedCoordinate_eq_weight_sigma (n : ℕ) (z : TestSpace L o) :
    completedCoordinate L o n z = (squareWeight n : ℝ) * completedSigma L o n z := by
  change completedCoordinate L o n z = (squareWeight n : ℝ) *
    ((squareWeight n : ℝ)⁻¹ * completedCoordinate L o n z)
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (squareWeight_pos n)), one_mul]

theorem one_class_detects (m : ℕ → TestSpace L o) (M r : ℝ) (hr : 0 < r)
    (hlower : ∀ i, r ≤ ‖m i‖)
    (hsum : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M) :
    ∃ h : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ f : ℕ → S → ℝ, ∀ i, f i ∈ L h ∧ δ ≤ |completedPairing L o (f i) (m (φ i))| := by
  have hnorm := bounded_signs_norm_each m M hsum
  have hM : 0 < M := hr.trans_le ((hlower 0).trans (hnorm 0))
  obtain ⟨n, hn⟩ := exists_nonzero_coordinate (completedCoordinate L o)
    (completedCoordinate_summable L o) (completedNorm_sq L o) m M r hr hlower hsum
  have hnσ : ¬ Filter.Tendsto (fun i => completedSigma L o n (m i))
      Filter.atTop (nhds 0) := by
    intro hh
    apply hn
    have hh' := hh.const_mul (squareWeight n : ℝ)
    simpa only [mul_zero, ← completedCoordinate_eq_weight_sigma] using hh'
  obtain ⟨a, ha, φ, hφ, hφa⟩ := nonnegative_has_positive_subsequence
    (fun i => completedSigma L o n (m i)) (fun i => apply_nonneg _ _) hnσ
  obtain ⟨δ, hδ, hδdetect⟩ := fixed_sigma_detector L o n a M ha hM
  have hchoose : ∀ i, ∃ f ∈ L (triple n).1, δ ≤ |completedPairing L o f (m (φ i))| :=
    fun i => hδdetect (m (φ i)) (hφa i) (hnorm (φ i))
  choose f hf hd using hchoose
  exact ⟨(triple n).1, δ, hδ, φ, hφ, f, fun i => ⟨hf i, hd i⟩⟩

end FurtherDetectors

end
end C0Absorption

end OAI

-- ---- platform node ----
open OAI OAI.C0Absorption
open scoped BigOperators NNReal ENNReal
open Finset


theorem solution : type_of% @_root_.OAI.C0Absorption.one_class_detects := @_root_.OAI.C0Absorption.one_class_detects
