-- Prove2me | solution 1 for OAI.RandomKSAT.variance_main
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:11:11.592602+00:00
-- url     : https://prove2.me/submissions/a3f51a42-3af2-4e64-bde7-c0a02d78ce69

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/Main.lean:L15-L25
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.RandomKSAT.variance_main.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_RandomKSAT_variance_main) verbatim and is proved by it.
import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiniteVariance
import Definitions.Def_OAI_Probability_SATVariance_LifetimePotential
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiberRefresh
import Definitions.Def_OAI_Probability_SATVariance_PairEvolution
import Definitions.Def_OAI_Probability_SATVariance_HiddenTests
import Definitions.Def_OAI_Probability_SATVariance_WeightedRewards
import Definitions.Def_OAI_Probability_SATVariance_CountMoments
import Definitions.Def_OAI_Probability_SATVariance_SupportProbabilities__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_OmissionCompression
import Definitions.Def_OAI_Probability_SATVariance_CapBridge
import Definitions.Def_OAI_Probability_SATVariance_ShuffleAverages
import Definitions.Def_OAI_Probability_SATVariance_BystanderStops
import Definitions.Def_OAI_Probability_SATVariance_InsertionVariance
import Definitions.Def_OAI_Probability_SATVariance_IsolatedSupports
import Definitions.Def_OAI_Probability_SATVariance_BystanderVariance
import Theorems.Thm_OAI_RandomKSAT_capped_variance_upper
import Theorems.Thm_OAI_RandomKSAT_exists_lower_scale
import Theorems.Thm_OAI_RandomKSAT_finiteTime_stream
import Theorems.Thm_OAI_RandomKSAT_firstFailure_finite_ae
import Theorems.Thm_OAI_RandomKSAT_lt_listStop_iff
import Theorems.Thm_OAI_RandomKSAT_measurable_firstFailure
import Theorems.Thm_OAI_RandomKSAT_natH_mass_bound
import Theorems.Thm_OAI_RandomKSAT_sentinel_linear_lower
import Theorems.Thm_OAI_RandomKSAT_sum_fin_indicator_lt
import Theorems.Thm_OAI_RandomKSAT_variance_bridge

-- ---- from OAI.Probability.SATVariance.ClauseCombinatorics ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma support_card (n k : ℕ) :
    Fintype.card {s : Finset (Fin n) // s.card = k} = n.choose k := by
  classical
  rw [Fintype.card_of_subtype ((Finset.univ : Finset (Fin n)).powersetCard k)
    (by intro s; simp)]
  simp

lemma clause_card (n k : ℕ) : Fintype.card (Clause n k) = n.choose k * 2 ^ k := by
  classical
  change Fintype.card ((s : {s : Finset (Fin n) // s.card = k}) × (s.1 → Bool)) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  trans ∑ _ : {s : Finset (Fin n) // s.card = k}, 2 ^ k
  · apply Finset.sum_congr rfl
    intro s _
    rw [s.property]
  · rw [Finset.sum_const, Finset.card_univ, support_card, smul_eq_mul]

lemma clause_nonempty (n k : ℕ) (hkn : k ≤ n) : Nonempty (Clause n k) := by
  rw [← Fintype.card_pos_iff, clause_card]
  exact Nat.mul_pos (Nat.choose_pos hkn) (pow_pos (by decide) _)

lemma clauseLaw_probability (n k : ℕ) (hkn : k ≤ n) :
    IsProbabilityMeasure (clauseLaw n k) := by
  let := clause_nonempty n k hkn
  unfold clauseLaw
  infer_instance

lemma streamLaw_probability (n k : ℕ) (hkn : k ≤ n) :
    IsProbabilityMeasure (streamLaw n k) := by
  let := clauseLaw_probability n k hkn
  unfold streamLaw
  infer_instance

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.FirstFailure ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma measurable_H (n k : ℕ) : Measurable (H : Stream n k → ℝ) :=
  (measurable_of_countable (fun x : ℕ∞ => (x.toNat : ℝ))).comp (measurable_firstFailure n k)

lemma measurable_T (n k : ℕ) (B : ℝ) : Measurable (T B : Stream n k → ℝ) :=
  (measurable_of_countable (fun x : ℕ∞ => ((min x (cap n B : ℕ∞)).toNat : ℝ))).comp
    (measurable_firstFailure n k)

lemma T_nonneg {n k : ℕ} (B : ℝ) (ω : Stream n k) : 0 ≤ T B ω := by
  unfold T
  positivity

lemma T_le_cap {n k : ℕ} (B : ℝ) (ω : Stream n k) : T B ω ≤ cap n B := by
  unfold T
  exact_mod_cast ENat.toNat_le_of_le_natCast (min_le_right (firstFailure ω) (cap n B : ℕ∞))

lemma T_memLp {n k : ℕ} (hkn : k ≤ n) (B : ℝ) (p : ℝ≥0∞) :
    MemLp (T B : Stream n k → ℝ) p (streamLaw n k) := by
  let := streamLaw_probability n k hkn
  apply MemLp.of_bound (measurable_T n k B).aestronglyMeasurable (cap n B)
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (T_nonneg B ω)]
  exact T_le_cap B ω

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.MarkovReplacement ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma favg_mono.{u_1} {α : Type u_1} [Fintype α] {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    favg f ≤ favg g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => h a) (by positivity)

lemma favg_const.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (c : ℝ) :
    favg (fun _ : α => c) = c := by
  simp [favg, Fintype.card_ne_zero]

lemma favg_add.{u_1} {α : Type u_1} [Fintype α] (f g : α → ℝ) :
    favg (fun a => f a + g a) = favg f + favg g := by
  simp only [favg, Finset.sum_add_distrib, add_div]

lemma favg_sub.{u_1} {α : Type u_1} [Fintype α] (f g : α → ℝ) :
    favg (fun a => f a - g a) = favg f - favg g := by
  simp only [favg, Finset.sum_sub_distrib, sub_div]

lemma prefixLaw {u s : ℕ} (hsu : s ≤ u) (m : ℕ) :
    (streamLaw u s).map (fun ω (i : Fin m) => ω i) =
      uniformOn (Set.univ : Set (Fin m → Clause u s)) := by
  let := clauseLaw_probability u s hsu
  rw [streamLaw, Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective,
    Measure.infinitePi_eq_pi]
  simpa only [Set.pi_univ, clauseLaw] using
    (uniformOn_pi (f := fun _ : Fin m => (Set.univ : Set (Clause u s)))).symm

lemma favg_mul.{u_1} {α : Type u_1} [Fintype α] (c : ℝ) (f : α → ℝ) :
    favg (fun a => c*f a) = c*favg f := by
  simp only [favg, ← Finset.mul_sum]
  ring

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.Moments ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma real_rate_pos {k : ℕ} (hk : 1 ≤ k) : 0 < 1-((2 : ℝ)^k)⁻¹ := by
  have hp : (2 : ℝ) ≤ (2 : ℝ)^k := by
    simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk)
  exact sub_pos.mpr ((inv_lt_one₀ (by positivity)).mpr (by linarith))

lemma real_rate_lt_one (k : ℕ) : 1-((2 : ℝ)^k)⁻¹ < 1 := by
  have h : 0 < ((2 : ℝ)^k)⁻¹ := by positivity
  linarith

lemma measurable_natH (n k : ℕ) :
    Measurable (fun ω : Stream n k => (firstFailure ω).toNat) :=
  (measurable_of_countable fun x : ℕ∞ => x.toNat).comp (measurable_firstFailure n k)

lemma H_integrable_pow {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (p : ℕ) :
    Integrable (fun ω : Stream n k => (H ω)^p) (streamLaw n k) := by
  let := streamLaw_probability n k hkn
  let ν := (streamLaw n k).map (fun ω => (firstFailure ω).toNat)
  have hp : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (measurable_natH n k).aemeasurable
  let q := 1-((2 : ℝ)^k)⁻¹
  have hq := real_rate_pos hk
  have hqNorm : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hq]; exact real_rate_lt_one k
  have hs : Summable (fun m : ℕ => (ν {m}).toReal * ‖(m : ℝ)^p‖) := by
    apply Summable.of_nonneg_of_le (fun _ => by positivity) _
      ((summable_pow_mul_geometric_of_norm_lt_one p hqNorm).mul_left ((2 : ℝ)^n/q))
    intro m
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ)^p)]
    calc
      _ ≤ (((2 : ℝ)^n/q)*q^m)*(m : ℝ)^p :=
        mul_le_mul_of_nonneg_right (natH_mass_bound hk hkn m) (by positivity)
      _ = _ := by ring
  have hi : Integrable (fun m : ℕ => (m : ℝ)^p) ν := by
    rw [← Measure.sum_smul_dirac ν]
    exact integrable_sum_dirac (fun _ => measure_ne_top _ _) hs
  exact hi.comp_measurable (measurable_natH n k)

lemma H_memLp_two {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    MemLp (H : Stream n k → ℝ) 2 (streamLaw n k) :=
  (memLp_two_iff_integrable_sq (measurable_H n k).aestronglyMeasurable).mpr
    (H_integrable_pow hk hkn 2)

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.FiniteVariance ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma favg_sq_sub_const.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (f : α → ℝ) (c : ℝ) :
    favg (fun a => (f a-c)^2) = favg (fun a => (f a)^2) - 2*c*favg f + c^2 := by
  have he : (fun a => (f a-c)^2) = (fun a => (f a)^2 - (2*c)*f a + c^2) := by
    funext a; ring
  rw [he, favg_add, favg_sub, favg_mul, favg_const]

lemma fvariance_centered.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (f : α → ℝ) :
    fvariance f = favg (fun a => (f a-favg f)^2) := by
  rw [favg_sq_sub_const, fvariance]; ring

lemma fvariance_le_sq_sub.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (f : α → ℝ) (c : ℝ) :
    fvariance f ≤ favg (fun a => (f a-c)^2) := by
  rw [favg_sq_sub_const, fvariance]
  nlinarith [sq_nonneg (favg f-c)]

lemma integral_uniform.{u_1} {α : Type u_1} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (f : α → ℝ) :
    ∫ a, f a ∂uniformOn Set.univ = favg f := by
  rw [integral_fintype Integrable.of_finite]
  simp only [measureReal_def, uniformOn_univ, Measure.count_singleton,
    one_div, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul,
    ← Finset.mul_sum, favg]
  ring

lemma variance_uniform.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (f : α → ℝ) :
    ProbabilityTheory.variance f (uniformOn Set.univ) = fvariance f := by
  have hm : MemLp f 2 (uniformOn Set.univ) :=
    (memLp_two_iff_integrable_sq (measurable_of_countable f).aestronglyMeasurable).mpr
      Integrable.of_finite
  rw [variance_eq_sub hm, integral_uniform, integral_uniform]
  rfl

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.CappedUpper ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma ell_eq_of_three {n : ℕ} (hn : 1 ≤ n) : ell 3 n = 1+Real.log n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  simp [ell, Real.log_mul (Real.exp_ne_zero _) hn0]

lemma ell_one_le (k n : ℕ) (hn : 1 ≤ n) : 1 ≤ ell k n := by
  by_cases hk : k = 3
  · subst k
    rw [ell_eq_of_three hn]
    have hh := Real.log_nonneg (show (1 : ℝ) ≤ n by exact_mod_cast hn)
    linarith
  · simp [ell, hk]

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.CapBridge ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma T_eq_min_natH_ae {n k : ℕ} (hkn : k ≤ n) (B : ℝ) :
    ∀ᵐ ω ∂streamLaw n k, T B ω = ((min (firstFailure ω).toNat (cap n B) : ℕ) : ℝ) := by
  filter_upwards [firstFailure_finite_ae hkn] with ω hω
  have he := ENat.natCast_toNat (ne_of_lt hω)
  by_cases h : (firstFailure ω).toNat ≤ cap n B
  · have hEN : firstFailure ω ≤ (cap n B : ℕ∞) := by rw [← he]; exact_mod_cast h
    simp only [T, min_eq_left hEN, min_eq_left h]
  · have hEN : (cap n B : ℕ∞) ≤ firstFailure ω := by rw [← he]; exact_mod_cast (le_of_not_ge h)
    simp only [T, min_eq_right hEN, min_eq_right (le_of_not_ge h), ENat.toNat_natCast]

lemma cap_error_eq_nat_ae {n k : ℕ} (hkn : k ≤ n) (B : ℝ) :
    ∀ᵐ ω ∂streamLaw n k, (H ω-T B ω)^2 = (((firstFailure ω).toNat-cap n B : ℕ) : ℝ)^2 := by
  filter_upwards [T_eq_min_natH_ae hkn B] with ω hω
  rw [hω, H, ← Nat.cast_sub (Nat.min_le_left _ _)]
  congr 2
  omega

lemma natH_integral {n k : ℕ} (hkn : k ≤ n) (f : ℕ → ℝ) :
    (∫ ω, f (firstFailure ω).toNat ∂streamLaw n k) =
      ∑' m, ((streamLaw n k).map (fun ω => (firstFailure ω).toNat) {m}).toReal * f m := by
  let := streamLaw_probability n k hkn
  rw [← integral_map (measurable_natH n k).aemeasurable
    (measurable_of_countable f).aestronglyMeasurable]
  conv_lhs => rw [
    ← Measure.sum_smul_dirac ((streamLaw n k).map (fun ω => (firstFailure ω).toNat)),
    integral_sum_dirac (fun _ => measure_ne_top _ _)]
  rfl

lemma summable_sub_sq_geometric {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (M : ℕ) :
    Summable (fun m : ℕ => ((m-M : ℕ) : ℝ)^2*q^m) := by
  have hn : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq] using hq1
  apply Summable.of_nonneg_of_le (fun m => by positivity) _
    (summable_pow_mul_geometric_of_norm_lt_one 2 hn)
  intro m
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity)
    (by exact_mod_cast Nat.sub_le m M) 2) (pow_nonneg hq m)

lemma tsum_sub_sq_geometric {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (M : ℕ) :
    (∑' m : ℕ, ((m-M : ℕ) : ℝ)^2*q^m) = q^M * ∑' j : ℕ, (j : ℝ)^2*q^j := by
  have hs := summable_sub_sq_geometric hq hq1 M
  have he := hs.sum_add_tsum_nat_add M
  have hz : ∑ m ∈ Finset.range M, ((m-M : ℕ) : ℝ)^2*q^m = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    simp only [Nat.sub_eq_zero_of_le (le_of_lt (Finset.mem_range.mp hm)),
      Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
  rw [hz, zero_add] at he
  rw [← he, ← tsum_mul_left]
  apply tsum_congr
  intro j
  rw [Nat.add_sub_cancel, pow_add]
  ring

lemma cap_error_geom {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (B : ℝ) :
    (∫ ω : Stream n k, (H ω-T B ω)^2 ∂streamLaw n k) ≤
      ((2 : ℝ)^n * (1-((2 : ℝ)^k)⁻¹)^(cap n B)) /
        (1-((2 : ℝ)^k)⁻¹) * ∑' j : ℕ, (j : ℝ)^2*(1-((2 : ℝ)^k)⁻¹)^j := by
  let q := 1-((2 : ℝ)^k)⁻¹
  have hq : 0 < q := real_rate_pos hk
  have hq1 : q < 1 := real_rate_lt_one k
  rw [integral_congr_ae (cap_error_eq_nat_ae hkn B),
    natH_integral hkn (fun m => (((m-cap n B : ℕ) : ℝ)^2))]
  have hb (m : ℕ) := mul_le_mul_of_nonneg_right (natH_mass_bound hk hkn m)
    (sq_nonneg (((m-cap n B : ℕ) : ℝ)))
  have hs := (summable_sub_sq_geometric hq.le hq1 (cap n B)).mul_left ((2 : ℝ)^n/q)
  have ht : Summable (fun m : ℕ =>
      ((streamLaw n k).map (fun ω => (firstFailure ω).toNat) {m}).toReal *
      (((m-cap n B : ℕ) : ℝ)^2)) := by
    apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hs
    intro m
    calc
      _ ≤ (((2 : ℝ)^n/q)*q^m)*(((m-cap n B : ℕ) : ℝ)^2) := hb m
      _ = _ := by ring
  calc
    _ ≤ ∑' m : ℕ, ((2 : ℝ)^n/q)*((((m-cap n B : ℕ) : ℝ)^2)*q^m) := by
      apply ht.tsum_le_tsum _ hs
      intro m
      convert hb m using 1
      dsimp [q]
      ring
    _ = _ := by rw [tsum_mul_left, tsum_sub_sq_geometric hq.le hq1]; dsimp [q]; ring

lemma U_pos {k : ℕ} (hk : 1 ≤ k) : 0 < U k := by
  have hq := real_rate_pos hk
  have hq1 := real_rate_lt_one k
  exact div_pos (Real.log_pos (by norm_num)) (neg_pos.mpr (Real.log_neg hq hq1))

lemma cap_geometric_uniform {k : ℕ} (hk : 1 ≤ k) {B : ℝ} (hB : U k ≤ B) (n : ℕ) :
    (2 : ℝ)^n * (1-((2 : ℝ)^k)⁻¹)^(cap n B) ≤ (1-((2 : ℝ)^k)⁻¹)⁻¹ := by
  let q := 1-((2 : ℝ)^k)⁻¹
  have hq : 0 < q := real_rate_pos hk
  have hl : Real.log q < 0 := Real.log_neg hq (real_rate_lt_one k)
  have ht : Real.log 2 ≤ B*(-Real.log q) := (div_le_iff₀ (by linarith)).mp hB
  have hf : B*n < (cap n B : ℝ)+1 := Nat.lt_floor_add_one _
  apply (Real.log_le_log_iff (mul_pos (by positivity) (pow_pos hq _)) (inv_pos.mpr hq)).mp
  rw [Real.log_mul (by positivity) (ne_of_gt (pow_pos hq _)), Real.log_pow, Real.log_pow,
    Real.log_inv]
  have hh := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  change _ ≤ -Real.log q
  nlinarith

lemma bridgeC_nonneg {k : ℕ} (hk : 1 ≤ k) : 0 ≤ bridgeC k := by
  unfold bridgeC
  exact mul_nonneg (sq_nonneg _) (tsum_nonneg (fun j => by positivity [real_rate_pos hk]))

lemma cap_error_uniform {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) {B : ℝ} (hB : U k ≤ B) :
    (∫ ω : Stream n k, (H ω-T B ω)^2 ∂streamLaw n k) ≤ bridgeC k := by
  have hq := real_rate_pos hk
  have hb := cap_error_geom hk hkn B
  have hz : 0 ≤ ∑' j : ℕ, (j : ℝ)^2*(1-((2 : ℝ)^k)⁻¹)^j :=
    tsum_nonneg (fun _ => by positivity)
  have hh := mul_le_mul_of_nonneg_right
    ((div_le_div_iff_of_pos_right hq).mpr (cap_geometric_uniform hk hB n)) hz
  apply hb.trans
  convert hh using 1
  dsimp [bridgeC]
  ring

lemma H_variance_le_cap {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) {B : ℝ} (hB : U k ≤ B) :
    variance (H : Stream n k → ℝ) (streamLaw n k) ≤
      2*variance (T B : Stream n k → ℝ) (streamLaw n k)+2*bridgeC k := by
  let := streamLaw_probability n k hkn
  exact (variance_bridge (H_memLp_two hk hkn) (T_memLp hkn B 2)).trans
    (by linarith [cap_error_uniform hk hkn hB])

lemma cap_variance_le_H {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) {B : ℝ} (hB : U k ≤ B) :
    variance (T B : Stream n k → ℝ) (streamLaw n k) ≤
      2*variance (H : Stream n k → ℝ) (streamLaw n k)+2*bridgeC k := by
  let := streamLaw_probability n k hkn
  have hh := variance_bridge (T_memLp hkn B 2) (H_memLp_two hk hkn)
  have he : (∫ ω : Stream n k, (T B ω-H ω)^2 ∂streamLaw n k) =
      ∫ ω : Stream n k, (H ω-T B ω)^2 ∂streamLaw n k := by
    congr 1
    funext ω
    ring
  rw [he] at hh
  exact hh.trans (by linarith [cap_error_uniform hk hkn hB])

theorem uncapped_variance_upper (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, k ≤ n →
      variance (H : Stream n k → ℝ) (streamLaw n k) ≤ C*n*ell k n := by
  have hk1 : 1 ≤ k := by omega
  obtain ⟨C,hC,hv⟩ := capped_variance_upper k hk (U k) (U_pos hk1)
  refine ⟨2*C+2*bridgeC k, by positivity [bridgeC_nonneg hk1], fun n hkn => ?_⟩
  have hh := H_variance_le_cap hk1 hkn (le_refl (U k))
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (hk1.trans hkn)
  have he := ell_one_le k n (hk1.trans hkn)
  have hb := bridgeC_nonneg hk1
  have hm : 1 ≤ (n : ℝ)*ell k n := by nlinarith
  have hm' := mul_le_mul_of_nonneg_left hm hb
  nlinarith [hv n hkn]

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.BystanderStops ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma listStop_le {n k : ℕ} (l : List (Clause n k)) : listStop l ≤ l.length+1 :=
  Nat.find_min' _ (Or.inl rfl)

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.SentinelBridge ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma mem_take_ofFn.{u_1} {α : Type u_1} {M m : ℕ} (w : Fin M → α) (c : α) :
    c ∈ (List.ofFn w).take m ↔ ∃ i : Fin M, i.val < m ∧ w i = c := by
  rw [List.mem_take_iff_getElem]
  constructor
  · rintro ⟨j,hj,he⟩
    have hj' : j < min m M := by simpa only [List.length_ofFn] using hj
    refine ⟨⟨j,lt_of_lt_of_le hj' (min_le_right _ _)⟩,lt_of_lt_of_le hj' (min_le_left _ _),?_⟩
    simpa only [List.getElem_ofFn] using he
  · rintro ⟨i,hi,he⟩
    refine ⟨i.val,?_,?_⟩
    · simpa only [List.length_ofFn,lt_min_iff] using And.intro hi i.isLt
    · simpa only [List.getElem_ofFn] using he

lemma listSAT_take_ofFn {n k M m : ℕ} (w : Fin M → Clause n k) :
    listSAT ((List.ofFn w).take m) ↔ finiteSAT w m := by
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a,fun i hi => ha (w i) ((mem_take_ofFn w _).mpr ⟨i,hi,rfl⟩)⟩
  · rintro ⟨a,ha⟩
    refine ⟨a,fun c hc => ?_⟩
    obtain ⟨i,hi,rfl⟩ := (mem_take_ofFn w c).mp hc
    exact ha i hi

lemma lt_listStop_ofFn_iff {n k M m : ℕ} (w : Fin M → Clause n k) (hm : m ≤ M) :
    m < listStop (List.ofFn w) ↔ finiteSAT w m := by
  rw [lt_listStop_iff,List.length_ofFn,and_iff_right hm,listSAT_take_ofFn]

lemma listStop_eq_finiteTime {n k M : ℕ} (w : Fin M → Clause n k) :
    (listStop (List.ofFn w):ℝ) = finiteTime w + if finiteSAT w M then 1 else 0 := by
  have hs : listStop (List.ofFn w) ≤ M+1 := by simpa only [List.length_ofFn] using listStop_le (List.ofFn w)
  have hh (i : Fin (M+1)) : i.val < listStop (List.ofFn w) ↔ finiteSAT w i.val :=
    lt_listStop_ofFn_iff w (by omega)
  rw [← sum_fin_indicator_lt hs]
  simp only [hh]
  rw [Fin.sum_univ_castSucc]
  rfl

lemma sentinel_error {n k M : ℕ} (w : Fin M → Clause n k) :
    ((listStop (List.ofFn w):ℝ)-finiteTime w)^2 ≤ 1 := by
  rw [listStop_eq_finiteTime]
  split_ifs <;> norm_num

lemma fvariance_bridge.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (f g : α → ℝ) :
    fvariance f ≤ 2*fvariance g+2*favg (fun a => (f a-g a)^2) := by
  apply (fvariance_le_sq_sub f (favg g)).trans
  have hh := favg_mono (fun a : α => show (f a-favg g)^2 ≤ 2*(g a-favg g)^2+2*(f a-g a)^2 by
    nlinarith [sq_nonneg ((g a-favg g)-(f a-g a))])
  rw [favg_add,favg_mul,favg_mul,←fvariance_centered] at hh
  exact hh

lemma sentinel_variance_bridge {n k M : ℕ} [Nonempty (Clause n k)] :
    fvariance (fun w : Fin M → Clause n k => (listStop (List.ofFn w):ℝ)) ≤
      2*fvariance (finiteTime (n := n) (k := k) (L := M))+2 := by
  apply (fvariance_bridge _ _).trans
  have hh := favg_mono (fun w : Fin M → Clause n k => sentinel_error w)
  rw [favg_const] at hh
  linarith

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.FailureWindows ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
private theorem Measurable.of_eval {α δ : Type*} {X : δ → Type*}
    [MeasurableSpace α] [∀ a, MeasurableSpace (X a)] {f : α → ∀ a, X a}
    (hf : ∀ a, Measurable fun c => f c a) : Measurable f :=
  measurable_pi_lambda f hf
end Lean433MeasurableOfEval

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma cap_variance_finite {n k : ℕ} (hkn : k ≤ n) (B : ℝ) :
    variance (T B : Stream n k → ℝ) (streamLaw n k) =
      fvariance (finiteTime (n := n) (k := k) (L := cap n B)) := by
  let := clause_nonempty n k hkn
  have hm : Measurable (fun ω : Stream n k => fun j : Fin (cap n B) => ω j) :=
    Measurable.of_eval (fun j => measurable_pi_apply j.val)
  have he : (T B : Stream n k → ℝ) =
      finiteTime ∘ (fun ω : Stream n k => fun j : Fin (cap n B) => ω j) := by
    funext ω
    exact (finiteTime_stream ω).symm
  rw [he, ← variance_map (measurable_of_countable finiteTime).aemeasurable hm.aemeasurable,
    prefixLaw hkn,variance_uniform]

lemma positive_linear_absorb (d : ℝ) (hd : 0 < d) (K : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K ≤ d*n := by
  obtain ⟨N,hN⟩ := exists_nat_gt (K/d)
  refine ⟨N,fun n hn => ?_⟩
  have hN' : (N:ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [(div_lt_iff₀ hd).mp (hN.trans_le hN')]

lemma eventual_geometric_small {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    {ε : ℝ} (hε : 0 < ε) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → r^n ≤ ε := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1
  have he : ∀ᶠ n : ℕ in Filter.atTop, r^n < ε := ht.eventually (gt_mem_nhds hε)
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp he
  exact ⟨N,fun n hn => (hN n hn).le⟩

lemma exists_lower_density {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ Real.exp 2*a ≤ 1/2 ∧ 2*a ≤ β/4 := by
  let a := β/(16*Real.exp 2)
  have he : 0 < Real.exp (2:ℝ) := Real.exp_pos _
  have he1 : 1 ≤ Real.exp (2:ℝ) := Real.one_le_exp (by norm_num)
  have ha : 0 < a := by dsimp [a]; positivity
  have hA : a ≤ β/16 := by
    change β/(16*Real.exp 2) ≤ β/16
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 16*Real.exp 2)).mpr
    nlinarith [mul_le_mul_of_nonneg_left he1 hβ.le]
  have hE : Real.exp 2*a = β/16 := by dsimp [a]; field_simp
  refine ⟨a,ha,by linarith,by rw [hE]; linarith,by linarith⟩

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.LinearLower ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

theorem fixed_cap_variance_lower (k : ℕ) (hk : 3 ≤ k) :
    ∃ B : ℝ, U k ≤ B ∧ ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n → k ≤ n →
        c*n ≤ variance (T B : Stream n k → ℝ) (streamLaw n k) := by
  obtain ⟨R,hR,hRU,hRq⟩ := exists_lower_scale k (by omega)
  let β := Real.exp (-4*(R:ℝ)*k^2)
  have hβ : 0 < β := Real.exp_pos _
  have hβ1 : β ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have : (0:ℝ) ≤ R := by positivity
    nlinarith [sq_nonneg (k:ℝ)]
  obtain ⟨a,ha,ha1,haHall,haβ⟩ := exists_lower_density hβ hβ1
  let d := (a/(16*((2*R:ℕ)+1:ℝ)^2))*a*β/16
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨Ng,hNg⟩ := eventual_geometric_small
    (by positivity [real_rate_pos (by omega : 1 ≤ k)] : 0 ≤ 2*(1-((2:ℝ)^k)⁻¹)^R)
    hRq (show 0 < β/4 by positivity)
  obtain ⟨Na,hNa⟩ := positive_linear_absorb a ha 8
  obtain ⟨Nd,hNd⟩ := positive_linear_absorb d hd 4
  refine ⟨2*(R:ℝ),hRU,d/4,by positivity,max (2*k^2) (max Ng (max Na Nd)),?_⟩
  intro n hn hkn
  have hn2 : 2*k^2 ≤ n := by omega
  have hng : Ng ≤ n := by omega
  have hna : Na ≤ n := by omega
  have hnd : Nd ≤ n := by omega
  let := clause_nonempty n k hkn
  have hs := sentinel_linear_lower (by omega : 2 ≤ k) hkn hR hn2 ha ha1 haHall haβ
    (hNa n hna) (hNg n hng)
  change d*n ≤ fvariance (fun w : Fin (2*R*n) → Clause n k => (listStop (List.ofFn w):ℝ)) at hs
  have hb := sentinel_variance_bridge (n := n) (k := k) (M := 2*R*n)
  have hcap : cap n (2*(R:ℝ)) = 2*R*n := by
    have he : 2*(R:ℝ)*n = ((2*R*n:ℕ):ℝ) := by
      simp only [Nat.cast_mul,Nat.cast_ofNat]
    simp only [cap,he,Nat.floor_natCast]
  have hv := cap_variance_finite hkn (2*(R:ℝ))
  rw [hcap] at hv
  rw [←hv] at hb
  have hdn := hNd n hnd
  nlinarith

theorem variance_linear_lower (k : ℕ) (hk : 3 ≤ k) :
    ∃ c : ℝ, 0 < c ∧
      (∃ N : ℕ, ∀ n : ℕ, N ≤ n → k ≤ n →
        c*n ≤ variance (H : Stream n k → ℝ) (streamLaw n k)) ∧
      (∀ B : ℝ, U k < B → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → k ≤ n →
        c*n ≤ variance (T B : Stream n k → ℝ) (streamLaw n k)) := by
  obtain ⟨B₀,hB₀,c₀,hc₀,N₀,hN₀⟩ := fixed_cap_variance_lower k hk
  have hk1 : 1 ≤ k := by omega
  have hK := bridgeC_nonneg hk1
  obtain ⟨N₁,hN₁⟩ := positive_linear_absorb c₀ hc₀ (12*bridgeC k)
  refine ⟨c₀/8,by positivity,?_,?_⟩
  · refine ⟨max N₀ N₁,fun n hn hkn => ?_⟩
    have hl := hN₀ n (by omega) hkn
    have ha := hN₁ n (by omega)
    have hv := cap_variance_le_H hk1 hkn hB₀
    have hn0 : (0:ℝ) ≤ n := by positivity
    nlinarith
  · intro B hB
    refine ⟨max N₀ N₁,fun n hn hkn => ?_⟩
    have hl := hN₀ n (by omega) hkn
    have ha := hN₁ n (by omega)
    have hv := cap_variance_le_H hk1 hkn hB₀
    have hv' := H_variance_le_cap hk1 hkn hB.le
    nlinarith

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.Main ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

theorem variance_main (k : ℕ) (hk : 3 ≤ k) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, k ≤ n →
      variance (H : Stream n k → ℝ) (streamLaw n k) ≤ C * n * ell k n) ∧
    (∀ B : ℝ, 0 < B → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, k ≤ n →
      variance (T B : Stream n k → ℝ) (streamLaw n k) ≤ C * n * ell k n) ∧
    (∃ c : ℝ, 0 < c ∧
      (∃ N : ℕ, ∀ n : ℕ, N ≤ n → k ≤ n →
        c * n ≤ variance (H : Stream n k → ℝ) (streamLaw n k)) ∧
      (∀ B : ℝ, U k < B → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → k ≤ n →
        c * n ≤ variance (T B : Stream n k → ℝ) (streamLaw n k))) := by
  exact ⟨uncapped_variance_upper k hk, capped_variance_upper k hk, variance_linear_lower k hk⟩

end RandomKSAT

end

end OAI

-- ---- mission target ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem solution (k : ℕ) (hk : 3 ≤ k) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, k ≤ n →
      variance (H : Stream n k → ℝ) (streamLaw n k) ≤ C * n * ell k n) ∧
    (∀ B : ℝ, 0 < B → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, k ≤ n →
      variance (T B : Stream n k → ℝ) (streamLaw n k) ≤ C * n * ell k n) ∧
    (∃ c : ℝ, 0 < c ∧
      (∃ N : ℕ, ∀ n : ℕ, N ≤ n → k ≤ n →
        c * n ≤ variance (H : Stream n k → ℝ) (streamLaw n k)) ∧
      (∀ B : ℝ, U k < B → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → k ≤ n →
        c * n ≤ variance (T B : Stream n k → ℝ) (streamLaw n k))) := by
  first
    | exact OAI.RandomKSAT.variance_main k hk
    | exact OAI.RandomKSAT.variance_main
    | (apply OAI.RandomKSAT.variance_main <;> assumption)
    | (intros; apply OAI.RandomKSAT.variance_main <;> assumption)
