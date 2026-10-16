-- Prove2me | solution 1 for OAI.RandomKSAT.replacement_scaled_limit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T15:42:41.078904+00:00
-- url     : https://prove2.me/submissions/1cb8bb42-ddd4-435a-be51-868f29752fb5

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/ReplacementSharpness.lean:L19-L65
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.replacement_scaled_limit. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SATSharpness
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration
import Definitions.Def_OAI_Probability_SATVariance_SupportProbabilities
import Definitions.Def_OAI_Probability_SATVariance_Subcube
import Theorems.Thm_OAI_RandomKSAT_blockKill_individual
import Theorems.Thm_OAI_RandomKSAT_killRatio_limit
import Theorems.Thm_OAI_RandomKSAT_subcube_block_upper

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

lemma killing_card {n k : ℕ} {S : Finset (Assignment n)} (hS : S.Nonempty) :
    Fintype.card {c : Clause n k // Kills S c} = (frozen S).card.choose k := by
  classical
  obtain ⟨a₀, ha₀⟩ := hS
  rw [Fintype.card_congr (killingEquiv ha₀)]
  rw [Fintype.card_of_subtype ((frozen S).powersetCard k) (by intro s; simp)]
  exact Finset.card_powersetCard _ _

lemma count_set_fintype.{u_1} {α : Type u_1} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype α] (s : Set α) :
    Measure.count s = (Fintype.card s : ℝ≥0∞) := by
  rw [Measure.count_apply (Set.toFinite s).measurableSet,
    Set.encard_eq_coe_toFinset_card]
  simp

lemma clauseLaw_kills {n k : ℕ} {S : Finset (Assignment n)} (hS : S.Nonempty) :
    clauseLaw n k {c | Kills S c} =
      ((frozen S).card.choose k : ℝ≥0∞) / ((n.choose k : ℝ≥0∞) * 2 ^ k) := by
  rw [clauseLaw, uniformOn_univ, count_set_fintype]
  have hc : Fintype.card ↑{c : Clause n k | Kills S c} = (frozen S).card.choose k := by
    simpa only [Fintype.card_subtype, Set.mem_ofPred_eq] using (killing_card hS)
  rw [hc, clause_card]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.FrozenReplacement ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma killRatio_nonneg (u b s : ℕ) : 0 ≤ killRatio u b s := by
  unfold killRatio
  positivity

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.BlockKilling ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma blockKill_le_one {u s : ℕ} (hsu : s ≤ u) (S : Finset (Assignment u)) (g : ℕ) :
    blockKill u s S g ≤ 1 := by
  let := streamLaw_probability u s hsu
  exact measureReal_le_one (μ := streamLaw u s)

lemma clauseLaw_kills_toReal {u s : ℕ} {S : Finset (Assignment u)} (hS : S.Nonempty) :
    (clauseLaw u s {c | Kills S c}).toReal = killRatio u (frozen S).card s := by
  rw [clauseLaw_kills hS]
  simp [killRatio, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow, mul_comm]

lemma blockKill_one {u s : ℕ} (hsu : s ≤ u) {S : Finset (Assignment u)} (hS : S.Nonempty) :
    blockKill u s S 1 = killRatio u (frozen S).card s := by
  let := clauseLaw_probability u s hsu
  have he : {ω : Stream u s | ¬ SetSAT S ω 1} =
      Set.pi ({0} : Finset ℕ) (fun _ => {c : Clause u s | Kills S c}) := by
    ext ω
    simp [SetSAT, Kills]
  rw [blockKill, he, streamLaw, Measure.infinitePi_pi]
  · simpa using clauseLaw_kills_toReal hS
  · intro _ _
    exact (Set.toFinite _).measurableSet

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.Subcube ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal Topology

namespace RandomKSAT

lemma mem_subcube {u b : ℕ} {a : Assignment u} :
    a ∈ subcube u b ↔ ∀ v : Fin u, (v : ℕ) < b → a v = false := by
  simp [subcube]

lemma subcube_nonempty (u b : ℕ) : (subcube u b).Nonempty := by
  exact ⟨fun _ => false, mem_subcube.mpr (by simp)⟩

lemma frozen_subcube (u b : ℕ) :
    frozen (subcube u b) = Finset.univ.filter (fun v : Fin u => (v : ℕ) < b) := by
  ext v
  simp only [frozen, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    by_contra hn
    let a : Assignment u := fun w => if w = v then true else false
    have ha : a ∈ subcube u b := by
      apply mem_subcube.mpr
      intro w hw
      have hwv : w ≠ v := by rintro rfl; exact hn hw
      simp [a, hwv]
    have h0 : (fun _ : Fin u => false) ∈ subcube u b := mem_subcube.mpr (by simp)
    have hh := h _ h0 a ha
    simp [a] at hh
  · intro hv a ha c hc
    exact (mem_subcube.mp ha v hv).trans (mem_subcube.mp hc v hv).symm

lemma frozen_subcube_card {u b : ℕ} (hbu : b ≤ u) :
    (frozen (subcube u b)).card = b := by
  let e : {v : Fin u // (v : ℕ) < b} ≃ Fin b :=
    { toFun := fun v => ⟨v.1.val, v.2⟩
      invFun := fun v => ⟨⟨v.val, v.isLt.trans_le hbu⟩, v.isLt⟩
      left_inv := by intro v; rfl
      right_inv := by intro v; rfl }
  rw [frozen_subcube]
  simpa only [Fintype.card_subtype, Fintype.card_fin] using Fintype.card_congr e

lemma subcube_one {u b s : ℕ} (hbu : b ≤ u) (hsu : s ≤ u) :
    blockKill u s (subcube u b) 1 = killRatio u b s := by
  rw [blockKill_one hsu (subcube_nonempty u b), frozen_subcube_card hbu]

lemma bernoulli_quadratic {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) (t : ℕ) :
    (t : ℝ)*h - (t : ℝ)^2*h^2 ≤ 1 - (1-h)^t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hm := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr h1)
    have h3 := mul_nonneg (sq_nonneg (t : ℝ)) (pow_nonneg h0 3)
    have h2 := mul_nonneg (Nat.cast_nonneg (α := ℝ) t) (sq_nonneg h)
    rw [pow_succ (1-h) t]
    push_cast
    nlinarith [sq_nonneg h]

lemma subcube_block_lower {u b k : ℕ} (hbu : b ≤ u) (hku : k ≤ u) (t : ℕ) :
    (t : ℝ) * killRatio u b k - (t : ℝ)^2 * (killRatio u b k)^2 ≤
      blockKill u k (subcube u b) t := by
  have hh := blockKill_individual hku (subcube_nonempty u b) t
  rw [frozen_subcube_card hbu] at hh
  apply (bernoulli_quadratic (killRatio_nonneg u b k) ?_ t).trans hh
  rw [← subcube_one hbu hku]
  exact blockKill_le_one hku _ _

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.SharpnessEstimates ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal Topology

namespace RandomKSAT

lemma tendsto_nat_pow_real (m : ℕ) (hm : 0 < m) :
    Tendsto (fun N : ℕ => (N : ℝ)^m) atTop atTop :=
  (tendsto_pow_atTop (Nat.ne_of_gt hm)).comp tendsto_natCast_atTop_atTop

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.ReplacementSharpness ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal Topology

namespace RandomKSAT

lemma sharp_parameters {k g : ℕ} (hg : 2 ≤ g) :
    g^(k+1) ≤ g^(k+2) ∧ k ≤ g^(k+1) ∧ 0 < g^(k+2) := by
  refine ⟨?_, ?_, by positivity⟩
  · exact Nat.pow_le_pow_right (by omega) (by omega)
  · exact (Nat.le_of_lt Nat.lt_two_pow_self).trans
      ((Nat.pow_le_pow_left hg k).trans (Nat.pow_le_pow_right (by omega) (by omega)))

lemma replacement_scaled_limit (k : ℕ) (hk : 3 ≤ k) :
    Tendsto (fun g : ℕ => (g : ℝ)^(k-1) * blockKill (g^(k+2)) k
      (subcube (g^(k+2)) (g^(k+1))) g) atTop (𝓝 (((2 : ℝ)^k)⁻¹)) := by
  let h := fun g : ℕ => killRatio (g^(k+2)) (g^(k+1)) k
  have hlim : Tendsto (fun g : ℕ => (g : ℝ)^k * h g) atTop (𝓝 (((2 : ℝ)^k)⁻¹)) :=
    killRatio_limit (by omega : 0 < k+1) k
  have elo : Tendsto (fun g : ℕ => ((g : ℝ)^k * h g)^2 / (g : ℝ)^(k-1))
      atTop (𝓝 0) := (hlim.pow 2).div_atTop (tendsto_nat_pow_real (k-1) (by omega))
  have elo' : Tendsto (fun g : ℕ => (g : ℝ)^k * h g - ((g : ℝ)^k * h g)^2 / (g : ℝ)^(k-1))
      atTop (𝓝 (((2 : ℝ)^k)⁻¹)) := by simpa using hlim.sub elo
  have eup : Tendsto (fun g : ℕ => (g : ℝ)^k * h g + (k : ℝ)^2 / g)
      atTop (𝓝 (((2 : ℝ)^k)⁻¹)) := by
    simpa using hlim.add (tendsto_const_div_atTop_nhds_zero_nat ((k : ℝ)^2))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' elo' eup
  · filter_upwards [eventually_ge_atTop 2] with g hg
    obtain ⟨hbu, hkb, hu⟩ := sharp_parameters (k := k) hg
    have hl := mul_le_mul_of_nonneg_left (subcube_block_lower hbu (hkb.trans hbu) g)
      (pow_nonneg (Nat.cast_nonneg g) (k-1))
    have he : (g : ℝ)^(k-1) * ((g : ℝ) * h g - (g : ℝ)^2 * (h g)^2) =
        (g : ℝ)^k * h g - ((g : ℝ)^k * h g)^2 / (g : ℝ)^(k-1) := by
      have hg0 : (g : ℝ) ≠ 0 := by positivity
      have hk' : k = (k-1)+1 := by omega
      have hpow : (g : ℝ)^k = (g : ℝ)^(k-1) * g := by
        conv_lhs => rw [hk']
        rw [pow_succ]
      rw [hpow]
      simp only [pow_succ]
      field_simp
    rwa [show killRatio (g^(k+2)) (g^(k+1)) k = h g from rfl, he] at hl
  · filter_upwards [eventually_ge_atTop 2] with g hg
    obtain ⟨hbu, hkb, hu⟩ := sharp_parameters (k := k) hg
    have hl := mul_le_mul_of_nonneg_left (subcube_block_upper hu hbu (hkb.trans hbu) g)
      (pow_nonneg (Nat.cast_nonneg g) (k-1))
    have he : (g : ℝ)^(k-1) * ((g : ℝ) * h g + (g : ℝ)^2 * (k : ℝ)^2 / (g^(k+2) : ℕ)) =
        (g : ℝ)^k * h g + (k : ℝ)^2 / g := by
      have hg0 : (g : ℝ) ≠ 0 := by positivity
      have hk' : k = (k-1)+1 := by omega
      have hk2 : k+2 = (k-1)+3 := by omega
      rw [hk2]
      have hpow : (g : ℝ)^k = (g : ℝ)^(k-1) * g := by
        conv_lhs => rw [hk']
        rw [pow_succ]
      rw [hpow]
      push_cast
      simp only [pow_succ]
      field_simp
    rwa [show killRatio (g^(k+2)) (g^(k+1)) k = h g from rfl, he] at hl

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal Topology


theorem solution : type_of% @_root_.OAI.RandomKSAT.replacement_scaled_limit := @_root_.OAI.RandomKSAT.replacement_scaled_limit
