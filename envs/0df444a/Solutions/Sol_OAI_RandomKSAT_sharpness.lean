-- Prove2me | solution 1 for OAI.RandomKSAT.sharpness
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T15:47:33.355626+00:00
-- url     : https://prove2.me/submissions/751389be-2916-41e6-86c2-2204df47ea1e

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/Sharpness.lean:L7-L21
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.RandomKSAT.sharpness.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_RandomKSAT_sharpness) verbatim and is proved by it.
import Mathlib
import Definitions.Def_SATSharpness
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration
import Definitions.Def_OAI_Probability_SATVariance_SupportProbabilities
import Definitions.Def_OAI_Probability_SATVariance_Subcube
import Theorems.Thm_OAI_RandomKSAT_killRatio_limit
import Theorems.Thm_OAI_RandomKSAT_lifetime_ge_survival
import Theorems.Thm_OAI_RandomKSAT_replacement_gap_scaled_limit
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

lemma killRatio_pos {u b s : ℕ} (hsb : s ≤ b) (hsu : s ≤ u) :
    0 < killRatio u b s := by
  unfold killRatio
  have hb : (0 : ℝ) < b.choose s := by exact_mod_cast Nat.choose_pos hsb
  have hu : (0 : ℝ) < u.choose s := by exact_mod_cast Nat.choose_pos hsu
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

-- ---- from OAI.Probability.SATVariance.LifetimeSharpness ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal Topology

namespace RandomKSAT

lemma lifetime_parameters {k N : ℕ} (hN : 2 ≤ N) :
    N^(2*k) ≤ N^(2*k+1) ∧ k ≤ N^(2*k) ∧ 0 < N^(2*k+1) := by
  refine ⟨Nat.pow_le_pow_right (by omega) (by omega), ?_, by positivity⟩
  exact (Nat.le_of_lt Nat.lt_two_pow_self).trans
    ((Nat.pow_le_pow_left hN k).trans (Nat.pow_le_pow_right (by omega) (by omega)))

lemma lifetime_subcube_eventually (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ)^k / 2 ≤
      lifetime (N^(2*k+1)) k (subcube (N^(2*k+1)) (N^(2*k))) := by
  have hh := (killRatio_limit (by omega : 0 < 2*k) k).add
    (tendsto_const_div_atTop_nhds_zero_nat ((k : ℝ)^2))
  simp only [add_zero] at hh
  have hC : ((2 : ℝ)^k)⁻¹ < (1/2 : ℝ) := by
    have h8 : (8 : ℝ) ≤ 2^k := by
      have hh8 := pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) hk
      norm_num at hh8 ⊢
      exact hh8
    rw [← one_div]
    apply (div_lt_div_iff₀ (by positivity) (by norm_num)).mpr
    nlinarith
  filter_upwards [eventually_ge_atTop 2, hh.eventually_lt_const hC] with N hN hsmall
  obtain ⟨hbu, hkb, hu⟩ := lifetime_parameters (k := k) hN
  have hbound := subcube_block_upper hu hbu (hkb.trans hbu) (N^k)
  have he : (N^k : ℕ) * killRatio (N^(2*k+1)) (N^(2*k)) k +
      ((N^k : ℕ) : ℝ)^2 * (k : ℝ)^2 / (N^(2*k+1) : ℕ) =
      (N : ℝ)^k * killRatio (N^(2*k+1)) (N^(2*k)) k + (k : ℝ)^2/N := by
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    push_cast
    rw [pow_succ, pow_mul]
    field_simp
    ring
  rw [he] at hbound
  have hhalf : (1/2 : ℝ) ≤ 1 - blockKill (N^(2*k+1)) k (subcube (N^(2*k+1)) (N^(2*k))) (N^k) := by
    linarith
  have ht := lifetime_ge_survival (hkb.trans hbu) (subcube (N^(2*k+1)) (N^(2*k))) (N^k)
  push_cast at ht
  calc
    _ = (N : ℝ)^k * (1/2) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hhalf (pow_nonneg (Nat.cast_nonneg N) k)).trans ht

lemma killing_above_scale {m r : ℕ} (hm : 0 < m) (hr : 0 < r) :
    Tendsto (fun N : ℕ => killRatio (N^(m+1)) (N^m) r * ((N^(m+1) : ℕ) : ℝ)^r)
      atTop atTop := by
  have hh := (tendsto_nat_pow_real (m*r) (by positivity)).atTop_mul_pos
    (by positivity : (0 : ℝ) < ((2 : ℝ)^r)⁻¹) (killRatio_limit hm r)
  apply hh.congr'
  filter_upwards [] with N
  push_cast
  calc
    _ = (N : ℝ)^(m*r+r) * killRatio (N^(m+1)) (N^m) r := by rw [pow_add]; ring
    _ = _ := by rw [show m*r+r = (m+1)*r by ring, pow_mul]; ring

lemma rpow_rescaling {x q : ℝ} (hx : 0 < x) (hq : 0 ≤ q) (k r : ℕ) (γ : ℝ) :
    x^((k : ℝ) - (r : ℝ)*γ) * (x^r*q)^γ = x^k * q^γ := by
  rw [Real.mul_rpow (pow_nonneg hx.le _) hq, ← Real.rpow_natCast_mul hx.le,
    ← mul_assoc, ← Real.rpow_add hx]
  simp only [sub_add_cancel, Real.rpow_natCast]

lemma lifetime_ratio_growth (k : ℕ) (hk : 3 ≤ k) (γ : ℝ)
    (hγ : γ < (k : ℝ)/((k-1 : ℕ) : ℝ)) :
    Tendsto (fun N : ℕ => (N : ℝ)^k / 2 * (killRatio (N^(2*k+1)) (N^(2*k)) (k-1))^γ)
      atTop atTop := by
  have hr : (0 : ℝ) < ((k-1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k-1)
  have hδ : 0 < (k : ℝ) - ((k-1 : ℕ) : ℝ)*γ := by
    have h := (lt_div_iff₀ hr).mp hγ
    nlinarith
  have hh := (killRatio_limit (by omega : 0 < 2*k) (k-1)).rpow_const (p := γ) (Or.inl (by positivity))
  have hp := ((tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop).atTop_mul_pos
    (Real.rpow_pos_of_pos (by positivity) γ) hh
  have hp' := Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1/2) hp
  apply hp'.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  simp only [Function.comp_apply]
  rw [rpow_rescaling (by positivity : (0 : ℝ) < N) (killRatio_nonneg _ _ _) k (k-1) γ]
  ring

theorem lifetime_sharp (k : ℕ) (hk : 3 ≤ k) (γ D A : ℝ)
    (hγ : γ < (k : ℝ) / ((k-1 : ℕ) : ℝ)) (_hD : 0 < D) (_hA : 0 < A) :
    ∀ N : ℕ, ∃ u : ℕ, N ≤ u ∧ k ≤ u ∧ ∃ S : Finset (Assignment u),
      S.Nonempty ∧ A * (u : ℝ) ^ (-((k-1 : ℕ) : ℝ)) ≤ blockKill u (k-1) S 1 ∧
      D * (blockKill u (k-1) S 1) ^ (-γ) < lifetime u k S := by
  intro M
  have ha := (killing_above_scale (by omega : 0 < 2*k) (by omega : 0 < k-1)).eventually_gt_atTop A
  have hd := (lifetime_ratio_growth k hk γ hγ).eventually_gt_atTop D
  obtain ⟨N, hN, hMN, ha, hd, ht⟩ :=
    ((eventually_ge_atTop 2).and ((eventually_ge_atTop M).and
      (ha.and (hd.and (lifetime_subcube_eventually k hk))))).exists
  obtain ⟨hbu, hkb, hu⟩ := lifetime_parameters (k := k) hN
  have hku := hkb.trans hbu
  have hru : k-1 ≤ N^(2*k+1) := by omega
  refine ⟨N^(2*k+1), hMN.trans (Nat.le_pow (by omega)), hku,
    subcube (N^(2*k+1)) (N^(2*k)), subcube_nonempty _ _, ?_, ?_⟩
  · rw [subcube_one hbu hru, Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv]
    exact (div_le_iff₀ (by positivity)).mpr ha.le
  · rw [subcube_one hbu hru]
    have hq : 0 < killRatio (N^(2*k+1)) (N^(2*k)) (k-1) := killRatio_pos (by omega) hru
    rw [Real.rpow_neg hq.le, ← div_eq_mul_inv]
    exact ((div_lt_iff₀ (Real.rpow_pos_of_pos hq γ)).mpr hd).trans_le ht

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

theorem replacement_sharp (k : ℕ) (hk : 3 ≤ k) :
    ∃ u : ℕ → ℕ, ∃ S : ∀ g, Finset (Assignment (u g)),
      (∀ g, 2 ≤ g → k ≤ u g ∧ (S g).Nonempty) ∧
      Asymptotics.IsEquivalent Filter.atTop
        (fun g => blockKill (u g) (k-1) (S g) 1 - blockKill (u g) k (S g) g)
        (fun g => ((2 : ℝ)^k)⁻¹ * (g : ℝ)^(-((k-1 : ℕ) : ℝ))) := by
  refine ⟨fun g => g^(k+2), fun g => subcube (g^(k+2)) (g^(k+1)), ?_, ?_⟩
  · intro g hg
    obtain ⟨hbu, hkb, hu⟩ := sharp_parameters (k := k) hg
    exact ⟨hkb.trans hbu, subcube_nonempty _ _⟩
  · have hc : ((2 : ℝ)^k)⁻¹ ≠ 0 := by positivity
    apply (Asymptotics.isEquivalent_iff_tendsto_one (by
      filter_upwards [eventually_ge_atTop 2] with g hg
      exact mul_ne_zero hc (ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)))).mpr
    have hh := (replacement_gap_scaled_limit k hk).div_const (((2 : ℝ)^k)⁻¹)
    rw [div_self hc] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 2] with g hg
    simp only [Pi.div_apply]
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
    field_simp

theorem no_uniform_littleO_error (k : ℕ) (hk : 3 ≤ k) :
    ¬ ∃ e : ℕ → ℝ,
      Asymptotics.IsLittleO Filter.atTop e (fun g => (g : ℝ)^(-((k-1 : ℕ) : ℝ))) ∧
      ∀ u, k ≤ u → ∀ S : Finset (Assignment u), S.Nonempty → ∀ g, 2 ≤ g →
        blockKill u (k-1) S 1 - e g ≤ blockKill u k S g := by
  rintro ⟨e, he, hbound⟩
  have hc : 0 < ((2 : ℝ)^k)⁻¹ := by positivity
  have hp := (replacement_gap_scaled_limit k hk).eventually_const_lt (show
    ((2 : ℝ)^k)⁻¹ / 2 < ((2 : ℝ)^k)⁻¹ by linarith)
  have hsmall := he.tendsto_div_nhds_zero.eventually_lt_const (show
    (0 : ℝ) < ((2 : ℝ)^k)⁻¹ / 2 by positivity)
  obtain ⟨g, hg, hp, he'⟩ := ((eventually_ge_atTop 2).and (hp.and hsmall)).exists
  obtain ⟨hbu, hkb, hu⟩ := sharp_parameters (k := k) hg
  have hb := hbound (g^(k+2)) (hkb.trans hbu)
    (subcube (g^(k+2)) (g^(k+1))) (subcube_nonempty _ _) g hg
  have hb' : blockKill (g^(k+2)) (k-1) (subcube (g^(k+2)) (g^(k+1))) 1 -
      blockKill (g^(k+2)) k (subcube (g^(k+2)) (g^(k+1))) g ≤ e g := by linarith
  have hm := mul_le_mul_of_nonneg_left hb' (pow_nonneg (Nat.cast_nonneg (α := ℝ) g) (k-1))
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, div_inv_eq_mul] at he'
  nlinarith

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.Sharpness ----
namespace OAI

namespace RandomKSAT

theorem sharpness (k : ℕ) (hk : 3 ≤ k) :
    (∀ γ D A : ℝ, γ < (k : ℝ) / ((k-1 : ℕ) : ℝ) → 0 < D → 0 < A →
      ∀ N : ℕ, ∃ u : ℕ, N ≤ u ∧ k ≤ u ∧ ∃ S : Finset (Assignment u),
        S.Nonempty ∧ A * (u : ℝ) ^ (-((k-1 : ℕ) : ℝ)) ≤ blockKill u (k-1) S 1 ∧
        D * (blockKill u (k-1) S 1) ^ (-γ) < lifetime u k S) ∧
    (∃ u : ℕ → ℕ, ∃ S : ∀ g, Finset (Assignment (u g)),
      (∀ g, 2 ≤ g → k ≤ u g ∧ (S g).Nonempty) ∧
      Asymptotics.IsEquivalent Filter.atTop
        (fun g => blockKill (u g) (k-1) (S g) 1 - blockKill (u g) k (S g) g)
        (fun g => ((2 : ℝ)^k)⁻¹ * (g : ℝ)^(-((k-1 : ℕ) : ℝ)))) ∧
    (¬ ∃ e : ℕ → ℝ,
      Asymptotics.IsLittleO Filter.atTop e (fun g => (g : ℝ)^(-((k-1 : ℕ) : ℝ))) ∧
      ∀ u, k ≤ u → ∀ S : Finset (Assignment u), S.Nonempty → ∀ g, 2 ≤ g →
        blockKill u (k-1) S 1 - e g ≤ blockKill u k S g) := by
  exact ⟨lifetime_sharp k hk, replacement_sharp k hk, no_uniform_littleO_error k hk⟩

end RandomKSAT

end OAI

-- ---- mission target ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem solution (k : ℕ) (hk : 3 ≤ k) :
    (∀ γ D A : ℝ, γ < (k : ℝ) / ((k-1 : ℕ) : ℝ) → 0 < D → 0 < A →
      ∀ N : ℕ, ∃ u : ℕ, N ≤ u ∧ k ≤ u ∧ ∃ S : Finset (Assignment u),
        S.Nonempty ∧ A * (u : ℝ) ^ (-((k-1 : ℕ) : ℝ)) ≤ blockKill u (k-1) S 1 ∧
        D * (blockKill u (k-1) S 1) ^ (-γ) < lifetime u k S) ∧
    (∃ u : ℕ → ℕ, ∃ S : ∀ g, Finset (Assignment (u g)),
      (∀ g, 2 ≤ g → k ≤ u g ∧ (S g).Nonempty) ∧
      Asymptotics.IsEquivalent Filter.atTop
        (fun g => blockKill (u g) (k-1) (S g) 1 - blockKill (u g) k (S g) g)
        (fun g => ((2 : ℝ)^k)⁻¹ * (g : ℝ)^(-((k-1 : ℕ) : ℝ)))) ∧
    (¬ ∃ e : ℕ → ℝ,
      Asymptotics.IsLittleO Filter.atTop e (fun g => (g : ℝ)^(-((k-1 : ℕ) : ℝ))) ∧
      ∀ u, k ≤ u → ∀ S : Finset (Assignment u), S.Nonempty → ∀ g, 2 ≤ g →
        blockKill u (k-1) S 1 - e g ≤ blockKill u k S g) := by
  first
    | exact OAI.RandomKSAT.sharpness k hk
    | exact OAI.RandomKSAT.sharpness
    | (apply OAI.RandomKSAT.sharpness <;> assumption)
    | (intros; apply OAI.RandomKSAT.sharpness <;> assumption)
