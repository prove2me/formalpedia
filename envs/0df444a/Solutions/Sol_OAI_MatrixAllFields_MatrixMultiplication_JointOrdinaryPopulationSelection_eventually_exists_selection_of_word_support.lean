-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.JointOrdinaryPopulationSelection.eventually_exists_selection_of_word_support
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T05:54:51.708584+00:00
-- url     : https://prove2.me/submissions/583ecb7d-75c7-4eda-b85d-a1acc41e216f

import Mathlib
import Definitions.Def_OAIQ254M002
import Definitions.Def_OAIQ254M003
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_JointOrdinaryPopulationSelection_uniformDegree_log_upper_of_word_support

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointAPFree
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.JointAPFree

theorem natSet_card (N : ℕ) : (natSet N).card = rothNumberNat N :=
  (rothNumberNat_spec N).choose_spec.2.1

theorem modularSet_card (M : ℕ) :
    (modularSet M).card = rothNumberNat (M / 2) := by
  rw [modularSet, Finset.card_image_iff.mpr, natSet_card]
  intro a ha b hb hab
  exact natCast_injective_below
    ((mem_natSet_lt ha).trans_le (Nat.div_le_self M 2))
    ((mem_natSet_lt hb).trans_le (Nat.div_le_self M 2)) hab

theorem modularSet_card_lower (M : ℕ) :
    ((M / 2 : ℕ) : ℝ) * Real.exp (-4 * Real.sqrt (Real.log ((M / 2 : ℕ) : ℝ))) ≤
      ((modularSet M).card : ℝ) := by
  rw [modularSet_card]
  exact Behrend.roth_lower_bound

theorem modularSet_card_le_half (M : ℕ) : (modularSet M).card ≤ M / 2 := by
  rw [modularSet_card]
  exact rothNumberNat_le _

theorem modularSet_card_pos {M : ℕ} (hM : 2 ≤ M) : 0 < (modularSet M).card := by
  have hhalf : 0 < M / 2 := Nat.div_pos hM (by decide)
  have hpos : (0 : ℝ) < ((M / 2 : ℕ) : ℝ) *
      Real.exp (-4 * Real.sqrt (Real.log ((M / 2 : ℕ) : ℝ))) := by
    exact mul_pos (by exact_mod_cast hhalf) (Real.exp_pos _)
  exact_mod_cast hpos.trans_le (modularSet_card_lower M)

theorem modularSet_log_card_lower {M : ℕ} (hM : 2 ≤ M) :
    Real.log ((M / 2 : ℕ) : ℝ) - 4 * Real.sqrt (Real.log ((M / 2 : ℕ) : ℝ)) ≤
      Real.log ((modularSet M).card : ℝ) := by
  have hhalf : (0 : ℝ) < ((M / 2 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_pos hM (by decide) : 0 < M / 2)
  have h := Real.log_le_log (mul_pos hhalf (Real.exp_pos _)) (modularSet_card_lower M)
  rw [Real.log_mul hhalf.ne' (Real.exp_pos _).ne', Real.log_exp] at h
  linarith

theorem modularSet_log_card_lower_modulus {M : ℕ} (hM : 2 ≤ M) :
    Real.log (M : ℝ) - Real.log 3 - 4 * Real.sqrt (Real.log (M : ℝ)) ≤
      Real.log ((modularSet M).card : ℝ) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hhalf : (0 : ℝ) < ((M / 2 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_pos hM (by decide) : 0 < M / 2)
  have hround : (M : ℝ) / 3 ≤ ((M / 2 : ℕ) : ℝ) := by
    have hn : M ≤ 3 * (M / 2) := by omega
    have hr : (M : ℝ) ≤ 3 * ((M / 2 : ℕ) : ℝ) := by exact_mod_cast hn
    linarith
  have hlog := Real.log_le_log (div_pos hMr (by norm_num)) hround
  rw [Real.log_div hMr.ne' (by norm_num)] at hlog
  have hlogUpper : Real.log ((M / 2 : ℕ) : ℝ) ≤ Real.log (M : ℝ) := by
    apply Real.log_le_log hhalf
    exact_mod_cast Nat.div_le_self M 2
  have hsqrt := Real.sqrt_le_sqrt hlogUpper
  have hcard := modularSet_log_card_lower hM
  linarith

theorem modularSet_log_card_le_modulus {M : ℕ} (hM : 2 ≤ M) :
    Real.log ((modularSet M).card : ℝ) ≤ Real.log (M : ℝ) := by
  apply Real.log_le_log
  · exact_mod_cast modularSet_card_pos hM
  · exact_mod_cast (modularSet_card_le_half M).trans (Nat.div_le_self M 2)

end MatrixMultiplication.JointAPFree

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointLossCounts
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.JointLossCounts

open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {Ω V I : Type*}

theorem card_filter_exists_le (samples : Finset Ω) (indices : Finset I)
    (event : I → Ω → Prop) :
    (samples.filter (fun ω => ∃ i ∈ indices, event i ω)).card ≤
      ∑ i ∈ indices, (samples.filter (event i)).card := by
  classical
  have heq : samples.filter (fun ω => ∃ i ∈ indices, event i ω) =
      indices.biUnion (fun i => samples.filter (event i)) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨hω, i, hi, he⟩
      exact ⟨i, hi, hω, he⟩
    · rintro ⟨i, hi, hω, he⟩
      exact ⟨hω, i, hi, he⟩
  rw [heq]
  exact Finset.card_biUnion_le

theorem competitor_union_card_mul_le (ownSurvival : Finset Ω)
    (competitors : Finset I) (collision : I → Ω → Prop) (M : ℕ)
    (hcollision : ∀ i ∈ competitors,
      M * (ownSurvival.filter (collision i)).card ≤ ownSurvival.card) :
    M * (ownSurvival.filter (fun ω => ∃ i ∈ competitors, collision i ω)).card ≤
      competitors.card * ownSurvival.card := by
  classical
  calc
    _ ≤ M * ∑ i ∈ competitors, (ownSurvival.filter (collision i)).card :=
      Nat.mul_le_mul_left M (card_filter_exists_le ownSurvival competitors collision)
    _ = ∑ i ∈ competitors, M * (ownSurvival.filter (collision i)).card :=
      by rw [Finset.mul_sum]
    _ ≤ ∑ _i ∈ competitors, ownSurvival.card :=
      Finset.sum_le_sum hcollision
    _ = _ := by simp

theorem good_card_lower (ownSurvival : Finset Ω) (failure : Ω → Prop) (error : ℝ)
    (hbad : ((ownSurvival.filter failure).card : ℝ) ≤ error * (ownSurvival.card : ℝ)) :
    (1 - error) * (ownSurvival.card : ℝ) ≤
      ((ownSurvival.filter (fun ω => ¬ failure ω)).card : ℝ) := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := ownSurvival) failure
  have hsplitR : ((ownSurvival.filter failure).card : ℝ) +
      ((ownSurvival.filter (fun ω => ¬ failure ω)).card : ℝ) =
      (ownSurvival.card : ℝ) := by exact_mod_cast hsplit
  nlinarith

end MatrixMultiplication.JointLossCounts

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_JointExtractionRates
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.Foundation.Separation

open Filter

theorem log_nat_prod {I : Type*} (s : Finset I) (a : I → ℕ)
    (ha : ∀ i ∈ s, 0 < a i) :
    Real.log ((∏ i ∈ s, a i : ℕ) : ℝ) = ∑ i ∈ s, Real.log (a i : ℝ) := by
  rw [Nat.cast_prod]
  exact Real.log_prod fun i hi =>
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (ha i hi))

theorem tendsto_log_nat_prod_div_nat {I : Type*} (s : Finset I)
    {K : I → ℕ → ℕ} {H : I → ℝ}
    (hK : ∀ i ∈ s, ∀ N, 0 < K i N)
    (hpop : ∀ i ∈ s,
      Tendsto (fun N => Real.log (K i N : ℝ) / (N : ℝ)) atTop (nhds (H i))) :
    Tendsto (fun N => Real.log ((∏ i ∈ s, K i N : ℕ) : ℝ) / (N : ℝ))
      atTop (nhds (∑ i ∈ s, H i)) := by
  have hsum := tendsto_finsetSum s hpop
  apply hsum.congr
  intro N
  rw [log_nat_prod s (fun i => K i N) (fun i hi => hK i hi N)]
  simp only [div_eq_mul_inv, Finset.sum_mul]

end MatrixMultiplication.Foundation.Separation






namespace MatrixMultiplication.JointExtractionRates

open Filter
open scoped BigOperators Topology

theorem sum_goodCount_eq_sum_goodIncidence {Ω E : Type*} [Fintype Ω] [Fintype E]
    (good : Ω → E → Prop) :
    (∑ ω, goodCount good ω) = ∑ e, goodIncidence good e := by
  classical
  simp only [goodCount, goodIncidence, Finset.card_filter]
  exact Finset.sum_comm

theorem exists_goodCount_ge {Ω E : Type*} [Fintype Ω] [Nonempty Ω] [Fintype E]
    (good : Ω → E → Prop) (q : ℝ)
    (hinc : ∀ e, q * (Fintype.card Ω : ℝ) ≤ (goodIncidence good e : ℝ)) :
    ∃ ω, (Fintype.card E : ℝ) * q ≤ (goodCount good ω : ℝ) := by
  have hsum := Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => hinc e)
  have hdouble : (∑ ω, (goodCount good ω : ℝ)) =
      ∑ e, (goodIncidence good e : ℝ) := by
    exact_mod_cast sum_goodCount_eq_sum_goodIncidence good
  have havg : (∑ _ω : Ω, (Fintype.card E : ℝ) * q) ≤
      ∑ ω, (goodCount good ω : ℝ) := by
    rw [hdouble]
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc,
      mul_comm, mul_left_comm] using hsum
  obtain ⟨ω, _, hω⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty havg
  exact ⟨ω, hω⟩

theorem exists_good_subfamily {Ω E : Type*} [Fintype E]
    (good : Ω → E → Prop) (ω : Ω) (K : ℕ) (hK : K ≤ goodCount good ω) :
    ∃ G : Finset E, G.card = K ∧ ∀ e ∈ G, good ω e := by
  classical
  obtain ⟨G, hG, hcard⟩ := Finset.exists_subset_card_eq
    (s := Finset.univ.filter (good ω)) (by simpa only [goodCount] using hK)
  exact ⟨G, hcard, fun e he => (Finset.mem_filter.mp (hG he)).2⟩

theorem eventually_exists_good_subfamily {Ω E : ℕ → Type*}
    [∀ N, Fintype (E N)]
    (good : ∀ N, Ω N → E N → Prop) (K : ℕ → ℕ)
    (hK : ∀ᶠ N in atTop, ∃ ω : Ω N, K N ≤ goodCount (good N) ω) :
    ∀ᶠ N in atTop, ∃ (ω : Ω N) (G : Finset (E N)),
      G.card = K N ∧ ∀ e ∈ G, good N ω e := by
  filter_upwards [hK] with N hN
  obtain ⟨ω, hω⟩ := hN
  obtain ⟨G, hcard, hgood⟩ := exists_good_subfamily (good N) ω (K N) hω
  exact ⟨ω, G, hcard, hgood⟩

theorem tendsto_polynomial_mul_exp_neg (d : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ d * Real.exp (-c * (N : ℝ)))
      atTop (𝓝 0) := by
  have hbase := (Real.summable_pow_mul_exp_neg_nat_mul d hc).tendsto_atTop_zero
  have hshift := (hbase.comp (tendsto_add_atTop_nat 1)).mul_const (Real.exp c)
  simp only [zero_mul, Function.comp_apply, Nat.cast_add, Nat.cast_one] at hshift
  convert hshift using 1
  all_goals try with_reducible_and_instances rfl
  ext N
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem eventually_error_le_half {error : ℕ → ℝ} (B : ℝ) (d : ℕ)
    {c : ℝ} (hc : 0 < c)
    (hbound : ∀ᶠ N in atTop,
      error N ≤ B * (((N : ℝ) + 1) ^ d * Real.exp (-c * (N : ℝ)))) :
    ∀ᶠ N in atTop, error N ≤ 1 / 2 := by
  have hlim := (tendsto_polynomial_mul_exp_neg d hc).const_mul B
  have hsmall : ∀ᶠ N : ℕ in atTop,
      B * (((N : ℝ) + 1) ^ d * Real.exp (-c * (N : ℝ))) < 1 / 2 := by
    simpa only [mul_zero] using (tendsto_order.1 hlim).2 (1 / 2) (by simp)
  filter_upwards [hbound, hsmall] with N hb hs
  exact hb.trans hs.le

theorem hashModulus_ge (H : ℝ) (N : ℕ) : 37 ≤ hashModulus H N := by
  simpa only [hashModulus, pow_one] using
    (Nat.pow_le_pow_right (by norm_num : 0 < 37)
      (show 1 ≤ ⌊(N : ℝ) * H / Real.log 37⌋₊ + 1 by omega))

theorem hashModulus_log_bounds {H : ℝ} (hH : 0 ≤ H) (N : ℕ) :
    (N : ℝ) * H ≤ Real.log (hashModulus H N : ℝ) ∧
      Real.log (hashModulus H N : ℝ) ≤ (N : ℝ) * H + Real.log 37 := by
  have hl : 0 < Real.log (37 : ℝ) := Real.log_pos (by norm_num)
  have harg : 0 ≤ (N : ℝ) * H / Real.log 37 :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg N) hH) hl.le
  have hfloor := mul_le_mul_of_nonneg_right (Nat.floor_le harg) hl.le
  have hceil := mul_lt_mul_of_pos_right
    (Nat.lt_floor_add_one ((N : ℝ) * H / Real.log 37)) hl
  have hcancel : (N : ℝ) * H / Real.log 37 * Real.log 37 = (N : ℝ) * H :=
    div_mul_cancel₀ _ hl.ne'
  simp only [hashModulus, Nat.cast_pow, Real.log_pow, Nat.cast_add, Nat.cast_one]
  constructor <;> nlinarith

theorem tendsto_log_hashModulus_div_nat {H : ℝ} (hH : 0 ≤ H) :
    Tendsto (fun N => Real.log (hashModulus H N : ℝ) / (N : ℝ))
      atTop (𝓝 H) := by
  have hc : Tendsto (fun N : ℕ => Real.log 37 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun N : ℕ => H + Real.log 37 / (N : ℝ)) atTop (𝓝 H) := by
    simpa only [add_zero] using hc.const_add H
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    apply (le_div_iff₀ hNr).2
    nlinarith [(hashModulus_log_bounds hH N).1]
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hb := div_le_div_of_nonneg_right (hashModulus_log_bounds hH N).2 hNr.le
    simpa only [add_div, mul_div_cancel_left₀ H hNr.ne'] using hb

theorem eventually_ratio_le_exp_neg_of_log_bounds {degree M : ℕ → ℕ} {D H c : ℝ}
    (hdegree : ∀ η : ℝ, 0 < η →
      ∀ᶠ N in atTop, Real.log (degree N : ℝ) / (N : ℝ) ≤ D + η)
    (hpos : ∀ᶠ N in atTop, 0 < M N)
    (hM : Tendsto (fun N => Real.log (M N : ℝ) / (N : ℝ)) atTop (𝓝 H))
    (hc : c < H - D) :
    ∀ᶠ N in atTop, (degree N : ℝ) / (M N : ℝ) ≤ Real.exp (-c * (N : ℝ)) := by
  let η : ℝ := (H - D - c) / 3
  have hη : 0 < η := by dsimp [η] <;> linarith
  filter_upwards [hdegree η hη, hpos,
    (tendsto_order.1 hM).1 (H - η) (by linarith),
    eventually_ge_atTop (1 : ℕ)] with N hd hp hm hN
  by_cases hz : degree N = 0
  · simp only [hz, Nat.cast_zero, zero_div]
    exact (Real.exp_pos _).le
  have hdpos : (0 : ℝ) < degree N := by
    exact_mod_cast Nat.pos_of_ne_zero hz
  have hmpos : (0 : ℝ) < M N := by exact_mod_cast hp
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hdu := (div_le_iff₀ hNr).mp hd
  have hml := (lt_div_iff₀ hNr).mp hm
  have hcoefficient : D - H + 2 * η ≤ -c := by dsimp [η] <;> linarith
  have hscaled := mul_le_mul_of_nonneg_right hcoefficient hNr.le
  have hdiff : Real.log (degree N : ℝ) - Real.log (M N : ℝ) ≤
      -c * (N : ℝ) := by nlinarith
  calc
    _ = Real.exp (Real.log (degree N : ℝ) - Real.log (M N : ℝ)) := by
      rw [Real.exp_sub, Real.exp_log hdpos, Real.exp_log hmpos]
    _ ≤ _ := Real.exp_le_exp.mpr hdiff

theorem eventually_degree_div_hashModulus_le_exp {degree : ℕ → ℕ} {D H c : ℝ}
    (hH : 0 ≤ H)
    (hdegree : ∀ η : ℝ, 0 < η →
      ∀ᶠ N in atTop, Real.log (degree N : ℝ) / (N : ℝ) ≤ D + η)
    (hc : c < H - D) :
    ∀ᶠ N in atTop, (degree N : ℝ) / (hashModulus H N : ℝ) ≤
      Real.exp (-c * (N : ℝ)) := by
  apply eventually_ratio_le_exp_neg_of_log_bounds hdegree _
    (tendsto_log_hashModulus_div_nat hH) hc
  exact Eventually.of_forall fun N =>
    lt_of_lt_of_le (by decide : 0 < 37) (hashModulus_ge H N)

theorem tendsto_sqrt_div_nat_of_div_nat {a : ℕ → ℝ} {A : ℝ}
    (ha : ∀ N, 0 ≤ a N)
    (h : Tendsto (fun N => a N / (N : ℝ)) atTop (𝓝 A)) :
    Tendsto (fun N => Real.sqrt (a N) / (N : ℝ)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hp := h.sqrt.mul hinv.sqrt
  simp only [Real.sqrt_zero, mul_zero] at hp
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  ext N
  symm
  rw [Real.sqrt_div (ha N), Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1),
    Real.sqrt_one, div_mul_div_comm, mul_one, Real.mul_self_sqrt (Nat.cast_nonneg N)]

theorem tendsto_log_modularSet_card_div_nat {M : ℕ → ℕ} {H : ℝ}
    (hM : ∀ᶠ N in atTop, 2 ≤ M N)
    (hlog : Tendsto (fun N => Real.log (M N : ℝ) / (N : ℝ)) atTop (𝓝 H)) :
    Tendsto (fun N => Real.log ((JointAPFree.modularSet (M N)).card : ℝ) / (N : ℝ))
      atTop (𝓝 H) := by
  have hsqrt := tendsto_sqrt_div_nat_of_div_nat
    (fun N => Real.log_natCast_nonneg (M N)) hlog
  have hconst : Tendsto (fun N : ℕ => Real.log 3 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlower : Tendsto (fun N =>
      (Real.log (M N : ℝ) - Real.log 3 -
        4 * Real.sqrt (Real.log (M N : ℝ))) / (N : ℝ))
      atTop (𝓝 H) := by
    have h := (hlog.sub hconst).sub (hsqrt.const_mul 4)
    simp only [mul_zero, sub_zero] at h
    apply h.congr
    intro N
    ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hlog
  · filter_upwards [hM] with N hN
    exact div_le_div_of_nonneg_right
      (JointAPFree.modularSet_log_card_lower_modulus hN) (Nat.cast_nonneg N)
  · filter_upwards [hM] with N hN
    exact div_le_div_of_nonneg_right
      (JointAPFree.modularSet_log_card_le_modulus hN) (Nat.cast_nonneg N)

theorem tendsto_log_yield_lower {T U M : ℕ → ℕ} {A B C : ℝ}
    (hT : Tendsto (fun N => Real.log (T N : ℝ) / (N : ℝ)) atTop (𝓝 A))
    (hU : Tendsto (fun N => Real.log (U N : ℝ) / (N : ℝ)) atTop (𝓝 B))
    (hM : Tendsto (fun N => Real.log (M N : ℝ) / (N : ℝ)) atTop (𝓝 C)) :
    Tendsto (fun N =>
      (Real.log (T N : ℝ) + Real.log (U N : ℝ) -
        2 * Real.log (M N : ℝ) - Real.log 2) / (N : ℝ))
      atTop (𝓝 (A + B - 2 * C)) := by
  have hconst : Tendsto (fun N : ℕ => Real.log 2 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h := ((hT.add hU).sub (hM.const_mul 2)).sub hconst
  simp only [sub_zero] at h
  apply h.congr
  intro N
  ring

theorem exp_log_yield_lower {T U M : ℕ} (hT : 0 < T) (hU : 0 < U) (hM : 0 < M) :
    Real.exp (Real.log (T : ℝ) + Real.log (U : ℝ) -
        2 * Real.log (M : ℝ) - Real.log 2) =
      (T : ℝ) * ((U : ℝ) / (M : ℝ) ^ 2 / 2) := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hUr : (0 : ℝ) < U := by exact_mod_cast hU
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  rw [Real.exp_sub, Real.exp_sub, Real.exp_add, Real.exp_log hTr,
    Real.exp_log hUr, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [show 2 * Real.log (M : ℝ) = Real.log ((M : ℝ) ^ 2) by
    rw [Real.log_pow]; norm_num, Real.exp_log (pow_pos hMr 2)]
  ring

theorem eventually_exists_many_good
    {Ω E : ℕ → Type*} [∀ N, Fintype (Ω N)] [∀ N, Nonempty (Ω N)]
    [∀ N, Fintype (E N)]
    (good : ∀ N, Ω N → E N → Prop) (U M : ℕ → ℕ) {A H : ℝ}
    (hpos : ∀ᶠ N in atTop, 0 < Fintype.card (E N) ∧ 0 < U N ∧ 0 < M N)
    (hinc : ∀ᶠ N in atTop, ∀ e,
      ((U N : ℝ) / (M N : ℝ) ^ 2 / 2) * (Fintype.card (Ω N) : ℝ) ≤
        (goodIncidence (good N) e : ℝ))
    (hE : Tendsto (fun N => Real.log (Fintype.card (E N) : ℝ) / (N : ℝ))
      atTop (𝓝 A))
    (hU : Tendsto (fun N => Real.log (U N : ℝ) / (N : ℝ)) atTop (𝓝 H))
    (hM : Tendsto (fun N => Real.log (M N : ℝ) / (N : ℝ)) atTop (𝓝 H))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ ω : Ω N,
      ⌊Real.exp ((N : ℝ) * (A - H - ε))⌋₊ ≤ goodCount (good N) ω := by
  let L : ℕ → ℝ := fun N => Real.log (Fintype.card (E N) : ℝ) +
    Real.log (U N : ℝ) - 2 * Real.log (M N : ℝ) - Real.log 2
  have hL : Tendsto (fun N => L N / (N : ℝ)) atTop (𝓝 (A - H)) := by
    simpa only [L, show A + H - 2 * H = A - H by ring] using
      tendsto_log_yield_lower hE hU hM
  filter_upwards [hpos, hinc, (tendsto_order.1 hL).1 (A - H - ε) (by linarith),
    (eventually_atTop.2 ⟨1, fun N (hN : 1 ≤ N) => hN⟩)] with N hp hi hr hN
  obtain ⟨ω, hω⟩ := exists_goodCount_ge (good N) _ hi
  refine ⟨ω, ?_⟩
  have heq := exp_log_yield_lower hp.1 hp.2.1 hp.2.2
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have he : Real.exp ((N : ℝ) * (A - H - ε)) ≤
      (goodCount (good N) ω : ℝ) := by
    calc
      _ ≤ Real.exp (L N) := Real.exp_le_exp.mpr (by
        have hm := (lt_div_iff₀ hNr).mp hr
        nlinarith)
      _ = _ := heq
      _ ≤ _ := hω
  simpa only [Nat.floor_natCast] using Nat.floor_le_floor he

theorem eventually_exists_many_good_explicit
    {Ω E : ℕ → Type*} [∀ N, Fintype (Ω N)] [∀ N, Nonempty (Ω N)]
    [∀ N, Fintype (E N)]
    (good : ∀ N, Ω N → E N → Prop) {A H : ℝ} (hH : 0 ≤ H)
    (hpos : ∀ᶠ N in atTop, 0 < Fintype.card (E N))
    (hinc : ∀ᶠ N in atTop, ∀ e,
      (((JointAPFree.modularSet (hashModulus H N)).card : ℝ) /
        (hashModulus H N : ℝ) ^ 2 / 2) * (Fintype.card (Ω N) : ℝ) ≤
        (goodIncidence (good N) e : ℝ))
    (hE : Tendsto (fun N => Real.log (Fintype.card (E N) : ℝ) / (N : ℝ))
      atTop (𝓝 A))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ ω : Ω N,
      ⌊Real.exp ((N : ℝ) * (A - H - ε))⌋₊ ≤ goodCount (good N) ω := by
  have hM : ∀ N, 2 ≤ hashModulus H N := fun N =>
    (by norm_num : 2 ≤ 37).trans (hashModulus_ge H N)
  have hr := tendsto_log_hashModulus_div_nat hH
  apply eventually_exists_many_good good
    (fun N => (JointAPFree.modularSet (hashModulus H N)).card) (hashModulus H)
    _ hinc hE (tendsto_log_modularSet_card_div_nat (Eventually.of_forall hM) hr) hr hε
  filter_upwards [hpos] with N hN
  exact ⟨hN, JointAPFree.modularSet_card_pos (hM N),
    lt_of_lt_of_le (by decide : 0 < 2) (hM N)⟩

end MatrixMultiplication.JointExtractionRates

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_JointMaskedSelection
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.tripleSide_reorder _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialExact.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.JointCoarseReorder.tripleSide_reorder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.JointHashing

open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {P R : Type*} [Fintype P] [CommRing R]

theorem survival_card [Fintype R] (U : Finset R) (I J : P → R) :
    Fintype.card {s : Sample P R // Survives (U : Set R) I J s} =
      Fintype.card R ^ Fintype.card P * U.card := by
  classical
  rw [Fintype.card_congr (survivalEquiv (U : Set R) I J)]
  simp

theorem shared_x_collision_iff (U : Set R) (I J J' : P → R)
    (s : Sample P R) (hs : Survives U I J s) :
    Survives U I J' s ↔ dot s.1 (J' - J) = 0 := by
  rcases hs with ⟨heq, hU⟩
  simp only [Survives, dot_sub_right]
  constructor
  · intro h
    dsimp [xHash, yHash] at heq h
    linear_combination heq - h.1
  · intro h
    refine ⟨?_, hU⟩
    dsimp [xHash, yHash] at heq ⊢
    linear_combination heq - h

theorem shared_y_collision_iff (U : Set R) (I I' J : P → R)
    (s : Sample P R) (hs : Survives U I J s) :
    Survives U I' J s ↔ dot s.1 (I' - I) = 0 := by
  rcases hs with ⟨heq, hU⟩
  simp only [Survives, dot_sub_right]
  constructor
  · intro h
    dsimp [xHash, yHash] at heq h
    linear_combination h.1 - heq
  · intro h
    have hx : xHash s I' = xHash s I := by
      dsimp [xHash]
      linear_combination h
    exact ⟨hx.trans heq, hx ▸ hU⟩

theorem linear_zero_fiber_card [Fintype R]
    (d : P → R) (i : P) (u : Rˣ) (hu : d i = u) :
    Fintype.card R * Fintype.card {v : P → R // dot v d = 0} =
      Fintype.card R ^ Fintype.card P := by
  classical
  have h := Fintype.card_congr (linearSplitEquiv d i u hu)
  simpa only [Fintype.card_prod, Fintype.card_fun] using h.symm

theorem collision_card_mul [Fintype R]
    (U : Finset R) (I J d : P → R) (i : P) (u : Rˣ) (hu : d i = u) :
    Fintype.card R *
      Fintype.card {s : Sample P R // Survives (U : Set R) I J s ∧ dot s.1 d = 0} =
      Fintype.card {s : Sample P R // Survives (U : Set R) I J s} := by
  classical
  have hcard : Fintype.card {s : Sample P R //
      Survives (U : Set R) I J s ∧ dot s.1 d = 0} =
      Fintype.card {v : P → R // dot v d = 0} * U.card := by
    simpa using Fintype.card_congr (collisionEquiv (U : Set R) I J d)
  calc
    _ = Fintype.card R * (Fintype.card {v : P → R // dot v d = 0} * U.card) :=
      congrArg (fun n : ℕ => Fintype.card R * n) hcard
    _ = (Fintype.card R * Fintype.card {v : P → R // dot v d = 0}) * U.card :=
      (mul_assoc _ _ _).symm
    _ = (Fintype.card R ^ Fintype.card P) * U.card :=
      congrArg (fun n : ℕ => n * U.card) (linear_zero_fiber_card d i u hu)
    _ = _ := (survival_card U I J).symm

theorem shared_x_collision_card_mul [Fintype R]
    (U : Finset R) (I J J' : P → R) (i : P) (u : Rˣ)
    (hu : J' i - J i = u) :
    Fintype.card R * Fintype.card {s : Sample P R //
      Survives (U : Set R) I J s ∧ Survives (U : Set R) I J' s} =
      Fintype.card {s : Sample P R // Survives (U : Set R) I J s} := by
  classical
  let e : {s : Sample P R // Survives (U : Set R) I J s ∧
      Survives (U : Set R) I J' s} ≃
      {s : Sample P R // Survives (U : Set R) I J s ∧ dot s.1 (J' - J) = 0} :=
    Equiv.subtypeEquivRight (fun s => and_congr_right (fun hs =>
      shared_x_collision_iff (U : Set R) I J J' s hs))
  rw [Fintype.card_congr e]
  exact collision_card_mul U I J (J' - J) i u hu

theorem shared_y_collision_card_mul [Fintype R]
    (U : Finset R) (I I' J : P → R) (i : P) (u : Rˣ)
    (hu : I' i - I i = u) :
    Fintype.card R * Fintype.card {s : Sample P R //
      Survives (U : Set R) I J s ∧ Survives (U : Set R) I' J s} =
      Fintype.card {s : Sample P R // Survives (U : Set R) I J s} := by
  classical
  let e : {s : Sample P R // Survives (U : Set R) I J s ∧
      Survives (U : Set R) I' J s} ≃
      {s : Sample P R // Survives (U : Set R) I J s ∧ dot s.1 (I' - I) = 0} :=
    Equiv.subtypeEquivRight (fun s => and_congr_right (fun hs =>
      shared_y_collision_iff (U : Set R) I I' J s hs))
  rw [Fintype.card_congr e]
  exact collision_card_mul U I J (I' - I) i u hu

theorem coarse_difference_isUnit (k : ℕ) (a b : Fin 17) (hab : a ≠ b) :
    IsUnit ((a.val : ZMod (37 ^ k)) - (b.val : ZMod (37 ^ k))) := by
  have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
  rcases lt_or_gt_of_ne hne with h | h
  · have hu := small_nat_isUnit k (b.val - a.val) (Nat.sub_pos_of_lt h) (by omega)
    rw [Nat.cast_sub h.le] at hu
    simpa only [neg_sub] using hu.neg
  · have hu := small_nat_isUnit k (a.val - b.val) (Nat.sub_pos_of_lt h) (by omega)
    rwa [Nat.cast_sub h.le] at hu

theorem coarse_words_unit_coordinate (k : ℕ) (I J : P → Fin 17) (hIJ : I ≠ J) :
    ∃ i : P, IsUnit (((I i : ℕ) : ZMod (37 ^ k)) - ((J i : ℕ) : ZMod (37 ^ k))) := by
  classical
  have hi : ∃ i, I i ≠ J i := by
    by_contra h
    push Not at h
    exact hIJ (funext h)
  obtain ⟨i, hi⟩ := hi
  exact ⟨i, coarse_difference_isUnit k (I i) (J i) hi⟩

theorem shared_z_collision_iff (two : Rˣ) (htwo : (two : R) = 2)
    (U : Set R) (I I' J J' : P → R) (hIJ : I' + J' = I + J)
    (s : Sample P R) (hs : Survives U I J s) :
    Survives U I' J' s ↔ dot s.1 (I' - I) = 0 := by
  have hsum : dot s.1 I' + dot s.1 J' = dot s.1 I + dot s.1 J := by
    simpa using congrArg (dot s.1) hIJ
  rcases hs with ⟨heq, hU⟩
  rw [dot_sub_right]
  constructor
  · rintro ⟨heq', _⟩
    dsimp [xHash, yHash] at heq heq'
    have hz : (two : R) * (dot s.1 I' - dot s.1 I) = (two : R) * 0 := by
      rw [htwo]
      linear_combination heq' - heq + hsum
    exact two.isUnit.mul_left_cancel hz
  · intro hd
    have hx : xHash s I' = xHash s I := by
      dsimp [xHash]
      linear_combination hd
    have hy : yHash s J' = yHash s J := by
      dsimp [yHash]
      linear_combination hsum - hd
    exact ⟨hx.trans (heq.trans hy.symm), hx ▸ hU⟩

theorem shared_z_collision_card_mul [Fintype R]
    (two : Rˣ) (htwo : (two : R) = 2)
    (U : Finset R) (I I' J J' : P → R) (hIJ : I' + J' = I + J)
    (i : P) (u : Rˣ) (hu : I' i - I i = u) :
    Fintype.card R * Fintype.card {s : Sample P R //
      Survives (U : Set R) I J s ∧ Survives (U : Set R) I' J' s} =
      Fintype.card {s : Sample P R // Survives (U : Set R) I J s} := by
  classical
  let e : {s : Sample P R // Survives (U : Set R) I J s ∧
      Survives (U : Set R) I' J' s} ≃
      {s : Sample P R // Survives (U : Set R) I J s ∧ dot s.1 (I' - I) = 0} :=
    Equiv.subtypeEquivRight (fun s => and_congr_right (fun hs =>
      shared_z_collision_iff two htwo (U : Set R) I I' J J' hIJ s hs))
  rw [Fintype.card_congr e]
  exact collision_card_mul U I J (I' - I) i u hu

end MatrixMultiplication.JointHashing





noncomputable section

namespace MatrixMultiplication.JointCoarseHashing

attribute [local instance] Classical.propDecidable

variable {P : Type*}

theorem eq_of_shared_xy (S : P → ℕ) (e f : Triple P)
    (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hx : e.1 = f.1) (hy : e.2.1 = f.2.1) : e = f := by
  have hz : e.2.2 = f.2.2 := by
    funext p
    apply Fin.ext
    have he' := he p
    have hf' := hf p
    rw [hx, hy] at he'
    omega
  exact Prod.ext hx (Prod.ext hy hz)

theorem eq_of_shared_xz (S : P → ℕ) (e f : Triple P)
    (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hx : e.1 = f.1) (hz : e.2.2 = f.2.2) : e = f := by
  have hy : e.2.1 = f.2.1 := by
    funext p
    apply Fin.ext
    have he' := he p
    have hf' := hf p
    rw [hx, hz] at he'
    omega
  exact Prod.ext hx (Prod.ext hy hz)

theorem shared_z_cast_sum (k : ℕ) (S : P → ℕ) (e f : Triple P)
    (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hz : f.2.2 = e.2.2) :
    castWord k f.1 + castWord k f.2.1 = castWord k e.1 + castWord k e.2.1 := by
  have h := (supportSum_cast k S f hf).trans (supportSum_cast k S e he).symm
  rw [hz] at h
  exact add_right_cancel h

section FiniteHashing

variable [Fintype P]

theorem survival_card (k : ℕ) (U : Finset (ZMod (37 ^ k))) (e : Triple P) :
    Fintype.card {s : Sample P k // Survives k U e s} =
      (37 ^ k) ^ Fintype.card P * U.card := by
  have hcard := JointHashing.survival_card U (castWord k e.1) (castWord k e.2.1)
  simp only [ZMod.card] at hcard
  simp only [Fintype.card_eq_nat_card] at hcard ⊢
  exact hcard

theorem shared_x_card_mul (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (S : P → ℕ) (e f : Triple P) (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hne : f ≠ e) (hx : f.1 = e.1) :
    (37 ^ k) * Fintype.card {s : Sample P k // Survives k U e s ∧ Survives k U f s} =
      Fintype.card {s : Sample P k // Survives k U e s} := by
  classical
  have hy : f.2.1 ≠ e.2.1 := fun hy => hne (eq_of_shared_xy S f e hf he hx hy)
  obtain ⟨i, hi⟩ := JointHashing.coarse_words_unit_coordinate k f.2.1 e.2.1 hy
  have h := JointHashing.shared_x_collision_card_mul U (castWord k e.1)
    (castWord k e.2.1) (castWord k f.2.1) i hi.unit hi.unit_spec.symm
  simp only [ZMod.card] at h
  simp only [Fintype.card_eq_nat_card] at h ⊢
  simpa only [Survives, hx] using h

theorem shared_y_card_mul (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (S : P → ℕ) (e f : Triple P) (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hne : f ≠ e) (hy : f.2.1 = e.2.1) :
    (37 ^ k) * Fintype.card {s : Sample P k // Survives k U e s ∧ Survives k U f s} =
      Fintype.card {s : Sample P k // Survives k U e s} := by
  classical
  have hx : f.1 ≠ e.1 := fun hx => hne (eq_of_shared_xy S f e hf he hx hy)
  obtain ⟨i, hi⟩ := JointHashing.coarse_words_unit_coordinate k f.1 e.1 hx
  have h := JointHashing.shared_y_collision_card_mul U (castWord k e.1)
    (castWord k f.1) (castWord k e.2.1) i hi.unit hi.unit_spec.symm
  simp only [ZMod.card] at h
  simp only [Fintype.card_eq_nat_card] at h ⊢
  simpa only [Survives, hy] using h

theorem shared_z_card_mul (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (S : P → ℕ) (e f : Triple P) (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hne : f ≠ e) (hz : f.2.2 = e.2.2) :
    (37 ^ k) * Fintype.card {s : Sample P k // Survives k U e s ∧ Survives k U f s} =
      Fintype.card {s : Sample P k // Survives k U e s} := by
  classical
  have hx : f.1 ≠ e.1 := fun hx => hne (eq_of_shared_xz S f e hf he hx hz)
  obtain ⟨i, hi⟩ := JointHashing.coarse_words_unit_coordinate k f.1 e.1 hx
  have h := JointHashing.shared_z_collision_card_mul (twoUnit k) (twoUnit_coe k)
    U (castWord k e.1) (castWord k f.1) (castWord k e.2.1) (castWord k f.2.1)
    (shared_z_cast_sum k S e f he hf hz) i hi.unit hi.unit_spec.symm
  simp only [ZMod.card] at h
  simp only [Fintype.card_eq_nat_card] at h ⊢
  exact h

theorem pair_survival_card_mul (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (S : P → ℕ) (e f : Triple P) (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hne : f ≠ e) (hshare : SharesSide e f) :
    (37 ^ k) * Fintype.card {s : Sample P k // Survives k U e s ∧ Survives k U f s} =
      Fintype.card {s : Sample P k // Survives k U e s} := by
  rcases hshare with hx | hy | hz
  · exact shared_x_card_mul k U S e f he hf hne hx
  · exact shared_y_card_mul k U S e f he hf hne hy
  · exact shared_z_card_mul k U S e f he hf hne hz

theorem ownEvent_card (k : ℕ) (U : Finset (ZMod (37 ^ k))) (e : Triple P) :
    (ownEvent k U e).card = (37 ^ k) ^ Fintype.card P * U.card := by
  simpa only [ownEvent, Fintype.card_subtype] using survival_card k U e

theorem pair_event_card_mul (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (S : P → ℕ) (e f : Triple P) (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hne : f ≠ e) (hshare : SharesSide e f) :
    (37 ^ k) * ((ownEvent k U e).filter (Survives k U f)).card = (ownEvent k U e).card := by
  simpa only [ownEvent, Finset.filter_filter, Fintype.card_subtype] using
    pair_survival_card_mul k U S e f he hf hne hshare

theorem competitor_union_card_mul_le (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (S : P → ℕ) (e : Triple P) (he : HasSupportSum S e) (competitors : Finset (Triple P))
    (hf : ∀ f ∈ competitors, HasSupportSum S f)
    (hne : ∀ f ∈ competitors, f ≠ e)
    (hshare : ∀ f ∈ competitors, SharesSide e f) :
    (37 ^ k) * ((ownEvent k U e).filter
      (fun s => ∃ f ∈ competitors, Survives k U f s)).card ≤
        competitors.card * (ownEvent k U e).card := by
  apply JointLossCounts.competitor_union_card_mul_le
  intro f hf'
  exact (pair_event_card_mul k U S e f he (hf f hf') (hne f hf') (hshare f hf')).le

theorem competitor_union_card_le (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (S : P → ℕ) (e : Triple P) (he : HasSupportSum S e) (competitors : Finset (Triple P))
    (hf : ∀ f ∈ competitors, HasSupportSum S f)
    (hne : ∀ f ∈ competitors, f ≠ e)
    (hshare : ∀ f ∈ competitors, SharesSide e f) :
    (((ownEvent k U e).filter (fun s => ∃ f ∈ competitors, Survives k U f s)).card : ℝ) ≤
      ((competitors.card : ℝ) / ((37 ^ k : ℕ) : ℝ)) * ((ownEvent k U e).card : ℝ) := by
  have hM : (0 : ℝ) < ((37 ^ k : ℕ) : ℝ) := by
    exact_mod_cast (pow_pos (by decide : 0 < (37 : ℕ)) k)
  have h := competitor_union_card_mul_le k U S e he competitors hf hne hshare
  have hR : ((37 ^ k : ℕ) : ℝ) *
      (((ownEvent k U e).filter (fun s => ∃ f ∈ competitors, Survives k U f s)).card : ℝ) ≤
      (competitors.card : ℝ) * ((ownEvent k U e).card : ℝ) := by exact_mod_cast h
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hM).2 (by simpa only [mul_comm] using hR)

end FiniteHashing

end MatrixMultiplication.JointCoarseHashing






namespace MatrixMultiplication.JointOrdinarySelection

open JointCoarseHashing JointExtractionRates Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

variable {P E : Type*}

section Finite

variable [Fintype P]

theorem good_no_shared_side (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (ambient : Finset (Triple P)) (e f : Triple P) (s : Sample P k)
    (he : Good k U ambient e s) (hf : Good k U ambient f s)
    (hmem : f ∈ ambient) (hne : f ≠ e) : ¬ SharesSide e f := by
  intro hshare
  exact good_excludes_neighbor k U ambient e f s he hmem hne hshare hf.1

theorem ownEvent_card_real (k : ℕ) (U : Finset (ZMod (37 ^ k))) (e : Triple P) :
    ((ownEvent k U e).card : ℝ) =
      ((U.card : ℝ) / ((37 ^ k : ℕ) : ℝ) ^ 2) * (Fintype.card (Sample P k) : ℝ) := by
  rw [ownEvent_card, JointHashing.sample_card, ZMod.card]
  push_cast
  field_simp

theorem bad_card_le (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (ambient : Finset (Triple P)) (S : P → ℕ)
    (hsupport : ∀ f ∈ ambient, HasSupportSum S f)
    (e : Triple P) (he : e ∈ ambient) :
    (((ownEvent k U e).filter (Bad k U ambient e)).card : ℝ) ≤
      ((neighbors ambient e).card : ℝ) / ((37 ^ k : ℕ) : ℝ) *
        ((ownEvent k U e).card : ℝ) := by
  have hset : (ownEvent k U e).filter (Bad k U ambient e) =
      (ownEvent k U e).filter (fun s => ∃ f ∈ neighbors ambient e, Survives k U f s) := by
    ext s
    simp only [Finset.mem_filter, Bad]
  rw [hset]
  apply competitor_union_card_le k U S e (hsupport e he) (neighbors ambient e)
  · intro f hf
    exact hsupport f ((mem_neighbors ambient e f).mp hf).1
  · intro f hf
    exact ((mem_neighbors ambient e f).mp hf).2.1
  · intro f hf
    exact ((mem_neighbors ambient e f).mp hf).2.2

theorem goodEvent_card_lower (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (ambient : Finset (Triple P)) (S : P → ℕ)
    (hsupport : ∀ f ∈ ambient, HasSupportSum S f)
    (e : Triple P) (he : e ∈ ambient) (D : ℕ)
    (hdegree : (neighbors ambient e).card ≤ D)
    (hsmall : (D : ℝ) / ((37 ^ k : ℕ) : ℝ) ≤ 1 / 2) :
    ((U.card : ℝ) / ((37 ^ k : ℕ) : ℝ) ^ 2 / 2) *
      (Fintype.card (Sample P k) : ℝ) ≤ (goodEvent k U ambient e).card := by
  have hM : (0 : ℝ) ≤ ((37 ^ k : ℕ) : ℝ) := Nat.cast_nonneg _
  have hdeg : ((neighbors ambient e).card : ℝ) / ((37 ^ k : ℕ) : ℝ) ≤ 1 / 2 :=
    (div_le_div_of_nonneg_right (by exact_mod_cast hdegree) hM).trans hsmall
  have hb : (((ownEvent k U e).filter (Bad k U ambient e)).card : ℝ) ≤
      (1 / 2) * ((ownEvent k U e).card : ℝ) :=
    (bad_card_le k U ambient S hsupport e he).trans
      (mul_le_mul_of_nonneg_right hdeg (Nat.cast_nonneg _))
  have hg := JointLossCounts.good_card_lower (ownEvent k U e) (Bad k U ambient e)
    (1 / 2) hb
  rw [ownEvent_card_real] at hg
  change _ ≤ ((goodEvent k U ambient e).card : ℝ) at hg
  convert hg using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem goodIncidence_eq (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (ambient : Finset (Triple P)) (coarse : E → Triple P) (e : E) :
    goodIncidence (fun s e => Good k U ambient (coarse e) s) e =
      (goodEvent k U ambient (coarse e)).card := by
  unfold goodIncidence
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_goodEvent]

end Finite

theorem eventually_exists_selection
    {P E : ℕ → Type*} [∀ N, Fintype (P N)] [∀ N, Fintype (E N)]
    (ambient : ∀ N, Finset (Triple (P N))) (S : ∀ N, P N → ℕ)
    (coarse : ∀ N, E N → Triple (P N))
    (hinj : ∀ N, Function.Injective (coarse N))
    (hsupport : ∀ N, ∀ f ∈ ambient N, HasSupportSum (S N) f)
    (htarget : ∀ N e, coarse N e ∈ ambient N)
    (degree : ℕ → ℕ)
    (hdegree : ∀ N e, (neighbors (ambient N) (coarse N e)).card ≤ degree N)
    {A D H : ℝ} (hH : 0 ≤ H) (hgap : D < H)
    (hdegreeRate : ∀ η : ℝ, 0 < η →
      ∀ᶠ N in atTop, Real.log (degree N : ℝ) / (N : ℝ) ≤ D + η)
    (hpos : ∀ᶠ N in atTop, 0 < Fintype.card (E N))
    (hE : Tendsto (fun N => Real.log (Fintype.card (E N) : ℝ) / (N : ℝ))
      atTop (𝓝 A))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ (s : Sample (P N) (hashLevel H N)) (G : Finset (E N)),
      G.card = ⌊Real.exp ((N : ℝ) * (A - H - ε))⌋₊ ∧
      (∀ e ∈ G, Good (hashLevel H N) (hashSet H N) (ambient N) (coarse N e) s) ∧
      (G : Set (E N)).Pairwise (fun e f => ¬ SharesSide (coarse N e) (coarse N f)) := by
  classical
  let c : ℝ := (H - D) / 2
  have hc : 0 < c := by dsimp [c] <;> linarith
  have hclt : c < H - D := by dsimp [c] <;> linarith
  have hratio := eventually_degree_div_hashModulus_le_exp hH hdegreeRate hclt
  have hsmall : ∀ᶠ N in atTop,
      (degree N : ℝ) / (hashModulus H N : ℝ) ≤ 1 / 2 := by
    apply eventually_error_le_half 1 0 hc
    simpa only [pow_zero, one_mul] using hratio
  let good := fun N (s : Sample (P N) (hashLevel H N)) (e : E N) =>
    Good (hashLevel H N) (hashSet H N) (ambient N) (coarse N e) s
  have hinc : ∀ᶠ N in atTop, ∀ e,
      (((JointAPFree.modularSet (hashModulus H N)).card : ℝ) /
        (hashModulus H N : ℝ) ^ 2 / 2) *
        (Fintype.card (Sample (P N) (hashLevel H N)) : ℝ) ≤
          (goodIncidence (good N) e : ℝ) := by
    filter_upwards [hsmall] with N hN e
    rw [show goodIncidence (good N) e =
        (goodEvent (hashLevel H N) (hashSet H N) (ambient N) (coarse N e)).card from
      goodIncidence_eq _ _ _ _ _]
    exact goodEvent_card_lower (hashLevel H N) (hashSet H N) (ambient N) (S N)
      (hsupport N) (coarse N e) (htarget N e) (degree N) (hdegree N e) hN
  have hyield := eventually_exists_many_good_explicit good hH hpos hinc hE hε
  have hselection := eventually_exists_good_subfamily good
    (fun N => ⌊Real.exp ((N : ℝ) * (A - H - ε))⌋₊) hyield
  filter_upwards [hselection] with N hN
  obtain ⟨s, G, hcard, hgood⟩ := hN
  refine ⟨s, G, hcard, hgood, ?_⟩
  intro e he f hf hne
  exact good_no_shared_side (hashLevel H N) (hashSet H N) (ambient N)
    (coarse N e) (coarse N f) s (hgood e he) (hgood f hf) (htarget N f)
    (fun h => hne ((hinj N) h).symm)

end MatrixMultiplication.JointOrdinarySelection






end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_ZeroLeafRateFormula
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.branchLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.placedLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.RationalLaw.toFiniteLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.Foundation

open scoped BigOperators

theorem entropyTerm_mul (p q : ℝ) :
    entropyTerm (p * q) = q * entropyTerm p + p * entropyTerm q := by
  by_cases hp : p = 0
  · simp [hp]
  by_cases hq : q = 0
  · simp [hq]
  rw [entropyTerm, Real.log_mul hp hq]
  unfold entropyTerm
  ring

theorem finiteEntropy_chain {A B : Type*} [Fintype A] [Fintype B]
    (p : A → ℝ) (q : A → B → ℝ) (hq : ∀ a, ∑ b, q a b = 1) :
    finiteEntropy (fun ab : A × B => p ab.1 * q ab.1 ab.2) =
      finiteEntropy p + ∑ a, p a * finiteEntropy (q a) := by
  simp only [finiteEntropy, Fintype.sum_prod_type, entropyTerm_mul,
    Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hq, one_mul]

namespace FiniteLaw

variable {A B : Type*} [Fintype A] [Fintype B]

theorem map_mass_apply (p : FiniteLaw A) (f : A → B)
    (hf : Function.Injective f) (a : A) : (p.map f).mass (f a) = p.mass a := by
  classical
  simp [map_mass, hf.eq_iff]

theorem map_entropy_of_injective (p : FiniteLaw A) (f : A → B)
    (hf : Function.Injective f) : finiteEntropy (p.map f).mass = finiteEntropy p.mass := by
  classical
  have hterm (b : B) : entropyTerm ((p.map f).mass b) =
      ∑ a, if f a = b then entropyTerm (p.mass a) else 0 := by
    by_cases hb : ∃ a, f a = b
    · obtain ⟨a, rfl⟩ := hb
      rw [map_mass_apply p f hf]
      simp [hf.eq_iff]
    · simp [map_mass, not_exists.mp hb]
  unfold finiteEntropy
  simp_rw [hterm]
  rw [Finset.sum_comm]
  simp

theorem joint_entropy (p : FiniteLaw A) (q : A → FiniteLaw B) :
    finiteEntropy (p.joint q).mass =
      finiteEntropy p.mass + ∑ a, p.mass a * finiteEntropy (q a).mass :=
  finiteEntropy_chain p.mass (fun a => (q a).mass) (fun a => (q a).total)

theorem mass_le_map_mass (p : FiniteLaw A) (f : A → B) (a : A) :
    p.mass a ≤ (p.map f).mass (f a) := by
  classical
  rw [map_mass]
  have h := Finset.single_le_sum
    (s := (Finset.univ : Finset A))
    (f := fun a' => if f a' = f a then p.mass a' else 0)
    (fun a' _ => by
      split_ifs
      · exact p.nonneg a'
      · exact le_rfl)
    (Finset.mem_univ a)
  simpa using h

theorem map_mass_mul_conditional [DecidableEq B]
    (p : FiniteLaw A) (f : A → B) (b : B) (a : A) :
    (p.map f).mass b * (p.conditional f b).mass a =
      if f a = b then p.mass a else 0 := by
  classical
  by_cases hzero : (p.map f).mass b = 0
  · have ha : f a = b → p.mass a = 0 := by
      intro hab
      have hle := p.mass_le_map_mass f a
      rw [hab, hzero] at hle
      exact le_antisymm hle (p.nonneg a)
    rw [hzero, zero_mul]
    by_cases hab : f a = b
    · rw [ite_eq_left hab, ha hab]
    · rw [ite_eq_right hab]
  · simp only [conditional, hzero, ↓reduceDIte]
    by_cases hab : f a = b
    · simpa only [hab, ite_true, if_true] using (mul_div_cancel₀ (p.mass a) hzero)
    · simp only [hab, ite_false, if_false, zero_div, mul_zero]

theorem entropy_eq_map_add_conditional (p : FiniteLaw A) (f : A → B) :
    finiteEntropy p.mass = finiteEntropy (p.map f).mass +
      ∑ b, (p.map f).mass b * finiteEntropy (p.conditional f b).mass := by
  classical
  let graph : A → B × A := fun a => (f a, a)
  have hinj : Function.Injective graph := fun _ _ h => congrArg Prod.snd h
  have hmass : ((p.map f).joint (p.conditional f)).mass = (p.map graph).mass := by
    funext ba
    rcases ba with ⟨b, a⟩
    change (p.map f).mass b * (p.conditional f b).mass a = (p.map graph).mass (b, a)
    rw [map_mass_mul_conditional, map_mass, Finset.sum_eq_single a]
    · simp only [graph, Prod.mk.injEq, and_true]
    · intro x _ hxa
      simp only [graph, Prod.mk.injEq, hxa, and_false, ite_false, if_false]
    · intro ha
      exact (ha (Finset.mem_univ a)).elim
  calc
    finiteEntropy p.mass = finiteEntropy (p.map graph).mass :=
      (p.map_entropy_of_injective graph hinj).symm
    _ = finiteEntropy ((p.map f).joint (p.conditional f)).mass := by rw [hmass]
    _ = _ := (p.map f).joint_entropy (p.conditional f)

end FiniteLaw
end MatrixMultiplication.Foundation

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open scoped Topology
open Filter

namespace MatrixMultiplication.Foundation

theorem entropyTerm_nonneg {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    0 ≤ entropyTerm p :=
  Real.negMulLog_nonneg hp₀ hp₁

theorem tendsto_finiteEntropy_of_tendsto {I A : Type*} [Fintype A]
    {l : Filter I} {p : I → A → ℝ} {q : A → ℝ}
    (h : ∀ a, Tendsto (fun i => p i a) l (𝓝 (q a))) :
    Tendsto (fun i => finiteEntropy (p i)) l (𝓝 (finiteEntropy q)) :=
  continuous_finiteEntropy.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr h)

theorem finiteEntropy_nonneg {A : Type*} [Fintype A] (p : A → ℝ)
    (hp₀ : ∀ a, 0 ≤ p a) (hp₁ : ∀ a, p a ≤ 1) : 0 ≤ finiteEntropy p := by
  exact Finset.sum_nonneg fun a _ => entropyTerm_nonneg (hp₀ a) (hp₁ a)

namespace FiniteLaw

variable {A : Type*} [Fintype A]

theorem mass_le_one (p : FiniteLaw A) (a : A) : p.mass a ≤ 1 := by
  calc
    p.mass a ≤ ∑ b, p.mass b :=
      Finset.single_le_sum (fun b _hb => p.nonneg b) (Finset.mem_univ a)
    _ = 1 := p.total

theorem entropy_nonneg (p : FiniteLaw A) : 0 ≤ finiteEntropy p.mass :=
  finiteEntropy_nonneg p.mass p.nonneg p.mass_le_one

theorem map_entropy_le {B : Type*} [Fintype B] (p : FiniteLaw A) (f : A → B) :
    finiteEntropy (p.map f).mass ≤ finiteEntropy p.mass := by
  calc
    finiteEntropy (p.map f).mass ≤ finiteEntropy (p.map f).mass +
        ∑ b, (p.map f).mass b * finiteEntropy (p.conditional f b).mass :=
      le_add_of_nonneg_right (Finset.sum_nonneg fun b _ =>
        mul_nonneg ((p.map f).nonneg b) ((p.conditional f b).entropy_nonneg))
    _ = finiteEntropy p.mass := (p.entropy_eq_map_add_conditional f).symm

end FiniteLaw
end MatrixMultiplication.Foundation

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_JointPairClassWindows
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_on_group _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.JointCanonicalization.positionEquiv_shape _root_.OAI.MatrixAllFields.MatrixMultiplication.JointCanonicalization.positionEquiv_symm_shape _root_.OAI.MatrixAllFields.MatrixMultiplication.JointPopulationCompatibility.candidateEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.Foundation

open scoped BigOperators

variable {A I J : Type*} [Fintype A] [DecidableEq A] [Fintype I] [Fintype J]
  [DecidableEq I]

theorem exactWords_card_le (counts : A → ℕ) :
    Fintype.card (ExactWords counts) ≤ (Fintype.card A) ^ (∑ a, counts a) := by
  classical
  calc
    Fintype.card (ExactWords counts) ≤
        Fintype.card (Fin (∑ a, counts a) → A) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = _ := by simp

end MatrixMultiplication.Foundation





end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_JointPopulation
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointPopulation

open MatrixMultiplication.Foundation
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {H : Type*} [Fintype H] [DecidableEq H]
    (counts : H → Shape → ℕ)

theorem target_card : Fintype.card (Target counts) =
    ∏ h, Nat.multinomial Finset.univ (counts h) := by
  simp only [Target, Fintype.card_pi, exactWords_card]

omit [Fintype H] [DecidableEq H] in
theorem target_nonempty : Nonempty (Target counts) := ⟨canonicalTarget counts⟩

end MatrixMultiplication.JointPopulation

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_ZeroLeafRates
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.Foundation

open Filter
open scoped Topology

theorem factorialLogRemainder_succ (n : ℕ) :
    factorialLogRemainder (n + 1) = factorialLogRemainder n + 1 -
      (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) := by
  unfold factorialLogRemainder
  rw [Nat.factorial_succ, Nat.cast_mul,
    Real.log_mul (by positivity) (by positivity)]
  push_cast
  ring

private theorem nat_mul_log_increment_le_one (n : ℕ) :
    (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  have hpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hsucc : 0 < (n : ℝ) + 1 := by positivity
  have hlog := Real.log_le_sub_one_of_pos (div_pos hsucc hpos)
  rw [Real.log_div hsucc.ne' hpos.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hpos.le
  have heq : (n : ℝ) * (((n : ℝ) + 1) / (n : ℝ) - 1) = 1 := by
    field_simp [hpos.ne']
    ring
  rwa [heq] at hmul

private theorem one_le_succ_mul_log_increment (n : ℕ) (hn : 0 < n) :
    1 ≤ ((n : ℝ) + 1) * (Real.log ((n : ℝ) + 1) - Real.log n) := by
  have hpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsucc : 0 < (n : ℝ) + 1 := by positivity
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hsucc hpos)
  rw [Real.log_div hsucc.ne' hpos.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hsucc.le
  have heq : ((n : ℝ) + 1) * (1 - (((n : ℝ) + 1) / (n : ℝ))⁻¹) = 1 := by
    rw [inv_div]
    field_simp [hsucc.ne']
    ring
  rwa [heq] at hmul

theorem factorialLogRemainder_nonneg (n : ℕ) : 0 ≤ factorialLogRemainder n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hlog := nat_mul_log_increment_le_one n
    rw [factorialLogRemainder_succ]
    linarith

theorem factorialLogRemainder_le_one_add_log_pos (n : ℕ) :
    factorialLogRemainder (n + 1) ≤ 1 + Real.log (n + 1 : ℕ) := by
  induction n with
  | zero => norm_num [factorialLogRemainder]
  | succ n ih =>
    have hlog := one_le_succ_mul_log_increment (n + 1) (Nat.succ_pos n)
    have hstep := factorialLogRemainder_succ (n + 1)
    push_cast at ih hlog hstep ⊢
    nlinarith

theorem factorialLogRemainder_le_one_add_log (n : ℕ) :
    factorialLogRemainder n ≤ 1 + Real.log (n + 1 : ℕ) := by
  cases n with
  | zero => norm_num
  | succ n =>
    refine (factorialLogRemainder_le_one_add_log_pos n).trans ?_
    apply add_le_add le_rfl
    apply Real.log_le_log
    · positivity
    · exact_mod_cast Nat.le_succ (n + 1)

end MatrixMultiplication.Foundation





namespace MatrixMultiplication.Foundation

open Filter
open scoped BigOperators Topology

variable {A : Type*} [Fintype A]

theorem log_multinomial (counts : A → ℕ) :
    Real.log (Nat.multinomial Finset.univ counts : ℝ) =
      Real.log (Nat.factorial (∑ a, counts a) : ℝ) -
        ∑ a, Real.log (Nat.factorial (counts a) : ℝ) := by
  have hspec :
      (∏ a, (Nat.factorial (counts a) : ℝ)) *
          (Nat.multinomial Finset.univ counts : ℝ) =
        (Nat.factorial (∑ a, counts a) : ℝ) := by
    exact_mod_cast Nat.multinomial_spec Finset.univ counts
  have hprod : (∏ a, (Nat.factorial (counts a) : ℝ)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun a _ => by positivity)
  have hmulti : (Nat.multinomial Finset.univ counts : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.multinomial_pos Finset.univ counts))
  have hlog := congrArg Real.log hspec
  rw [Real.log_mul hprod hmulti,
    Real.log_prod (fun a _ => by positivity)] at hlog
  linarith

private theorem entropyTerm_div_scalar (x y : ℝ) :
    entropyTerm (x / y) = entropyTerm x / y + (x / y) * Real.log y := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [entropyTerm, Real.log_div hx hy]
  unfold entropyTerm
  ring

theorem finiteEntropy_nat_normalize (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) :
    finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) =
      Real.log (∑ a, counts a : ℕ) -
        (∑ a, (counts a : ℝ) * Real.log (counts a : ℝ)) /
          (∑ a, counts a : ℕ) := by
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hD)
  unfold finiteEntropy
  simp only [entropyTerm_div_scalar]
  simp only [entropyTerm, neg_mul,
    Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul,
    Finset.sum_neg_distrib]
  rw [← Nat.cast_sum, div_self hD']
  ring

theorem log_multinomial_eq_main_add_remainder (counts : A → ℕ) :
    Real.log (Nat.multinomial Finset.univ counts : ℝ) =
      (∑ a, counts a : ℕ) * Real.log (∑ a, counts a : ℕ) -
        (∑ a, (counts a : ℝ) * Real.log (counts a : ℝ)) +
        factorialLogRemainder (∑ a, counts a) -
        ∑ a, factorialLogRemainder (counts a) := by
  rw [log_multinomial]
  unfold factorialLogRemainder
  simp only [Finset.sum_sub_distrib, ← Nat.cast_sum]
  ring

theorem log_multinomial_eq_entropy_add_remainder (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) :
    Real.log (Nat.multinomial Finset.univ counts : ℝ) =
      (∑ a, counts a : ℕ) *
          finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) +
        factorialLogRemainder (∑ a, counts a) -
        ∑ a, factorialLogRemainder (counts a) := by
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hD)
  rw [log_multinomial_eq_main_add_remainder, finiteEntropy_nat_normalize counts hD,
    mul_sub, mul_div_cancel₀ _ hD']

theorem log_multinomial_sub_entropy_eq_remainder (counts : A → ℕ) :
    Real.log (Nat.multinomial Finset.univ counts : ℝ) -
        (∑ a, counts a : ℕ) *
          finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) =
      factorialLogRemainder (∑ a, counts a) -
        ∑ a, factorialLogRemainder (counts a) := by
  by_cases hD : 0 < ∑ a, counts a
  · rw [log_multinomial_eq_entropy_add_remainder counts hD]
    ring
  · have hzero : (∑ a, counts a) = 0 := Nat.eq_zero_of_not_pos hD
    have hc : ∀ a, counts a = 0 := by
      intro a
      have hle : counts a ≤ ∑ b, counts b :=
        Finset.single_le_sum (fun b _ => Nat.zero_le (counts b)) (Finset.mem_univ a)
      rw [hzero] at hle
      exact Nat.eq_zero_of_le_zero hle
    simp [hc, Nat.multinomial]

theorem abs_log_multinomial_sub_entropy_le (counts : A → ℕ) :
    |Real.log (Nat.multinomial Finset.univ counts : ℝ) -
        (∑ a, counts a : ℕ) *
          finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))| ≤
      ((Fintype.card A : ℝ) + 1) *
        (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) := by
  rw [log_multinomial_sub_entropy_eq_remainder]
  have hsum_nonneg : 0 ≤ ∑ a, factorialLogRemainder (counts a) :=
    Finset.sum_nonneg (fun a _ => factorialLogRemainder_nonneg (counts a))
  have heach (a : A) : factorialLogRemainder (counts a) ≤
      1 + Real.log ((∑ b, counts b) + 1 : ℕ) := by
    refine (factorialLogRemainder_le_one_add_log (counts a)).trans ?_
    apply add_le_add le_rfl
    apply Real.log_le_log
    · positivity
    · have hle : counts a ≤ ∑ b, counts b :=
        Finset.single_le_sum (fun b _ => Nat.zero_le (counts b)) (Finset.mem_univ a)
      exact_mod_cast Nat.add_le_add_right hle 1
  calc
    |factorialLogRemainder (∑ a, counts a) - ∑ a, factorialLogRemainder (counts a)| ≤
        |factorialLogRemainder (∑ a, counts a)| +
          |∑ a, factorialLogRemainder (counts a)| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (factorialLogRemainder (∑ a, counts a))
          (-(∑ a, factorialLogRemainder (counts a)))
    _ = factorialLogRemainder (∑ a, counts a) +
        ∑ a, factorialLogRemainder (counts a) := by
      rw [abs_of_nonneg (factorialLogRemainder_nonneg _), abs_of_nonneg hsum_nonneg]
    _ ≤ (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) +
        ∑ _a : A, (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) :=
      add_le_add (factorialLogRemainder_le_one_add_log _)
        (Finset.sum_le_sum (fun a _ => heach a))
    _ = ((Fintype.card A : ℝ) + 1) *
        (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

theorem abs_log_multinomial_div_sub_entropy_le (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) :
    |Real.log (Nat.multinomial Finset.univ counts : ℝ) / (∑ a, counts a : ℕ) -
        finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))| ≤
      ((Fintype.card A : ℝ) + 1) *
        ((1 + Real.log ((∑ a, counts a) + 1 : ℕ)) / (∑ a, counts a : ℕ)) := by
  have hD' : (0 : ℝ) < (∑ a, counts a : ℕ) := Nat.cast_pos.mpr hD
  calc
    |Real.log (Nat.multinomial Finset.univ counts : ℝ) / (∑ a, counts a : ℕ) -
        finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))| =
        |(Real.log (Nat.multinomial Finset.univ counts : ℝ) -
          (∑ a, counts a : ℕ) *
            finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))) /
              (∑ a, counts a : ℕ)| := by
      rw [sub_div, mul_div_cancel_left₀ _ hD'.ne']
    _ = |Real.log (Nat.multinomial Finset.univ counts : ℝ) -
          (∑ a, counts a : ℕ) *
            finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))| /
              (∑ a, counts a : ℕ) := by
      rw [abs_div, abs_of_pos hD']
    _ ≤ ((Fintype.card A : ℝ) + 1) *
        ((1 + Real.log ((∑ a, counts a) + 1 : ℕ)) / (∑ a, counts a : ℕ)) := by
      simpa only [mul_div_assoc] using
        div_le_div_of_nonneg_right (abs_log_multinomial_sub_entropy_le counts) hD'.le

private theorem tendsto_one_add_log_succ_div :
    Tendsto (fun n : ℕ => (1 + Real.log (n + 1 : ℕ)) / (n : ℝ))
      atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hconstant : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hnat
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / n) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hnat
  have hshift := Real.tendsto_log_nat_add_one_sub_log.div_atTop hnat
  have hsum : Tendsto
      (fun n : ℕ => (1 : ℝ) / n +
        ((Real.log ((n : ℝ) + 1) - Real.log n) / n + Real.log n / n))
      atTop (𝓝 0) := by
    simpa using hconstant.add (hshift.add hlog)
  apply hsum.congr
  intro n
  push_cast
  ring

theorem tendsto_log_multinomial_div_sub_entropy {I : Type*} {l : Filter I}
    (counts : I → A → ℕ)
    (htotal : Tendsto (fun i => ∑ a, counts i a) l atTop) :
    Tendsto
      (fun i => Real.log (Nat.multinomial Finset.univ (counts i) : ℝ) /
          (∑ a, counts i a : ℕ) -
        finiteEntropy (fun a => (counts i a : ℝ) / (∑ a, counts i a : ℕ)))
      l (𝓝 0) := by
  have hbound : Tendsto
      (fun i => ((Fintype.card A : ℝ) + 1) *
        ((1 + Real.log ((∑ a, counts i a) + 1 : ℕ)) / (∑ a, counts i a : ℕ)))
      l (𝓝 0) := by
    simpa using (tendsto_one_add_log_succ_div.comp htotal).const_mul
      ((Fintype.card A : ℝ) + 1)
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [htotal.eventually (eventually_gt_atTop (0 : ℕ))] with i hi
  simpa only [Real.norm_eq_abs] using
    abs_log_multinomial_div_sub_entropy_le (counts i) hi

theorem tendsto_log_multinomial_of_empirical_tendsto {I : Type*} {l : Filter I}
    (counts : I → A → ℕ) (p : A → ℝ)
    (htotal : Tendsto (fun i => ∑ a, counts i a) l atTop)
    (hmass : ∀ a, Tendsto
      (fun i => (counts i a : ℝ) / (∑ b, counts i b : ℕ)) l (𝓝 (p a))) :
    Tendsto
      (fun i => Real.log (Nat.multinomial Finset.univ (counts i) : ℝ) /
        (∑ a, counts i a : ℕ))
      l (𝓝 (finiteEntropy p)) := by
  have herror := tendsto_log_multinomial_div_sub_entropy counts htotal
  have hentropy := tendsto_finiteEntropy_of_tendsto hmass
  simpa only [zero_add, sub_add_cancel] using herror.add hentropy

end MatrixMultiplication.Foundation





end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_GroupBranchLaws
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointPopulationRates

open MatrixMultiplication.Foundation Filter JointPopulation
open scoped BigOperators Topology

theorem tendsto_log_multinomial_div_of_total_div_zero
    {A : Type*} [Fintype A] [DecidableEq A] (counts : ℕ → A → ℕ)
    (hratio : Tendsto
      (fun n : ℕ => ((∑ a, counts n a : ℕ) : ℝ) / (n : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      Real.log (Nat.multinomial Finset.univ (counts n) : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
  have hupperlim : Tendsto
      (fun n : ℕ => (((∑ a, counts n a : ℕ) : ℝ) / (n : ℝ)) *
        Real.log (Fintype.card A : ℝ)) atTop (𝓝 0) := by
    simpa using hratio.mul_const (Real.log (Fintype.card A : ℝ))
  refine squeeze_zero ?_ ?_ hupperlim
  · intro n
    apply div_nonneg
    · apply Real.log_nonneg
      exact_mod_cast (Nat.succ_le_of_lt (Nat.multinomial_pos Finset.univ (counts n)))
    · exact Nat.cast_nonneg n
  · intro n
    have hcardNat : Nat.multinomial Finset.univ (counts n) ≤
        (Fintype.card A) ^ (∑ a, counts n a) := by
      simpa only [exactWords_card] using exactWords_card_le (counts n)
    have hcard : (Nat.multinomial Finset.univ (counts n) : ℝ) ≤
        (Fintype.card A : ℝ) ^ (∑ a, counts n a) := by
      exact_mod_cast hcardNat
    have hlog : Real.log (Nat.multinomial Finset.univ (counts n) : ℝ) ≤
        ((∑ a, counts n a : ℕ) : ℝ) * Real.log (Fintype.card A : ℝ) := by
      simpa only [Real.log_pow] using
        Real.log_le_log (Nat.cast_pos.mpr (Nat.multinomial_pos Finset.univ (counts n))) hcard
    calc
      Real.log (Nat.multinomial Finset.univ (counts n) : ℝ) / (n : ℝ) ≤
          (((∑ a, counts n a : ℕ) : ℝ) * Real.log (Fintype.card A : ℝ)) / (n : ℝ) :=
        div_le_div_of_nonneg_right hlog (Nat.cast_nonneg n)
      _ = (((∑ a, counts n a : ℕ) : ℝ) / (n : ℝ)) *
          Real.log (Fintype.card A : ℝ) := by ring

theorem tendsto_log_multinomial_div_of_mass
    {A : Type*} [Fintype A] [DecidableEq A] (counts : ℕ → A → ℕ)
    (mass : ℝ) (p : A → ℝ) (hmass : 0 ≤ mass)
    (htotal : Tendsto (fun n : ℕ => (∑ a, counts n a : ℕ) / (n : ℝ))
      atTop (𝓝 mass))
    (hempirical : 0 < mass → ∀ a, Tendsto
      (fun n : ℕ => (counts n a : ℝ) / (∑ a, counts n a : ℕ)) atTop (𝓝 (p a))) :
    Tendsto (fun n : ℕ => Real.log (Nat.multinomial Finset.univ (counts n) : ℝ) /
      (n : ℝ)) atTop (𝓝 (mass * finiteEntropy p)) := by
  by_cases hzero : mass = 0
  · subst mass
    simpa only [zero_mul] using tendsto_log_multinomial_div_of_total_div_zero counts htotal
  have hpos : 0 < mass := lt_of_le_of_ne hmass (Ne.symm hzero)
  have htop : Tendsto (fun n => ∑ a, counts n a) atTop atTop :=
    (tendsto_natCast_atTop_iff (R := ℝ)).mp
      (Tendsto.num (tendsto_natCast_atTop_atTop (R := ℝ)) hpos htotal)
  have hlog := tendsto_log_multinomial_of_empirical_tendsto counts p htop (hempirical hpos)
  apply (htotal.mul hlog).congr'
  filter_upwards [htop.eventually (eventually_gt_atTop (0 : ℕ))] with n hn
  have hn' : ((∑ a, counts n a : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  rw [div_mul_div_comm,
    mul_comm (n : ℝ) ((∑ a, counts n a : ℕ) : ℝ), mul_div_mul_left _ _ hn']

theorem tendsto_total_div_of_coordinate_rates
    {A : Type*} [Fintype A] (counts : ℕ → A → ℕ)
    (mass : ℝ) (p : A → ℝ) (hp : ∑ a, p a = 1)
    (hcounts : ∀ a, Tendsto (fun n : ℕ => (counts n a : ℝ) / (n : ℝ))
      atTop (𝓝 (mass * p a))) :
    Tendsto (fun n : ℕ => (∑ a, counts n a : ℕ) / (n : ℝ)) atTop (𝓝 mass) := by
  have h := tendsto_finsetSum Finset.univ (fun a _ => hcounts a)
  simpa only [← Finset.sum_div, ← Nat.cast_sum, ← Finset.mul_sum, hp, mul_one] using h

theorem tendsto_empirical_of_coordinate_rates
    {A : Type*} [Fintype A] (counts : ℕ → A → ℕ)
    (mass : ℝ) (p : A → ℝ) (hmass : 0 < mass) (hp : ∑ a, p a = 1)
    (hcounts : ∀ a, Tendsto (fun n : ℕ => (counts n a : ℝ) / (n : ℝ))
      atTop (𝓝 (mass * p a))) (a : A) :
    Tendsto (fun n : ℕ => (counts n a : ℝ) / (∑ a, counts n a : ℕ))
      atTop (𝓝 (p a)) := by
  have htotal := tendsto_total_div_of_coordinate_rates counts mass p hp hcounts
  have h := (hcounts a).div htotal hmass.ne'
  rw [mul_div_cancel_left₀ _ hmass.ne'] at h
  apply h.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
  exact div_div_div_cancel_right₀ (Nat.cast_ne_zero.mpr hn) _ _

variable {H : Type*} [Fintype H] [DecidableEq H]

theorem tendsto_log_target_card_div
    (counts : ℕ → H → Shape → ℕ) (mass : H → ℝ) (p : H → Shape → ℝ)
    (hmass : ∀ h, 0 ≤ mass h)
    (htotal : ∀ h, Tendsto (fun n : ℕ => (∑ a, counts n h a : ℕ) / (n : ℝ))
      atTop (𝓝 (mass h)))
    (hempirical : ∀ h, 0 < mass h → ∀ a, Tendsto
      (fun n : ℕ => (counts n h a : ℝ) / (∑ a, counts n h a : ℕ))
        atTop (𝓝 (p h a))) :
    Tendsto (fun n : ℕ => Real.log (Fintype.card (Target (counts n)) : ℝ) / (n : ℝ))
      atTop (𝓝 (∑ h, mass h * finiteEntropy (p h))) := by
  simp_rw [target_card]
  exact Separation.tendsto_log_nat_prod_div_nat Finset.univ
    (fun h _ n => Nat.multinomial_pos _ _)
    (fun h _ => tendsto_log_multinomial_div_of_mass
      (fun n => counts n h) (mass h) (p h) (hmass h) (htotal h) (hempirical h))

theorem tendsto_log_target_card_div_of_coordinate_rates
    (counts : ℕ → H → Shape → ℕ) (mass : H → ℝ) (p : H → Shape → ℝ)
    (hmass : ∀ h, 0 ≤ mass h) (hp : ∀ h, ∑ a, p h a = 1)
    (hcounts : ∀ h a, Tendsto (fun n : ℕ => (counts n h a : ℝ) / (n : ℝ))
      atTop (𝓝 (mass h * p h a))) :
    Tendsto (fun n : ℕ => Real.log (Fintype.card (Target (counts n)) : ℝ) / (n : ℝ))
      atTop (𝓝 (∑ h, mass h * finiteEntropy (p h))) := by
  apply tendsto_log_target_card_div counts mass p hmass
  · intro h
    exact tendsto_total_div_of_coordinate_rates (fun n => counts n h)
      (mass h) (p h) (hp h) (hcounts h)
  · intro h hpos a
    exact tendsto_empirical_of_coordinate_rates (fun n => counts n h)
      (mass h) (p h) hpos (hp h) (hcounts h) a

end MatrixMultiplication.JointPopulationRates






end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_JointOrdinaryPopulationSelection
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section





noncomputable section

namespace MatrixMultiplication.JointOrdinaryPopulationSelection

open MatrixMultiplication.Foundation JointPopulation JointPopulationRates Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

variable {Hist : Type*} [Fintype Hist] [DecidableEq Hist]

theorem sideMass_entropy_le (p : FiniteLaw Shape) (s : Fin 3) :
    finiteEntropy (sideMass p.mass s) ≤ finiteEntropy p.mass := by
  simpa only [finiteEntropy, FiniteLaw.map_mass, sideMass] using
    p.map_entropy_le (shapeSide s)

omit [DecidableEq Hist] in
theorem sideDegreeRate_nonneg (mass : Hist → ℝ) (p : Hist → FiniteLaw Shape)
    (hmass : ∀ h, 0 ≤ mass h) (s : Fin 3) : 0 ≤ sideDegreeRate mass p s := by
  exact Finset.sum_nonneg fun h _ =>
    mul_nonneg (hmass h) (sub_nonneg.mpr (sideMass_entropy_le (p h) s))

omit [DecidableEq Hist] in
theorem degreeRate_nonneg (mass : Hist → ℝ) (p : Hist → FiniteLaw Shape)
    (hmass : ∀ h, 0 ≤ mass h) : 0 ≤ degreeRate mass p :=
  (sideDegreeRate_nonneg mass p hmass 0).trans (le_max_left _ _)

theorem ordinary_neighbors_eq (counts : Hist → Shape → ℕ) (sum : Hist → ℕ)
    (e : JointCoarseHashing.Triple (Position counts)) :
    JointOrdinarySelection.neighbors (ambientSet counts sum) e =
      JointAmbientDegree.neighbors counts sum e := by
  ext neighbor
  rw [JointOrdinarySelection.mem_neighbors, JointAmbientDegree.neighbors,
    Finset.mem_filter]
  simp only [JointCoarseHashing.SharesSide, eq_comm]

theorem neighbors_card_le_uniformDegree (counts : Hist → Shape → ℕ)
    (sum : Hist → ℕ) (e : Target counts) :
    (JointOrdinarySelection.neighbors (ambientSet counts sum) (triple counts e)).card ≤
      uniformDegree counts sum := by
  rw [ordinary_neighbors_eq]
  exact Finset.le_sup
    (f := fun e : Target counts =>
      (JointAmbientDegree.neighbors counts sum (triple counts e)).card)
    (Finset.mem_univ e)

theorem eventually_exists_selection_of_word_support_oai
    (counts : ℕ → Hist → Shape → ℕ) (sum : Hist → ℕ) (mass : Hist → ℝ)
    (p : Hist → FiniteLaw Shape) (u v w : Hist → Fin 17 → ℝ) (c : Hist → ℝ)
    (hmass : ∀ h, 0 ≤ mass h)
    (hcountSupport : ∀ N h a, 0 < counts N h a →
      a.1.val + a.2.1.val + a.2.2.val = sum h)
    (hsupport : ∀ᶠ N in atTop, ∀ h word,
      JointAmbientDegree.localAllowed (counts N) sum h word →
        ∀ i, 0 < (p h).mass (word i))
    (hlog : ∀ h a, 0 < (p h).mass a → Real.log ((p h).mass a) =
      u h (shapeSide 0 a) + v h (shapeSide 1 a) + w h (shapeSide 2 a) - c h)
    (hcounts : ∀ h a, Tendsto (fun N : ℕ => (counts N h a : ℝ) / (N : ℝ))
      atTop (𝓝 (mass h * (p h).mass a)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop,
      ∃ (s : JointCoarseHashing.Sample (Position (counts N))
          (JointOrdinarySelection.hashLevel (selectionHashRate mass p ε) N))
        (G : Finset (Target (counts N))),
        G.card = ⌊Real.exp ((N : ℝ) * (entropyRate mass p - degreeRate mass p - ε))⌋₊ ∧
        (∀ e ∈ G, JointOrdinarySelection.Good
          (JointOrdinarySelection.hashLevel (selectionHashRate mass p ε) N)
          (JointOrdinarySelection.hashSet (selectionHashRate mass p ε) N)
          (ambientSet (counts N) sum) (triple (counts N) e) s) ∧
        (G : Set (Target (counts N))).Pairwise (fun e f =>
          ¬ JointCoarseHashing.SharesSide (triple (counts N) e) (triple (counts N) f)) := by
  have hD : 0 ≤ degreeRate mass p := degreeRate_nonneg mass p hmass
  have hH : 0 ≤ selectionHashRate mass p ε := by unfold selectionHashRate; linarith
  have hgap : degreeRate mass p < selectionHashRate mass p ε := by
    unfold selectionHashRate
    linarith
  have htarget (N : ℕ) (e : Target (counts N)) :
      triple (counts N) e ∈ ambientSet (counts N) sum := by
    apply targetSet_subset_ambient (counts N) sum (hcountSupport N)
    exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩
  have hpos : ∀ᶠ N in atTop, 0 < Fintype.card (Target (counts N)) :=
    Eventually.of_forall fun N => Fintype.card_pos_iff.mpr (target_nonempty (counts N))
  have htargetRate : Tendsto (fun N : ℕ =>
      Real.log (Fintype.card (Target (counts N)) : ℝ) / (N : ℝ))
      atTop (𝓝 (entropyRate mass p)) :=
    tendsto_log_target_card_div_of_coordinate_rates counts mass
      (fun h => (p h).mass) hmass (fun h => (p h).total) hcounts
  have hselection := JointOrdinarySelection.eventually_exists_selection
    (fun N => ambientSet (counts N) sum)
    (fun N (position : Position (counts N)) => sum position.1)
    (fun N => triple (counts N)) (fun N => triple_injective (counts N))
    (fun N f hf => (Finset.mem_filter.mp hf).2.1) htarget
    (fun N => uniformDegree (counts N) sum)
    (fun N e => neighbors_card_le_uniformDegree (counts N) sum e)
    hH hgap (uniformDegree_log_upper_of_word_support counts sum mass p u v w c
      hmass hsupport hlog hcounts)
    hpos htargetRate (show 0 < ε / 2 by linarith)
  have heq : entropyRate mass p - selectionHashRate mass p ε - ε / 2 =
      entropyRate mass p - degreeRate mass p - ε := by unfold selectionHashRate; ring
  simpa only [heq] using hselection

end MatrixMultiplication.JointOrdinaryPopulationSelection

end
end

end MatrixAllFields

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MatrixAllFields.MatrixMultiplication.JointOrdinaryPopulationSelection.eventually_exists_selection_of_word_support_oai.{u_1} := @OAI.MatrixAllFields.MatrixMultiplication.JointOrdinaryPopulationSelection.eventually_exists_selection_of_word_support_oai.{u_1}
