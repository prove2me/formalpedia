-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.JointMaskedGoodSelection.eventually_exists_good_selection
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:26:15.519632+00:00
-- url     : https://prove2.me/submissions/c94dfe40-0c4a-4391-9a5e-e69c18ff81ce

import Mathlib
import Definitions.Def_OAIQ254M003
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_JointMaskedSelection_OrbitData_goodEvent_card_lower

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
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section





noncomputable section






namespace MatrixMultiplication.JointMaskedSelection

open JointCoarseHashing JointExtractionRates

attribute [local instance] Classical.propDecidable

variable {P E O V : Type*}

namespace OrbitData

section Finite

variable [Fintype P]

theorem goodIncidence_eq (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k))) (N : ℝ) (e : E) :
    goodIncidence (fun s e => d.Good k U N e s) e = (d.goodEvent k U N e).card := by
  unfold goodIncidence
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_goodEvent]

theorem good_no_shared_x (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k))) (N : ℝ) (e f : E) (s : Sample P k)
    (he : d.Good k U N e s) (hf : d.Good k U N f s)
    (hne : d.coarse f ≠ d.coarse e) : (d.coarse f).1 ≠ (d.coarse e).1 := by
  intro hx
  exact d.good_eligibility k U N e s he
    ⟨d.coarse f, (d.mem_eligibilityCompetitors e _).2 ⟨d.target_mem f, hne, hx⟩, hf.1⟩

end Finite

end OrbitData

end MatrixMultiplication.JointMaskedSelection

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_JointMaskedRates
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

namespace MatrixMultiplication.JointMaskedRates

open Filter JointCoarseHashing JointExtractionRates JointMaskedSelection
open JointOrdinarySelection (hashLevel hashSet)
open scoped Topology

attribute [local instance] Classical.propDecidable

theorem polynomialFactor_le (B p N : ℕ) :
    1 + (B : ℝ) * ((N : ℝ) + 1) ^ p * (N : ℝ) ≤
      ((B : ℝ) + 1) * ((N : ℝ) + 1) ^ (p + 1) := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hx : (0 : ℝ) ≤ (N : ℝ) + 1 := by linarith
  have hpower : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ (p + 1) :=
    one_le_pow₀ (by linarith : (1 : ℝ) ≤ (N : ℝ) + 1)
  calc
    _ ≤ 1 + (B : ℝ) * ((N : ℝ) + 1) ^ p * ((N : ℝ) + 1) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (by linarith)
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx _)))
    _ = 1 + (B : ℝ) * ((N : ℝ) + 1) ^ (p + 1) := by rw [pow_succ]; ring
    _ ≤ ((N : ℝ) + 1) ^ (p + 1) + (B : ℝ) * ((N : ℝ) + 1) ^ (p + 1) :=
      add_le_add hpower le_rfl
    _ = _ := by ring

theorem eventually_errorBound_le_half (degree : ℕ → ℕ) (B p : ℕ)
    {D H : ℝ} (hH : 0 ≤ H) (hgap : D < H)
    (hdegreeRate : ∀ η : ℝ, 0 < η →
      ∀ᶠ N in atTop, Real.log (degree N : ℝ) / (N : ℝ) ≤ D + η) :
    ∀ᶠ N in atTop, errorBound degree B p H N ≤ 1 / 2 := by
  let c : ℝ := (H - D) / 2
  have hc : 0 < c := by dsimp [c] <;> linarith
  have hclt : c < H - D := by dsimp [c] <;> linarith
  have hratio := eventually_degree_div_hashModulus_le_exp hH hdegreeRate hclt
  apply eventually_error_le_half ((B : ℝ) + 1) (p + 1) hc
  filter_upwards [hratio] with N hN
  have hx : (0 : ℝ) ≤ (N : ℝ) + 1 := add_nonneg (Nat.cast_nonneg N) zero_le_one
  have hfactor : 0 ≤ 1 + (B : ℝ) * ((N : ℝ) + 1) ^ p * (N : ℝ) :=
    add_nonneg zero_le_one
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx _)) (Nat.cast_nonneg _))
  calc
    errorBound degree B p H N ≤ Real.exp (-c * (N : ℝ)) *
        (1 + (B : ℝ) * ((N : ℝ) + 1) ^ p * (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hN hfactor
    _ ≤ Real.exp (-c * (N : ℝ)) * (((B : ℝ) + 1) * ((N : ℝ) + 1) ^ (p + 1)) :=
      mul_le_mul_of_nonneg_left (polynomialFactor_le B p N) (Real.exp_pos _).le
    _ = ((B : ℝ) + 1) * (((N : ℝ) + 1) ^ (p + 1) * Real.exp (-c * (N : ℝ))) := by ring

theorem count_error_le_envelope {P E O V : Type*} (d : OrbitData P E O V)
    (e : E) (degree B p N M : ℕ)
    (heligibility : (d.eligibilityCompetitors e).card ≤ degree)
    (horbits : (d.orbits e).card ≤ B * (N + 1) ^ p) :
    ((d.eligibilityCompetitors e).card : ℝ) / (M : ℝ) +
      ((d.orbits e).card : ℝ) * (N : ℝ) * ((degree : ℝ) / (M : ℝ)) ≤
    (degree : ℝ) / (M : ℝ) * (1 + (B : ℝ) * ((N : ℝ) + 1) ^ p * (N : ℝ)) := by
  have hdegreeR : ((d.eligibilityCompetitors e).card : ℝ) ≤ (degree : ℝ) := by
    exact_mod_cast heligibility
  have horbitsR : ((d.orbits e).card : ℝ) ≤ (B : ℝ) * ((N : ℝ) + 1) ^ p := by
    exact_mod_cast horbits
  have hratio : (0 : ℝ) ≤ (degree : ℝ) / (M : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  calc
    _ ≤ (degree : ℝ) / (M : ℝ) +
        ((B : ℝ) * ((N : ℝ) + 1) ^ p) * (N : ℝ) * ((degree : ℝ) / (M : ℝ)) :=
      add_le_add (div_le_div_of_nonneg_right hdegreeR (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right horbitsR (Nat.cast_nonneg _)) hratio)
    _ = _ := by ring

end MatrixMultiplication.JointMaskedRates

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_JointMaskedGoodSelection
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointMaskedGoodSelection

open Filter JointCoarseHashing JointExtractionRates JointMaskedSelection
open JointOrdinarySelection (hashLevel hashSet)
open JointMaskedRates
open scoped Topology

attribute [local instance] Classical.propDecidable

theorem eventually_exists_good_selection_oai
    {P E O V : ℕ → Type*} [∀ N, Fintype (P N)] [∀ N, Fintype (E N)]
    (d : ∀ N, OrbitData (P N) (E N) (O N) (V N))
    (hinj : ∀ N, Function.Injective (d N).coarse)
    (degree : ℕ → ℕ) (B p : ℕ)
    (heligibility : ∀ N e, ((d N).eligibilityCompetitors e).card ≤ degree N)
    (hdegree : ∀ N e, ∀ o ∈ (d N).orbits e, ∀ v ∈ (d N).passing e o,
      ((d N).competitors e o v).card ≤ degree N)
    (horbits : ∀ N e, ((d N).orbits e).card ≤ B * (N + 1) ^ p)
    {A D H : ℝ} (hH : 0 ≤ H) (hgap : D < H)
    (hdegreeRate : ∀ η : ℝ, 0 < η →
      ∀ᶠ N in atTop, Real.log (degree N : ℝ) / (N : ℝ) ≤ D + η)
    (hpos : ∀ᶠ N in atTop, 0 < Fintype.card (E N))
    (hE : Tendsto (fun N => Real.log (Fintype.card (E N) : ℝ) / (N : ℝ)) atTop (𝓝 A))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ (s : Sample (P N) (hashLevel H N)) (G : Finset (E N)),
      G.card = ⌊Real.exp ((N : ℝ) * (A - H - ε))⌋₊ ∧
      (∀ e ∈ G, (d N).Good (hashLevel H N) (hashSet H N) (N : ℝ) e s) ∧
      (∀ e ∈ G, ∀ f ∈ G, e ≠ f → ((d N).coarse e).1 ≠ ((d N).coarse f).1) := by
  classical
  have huniform := eventually_errorBound_le_half degree B p hH hgap hdegreeRate
  have hsmall : ∀ᶠ N in atTop, ∀ e,
      (((d N).eligibilityCompetitors e).card : ℝ) / (hashModulus H N : ℝ) +
        (((d N).orbits e).card : ℝ) * (N : ℝ) *
          ((degree N : ℝ) / (hashModulus H N : ℝ)) ≤ 1 / 2 := by
    filter_upwards [huniform] with N hN e
    exact (count_error_le_envelope (d N) e (degree N) B p N (hashModulus H N)
      (heligibility N e) (horbits N e)).trans hN
  have hpositive : ∀ᶠ N : ℕ in atTop, (0 : ℝ) < N := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact_mod_cast hN
  let good := fun N (s : Sample (P N) (hashLevel H N)) (e : E N) =>
    (d N).Good (hashLevel H N) (hashSet H N) (N : ℝ) e s
  have hinc : ∀ᶠ N in atTop, ∀ e,
      (((JointAPFree.modularSet (hashModulus H N)).card : ℝ) /
        (hashModulus H N : ℝ) ^ 2 / 2) *
        (Fintype.card (Sample (P N) (hashLevel H N)) : ℝ) ≤
          (goodIncidence (good N) e : ℝ) := by
    filter_upwards [hsmall, hpositive] with N hN hNpos e
    rw [show goodIncidence (good N) e =
        ((d N).goodEvent (hashLevel H N) (hashSet H N) (N : ℝ) e).card from
      (d N).goodIncidence_eq _ _ _ _]
    exact (d N).goodEvent_card_lower (hashLevel H N) (hashSet H N) (N : ℝ) hNpos e
      (degree N) (hdegree N e) (hN e)
  have hyield := eventually_exists_many_good_explicit good hH hpos hinc hE hε
  have hselection := eventually_exists_good_subfamily good
    (fun N => ⌊Real.exp ((N : ℝ) * (A - H - ε))⌋₊) hyield
  filter_upwards [hselection] with N hN
  obtain ⟨s, G, hcard, hgood⟩ := hN
  refine ⟨s, G, hcard, hgood, ?_⟩
  intro e he f hf hne
  exact (d N).good_no_shared_x (hashLevel H N) (hashSet H N) (N : ℝ) f e s
    (hgood f hf) (hgood e he) (fun h => hne ((hinj N) h))

end MatrixMultiplication.JointMaskedGoodSelection

end
end

end MatrixAllFields

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.MatrixAllFields.MatrixMultiplication.JointMaskedGoodSelection.eventually_exists_good_selection_oai.{u_1, u_2, u_3, u_4} := @OAI.MatrixAllFields.MatrixMultiplication.JointMaskedGoodSelection.eventually_exists_good_selection_oai.{u_1, u_2, u_3, u_4}
