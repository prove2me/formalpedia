-- Prove2me | solution 1 for OAI.Ostmann.eventual_constituent_final_pair_decay
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:07:44.905956+00:00
-- url     : https://prove2.me/submissions/1070dc96-f046-4805-b03c-755726bf4d5b

import Mathlib
import Definitions.Def_OAIQ095D007
import Theorems.Thm_OAI_Ostmann_constituent_final_pair_bound

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_CommonHistoryPeriod
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A nonzero common modulus constructed from the actual small frequencies -/

namespace Ostmann

theorem historyFrequencyPeriod_le (frequencies : List ℤ) (V degree : ℕ)
    (hV : ∀ s ∈ frequencies, s.natAbs ≤ V) :
    historyFrequencyPeriod frequencies degree ≤ V ^ (frequencies.length * degree) := by
  have hb : historyFrequencyBase frequencies ≤ V ^ frequencies.length := by
    induction frequencies with
    | nil => simp [historyFrequencyBase]
    | cons s rest ih =>
      simp only [historyFrequencyBase, List.map_cons, List.prod_cons, List.length_cons, pow_succ]
      exact (Nat.mul_le_mul (hV s (by simp))
        (ih (fun t ht => hV t (by simp [ht])))).trans_eq (Nat.mul_comm _ _)
  exact (Nat.pow_le_pow_left hb degree).trans_eq (pow_mul V frequencies.length degree).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OneSidedDecayBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The separated long/short scales absorb the one-sided losses -/

namespace Ostmann

open Filter

theorem eventual_polynomial_log_budget (C z α ε : ℝ) (d : ℕ)
    (hC : 0 ≤ C) (hz : 0 ≤ z) (hα : 0 < α) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ m : ℝ, 0 ≤ m → m ≤ z * L →
      C * (1 + m) ^ d ≤ ε * Real.exp (α * L) := by
  have hb := ((isLittleO_pow_exp_pos_mul_atTop d hα).const_mul_left
    (C * (z + 1) ^ d)).bound hε
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with L hlarge hL m hm hmL
  have hx : 1 + m ≤ (z + 1) * L := by nlinarith
  have hp : (1 + m) ^ d ≤ ((z + 1) * L) ^ d := pow_le_pow_left₀ (by linarith) hx d
  have hlarge' : C * (z + 1) ^ d * L ^ d ≤ ε * Real.exp (α * L) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ C * (z + 1) ^ d * L ^ d),
      abs_of_pos (Real.exp_pos _)] using hlarge
  calc
    _ ≤ C * (((z + 1) * L) ^ d) := mul_le_mul_of_nonneg_left hp hC
    _ = C * (z + 1) ^ d * L ^ d := by rw [mul_pow]; ring
    _ ≤ _ := hlarge'

/-- The square-mean off-diagonal error after all polynomial history costs.
The long logarithmic scale β exceeds both the short scale γ and the desired
error scale α. -/
theorem eventual_separated_character_error (C z α β γ c : ℝ) (d : ℕ)
    (hC : 0 ≤ C) (hz : 0 ≤ z) (hα : 0 < α) (hαβ : α < β)
    (hγβ : γ < β) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ m : ℝ, 0 ≤ m → m ≤ z * L →
      Real.exp (C * (1 + m) ^ d + 2 * Real.exp (γ * L) - Real.exp (β * L)) ≤
        Real.exp (-c * Real.exp (α * L)) := by
  have hpoly := eventual_polynomial_log_budget C z β (1 / 4) d hC hz (hα.trans hαβ) (by norm_num)
  have hshort := ((isLittleO_exp_mul_rpow_of_lt 0 hγβ).const_mul_left (2 : ℝ)).bound
    (by norm_num : (0 : ℝ) < 1 / 4)
  have herr := ((isLittleO_exp_mul_rpow_of_lt 0 hαβ).const_mul_left c).bound
    (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [hpoly, hshort, herr] with L hpoly hshort herr m hm hmL
  have hs : 2 * Real.exp (γ * L) ≤ Real.exp (β * L) / 4 := by
    simpa only [Real.rpow_zero, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ 2 * Real.exp (γ * L)),
      abs_of_pos (Real.exp_pos _), one_div_mul_eq_div] using hshort
  have he : c * Real.exp (α * L) ≤ Real.exp (β * L) / 4 := by
    simpa only [Real.rpow_zero, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ c * Real.exp (α * L)),
      abs_of_pos (Real.exp_pos _), one_div_mul_eq_div] using herr
  have hp := hpoly m hm hmL
  apply Real.exp_le_exp.mpr
  nlinarith [Real.exp_pos (β * L)]

/-- The small diagonal atom remains exponentially small after multiplication
by every fixed polynomial-in-m exponential loss. -/
theorem eventual_diagonal_atom_error (C z α c : ℝ) (d : ℕ)
    (hC : 0 ≤ C) (hz : 0 ≤ z) (hα : 0 < α) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ m : ℝ, 0 ≤ m → m ≤ z * L →
      2 * Real.exp (C * (1 + m) ^ d - c * Real.exp (α * L)) ≤
        Real.exp (-(c / 2) * Real.exp (α * L)) := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hb := eventual_polynomial_log_budget (C + Real.log 2) z α (c / 2) d
    (by positivity) hz hα (by positivity)
  filter_upwards [hb] with L hb m hm hmL
  have hpow : 1 ≤ (1 + m) ^ d := one_le_pow₀ (by linarith)
  have hlog : Real.log 2 ≤ Real.log 2 * (1 + m) ^ d := by nlinarith
  have hh := hb m hm hmL
  calc
    _ = Real.exp (Real.log 2 + C * (1 + m) ^ d - c * Real.exp (α * L)) := by
      rw [show Real.log 2 + C * (1 + m) ^ d - c * Real.exp (α * L) =
        Real.log 2 + (C * (1 + m) ^ d - c * Real.exp (α * L)) by ring,
        Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

/-- Both parts of the expanded square, including all fixed polynomial losses,
obey one common smallness bound. -/
theorem eventual_one_sided_squared_budget (C z α β γ c : ℝ) (d : ℕ)
    (hC : 0 ≤ C) (hz : 0 ≤ z) (hα : 0 < α) (hαβ : α < β)
    (hγβ : γ < β) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ m : ℝ, 0 ≤ m → m ≤ z * L →
      Real.exp (C * (1 + m) ^ d) *
        (Real.exp (-c * Real.exp (α * L)) +
          Real.exp (2 * Real.exp (γ * L) - Real.exp (β * L))) ≤
        Real.exp (-(c / 2) * Real.exp (α * L)) := by
  have hdiag := eventual_diagonal_atom_error C z α c d hC hz hα hc
  have hoff := eventual_separated_character_error 0 z α β γ c d (by norm_num) hz hα hαβ hγβ hc
  filter_upwards [hdiag, hoff] with L hdiag hoff m hm hmL
  have ho := hoff m hm hmL
  simp only [zero_mul, zero_add] at ho
  calc
    _ ≤ Real.exp (C * (1 + m) ^ d) *
        (Real.exp (-c * Real.exp (α * L)) + Real.exp (-c * Real.exp (α * L))) := by
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl ho) (Real.exp_pos _).le
    _ = 2 * Real.exp (C * (1 + m) ^ d - c * Real.exp (α * L)) := by
      rw [show C * (1 + m) ^ d - c * Real.exp (α * L) =
        C * (1 + m) ^ d + (-c * Real.exp (α * L)) by ring, Real.exp_add]
      ring
    _ ≤ _ := hdiag m hm hmL

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_DyadicCharacterBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit scale decay for the dyadic supported-history estimate -/

namespace Ostmann

open Filter

theorem dyadic_character_numeric_bound (N CP CQ M R B a b q K α β γ c L : ℝ)
    (hN : 0 ≤ N) (hCP : 0 ≤ CP) (hCQ : 0 ≤ CQ) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hb : Real.exp (c * Real.exp (α * L)) ≤ b)
    (ha : Real.exp (Real.exp (β * L)) ≤ a)
    (hq : 0 ≤ q) (hqupper : q ≤ Real.exp (Real.exp (γ * L)))
    (hcost₁ : 2 * N * CP * CQ * B ^ 2 ≤ K)
    (hcost₂ : 2 * N * CP * M * R * B ^ 2 ≤ K) :
    N * CP * (CQ * b⁻¹ * (2 * B ^ 2) + M * (R * (2 * a⁻¹ * B ^ 2)) * q ^ 2) ≤
      K * (Real.exp (-c * Real.exp (α * L)) +
        Real.exp (2 * Real.exp (γ * L) - Real.exp (β * L))) := by
  have hb' : b⁻¹ ≤ Real.exp (-c * Real.exp (α * L)) := by
    simpa only [← Real.exp_neg, neg_mul] using inv_anti₀ (Real.exp_pos _) hb
  have ha' : a⁻¹ * q ^ 2 ≤
      Real.exp (2 * Real.exp (γ * L) - Real.exp (β * L)) := by
    calc
      _ ≤ (Real.exp (Real.exp (β * L)))⁻¹ * (Real.exp (Real.exp (γ * L))) ^ 2 :=
        mul_le_mul (inv_anti₀ (Real.exp_pos _) ha)
          (pow_le_pow_left₀ hq hqupper 2) (sq_nonneg q) (by positivity)
      _ = _ := by rw [← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  have h₁ := mul_le_mul_of_nonneg_left hb' (by positivity : 0 ≤ 2 * N * CP * CQ * B ^ 2)
  have h₂ := mul_le_mul_of_nonneg_left ha' (by positivity : 0 ≤ 2 * N * CP * M * R * B ^ 2)
  calc
    _ = (2 * N * CP * CQ * B ^ 2) * b⁻¹ +
        (2 * N * CP * M * R * B ^ 2) * (a⁻¹ * q ^ 2) := by ring
    _ ≤ (2 * N * CP * CQ * B ^ 2) * Real.exp (-c * Real.exp (α * L)) +
        (2 * N * CP * M * R * B ^ 2) *
          Real.exp (2 * Real.exp (γ * L) - Real.exp (β * L)) := add_le_add h₁ h₂
    _ ≤ K * Real.exp (-c * Real.exp (α * L)) +
        K * Real.exp (2 * Real.exp (γ * L) - Real.exp (β * L)) :=
      add_le_add (mul_le_mul_of_nonneg_right hcost₁ (Real.exp_pos _).le)
        (mul_le_mul_of_nonneg_right hcost₂ (Real.exp_pos _).le)
    _ = _ := by ring

/-- All six concrete loss factors may be charged to one polynomial exponent.
The short-prime atom and the long/short gap remain outside that exponent. -/
theorem dyadic_character_cost (N CP CQ M R B P : ℝ)
    (_hN : 0 ≤ N) (hCP : 0 ≤ CP) (hCQ : 0 ≤ CQ) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hB : 0 ≤ B) (hP : 0 ≤ P)
    (bN : N ≤ Real.exp P) (bCP : CP ≤ Real.exp P) (bCQ : CQ ≤ Real.exp P)
    (bM : M ≤ Real.exp P) (bR : R ≤ Real.exp P) (bB : B ≤ Real.exp P) :
    2 * N * CP * CQ * B ^ 2 ≤ Real.exp (Real.log 2 + 6 * P) ∧
      2 * N * CP * M * R * B ^ 2 ≤ Real.exp (Real.log 2 + 6 * P) := by
  have he : 1 ≤ Real.exp P := Real.one_le_exp hP
  have hpow : (Real.exp P) ^ 5 ≤ (Real.exp P) ^ 6 := pow_le_pow_right₀ he (by omega)
  have hexact : 2 * (Real.exp P) ^ 6 = Real.exp (Real.log 2 + 6 * P) := by
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_nat_mul]
    norm_num
  constructor
  · calc
      _ ≤ 2 * Real.exp P * Real.exp P * Real.exp P * (Real.exp P) ^ 2 := by gcongr
      _ = 2 * (Real.exp P) ^ 5 := by ring
      _ ≤ 2 * (Real.exp P) ^ 6 := by gcongr
      _ = _ := hexact
  · calc
      _ ≤ 2 * Real.exp P * Real.exp P * Real.exp P * Real.exp P * (Real.exp P) ^ 2 := by gcongr
      _ = _ := by rw [← hexact]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HistoryFormulaFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fourier factors of the constructed history formulas, with derived budgets -/

namespace Ostmann

open scoped BigOperators SchwartzMap Classical

theorem formulaFourierBudget_nonneg {n : ℕ} (ψ : 𝓢(ℝ, ℂ)) (v lo hi : Fin n → ℝ)
    (hhi : ∀ j, lo j ≤ hi j) : 0 ≤ formulaFourierBudget ψ v lo hi := by
  have hψ : 0 ≤ SchwartzMap.seminorm ℝ 0 0 ψ :=
    (norm_nonneg (ψ 0)).trans (ψ.norm_le_seminorm ℝ 0)
  exact Finset.prod_nonneg fun j _ => add_nonneg (mul_nonneg (by norm_num) hψ)
    (mul_nonneg (add_nonneg hψ (mul_nonneg (schwartz_profile_lip_nonneg ψ) (abs_nonneg _)))
      (sub_nonneg.mpr (hhi j)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferPeriods
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common residue period derived from the actual branching frequencies -/

namespace Ostmann

open scoped Classical

theorem internalFrequencyList_length (n : ℕ) (t : FrequencyTree ℤ n) :
    (internalFrequencyList n t).length = 2 ^ n - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [internalFrequencyList, List.length_cons, List.length_append, ih, pow_succ]
    have := Nat.one_le_two_pow (n := n)
    omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferFullPeriod
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full small-frequency modulus, including every node's unit tests -/

namespace Ostmann

open scoped Classical

theorem internalFrequencyList_subset_all (n : ℕ) (t : FrequencyTree ℤ n) :
    ∀ s ∈ internalFrequencyList n t, s ∈ allFrequencyList n t := by
  induction n with
  | zero => simp [internalFrequencyList]
  | succ n ih =>
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact List.mem_cons_self ..
    · rcases List.mem_append.mp hs with hs | hs
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ih _ s hs))
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ih _ s hs))

theorem allFrequencyList_length (n : ℕ) (t : FrequencyTree ℤ n) :
    (allFrequencyList n t).length = 2 ^ (n + 1) - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [allFrequencyList, List.length_cons, List.length_append, ih, pow_succ]
    have := Nat.one_le_two_pow (n := n)
    omega

theorem wordTransferFullPeriod_le (n : ℕ) (t : FrequencyTree ℤ n) (B V : ℕ)
    (hV : ∀ s ∈ allFrequencyList n t, s.natAbs ≤ V) :
    wordTransferFullPeriod n t B ≤
      V ^ ((2 ^ n - 1) * (B ^ (n + 1) + 1) + (2 ^ (n + 1) - 1)) := by
  have hi := historyFrequencyPeriod_le (internalFrequencyList n t) V (B ^ (n + 1) + 1)
    (fun s hs => hV s (internalFrequencyList_subset_all n t s hs))
  have ha := historyFrequencyPeriod_le (allFrequencyList n t) V 1 hV
  simp only [historyFrequencyPeriod, pow_one, mul_one] at ha
  rw [internalFrequencyList_length] at hi
  rw [allFrequencyList_length] at ha
  exact (Nat.mul_le_mul hi ha).trans_eq (pow_add _ _ _).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferArrays
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Indexed arrays of the actual branching guards and Fourier leaves -/

namespace Ostmann.WordTransferTemplate

open scoped Classical

variable {σ : Type*} {n : ℕ}

theorem leafAt_mem (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (i : Fin (2 ^ n)) :
    template.leafAt t hn i ∈ template.weightedLeaves t hn .prime := List.getElem_mem _

end Ostmann.WordTransferTemplate

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The constructed coefficient for a branching word history -/

namespace Ostmann

open scoped BigOperators SchwartzMap Classical

namespace WordFourierParameters

variable {σ : Type*} {n : ℕ}

theorem budget_nonneg (p : WordFourierParameters n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (hn : NonzeroInternalFrequencies n t) :
    0 ≤ p.budget template t hn :=
  formulaFourierBudget_nonneg _ _ _ _ p.lower_upper

end WordFourierParameters
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_PrimePairDecay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numerical decay with all range, unit and large-prime support costs -/

namespace Ostmann

open scoped BigOperators
open Filter

/-- Point-mass and polynomial history losses remain negligible alongside the
already proved one-sided character error. -/
theorem eventual_prime_support_decay (K z α c : ℝ) (d : ℕ)
    (hK : 0 ≤ K) (hz : 0 ≤ z) (hα : 0 < α) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ (m δ loss atom value : ℝ),
      0 ≤ m → m ≤ z * L → 0 ≤ loss →
      loss ≤ Real.exp (K * (1 + m) ^ d) →
      atom ≤ Real.exp (-c * Real.exp (α * L)) →
      δ ≤ Real.exp (-(c / 4) * Real.exp (α * L)) →
      value ≤ δ + loss * atom → value ≤ Real.exp (-(c / 8) * Real.exp (α * L)) := by
  have hpoly := eventual_polynomial_log_budget K z α (c / 2) d hK hz hα (by positivity)
  have htwo := eventual_diagonal_atom_error 0 z α (c / 4) d (by norm_num) hz hα (by positivity)
  filter_upwards [hpoly, htwo] with L hpoly htwo m δ loss atom value hm hmL hloss hcost hatom hδ hv
  have he : loss * atom ≤ Real.exp (-(c / 2) * Real.exp (α * L)) := by
    calc
      _ ≤ loss * Real.exp (-c * Real.exp (α * L)) := mul_le_mul_of_nonneg_left hatom hloss
      _ ≤ Real.exp (K * (1 + m) ^ d) * Real.exp (-c * Real.exp (α * L)) :=
        mul_le_mul_of_nonneg_right hcost (Real.exp_nonneg _)
      _ = Real.exp (K * (1 + m) ^ d - c * Real.exp (α * L)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith [hpoly m hm hmL])
  have he' : Real.exp (-(c / 2) * Real.exp (α * L)) ≤
      Real.exp (-(c / 4) * Real.exp (α * L)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.exp_pos (α * L)]
  have hh := htwo m hm hmL
  simp only [zero_mul, zero_sub] at hh
  calc
    value ≤ δ + loss * atom := hv
    _ ≤ Real.exp (-(c / 4) * Real.exp (α * L)) + Real.exp (-(c / 4) * Real.exp (α * L)) :=
      add_le_add hδ (he.trans he')
    _ = 2 * Real.exp (-(c / 4) * Real.exp (α * L)) := by ring
    _ ≤ _ := by convert hh using 1 <;> congr 2 <;> ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordPeriodBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial exponential bound for the actual common frequency period -/

namespace Ostmann

theorem wordTransferFullPeriod_le_exp (n : ℕ) (t : FrequencyTree ℤ n) (B V : ℕ)
    (b C m : ℝ) (hC : 0 ≤ C) (hm : 0 ≤ m)
    (hB : (B : ℝ) ≤ b * (1 + m)) (hV : (V : ℝ) ≤ Real.exp (C * (1 + m)))
    (hf : ∀ s ∈ allFrequencyList n t, s.natAbs ≤ V) :
    (wordTransferFullPeriod n t B : ℝ) ≤
      Real.exp (C * wordPeriodExponent n b * (1 + m) ^ (n + 2)) := by
  let e := (2 ^ n - 1) * (B ^ (n + 1) + 1) + (2 ^ (n + 1) - 1)
  have hr : 0 ≤ 1 + m := by linarith
  have hr1 : 1 ≤ (1 + m) ^ (n + 1) := one_le_pow₀ (by linarith)
  have hbp : (B : ℝ) ^ (n + 1) ≤ b ^ (n + 1) * (1 + m) ^ (n + 1) := by
    simpa only [mul_pow] using pow_le_pow_left₀ (Nat.cast_nonneg B) hB (n + 1)
  have he : (e : ℝ) ≤ wordPeriodExponent n b * (1 + m) ^ (n + 1) := by
    dsimp [e, wordPeriodExponent]
    push_cast
    calc
      _ ≤ ((2 ^ n - 1 : ℕ) : ℝ) * ((b ^ (n + 1) + 1) * (1 + m) ^ (n + 1)) +
          ((2 ^ (n + 1) - 1 : ℕ) : ℝ) * (1 + m) ^ (n + 1) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (by nlinarith only [hbp, hr1]) (Nat.cast_nonneg _))
          (le_mul_of_one_le_right (Nat.cast_nonneg _) hr1)
      _ = _ := by ring
  have hnat : (wordTransferFullPeriod n t B : ℝ) ≤ (V : ℝ) ^ e := by
    exact_mod_cast wordTransferFullPeriod_le n t B V hf
  calc
    _ ≤ (V : ℝ) ^ e := hnat
    _ ≤ (Real.exp (C * (1 + m))) ^ e :=
      pow_le_pow_left₀ (Nat.cast_nonneg V) hV e
    _ = Real.exp ((e : ℝ) * (C * (1 + m))) := (Real.exp_nat_mul _ e).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left he (mul_nonneg hC hr)
      calc
        _ = (C * (1 + m)) * e := by ring
        _ ≤ (C * (1 + m)) * (wordPeriodExponent n b * (1 + m) ^ (n + 1)) := hh
        _ = _ := by rw [pow_succ]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RangedComplexityBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual range partition cost is polynomial at fixed depth -/

namespace Ostmann

/-- Include the extra root product interval in `D`; the same bound then
covers the normalized reciprocal-product comparison. -/
theorem ranged_word_complexity_le {V : Type*} {n : ℕ}
    (D D' : WordRangeDecoration V n) (B : ℕ) (b d m : ℝ)
    (hd : 0 ≤ d) (hm : 0 ≤ m)
    (hB : (B : ℝ) ≤ b * (1 + m))
    (hD : (D.count : ℝ) ≤ d * (1 + m))
    (hD' : (D'.count : ℝ) ≤ d * (1 + m)) :
    (((3 * 2 ^ n + 3 * (2 ^ n - 1) + 2 * (D.count + D'.count)) * B ^ (n + 1) : ℕ) : ℝ) ≤
      (((3 * 2 ^ n + 3 * (2 ^ n - 1) : ℕ) : ℝ) + 4 * d) *
        b ^ (n + 1) * (1 + m) ^ (n + 2) := by
  let c : ℝ := 3 * 2 ^ n + 3 * ((2 ^ n - 1 : ℕ) : ℝ)
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have h1 : 1 ≤ 1 + m := by linarith
  have hpoly : (B : ℝ) ^ (n + 1) ≤ b ^ (n + 1) * (1 + m) ^ (n + 1) := by
    simpa only [mul_pow] using pow_le_pow_left₀ (Nat.cast_nonneg B) hB (n + 1)
  have hcount : c + 2 * ((D.count : ℝ) + D'.count) ≤ (c + 4 * d) * (1 + m) := by
    nlinarith
  push_cast
  change (c + 2 * ((D.count : ℝ) + D'.count)) * (B : ℝ) ^ (n + 1) ≤ _
  calc
    _ ≤ ((c + 4 * d) * (1 + m)) * (b ^ (n + 1) * (1 + m) ^ (n + 1)) :=
      mul_le_mul hcount hpoly (by positivity) (by positivity)
    _ = _ := by rw [show n + 2 = n + 1 + 1 from rfl, pow_succ]; ring

theorem ranged_boolean_partition_le {V : Type*} {n : ℕ}
    (D D' : WordRangeDecoration V n) (B : ℕ) (K m : ℝ)
    (hcost : (((3 * 2 ^ n + 3 * (2 ^ n - 1) + 2 * (D.count + D'.count)) * B ^ (n + 1) : ℕ) : ℝ) ≤
      K * (1 + m) ^ (n + 2)) :
    ((3 ^ (2 * ((((3 * 2 ^ n + 3 * (2 ^ n - 1) + 2 * (D.count + D'.count)) * B ^ (n + 1))) +
      ((3 * 2 ^ n + 3 * (2 ^ n - 1) + 2 * (D.count + D'.count)) * B ^ (n + 1)))) : ℕ) : ℝ) ≤
      Real.exp ((4 * Real.log 3 * K) * (1 + m) ^ (n + 2)) := by
  let r := (3 * 2 ^ n + 3 * (2 ^ n - 1) + 2 * (D.count + D'.count)) * B ^ (n + 1)
  calc
    _ = Real.exp ((2 * (r + r) : ℕ) * Real.log 3) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
      norm_cast
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hcost (show 0 ≤ 4 * Real.log 3 by positivity)
      change (2 * (r + r) : ℕ) * Real.log 3 ≤ _
      change (r : ℝ) ≤ _ at hcost
      change 4 * Real.log 3 * (r : ℝ) ≤ _ at hh
      push_cast
      nlinarith only [hh]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordFourierBudgetBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit Fourier variation bounds from the actual frequency range -/

namespace Ostmann

open scoped BigOperators Classical SchwartzMap

theorem WordTransferTemplate.weightedLeaves_frequency_mem {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (ht : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ)
    (z : WeightedWordLeaf σ) (hz : z ∈ template.weightedLeaves t ht env) :
    z.frequency ∈ allFrequencyList n t := by
  induction template generalizing env z with
  | leaf word =>
    have he : z = ⟨true, t, HistoryFormula.listProduct (word.map env)⟩ :=
      List.mem_singleton.mp hz
    subst z
    exact List.mem_singleton_self _
  | @node n d l r ihl ihr =>
    rcases List.mem_append.mp hz with hz | hz
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ihl _ _ _ _ hz))
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
      exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihr _ _ _ a ha))

theorem WordFourierParameters.frequency_abs_le {σ : Type*} {n : ℕ}
    (p : WordFourierParameters n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (V : ℝ) (hV : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ V)
    (i : Fin (2 ^ n)) : |p.frequency template t ht i| ≤ V := by
  have hh := hV _ (template.weightedLeaves_frequency_mem t ht .prime _
    (template.leafAt_mem t ht i))
  dsimp only [frequency]
  split_ifs <;> simpa only [abs_neg] using hh

theorem WordFourierParameters.budget_le {σ : Type*} {n : ℕ}
    (p : WordFourierParameters n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (V H : ℝ) (hV : 0 ≤ V)
    (hf : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ V)
    (hr : ∀ i, p.upper i - p.lower i ≤ H) :
    p.budget template t ht ≤
      (2 * SchwartzMap.seminorm ℝ 0 0 p.profile +
        (SchwartzMap.seminorm ℝ 0 0 p.profile +
          SchwartzMap.seminorm ℝ 0 1 p.profile * V) * H) ^ (2 ^ n) := by
  unfold budget formulaFourierBudget
  have he : (∏ _i : Fin (2 ^ n),
      (2 * SchwartzMap.seminorm ℝ 0 0 p.profile +
        (SchwartzMap.seminorm ℝ 0 0 p.profile +
          SchwartzMap.seminorm ℝ 0 1 p.profile * V) * H)) =
      (2 * SchwartzMap.seminorm ℝ 0 0 p.profile +
        (SchwartzMap.seminorm ℝ 0 0 p.profile +
          SchwartzMap.seminorm ℝ 0 1 p.profile * V) * H) ^ (2 ^ n) := by simp
  rw [← he]
  apply Finset.prod_le_prod
  · intro i _
    exact add_nonneg (by positivity) (mul_nonneg (by positivity)
      (sub_nonneg.mpr (p.lower_upper i)))
  · intro i _
    apply add_le_add le_rfl
    apply mul_le_mul _ (hr i) (sub_nonneg.mpr (p.lower_upper i))
      (by positivity)
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (p.frequency_abs_le template t ht V hf i) (apply_nonneg _ _))

/-- All variation loss is exponential in the original linear frequency and
bin bounds, uniformly in the reconstructed integers and polynomial coefficients. -/
theorem WordFourierParameters.budget_le_exp {σ : Type*} {n : ℕ}
    (p : WordFourierParameters n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (S C m : ℝ) (hS : 1 ≤ S) (hC : 0 ≤ C) (hm : 0 ≤ m)
    (hS₀ : SchwartzMap.seminorm ℝ 0 0 p.profile ≤ S)
    (hS₁ : SchwartzMap.seminorm ℝ 0 1 p.profile ≤ S)
    (hf : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ Real.exp (C * (1 + m)))
    (hr : ∀ i, p.upper i - p.lower i ≤ Real.exp (C * (1 + m))) :
    p.budget template t ht ≤ Real.exp (((4 * S + 2 * C) * (2 ^ n : ℕ)) * (1 + m)) := by
  let T := Real.exp (C * (1 + m))
  have hT : 1 ≤ T := Real.one_le_exp_iff.mpr (by positivity)
  have hT0 : 0 ≤ T := (by positivity : 0 ≤ Real.exp (C * (1 + m)))
  have hS0 : 0 ≤ S := by linarith
  have hbase : 2 * SchwartzMap.seminorm ℝ 0 0 p.profile +
      (SchwartzMap.seminorm ℝ 0 0 p.profile +
        SchwartzMap.seminorm ℝ 0 1 p.profile * T) * T ≤ 4 * S * T ^ 2 := by
    have h₁ : 2 * SchwartzMap.seminorm ℝ 0 0 p.profile ≤ 2 * S := by linarith
    have h₂ : (SchwartzMap.seminorm ℝ 0 0 p.profile +
        SchwartzMap.seminorm ℝ 0 1 p.profile * T) * T ≤ (S + S * T) * T := by
      gcongr
    have h₃ : S ≤ S * T := le_mul_of_one_le_right hS0 hT
    have h₄ : S * T ≤ S * T ^ 2 := by nlinarith
    nlinarith
  have hexp : 4 * S * T ^ 2 ≤ Real.exp ((4 * S + 2 * C) * (1 + m)) := by
    have hs : 4 * S ≤ Real.exp (4 * S) := (by linarith [Real.add_one_le_exp (4 * S)])
    calc
      _ ≤ Real.exp (4 * S) * T ^ 2 := mul_le_mul_of_nonneg_right hs (sq_nonneg T)
      _ = Real.exp (4 * S + 2 * (C * (1 + m))) := by
        dsimp [T]
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        norm_num
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  calc
    _ ≤ (2 * SchwartzMap.seminorm ℝ 0 0 p.profile +
        (SchwartzMap.seminorm ℝ 0 0 p.profile +
          SchwartzMap.seminorm ℝ 0 1 p.profile * T) * T) ^ (2 ^ n) :=
      p.budget_le template t ht T T hT0 hf hr
    _ ≤ (Real.exp ((4 * S + 2 * C) * (1 + m))) ^ (2 ^ n) :=
      pow_le_pow_left₀ (by positivity) (hbase.trans hexp) _
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RangedPairNumericBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit numerical costs of the two actual ranged word histories -/

namespace Ostmann
open scoped BigOperators
open Filter

theorem rangedPairExponent_nonneg (n : ℕ) (b d C S H : ℝ)
    (hb : 0 ≤ b) (hd : 0 ≤ d) (hC : 0 ≤ C) (hS : 0 ≤ S) (hH : 0 ≤ H) :
    0 ≤ rangedPairExponent n b d C S H := by
  unfold rangedPairExponent wordPeriodExponent
  positivity

/-- The period, Boolean partition, Fourier variation and harmonic normalizers
all have a common explicit polynomial exponent. -/
theorem ranged_pair_numeric_costs {σ : Type*} {n : ℕ}
    (T T' : WordTransferTemplate σ n) (D D' : WordRangeDecoration σ n)
    (t t' : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (ht' : NonzeroInternalFrequencies n t')
    (B V E : ℕ) (f f' : WordFourierParameters n) (P Q : Finset ℕ)
    (b d C S H m : ℝ) (hb : 0 ≤ b) (hd : 0 ≤ d) (hC : 0 ≤ C)
    (hS : 1 ≤ S) (hH : 0 ≤ H) (hm : 0 ≤ m)
    (hB : (B : ℝ) ≤ b * (1 + m))
    (hD : (D.count : ℝ) ≤ d * (1 + m)) (hD' : (D'.count : ℝ) ≤ d * (1 + m))
    (hV : (V : ℝ) ≤ Real.exp (C * (1 + m)))
    (hf : ∀ s ∈ allFrequencyList n t, s.natAbs ≤ V)
    (hf' : ∀ s ∈ allFrequencyList n t', s.natAbs ≤ V)
    (hs₀ : SchwartzMap.seminorm ℝ 0 0 f.profile ≤ S)
    (hs₁ : SchwartzMap.seminorm ℝ 0 1 f.profile ≤ S)
    (hs₀' : SchwartzMap.seminorm ℝ 0 0 f'.profile ≤ S)
    (hs₁' : SchwartzMap.seminorm ℝ 0 1 f'.profile ≤ S)
    (hr : ∀ i, f.upper i - f.lower i ≤ Real.exp (C * (1 + m)))
    (hr' : ∀ i, f'.upper i - f'.lower i ≤ Real.exp (C * (1 + m)))
    (hE : ((Nat.log 2 E + 1 : ℕ) : ℝ) ≤ Real.exp (H * (1 + m)))
    (hP : (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (H * (1 + m)))
    (hQ : (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ ≤ Real.exp (H * (1 + m))) :
    let K := Real.log 2 + 6 * rangedPairExponent n b d C S H
    2 * ((Nat.log 2 E + 1 : ℕ) : ℝ) * (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ *
        (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * (f.budget T t ht * f'.budget T' t' ht') ^ 2 ≤
      Real.exp (K * (1 + m) ^ (n + 2)) ∧
    2 * ((Nat.log 2 E + 1 : ℕ) : ℝ) * (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ *
        (wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B : ℕ) *
        (3 ^ (2 * (((3 * 2 ^ n + 3 * (2 ^ n - 1) + 2 * (D.count + D'.count)) * B ^ (n + 1)) +
          ((3 * 2 ^ n + 3 * (2 ^ n - 1) + 2 * (D.count + D'.count)) * B ^ (n + 1)))) : ℕ) *
        (f.budget T t ht * f'.budget T' t' ht') ^ 2 ≤
      Real.exp (K * (1 + m) ^ (n + 2)) := by
  let W := wordPeriodExponent n b
  let R := (((3 * 2 ^ n + 3 * (2 ^ n - 1) : ℕ) : ℝ) + 4 * d) * b ^ (n + 1)
  let F := (4 * S + 2 * C) * (2 ^ n : ℕ)
  let K₀ := rangedPairExponent n b d C S H
  have hW : 0 ≤ W := by dsimp [W, wordPeriodExponent]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hK₀ : 0 ≤ K₀ := rangedPairExponent_nonneg n b d C S H hb hd hC (by linarith) hH
  have hpow : 1 + m ≤ (1 + m) ^ (n + 2) := by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ 1 + m)
      (show 1 ≤ n + 2 by omega)
  have hunit : 1 ≤ (1 + m) ^ (n + 2) := one_le_pow₀ (by linarith)
  have hKeq : K₀ = H + 2 * C * W + 4 * Real.log 3 * R + 2 * F := by
    dsimp [K₀, rangedPairExponent, W, R, F]
    ring
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hCW : 0 ≤ 2 * C * W := by positivity
  have hRR : 0 ≤ 4 * Real.log 3 * R := by positivity
  have hHK : H ≤ K₀ := by rw [hKeq]; linarith
  have hWK : 2 * C * W ≤ K₀ := by rw [hKeq]; linarith
  have hRK : 4 * Real.log 3 * R ≤ K₀ := by rw [hKeq]; linarith
  have hFK : 2 * F ≤ K₀ := by rw [hKeq]; linarith
  have hlift (a : ℝ) (ha : 0 ≤ a) (haK : a ≤ K₀) :
      a * (1 + m) ≤ K₀ * (1 + m) ^ (n + 2) :=
    (mul_le_mul_of_nonneg_left hpow ha).trans
      (mul_le_mul_of_nonneg_right haK (by positivity))
  have hfreq (s : ℤ) (hs : s.natAbs ≤ V) : |(s : ℝ)| ≤ Real.exp (C * (1 + m)) := by
    have hh : |(s : ℝ)| ≤ (V : ℝ) := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using (show (s.natAbs : ℝ) ≤ (V : ℝ) from by exact_mod_cast hs)
    exact hh.trans hV
  have hbudget := f.budget_le_exp T t ht S C m hS hC hm hs₀ hs₁
    (fun s hs => hfreq s (hf s hs)) hr
  have hbudget' := f'.budget_le_exp T' t' ht' S C m hS hC hm hs₀' hs₁'
    (fun s hs => hfreq s (hf' s hs)) hr'
  have hBpair : f.budget T t ht * f'.budget T' t' ht' ≤
      Real.exp (K₀ * (1 + m) ^ (n + 2)) := by
    calc
      _ ≤ Real.exp (F * (1 + m)) * Real.exp (F * (1 + m)) :=
        mul_le_mul hbudget hbudget' (f'.budget_nonneg _ _ _) (Real.exp_nonneg _)
      _ = Real.exp ((2 * F) * (1 + m)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (hlift (2 * F) (by positivity) hFK)
  have hperiod : (wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B : ℝ) ≤
      Real.exp (K₀ * (1 + m) ^ (n + 2)) := by
    calc
      _ ≤ Real.exp (C * W * (1 + m) ^ (n + 2)) *
          Real.exp (C * W * (1 + m) ^ (n + 2)) :=
        mul_le_mul (wordTransferFullPeriod_le_exp n t B V b C m hC hm hB hV hf)
          (wordTransferFullPeriod_le_exp n t' B V b C m hC hm hB hV hf')
          (by positivity) (Real.exp_nonneg _)
      _ = Real.exp ((2 * C * W) * (1 + m) ^ (n + 2)) := by
        rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hWK (by positivity))
  have hpartition := ranged_boolean_partition_le D D' B R m
    (ranged_word_complexity_le D D' B b d m hd hm hB hD hD')
  have hpartition' := hpartition.trans (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right hRK (by positivity : 0 ≤ (1 + m) ^ (n + 2))))
  have hcost := dyadic_character_cost ((Nat.log 2 E + 1 : ℕ) : ℝ)
    (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹
    (wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B : ℕ)
    (3 ^ (2 * (((3 * 2 ^ n + 3 * (2 ^ n - 1) + 2 * (D.count + D'.count)) * B ^ (n + 1)) +
      ((3 * 2 ^ n + 3 * (2 ^ n - 1) + 2 * (D.count + D'.count)) * B ^ (n + 1)))) : ℕ)
    (f.budget T t ht * f'.budget T' t' ht') (K₀ * (1 + m) ^ (n + 2))
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (mul_nonneg (f.budget_nonneg _ _ _) (f'.budget_nonneg _ _ _)) (by positivity)
    (hE.trans (Real.exp_le_exp.mpr (hlift H hH hHK)))
    (hP.trans (Real.exp_le_exp.mpr (hlift H hH hHK)))
    (hQ.trans (Real.exp_le_exp.mpr (hlift H hH hHK)))
    (by exact_mod_cast hperiod) hpartition' hBpair
  have hexp : Real.log 2 + 6 * (K₀ * (1 + m) ^ (n + 2)) ≤
      (Real.log 2 + 6 * K₀) * (1 + m) ^ (n + 2) := by
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith
  exact ⟨hcost.1.trans (Real.exp_le_exp.mpr hexp), hcost.2.trans (Real.exp_le_exp.mpr hexp)⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RangedPairUniformDecay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One-sided numerical decay uniform over the growing prime-coordinate space -/
namespace Ostmann
universe u
open Filter
open scoped BigOperators

theorem eventual_ranged_word_pair_decay_uniform {n : ℕ}
    (K z α β γ c : ℝ) (d : ℕ)
    (hK : 0 ≤ K) (hz : 0 ≤ z) (hα : 0 < α) (hαβ : α < β)
    (hγβ : γ < β) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ (σ : Type u),
      ∀ (template template' : WordTransferTemplate σ n)
      (D D' : WordRangeDecoration σ n) (t t' : FrequencyTree ℤ n)
      (ht : NonzeroInternalFrequencies n t) (ht' : NonzeroInternalFrequencies n t')
      (B A E : ℕ) (f f' : WordFourierParameters n) (P Q : Finset ℕ)
      (lower : ℝ) (Bq : ℕ) (m : ℝ),
      0 ≤ m → m ≤ z * L →
      Real.exp (c * Real.exp (α * L)) ≤ lower →
      Real.exp (Real.exp (β * L)) ≤ (A : ℝ) →
      (Bq : ℝ) ≤ Real.exp (Real.exp (γ * L)) →
      2 * ((Nat.log 2 E + 1 : ℕ) : ℝ) * (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ *
        (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ *
        (f.budget template t ht * f'.budget template' t' ht') ^ 2 ≤
          Real.exp (K * (1 + m) ^ d) →
      2 * ((Nat.log 2 E + 1 : ℕ) : ℝ) * (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ *
        (wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B : ℕ) *
        (3 ^ (2 * (((3 * 2 ^ n + 3 * (2 ^ n - 1) + 2 * (D.count + D'.count)) * B ^ (n + 1)) +
          ((3 * 2 ^ n + 3 * (2 ^ n - 1) + 2 * (D.count + D'.count)) * B ^ (n + 1)))) : ℕ) *
        (f.budget template t ht * f'.budget template' t' ht') ^ 2 ≤
          Real.exp (K * (1 + m) ^ d) →
      rangedWordTransferPairBound template template' D D' t t' ht ht' B f f'
        A E P Q lower Bq ≤ (Real.exp (-(c / 4) * Real.exp (α * L))) ^ 2 := by
  filter_upwards [eventual_one_sided_squared_budget K z α β γ c d hK hz hα hαβ hγβ hc]
    with L hL σ template template' D D' t t' ht ht' B A E f f' P Q lower Bq m
      hm hmL hlower hA hBq hcost₁ hcost₂
  have hh := dyadic_character_numeric_bound
    ((Nat.log 2 E + 1 : ℕ) : ℝ) (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹
    (wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B : ℕ)
    (3 ^ (2 * (((3 * 2 ^ n + 3 * (2 ^ n - 1) + 2 * (D.count + D'.count)) * B ^ (n + 1)) +
      ((3 * 2 ^ n + 3 * (2 ^ n - 1) + 2 * (D.count + D'.count)) * B ^ (n + 1)))) : ℕ)
    (f.budget template t ht * f'.budget template' t' ht') A lower Bq
    (Real.exp (K * (1 + m) ^ d)) α β γ c L
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hlower hA (Nat.cast_nonneg _) hBq hcost₁ hcost₂
  apply hh.trans
  apply (hL m hm hmL).trans_eq
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem eventual_ranged_pair_decay_from_data_uniform (n : ℕ)
    (b d C S H z α β γ c : ℝ)
    (hb : 0 ≤ b) (hd : 0 ≤ d) (hC : 0 ≤ C) (hS : 1 ≤ S) (hH : 0 ≤ H)
    (hz : 0 ≤ z) (hα : 0 < α) (hαβ : α < β) (hγβ : γ < β) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ (σ : Type u), ∀
      (T T' : WordTransferTemplate σ n) (D D' : WordRangeDecoration σ n)
      (t t' : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
      (ht' : NonzeroInternalFrequencies n t')
      (B V A E : ℕ) (f f' : WordFourierParameters n) (P Q : Finset ℕ)
      (lower : ℝ) (Bq : ℕ) (m : ℝ),
      0 ≤ m → m ≤ z * L →
      (B : ℝ) ≤ b * (1 + m) →
      (D.count : ℝ) ≤ d * (1 + m) → (D'.count : ℝ) ≤ d * (1 + m) →
      (V : ℝ) ≤ Real.exp (C * (1 + m)) →
      (∀ s ∈ allFrequencyList n t, s.natAbs ≤ V) →
      (∀ s ∈ allFrequencyList n t', s.natAbs ≤ V) →
      SchwartzMap.seminorm ℝ 0 0 f.profile ≤ S →
      SchwartzMap.seminorm ℝ 0 1 f.profile ≤ S →
      SchwartzMap.seminorm ℝ 0 0 f'.profile ≤ S →
      SchwartzMap.seminorm ℝ 0 1 f'.profile ≤ S →
      (∀ i, f.upper i - f.lower i ≤ Real.exp (C * (1 + m))) →
      (∀ i, f'.upper i - f'.lower i ≤ Real.exp (C * (1 + m))) →
      ((Nat.log 2 E + 1 : ℕ) : ℝ) ≤ Real.exp (H * (1 + m)) →
      (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (H * (1 + m)) →
      (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ ≤ Real.exp (H * (1 + m)) →
      Real.exp (c * Real.exp (α * L)) ≤ lower →
      Real.exp (Real.exp (β * L)) ≤ (A : ℝ) →
      (Bq : ℝ) ≤ Real.exp (Real.exp (γ * L)) →
      rangedWordTransferPairBound T T' D D' t t' ht ht' B f f'
        A E P Q lower Bq ≤ (Real.exp (-(c / 4) * Real.exp (α * L))) ^ 2 := by
  let K := Real.log 2 + 6 * rangedPairExponent n b d C S H
  have hK : 0 ≤ K := by
    have hh := rangedPairExponent_nonneg n b d C S H hb hd hC (by linarith) hH
    dsimp [K]
    positivity
  filter_upwards [eventual_ranged_word_pair_decay_uniform (n := n) K z α β γ c (n + 2)
    hK hz hα hαβ hγβ hc] with L hL
  intro σ T T' D D' t t' ht ht' B V A E f f' P Q lower Bq m
    hm hmL hB hD hD' hV hf hf' hs₀ hs₁ hs₀' hs₁' hr hr' hE hP hQ hlower hA hBq
  have hcost := ranged_pair_numeric_costs T T' D D' t t' ht ht' B V E f f' P Q
    b d C S H m hb hd hC hS hH hm hB hD hD' hV hf hf' hs₀ hs₁ hs₀' hs₁' hr hr'
    hE hP hQ
  exact hL σ T T' D D' t t' ht ht' B A E f f' P Q lower Bq m hm hmL hlower hA hBq
    hcost.1 hcost.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentGuardCost
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial counts control the original prime-guard loss -/
namespace Ostmann

theorem constituent_guard_cost_le_exp (n J U B : ℕ) (s S a b m : ℝ)
    (hs : 0 ≤ s) (hsS : s ≤ S) (ha : 0 ≤ a) (hm : 0 ≤ m)
    (hJ : (J : ℝ) ≤ a * (1 + m)) (hU : (U : ℝ) ≤ a * (1 + m) ^ 2)
    (hB : (B : ℝ) ≤ b * (1 + m)) :
    s ^ (2 ^ n) * s ^ (2 ^ n) * ((J : ℝ) * (B : ℝ) ^ (n + 1) + U) ≤
      Real.exp ((2 * (2 ^ n : ℕ) * S + a * (b ^ (n + 1) + 1)) * (1 + m) ^ (n + 2)) := by
  let t := 1 + m
  have ht : 1 ≤ t := by dsimp [t]; linarith
  have ht0 : 0 ≤ t := by linarith
  have hS : 0 ≤ S := hs.trans hsS
  have htp : 1 ≤ t ^ (n + 2) := one_le_pow₀ ht
  have hpow : (B : ℝ) ^ (n + 1) ≤ b ^ (n + 1) * t ^ (n + 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg B) hB _
  have hpoly : (J : ℝ) * (B : ℝ) ^ (n + 1) + U ≤
      a * (b ^ (n + 1) + 1) * t ^ (n + 2) := by
    have hmul := mul_le_mul hJ hpow (by positivity) (by positivity : 0 ≤ a * t)
    have hU' := hU.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ ht (show 2 ≤ n + 2 by omega)) ha)
    have hid : a * t * (b ^ (n + 1) * t ^ (n + 1)) =
        a * b ^ (n + 1) * t ^ (n + 2) := by rw [pow_succ t (n + 1)]; ring
    rw [hid] at hmul
    linarith
  have hse : s ≤ Real.exp S := hsS.trans (by linarith [Real.add_one_le_exp S])
  have hsp := pow_le_pow_left₀ hs hse (2 ^ n)
  rw [← Real.exp_nat_mul] at hsp
  have hss : s ^ (2 ^ n) * s ^ (2 ^ n) ≤
      Real.exp ((2 * (2 ^ n : ℕ) * S) * t ^ (n + 2)) := by
    calc
      _ ≤ Real.exp ((2 ^ n : ℕ) * S) * Real.exp ((2 ^ n : ℕ) * S) :=
        mul_le_mul hsp hsp (by positivity) (Real.exp_nonneg _)
      _ = Real.exp (2 * (2 ^ n : ℕ) * S) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (le_mul_of_one_le_right (by positivity) htp)
  have hpE : (J : ℝ) * (B : ℝ) ^ (n + 1) + U ≤
      Real.exp (a * (b ^ (n + 1) + 1) * t ^ (n + 2)) :=
    hpoly.trans (by linarith [Real.add_one_le_exp (a * (b ^ (n + 1) + 1) * t ^ (n + 2))])
  calc
    _ ≤ Real.exp ((2 * (2 ^ n : ℕ) * S) * t ^ (n + 2)) *
        Real.exp (a * (b ^ (n + 1) + 1) * t ^ (n + 2)) :=
      mul_le_mul hss hpE (by positivity) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [t]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HarmonicTuplePointBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counterpart point probabilities from the original prime-cell lower endpoints -/

namespace Ostmann
open scoped BigOperators Classical

theorem primeSubsetPrior_le_lower_endpoint (P Q : Finset ℕ) (lo : ℝ) (hlo : 0 < lo)
    (hcell : ∀ p ∈ Q, lo ≤ (p : ℝ)) (p : P) :
    primeSubsetPrior P Q p ≤ (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * lo⁻¹ := by
  unfold primeSubsetPrior
  split_ifs with hp
  · rw [div_eq_mul_inv, mul_comm]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa only [one_div] using one_div_le_one_div_of_le hlo (hcell p hp)
  · positivity

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HarmonicPriorAtomDecay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual harmonic prime priors have negligible point masses -/
namespace Ostmann
open Filter

/-- A lower prime cutoff dominates the harmonic normalization uniformly in
all selected cells, even after their permitted finite deletions. -/
theorem eventual_primeSubsetPrior_atom_decay (H z α c : ℝ)
    (hH : 0 ≤ H) (hz : 0 ≤ z) (hα : 0 < α) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ (m : ℝ) (P Q : Finset ℕ),
      0 ≤ m → m ≤ z * L →
      (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ ≤ Real.exp (H * (1 + m)) →
      (∀ q ∈ Q, Real.exp (c * Real.exp (α * L)) ≤ (q : ℝ)) →
      ∀ p : P, primeSubsetPrior P Q p ≤ Real.exp (-(c / 2) * Real.exp (α * L)) := by
  filter_upwards [eventual_polynomial_log_budget H z α (c / 2) 1 hH hz hα (by positivity)]
    with L hL m P Q hm hmL hmass hmin p
  have hh := primeSubsetPrior_le_lower_endpoint P Q (Real.exp (c * Real.exp (α * L)))
    (Real.exp_pos _) hmin p
  apply hh.trans
  calc
    _ ≤ Real.exp (H * (1 + m)) * (Real.exp (c * Real.exp (α * L)))⁻¹ :=
      mul_le_mul_of_nonneg_right hmass (by positivity)
    _ = Real.exp (H * (1 + m) - c * Real.exp (α * L)) := by
      rw [Real.exp_sub, div_eq_mul_inv]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have he := hL m hm hmL
      simp only [pow_one] at he
      linarith

/-- The extra unit and divisibility guards add a polynomially bounded
multiple of the same actual point mass. -/
theorem eventual_prime_prior_guard_decay (H z α c : ℝ)
    (hH : 0 ≤ H) (hz : 0 ≤ z) (hα : 0 < α) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ m atom ratio : ℝ,
      0 ≤ m → m ≤ z * L → 0 ≤ atom →
      atom ≤ Real.exp (-c * Real.exp (α * L)) →
      ratio ≤ Real.exp (H * (1 + m)) →
      atom + ratio * atom ≤ Real.exp (-(c / 2) * Real.exp (α * L)) := by
  filter_upwards [eventual_diagonal_atom_error H z α c 1 hH hz hα hc]
    with L hL m atom ratio hm hmL hatom hatomhi hratio
  have he : 1 ≤ Real.exp (H * (1 + m)) := Real.one_le_exp (by positivity)
  calc
    atom + ratio * atom ≤
        Real.exp (H * (1 + m)) * atom + Real.exp (H * (1 + m)) * atom :=
      add_le_add (le_mul_of_one_le_left hatom he) (mul_le_mul_of_nonneg_right hratio hatom)
    _ ≤ 2 * (Real.exp (H * (1 + m)) * Real.exp (-c * Real.exp (α * L))) := by
      have hh := mul_le_mul_of_nonneg_left hatomhi (Real.exp_nonneg (H * (1 + m)))
      linarith
    _ = 2 * Real.exp (H * (1 + m) - c * Real.exp (α * L)) := by
      rw [← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := by simpa only [pow_one] using hL m hm hmL

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentFinalPairDecay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original final pair decays from explicit prime and history bounds -/
namespace Ostmann
universe u
open Filter
open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

/-- The threshold is uniform over the growing constituent coordinate space.
The ranged-character error and the discarded prime guards are both derived
from the stated scalar size bounds. -/
theorem eventual_constituent_final_pair_decay_oai
    (n : ℕ) (a₀ b₀ d₀ C S H z α₀ β γ c : ℝ)
    (ha₀ : 0 ≤ a₀) (hb₀ : 0 ≤ b₀) (hd₀ : 0 ≤ d₀) (hC : 0 ≤ C) (hS : 1 ≤ S)
    (hH : 0 ≤ H) (hz : 0 ≤ z)
    (hα₀ : 0 < α₀) (hαβ : α₀ < β) (hγβ : γ < β) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (I : Type u) [Fintype I] (role : I → CopyScheduleRole) (size : I → ℕ)
      (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
      (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
      (_hκ : ∀ i p, ‖κ i p‖ ≤ 1)
      (e : Equiv.Perm (SurvivingConstituent role size n))
      (_hχ : ∀ i, χ (copyScheduleOrigin n (e i).val) = χ (copyScheduleOrigin n i.val))
      (childBound pivotBound : ℕ → ℕ)
      (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
      (ψ : 𝓢(ℝ, ℂ)) (_hreal : ∀ y, conj (ψ y) = ψ y)
      (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (_hu : ∀ j < n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b),
    let K := SurvivingConstituent role size n
    let ρ := (fun i : Σ a, Fin (size a) => role (Sigma.fst i))
    let W := primeWordEmbedding (scheduleConstituentWord role size n)
    let W' := primeWordEmbedding (fun v => List.map e (scheduleConstituentWord role size n v))
    let G := graphDifference (scheduledSurvivorGraph ρ pivot n)
      (transportGraph e (scheduledSurvivorGraph ρ pivot n))
    let Tpl := expandedRootTemplate role n W childBound pivotBound
    let Tpl' := expandedRootTemplate role n W' childBound pivotBound
    let D := expandedRootRanges role n W ranges
    let D' := expandedRootRanges role n W' ranges
    let U := expandedRootRanges role n W (totalAtomUnitRanges role)
    let U' := expandedRootRanges role n W' (totalAtomUnitRanges role)
    let Pr := expandedSchedulePrimes role n n [] (fun i => List.map Sum.inl (W i))
    let Pr' := expandedSchedulePrimes role n n [] (fun i => List.map Sum.inl (W' i))
    let FP := WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi
    ∀
    (a b : K) (_hab : a ≠ b)
    (t t' : FrequencyTree ℤ n) (_ht : NonzeroInternalFrequencies n t)
    (_ht' : NonzeroInternalFrequencies n t') (_hroot : frequencyRoot n t = frequencyRoot n t')
    (B : ℕ) (_hB : 1 ≤ B) (_hwords : (Tpl).WordsBounded B) (_hwords' : (Tpl').WordsBounded B)
    (_hD : (D).WordsBounded B) (_hD' : (D').WordsBounded B)
    (_hU : (U).WordsBounded B) (_hU' : (U').WordsBounded B) (_hreverse : G b a = 0)
    (P : Finset ℕ) (_hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
    (Q : K → Finset ℕ) (_hQP : ∀ i, Q i ⊆ P)
    (_hQmass : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹)
    (_hnonprincipal : ∀ q ∈ Q a, χ (copyScheduleOrigin n a.val) q ^ G a b ≠ 1)
    (A E : ℕ) (_hA : 0 < A)
    (_hMA : wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B ≤ A)
    (_hsmall : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t, 0 < s.natAbs ∧ s.natAbs < p)
    (_hsmall' : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t', 0 < s.natAbs ∧ s.natAbs < p)
    (_hlow : ∀ p ∈ Q b, 2 * A ≤ p) (_hhigh : ∀ p ∈ Q b, p ≤ E)
    (lower : ℝ) (_hlower : 0 < lower) (_hlowerQ : ∀ q ∈ Q a, lower ≤ (q : ℝ))
    (Bq : ℕ) (_hBq : ∀ q : Q a, (q : ℕ) ≤ Bq)
    (V R : ℝ) (_hV : 0 < V) (_hR : 3 ≤ R)
    (_hlowerP : ∀ p ∈ P, V ≤ Real.log (p : ℝ)) (_hupperP : ∀ p ∈ P, (p : ℝ) ≤ R)
    (_hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
    (_hfreq' : ∀ s ∈ allFrequencyList n t', |(s : ℝ)| ≤ R)
    (M : ℝ) (_hm : 0 ≤ M) (_hmL : M ≤ z * L)
    (Vfreq : ℕ) (_hBlinear : (B : ℝ) ≤ b₀ * (1 + M))
    (_hDcount : (((D).prependRoot (originalProductRange ([] : List (Option K)) n 1 0)).count : ℝ) ≤ d₀ * (1 + M))
    (_hD'count : ((D').count : ℝ) ≤ d₀ * (1 + M))
    (_hVfreq : (Vfreq : ℝ) ≤ Real.exp (C * (1 + M)))
    (_hfv : ∀ s ∈ allFrequencyList n t, s.natAbs ≤ Vfreq)
    (_hfv' : ∀ s ∈ allFrequencyList n t', s.natAbs ≤ Vfreq)
    (_hs₀ : SchwartzMap.seminorm ℝ 0 0 (FP).profile ≤ S)
    (_hs₁ : SchwartzMap.seminorm ℝ 0 1 (FP).profile ≤ S)
    (_hwidth : ∀ i, (FP).upper i - (FP).lower i ≤ Real.exp (C * (1 + M)))
    (_hE : ((Nat.log 2 E + 1 : ℕ) : ℝ) ≤ Real.exp (H * (1 + M)))
    (_hQinv : ∀ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹ ≤ Real.exp (H * (1 + M)))
    (_hshort : Real.exp (c * Real.exp (α₀ * L)) ≤ lower)
    (_hlong : Real.exp (Real.exp (β * L)) ≤ (A : ℝ))
    (_hBqscale : (Bq : ℝ) ≤ Real.exp (Real.exp (γ * L)))
    (_hmin : ∀ p ∈ P, Real.exp (c * Real.exp (α₀ * L)) ≤ (p : ℝ))
    (_hratio : Real.log R / V ≤ Real.exp (H * (1 + M)))
    (_hprimecount : (((Pr).count + (Pr').count : ℕ) : ℝ) ≤ a₀ * (1 + M))
    (_hcheckcount : ((constituentPrimePairChecks K ++ atomPairChecks W ++ atomPairChecks W').length : ℝ) ≤
      a₀ * (1 + M) ^ 2)
    (center : ∀ p : ℕ, ZMod p),
    ‖∑ q : K → P, ((∏ i, primeSubsetPrior P (Q i) (q i) : ℝ) : ℂ) *
      (constituentPrimeTerm role size χ κ pivot n P hprime childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo hi) center t q *
      conj (constituentPrimeTerm role size χ κ pivot n P hprime childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo hi) center t' (fun i => q (e i))))‖ ≤
      Real.exp (-(c / 32) * Real.exp (α₀ * L)) := by
  let K₀ := 2 * (2 ^ n : ℕ) * S + a₀ * (b₀ ^ (n + 1) + 1)
  have hK₀ : 0 ≤ K₀ := by dsimp [K₀]; positivity
  filter_upwards [eventual_ranged_pair_decay_from_data_uniform n b₀ d₀ C S H z α₀ β γ c
      hb₀ hd₀ hC hS hH hz hα₀ hαβ hγβ hc,
    eventual_primeSubsetPrior_atom_decay H z α₀ c hH hz hα₀ hc,
    eventual_prime_prior_guard_decay H z α₀ (c / 2) hH hz hα₀ (by positivity),
    eventual_prime_support_decay K₀ z α₀ (c / 4) (n + 2) hK₀ hz hα₀ (by positivity)]
    with L hranged hatoms hguards hsupport
  intro I _ role size χ κ pivot hκ e hχ childBound pivotBound ranges ψ hreal X lo hi hlo hhi hu
    K ρ W W' G Tpl Tpl' D D' U U' Pr Pr' FP
    a b hab t t' ht ht' hroot B hB hwords hwords' hD hD' hU hU' hreverse
    P hP hprime Q hQP hQmass hnonprincipal A E hA hMA hsmall hsmall' hlow hhigh
    lower hlower hlowerQ Bq hBq V R hV hR hlowerP hupperP hfreq hfreq'
    M hm hmL Vfreq hBlinear hDcount hD'count hVfreq hfv hfv' hs₀ hs₁ hwidth hE hQinv
    hshort hlong hBqscale hmin hratio hprimecount hcheckcount center
  let atom := Real.exp (-(c / 2) * Real.exp (α₀ * L))
  let δ := Real.exp (-(c / 4) * Real.exp (α₀ * L))
  let loss := ((SchwartzMap.seminorm ℝ 0 0 (FP).profile) ^ (2 ^ n) *
      (SchwartzMap.seminorm ℝ 0 0 (FP).profile) ^ (2 ^ n)) *
      ((((Pr).count + (Pr').count : ℕ) : ℝ) * (B ^ (n + 1) : ℕ) +
        (constituentPrimePairChecks K ++ atomPairChecks W ++ atomPairChecks W').length)
  have hcost : loss ≤ Real.exp (K₀ * (1 + M) ^ (n + 2)) := by
    simpa only [loss, K₀, Nat.cast_pow] using
      constituent_guard_cost_le_exp n ((Pr).count + (Pr').count)
        (constituentPrimePairChecks K ++ atomPairChecks W ++ atomPairChecks W').length B
        (SchwartzMap.seminorm ℝ 0 0 (FP).profile) S a₀ b₀ M
        (apply_nonneg _ _) hs₀ ha₀ hm hprimecount hcheckcount hBlinear
  have hmax (i : K) (p : P) : primeSubsetPrior P (Q i) p ≤ atom :=
    hatoms M P (Q i) hm hmL (hQinv i) (fun q hq => hmin q (hQP i hq)) p
  have hnum := hranged (ExpandedScheduledVariable (Option K) n) Tpl Tpl'
    ((D).prependRoot (originalProductRange ([] : List (Option K)) n 1 0)) D'
    t t' ht ht' B Vfreq A E FP FP (Q b) (Q a) lower Bq M
    hm hmL hBlinear hDcount hD'count hVfreq hfv hfv'
    hs₀ hs₁ hs₀ hs₁ hwidth hwidth hE (hQinv b) (hQinv a) hshort hlong hBqscale
  have hold := constituent_final_pair_bound role size n χ κ pivot hκ e hχ childBound pivotBound
    ranges ψ hreal X lo hi hlo hhi hu a b hab t t' ht ht' hroot B hB hwords hwords'
    hD hD' hU hU' hreverse P hP hprime Q hQP hQmass hnonprincipal A E hA hMA
    hsmall hsmall' hlow hhigh lower hlower hlowerQ Bq hBq atom V R (Real.exp_nonneg _)
    hV hR hmax hlowerP hupperP hfreq hfreq' δ (Real.exp_nonneg _) hnum center
  have hguard : atom + Real.log R / V * atom ≤ δ := by
    have hh := hguards M atom (Real.log R / V) hm hmL (Real.exp_nonneg _) le_rfl hratio
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [δ]
    congr 2
    ring
  have hloss : 0 ≤ loss := by dsimp [loss]; positivity
  have hδ : δ ≤ Real.exp (-(c / 4 / 4) * Real.exp (α₀ * L)) := by
    dsimp [δ]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.exp_pos (α₀ * L)]
  have hsum : δ + loss * (atom + Real.log R / V * atom) ≤ δ + loss * δ := by
    linarith only [mul_le_mul_of_nonneg_left hguard hloss]
  have hh := hsupport M δ loss δ _ hm hmL hloss hcost le_rfl hδ (hold.trans hsum)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end Ostmann

end OAI
end

theorem solution.{u} : type_of% @OAI.Ostmann.eventual_constituent_final_pair_decay_oai.{u} := @OAI.Ostmann.eventual_constituent_final_pair_decay_oai.{u}
