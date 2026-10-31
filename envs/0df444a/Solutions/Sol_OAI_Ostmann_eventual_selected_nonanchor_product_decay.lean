-- Prove2me | solution 1 for OAI.Ostmann.eventual_selected_nonanchor_product_decay
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:13:35.466183+00:00
-- url     : https://prove2.me/submissions/61043ea6-fafa-4999-b9ae-a42ac2f917db

import Mathlib
import Definitions.Def_OAIQ095D007
import Theorems.Thm_OAI_Ostmann_constituent_signed_supported_pair_bound

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferGraph
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The graph update and the regular-row invariant in one transfer -/

namespace Ostmann

theorem transferredGraph_diagonal {H Y : Type*}
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ) (hb : ∀ i, b i i = 0) :
    ∀ i, transferredGraph b i i = 0 := by
  intro i
  cases i with
  | inl q => simp [transferredGraph, hb]
  | inr y => rfl

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
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AnchorPairCode
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Anchor codes from the actual graph update -/

namespace Ostmann

theorem transferCopySign_sq (t : Bool) : transferCopySign t ^ 2 = 1 := by
  cases t <;> rfl

/-- Normalize by the new bulk parity. Its inverse equals itself, since it is
a sign. Both entries come directly from the copied graph, including the
cross-copy incoming-pivot coefficient. -/
theorem transferred_anchor_pair {H Y : Type*}
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ) (a i : H) (α ε : ℤ)
    (hε : ε = 1 ∨ ε = -1)
    (hincoming : b (some (.inl a)) (some (.inl i)) = ε)
    (hpivot : b (some (.inl a)) none = α) (t : Bool) :
    (transferCopySign t * ε * transferredGraph b (.inl (true, a)) (.inl (t, i)),
      transferCopySign t * ε * transferredGraph b (.inl (false, a)) (.inl (t, i))) =
      anchorSignPair α ε t := by
  rcases hε with rfl | rfl <;> cases t <;>
    simp [anchorSignPair, transferredGraph, transferCopySign, hincoming, hpivot]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AnchorOneSidedEdge
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A changed anchor code supplies a one-sided squared character -/

namespace Ostmann

theorem changed_anchor_code_one_sided (ε ε' c c' : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hε' : ε' = 1 ∨ ε' = -1)
    (hc : c = 1 ∨ c = -1) (hc' : c' = 1 ∨ c' = -1) (hne : c ≠ c') :
    ((ε * c - ε' * c' = 2 ∨ ε * c - ε' * c' = -2) ∧ ε - ε' = 0) ∨
      (ε * c - ε' * c' = 0 ∧ (ε - ε' = 2 ∨ ε - ε' = -2)) := by
  rcases hε with rfl | rfl <;> rcases hε' with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl <;> norm_num at *

theorem signed_square_nonprincipal {p : ℕ} (χ : DirichletCharacter ℂ p)
    (hχ : χ ^ 2 ≠ 1) (e : ℤ) (he : e = 2 ∨ e = -2) : χ ^ e ≠ 1 := by
  rcases he with rfl | rfl
  · simpa only [zpow_ofNat] using hχ
  · intro h
    have hinv := congrArg Inv.inv h
    simp only [zpow_neg, inv_inv, inv_one, zpow_ofNat] at hinv
    exact hχ hinv

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FinalReassignmentInteraction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting the actual small-anchor interaction between two reassignments -/

namespace Ostmann

theorem anchorCodeEntry_sign {n : ℕ} (α : Fin n → ℤ)
    (hα : ∀ j, α j = 1 ∨ α j = -1) (t : Fin n → Bool) (j : Fin n) (b : Bool) :
    anchorCodeEntry α t j b = 1 ∨ anchorCodeEntry α t j b = -1 := by
  have hp := copyPathParity_sign (finiteCopyPath t) j
  rcases hα j with ha | ha <;> rcases hp with hp | hp <;>
    cases hb : t j <;> cases b <;>
    simp [anchorCodeEntry, finiteAnchorCode, anchorSignPair, ha, hp, hb]

theorem distinct_anchor_code_entry {n : ℕ} (α : Fin n → ℤ) (t u : Fin n → Bool)
    (hne : finiteAnchorCode α t ≠ finiteAnchorCode α u) :
    ∃ j b, anchorCodeEntry α t j b ≠ anchorCodeEntry α u j b := by
  by_contra h
  push Not at h
  apply hne
  funext j
  apply Prod.ext
  · exact h j true
  · exact h j false

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AnchorGraphEvolution
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The anchor coefficients through their actual creation and later copies -/

namespace Ostmann

theorem copyPathParity_snoc_prefix {n : ℕ} (t : Fin n → Bool) (b : Bool)
    (j : ℕ) (hj : j ≤ n) :
    copyPathParity (finiteCopyPath (Fin.snoc t b)) j = copyPathParity (finiteCopyPath t) j := by
  apply copyPathParity_congr_prefix
  intro h hh
  have hhn : h < n := lt_of_lt_of_le hh hj
  simp only [finiteCopyPath, hhn, Nat.lt_succ_of_lt hhn, dite_true]
  exact @Fin.snoc_castSucc n (fun _ => Bool) b t ⟨h, hhn⟩

theorem anchorCodeEntry_snoc {n : ℕ} (α : Fin (n + 1) → ℤ)
    (t : Fin n → Bool) (u b : Bool) (j : Fin n) :
    anchorCodeEntry α (Fin.snoc t u) j.castSucc b =
      anchorCodeEntry (fun j => α j.castSucc) t j b := by
  have hp := copyPathParity_snoc_prefix t u j (Nat.le_of_lt j.isLt)
  simp only [anchorCodeEntry, finiteAnchorCode, Fin.val_castSucc, hp,
    @Fin.snoc_castSucc n (fun _ => Bool) u t j]

/-- This is exactly the outside-anchor row of `transferredGraph`: every
later copy multiplies its incoming coefficient by that copy's sign. -/
theorem anchorIncoming_snoc_old {n : ℕ} (α : Fin (n + 1) → ℤ)
    (t : Fin n → Bool) (u b : Bool) (j : Fin n) :
    anchorIncoming α (Fin.snoc t u) j.castSucc b =
      transferCopySign u * anchorIncoming (fun j => α j.castSucc) t j b := by
  unfold anchorIncoming
  rw [finalCopyParity_snoc, anchorCodeEntry_snoc, mul_assoc]

theorem anchorIncoming_snoc_new {n : ℕ} (α : Fin (n + 1) → ℤ)
    (t : Fin n → Bool) (u b : Bool) :
    anchorIncoming α (Fin.snoc t u) (Fin.last n) b =
      (transferCopySign u * finalCopyParity t) *
        (if b then (anchorSignPair (α (Fin.last n)) (finalCopyParity t) u).1
         else (anchorSignPair (α (Fin.last n)) (finalCopyParity t) u).2) := by
  have hp := copyPathParity_snoc_prefix t u n le_rfl
  unfold anchorIncoming
  rw [finalCopyParity_snoc]
  congr 1
  simp only [anchorCodeEntry, finiteAnchorCode, Fin.val_last, hp,
    @Fin.snoc_last n (fun _ => Bool) u t]
  rfl

/-- At its reserved step the unnormalized coefficient is precisely the
edge created by the graph transfer, for either clone of the fresh anchor. -/
theorem anchorIncoming_created_by_transfer {H Y : Type*}
    (graph : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ) (a i : H)
    {n : ℕ} (α : Fin (n + 1) → ℤ) (t : Fin n → Bool) (u b : Bool)
    (hincoming : graph (some (.inl a)) (some (.inl i)) = finalCopyParity t)
    (hpivot : graph (some (.inl a)) none = α (Fin.last n)) :
    anchorIncoming α (Fin.snoc t u) (Fin.last n) b =
      transferredGraph graph (.inl (b, a)) (.inl (u, i)) := by
  have hs := copyPathParity_sign (finiteCopyPath t) n
  change finalCopyParity t = 1 ∨ finalCopyParity t = -1 at hs
  have hpair := transferred_anchor_pair graph a i (α (Fin.last n)) (finalCopyParity t)
    hs hincoming hpivot u
  rw [anchorIncoming_snoc_new]
  have hsq : (transferCopySign u * finalCopyParity t) ^ 2 = 1 := by
    rw [mul_pow, transferCopySign_sq]
    rcases hs with hs | hs <;> simp only [hs] <;> norm_num
  cases b
  · have he := congrArg Prod.snd hpair
    dsimp only at he
    simp only [Bool.false_eq_true, ite_false, if_false]
    rw [← he]
    rw [← mul_assoc, ← pow_two, hsq, one_mul]
  · have he := congrArg Prod.fst hpair
    dsimp only at he
    simp only [ite_true, if_true]
    rw [← he]
    rw [← mul_assoc, ← pow_two, hsq, one_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GraphCopySchedule
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.copyScheduleVertexFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The graph on the literal copied and retained slot labels

The ambient label type includes both alternatives at a transfer. The actual
partition restricts the copied alternative to H and the retained alternative to
Y. Thus copying and retaining never identify two surviving slots. -/

namespace Ostmann

universe u

theorem copyScheduleGraph_diagonal {I : Type*} (g : I → I → ℤ) (pivot : ℕ → I)
    (hg : ∀ i, g i i = 0) (n : ℕ) : ∀ i, copyScheduleGraph g pivot n i i = 0 := by
  induction n with
  | zero => exact hg
  | succ n ih =>
    apply transferredGraph_diagonal
    intro i
    exact ih _

/-- Incoming edges from an unused reserved anchor simply accumulate the signs
of the copied word. The pivot sequence does not enter this identity. -/
theorem copyScheduleGraph_fresh_to_path {I : Type*}
    (g : I → I → ℤ) (pivot : ℕ → I) (n : ℕ) (a i : I) (t : Fin n → Bool) :
    copyScheduleGraph g pivot n (copyScheduleOutside n a) (copySchedulePath n t i) =
      finalCopyParity t * g a i := by
  induction n with
  | zero => simp [copyScheduleGraph, copyScheduleOutside, copySchedulePath, finalCopyParity, copyPathParity]
  | succ n ih =>
    change transferCopySign (t (Fin.last n)) *
      copyScheduleGraph g pivot n (copyScheduleOutside n a)
        (copySchedulePath n (fun j => t j.castSucc) i) = _
    rw [ih]
    have ht : Fin.snoc (fun j => t j.castSucc) (t (Fin.last n)) = t := by
      ext j
      refine Fin.lastCases ?_ (fun k => ?_) j <;> simp
    rw [← ht, finalCopyParity_snoc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, mul_assoc]

theorem copyScheduleGraph_fresh_to_positive {I : Type*}
    (g : I → I → ℤ) (pivot : ℕ → I) (n : ℕ) (a i : I) :
    copyScheduleGraph g pivot n (copyScheduleOutside n a) (copySchedulePositive n i) = g a i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change transferCopySign true *
      copyScheduleGraph g pivot n (copyScheduleOutside n a) (copySchedulePositive n i) = _
    simpa [transferCopySign] using ih

/-- A regular original word has the same signed edge to every future active
pivot. The hypothesis refers only to the initial graph's off-diagonal edges. -/
theorem copyScheduleGraph_path_to_positive {I : Type*}
    (g : I → I → ℤ) (pivot : ℕ → I) (n : ℕ) (i a : I)
    (hp : ∀ k < n, g i (pivot k) = 1) (ha : g i a = 1) (t : Fin n → Bool) :
    copyScheduleGraph g pivot n (copySchedulePath n t i) (copySchedulePositive n a) =
      finalCopyParity t := by
  induction n generalizing a with
  | zero => simpa [copyScheduleGraph, copySchedulePath, copySchedulePositive, finalCopyParity, copyPathParity] using ha
  | succ n ih =>
    change (if t (Fin.last n) = true then
      transferCopySign (t (Fin.last n)) * copyScheduleGraph g pivot n
        (copySchedulePath n (fun j => t j.castSucc) i) (copySchedulePositive n a)
      else transferCopySign (t (Fin.last n)) * copyScheduleGraph g pivot n
        (copySchedulePath n (fun j => t j.castSucc) i) (copySchedulePositive n (pivot n))) = _
    have hprev : ∀ k < n, g i (pivot k) = 1 := fun k hk => hp k (by omega)
    rw [ih a hprev ha, ih (pivot n) hprev (hp n (by omega))]
    split_ifs <;>
      have ht : Fin.snoc (fun j => t j.castSucc) (t (Fin.last n)) = t := by
        ext j
        refine Fin.lastCases ?_ (fun k => ?_) j <;> simp
    all_goals rw [← ht, finalCopyParity_snoc]; simp

/-- The same regular row holds against every anchor not yet used. -/
theorem copyScheduleGraph_path_to_fresh {I : Type*}
    (g : I → I → ℤ) (pivot : ℕ → I) (n : ℕ) (i a : I)
    (ha : g i a = 1) (t : Fin n → Bool) :
    copyScheduleGraph g pivot n (copySchedulePath n t i) (copyScheduleOutside n a) =
      finalCopyParity t := by
  induction n with
  | zero => simpa [copyScheduleGraph, copySchedulePath, copyScheduleOutside, finalCopyParity, copyPathParity] using ha
  | succ n ih =>
    change transferCopySign (t (Fin.last n)) * copyScheduleGraph g pivot n
      (copySchedulePath n (fun j => t j.castSucc) i) (copyScheduleOutside n a) = _
    rw [ih]
    have ht : Fin.snoc (fun j => t j.castSucc) (t (Fin.last n)) = t := by
      ext j
      refine Fin.lastCases ?_ (fun k => ?_) j <;> simp
    rw [← ht, finalCopyParity_snoc]
    simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferredPivotSubstitution
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Eliminating the extended integer by its exact signed quotient -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem reconstructedPivot_of_eq (N s : ℤ) (hs : s ≠ 0) (M : ℕ)
    (h : N = s * M) : reconstructedPivot N s = M := by
  rw [reconstructedPivot, Int.ediv_eq_of_eq_mul_right hs h, Int.toNat_natCast]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RecursiveTransferWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The recursive weight with its actual reconstructed integer pivots -/

namespace Ostmann

open scoped BigOperators Classical

theorem ValidTransferNode.historyPivot_eq {State : Type*} {sys : TransferHistorySystem State}
    {σ : State} {s v w : ℤ} {P : ℕ} (h : ValidTransferNode sys σ s v w P) :
    historyPivot sys σ s v w = P :=
  reconstructedPivot_of_eq _ _ h.root_ne_zero P h.relation

/-- No witness choices enter the recursive weight: the integer equation
forces the pivot at every valid node. -/
theorem recursiveTransferWeight_node {State : Type*} (sys : TransferHistorySystem State)
    (leaf : State → ℤ → ℂ) (cutoff : State → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ (n + 1)) (P : ℕ)
    (hP : ValidTransferNode sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P) :
    recursiveTransferWeight sys leaf cutoff (n + 1) σ t =
      (cutoff σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) : ℂ) *
        recursiveTransferWeight sys leaf cutoff n (sys.leftState σ P) t.2.1 *
        star (recursiveTransferWeight sys leaf cutoff n (sys.rightState σ P) t.2.2) := by
  simp only [recursiveTransferWeight, hP.historyPivot_eq, hP, ite_true, if_true]

theorem recursiveTransferWeight_nonzero_valid {State : Type*} (sys : TransferHistorySystem State)
    (leaf : State → ℤ → ℂ) (cutoff : State → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n)
    (ht : recursiveTransferWeight sys leaf cutoff n σ t ≠ 0) :
    ValidTransferHistory sys n σ t := by
  induction n generalizing σ with
  | zero => trivial
  | succ n ih =>
    let P := historyPivot sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
    by_cases hP : ValidTransferNode sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P
    · rw [recursiveTransferWeight_node sys leaf cutoff n σ t P hP] at ht
      have hl : recursiveTransferWeight sys leaf cutoff n (sys.leftState σ P) t.2.1 ≠ 0 := by
        intro hz
        simp only [hz, mul_zero, zero_mul, ne_eq, not_true_eq_false] at ht
      have hr : recursiveTransferWeight sys leaf cutoff n (sys.rightState σ P) t.2.2 ≠ 0 := by
        intro hz
        simp only [hz, star_zero, mul_zero, ne_eq, not_true_eq_false] at ht
      exact ⟨P, hP, ih _ _ hl, ih _ _ hr⟩
    · exact False.elim (ht (by simp only [recursiveTransferWeight, P, hP, ite_false, if_false]))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferTemplate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete transfer system of word products and reconstructed pivots -/

namespace Ostmann

open scoped Classical

universe u

theorem ValidTransferHistory.nonzero_internal {State : Type*} (sys : TransferHistorySystem State)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) (ht : ValidTransferHistory sys n σ t) :
    NonzeroInternalFrequencies n t := by
  induction n generalizing σ with
  | zero => trivial
  | succ n ih =>
    obtain ⟨P, hp, hl, hr⟩ := ht
    exact ⟨hp.root_ne_zero, ih _ _ hl, ih _ _ hr⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledTemplateBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Word-size bounds for the constructed copied-atom template -/

namespace Ostmann

open scoped Classical

theorem copyScheduleVertex_card {I : Type*} [Fintype I] (n : ℕ) :
    Fintype.card (CopyScheduleVertex I n) = 3 ^ n * Fintype.card I := by
  induction n with
  | zero =>
    simp only [pow_zero, one_mul]
    exact Fintype.card_congr (Equiv.refl I)
  | succ n ih =>
    change Fintype.card ((Bool × CopyScheduleVertex I n) ⊕ CopyScheduleVertex I n) = _
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, ih, pow_succ]
    ring

theorem copyScheduleAtoms_zero_card {I : Type*} [Fintype I] (role : I → CopyScheduleRole) :
    Fintype.card (CopyScheduleAtoms role 0) = Fintype.card I := by
  let e : CopyScheduleAtoms role 0 ≃ I :=
    ⟨Subtype.val, fun i => ⟨i, True.intro⟩, (by intro i; rfl), (by intro i; rfl)⟩
  exact Fintype.card_congr e

theorem copyScheduleH_card_le {I : Type*} [Fintype I] (role : I → CopyScheduleRole) (n : ℕ) :
    Fintype.card (CopyScheduleH role n) ≤ 3 ^ n * Fintype.card I := by
  rw [← copyScheduleVertex_card n]
  exact Fintype.card_subtype_le _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedScheduledTemplate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The atom schedule expanded into its actual prime constituents -/

namespace Ostmann

open scoped BigOperators Classical

theorem list_flatMap_length_bound {α β : Type*} (l : List α) (f : α → List β) (M : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ M) : (l.flatMap f).length ≤ l.length * M := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have ha := h a (by simp)
    have hl := ih (fun b hb => h b (by simp [hb]))
    nlinarith

theorem reverseCopyLabelMap_list_length {I σ : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (pivot : σ) (current : CopyScheduleAtoms role (n + 1) → List σ)
    (M : ℕ) (hM : 1 ≤ M) (hc : ∀ i, (current i).length ≤ M) :
    ∀ i, (reverseCopyLabelMap role n b [pivot] current i).length ≤ M := by
  intro i
  unfold reverseCopyLabelMap
  split_ifs
  · exact hc _
  · exact hM
  · exact hc _

theorem expandedHWord_length {I σ : Type*} [Fintype I] (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (current : CopyScheduleAtoms role (n + 1) → List σ)
    (M : ℕ) (hc : ∀ i, (current i).length ≤ M) :
    (expandedHWord role n b current).length ≤ Fintype.card (CopyScheduleH role n) * M := by
  simpa only [expandedHWord, Finset.length_toList, Finset.card_univ] using
    list_flatMap_length_bound (Finset.univ.toList : List (CopyScheduleH role n))
      (fun i => current ⟨.inl (b, i.val), i.property⟩) M (fun _ _ => hc _)

theorem expandedScheduledTemplate_words_bounded {I σ : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (address : ℕ → List Bool → σ) (childBound pivotBound : ℕ → ℕ)
    (n M B : ℕ) (hM : 1 ≤ M) (hbase : Fintype.card (CopyScheduleAtoms role 0) * M + 1 ≤ B)
    (hH : ∀ j < n, 2 * Fintype.card (CopyScheduleH role j) * M + 4 ≤ B)
    (path : List Bool) (current : CopyScheduleAtoms role n → List σ)
    (hc : ∀ i, (current i).length ≤ M) :
    (expandedScheduledTemplate role address childBound pivotBound n path current).WordsBounded B := by
  induction n generalizing path with
  | zero =>
    change (List.flatMap current (Finset.univ.toList : List (CopyScheduleAtoms role 0))).length + 1 ≤ B
    have hh := list_flatMap_length_bound (Finset.univ.toList : List (CopyScheduleAtoms role 0)) current M
      (fun i _ => hc i)
    simp only [Finset.length_toList, Finset.card_univ] at hh
    omega
  | succ n ih =>
    change _ ∧ _ ∧ _
    refine ⟨?_, ih (fun j hj => hH j (by omega)) _ _
      (reverseCopyLabelMap_list_length role n true _ current M hM hc),
      ih (fun j hj => hH j (by omega)) _ _
      (reverseCopyLabelMap_list_length role n false _ current M hM hc)⟩
    have hL := expandedHWord_length role n true current M hc
    have hR := expandedHWord_length role n false current M hc
    have hh := hH n (by omega)
    dsimp only
    nlinarith

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordRangeBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete complexity of all replayed intermediate range tests -/

namespace Ostmann

open scoped Classical

theorem WordRangeDecoration.count_le {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (K : ℕ) (hD : D.CountBounded K) :
    D.count ≤ K * (2 ^ (n + 1) - 1) := by
  induction D with
  | leaf ranges => simpa only [count, CountBounded, Nat.zero_add, pow_one, Nat.reduceSub, Nat.mul_one] using hD
  | @node n ranges L R ihL ihR =>
    have hL := ihL hD.2.1
    have hR := ihR hD.2.2
    have hp := Nat.one_le_two_pow (n := n + 1)
    change ranges.length + L.count + R.count ≤ K * (2 ^ (n + 1 + 1) - 1)
    rw [pow_succ]
    have he : 2 ^ (n + 1) * 2 - 1 = (2 ^ (n + 1) - 1) * 2 + 1 := by omega
    rw [he]
    nlinarith only [hD.1, hL, hR]

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedScheduleCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fresh finite pivot coordinates for expanded prime-word templates -/

namespace Ostmann

open scoped Classical

/-- The prime-expanded template has a concrete polynomial word bound. -/
theorem expandedRootTemplate_size {I α : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (depth : ℕ) (words : CopyScheduleAtoms role depth → List α)
    (childBound pivotBound : ℕ → ℕ) (M : ℕ) (hM : 1 ≤ M)
    (hwords : ∀ i, (words i).length ≤ M) :
    (expandedRootTemplate role depth words childBound pivotBound).WordsBounded
      (2 * 3 ^ depth * Fintype.card I * M + 4) := by
  apply expandedScheduledTemplate_words_bounded role _ _ _ depth M _ hM
  · rw [copyScheduleAtoms_zero_card]
    have hp : 1 ≤ 3 ^ depth := Nat.one_le_pow _ _ (by omega)
    have hm := Nat.mul_le_mul_right (Fintype.card I * M) hp
    nlinarith only [hm]
  · intro j hj
    have hc := copyScheduleH_card_le role j
    have hp : 3 ^ j ≤ 3 ^ depth := Nat.pow_le_pow_right (by omega) (by omega)
    have hmul := Nat.mul_le_mul_right (Fintype.card I) hp
    have hmulM := Nat.mul_le_mul_right M (hc.trans hmul)
    nlinarith
  · intro i
    simpa only [List.length_map] using hwords i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordPrimeBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Derived size, integrality and denominator bounds for the prime checks -/

namespace Ostmann

open scoped Classical

theorem WordPrimeDecoration.count_le {V : Type*} {n : ℕ}
    (D : WordPrimeDecoration V n) (K : ℕ) (hD : D.CountBounded K) :
    D.count ≤ K * (2 ^ n - 1) := by
  induction D with
  | leaf => simp only [count, pow_zero, Nat.sub_self, Nat.mul_zero, le_refl]
  | @node n coordinates L R ihL ihR =>
    have hL := ihL hD.2.1
    have hR := ihR hD.2.2
    have hp := Nat.one_le_two_pow (n := n)
    change coordinates.length + L.count + R.count ≤ K * (2 ^ (n + 1) - 1)
    rw [pow_succ]
    have he : 2 ^ n * 2 - 1 = (2 ^ n - 1) * 2 + 1 := by omega
    rw [he]
    nlinarith only [hD.1, hL, hR]

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedScheduleRanges
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original atom-product and word-bin ranges on the expanded schedule -/

namespace Ostmann

open scoped Classical

theorem ScheduleAtomRange.toWord_length {I σ : Type*} {role : I → CopyScheduleRole} {n : ℕ}
    (r : ScheduleAtomRange role n) (current : CopyScheduleAtoms role n → List σ)
    (A M : ℕ) (hr : r.atoms.length ≤ A) (hc : ∀ i, (current i).length ≤ M) :
    (r.toWord current).word.length ≤ A * M := by
  exact (list_flatMap_length_bound r.atoms current M (fun i _ => hc i)).trans
    (Nat.mul_le_mul_right M hr)

/-- The range count is controlled at every stage, including the terminal bins. -/
theorem expandedScheduleRanges_count_bounded {I σ : Type*} (role : I → CopyScheduleRole)
    (address : ℕ → List Bool → σ) (ranges : (n : ℕ) → List (ScheduleAtomRange role n))
    (n K : ℕ) (hK : ∀ j ≤ n, (ranges j).length ≤ K)
    (path : List Bool) (current : CopyScheduleAtoms role n → List σ) :
    (expandedScheduleRanges role address ranges n path current).CountBounded K := by
  induction n generalizing path with
  | zero => simpa only [expandedScheduleRanges, WordRangeDecoration.CountBounded, List.length_map]
      using hK 0 le_rfl
  | succ n ih =>
    exact ⟨by simpa only [List.length_map] using hK (n + 1) le_rfl,
      ih (fun j hj => hK j (by omega)) _ _, ih (fun j hj => hK j (by omega)) _ _⟩

/-- Products in all original range tests have the same finite word bound
as their actual constituent expansion. -/
theorem expandedScheduleRanges_words_bounded {I σ : Type*} (role : I → CopyScheduleRole)
    (address : ℕ → List Bool → σ) (ranges : (n : ℕ) → List (ScheduleAtomRange role n))
    (n A M : ℕ) (hM : 1 ≤ M)
    (hA : ∀ j ≤ n, ∀ r ∈ ranges j, r.atoms.length ≤ A)
    (path : List Bool) (current : CopyScheduleAtoms role n → List σ)
    (hc : ∀ i, (current i).length ≤ M) :
    (expandedScheduleRanges role address ranges n path current).WordsBounded (A * M + 1) := by
  induction n generalizing path with
  | zero =>
    intro r hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
    exact Nat.add_le_add_right (q.toWord_length current A M (hA 0 le_rfl q hq) hc) 1
  | succ n ih =>
    refine ⟨?_, ih (fun j hj => hA j (by omega)) _ _
      (reverseCopyLabelMap_list_length role n true _ current M hM hc),
      ih (fun j hj => hA j (by omega)) _ _
      (reverseCopyLabelMap_list_length role n false _ current M hM hc)⟩
    intro r hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
    exact Nat.add_le_add_right (q.toWord_length current A M (hA (n + 1) le_rfl q hq) hc) 1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_TotalAtomUnits
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual unit condition on every current atom at every frequency -/

namespace Ostmann

open scoped BigOperators Classical

/-- A unit product is exactly the original assertion that every current
atom is a unit. The dummy interval endpoints play no part in this test. -/
theorem totalAtomUnitRanges_iff {I : Type*} [Fintype I] (role : I → CopyScheduleRole)
    (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (s : ℤ) :
    (∀ r ∈ totalAtomUnitRanges role n, ((r.atoms.map x).prod).Coprime s.natAbs) ↔
      ∀ i, (x i).Coprime s.natAbs := by
  simp only [totalAtomUnitRanges, List.mem_singleton, forall_eq]
  rw [Finset.prod_map_toList]
  exact Nat.coprime_fintype_prod_left_iff

theorem WordRangeDecoration.wordsBounded_mono {σ : Type*} {n B C : ℕ}
    (D : WordRangeDecoration σ n) (hD : D.WordsBounded B) (hBC : B ≤ C) : D.WordsBounded C := by
  induction D with
  | leaf ranges => exact fun r hr => (hD r hr).trans hBC
  | node ranges L R ihL ihR => exact ⟨fun r hr => (hD.1 r hr).trans hBC, ihL hD.2.1, ihR hD.2.2⟩

theorem copyScheduleAtoms_card_le {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) :
    Fintype.card (CopyScheduleAtoms role n) ≤ 3 ^ n * Fintype.card I := by
  rw [← copyScheduleVertex_card n]
  exact Fintype.card_subtype_le _

/-- Its product words fit the same concrete bound as the Fourier template. -/
theorem totalAtomUnits_words_bounded {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List V)
    (M : ℕ) (hM : 1 ≤ M) (hwords : ∀ i, (words i).length ≤ M) :
    (expandedRootRanges role n words (totalAtomUnitRanges role)).WordsBounded
      (2 * 3 ^ n * Fintype.card I * M + 4) := by
  have hA : ∀ j ≤ n, ∀ r ∈ totalAtomUnitRanges role j,
      r.atoms.length ≤ 3 ^ n * Fintype.card I := by
    intro j hj r hr
    have he : r = ⟨Finset.univ.toList, 0, 0⟩ := List.mem_singleton.mp hr
    subst r
    simp only [Finset.length_toList, Finset.card_univ]
    exact (copyScheduleAtoms_card_le role j).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hj))
  have hh := expandedScheduleRanges_words_bounded role (expandedPivotAddress V n)
    (totalAtomUnitRanges role) n (3 ^ n * Fintype.card I) M hM hA []
    (fun i => (words i).map Sum.inl) (fun i => by simpa only [List.length_map] using hwords i)
  exact WordRangeDecoration.wordsBounded_mono _ hh (by nlinarith only [Nat.zero_le (3 ^ n * Fintype.card I * M)])

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_AtomTopSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The top atom support as explicit original-prime tests -/

namespace Ostmann

open scoped BigOperators Classical

theorem atomPairChecks_length {I V : Type*} [Fintype I]
    (words : I → List V) (M : ℕ) (hw : ∀ i, (words i).length ≤ M) :
    (atomPairChecks words).length ≤ (Fintype.card I * M) ^ 2 := by
  have hp (i j : I) :
      (if i = j then [] else (words i).flatMap fun v =>
        (words j).map (TopPrimeCondition.distinct v)).length ≤ M * M := by
    split_ifs
    · simp only [List.length_nil]; omega
    · apply (list_flatMap_length_bound (words i) _ M
        (fun _ _ => by simpa only [List.length_map] using hw j)).trans
      exact Nat.mul_le_mul_right M (hw i)
  have hi (i : I) :
      (Finset.univ.toList.flatMap fun j => if i = j then [] else
        (words i).flatMap fun v => (words j).map (TopPrimeCondition.distinct v)).length ≤
          Fintype.card I * (M * M) := by
    simpa only [Finset.length_toList, Finset.card_univ] using
      list_flatMap_length_bound Finset.univ.toList _ (M * M) (fun j _ => hp i j)
  calc
    _ ≤ Fintype.card I * (Fintype.card I * (M * M)) := by
      simpa only [atomPairChecks, Finset.length_toList, Finset.card_univ] using
        list_flatMap_length_bound Finset.univ.toList _ (Fintype.card I * (M * M)) (fun i _ => hi i)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledAnchorGraph
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.copyScheduleVertexFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Anchor codes derived from the full copied-slot schedule -/

namespace Ostmann

open scoped Classical

/-- Every outgoing word-to-anchor edge is its final copy parity. -/
theorem copyScheduleGraph_path_to_anchor {I : Type*}
    (g : I → I → ℤ) (pivot : ℕ → I) (n : ℕ) (i a : I)
    (hp : ∀ k < n, g i (pivot k) = 1) (ha : g i a = 1)
    (t : Fin n → Bool) (j : ℕ) (hj : j < n) (b : Bool) :
    copyScheduleGraph g pivot n (copySchedulePath n t i) (copyScheduleAnchor n j b a) =
      finalCopyParity t := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hprev : ∀ k < n, g i (pivot k) = 1 := fun k hk => hp k (by omega)
    have ht : Fin.snoc (fun k => t k.castSucc) (t (Fin.last n)) = t :=
      Fin.snoc_init_self t
    by_cases hjn : j = n
    · subst j
      have hanc : copyScheduleAnchor (n + 1) n b a =
          Sum.inl (b, copyScheduleOutside n a) := copyScheduleAnchor_new n b a
      rw [hanc]
      change (if t (Fin.last n) = b then
        transferCopySign (t (Fin.last n)) * copyScheduleGraph g pivot n
          (copySchedulePath n (fun k => t k.castSucc) i) (copyScheduleOutside n a)
        else transferCopySign (t (Fin.last n)) * copyScheduleGraph g pivot n
          (copySchedulePath n (fun k => t k.castSucc) i) (copySchedulePositive n (pivot n))) = _
      rw [copyScheduleGraph_path_to_fresh g pivot n i a ha,
        copyScheduleGraph_path_to_positive g pivot n i (pivot n) hprev (hp n (by omega))]
      rw [← ht, finalCopyParity_snoc]
      simp
    · have hj' : j < n := by omega
      have hanc : copyScheduleAnchor (n + 1) j b a =
          Sum.inr (copyScheduleAnchor n j b a) := copyScheduleAnchor_old n _ b a hjn
      rw [hanc]
      change transferCopySign (t (Fin.last n)) * copyScheduleGraph g pivot n
        (copySchedulePath n (fun k => t k.castSucc) i) (copyScheduleAnchor n j b a) = _
      rw [ih hprev (fun k => t k.castSucc) hj']
      rw [← ht, finalCopyParity_snoc]
      simp

/-- The incoming anchor edge has exactly the previously constructed code.
The initial graph is the only source of the two hypotheses. -/
theorem copyScheduleGraph_anchor_to_path {I : Type*}
    (g : I → I → ℤ) (pivot : ℕ → I) (n : ℕ) (i a : I)
    (hp : ∀ k < n, g a (pivot k) = 1) (ha : g a i = 1)
    (t : Fin n → Bool) (j : Fin n) (b : Bool) :
    copyScheduleGraph g pivot n (copyScheduleAnchor n j b a) (copySchedulePath n t i) =
      anchorIncoming (fun _ => 1) t j b := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    have ht : Fin.snoc (fun k => t k.castSucc) (t (Fin.last n)) = t :=
      Fin.snoc_init_self t
    have hprev : ∀ k < n, g a (pivot k) = 1 := fun k hk => hp k (by omega)
    by_cases hjn : j.val = n
    · have hjlast : j = Fin.last n := Fin.ext hjn
      subst j
      let G := fun x y => copyScheduleGraph g pivot n
        (copySchedulePredecessor (copySchedulePositive n (pivot n)) x)
        (copySchedulePredecessor (copySchedulePositive n (pivot n)) y)
      have hinc : G (some (.inl (copyScheduleOutside n a)))
          (some (.inl (copySchedulePath n (fun k => t k.castSucc) i))) =
            finalCopyParity (fun k => t k.castSucc) := by
        change copyScheduleGraph g pivot n (copyScheduleOutside n a)
          (copySchedulePath n (fun k => t k.castSucc) i) = _
        rw [copyScheduleGraph_fresh_to_path, ha, mul_one]
      have hpiv : G (some (.inl (copyScheduleOutside n a))) none = 1 := by
        change copyScheduleGraph g pivot n (copyScheduleOutside n a)
          (copySchedulePositive n (pivot n)) = _
        rw [copyScheduleGraph_fresh_to_positive, hp n (by omega)]
      have hc := anchorIncoming_created_by_transfer G (copyScheduleOutside n a)
        (copySchedulePath n (fun k => t k.castSucc) i)
        (α := fun _ => 1) (fun k => t k.castSucc) (t (Fin.last n)) b hinc hpiv
      have he : copyScheduleGraph g pivot (n + 1)
          (Sum.inl (b, copyScheduleOutside n a))
          (Sum.inl (t (Fin.last n), copySchedulePath n (fun k => t k.castSucc) i)) =
            anchorIncoming (fun _ => 1) (Fin.snoc (fun k => t k.castSucc) (t (Fin.last n)))
              (Fin.last n) b := hc.symm
      rw [ht] at he
      have hanc : copyScheduleAnchor (n + 1) n b a =
          Sum.inl (b, copyScheduleOutside n a) := copyScheduleAnchor_new n b a
      rw [show (Fin.last n).val = n from rfl, hanc]
      exact he
    · let j' : Fin n := ⟨j.val, by omega⟩
      have hjcast : j'.castSucc = j := Fin.ext rfl
      have hanc : copyScheduleAnchor (n + 1) j b a =
          Sum.inr (copyScheduleAnchor n j b a) := copyScheduleAnchor_old n _ b a hjn
      rw [hanc]
      change transferCopySign (t (Fin.last n)) * copyScheduleGraph g pivot n
        (copyScheduleAnchor n j b a) (copySchedulePath n (fun k => t k.castSucc) i) = _
      rw [ih hprev (fun k => t k.castSucc) j']
      rw [← ht, ← hjcast, anchorIncoming_snoc_old]
      simp

theorem initialCompleteGraph_of_ne {I : Type*} {i j : I} (h : i ≠ j) :
    initialCompleteGraph i j = 1 := by simp [initialCompleteGraph, h]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledTransferGraph
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restricting the graph update to the actual H/Y partition -/

namespace Ostmann

theorem scheduledRetainedGraph_diagonal {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n : ℕ) (i : Option (CopyScheduleH role n ⊕ CopyScheduleY role n)) :
    scheduledRetainedGraph role initialCompleteGraph pivot n i i = 0 :=
  copyScheduleGraph_diagonal initialCompleteGraph pivot initialCompleteGraph_self n _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedOutsideWords
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original prime constituents of each retained Y atom -/

namespace Ostmann

open scoped Classical

theorem expandedOriginalWord_length {V : Type*} {depth : ℕ}
    (w : List (ExpandedScheduledVariable V depth)) :
    (expandedOriginalWord w).length ≤ w.length := by
  induction w with
  | nil => rfl
  | cons v w ih => cases v <;> simp only [expandedOriginalWord, List.length_cons] <;> omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedPrimeCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete Y-prime check count is polynomial in the original word size -/

namespace Ostmann

open scoped Classical

theorem expandedYPrimeCoordinates_length {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (depth n M : ℕ)
    (current : CopyScheduleAtoms role (n + 1) → List (ExpandedScheduledVariable V depth))
    (hc : ∀ i, (current i).length ≤ M) :
    (expandedYPrimeCoordinates role depth n current).length ≤
      3 ^ n * Fintype.card I * M := by
  have hY : Fintype.card (CopyScheduleY role n) ≤ 3 ^ n * Fintype.card I := by
    rw [← copyScheduleVertex_card n]
    exact Fintype.card_subtype_le _
  apply (list_flatMap_length_bound _ _ M (fun i _ =>
    (expandedOriginalWord_length _).trans (hc ⟨.inr i.val, i.property⟩))).trans
  simpa only [Finset.length_toList, Finset.card_univ] using Nat.mul_le_mul_right M hY

theorem expandedSchedulePrimes_count_bounded {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (depth n M : ℕ) (hn : n ≤ depth) (hM : 1 ≤ M)
    (path : List Bool)
    (current : CopyScheduleAtoms role n → List (ExpandedScheduledVariable V depth))
    (hc : ∀ i, (current i).length ≤ M) :
    (expandedSchedulePrimes role depth n path current).CountBounded
      (3 ^ depth * Fintype.card I * M) := by
  induction n generalizing path with
  | zero => trivial
  | succ n ih =>
    refine ⟨?_, ih (by omega) _ _ (reverseCopyLabelMap_list_length role n true _ current M hM hc),
      ih (by omega) _ _ (reverseCopyLabelMap_list_length role n false _ current M hM hc)⟩
    exact (expandedYPrimeCoordinates_length role depth n M current hc).trans
      (Nat.mul_le_mul_right M (Nat.mul_le_mul_right (Fintype.card I)
        (Nat.pow_le_pow_right (by omega) (by omega))))

theorem expandedRootPrimes_count {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n M : ℕ) (hM : 1 ≤ M)
    (words : CopyScheduleAtoms role n → List V) (hw : ∀ i, (words i).length ≤ M) :
    (expandedSchedulePrimes role n n [] (fun i => (words i).map Sum.inl)).count ≤
      (3 ^ n * Fintype.card I * M) * (2 ^ n - 1) := by
  exact WordPrimeDecoration.count_le _ _
    (expandedSchedulePrimes_count_bounded role n n M le_rfl hM [] _
      (fun i => by simpa only [List.length_map] using hw i))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SchedulePairwiseReplay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The reduced support implies every original pairwise-coprimality gate -/

namespace Ostmann

open scoped BigOperators Classical

theorem scheduleAtomUnitsValid_root {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (hu : scheduleAtomUnitsValid role childBound pivotBound (totalAtomUnitRanges role) n x t) :
    ∀ i, (x i).Coprime (frequencyRoot n t).natAbs := by
  cases n with
  | zero => exact (totalAtomUnitRanges_iff role 0 x t).mp hu
  | succ n => exact (totalAtomUnitRanges_iff role (n + 1) x t.1).mp hu.1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduleFullCoprime
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering the complete large-coprimality support from the reduced tests -/

namespace Ostmann

open scoped BigOperators Classical

theorem schedule_full_coprime_reduced {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (h : scheduleAtomFullCoprimeValid role childBound pivotBound n x t) :
    Pairwise (fun i j => (x i).Coprime (x j)) ∧
      scheduleAtomCoprimalitiesValid role childBound pivotBound n x t := by
  induction n with
  | zero => exact ⟨h, trivial⟩
  | succ n ih =>
    exact ⟨h.1, (fun i => (h.2.1 _).symm), (ih _ _ h.2.2.1).2,
      (ih _ _ h.2.2.2).2⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FullAtomTransferWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete grouped weight as a single supported recursive weight -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

theorem fullAtomWeightGuard_node {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j)) (n : ℕ)
    (x : CopyScheduleAtoms role (n + 1) → ℕ) (t : FrequencyTree ℤ (n + 1)) (P : ℕ)
    (hP : ValidTransferNode (scheduleAtomSystem role childBound pivotBound) ⟨n + 1, x⟩
      t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P) :
    fullAtomWeightGuard role childBound pivotBound ranges (n + 1) x t ↔
      fullAtomRootGuard role ranges n x P t.1 ∧
      fullAtomWeightGuard role childBound pivotBound ranges n (reverseCopyLabelMap role n true P x) t.2.1 ∧
      fullAtomWeightGuard role childBound pivotBound ranges n (reverseCopyLabelMap role n false P x) t.2.2 := by
  simp only [fullAtomWeightGuard, scheduleAtomFullCoprimeValid, scheduleAtomUnitsValid,
    scheduleAtomRangesValid, hP.historyPivot_eq, totalAtomUnitRanges_iff, fullAtomRootGuard]
  tauto

private theorem guarded_product (A B C : Prop) [Decidable A] [Decidable B] [Decidable C] (x y : ℂ) :
    (if A ∧ B ∧ C then x * conj y else 0) =
      if A then (if B then x else 0) * conj (if C then y else 0) else 0 := by
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;> simp [hA, hB, hC]

/-- The full weight has exactly the inherited left/right factors, with all
new top tests in the root guard. There is no loss of boundary or unit tests. -/
theorem fullAtomTransferWeight_node {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (n : ℕ)
    (x : CopyScheduleAtoms role (n + 1) → ℕ) (t : FrequencyTree ℤ (n + 1)) (P : ℕ)
    (hP : ValidTransferNode (scheduleAtomSystem role childBound pivotBound) ⟨n + 1, x⟩
      t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P) :
    fullAtomTransferWeight role childBound pivotBound ranges leaf (n + 1) x t =
      if fullAtomRootGuard role ranges n x P t.1 then
        fullAtomTransferWeight role childBound pivotBound ranges leaf n
          (reverseCopyLabelMap role n true P x) t.2.1 *
        conj (fullAtomTransferWeight role childBound pivotBound ranges leaf n
          (reverseCopyLabelMap role n false P x) t.2.2) else 0 := by
  simp only [fullAtomTransferWeight,
    fullAtomWeightGuard_node role childBound pivotBound ranges n x t P hP,
    recursiveTransferWeight_node _ leaf _ n ⟨n + 1, x⟩ t P hP,
    Complex.ofReal_one, one_mul]
  exact guarded_product _ _ _ _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FullAtomWeightSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Support and square-energy bounds for the actual full atom weight -/

namespace Ostmann

open scoped BigOperators Classical

theorem fullAtomTransferWeight_support {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (n : ℕ)
    (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (h : fullAtomTransferWeight role childBound pivotBound ranges leaf n x t ≠ 0) :
    fullAtomWeightGuard role childBound pivotBound ranges n x t ∧
    ValidTransferHistory (scheduleAtomSystem role childBound pivotBound) n ⟨n, x⟩ t := by
  unfold fullAtomTransferWeight at h
  split_ifs at h with hg
  · exact ⟨hg, recursiveTransferWeight_nonzero_valid _ _ _ _ _ _ h⟩
  · exact False.elim (h rfl)

theorem fullAtomTransferWeight_top_support {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (n : ℕ)
    (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (h : fullAtomTransferWeight role childBound pivotBound ranges leaf n x t ≠ 0) :
    Pairwise (fun i j => (x i).Coprime (x j)) ∧
      (∀ i, (x i).Coprime (frequencyRoot n t).natAbs) := by
  have hg := (fullAtomTransferWeight_support role childBound pivotBound ranges leaf n x t h).1
  exact ⟨(schedule_full_coprime_reduced role childBound pivotBound n x t hg.1).1,
    scheduleAtomUnitsValid_root role childBound pivotBound n x t hg.2.1⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FullWeightFrequencies
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nonzero frequencies from the actual unit and modulus-window support -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

theorem fullAtomTransferWeight_all_frequencies_ne_zero {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ)
    (hzero : ∀ x, fullAtomTransferWeight role childBound pivotBound ranges leaf 0 x (0 : ℤ) = 0)
    (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (hw : fullAtomTransferWeight role childBound pivotBound ranges leaf n x t ≠ 0) :
    ∀ s ∈ allFrequencyList n t, s ≠ 0 := by
  induction n with
  | zero =>
    intro s hs
    have he : s = t := by simpa only [allFrequencyList, List.mem_singleton] using hs
    subst s
    intro ht
    subst t
    exact hw (hzero x)
  | succ n ih =>
    obtain ⟨hg, P, hP, _, _⟩ := fullAtomTransferWeight_support role childBound pivotBound ranges leaf
      (n + 1) x t hw
    have hr := ((fullAtomWeightGuard_node role childBound pivotBound ranges n x t P hP).mp hg).1
    rw [fullAtomTransferWeight_node role childBound pivotBound ranges leaf n x t P hP,
      ite_eq_left hr] at hw
    obtain ⟨hL, hR⟩ := mul_ne_zero_iff.mp hw
    have hR' : fullAtomTransferWeight role childBound pivotBound ranges leaf n
        (reverseCopyLabelMap role n false P x) t.2.2 ≠ 0 := by
      intro hz
      exact hR (by rw [hz, map_zero])
    intro s hs
    rcases List.mem_cons.mp hs with he | hs
    · exact he ▸ hP.root_ne_zero
    · rcases List.mem_append.mp hs with hs | hs
      · exact ih _ t.2.1 hL s hs
      · exact ih _ t.2.2 hR' s hs

/-- A zero bottom frequency would make every atom equal to one. The actual
initial modulus window excludes that case, including at its endpoints. -/
theorem fullAtomFourierWeight_zero_frequency {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hX : 0 < X) (hlo : 1 < X * lo)
    (x : CopyScheduleAtoms role 0 → ℕ) :
    fullAtomTransferWeight role childBound pivotBound ranges
      (fun τ v => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
        normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X))
      0 x (0 : ℤ) = 0 := by
  by_contra hw
  have hu := (fullAtomTransferWeight_top_support role childBound pivotBound ranges _ 0 x (0 : ℤ) hw).2
  have hx (i) : x i = 1 := by simpa only [frequencyRoot, Int.natAbs_zero, Nat.coprime_zero_right] using hu i
  have ht : scheduleAtomTotal role ⟨0, x⟩ = 1 := by
    simp only [scheduleAtomTotal, hx, Finset.prod_const_one]
  have hm : ¬ (scheduleAtomTotal role ⟨0, x⟩ : ℝ) / X ∈ Set.Icc lo hi := by
    intro hm
    have h := (le_div_iff₀ hX).mp hm.1
    rw [ht, Nat.cast_one] at h
    nlinarith
  apply hw
  unfold fullAtomTransferWeight
  split_ifs
  · simp only [recursiveTransferWeight, hm, ite_false, if_false, zero_mul]
  · rfl

theorem fullAtomFourierWeight_all_frequencies_ne_zero {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hX : 0 < X) (hlo : 1 < X * lo)
    (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (hw : fullAtomTransferWeight role childBound pivotBound ranges
      (fun τ v => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
        normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X)) n x t ≠ 0) :
    ∀ s ∈ allFrequencyList n t, s ≠ 0 := by
  exact fullAtomTransferWeight_all_frequencies_ne_zero role childBound pivotBound ranges _
    (fullAtomFourierWeight_zero_frequency role childBound pivotBound ranges ψ X lo hi hX hlo) n x t hw

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentUnweighted
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating the original H prior from the supported Fourier weight -/

namespace Ostmann

open scoped BigOperators Classical

theorem constituentTransferWeight_eq_prior_mul {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (P : Finset ℕ) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D) :
    constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a =
      ((∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (a.1 h) : ℝ) : ℂ) *
        constituentUnweightedTransferWeight role size n P childBound pivotBound ranges leaf hist u M a := by
  unfold constituentTransferWeight constituentCurrentWeight constituentUnweightedTransferWeight
  split_ifs
  · rfl
  · exact (mul_zero _).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentCharacterCore
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original priors in each matched character correlation -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

section

variable {I D : Type*} [Fintype I]
variable (role : I → CopyScheduleRole) (size : I → ℕ)
variable (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
variable (Q : (Σ i, Fin (size i)) → Finset ℕ)
variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
variable (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
variable (center : ∀ p : ℕ, ZMod p)
variable (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)

theorem constituentCharacterCoefficient_factor
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D) :
    constituentCharacterCoefficient role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist u M a =
    ((∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (a.1 h) : ℝ) : ℂ) *
      constituentCharacterCore role size χ κ pivot n P hP childBound pivotBound ranges leaf hist u M a := by
  unfold constituentCharacterCoefficient constituentCharacterCore
  rw [constituentTransferWeight_eq_prior_mul]
  ring

end

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FactorialExponential
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary exponential factorial bounds used in arrangement ratios -/

namespace Ostmann

theorem factorial_exp_upper {n : ℕ} (hn : 1 ≤ n) :
    (n.factorial : ℝ) ≤ Real.exp ((n : ℝ) * Real.log n) := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hn
  rw [Real.exp_nat_mul, Real.exp_log hn0]
  exact_mod_cast Nat.factorial_le_pow n

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FinalHistoryCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite-depth cost of summing both frequency histories -/

namespace Ostmann

open scoped BigOperators
open Filter

theorem card_frequencyTree (A : Type) [Fintype A] (n : ℕ) :
    Fintype.card (FrequencyTree A n) = (Fintype.card A) ^ (2 ^ (n + 1) - 1) := by
  induction n with
  | zero => simp [FrequencyTree]
  | succ n ih =>
    simp only [FrequencyTree, Fintype.card_prod] at *
    rw [ih, ← pow_add, ← pow_succ']
    congr 1
    have hp : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
    rw [pow_succ]
    omega

theorem frequency_history_pair_card_bound (S : Finset ℤ) (n : ℕ) (C m : ℝ)
    (hS : (S.card : ℝ) ≤ Real.exp (C * m)) :
    ((Fintype.card (FrequencyTree S n) : ℝ) ^ 2) ≤
      Real.exp ((2 * (2 ^ (n + 1) - 1 : ℕ) : ℝ) * C * m) := by
  rw [card_frequencyTree]
  simp only [Fintype.card_coe]
  push_cast
  rw [← pow_mul]
  have h := pow_le_pow_left₀ (Nat.cast_nonneg S.card) hS ((2 ^ (n + 1) - 1) * 2)
  rw [← Real.exp_nat_mul] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  push_cast
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentCoreEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unique-history energy of the actual fixed-pivot character core -/

namespace Ostmann
open scoped BigOperators Classical

section
variable {I D R : Type*} [Fintype I] [Fintype D] [Fintype R]
variable (role : I → CopyScheduleRole) (size : I → ℕ)
variable (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
variable (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
variable (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)

omit [Fintype D] in
include hP in
theorem constituentCharacterCore_nonzero_valid
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) (d : D)
    (h : constituentCharacterCore role size χ κ pivot n P hP childBound pivotBound ranges leaf hist u M (l, d) ≠ 0) :
    ValidTransferHistory (scheduleAtomSystem role childBound pivotBound) n
      ⟨n, scheduledInsertedAtoms role n M
        (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
        (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))⟩ (hist d) := by
  unfold constituentCharacterCore at h
  have hw := (mul_ne_zero_iff.mp h).1
  unfold constituentUnweightedTransferWeight at hw
  split_ifs at hw
  · exact (fullAtomTransferWeight_support role childBound pivotBound ranges leaf n _ _ hw).2
  · exact False.elim (hw rfl)

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentPrimeFrequencySupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every live final term has nonzero frequencies, including at its leaves -/
namespace Ostmann
open scoped BigOperators Classical SchwartzMap FourierTransform

theorem finite_frequency_range_data (P : Finset ℕ) (hP : P.Nonempty) (R : ℝ) (V : ℕ)
    (hlarge : ∀ p ∈ P, V < p) (hupper : ∀ p ∈ P, (p : ℝ) ≤ R)
    (n : ℕ) (t : FrequencyTree ℤ n)
    (hz : ∀ a ∈ allFrequencyList n t, a ≠ 0)
    (hfreq : ∀ a ∈ allFrequencyList n t, a.natAbs ≤ V) :
    (∀ p ∈ P, ∀ a ∈ allFrequencyList n t, 0 < a.natAbs ∧ a.natAbs < p) ∧
      ∀ a ∈ allFrequencyList n t, |(a : ℝ)| ≤ R := by
  constructor
  · intro p hp a ha
    exact ⟨Int.natAbs_pos.mpr (hz a ha), (hfreq a ha).trans_lt (hlarge p hp)⟩
  · intro a ha
    obtain ⟨p, hp⟩ := hP
    have hh : (a.natAbs : ℝ) ≤ R :=
      (Nat.cast_le.mpr (hfreq a ha)).trans ((Nat.cast_le.mpr (hlarge p hp).le).trans (hupper p hp))
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentCoreFrequencySupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every live matched core has the actual nonzero Fourier frequencies -/
namespace Ostmann
open scoped BigOperators Classical SchwartzMap FourierTransform

theorem constituentCharacterCore_nonzero_frequencies {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hX : 0 < X) (hXlo : 1 < X * lo)
    (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) (d : D)
    (hq : constituentCharacterCore role size χ κ pivot n P hP childBound pivotBound ranges
      (scheduleFourierLeaf role ψ X lo hi) hist u M (l, d) ≠ 0) :
    NonzeroInternalFrequencies n (hist d) ∧ ∀ a ∈ allFrequencyList n (hist d), a ≠ 0 := by
  have hv := constituentCharacterCore_nonzero_valid role size χ κ pivot n P hP childBound
    pivotBound ranges (scheduleFourierLeaf role ψ X lo hi) hist u M l d hq
  refine ⟨hv.nonzero_internal _ _ _ _, ?_⟩
  unfold constituentCharacterCore at hq
  have hw := (mul_ne_zero_iff.mp hq).1
  unfold constituentUnweightedTransferWeight at hw
  split_ifs at hw
  · exact fullAtomFourierWeight_all_frequencies_ne_zero role childBound pivotBound ranges
      ψ X lo hi hX hXlo n _ (hist d) hw
  · exact False.elim (hw rfl)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InsertedConstituentWords
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Word coordinates for the fixed integer pivot and the retained primes -/

namespace Ostmann

open scoped BigOperators Classical

theorem insertedConstituentWord_length_le {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n S : ℕ) (hS : 1 ≤ S) (hsize : ∀ i, size i ≤ S)
    (v : CopyScheduleAtoms role n) : (insertedConstituentWord role size n v).length ≤ S := by
  obtain ⟨a, rfl⟩ := (scheduledPartitionEquiv role n).surjective v
  rcases a with p | h | y
  · simpa only [insertedConstituentWord, Equiv.symm_apply_apply, List.length_singleton] using hS
  · simpa only [insertedConstituentWord, Equiv.symm_apply_apply, List.length_ofFn] using
      hsize (copyScheduleOrigin n h.val)
  · simpa only [insertedConstituentWord, Equiv.symm_apply_apply, List.length_ofFn] using
      hsize (copyScheduleOrigin n y.val)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentPairComplexity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete word and support counts for the actual two histories -/

namespace Ostmann
open scoped Classical

theorem WordTransferTemplate.wordsBounded_mono {V : Type*} {n B C : ℕ}
    (T : WordTransferTemplate V n) (hT : T.WordsBounded B) (hBC : B ≤ C) : T.WordsBounded C := by
  induction T with
  | leaf w => exact hT.trans hBC
  | node d L R ihL ihR => exact ⟨hT.1.trans hBC, ihL hT.2.1, ihR hT.2.2⟩

section
variable {I : Type*} [Fintype I]
variable (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
variable (e : Equiv.Perm (CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n))

/-- One linear word budget covers both exact templates, all inherited units,
and every supplied range involving at most `A` current atoms. -/
theorem constituent_pair_word_bounds
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (S A : ℕ) (hS : 1 ≤ S) (hsize : ∀ i, size i ≤ S)
    (hA : ∀ j ≤ n, ∀ r ∈ ranges j, r.atoms.length ≤ A) :
    let B := 2 * 3 ^ n * Fintype.card I * S + A * S + 4
    (expandedRootTemplate role n (insertedConstituentWord role size n) childBound pivotBound).WordsBounded B ∧
    (expandedRootTemplate role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) childBound pivotBound).WordsBounded B ∧
    (expandedRootRanges role n (insertedConstituentWord role size n) ranges).WordsBounded B ∧
    (expandedRootRanges role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) ranges).WordsBounded B ∧
    (expandedRootRanges role n (insertedConstituentWord role size n) (totalAtomUnitRanges role)).WordsBounded B ∧
    (expandedRootRanges role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) (totalAtomUnitRanges role)).WordsBounded B := by
  dsimp only
  have hw := insertedConstituentWord_length_le role size n S hS hsize
  have hwR (i) : (((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) i).length ≤ S := by simpa only [List.length_map] using hw i
  have ht : 2 * 3 ^ n * Fintype.card I * S + 4 ≤
      2 * 3 ^ n * Fintype.card I * S + A * S + 4 := by omega
  have hr : A * S + 1 ≤ 2 * 3 ^ n * Fintype.card I * S + A * S + 4 := by omega
  have hd (words : CopyScheduleAtoms role n → List (Option ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n))))
      (hwords : ∀ i, (words i).length ≤ S) :
      (expandedRootRanges role n words ranges).WordsBounded
        (2 * 3 ^ n * Fintype.card I * S + A * S + 4) := by
    apply WordRangeDecoration.wordsBounded_mono _ _ hr
    exact expandedScheduleRanges_words_bounded role _ ranges n A S hS hA [] _
      (fun i => by simpa only [List.length_map] using hwords i)
  exact ⟨WordTransferTemplate.wordsBounded_mono _ (expandedRootTemplate_size role n (insertedConstituentWord role size n) childBound pivotBound S hS hw) ht,
    WordTransferTemplate.wordsBounded_mono _ (expandedRootTemplate_size role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) childBound pivotBound S hS hwR) ht,
    hd (insertedConstituentWord role size n) hw, hd ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) hwR,
    WordRangeDecoration.wordsBounded_mono _ (totalAtomUnits_words_bounded role n (insertedConstituentWord role size n) S hS hw) ht,
    WordRangeDecoration.wordsBounded_mono _ (totalAtomUnits_words_bounded role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) S hS hwR) ht⟩

theorem constituent_pair_prime_count (S : ℕ) (hS : 1 ≤ S) (hsize : ∀ i, size i ≤ S) :
    (expandedSchedulePrimes role n n [] (fun i => List.map Sum.inl ((insertedConstituentWord role size n) i))).count +
    (expandedSchedulePrimes role n n [] (fun i => List.map Sum.inl (((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) i))).count ≤
      2 * ((3 ^ n * Fintype.card I * S) * (2 ^ n - 1)) := by
  have hw := insertedConstituentWord_length_le role size n S hS hsize
  have hwR (i) : (((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) i).length ≤ S := by simpa only [List.length_map] using hw i
  have hL := expandedRootPrimes_count role n S hS (insertedConstituentWord role size n) hw
  have hR := expandedRootPrimes_count role n S hS ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) hwR
  exact (Nat.add_le_add hL hR).trans_eq (by omega)

theorem constituent_pair_top_count (S : ℕ) (hS : 1 ≤ S) (hsize : ∀ i, size i ≤ S) :
    (constituentPrimePairChecks ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n)) ++ atomPairChecks (insertedConstituentWord role size n) ++ atomPairChecks ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i)))).length ≤
      (Fintype.card ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n))) ^ 2 + 2 * (3 ^ n * Fintype.card I * S) ^ 2 := by
  have hw := insertedConstituentWord_length_le role size n S hS hsize
  have hwR (i) : (((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) i).length ≤ S := by simpa only [List.length_map] using hw i
  have he := atomPairChecks_length (fun i : ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n)) => [some i]) 1 (by intro i; rfl)
  simp only [Nat.mul_one] at he
  have hL := atomPairChecks_length (insertedConstituentWord role size n) S hw
  have hR := atomPairChecks_length ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) S hwR
  have hc := Nat.mul_le_mul_right S (copyScheduleAtoms_card_le role n)
  have hs := Nat.pow_le_pow_left hc 2
  simp only [List.length_append, constituentPrimePairChecks]
  omega

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordRootRange
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Adding one exact product cutoff at the root of a history -/

namespace Ostmann

open scoped BigOperators Classical

theorem WordRangeDecoration.prependRoot_count {σ : Type*} {n : ℕ}
    (r : WordRange σ) (D : WordRangeDecoration σ n) :
    (D.prependRoot r).count = D.count + 1 := by
  cases D with
  | leaf ranges => simp only [prependRoot, count, List.length_cons]
  | node ranges L R => simp only [prependRoot, count, List.length_cons]; omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentRangeCounts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counts for the actual ranges, including the reciprocal-product cutoff -/

namespace Ostmann
open scoped Classical

/-- The added root cutoff costs one test; all inherited tests are counted
on their actual binary history tree. -/
theorem expandedRootRanges_count_le {I σ : Type*}
    (role : I → CopyScheduleRole) (n K : ℕ)
    (words : CopyScheduleAtoms role n → List σ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (hK : ∀ j ≤ n, (ranges j).length ≤ K) :
    (expandedRootRanges role n words ranges).count ≤ K * (2 ^ (n + 1) - 1) := by
  exact WordRangeDecoration.count_le _ K
    (expandedScheduleRanges_count_bounded role _ ranges n K hK [] _)

theorem expandedRootRanges_cutoff_count_le {I σ : Type*}
    (role : I → CopyScheduleRole) (n K : ℕ)
    (words : CopyScheduleAtoms role n → List σ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (hK : ∀ j ≤ n, (ranges j).length ≤ K)
    (r : WordRange (ExpandedScheduledVariable σ n)) :
    ((expandedRootRanges role n words ranges).prependRoot r).count ≤
      K * (2 ^ (n + 1) - 1) + 1 := by
  rw [WordRangeDecoration.prependRoot_count]
  exact Nat.add_le_add_right (expandedRootRanges_count_le role n K words ranges hK) 1

/-- Both histories, with the extra cutoff on the left, share one constant
range-count bound and hence the linear bound used in the numerical estimate. -/
theorem expandedRootRanges_pair_linear_count {I σ : Type*}
    (role : I → CopyScheduleRole) (n K : ℕ)
    (words words' : CopyScheduleAtoms role n → List σ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (hK : ∀ j ≤ n, (ranges j).length ≤ K)
    (r : WordRange (ExpandedScheduledVariable σ n)) (m : ℝ) (hm : 0 ≤ m) :
    (((expandedRootRanges role n words ranges).prependRoot r).count : ℝ) ≤
      (K * (2 ^ (n + 1) - 1) + 1 : ℕ) * (1 + m) ∧
    ((expandedRootRanges role n words' ranges).count : ℝ) ≤
      (K * (2 ^ (n + 1) - 1) + 1 : ℕ) * (1 + m) := by
  have hL : (((expandedRootRanges role n words ranges).prependRoot r).count : ℝ) ≤
      (K * (2 ^ (n + 1) - 1) + 1 : ℕ) := by
    exact_mod_cast expandedRootRanges_cutoff_count_le role n K words ranges hK r
  have hR : ((expandedRootRanges role n words' ranges).count : ℝ) ≤
      (K * (2 ^ (n + 1) - 1) + 1 : ℕ) := by
    exact_mod_cast (expandedRootRanges_count_le role n K words' ranges hK).trans (Nat.le_add_right _ 1)
  have hb : ((K * (2 ^ (n + 1) - 1) + 1 : ℕ) : ℝ) ≤
      (K * (2 ^ (n + 1) - 1) + 1 : ℕ) * (1 + m) :=
    le_mul_of_one_le_right (Nat.cast_nonneg _) (by linarith)
  exact ⟨hL.trans hb, hR.trans hb⟩

/-- With linear atom sizes, the concrete word budget stays linear. -/
theorem constituent_word_budget_linear {I : Type*} [Fintype I]
    (n A S : ℕ) (s m : ℝ) (hs : (S : ℝ) ≤ s * (1 + m)) (hm : 0 ≤ m) :
    ((2 * 3 ^ n * Fintype.card I * S + A * S + 4 : ℕ) : ℝ) ≤
      (((2 * 3 ^ n * Fintype.card I + A : ℕ) : ℝ) * s + 4) * (1 + m) := by
  have hmult := mul_le_mul_of_nonneg_left hs
    (Nat.cast_nonneg (2 * 3 ^ n * Fintype.card I + A))
  push_cast at hmult ⊢
  nlinarith only [hm, hmult]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentFinalCostData
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual final pair counts at the linear constituent-size scale -/
namespace Ostmann
open scoped Classical

theorem constituentFinalCountRate_nonneg (N n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    0 ≤ constituentFinalCountRate N n s := by
  unfold constituentFinalCountRate
  positivity

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledMatchedEdges
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The anchor interaction in the literal retained matching graph -/

namespace Ostmann
open scoped Classical

theorem scheduledMatchedGraph_self {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n : ℕ) (e : Equiv.Perm (CopyScheduleH role n))
    (x : CopyScheduleH role n ⊕ CopyScheduleY role n) :
    scheduledMatchedGraph role pivot n e x x = 0 := by
  simp only [scheduledMatchedGraph, graphDifference, transportGraph, retainedInternalGraph,
    scheduledRetainedGraph_diagonal, sub_self]

/-- This is an identity for the computed graph, with the counterpart slot
identified by the actual inverse matching permutation. -/
theorem scheduledMatchedGraph_anchor_word {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n : ℕ) (e : Equiv.Perm (CopyScheduleH role (n + 1)))
    (a i i' : I) (j : Fin (n + 1)) (ha : role a = .anchor j) (b : Bool)
    (hap : ∀ k < n + 1, a ≠ pivot k) (hai : a ≠ i) (hai' : a ≠ i')
    (t t' : Fin (n + 1) → Bool) (h : CopyScheduleH role (n + 1))
    (hh : h.val = copySchedulePath (n + 1) t i)
    (hh' : (e.symm h).val = copySchedulePath (n + 1) t' i') :
    scheduledMatchedGraph role pivot (n + 1) e
      (.inr (scheduledPastAnchor role n a j ha b)) (.inl h) =
      anchorIncoming (fun _ => 1) t j b - anchorIncoming (fun _ => 1) t' j b := by
  change copyScheduleGraph initialCompleteGraph pivot (n + 1)
      (copyScheduleAnchor (n + 1) j b a) h.val -
    copyScheduleGraph initialCompleteGraph pivot (n + 1)
      (copyScheduleAnchor (n + 1) j b a) (e.symm h).val = _
  rw [hh, hh', copyScheduleGraph_anchor_to_path, copyScheduleGraph_anchor_to_path]
  · exact fun k hk => initialCompleteGraph_of_ne (hap k hk)
  · exact initialCompleteGraph_of_ne hai'
  · exact fun k hk => initialCompleteGraph_of_ne (hap k hk)
  · exact initialCompleteGraph_of_ne hai

theorem scheduledMatchedGraph_word_anchor {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n : ℕ) (e : Equiv.Perm (CopyScheduleH role (n + 1)))
    (a i i' : I) (j : Fin (n + 1)) (ha : role a = .anchor j) (b : Bool)
    (hip : ∀ k < n + 1, i ≠ pivot k) (hi'p : ∀ k < n + 1, i' ≠ pivot k)
    (hia : i ≠ a) (hi'a : i' ≠ a)
    (t t' : Fin (n + 1) → Bool) (h : CopyScheduleH role (n + 1))
    (hh : h.val = copySchedulePath (n + 1) t i)
    (hh' : (e.symm h).val = copySchedulePath (n + 1) t' i') :
    scheduledMatchedGraph role pivot (n + 1) e
      (.inl h) (.inr (scheduledPastAnchor role n a j ha b)) =
      finalCopyParity t - finalCopyParity t' := by
  change copyScheduleGraph initialCompleteGraph pivot (n + 1)
      h.val (copyScheduleAnchor (n + 1) j b a) -
    copyScheduleGraph initialCompleteGraph pivot (n + 1)
      (e.symm h).val (copyScheduleAnchor (n + 1) j b a) = _
  rw [hh, hh', copyScheduleGraph_path_to_anchor, copyScheduleGraph_path_to_anchor]
  · exact fun k hk => initialCompleteGraph_of_ne (hi'p k hk)
  · exact initialCompleteGraph_of_ne hi'a
  · exact j.isLt
  · exact fun k hk => initialCompleteGraph_of_ne (hip k hk)
  · exact initialCompleteGraph_of_ne hia
  · exact j.isLt

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentMatchedCostData
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual matched pair counts at the linear constituent-size scale -/
namespace Ostmann
open scoped Classical

theorem constituent_retained_card_le {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n S : ℕ)
    (hsize : ∀ i, size i ≤ S) :
    Fintype.card (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n ⊕
      CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n) ≤
        3 ^ n * Fintype.card I * S := by
  have hcard : Fintype.card (Σ i, Fin (size i)) ≤ Fintype.card I * S := by
    rw [Fintype.card_sigma]
    simpa only [Fintype.card_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul] using
      (Finset.sum_le_sum (s := Finset.univ) (f := size) (g := fun _ => S)
        (fun i _ => hsize i))
  apply (Fintype.card_le_of_injective _
    (scheduledRetainedEmbedding (fun i : Σ a, Fin (size a) => role i.1) n).injective).trans
  apply (copyScheduleAtoms_card_le _ n).trans
  simpa only [mul_assoc] using Nat.mul_le_mul_left (3 ^ n) hcard

theorem constituent_retained_word_bound {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n S A : ℕ)
    (hsize : ∀ i, size i ≤ S) :
    Fintype.card (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n) + 1 ≤
      2 * 3 ^ n * Fintype.card I * S + A * S + 4 := by
  have hc := constituent_retained_card_le role size n S hsize
  rw [Fintype.card_sum] at hc
  have he : 2 * 3 ^ n * Fintype.card I * S = 2 * (3 ^ n * Fintype.card I * S) := by ring
  rw [he]
  omega

theorem constituent_matched_top_count {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n))
    (S : ℕ) (hS : 1 ≤ S) (hsize : ∀ i, size i ≤ S) :
    let ρ := fun i : Σ a, Fin (size a) => role i.1
    let W := insertedConstituentWord role size n
    let W' := fun v => List.map (insertedConstituentPerm role size n e) (W v)
    (constituentPrimePairChecks (CopyScheduleH ρ n ⊕ CopyScheduleY ρ n) ++
      atomPairChecks W ++ atomPairChecks W').length ≤ 3 * (3 ^ n * Fintype.card I * S) ^ 2 := by
  intro ρ W W'
  have hcard : Fintype.card (Σ i, Fin (size i)) ≤ Fintype.card I * S := by
    rw [Fintype.card_sigma]
    simpa only [Fintype.card_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul] using
      (Finset.sum_le_sum (s := Finset.univ) (f := size) (g := fun _ => S)
        (fun i _ => hsize i))
  have hK : Fintype.card (CopyScheduleH ρ n ⊕ CopyScheduleY ρ n) ≤
      3 ^ n * Fintype.card I * S := by
    apply (Fintype.card_le_of_injective _ (scheduledRetainedEmbedding ρ n).injective).trans
    apply (copyScheduleAtoms_card_le ρ n).trans
    simpa only [mul_assoc] using Nat.mul_le_mul_left (3 ^ n) hcard
  have hc := constituent_pair_top_count role size n e S hS hsize
  have hp := Nat.pow_le_pow_left hK 2
  dsimp only [ρ] at hp
  exact hc.trans (by omega)

theorem constituent_matched_linear_counts {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n))
    (S : ℕ) (s m : ℝ) (hS : 1 ≤ S) (hsize : ∀ i, size i ≤ S)
    (hs : 0 ≤ s) (hm : 0 ≤ m) (hSm : (S : ℝ) ≤ s * (1 + m)) :
    let W := insertedConstituentWord role size n
    let W' := fun v => List.map (insertedConstituentPerm role size n e) (W v)
    let a := constituentFinalCountRate (Fintype.card I) n s
    (((expandedSchedulePrimes role n n [] (fun i => (W i).map Sum.inl)).count +
      (expandedSchedulePrimes role n n [] (fun i => (W' i).map Sum.inl)).count : ℕ) : ℝ) ≤
        a * (1 + m) ∧
    ((constituentPrimePairChecks (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n ⊕
      CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n) ++
      atomPairChecks W ++ atomPairChecks W').length : ℝ) ≤ a * (1 + m) ^ 2 := by
  intro W W' a
  have hp := constituent_pair_prime_count role size n e S hS hsize
  have hc := constituent_matched_top_count role size n e S hS hsize
  have hrealp : (((expandedSchedulePrimes role n n [] (fun i => (W i).map Sum.inl)).count +
      (expandedSchedulePrimes role n n [] (fun i => (W' i).map Sum.inl)).count : ℕ) : ℝ) ≤
      2 * (((3 ^ n * Fintype.card I : ℕ) : ℝ) : ℝ) * S * (2 ^ n - 1 : ℕ) := by
    calc
      _ ≤ 2 * (((3 ^ n * Fintype.card I : ℕ) : ℝ) * S * (2 ^ n - 1 : ℕ)) := by
        exact_mod_cast hp
      _ = _ := by ring
  have hrealc : ((constituentPrimePairChecks (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n ⊕
      CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n) ++
      atomPairChecks W ++ atomPairChecks W').length : ℝ) ≤
      3 * ((((3 ^ n * Fintype.card I : ℕ) : ℝ) : ℝ) * S) ^ 2 := by
    exact_mod_cast hc
  have ha1 : 2 * ((3 ^ n * Fintype.card I : ℕ) : ℝ) * s * (2 ^ n - 1 : ℕ) ≤ a := by
    dsimp [a, constituentFinalCountRate]
    linarith [sq_nonneg ((((3 ^ n * Fintype.card I : ℕ) : ℝ) : ℝ) * s)]
  have ha2 : 3 * (((3 ^ n * Fintype.card I : ℕ) : ℝ) * s) ^ 2 ≤ a := by
    dsimp [a, constituentFinalCountRate]
    have hh : 0 ≤ 2 * ((3 ^ n * Fintype.card I : ℕ) : ℝ) * s * (2 ^ n - 1 : ℕ) := by positivity
    linarith
  constructor
  · calc
      _ ≤ 2 * ((3 ^ n * Fintype.card I : ℕ) : ℝ) * S * (2 ^ n - 1 : ℕ) := hrealp
      _ ≤ 2 * ((3 ^ n * Fintype.card I : ℕ) : ℝ) * (s * (1 + m)) * (2 ^ n - 1 : ℕ) := by gcongr
      _ = (2 * ((3 ^ n * Fintype.card I : ℕ) : ℝ) * s * (2 ^ n - 1 : ℕ)) * (1 + m) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ha1 (by linarith)
  · calc
      _ ≤ 3 * (((3 ^ n * Fintype.card I : ℕ) : ℝ) * S) ^ 2 := hrealc
      _ ≤ 3 * (((3 ^ n * Fintype.card I : ℕ) : ℝ) * (s * (1 + m))) ^ 2 := by gcongr
      _ = (3 * (((3 ^ n * Fintype.card I : ℕ) : ℝ) * s) ^ 2) * (1 + m) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ha2 (sq_nonneg _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledFrequencyBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete rounded frequency family and its finite counting cost -/

namespace Ostmann

open scoped BigOperators Classical

theorem transferFrequencyRange_mono : Monotone transferFrequencyRange := by
  intro a b hab s hs
  exact (mem_transferFrequencyRange b s).mpr (((mem_transferFrequencyRange a s).mp hs).trans hab)

theorem scheduledFrequencyIndex_card_le (V : ℕ → ℕ) (hV : Monotone V) (n : ℕ) :
    Fintype.card (ScheduledFrequencyIndex V n) ≤
      (transferFrequencyRange (V n)).card ^ (2 ^ (n + 1) - 1) := by
  induction n with
  | zero =>
    have he : ScheduledFrequencyIndex V 0 ≃ transferFrequencyRange (V 0) := Equiv.refl _
    have hc := Fintype.card_congr he
    simpa only [Fintype.card_coe, Nat.zero_add, pow_one, Nat.reducePow, Nat.reduceSub] using hc.le
  | succ n ih =>
    have hc := Finset.card_le_card (transferFrequencyRange_mono (hV (Nat.le_succ n)))
    have hh := ih.trans (Nat.pow_le_pow_left hc (2 ^ (n + 1) - 1))
    have he : ScheduledFrequencyIndex V (n + 1) ≃
        (transferFrequencyRange (V (n + 1))) × (ScheduledFrequencyIndex V n × ScheduledFrequencyIndex V n) :=
      Equiv.refl _
    have hcard := Fintype.card_congr he
    simp only [Fintype.card_prod, Fintype.card_coe] at hcard
    rw [hcard]
    calc
      _ ≤ (transferFrequencyRange (V (n + 1))).card *
          ((transferFrequencyRange (V (n + 1))).card ^ (2 ^ (n + 1) - 1) *
           (transferFrequencyRange (V (n + 1))).card ^ (2 ^ (n + 1) - 1)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul hh hh)
      _ = _ := by
        rw [← pow_add, ← pow_succ']
        congr 1
        have hp : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
        rw [pow_succ]
        omega

theorem scheduledFrequencyIndex_pair_card_bound (V : ℕ → ℕ) (hV : Monotone V)
    (n : ℕ) (C m : ℝ) (hS : ((transferFrequencyRange (V n)).card : ℝ) ≤ Real.exp (C * m)) :
    (Fintype.card (ScheduledFrequencyIndex V n) : ℝ) ^ 2 ≤
      Real.exp ((2 * (2 ^ (n + 1) - 1 : ℕ) : ℝ) * C * m) := by
  have hc : Fintype.card (ScheduledFrequencyIndex V n) ≤
      Fintype.card (FrequencyTree (transferFrequencyRange (V n)) n) := by
    rw [card_frequencyTree, Fintype.card_coe]
    exact scheduledFrequencyIndex_card_le V hV n
  exact (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hc) 2).trans
    (frequency_history_pair_card_bound (transferFrequencyRange (V n)) n C m hS)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RoundedEnergyCutoffs
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numerical cutoffs for the actual square-root-reserve schedule -/

namespace Ostmann
open Filter

/-- The signed root-frequency set includes zero and both endpoints. -/
theorem card_transferFrequencyRange (V : ℕ) : (transferFrequencyRange V).card = 2 * V + 1 := by
  simp only [transferFrequencyRange, Int.card_Icc]
  omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledMatchingError
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All matching and frequency sums preserve the small character error -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem factorial_le_exp_square (n : ℕ) :
    (n.factorial : ℝ) ≤ Real.exp ((n : ℝ) ^ 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · apply (factorial_exp_upper hn).trans
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left (Real.log_le_self (Nat.cast_nonneg n)) (Nat.cast_nonneg n)]

theorem eventual_scheduled_matching_error (n : ℕ) (a C H T z α c : ℝ)
    (ha : 0 ≤ a) (hC : 0 ≤ C) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (hz : 0 ≤ z) (hα : 0 < α) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ (J : Type*) [Fintype J] (M : ℝ)
      (V : ℕ → ℕ) (S : Finset (Equiv.Perm J)) (mass : J → ℝ),
      0 ≤ M → M ≤ z * L → (Fintype.card J : ℝ) ≤ a * (1 + M) →
      Monotone V → ((transferFrequencyRange (V n)).card : ℝ) ≤ Real.exp (C * (1 + M)) →
      (∀ j, 0 ≤ mass j) → (∀ j, mass j ≤ Real.exp (H * (1 + M))) →
      (S.card : ℝ) * (Fintype.card (ScheduledFrequencyIndex V n) : ℝ) ^ 2 *
        (∏ j, mass j) * Real.exp (-c * Real.exp (α * L)) ≤ Real.exp (-T * M) := by
  let D : ℝ := 2 * ((2 ^ (n + 1) - 1 : ℕ) : ℝ)
  let B := a ^ 2 + a * H + D * C
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  filter_upwards [eventual_polynomial_log_budget (B + T) z α c 2 (by positivity) hz hα hc]
    with L hL
  intro J _ M V S mass hM hML hcard hV hfreq hmass hmassupper
  have hp : 0 ≤ 1 + M := by linarith
  have hfact : (S.card : ℝ) ≤ Real.exp (a ^ 2 * (1 + M) ^ 2) := by
    have hcount : S.card ≤ (Fintype.card J).factorial := by
      simpa only [Fintype.card_perm] using Finset.card_le_univ S
    apply (Nat.cast_le.mpr hcount).trans
    apply (factorial_le_exp_square _).trans
    apply Real.exp_le_exp.mpr
    calc
      (Fintype.card J : ℝ) ^ 2 ≤ (a * (1 + M)) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
      _ = _ := by ring
  have hhist : (Fintype.card (ScheduledFrequencyIndex V n) : ℝ) ^ 2 ≤
      Real.exp (D * C * (1 + M) ^ 2) := by
    apply (scheduledFrequencyIndex_pair_card_bound V hV n C (1 + M) hfreq).trans
    apply Real.exp_le_exp.mpr
    change D * C * (1 + M) ≤ D * C * (1 + M) ^ 2
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hD hC)
    nlinarith [sq_nonneg M]
  have hprod : (∏ j, mass j) ≤ Real.exp (a * H * (1 + M) ^ 2) := by
    calc
      _ ≤ ∏ _j : J, Real.exp (H * (1 + M)) :=
        Finset.prod_le_prod (fun j _ => hmass j) (fun j _ => hmassupper j)
      _ = Real.exp ((Fintype.card J : ℝ) * (H * (1 + M))) := by
        rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        calc
          _ ≤ (a * (1 + M)) * (H * (1 + M)) :=
            mul_le_mul_of_nonneg_right hcard (mul_nonneg hH hp)
          _ = _ := by ring
  have htotal : (S.card : ℝ) * (Fintype.card (ScheduledFrequencyIndex V n) : ℝ) ^ 2 *
      (∏ j, mass j) ≤ Real.exp (B * (1 + M) ^ 2) := by
    apply (mul_le_mul (mul_le_mul hfact hhist (sq_nonneg _) (Real.exp_nonneg _)) hprod
      (Finset.prod_nonneg fun j _ => hmass j) (by positivity)).trans_eq
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [B]
    ring
  calc
    _ ≤ Real.exp (B * (1 + M) ^ 2) * Real.exp (-c * Real.exp (α * L)) :=
      mul_le_mul_of_nonneg_right htotal (Real.exp_nonneg _)
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hh := hL M hM hML
      have ht : T * M ≤ T * (1 + M) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hT
        nlinarith [sq_nonneg M]
      nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentMatchingError
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The matched error with its actual constituent counts and frequency cutoff -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem transferFrequencyRange_card_exp_bound (V : ℕ) (C M : ℝ)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hV : (V : ℝ) ≤ Real.exp (C * (1 + M))) :
    ((transferFrequencyRange V).card : ℝ) ≤ Real.exp ((C + Real.log 3) * (1 + M)) := by
  have hlog : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have he : 1 ≤ Real.exp (C * (1 + M)) := Real.one_le_exp (by positivity)
  calc
    _ = 2 * (V : ℝ) + 1 := by rw [card_transferFrequencyRange]; push_cast; rfl
    _ ≤ 3 * Real.exp (C * (1 + M)) := by linarith
    _ = Real.exp (Real.log 3 + C * (1 + M)) := by
      rw [Real.exp_add, Real.exp_log (by norm_num)]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

theorem eventual_constituent_matching_error {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (s C H T z α c : ℝ)
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (hz : 0 ≤ z) (hα : 0 < α) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ (size : I → ℕ) (Smax : ℕ) (_hsize : ∀ i, size i ≤ Smax)
      (M : ℝ) (_hM : 0 ≤ M) (_hML : M ≤ z * L) (_hSM : (Smax : ℝ) ≤ s * (1 + M))
      (V : ℕ → ℕ) (_hV : Monotone V) (_hVn : (V n : ℝ) ≤ Real.exp (C * (1 + M)))
      (Sbad : Finset (Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)))
      (Q : (Σ a, Fin (size a)) → Finset ℕ)
      (_hQinv : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (H * (1 + M))),
      (Sbad.card : ℝ) * (Fintype.card (ScheduledFrequencyIndex V n) : ℝ) ^ 2 *
        (∏ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
          (∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)⁻¹) *
        Real.exp (-c * Real.exp (α * L)) ≤ Real.exp (-T * M) := by
  let a : ℝ := (3 ^ n * Fintype.card I : ℕ) * s
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hCr : 0 ≤ C + Real.log 3 := add_nonneg hC (Real.log_nonneg (by norm_num))
  filter_upwards [eventual_scheduled_matching_error n a (C + Real.log 3) H T z α c
    ha hCr hH hT hz hα hc] with L hL
  intro size Smax hsize M hM hML hSM V hV hVn Sbad Q hQinv
  let J := CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n
  have hcard : (Fintype.card J : ℝ) ≤ a * (1 + M) := by
    have hh := constituent_retained_card_le role size n Smax hsize
    rw [Fintype.card_sum] at hh
    have hh' : Fintype.card J ≤ 3 ^ n * Fintype.card I * Smax := by dsimp [J]; omega
    calc
      _ ≤ ((3 ^ n * Fintype.card I : ℕ) : ℝ) * (Smax : ℝ) := by exact_mod_cast hh'
      _ ≤ ((3 ^ n * Fintype.card I : ℕ) : ℝ) * (s * (1 + M)) :=
        mul_le_mul_of_nonneg_left hSM (by positivity)
      _ = _ := by dsimp [a]; ring
  exact hL J M V Sbad
    (fun h => (∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)⁻¹)
    hM hML hcard hV (transferFrequencyRange_card_exp_bound _ C M hC hM hVn)
    (fun _ => by positivity) (fun _ => hQinv _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteEnumeration
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An explicit bridge between equivalent finite enumerations -/

namespace Ostmann

theorem finite_univ_canonical {A : Type*} [Finite A] (F : Fintype A) :
    @Finset.univ A F = @Finset.univ A (Fintype.ofFinite A) := by
  cases Subsingleton.elim F (Fintype.ofFinite A)
  rfl

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentMatchingExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal matching sum under its original H and Y priors -/
namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem sum_split_prime_prior {H Y : Type*} [Fintype H] [Fintype Y]
    (P : Finset ℕ) (Q : H ⊕ Y → Finset ℕ) (F : (H ⊕ Y → P) → ℂ) :
    (∑ x : H ⊕ Y → P, ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) * F x) =
      ∑ u : Y → P, ((∏ y, primeSubsetPrior P (Q (.inr y)) (u y) : ℝ) : ℂ) *
        ∑ l : H → P, ((∏ h, primeSubsetPrior P (Q (.inl h)) (l h) : ℝ) : ℂ) *
          F (Sum.elim l u) := by
  rw [← (Equiv.sumArrowEquivProdArrow H Y P).symm.sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  simp only [Fintype.prod_sum_type, Equiv.sumArrowEquivProdArrow_symm_apply_inl,
    Equiv.sumArrowEquivProdArrow_symm_apply_inr, Complex.ofReal_mul]
  change _ * F (Sum.elim l u) = _
  ring

section
variable {I D : Type*} [Fintype I] [Fintype D]
variable (role : I → CopyScheduleRole) (size : I → ℕ)
variable (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
variable (Q : (Σ i, Fin (size i)) → Finset ℕ)
variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
variable (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)

omit [Fintype D] in
theorem constituentOriginalMatchedPair_eq
    (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n))
    (d d' : D) (M : ℕ) :
    constituentOriginalMatchedPair role size χ κ pivot n P hP Q childBound pivotBound ranges leaf hist e d d' M =
      ∑ u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P,
        ((∏ y, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) (u y) : ℝ) : ℂ) *
        ∑ l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P,
          constituentCharacterCoefficient role size χ κ pivot n P hP Q childBound pivotBound ranges
            leaf hist u M (l, d) *
          conj (constituentCharacterCoefficient role size χ κ pivot n P hP Q childBound pivotBound ranges
            leaf hist u M (l ∘ e.symm, d')) := by
  unfold constituentOriginalMatchedPair
  simp_rw [mul_assoc]
  have hsplit := sum_split_prime_prior (H := CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)
    (Y := CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n) P
    (Sum.elim (fun h => Q (copyScheduleOrigin n h.val)) (fun y => Q (copyScheduleOrigin n y.val)))
    (fun x => ((∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val))
      (x (.inl (e.symm h))) : ℝ) : ℂ) *
      (constituentCharacterCore role size χ κ pivot n P hP childBound pivotBound ranges leaf hist
        (fun y => x (.inr y)) M ((fun h => x (.inl h)), d) *
      conj (constituentCharacterCore role size χ κ pivot n P hP childBound pivotBound ranges leaf hist
        (fun y => x (.inr y)) M ((fun h => x (.inl (e.symm h))), d'))))
  simp only [finite_univ_canonical, Sum.elim_inl, Sum.elim_inr] at hsplit ⊢
  rw [hsplit]
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [constituentCharacterCoefficient_factor, constituentCharacterCoefficient_factor]
  simp only [Function.comp_apply, map_mul, Complex.conj_ofReal, finite_univ_canonical]
  dsimp only [Function.comp_def]
  ring

theorem constituentMatchingFamily_expand
    (S : Finset (Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n))) (M : ℕ) :
    constituentMatchingFamily role size χ κ pivot n P hP Q childBound pivotBound ranges leaf hist S M =
      ∑ e ∈ S, ∑ d : D, ∑ d' : D, if frequencyRoot n (hist d) = frequencyRoot n (hist d') then
        constituentOriginalMatchedPair role size χ κ pivot n P hP Q childBound pivotBound ranges leaf hist e d d' M
        else 0 := by
  simp_rw [constituentOriginalMatchedPair_eq]
  unfold constituentMatchingFamily primeMatchingContribution
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d' _
  by_cases h : frequencyRoot n (hist d) = frequencyRoot n (hist d')
  · simp only [h, ite_true, if_true, Finset.mul_sum, finite_univ_canonical]
  · simp only [h, ite_false, if_false, mul_zero, Finset.sum_const_zero]

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DiagonalEndpointCancellation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cancelling the external pivot count against the H endpoint product -/

namespace Ostmann
open scoped BigOperators

theorem natInterval_card_le_upper (a b : ℕ) (ha : 0 < a) :
    (Finset.Icc a b).card ≤ b := by
  rw [Nat.card_Icc]
  omega

theorem diagonal_endpoint_cancellation {H : Type*} [Fintype H]
    (a b : ℕ) (ha : 0 < a) (lower : H → ℝ) (hlower : ∀ h, 0 < lower h)
    (gap : ℝ) (hgap : Real.exp gap * (b : ℝ) ≤ ∏ h, lower h) :
    ((Finset.Icc a b).card : ℝ) * (∏ h, lower h)⁻¹ ≤ Real.exp (-gap) := by
  have hprod : 0 < ∏ h, lower h := Finset.prod_pos (fun h _ => hlower h)
  have hc : ((Finset.Icc a b).card : ℝ) ≤ b := by exact_mod_cast natInterval_card_le_upper a b ha
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hprod]
  calc
    _ ≤ (b : ℝ) := hc
    _ ≤ (Real.exp gap)⁻¹ * ∏ h, lower h := by
      have hh := mul_le_mul_of_nonneg_left hgap (inv_nonneg.mpr (Real.exp_pos gap).le)
      simpa only [← mul_assoc, inv_mul_cancel₀ (Real.exp_ne_zero gap), one_mul] using hh

theorem finite_pivot_sum_bound (a b : ℕ) (ha : 0 < a)
    (F : ℕ → ℂ) (A B gap : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (lower : Type*) [Fintype lower] (lo : lower → ℝ) (hlo : ∀ h, 0 < lo h)
    (hgap : Real.exp gap * (b : ℝ) ≤ ∏ h, lo h)
    (hF : ∀ M ∈ Finset.Icc a b, ‖F M‖ ≤ A * (∏ h, lo h)⁻¹ * B) :
    (∑ M ∈ Finset.Icc a b, (F M).re) ≤ Real.exp (-gap) * A * B := by
  calc
    _ ≤ ∑ M ∈ Finset.Icc a b, ‖F M‖ :=
      Finset.sum_le_sum (fun M _ => Complex.re_le_norm (F M))
    _ ≤ ∑ _M ∈ Finset.Icc a b, A * (∏ h, lo h)⁻¹ * B :=
      Finset.sum_le_sum (fun M hM => hF M hM)
    _ = (((Finset.Icc a b).card : ℝ) * (∏ h, lo h)⁻¹) * A * B := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (diagonal_endpoint_cancellation a b ha lo hlo gap hgap) hA) hB

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentMatchingPairSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing matched prime comparisons before counting external pivots -/
namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

section
variable {I D : Type*} [Fintype I] [Fintype D]
variable (role : I → CopyScheduleRole) (size : I → ℕ)
variable (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
variable (Q : (Σ i, Fin (size i)) → Finset ℕ)
variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
variable (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)

theorem constituentMatchingFamily_pair_sum_bound
    (S : Finset (Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)))
    (M : ℕ) (E : ℝ) (hE : 0 ≤ E)
    (hpair : ∀ e ∈ S, ∀ d d', frequencyRoot n (hist d) = frequencyRoot n (hist d') →
      ‖constituentOriginalMatchedPair role size χ κ pivot n P hP Q childBound pivotBound ranges
        leaf hist e d d' M‖ ≤ E) :
    ‖constituentMatchingFamily role size χ κ pivot n P hP Q childBound pivotBound ranges leaf hist S M‖ ≤
      (S.card : ℝ) * (Fintype.card D : ℝ) ^ 2 * E := by
  rw [constituentMatchingFamily_expand]
  calc
    _ ≤ ∑ e ∈ S, ‖∑ d : D, ∑ d' : D, if frequencyRoot n (hist d) = frequencyRoot n (hist d') then
        constituentOriginalMatchedPair role size χ κ pivot n P hP Q childBound pivotBound ranges
          leaf hist e d d' M else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _e ∈ S, (Fintype.card D : ℝ) ^ 2 * E := by
      apply Finset.sum_le_sum
      intro e he
      calc
        _ ≤ ∑ d : D, ∑ d' : D, ‖if frequencyRoot n (hist d) = frequencyRoot n (hist d') then
            constituentOriginalMatchedPair role size χ κ pivot n P hP Q childBound pivotBound ranges
              leaf hist e d d' M else 0‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => norm_sum_le _ _)
        _ ≤ ∑ _d : D, ∑ _d' : D, E := by
          apply Finset.sum_le_sum
          intro d _
          apply Finset.sum_le_sum
          intro d' _
          split_ifs with hr
          · exact hpair e he d d' hr
          · simpa only [norm_zero] using hE
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

end
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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentSupportedPairDecay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original matched pair decays from explicit prime and history bounds -/
namespace Ostmann
universe u
open Filter
open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

/-- The threshold is uniform over the growing constituent coordinate space.
The ranged-character error and the discarded prime guards are both derived
from the stated scalar size bounds. -/
theorem eventual_constituent_supported_pair_decay
    (n : ℕ) (a₀ b₀ d₀ C S H z α₀ β γ c : ℝ)
    (ha₀ : 0 ≤ a₀) (hb₀ : 0 ≤ b₀) (hd₀ : 0 ≤ d₀) (hC : 0 ≤ C) (hS : 1 ≤ S)
    (hH : 0 ≤ H) (hz : 0 ≤ z)
    (hα₀ : 0 < α₀) (hαβ : α₀ < β) (hγβ : γ < β) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (I : Type u) [Fintype I] (role : I → CopyScheduleRole) (size : I → ℕ)
      (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
      (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
      (_hκ : ∀ i p, ‖κ i p‖ ≤ 1)
      (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n))
      (_hχ : ∀ i, χ (copyScheduleOrigin n (e i).val) = χ (copyScheduleOrigin n i.val))
      (childBound pivotBound : ℕ → ℕ)
      (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
      (ψ : 𝓢(ℝ, ℂ)) (_hreal : ∀ y, conj (ψ y) = ψ y)
      (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (_hu : ∀ j ≤ n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b),
    let K := CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n ⊕
      CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n
    let ρ := (fun i : Σ a, Fin (size a) => role (Sigma.fst i))
    let W := insertedConstituentWord role size n
    let W' := fun v => List.map (insertedConstituentPerm role size n e) (W v)
    let G := constituentMatchedGraph role size pivot n e
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
    (_ht' : NonzeroInternalFrequencies n t')
    (B : ℕ) (_hB : 1 ≤ B) (_hwords : (Tpl).WordsBounded B) (_hwords' : (Tpl').WordsBounded B)
    (_hD : (D).WordsBounded B) (_hD' : (D').WordsBounded B)
    (_hU : (U).WordsBounded B) (_hU' : (U').WordsBounded B)
    (_hself : G a a = 0 ∧ G b b = 0) (_hreverse : G b a = 0)
    (P : Finset ℕ) (_hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
    (Q : K → Finset ℕ) (_hQP : ∀ i, Q i ⊆ P)
    (_hQmass : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹)
    (_hnonprincipal : ∀ q ∈ Q a, (scheduledRetainedCharacters ρ χ n) a q ^ G a b ≠ 1)
    (A E : ℕ) (_hA : 0 < A)
    (_hMA : wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B ≤ A)
    (_hsmall : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t, 0 < s.natAbs ∧ s.natAbs < p)
    (_hsmall' : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t', 0 < s.natAbs ∧ s.natAbs < p)
    (_hlow : ∀ p ∈ Q b, 2 * A ≤ p) (_hhigh : ∀ p ∈ Q b, p ≤ E)
    (lower : ℝ) (_hlower : 0 < lower) (_hlowerQ : ∀ q ∈ Q a, lower ≤ (q : ℝ))
    (Bq : ℕ) (_hBq : ∀ q : Q a, (q : ℕ) ≤ Bq)
    (V R : ℝ) (_hV : 0 < V) (_hR : 3 ≤ R) (N : ℕ) (_hN : (N : ℝ) ≤ R)
    (_hlowerP : ∀ p ∈ P, V ≤ Real.log (p : ℝ)) (_hupperP : ∀ p ∈ P, (p : ℝ) ≤ R)
    (_hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
    (_hfreq' : ∀ s ∈ allFrequencyList n t', |(s : ℝ)| ≤ R)
    (_hword : Fintype.card (CopyScheduleH ρ n) + 1 ≤ B)
    (Z : ℝ) (_hZ : 0 < Z) (_hproduct : ConstituentHProductLower role size n childBound pivotBound ranges
      (scheduleFourierLeaf role ψ X lo hi) Z)
    (M : ℝ) (_hm : 0 ≤ M) (_hmL : M ≤ z * L)
    (Vfreq : ℕ) (_hBlinear : (B : ℝ) ≤ b₀ * (1 + M))
    (_hDcount : (((D).prependRoot (originalProductRange ((retainedHWord (CopyScheduleH ρ n) (CopyScheduleY ρ n)).map some) n Z 0)).count : ℝ) ≤ d₀ * (1 + M))
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
      a₀ * (1 + M) ^ 2),
    let leaf := scheduleFourierLeaf role ψ X lo hi
    let core := fun x : K → P => constituentCharacterCore role size χ κ pivot n P hprime
      childBound pivotBound ranges leaf (fun z : FrequencyTree ℤ n => z) (fun y => x (.inr y)) N
    ‖∑ x : K → P, ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
      ((∏ h, primeSubsetPrior P (Q (.inl h)) (x (.inl (e h))) : ℝ) : ℂ) *
      (core x ((fun h => x (.inl h)), t) * conj (core x ((fun h => x (.inl (e h))), t')))‖ ≤
      (∏ h : CopyScheduleH ρ n, (∑ p ∈ Q (.inl h), (p : ℝ)⁻¹)⁻¹) * Z⁻¹ *
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
    a b hab t t' ht ht' B hB hwords hwords' hD hD' hU hU' hself hreverse
    P hP hprime Q hQP hQmass hnonprincipal A E hA hMA hsmall hsmall' hlow hhigh
    lower hlower hlowerQ Bq hBq V R hV hR N hN hlowerP hupperP hfreq hfreq'
    hword Z hZ hproduct M hm hmL Vfreq hBlinear hDcount hD'count hVfreq hfv hfv' hs₀ hs₁ hwidth hE hQinv
    hshort hlong hBqscale hmin hratio hprimecount hcheckcount leaf core
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
    ((D).prependRoot (originalProductRange ((retainedHWord (CopyScheduleH ρ n) (CopyScheduleY ρ n)).map some) n Z 0)) D'
    t t' ht ht' B Vfreq A E FP FP (Q b) (Q a) lower Bq M
    hm hmL hBlinear hDcount hD'count hVfreq hfv hfv'
    hs₀ hs₁ hs₀ hs₁ hwidth hwidth hE (hQinv b) (hQinv a) hshort hlong hBqscale
  have hold := constituent_signed_supported_pair_bound role size n χ κ pivot hκ e hχ
    childBound pivotBound ranges ψ hreal X lo hi hlo hhi hu a b hab t t' ht ht'
    B hB hwords hwords' hD hD' hU hU' hself hreverse P hP hprime Q hQP hQmass hnonprincipal
    A E hA hMA hsmall hsmall' hlow hhigh lower hlower hlowerQ Bq hBq atom V R
    (Real.exp_nonneg _) hV hR N hN hmax hlowerP hupperP hfreq hfreq'
    hword Z hZ hproduct δ (Real.exp_nonneg _) hnum
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
  have hh := hsupport M δ loss δ (δ + loss * δ) hm hmL hloss hcost le_rfl hδ le_rfl
  have hbound : δ + loss * (atom + Real.log R / V * atom) ≤
      Real.exp (-(c / 32) * Real.exp (α₀ * L)) := by
    apply hsum.trans
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  exact hold.trans (mul_le_mul_of_nonneg_left hbound (by positivity))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentSupportedPairSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing matched prime comparisons before counting external pivots -/
namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

section
variable {I D : Type*} [Fintype I] [Fintype D]
variable (role : I → CopyScheduleRole) (size : I → ℕ)
variable (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
variable (Q : (Σ i, Fin (size i)) → Finset ℕ)
variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
variable (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)

theorem constituentMatchingFamily_interval_pair_product
    (S : Finset (Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)))
    (a b : ℕ) (ha : 0 < a) (gap E : ℝ) (hE : 0 ≤ E)
    (productLower : ℝ) (hpositive : 0 < productLower)
    (hgap : Real.exp gap * (b : ℝ) ≤ productLower)
    (hpair : ∀ M ∈ Finset.Icc a b, ∀ e ∈ S, ∀ d d',
      frequencyRoot n (hist d) = frequencyRoot n (hist d') →
      ‖constituentOriginalMatchedPair role size χ κ pivot n P hP Q childBound pivotBound ranges
        leaf hist e d d' M‖ ≤
        (∏ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
          (∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)⁻¹) * productLower⁻¹ * E) :
    (∑ M ∈ Finset.Icc a b,
      (constituentMatchingFamily role size χ κ pivot n P hP Q childBound pivotBound ranges leaf hist S M).re) ≤
      Real.exp (-gap) * ((S.card : ℝ) * (Fintype.card D : ℝ) ^ 2 *
        (∏ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
          (∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)⁻¹)) * E := by
  let Z : ℝ := ∏ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
    (∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)⁻¹
  have hZ : 0 ≤ Z := Finset.prod_nonneg fun _ _ => by positivity
  have hlo : 0 ≤ productLower⁻¹ := inv_nonneg.mpr hpositive.le
  apply finite_pivot_sum_bound a b ha _ ((S.card : ℝ) * (Fintype.card D : ℝ) ^ 2 * Z)
    E gap (by positivity) hE Unit (fun _ => productLower) (fun _ => hpositive) (by simpa using hgap)
  intro M hM
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_unit, pow_one]
  calc
    _ ≤ (S.card : ℝ) * (Fintype.card D : ℝ) ^ 2 * (Z * productLower⁻¹ * E) :=
      constituentMatchingFamily_pair_sum_bound role size χ κ pivot n P hP Q childBound pivotBound
        ranges leaf hist S M _ (mul_nonneg (mul_nonneg hZ hlo) hE) (hpair M hM)
    _ = _ := by ring

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FinalPairPeriodScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The final history pair's actual modulus fits below the long-prime scale -/
namespace Ostmann
open Filter

theorem eventual_final_pair_period_scale (n : ℕ) (b C z β : ℝ)
    (hb : 0 ≤ b) (hC : 0 ≤ C) (hz : 0 ≤ z) (hβ : 0 < β) :
    ∀ᶠ L : ℝ in atTop, ∀ (m : ℝ) (B V A : ℕ) (t t' : FrequencyTree ℤ n),
      0 ≤ m → m ≤ z * L → (B : ℝ) ≤ b * (1 + m) →
      (V : ℝ) ≤ Real.exp (C * (1 + m)) →
      (∀ s ∈ allFrequencyList n t, s.natAbs ≤ V) →
      (∀ s ∈ allFrequencyList n t', s.natAbs ≤ V) →
      Real.exp (Real.exp (β * L)) ≤ (A : ℝ) →
      wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B ≤ A := by
  have hK : 0 ≤ 2 * C * wordPeriodExponent n b := by
    unfold wordPeriodExponent
    positivity
  filter_upwards [eventual_polynomial_log_budget (2 * C * wordPeriodExponent n b)
    z β 1 (n + 2) hK hz hβ zero_lt_one] with L hL m B V A t t' hm hmL hB hV hf hf' hA
  have hleft := wordTransferFullPeriod_le_exp n t B V b C m hC hm hB hV hf
  have hright := wordTransferFullPeriod_le_exp n t' B V b C m hC hm hB hV hf'
  have hprod : ((wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B : ℕ) : ℝ) ≤
      Real.exp (2 * C * wordPeriodExponent n b * (1 + m) ^ (n + 2)) := by
    push_cast
    calc
      _ ≤ Real.exp (C * wordPeriodExponent n b * (1 + m) ^ (n + 2)) *
          Real.exp (C * wordPeriodExponent n b * (1 + m) ^ (n + 2)) :=
        mul_le_mul hleft hright (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have he := hL m hm hmL
  simp only [one_mul] at he
  exact_mod_cast hprod.trans ((Real.exp_le_exp.mpr he).trans hA)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentSupportedSizeDecay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The matched original-prior comparison with its actual finite costs -/
namespace Ostmann
universe u
open Filter
open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

theorem eventual_constituent_supported_pair_from_sizes {I : Type u} [Fintype I]
    (role : I → CopyScheduleRole) (n Aw Kr : ℕ) (s C S H z α₀ β γ c : ℝ)
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hS : 1 ≤ S) (hH : 0 ≤ H) (hz : 0 ≤ z)
    (hα₀ : 0 < α₀) (hαβ : α₀ < β) (hγβ : γ < β) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ (size : I → ℕ) (Smax : ℕ)
      (_hSmax : 1 ≤ Smax) (_hsize : ∀ i, size i ≤ Smax)
      (M : ℝ) (_hm : 0 ≤ M) (_hmL : M ≤ z * L) (_hSm : (Smax : ℝ) ≤ s * (1 + M))
      (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
      (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
      (_hκ : ∀ i p, ‖κ i p‖ ≤ 1)
      (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n))
      (_hχ : ∀ i, χ (copyScheduleOrigin n (e i).val) = χ (copyScheduleOrigin n i.val))
      (childBound pivotBound : ℕ → ℕ)
      (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
      (_hrange : ∀ j ≤ n, ∀ r ∈ ranges j, r.atoms.length ≤ Aw)
      (_hcount : ∀ j ≤ n, (ranges j).length ≤ Kr)
      (ψ : 𝓢(ℝ, ℂ)) (_hreal : ∀ y, conj (ψ y) = ψ y)
      (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (_hu : ∀ j ≤ n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b),
    let K := CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n ⊕
      CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n
    let ρ := (fun i : Σ a, Fin (size a) => role (Sigma.fst i))
    let G := constituentMatchedGraph role size pivot n e
    let FP := WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi
    ∀
    (a b : K) (_hab : a ≠ b)
    (t t' : FrequencyTree ℤ n) (_ht : NonzeroInternalFrequencies n t)
    (_ht' : NonzeroInternalFrequencies n t')
    (_hself : G a a = 0 ∧ G b b = 0) (_hreverse : G b a = 0)
    (P : Finset ℕ) (_hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
    (Q : K → Finset ℕ) (_hQP : ∀ i, Q i ⊆ P)
    (_hQmass : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹)
    (_hnonprincipal : ∀ q ∈ Q a, (scheduledRetainedCharacters ρ χ n) a q ^ G a b ≠ 1)
    (A E : ℕ) (_hA : 0 < A)
    (_hsmall : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t, 0 < s.natAbs ∧ s.natAbs < p)
    (_hsmall' : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t', 0 < s.natAbs ∧ s.natAbs < p)
    (_hlow : ∀ p ∈ Q b, 2 * A ≤ p) (_hhigh : ∀ p ∈ Q b, p ≤ E)
    (lower : ℝ) (_hlower : 0 < lower) (_hlowerQ : ∀ q ∈ Q a, lower ≤ (q : ℝ))
    (Bq : ℕ) (_hBq : ∀ q : Q a, (q : ℕ) ≤ Bq)
    (V R : ℝ) (_hV : 0 < V) (_hR : 3 ≤ R) (N : ℕ) (_hN : (N : ℝ) ≤ R)
    (_hlowerP : ∀ p ∈ P, V ≤ Real.log (p : ℝ)) (_hupperP : ∀ p ∈ P, (p : ℝ) ≤ R)
    (_hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
    (_hfreq' : ∀ s ∈ allFrequencyList n t', |(s : ℝ)| ≤ R)
    (Z : ℝ) (_hZ : 0 < Z) (_hproduct : ConstituentHProductLower role size n childBound pivotBound ranges
      (scheduleFourierLeaf role ψ X lo hi) Z)
    (Vfreq : ℕ)
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
    (_hratio : Real.log R / V ≤ Real.exp (H * (1 + M))),
    let leaf := scheduleFourierLeaf role ψ X lo hi
    let core := fun x : K → P => constituentCharacterCore role size χ κ pivot n P hprime
      childBound pivotBound ranges leaf (fun z : FrequencyTree ℤ n => z) (fun y => x (.inr y)) N
    ‖∑ x : K → P, ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
      ((∏ h, primeSubsetPrior P (Q (.inl h)) (x (.inl (e h))) : ℝ) : ℂ) *
      (core x ((fun h => x (.inl h)), t) * conj (core x ((fun h => x (.inl (e h))), t')))‖ ≤
      (∏ h : CopyScheduleH ρ n, (∑ p ∈ Q (.inl h), (p : ℝ)⁻¹)⁻¹) * Z⁻¹ *
        Real.exp (-(c / 32) * Real.exp (α₀ * L)) := by
  let a₀ := constituentFinalCountRate (Fintype.card I) n s
  let b₀ := (((2 * 3 ^ n * Fintype.card I + Aw : ℕ) : ℝ) * s + 4)
  let d₀ : ℝ := (Kr * (2 ^ (n + 1) - 1) + 1 : ℕ)
  have ha₀ : 0 ≤ a₀ := constituentFinalCountRate_nonneg _ _ _ hs
  have hb₀ : 0 ≤ b₀ := by dsimp [b₀]; positivity
  have hd₀ : 0 ≤ d₀ := by dsimp [d₀]; positivity
  filter_upwards [eventual_constituent_supported_pair_decay n a₀ b₀ d₀ C S H z α₀ β γ c
      ha₀ hb₀ hd₀ hC hS hH hz hα₀ hαβ hγβ hc,
    eventual_final_pair_period_scale n b₀ C z β hb₀ hC hz (hα₀.trans hαβ)]
    with L hdec hperiod
  intro size Smax hSmax hsize M hm hmL hSm χ κ pivot hκ e hχ childBound pivotBound ranges
    hrange hcount ψ hreal X lo hi hlo hhi hu K ρ G FP
    a b hab t t' ht ht' hself hreverse P hP hprime Q hQP hQmass hnonprincipal
    A E hA hsmall hsmall' hlow hhigh lower hlower hlowerQ Bq hBq
    V R hV hR N hN hlowerP hupperP hfreq hfreq' Z hZ hproduct
    Vfreq hVfreq hfv hfv' hs₀ hs₁ hwidth hE hQinv hshort hlong hBqscale hmin hratio leaf core
  let W := insertedConstituentWord role size n
  let W' := fun v => List.map (insertedConstituentPerm role size n e) (W v)
  let B := 2 * 3 ^ n * Fintype.card I * Smax + Aw * Smax + 4
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hBlinear : (B : ℝ) ≤ b₀ * (1 + M) :=
    constituent_word_budget_linear n Aw Smax s M hSm hm
  obtain ⟨hw, hw', hD, hD', hU, hU'⟩ :=
    constituent_pair_word_bounds role size n e childBound pivotBound ranges
      Smax Aw hSmax hsize hrange
  have hcounts := constituent_matched_linear_counts role size n e Smax s M
    hSmax hsize hs hm hSm
  have hranges := expandedRootRanges_pair_linear_count role n Kr W W' ranges hcount
    (originalProductRange ((retainedHWord (CopyScheduleH ρ n) (CopyScheduleY ρ n)).map some) n Z 0) M hm
  have hMA := hperiod M B Vfreq A t t' hm hmL hBlinear hVfreq hfv hfv' hlong
  have hword := constituent_retained_word_bound role size n Smax Aw hsize
  exact hdec I role size χ κ pivot hκ e hχ childBound pivotBound ranges ψ hreal X lo hi hlo hhi hu
    a b hab t t' ht ht' B hB hw hw' hD hD' hU hU' hself hreverse P hP hprime Q hQP hQmass
    hnonprincipal A E hA hMA hsmall hsmall' hlow hhigh lower hlower hlowerQ Bq hBq V R hV hR
    N hN hlowerP hupperP hfreq hfreq' hword Z hZ hproduct
    M hm hmL Vfreq hBlinear hranges.1 hranges.2 hVfreq hfv hfv' hs₀ hs₁ hwidth hE hQinv
    hshort hlong hBqscale hmin hratio hcounts.1 hcounts.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledMatchedCodeSplit
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Both parity cases for the actual code-changing matching -/
namespace Ostmann
open scoped Classical

/-- A changed code chooses either the small-anchor-to-word character or the
word-to-large-anchor character. The same computed graph is used in both cases. -/
theorem scheduledMatchedGraph_changed_code_split {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n : ℕ) (e : Equiv.Perm (CopyScheduleH role (n + 1)))
    (small large : Fin (n + 1) → I)
    (hsmall : ∀ j, role (small j) = .anchor j) (hlarge : ∀ j, role (large j) = .anchor j)
    (hp : ∀ k < n + 1, role (pivot k) = .pivot k)
    (i i' : I) (hi : role i = .word) (hi' : role i' = .word)
    (t t' : Fin (n + 1) → Bool) (h : CopyScheduleH role (n + 1))
    (hh : h.val = copySchedulePath (n + 1) t i)
    (hh' : (e.symm h).val = copySchedulePath (n + 1) t' i')
    (hcode : finiteAnchorCode (fun _ => 1) t ≠ finiteAnchorCode (fun _ => 1) t') :
    ∃ (j : Fin (n + 1)) (b : Bool),
      let a := scheduledPastAnchor role n (small j) j (hsmall j) b
      let a' := scheduledPastAnchor role n (large j) j (hlarge j) b
      let G := scheduledMatchedGraph role pivot (n + 1) e
      ((G (.inr a) (.inl h) = 2 ∨ G (.inr a) (.inl h) = -2) ∧ G (.inl h) (.inr a) = 0) ∨
      ((G (.inl h) (.inr a') = 2 ∨ G (.inl h) (.inr a') = -2) ∧ G (.inr a') (.inl h) = 0) := by
  obtain ⟨j, b, hj⟩ := distinct_anchor_code_entry (fun _ => 1) t t' hcode
  have hs (u : Fin (n + 1) → Bool) : finalCopyParity u = 1 ∨ finalCopyParity u = -1 :=
    copyPathParity_sign (finiteCopyPath u) (n + 1)
  have hsign (u : Fin (n + 1) → Bool) :
      anchorCodeEntry (fun _ => 1) u j b = 1 ∨ anchorCodeEntry (fun _ => 1) u j b = -1 :=
    anchorCodeEntry_sign (fun _ => 1) (fun _ => Or.inl rfl) u j b
  have hsep (a : I) (ha : role a = .anchor j) :
      (∀ k < n + 1, a ≠ pivot k) ∧ a ≠ i ∧ a ≠ i' := by
    constructor
    · intro k hk he
      have he' := congrArg role he
      rw [ha, hp k hk] at he'
      cases he'
    · constructor
      · intro he
        have he' := congrArg role he
        rw [ha, hi] at he'
        cases he'
      · intro he
        have he' := congrArg role he
        rw [ha, hi'] at he'
        cases he'
  have hip : ∀ k < n + 1, i ≠ pivot k := by
    intro k hk he
    have he' := congrArg role he
    rw [hi, hp k hk] at he'
    cases he'
  have hi'p : ∀ k < n + 1, i' ≠ pivot k := by
    intro k hk he
    have he' := congrArg role he
    rw [hi', hp k hk] at he'
    cases he'
  have hsf := scheduledMatchedGraph_anchor_word role pivot n e (small j) i i' j (hsmall j) b
    (hsep _ (hsmall j)).1 (hsep _ (hsmall j)).2.1 (hsep _ (hsmall j)).2.2 t t' h hh hh'
  have hsr := scheduledMatchedGraph_word_anchor role pivot n e (small j) i i' j (hsmall j) b
    hip hi'p (hsep _ (hsmall j)).2.1.symm (hsep _ (hsmall j)).2.2.symm t t' h hh hh'
  have hlf := scheduledMatchedGraph_anchor_word role pivot n e (large j) i i' j (hlarge j) b
    (hsep _ (hlarge j)).1 (hsep _ (hlarge j)).2.1 (hsep _ (hlarge j)).2.2 t t' h hh hh'
  have hlr := scheduledMatchedGraph_word_anchor role pivot n e (large j) i i' j (hlarge j) b
    hip hi'p (hsep _ (hlarge j)).2.1.symm (hsep _ (hlarge j)).2.2.symm t t' h hh hh'
  refine ⟨j, b, ?_⟩
  dsimp only
  rcases changed_anchor_code_one_sided _ _ _ _ (hs t) (hs t') (hsign t) (hsign t') hj with hf | hr
  · apply Or.inl
    rw [hsf, hsr]
    exact hf
  · apply Or.inr
    rw [hlr, hlf]
    exact ⟨hr.2, hr.1⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledTreeBulkCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The counted bulk slots are the actual recursive arithmetic leaves -/

namespace Ostmann
open scoped Classical

theorem separatedMatchingLeft_apply {A B : Type*}
    (e : PartitionMatching (@sumSide A B) (@sumSide A B)) (a : A) :
    e.val (.inl a) = .inl (separatedMatchingLeft e a) := by
  have h := congrArg Subtype.val ((sumSideLeftEquiv A B).apply_symm_apply
    ((e.restrict true) (sumSideLeftEquiv A B a)))
  change Sum.inl (separatedMatchingLeft e a) = e.val (.inl a) at h
  exact h.symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedBulkCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bulk coordinates inside a larger word

The selected bulk slots are copied with the whole word. The top slot is
retained in that word but belongs to the complementary matching block.
-/
namespace Ostmann
open scoped Classical

theorem selectedBulkMatching_slot {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : PartitionMatching (selectedBulkLabel role n m bulk hbulk)
      (selectedBulkLabel role n m bulk hbulk)) (x : Fin (2 ^ n) × Fin m) :
    e.val (selectedBulkH role n m bulk hbulk x) =
      selectedBulkH role n m bulk hbulk
        (separatedMatchingLeft (selectedSeparatedMatching role n m bulk hbulk e) x) := by
  have h := congrArg (selectedSplitHCoordinates role n m bulk hbulk)
    (separatedMatchingLeft_apply (selectedSeparatedMatching role n m bulk hbulk e) x)
  simpa only [selectedSeparatedMatching, Equiv.trans_apply, Equiv.apply_symm_apply,
    selectedSplitHCoordinates_inl] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedAnchorSymmetry
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Inversion preserves the actual anchor-code matching family -/
namespace Ostmann
open scoped Classical

theorem selectedAnchorMatchingSet_symm {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : Equiv.Perm (CopyScheduleH role n))
    (he : e ∈ selectedAnchorMatchingSet role n m bulk hbulk) :
    e.symm ∈ selectedAnchorMatchingSet role n m bulk hbulk := by
  obtain ⟨hl, hc⟩ := (mem_selectedAnchorMatchingSet role n m bulk hbulk e).mp he
  have hl' : ∀ h, selectedBulkLabel role n m bulk hbulk (e.symm h) = selectedBulkLabel role n m bulk hbulk h := by
    intro h
    simpa only [e.apply_symm_apply] using (hl (e.symm h)).symm
  apply (mem_selectedAnchorMatchingSet role n m bulk hbulk e.symm).mpr
  refine ⟨hl', ?_⟩
  let f := separatedMatchingLeft (selectedSeparatedMatching role n m bulk hbulk ⟨e, hl⟩)
  let f' := separatedMatchingLeft (selectedSeparatedMatching role n m bulk hbulk ⟨e.symm, hl'⟩)
  intro x
  have hinv : f (f' x) = x := by
    apply (selectedBulkCoordinates role n m bulk hbulk).injective
    apply Subtype.ext
    have h := selectedBulkMatching_slot role n m bulk hbulk ⟨e, hl⟩ (f' x)
    have h' := selectedBulkMatching_slot role n m bulk hbulk ⟨e.symm, hl'⟩ x
    change e ((selectedBulkCoordinates role n m bulk hbulk (f' x)).val) =
      (selectedBulkCoordinates role n m bulk hbulk (f (f' x))).val at h
    change e.symm ((selectedBulkCoordinates role n m bulk hbulk x).val) =
      (selectedBulkCoordinates role n m bulk hbulk (f' x)).val at h'
    rw [← h', e.apply_symm_apply] at h
    exact h.symm
  have h := hc (f' x)
  change scheduledBulkAnchorCode n (f (f' x)) = scheduledBulkAnchorCode n (f' x) at h
  rw [hinv] at h
  exact h.symm

theorem selected_nonanchor_symm {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : Equiv.Perm (CopyScheduleH role n))
    (he : e ∈ cellPreservingMatchings (selectedBulkLabel role n m bulk hbulk) \
      selectedAnchorMatchingSet role n m bulk hbulk) :
    e.symm ∈ cellPreservingMatchings (selectedBulkLabel role n m bulk hbulk) \
      selectedAnchorMatchingSet role n m bulk hbulk := by
  obtain ⟨hl, hn⟩ := Finset.mem_sdiff.mp he
  apply Finset.mem_sdiff.mpr
  constructor
  · apply (mem_cellPreservingMatchings _ _).mpr
    intro h
    have hx := ((mem_cellPreservingMatchings _ _).mp hl) (e.symm h)
    simpa only [e.apply_symm_apply] using hx.symm
  · intro h
    exact hn (by simpa only [Equiv.symm_symm] using selectedAnchorMatchingSet_symm role n m bulk hbulk e.symm h)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedNonanchorWitness
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One-sided interactions at the actual selected bulk primes -/
namespace Ostmann
open scoped Classical

theorem scheduled_matched_code_prime_ranges_at {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n : ℕ) (e : Equiv.Perm (CopyScheduleH role (n + 1)))
    (small large : Fin (n + 1) → I)
    (hsmall : ∀ j, role (small j) = .anchor j) (hlarge : ∀ j, role (large j) = .anchor j)
    (hp : ∀ k < n + 1, role (pivot k) = .pivot k)
    (i i' : I) (hi : role i = .word) (hi' : role i' = .word)
    (t t' : Fin (n + 1) → Bool) (h : CopyScheduleH role (n + 1))
    (hh : h.val = copySchedulePath (n + 1) t i)
    (hh' : (e.symm h).val = copySchedulePath (n + 1) t' i')
    (hcode : finiteAnchorCode (fun _ => 1) t ≠ finiteAnchorCode (fun _ => 1) t')
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p) (Q₀ : I → Finset ℕ)
    (hχsmall : ∀ j q, q ∈ Q₀ (small j) → χ (small j) q ^ 2 ≠ 1)
    (hχword : ∀ q ∈ Q₀ i, χ i q ^ 2 ≠ 1)
    (ℓs ℓw : ℝ) (Bs Bw Aw Ew Aa Ea : ℕ)
    (hsmallrange : ∀ j q, q ∈ Q₀ (small j) → ℓs ≤ (q : ℝ) ∧ q ≤ Bs)
    (hwordrange : ∀ p ∈ Q₀ i,
      (ℓw ≤ (p : ℝ) ∧ p ≤ Bw) ∧ (2 * Aw ≤ p ∧ p ≤ Ew))
    (hlargerange : ∀ j p, p ∈ Q₀ (large j) → 2 * Aa ≤ p ∧ p ≤ Ea) :
    let χR := scheduledRetainedCharacters role χ (n + 1)
    let Q := Sum.elim (fun h : CopyScheduleH role (n + 1) => Q₀ (copyScheduleOrigin (n + 1) h.val))
      (fun y : CopyScheduleY role (n + 1) => Q₀ (copyScheduleOrigin (n + 1) y.val))
    let G := scheduledMatchedGraph role pivot (n + 1) e
    ∃ a b : CopyScheduleH role (n + 1) ⊕ CopyScheduleY role (n + 1),
      a ≠ b ∧ (G a a = 0 ∧ G b b = 0) ∧ G b a = 0 ∧
      (∀ q ∈ Q a, χR a q ^ G a b ≠ 1) ∧
      (((∀ q ∈ Q a, ℓs ≤ (q : ℝ) ∧ q ≤ Bs) ∧ (∀ p ∈ Q b, 2 * Aw ≤ p ∧ p ≤ Ew)) ∨
       ((∀ q ∈ Q a, ℓw ≤ (q : ℝ) ∧ q ≤ Bw) ∧ (∀ p ∈ Q b, 2 * Aa ≤ p ∧ p ≤ Ea))) := by
  intro χR Q G
  obtain ⟨j, sign, hedge⟩ := scheduledMatchedGraph_changed_code_split role pivot n e small large
    hsmall hlarge hp i i' hi hi' t t' h hh hh' hcode
  let a := scheduledPastAnchor role n (small j) j (hsmall j) sign
  let a' := scheduledPastAnchor role n (large j) j (hlarge j) sign
  have hwo : copyScheduleOrigin (n + 1) h.val = i := by rw [hh, copyScheduleOrigin_path]
  have hQs : Q (.inr a) = Q₀ (small j) := by
    change Q₀ (copyScheduleOrigin (n + 1) (copyScheduleAnchor (n + 1) j sign (small j))) = _
    rw [copyScheduleOrigin_anchor]
  have hQa : Q (.inr a') = Q₀ (large j) := by
    change Q₀ (copyScheduleOrigin (n + 1) (copyScheduleAnchor (n + 1) j sign (large j))) = _
    rw [copyScheduleOrigin_anchor]
  have hQw : Q (.inl h) = Q₀ i := by change Q₀ (copyScheduleOrigin (n + 1) h.val) = _; rw [hwo]
  have hχs : χR (.inr a) = χ (small j) := by
    change χ (copyScheduleOrigin (n + 1) (copyScheduleAnchor (n + 1) j sign (small j))) = _
    rw [copyScheduleOrigin_anchor]
  have hχw : χR (.inl h) = χ i := by change χ (copyScheduleOrigin (n + 1) h.val) = _; rw [hwo]
  rcases hedge with hedge | hedge
  · refine ⟨.inr a, .inl h, by simp, ⟨scheduledMatchedGraph_self _ _ _ _ _,
        scheduledMatchedGraph_self _ _ _ _ _⟩, hedge.2, ?_, Or.inl ?_⟩
    · intro q hq
      rw [hχs]
      exact signed_square_nonprincipal _ (hχsmall j q (hQs ▸ hq)) _ hedge.1
    · constructor
      · rw [hQs]
        exact hsmallrange j
      · rw [hQw]
        exact fun p hp => (hwordrange p hp).2
  · refine ⟨.inl h, .inr a', by simp, ⟨scheduledMatchedGraph_self _ _ _ _ _,
        scheduledMatchedGraph_self _ _ _ _ _⟩, hedge.2, ?_, Or.inr ?_⟩
    · intro q hq
      rw [hχw]
      exact signed_square_nonprincipal _ (hχword q (hQw ▸ hq)) _ hedge.1
    · constructor
      · rw [hQw]
        exact fun p hp => (hwordrange p hp).1
      · rw [hQa]
        exact hlargerange j

theorem selected_nonanchor_matching_witness {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : Equiv.Perm (CopyScheduleH role n))
    (he : e ∈ cellPreservingMatchings (selectedBulkLabel role n m bulk hbulk) \
      selectedAnchorMatchingSet role n m bulk hbulk) :
    ∃ (i i' : Fin m) (t t' : Fin n → Bool) (h : CopyScheduleH role n),
      h.val = copySchedulePath n t (bulk i) ∧
      (e.symm h).val = copySchedulePath n t' (bulk i') ∧
      finiteAnchorCode (fun _ => 1) t ≠ finiteAnchorCode (fun _ => 1) t' := by
  obtain ⟨hlabel, hn⟩ := Finset.mem_sdiff.mp he
  have hl := (mem_cellPreservingMatchings _ _).mp hlabel
  let e₀ : PartitionMatching (selectedBulkLabel role n m bulk hbulk)
      (selectedBulkLabel role n m bulk hbulk) := ⟨e, hl⟩
  have hncode : ¬ PreservesSelectedAnchorCode role n m bulk hbulk e₀ := by
    intro hc
    exact hn ((mem_selectedAnchorMatchingSet role n m bulk hbulk e).mpr ⟨hl, hc⟩)
  obtain ⟨x, hx⟩ := not_forall.mp hncode
  let f := separatedMatchingLeft (selectedSeparatedMatching role n m bulk hbulk e₀)
  let h := selectedBulkH role n m bulk hbulk (f x)
  have heh : e.symm h = selectedBulkH role n m bulk hbulk x := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (selectedBulkMatching_slot role n m bulk hbulk e₀ x).symm
  refine ⟨(f x).2, x.2, scheduledPathEnumeration n (f x).1,
    scheduledPathEnumeration n x.1, h, rfl, ?_, hx⟩
  rw [heh]
  rfl

/-- The only word-prime range used is that of the selected bulk embedding.
In particular no separation premise is imposed on the top label. -/
theorem selected_nonanchor_prime_ranges {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (pivot : ℕ → I) (n m : ℕ)
    (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : Equiv.Perm (CopyScheduleH role (n + 1)))
    (he : e ∈ cellPreservingMatchings (selectedBulkLabel role (n + 1) m bulk hbulk) \
      selectedAnchorMatchingSet role (n + 1) m bulk hbulk)
    (small large : Fin (n + 1) → I)
    (hsmall : ∀ j, role (small j) = .anchor j) (hlarge : ∀ j, role (large j) = .anchor j)
    (hp : ∀ k < n + 1, role (pivot k) = .pivot k)
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p) (Q₀ : I → Finset ℕ)
    (hχsmall : ∀ j q, q ∈ Q₀ (small j) → χ (small j) q ^ 2 ≠ 1)
    (hχbulk : ∀ i q, q ∈ Q₀ (bulk i) → χ (bulk i) q ^ 2 ≠ 1)
    (ℓs ℓw : ℝ) (Bs Bw Aw Ew Aa Ea : ℕ)
    (hsmallrange : ∀ j q, q ∈ Q₀ (small j) → ℓs ≤ (q : ℝ) ∧ q ≤ Bs)
    (hbulkrange : ∀ i p, p ∈ Q₀ (bulk i) →
      (ℓw ≤ (p : ℝ) ∧ p ≤ Bw) ∧ (2 * Aw ≤ p ∧ p ≤ Ew))
    (hlargerange : ∀ j p, p ∈ Q₀ (large j) → 2 * Aa ≤ p ∧ p ≤ Ea) :
    let χR := scheduledRetainedCharacters role χ (n + 1)
    let Q := Sum.elim (fun h : CopyScheduleH role (n + 1) => Q₀ (copyScheduleOrigin (n + 1) h.val))
      (fun y : CopyScheduleY role (n + 1) => Q₀ (copyScheduleOrigin (n + 1) y.val))
    let G := scheduledMatchedGraph role pivot (n + 1) e
    ∃ a b : CopyScheduleH role (n + 1) ⊕ CopyScheduleY role (n + 1),
      a ≠ b ∧ (G a a = 0 ∧ G b b = 0) ∧ G b a = 0 ∧
      (∀ q ∈ Q a, χR a q ^ G a b ≠ 1) ∧
      (((∀ q ∈ Q a, ℓs ≤ (q : ℝ) ∧ q ≤ Bs) ∧ (∀ p ∈ Q b, 2 * Aw ≤ p ∧ p ≤ Ew)) ∨
       ((∀ q ∈ Q a, ℓw ≤ (q : ℝ) ∧ q ≤ Bw) ∧ (∀ p ∈ Q b, 2 * Aa ≤ p ∧ p ≤ Ea))) := by
  obtain ⟨i, i', t, t', h, hh, hh', hc⟩ :=
    selected_nonanchor_matching_witness role (n + 1) m bulk hbulk e he
  exact scheduled_matched_code_prime_ranges_at role pivot n e small large hsmall hlarge hp
    (bulk i) (bulk i') (hbulk i) (hbulk i') t t' h hh hh' hc χ Q₀ hχsmall (hχbulk i)
    ℓs ℓw Bs Bw Aw Ew Aa Ea hsmallrange (hbulkrange i) hlargerange

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedSupportedPairDecay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Code-changing diagonal pairs with the actual varying-cutoff histories -/
namespace Ostmann
universe u
open Filter
open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

theorem eventual_selected_supported_pair_decay {I : Type u} [Fintype I]
    (role : I → CopyScheduleRole) (n Ar Kr : ℕ)
    (s C S H z α βw γs βa γw c : ℝ)
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hS : 1 ≤ S) (hH : 0 ≤ H) (hz : 0 ≤ z)
    (hα : 0 < α) (hαw : α < βw) (hsw : γs < βw)
    (hαa : α < βa) (hwa : γw < βa) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ (size : I → ℕ) (Smax : ℕ)
      (_hSmax : 1 ≤ Smax) (_hsize : ∀ i, size i ≤ Smax)
      (M : ℝ) (_hm : 0 ≤ M) (_hmL : M ≤ z * L) (_hSm : (Smax : ℝ) ≤ s * (1 + M))
      (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
      (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
      (_hκ : ∀ i p, ‖κ i p‖ ≤ 1)
      (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) (n + 1)))
      (_hχ : ∀ i, χ (copyScheduleOrigin (n + 1) (e i).val) = χ (copyScheduleOrigin (n + 1) i.val))
      (childBound pivotBound : ℕ → ℕ)
      (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
      (_hrange : ∀ j ≤ n + 1, ∀ r ∈ ranges j, r.atoms.length ≤ Ar)
      (_hcount : ∀ j ≤ n + 1, (ranges j).length ≤ Kr)
      (ψ : 𝓢(ℝ, ℂ)) (_hreal : ∀ y, conj (ψ y) = ψ y)
      (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (_hX : 0 < X) (_hXlo : 1 < X * lo)
      (_hu : ∀ j ≤ n + 1, ∀ a b, role a = .pivot j → role b = .pivot j → a = b),
    let ρ := fun i : Σ a, Fin (size a) => role i.1
    let K := CopyScheduleH ρ (n + 1) ⊕ CopyScheduleY ρ (n + 1)
    let FP := WordFourierParameters.uniform (n + 1) (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi
    ∀ (m : ℕ) (bulk : Fin m ↪ (Σ a, Fin (size a))) (hbulk : ∀ i, ρ (bulk i) = .word)
      (_he : e ∈ cellPreservingMatchings (selectedBulkLabel ρ (n + 1) m bulk hbulk) \
        selectedAnchorMatchingSet ρ (n + 1) m bulk hbulk)
      (small large : Fin (n + 1) → (Σ a, Fin (size a)))
      (_hsmall : ∀ j, ρ (small j) = .anchor j) (_hlarge : ∀ j, ρ (large j) = .anchor j)
      (_hp : ∀ j < n + 1, ρ (pivot j) = .pivot j)
      (P : Finset ℕ) (_hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
      (Q₀ : (Σ i, Fin (size i)) → Finset ℕ) (_hQP : ∀ i, Q₀ i ⊆ P)
      (_hQmass : ∀ i, 0 < ∑ q ∈ Q₀ i, (q : ℝ)⁻¹)
      (_hχsmall : ∀ j q, q ∈ Q₀ (small j) → χ (small j) q ^ 2 ≠ 1)
      (_hχword : ∀ i q, q ∈ Q₀ (bulk i) → χ (bulk i) q ^ 2 ≠ 1)
      (ℓs ℓw : ℝ) (_hℓs : 0 < ℓs) (_hℓw : 0 < ℓw) (Bs Bw Aw Ew Aa Ea : ℕ)
      (_hAw : 0 < Aw) (_hAa : 0 < Aa)
      (_hsmallrange : ∀ j q, q ∈ Q₀ (small j) → ℓs ≤ (q : ℝ) ∧ q ≤ Bs)
      (_hwordrange : ∀ i p, p ∈ Q₀ (bulk i) →
        (ℓw ≤ (p : ℝ) ∧ p ≤ Bw) ∧ (2 * Aw ≤ p ∧ p ≤ Ew))
      (_hlargerange : ∀ j p, p ∈ Q₀ (large j) → 2 * Aa ≤ p ∧ p ≤ Ea)
      (V R : ℝ) (_hV : 0 < V) (_hR : 3 ≤ R) (N : ℕ) (_hN : (N : ℝ) ≤ R)
      (_hlowerP : ∀ p ∈ P, V ≤ Real.log (p : ℝ)) (_hupperP : ∀ p ∈ P, (p : ℝ) ≤ R)
      (Z : ℝ) (_hZ : 0 < Z) (_hproduct : ConstituentHProductLower role size (n + 1) childBound pivotBound ranges
      (scheduleFourierLeaf role ψ X lo hi) Z)
      (cutoff : ℕ → ℕ) (_hcutoff : Monotone cutoff)
      (_hVfreq : (cutoff (n + 1) : ℝ) ≤ Real.exp (C * (1 + M)))
      (_hs₀ : SchwartzMap.seminorm ℝ 0 0 FP.profile ≤ S)
      (_hs₁ : SchwartzMap.seminorm ℝ 0 1 FP.profile ≤ S)
      (_hwidth : ∀ i, FP.upper i - FP.lower i ≤ Real.exp (C * (1 + M)))
      (_hEw : ((Nat.log 2 Ew + 1 : ℕ) : ℝ) ≤ Real.exp (H * (1 + M)))
      (_hEa : ((Nat.log 2 Ea + 1 : ℕ) : ℝ) ≤ Real.exp (H * (1 + M)))
      (_hQinv : ∀ i, (∑ q ∈ Q₀ i, (q : ℝ)⁻¹)⁻¹ ≤ Real.exp (H * (1 + M)))
      (_hshorts : Real.exp (c * Real.exp (α * L)) ≤ ℓs)
      (_hshortw : Real.exp (c * Real.exp (α * L)) ≤ ℓw)
      (_hlongw : Real.exp (Real.exp (βw * L)) ≤ (Aw : ℝ))
      (_hlonga : Real.exp (Real.exp (βa * L)) ≤ (Aa : ℝ))
      (_hBs : (Bs : ℝ) ≤ Real.exp (Real.exp (γs * L)))
      (_hBw : (Bw : ℝ) ≤ Real.exp (Real.exp (γw * L)))
      (_hmin : ∀ p ∈ P, Real.exp (c * Real.exp (α * L)) ≤ (p : ℝ))
      (_hratio : Real.log R / V ≤ Real.exp (H * (1 + M)))
      (_hprimefreq : ∀ p ∈ P, cutoff (n + 1) < p)
      (d d' : ScheduledFrequencyIndex cutoff (n + 1)),
    let Q : K → Finset ℕ := Sum.elim
      (fun h => Q₀ (copyScheduleOrigin (n + 1) h.val))
      (fun y => Q₀ (copyScheduleOrigin (n + 1) y.val))
    let core := fun x : K → P => constituentCharacterCore role size χ κ pivot (n + 1) P hprime
      childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo hi)
      (scheduledFrequencyHistory cutoff (n + 1)) (fun y => x (.inr y)) N
    ‖∑ x : K → P, ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
      ((∏ h, primeSubsetPrior P (Q (.inl h)) (x (.inl (e h))) : ℝ) : ℂ) *
      (core x ((fun h => x (.inl h)), d) * conj (core x ((fun h => x (.inl (e h))), d')))‖ ≤
      (∏ h : CopyScheduleH ρ (n + 1), (∑ p ∈ Q (.inl h), (p : ℝ)⁻¹)⁻¹) * Z⁻¹ *
        Real.exp (-(c / 32) * Real.exp (α * L)) := by
  filter_upwards [eventual_constituent_supported_pair_from_sizes role (n + 1) Ar Kr
      s C S H z α βw γs c hs hC hS hH hz hα hαw hsw hc,
    eventual_constituent_supported_pair_from_sizes role (n + 1) Ar Kr
      s C S H z α βa γw c hs hC hS hH hz hα hαa hwa hc] with L hdecw hdeca
  intro size Smax hSmax hsize M hm hmL hSm χ κ pivot hκ e hχ childBound pivotBound ranges
    hrange hcount ψ hreal X lo hi hlo hhi hX hXlo hu ρ K FP m bulk hbulk he small large hsmall hlarge
    hp P hP hprime Q₀ hQP hQmass hχsmall hχword ℓs ℓw hℓs hℓw Bs Bw Aw Ew Aa Ea hAw hAa
    hsmallrange hwordrange hlargerange V R hV hR N hN hlowerP hupperP Z hZ hproduct
    cutoff hcutoff hVfreq hs₀ hs₁ hwidth hEw hEa hQinv hshorts hshortw hlongw hlonga hBs hBw
    hmin hratio hprimefreq d d' Q core
  let t := scheduledFrequencyHistory cutoff (n + 1) d
  let t' := scheduledFrequencyHistory cutoff (n + 1) d'
  have hnonneg : 0 ≤ (∏ h : CopyScheduleH ρ (n + 1),
      (∑ p ∈ Q (.inl h), (p : ℝ)⁻¹)⁻¹) * Z⁻¹ * Real.exp (-(c / 32) * Real.exp (α * L)) :=
    mul_nonneg (mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity) (inv_nonneg.mpr hZ.le))
      (Real.exp_nonneg _)
  by_cases hzero : ∀ (x : K → P) (l : CopyScheduleH ρ (n + 1) → P), core x (l, d) = 0
  · simp only [hzero, zero_mul, mul_zero, Finset.sum_const_zero, norm_zero]
    exact hnonneg
  by_cases hzero' : ∀ (x : K → P) (l : CopyScheduleH ρ (n + 1) → P), core x (l, d') = 0
  · simp only [hzero', map_zero, mul_zero, Finset.sum_const_zero, norm_zero]
    exact hnonneg
  push Not at hzero hzero'
  obtain ⟨x, l, hxl⟩ := hzero
  obtain ⟨x', l', hxl'⟩ := hzero'
  obtain ⟨ht, hn⟩ := constituentCharacterCore_nonzero_frequencies role size χ κ pivot (n + 1)
    P hprime childBound pivotBound ranges ψ X lo hi hX hXlo
    (scheduledFrequencyHistory cutoff (n + 1)) (fun y => x (.inr y)) N l d hxl
  obtain ⟨ht', hn'⟩ := constituentCharacterCore_nonzero_frequencies role size χ κ pivot (n + 1)
    P hprime childBound pivotBound ranges ψ X lo hi hX hXlo
    (scheduledFrequencyHistory cutoff (n + 1)) (fun y => x' (.inr y)) N l' d' hxl'
  have hfv := scheduledFrequencyHistory_all_bound cutoff hcutoff (n + 1) d
  have hfv' := scheduledFrequencyHistory_all_bound cutoff hcutoff (n + 1) d'
  obtain ⟨hfreq, hrealFreq⟩ := finite_frequency_range_data P hP R (cutoff (n + 1))
    hprimefreq hupperP (n + 1) t hn hfv
  obtain ⟨hfreq', hrealFreq'⟩ := finite_frequency_range_data P hP R (cutoff (n + 1))
    hprimefreq hupperP (n + 1) t' hn' hfv'
  obtain ⟨a, b, hab, hself, hreverse, hnonprincipal, hcases⟩ :=
    selected_nonanchor_prime_ranges ρ pivot n m bulk hbulk e he small large hsmall hlarge hp χ Q₀
      hχsmall hχword ℓs ℓw Bs Bw Aw Ew Aa Ea hsmallrange hwordrange hlargerange
  have hQP' : ∀ i, Q i ⊆ P := by intro i; cases i <;> exact hQP _
  have hQmass' : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹ := by intro i; cases i <;> exact hQmass _
  have hQinv' : ∀ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹ ≤ Real.exp (H * (1 + M)) := by
    intro i; cases i <;> exact hQinv _
  rcases hcases with hcase | hcase
  · exact hdecw size Smax hSmax hsize M hm hmL hSm χ κ pivot hκ e hχ childBound pivotBound ranges
      hrange hcount ψ hreal X lo hi hlo hhi hu a b hab t t' ht ht' hself hreverse P hP hprime Q
      hQP' hQmass' hnonprincipal Aw Ew hAw hfreq hfreq'
      (fun p hp => (hcase.2 p hp).1) (fun p hp => (hcase.2 p hp).2) ℓs hℓs
      (fun q hq => (hcase.1 q hq).1) Bs (fun q => (hcase.1 q.val q.property).2)
      V R hV hR N hN hlowerP hupperP hrealFreq hrealFreq' Z hZ hproduct
      (cutoff (n + 1)) hVfreq hfv hfv' hs₀ hs₁ hwidth hEw hQinv' hshorts hlongw hBs hmin hratio
  · exact hdeca size Smax hSmax hsize M hm hmL hSm χ κ pivot hκ e hχ childBound pivotBound ranges
      hrange hcount ψ hreal X lo hi hlo hhi hu a b hab t t' ht ht' hself hreverse P hP hprime Q
      hQP' hQmass' hnonprincipal Aa Ea hAa hfreq hfreq'
      (fun p hp => (hcase.2 p hp).1) (fun p hp => (hcase.2 p hp).2) ℓw hℓw
      (fun q hq => (hcase.1 q hq).1) Bw (fun q => (hcase.1 q.val q.property).2)
      V R hV hR N hN hlowerP hupperP hrealFreq hrealFreq' Z hZ hproduct
      (cutoff (n + 1)) hVfreq hfv hfv' hs₀ hs₁ hwidth hEa hQinv' hshortw hlonga hBw hmin hratio

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedNonanchorProductDiagonal
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual code-changing diagonal after summing external pivots -/
namespace Ostmann
universe u
open Filter
open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

theorem eventual_selected_nonanchor_product_diagonal {I : Type u} [Fintype I]
    (role : I → CopyScheduleRole) (n Ar Kr : ℕ)
    (s C S H z α βw γs βa γw c : ℝ)
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hS : 1 ≤ S) (hH : 0 ≤ H) (hz : 0 ≤ z)
    (hα : 0 < α) (hαw : α < βw) (hsw : γs < βw)
    (hαa : α < βa) (hwa : γw < βa) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ (size : I → ℕ) (Smax : ℕ)
      (_hSmax : 1 ≤ Smax) (_hsize : ∀ i, size i ≤ Smax)
      (M : ℝ) (_hm : 0 ≤ M) (_hmL : M ≤ z * L) (_hSm : (Smax : ℝ) ≤ s * (1 + M))
      (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
      (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
      (_hκ : ∀ i p, ‖κ i p‖ ≤ 1)
      (childBound pivotBound : ℕ → ℕ)
      (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
      (_hrange : ∀ j ≤ n + 1, ∀ r ∈ ranges j, r.atoms.length ≤ Ar)
      (_hcount : ∀ j ≤ n + 1, (ranges j).length ≤ Kr)
      (ψ : 𝓢(ℝ, ℂ)) (_hreal : ∀ y, conj (ψ y) = ψ y)
      (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (_hX : 0 < X) (_hXlo : 1 < X * lo)
      (_hu : ∀ j ≤ n + 1, ∀ a b, role a = .pivot j → role b = .pivot j → a = b),
    let ρ := fun i : Σ a, Fin (size a) => role i.1
    let FP := WordFourierParameters.uniform (n + 1) (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi
    ∀ (m : ℕ) (bulk : Fin m ↪ (Σ a, Fin (size a))) (hbulk : ∀ i, ρ (bulk i) = .word)
      (_hχ : ∀ e ∈ cellPreservingMatchings (selectedBulkLabel ρ (n + 1) m bulk hbulk) \
        selectedAnchorMatchingSet ρ (n + 1) m bulk hbulk,
        ∀ i, χ (copyScheduleOrigin (n + 1) (e i).val) = χ (copyScheduleOrigin (n + 1) i.val))
      (small large : Fin (n + 1) → (Σ a, Fin (size a)))
      (_hsmall : ∀ j, ρ (small j) = .anchor j) (_hlarge : ∀ j, ρ (large j) = .anchor j)
      (_hp : ∀ j < n + 1, ρ (pivot j) = .pivot j)
      (P : Finset ℕ) (_hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
      (Q₀ : (Σ i, Fin (size i)) → Finset ℕ) (_hQP : ∀ i, Q₀ i ⊆ P)
      (_hQmass : ∀ i, 0 < ∑ q ∈ Q₀ i, (q : ℝ)⁻¹)
      (_hχsmall : ∀ j q, q ∈ Q₀ (small j) → χ (small j) q ^ 2 ≠ 1)
      (_hχword : ∀ i q, q ∈ Q₀ (bulk i) → χ (bulk i) q ^ 2 ≠ 1)
      (ℓs ℓw : ℝ) (_hℓs : 0 < ℓs) (_hℓw : 0 < ℓw) (Bs Bw Aw Ew Aa Ea : ℕ)
      (_hAw : 0 < Aw) (_hAa : 0 < Aa)
      (_hsmallrange : ∀ j q, q ∈ Q₀ (small j) → ℓs ≤ (q : ℝ) ∧ q ≤ Bs)
      (_hwordrange : ∀ i p, p ∈ Q₀ (bulk i) →
        (ℓw ≤ (p : ℝ) ∧ p ≤ Bw) ∧ (2 * Aw ≤ p ∧ p ≤ Ew))
      (_hlargerange : ∀ j p, p ∈ Q₀ (large j) → 2 * Aa ≤ p ∧ p ≤ Ea)
      (V R : ℝ) (_hV : 0 < V) (_hR : 3 ≤ R) (a b : ℕ) (_ha : 0 < a) (_hb : (b : ℝ) ≤ R) (gap : ℝ)
      (_hlowerP : ∀ p ∈ P, V ≤ Real.log (p : ℝ)) (_hupperP : ∀ p ∈ P, (p : ℝ) ≤ R)
      (productLower : ℝ) (_hproductLower : 0 < productLower)
      (_hgap : Real.exp gap * (b : ℝ) ≤ productLower)
      (_hproduct : ConstituentHProductLower role size (n + 1) childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo hi) productLower)
      (cutoff : ℕ → ℕ) (_hcutoff : Monotone cutoff)
      (_hVfreq : (cutoff (n + 1) : ℝ) ≤ Real.exp (C * (1 + M)))
      (_hs₀ : SchwartzMap.seminorm ℝ 0 0 FP.profile ≤ S)
      (_hs₁ : SchwartzMap.seminorm ℝ 0 1 FP.profile ≤ S)
      (_hwidth : ∀ i, FP.upper i - FP.lower i ≤ Real.exp (C * (1 + M)))
      (_hEw : ((Nat.log 2 Ew + 1 : ℕ) : ℝ) ≤ Real.exp (H * (1 + M)))
      (_hEa : ((Nat.log 2 Ea + 1 : ℕ) : ℝ) ≤ Real.exp (H * (1 + M)))
      (_hQinv : ∀ i, (∑ q ∈ Q₀ i, (q : ℝ)⁻¹)⁻¹ ≤ Real.exp (H * (1 + M)))
      (_hshorts : Real.exp (c * Real.exp (α * L)) ≤ ℓs)
      (_hshortw : Real.exp (c * Real.exp (α * L)) ≤ ℓw)
      (_hlongw : Real.exp (Real.exp (βw * L)) ≤ (Aw : ℝ))
      (_hlonga : Real.exp (Real.exp (βa * L)) ≤ (Aa : ℝ))
      (_hBs : (Bs : ℝ) ≤ Real.exp (Real.exp (γs * L)))
      (_hBw : (Bw : ℝ) ≤ Real.exp (Real.exp (γw * L)))
      (_hmin : ∀ p ∈ P, Real.exp (c * Real.exp (α * L)) ≤ (p : ℝ))
      (_hratio : Real.log R / V ≤ Real.exp (H * (1 + M)))
      (_hprimefreq : ∀ p ∈ P, cutoff (n + 1) < p),
    let Sbad := cellPreservingMatchings (selectedBulkLabel ρ (n + 1) m bulk hbulk) \
      selectedAnchorMatchingSet ρ (n + 1) m bulk hbulk
    (∑ N ∈ Finset.Icc a b,
      (constituentMatchingFamily role size χ κ pivot (n + 1) P hprime Q₀ childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo hi) (scheduledFrequencyHistory cutoff (n + 1)) Sbad N).re) ≤
      Real.exp (-gap) * ((Sbad.card : ℝ) *
        (Fintype.card (ScheduledFrequencyIndex cutoff (n + 1)) : ℝ) ^ 2 *
        (∏ h : CopyScheduleH ρ (n + 1),
          (∑ p ∈ Q₀ (copyScheduleOrigin (n + 1) h.val), (p : ℝ)⁻¹)⁻¹)) *
        Real.exp (-(c / 32) * Real.exp (α * L)) := by
  filter_upwards [eventual_selected_supported_pair_decay role n Ar Kr
    s C S H z α βw γs βa γw c hs hC hS hH hz hα hαw hsw hαa hwa hc] with L hdec
  intro size Smax hSmax hsize M hm hmL hSm χ κ pivot hκ childBound pivotBound ranges
    hrange hcount ψ hreal X lo hi hlo hhi hX hXlo hu ρ FP m bulk hbulk hχ small large hsmall hlarge
    hp P hP hprime Q₀ hQP hQmass hχsmall hχword ℓs ℓw hℓs hℓw Bs Bw Aw Ew Aa Ea hAw hAa
    hsmallrange hwordrange hlargerange V R hV hR a b ha hb gap hlowerP hupperP productLower hproductLower hgap hproduct
    cutoff hcutoff hVfreq hs₀ hs₁ hwidth hEw hEa hQinv hshorts hshortw hlongw hlonga hBs hBw
    hmin hratio hprimefreq Sbad
  apply constituentMatchingFamily_interval_pair_product role size χ κ pivot (n + 1) P hprime Q₀
    childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo hi)
    (scheduledFrequencyHistory cutoff (n + 1)) Sbad a b ha gap
    (Real.exp (-(c / 32) * Real.exp (α * L))) (Real.exp_nonneg _) productLower hproductLower hgap
  intro N hN e he d d' _
  have hinv := selected_nonanchor_symm ρ (n + 1) m bulk hbulk e he
  have hNr : (N : ℝ) ≤ R := (Nat.cast_le.mpr (Finset.mem_Icc.mp hN).2).trans hb
  have hh := hdec size Smax hSmax hsize M hm hmL hSm χ κ pivot hκ e.symm (hχ _ hinv)
    childBound pivotBound ranges hrange hcount ψ hreal X lo hi hlo hhi hX hXlo hu
    m bulk hbulk hinv small large hsmall hlarge hp P hP hprime Q₀ hQP hQmass hχsmall hχword
    ℓs ℓw hℓs hℓw Bs Bw Aw Ew Aa Ea hAw hAa hsmallrange hwordrange hlargerange
    V R hV hR N hNr hlowerP hupperP productLower hproductLower hproduct cutoff hcutoff hVfreq hs₀ hs₁ hwidth hEw hEa hQinv
    hshorts hshortw hlongw hlonga hBs hBw hmin hratio hprimefreq d d'
  simpa only [constituentOriginalMatchedPair, Equiv.symm_symm, Sum.elim_inl, Sum.elim_inr,
    finite_univ_canonical] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedNonanchorProductDecay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every code-changing diagonal cost is absorbed by the actual character error -/
namespace Ostmann
universe u
open Filter
open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

theorem eventual_selected_nonanchor_product_decay_oai {I : Type u} [Fintype I]
    (role : I → CopyScheduleRole) (n Ar Kr : ℕ)
    (s C S H z α βw γs βa γw c T : ℝ)
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hS : 1 ≤ S) (hH : 0 ≤ H) (hz : 0 ≤ z)
    (hα : 0 < α) (hαw : α < βw) (hsw : γs < βw)
    (hαa : α < βa) (hwa : γw < βa) (hc : 0 < c) (hT : 0 ≤ T) :
    ∀ᶠ L : ℝ in atTop, ∀ (size : I → ℕ) (Smax : ℕ)
      (_hSmax : 1 ≤ Smax) (_hsize : ∀ i, size i ≤ Smax)
      (M : ℝ) (_hm : 0 ≤ M) (_hmL : M ≤ z * L) (_hSm : (Smax : ℝ) ≤ s * (1 + M))
      (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
      (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
      (_hκ : ∀ i p, ‖κ i p‖ ≤ 1)
      (childBound pivotBound : ℕ → ℕ)
      (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
      (_hrange : ∀ j ≤ n + 1, ∀ r ∈ ranges j, r.atoms.length ≤ Ar)
      (_hcount : ∀ j ≤ n + 1, (ranges j).length ≤ Kr)
      (ψ : 𝓢(ℝ, ℂ)) (_hreal : ∀ y, conj (ψ y) = ψ y)
      (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (_hX : 0 < X) (_hXlo : 1 < X * lo)
      (_hu : ∀ j ≤ n + 1, ∀ a b, role a = .pivot j → role b = .pivot j → a = b),
    let ρ := fun i : Σ a, Fin (size a) => role i.1
    let FP := WordFourierParameters.uniform (n + 1) (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi
    ∀ (m : ℕ) (bulk : Fin m ↪ (Σ a, Fin (size a))) (hbulk : ∀ i, ρ (bulk i) = .word)
      (_hχ : ∀ e ∈ cellPreservingMatchings (selectedBulkLabel ρ (n + 1) m bulk hbulk) \
        selectedAnchorMatchingSet ρ (n + 1) m bulk hbulk,
        ∀ i, χ (copyScheduleOrigin (n + 1) (e i).val) = χ (copyScheduleOrigin (n + 1) i.val))
      (small large : Fin (n + 1) → (Σ a, Fin (size a)))
      (_hsmall : ∀ j, ρ (small j) = .anchor j) (_hlarge : ∀ j, ρ (large j) = .anchor j)
      (_hp : ∀ j < n + 1, ρ (pivot j) = .pivot j)
      (P : Finset ℕ) (_hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
      (Q₀ : (Σ i, Fin (size i)) → Finset ℕ) (_hQP : ∀ i, Q₀ i ⊆ P)
      (_hQmass : ∀ i, 0 < ∑ q ∈ Q₀ i, (q : ℝ)⁻¹)
      (_hχsmall : ∀ j q, q ∈ Q₀ (small j) → χ (small j) q ^ 2 ≠ 1)
      (_hχword : ∀ i q, q ∈ Q₀ (bulk i) → χ (bulk i) q ^ 2 ≠ 1)
      (ℓs ℓw : ℝ) (_hℓs : 0 < ℓs) (_hℓw : 0 < ℓw) (Bs Bw Aw Ew Aa Ea : ℕ)
      (_hAw : 0 < Aw) (_hAa : 0 < Aa)
      (_hsmallrange : ∀ j q, q ∈ Q₀ (small j) → ℓs ≤ (q : ℝ) ∧ q ≤ Bs)
      (_hwordrange : ∀ i p, p ∈ Q₀ (bulk i) →
        (ℓw ≤ (p : ℝ) ∧ p ≤ Bw) ∧ (2 * Aw ≤ p ∧ p ≤ Ew))
      (_hlargerange : ∀ j p, p ∈ Q₀ (large j) → 2 * Aa ≤ p ∧ p ≤ Ea)
      (V R : ℝ) (_hV : 0 < V) (_hR : 3 ≤ R) (a b : ℕ) (_ha : 0 < a) (_hb : (b : ℝ) ≤ R) (gap : ℝ)
      (_hlowerP : ∀ p ∈ P, V ≤ Real.log (p : ℝ)) (_hupperP : ∀ p ∈ P, (p : ℝ) ≤ R)
      (productLower : ℝ) (_hproductLower : 0 < productLower)
      (_hgap : Real.exp gap * (b : ℝ) ≤ productLower)
      (_hproduct : ConstituentHProductLower role size (n + 1) childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo hi) productLower)
      (cutoff : ℕ → ℕ) (_hcutoff : Monotone cutoff)
      (_hVfreq : (cutoff (n + 1) : ℝ) ≤ Real.exp (C * (1 + M)))
      (_hs₀ : SchwartzMap.seminorm ℝ 0 0 FP.profile ≤ S)
      (_hs₁ : SchwartzMap.seminorm ℝ 0 1 FP.profile ≤ S)
      (_hwidth : ∀ i, FP.upper i - FP.lower i ≤ Real.exp (C * (1 + M)))
      (_hEw : ((Nat.log 2 Ew + 1 : ℕ) : ℝ) ≤ Real.exp (H * (1 + M)))
      (_hEa : ((Nat.log 2 Ea + 1 : ℕ) : ℝ) ≤ Real.exp (H * (1 + M)))
      (_hQinv : ∀ i, (∑ q ∈ Q₀ i, (q : ℝ)⁻¹)⁻¹ ≤ Real.exp (H * (1 + M)))
      (_hshorts : Real.exp (c * Real.exp (α * L)) ≤ ℓs)
      (_hshortw : Real.exp (c * Real.exp (α * L)) ≤ ℓw)
      (_hlongw : Real.exp (Real.exp (βw * L)) ≤ (Aw : ℝ))
      (_hlonga : Real.exp (Real.exp (βa * L)) ≤ (Aa : ℝ))
      (_hBs : (Bs : ℝ) ≤ Real.exp (Real.exp (γs * L)))
      (_hBw : (Bw : ℝ) ≤ Real.exp (Real.exp (γw * L)))
      (_hmin : ∀ p ∈ P, Real.exp (c * Real.exp (α * L)) ≤ (p : ℝ))
      (_hratio : Real.log R / V ≤ Real.exp (H * (1 + M)))
      (_hprimefreq : ∀ p ∈ P, cutoff (n + 1) < p),
    let Sbad := cellPreservingMatchings (selectedBulkLabel ρ (n + 1) m bulk hbulk) \
      selectedAnchorMatchingSet ρ (n + 1) m bulk hbulk
    (∑ N ∈ Finset.Icc a b,
      (constituentMatchingFamily role size χ κ pivot (n + 1) P hprime Q₀ childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo hi) (scheduledFrequencyHistory cutoff (n + 1)) Sbad N).re) ≤
      Real.exp (-gap) * Real.exp (-T * M) := by
  filter_upwards [eventual_selected_nonanchor_product_diagonal role n Ar Kr
      s C S H z α βw γs βa γw c hs hC hS hH hz hα hαw hsw hαa hwa hc,
    eventual_constituent_matching_error role (n + 1) s C H T z α (c / 32)
      hs hC hH hT hz hα (by positivity)] with L hdiag herr
  intro size Smax hSmax hsize M hm hmL hSm χ κ pivot hκ childBound pivotBound ranges
    hrange hcount ψ hreal X lo hi hlo hhi hX hXlo hu ρ FP m bulk hbulk hχ small large hsmall hlarge
    hp P hP hprime Q₀ hQP hQmass hχsmall hχword ℓs ℓw hℓs hℓw Bs Bw Aw Ew Aa Ea hAw hAa
    hsmallrange hwordrange hlargerange V R hV hR a b ha hb gap hlowerP hupperP productLower hproductLower hgap hproduct
    cutoff hcutoff hVfreq hs₀ hs₁ hwidth hEw hEa hQinv hshorts hshortw hlongw hlonga hBs hBw
    hmin hratio hprimefreq Sbad
  have hd := hdiag size Smax hSmax hsize M hm hmL hSm χ κ pivot hκ childBound pivotBound ranges
    hrange hcount ψ hreal X lo hi hlo hhi hX hXlo hu m bulk hbulk hχ small large hsmall hlarge
    hp P hP hprime Q₀ hQP hQmass hχsmall hχword ℓs ℓw hℓs hℓw Bs Bw Aw Ew Aa Ea hAw hAa
    hsmallrange hwordrange hlargerange V R hV hR a b ha hb gap hlowerP hupperP productLower hproductLower hgap hproduct
    cutoff hcutoff hVfreq hs₀ hs₁ hwidth hEw hEa hQinv hshorts hshortw hlongw hlonga hBs hBw
    hmin hratio hprimefreq
  have he := herr size Smax hsize M hm hmL hSm cutoff hcutoff hVfreq Sbad Q₀ hQinv
  apply hd.trans
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left he (Real.exp_nonneg _)

end Ostmann

end OAI
end

theorem solution.{u} : type_of% @OAI.Ostmann.eventual_selected_nonanchor_product_decay_oai.{u} := @OAI.Ostmann.eventual_selected_nonanchor_product_decay_oai.{u}
