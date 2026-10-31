-- Prove2me | solution 1 for OAI.Ostmann.eventual_character_atom_iteration
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:03:58.992849+00:00
-- url     : https://prove2.me/submissions/c7d8ed9b-9465-488d-9e17-a150c3cd3602

import Mathlib
import Definitions.Def_OAIQ095D007

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DistinctTupleProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Grouping distinct ordered products by their underlying subsets -/

namespace Ostmann

open scoped BigOperators Classical

theorem card_tupleImage_fiber {A : Type*} [Fintype A] [DecidableEq A]
    (k : ℕ) (Q : Finset A) (hQ : Q.card = k) :
    Fintype.card {e : Fin k ↪ A // tupleImage e = Q} = k.factorial := by
  rw [Fintype.card_congr (tupleImageFiberEquiv k Q)]
  let E : Fin k ≃ Q := Fintype.equivOfCardEq (by simpa using hQ.symm)
  simpa using Fintype.card_equiv E

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferArithmetic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The arithmetic separation of diagonal and transferred terms -/

namespace Ostmann

/-- A nonzero transferred frequency rules out a shared prime between
the two inherited products. All such primes exceed the frequency. -/
theorem transferred_products_coprime (HL HR : ℕ) (v w s P : ℤ) (hs : s ≠ 0)
    (hrel : v * HR - w * HL = s * P)
    (hsmall : ∀ q, q.Prime → q ∣ HL → q ∣ HR → s.natAbs < q)
    (hunit : ∀ q, q.Prime → q ∣ HL → q ∣ HR → IsCoprime (q : ℤ) P) :
    HL.Coprime HR := by
  apply Nat.coprime_of_dvd
  intro q hq hqL hqR
  have hL : (q : ℤ) ∣ (HL : ℤ) := Int.natCast_dvd_natCast.mpr hqL
  have hR : (q : ℤ) ∣ (HR : ℤ) := Int.natCast_dvd_natCast.mpr hqR
  have hN : (q : ℤ) ∣ v * HR - w * HL :=
    dvd_sub (dvd_mul_of_dvd_right hR v) (dvd_mul_of_dvd_right hL w)
  rw [hrel] at hN
  have hqs : (q : ℤ) ∣ s := (hunit q hq hqL hqR).dvd_of_dvd_mul_right hN
  have hle := Int.natAbs_le_of_dvd_ne_zero hqs hs
  simp only [Int.natAbs_natCast] at hle
  exact (not_le_of_gt (hsmall q hq hqL hqR)) hle

/-- Regrouping a nonzero numerator by the new signed frequency is
one-to-one, exactly as in the transfer substitution. -/
theorem unique_transferred_frequency (N P : ℤ) (hN : N ≠ 0) (hP : P ≠ 0)
    (hdiv : P ∣ N) : ∃! s : ℤ, s ≠ 0 ∧ N = s * P := by
  obtain ⟨s, hs⟩ := hdiv
  refine ⟨s, ⟨?_, by simpa only [mul_comm] using hs⟩, ?_⟩
  · intro hz
    simp only [hz, mul_zero] at hs
    exact hN hs
  · intro t ht
    apply mul_right_cancel₀ hP
    rw [← ht.2, hs, mul_comm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferLocalPhases
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local additive and character substitutions in one transfer -/

namespace Ostmann

open scoped ComplexConjugate

private theorem transfer_left_division {K : Type*} [Field K]
    (P R D v s : K) (hP : P ≠ 0) (hR : R ≠ 0) (hD : D ≠ 0)
    (hrel : v * R = s * P) : v / (P * D) = s / (R * D) := by
  apply (div_eq_div_iff (mul_ne_zero hP hD) (mul_ne_zero hR hD)).mpr
  calc
    v * (R * D) = (v * R) * D := by ring
    _ = (s * P) * D := by rw [hrel]
    _ = s * (P * D) := by ring

private theorem transfer_outside_division {K : Type*} [Field K]
    (P L R D v w s : K) (hP : P ≠ 0) (hL : L ≠ 0) (hR : R ≠ 0) (hD : D ≠ 0)
    (hrel : v * R - w * L = s * P) :
    v / (P * L * D) - w / (P * R * D) = s / (L * R * D) := by
  calc
    _ = (v * R - w * L) / (P * L * R * D) := by field_simp
    _ = (s * P) / (P * L * R * D) := by rw [hrel]
    _ = _ := by field_simp

/-- At a left-slot prime the right branch survives modulo p. -/
theorem transfer_left_additive {p : ℕ} [Fact p.Prime]
    (P R D v s t : ZMod p) (hP : P ≠ 0) (hR : R ≠ 0) (hD : D ≠ 0)
    (hrel : v * R = s * P) :
    ZMod.stdAddChar (t * (v / (P * D))) =
      ZMod.stdAddChar (t * (s / (R * D))) := by
  rw [transfer_left_division P R D v s hP hR hD hrel]

/-- At a right-slot prime conjugation supplies the minus sign. -/
theorem transfer_right_additive {p : ℕ} [Fact p.Prime]
    (P L D w s t : ZMod p) (hP : P ≠ 0) (hL : L ≠ 0) (hD : D ≠ 0)
    (hrel : -w * L = s * P) :
    conj (ZMod.stdAddChar (t * (w / (P * D)))) =
      ZMod.stdAddChar (t * (s / (L * D))) := by
  have h := transfer_left_division P L D (-w) s hP hL hD hrel
  rw [← h]
  simp only [neg_div, mul_neg, AddChar.map_neg_eq_conj]

/-- Outside slots occur in both branches and their translation differences
combine at the new signed frequency. -/
theorem transfer_outside_additive {p : ℕ} [Fact p.Prime]
    (P L R D v w s t : ZMod p)
    (hP : P ≠ 0) (hL : L ≠ 0) (hR : R ≠ 0) (hD : D ≠ 0)
    (hrel : v * R - w * L = s * P) :
    ZMod.stdAddChar (t * (v / (P * L * D))) *
        conj (ZMod.stdAddChar (t * (w / (P * R * D)))) =
      ZMod.stdAddChar (t * (s / (L * R * D))) := by
  rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← mul_sub,
    transfer_outside_division P L R D v w s hP hL hR hD hrel]

private theorem mulChar_div {K : Type*} [Field K] (χ : MulChar K ℂ) (v s : K) :
    χ (v / s) = χ v / χ s := by
  rw [div_eq_mul_inv, map_mul, ← MulChar.inv_apply', MulChar.inv_apply_eq_inv', div_eq_mul_inv]

/-- The incoming pivot column becomes a cross-branch character factor. -/
theorem transfer_left_character {p : ℕ} [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (P R v s : ZMod p) (hs : s ≠ 0)
    (hrel : v * R = s * P) : χ P = χ (v / s) * χ R := by
  have he : P = v / s * R := by
    apply (mul_left_cancel₀ hs)
    calc
      s * P = v * R := hrel.symm
      _ = s * (v / s * R) := by field_simp
  rw [he, map_mul]

/-- Frequency factors cancel in every regular outgoing row, for either sign. -/
theorem transfer_regular_unary {p : ℕ} [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (v s : ZMod p) (hv : v ≠ 0) (ε : ℤ) :
    χ v ^ (-ε) * χ (v / s) ^ ε = χ s ^ (-ε) := by
  have hχv : χ v ≠ 0 := (MulChar.apply_ne_zero_iff).mpr (isUnit_iff_ne_zero.mpr hv)
  rw [mulChar_div, div_zpow, zpow_neg, zpow_neg]
  field_simp

theorem character_product_power {I : Type*} [Fintype I] {p : ℕ}
    (χ : DirichletCharacter ℂ p) (q : I → ZMod p) (b : ℤ) :
    χ (∏ i, q i) ^ b = ∏ i, χ (q i) ^ b := by
  rw [map_prod, Finset.prod_zpow]

theorem conjugate_character_power {p : ℕ} (χ : DirichletCharacter ℂ p)
    (x : ZMod p) (b : ℤ) : conj (χ x ^ b) = χ x ^ (-b) := by
  change star (χ x ^ b) = _
  rw [star_zpow₀, MulChar.star_apply', MulChar.inv_apply_eq_inv', inv_zpow, zpow_neg]

theorem transfer_incoming_character {p : ℕ} [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (P R v s : ZMod p) (hs : s ≠ 0)
    (hrel : v * R = s * P) (b : ℤ) :
    χ P ^ b = χ (v / s) ^ b * χ R ^ b := by
  rw [transfer_left_character χ P R v s hs hrel, mul_zpow]

theorem transfer_left_regular_factor {p : ℕ} [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (P R v s : ZMod p) (hv : v ≠ 0) (hs : s ≠ 0)
    (hrel : v * R = s * P) (ε : ℤ) :
    χ v ^ (-ε) * χ P ^ ε = χ s ^ (-ε) * χ R ^ ε := by
  rw [transfer_incoming_character χ P R v s hs hrel, ← mul_assoc,
    transfer_regular_unary χ v s hv ε]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PivotRowPhase
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded pivot row after grouping by v/H -/

namespace Ostmann

open scoped BigOperators

theorem character_zpow_norm_le_one {p : ℕ} (χ : DirichletCharacter ℂ p)
    (x : ZMod p) (ε : ℤ) : ‖χ x ^ ε‖ ≤ 1 := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    simp only [norm_zpow, χ.unit_norm_eq_one, one_zpow, le_refl]
  · rw [χ.map_nonunit hx]
    by_cases he : ε = 0
    · simp [he]
    · simp [zero_zpow, he]

theorem pivotLocalRow_norm_le_one {p : ℕ} [NeZero p] (χ : DirichletCharacter ℂ p)
    (κ : ℂ) (hκ : ‖κ‖ ≤ 1) (t D Y u : ZMod p) (ε : ℤ) :
    ‖pivotLocalRow χ κ t D Y u ε‖ ≤ 1 := by
  rw [pivotLocalRow, norm_mul, norm_mul]
  simp only [ZMod.stdAddChar_apply, Circle.norm_coe, one_mul]
  exact (mul_le_mul hκ (character_zpow_norm_le_one χ _ ε)
    (norm_nonneg _) (by norm_num)).trans (by norm_num)

/-- The complete outgoing local pivot factor sees the other active product H
only through u = v/H. -/
theorem pivotLocalRow_eq {p : ℕ} [Fact p.Prime] (χ : DirichletCharacter ℂ p)
    (κ : ℂ) (t D Y H v u : ZMod p) (ε : ℤ)
    (hD : D ≠ 0) (hY : Y ≠ 0) (hH : H ≠ 0) (hu : u ≠ 0) (hv : v = u * H) :
    ZMod.stdAddChar (t * (v / (D * Y * H))) * κ *
      (χ v ^ (-ε) * χ (D * Y * H) ^ ε) = pivotLocalRow χ κ t D Y u ε := by
  have hv0 : v ≠ 0 := by rw [hv]; exact mul_ne_zero hu hH
  have ha : v / (D * Y * H) = u / (D * Y) := by rw [hv]; field_simp
  have hr : v * (D * Y) = u * (D * Y * H) := by rw [hv]; ring
  have hc := transfer_left_regular_factor χ (D * Y * H) (D * Y) v u hv0 hu hr ε
  rw [ha, hc]
  change _ = ZMod.stdAddChar (t * (u / (D * Y))) * κ * χ (D * Y / u) ^ ε
  have hd : χ (D * Y / u) ^ ε = χ (D * Y) ^ ε * χ u ^ (-ε) := by
    rw [div_eq_mul_inv, map_mul, ← MulChar.inv_apply', MulChar.inv_apply_eq_inv',
      mul_zpow, inv_zpow, zpow_neg]
  rw [hd]
  ring

theorem pivotTupleRow_norm_le_one {I : Type*} [Fintype I] (p : I → ℕ)
    [∀ i, NeZero (p i)] (χ : ∀ i, DirichletCharacter ℂ (p i)) (κ : I → ℂ)
    (hκ : ∀ i, ‖κ i‖ ≤ 1) (t D Y u : ∀ i, ZMod (p i)) (ε : I → ℤ) :
    ‖pivotTupleRow p χ κ t D Y u ε‖ ≤ 1 := by
  rw [pivotTupleRow, norm_prod]
  exact Finset.prod_le_one (fun i _ => norm_nonneg _)
    (fun i _ => pivotLocalRow_norm_le_one _ _ (hκ i) _ _ _ _ _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferIntegerPhases
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reducing the actual integer transfer equation at each surviving prime -/

namespace Ostmann

/-- A left-slot prime divides the left product, so its local equation loses
that term. No primality is required for this algebraic reduction. -/
theorem transfer_equation_mod_left (p L R M : ℕ) (v w s : ℤ)
    (hpL : p ∣ L) (h : v * R - w * L = s * M) :
    (v : ZMod p) * (R : ZMod p) = (s : ZMod p) * (M : ZMod p) := by
  have hL : (L : ZMod p) = 0 := by
    obtain ⟨k, hk⟩ := hpL
    rw [hk, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have he := congrArg (fun z : ℤ => (z : ZMod p)) h
  push_cast at he
  simpa only [hL, mul_zero, sub_zero] using he

theorem transfer_equation_mod_right (p L R M : ℕ) (v w s : ℤ)
    (hpR : p ∣ R) (h : v * R - w * L = s * M) :
    -(w : ZMod p) * (L : ZMod p) = (s : ZMod p) * (M : ZMod p) := by
  have hR : (R : ZMod p) = 0 := by
    obtain ⟨k, hk⟩ := hpR
    rw [hk, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have he := congrArg (fun z : ℤ => (z : ZMod p)) h
  push_cast at he
  simpa only [hR, mul_zero, zero_sub, neg_mul] using he

theorem transfer_equation_mod_outside (p L R M : ℕ) (v w s : ℤ)
    (h : v * R - w * L = s * M) :
    (v : ZMod p) * (R : ZMod p) - (w : ZMod p) * (L : ZMod p) =
      (s : ZMod p) * (M : ZMod p) := by
  have he := congrArg (fun z : ℤ => (z : ZMod p)) h
  push_cast at he
  exact he

/-- Natural coprimality supplies the nonzero denominators in the prime field. -/
theorem zmod_natCast_ne_zero_of_coprime {p : ℕ} [Fact p.Prime] (a : ℕ)
    (h : a.Coprime p) : (a : ZMod p) ≠ 0 :=
  isUnit_iff_ne_zero.mp ((ZMod.isUnit_iff_coprime a p).mpr h)

/-- The actual integer equation supplies the left additive phase identity. -/
theorem transfer_left_additive_integer {p : ℕ} [Fact p.Prime]
    (L R M D : ℕ) (v w s : ℤ) (t : ZMod p)
    (hpL : p ∣ L) (hM : M.Coprime p) (hR : R.Coprime p) (hD : D.Coprime p)
    (hrel : v * R - w * L = s * M) :
    ZMod.stdAddChar (t * ((v : ZMod p) / ((M : ZMod p) * (D : ZMod p)))) =
      ZMod.stdAddChar (t * ((s : ZMod p) / ((R : ZMod p) * (D : ZMod p)))) :=
  transfer_left_additive _ _ _ _ _ _
    (zmod_natCast_ne_zero_of_coprime M hM)
    (zmod_natCast_ne_zero_of_coprime R hR)
    (zmod_natCast_ne_zero_of_coprime D hD)
    (transfer_equation_mod_left p L R M v w s hpL hrel)

/-- The right copy is conjugated before using the integer equation. -/
theorem transfer_right_additive_integer {p : ℕ} [Fact p.Prime]
    (L R M D : ℕ) (v w s : ℤ) (t : ZMod p)
    (hpR : p ∣ R) (hM : M.Coprime p) (hL : L.Coprime p) (hD : D.Coprime p)
    (hrel : v * R - w * L = s * M) :
    star (ZMod.stdAddChar (t * ((w : ZMod p) / ((M : ZMod p) * (D : ZMod p))))) =
      ZMod.stdAddChar (t * ((s : ZMod p) / ((L : ZMod p) * (D : ZMod p)))) :=
  transfer_right_additive _ _ _ _ _ _
    (zmod_natCast_ne_zero_of_coprime M hM)
    (zmod_natCast_ne_zero_of_coprime L hL)
    (zmod_natCast_ne_zero_of_coprime D hD)
    (transfer_equation_mod_right p L R M v w s hpR hrel)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferRowProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complete local rows and their product under transfer -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

/-- The incoming pivot column becomes one constant exponent on every
opposite-branch constituent. The other old row factors are retained. -/
theorem transfer_left_row {I : Type*} [Fintype I] {p : ℕ} [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (P D v s t : ZMod p) (R : I → ZMod p)
    (ν S O : ℂ) (b : ℤ)
    (hP : P ≠ 0) (hD : D ≠ 0) (hR : (∏ i, R i) ≠ 0) (hs : s ≠ 0)
    (hrel : v * (∏ i, R i) = s * P) :
    ZMod.stdAddChar (t * (v / (P * D))) * ν * χ P ^ b * S * O =
      ZMod.stdAddChar (t * (s / ((∏ i, R i) * D))) *
        (ν * χ (v / s) ^ b) * S * (∏ i, χ (R i) ^ b) * O := by
  rw [transfer_left_additive P (∏ i, R i) D v s t hP hR hD hrel,
    transfer_incoming_character χ P (∏ i, R i) v s hs hrel b,
    character_product_power χ R b]
  ring

/-- The conjugated right row has the negative incoming exponent on every
left-branch constituent. This includes its new unary factor exactly. -/
theorem transfer_right_row {I : Type*} [Fintype I] {p : ℕ} [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (P D w s t : ZMod p) (L : I → ZMod p)
    (ν S O : ℂ) (b : ℤ)
    (hP : P ≠ 0) (hD : D ≠ 0) (hL : (∏ i, L i) ≠ 0) (hs : s ≠ 0)
    (hrel : -w * (∏ i, L i) = s * P) :
    conj (ZMod.stdAddChar (t * (w / (P * D))) * ν * χ P ^ b * S * O) =
      ZMod.stdAddChar (t * (s / ((∏ i, L i) * D))) *
        (conj ν * χ (-w / s) ^ (-b)) * conj S * (∏ i, χ (L i) ^ (-b)) * conj O := by
  have hc : conj (χ P ^ b) = χ (-w / s) ^ (-b) * ∏ i, χ (L i) ^ (-b) := by
    rw [transfer_incoming_character χ P (∏ i, L i) (-w) s hs hrel b, map_mul,
      conjugate_character_power, conjugate_character_power, character_product_power]
  rw [map_mul, map_mul, map_mul, map_mul, hc,
    transfer_right_additive P (∏ i, L i) D w s t hP hL hD hrel]
  ring

/-- Every common outside factor cancels at a shared slot. The remaining
incoming exponents on the copied branches have opposite signs. -/
theorem transfer_outside_row {p : ℕ} [Fact p.Prime]
    (P L R D v w s t : ZMod p) (νv νw C SL SR : ℂ)
    (hP : P ≠ 0) (hL : L ≠ 0) (hR : R ≠ 0) (hD : D ≠ 0)
    (hC : ‖C‖ = 1) (hrel : v * R - w * L = s * P) :
    (ZMod.stdAddChar (t * (v / (P * L * D))) * νv * C * SL) *
      conj (ZMod.stdAddChar (t * (w / (P * R * D))) * νw * C * SR) =
    ZMod.stdAddChar (t * (s / (L * R * D))) * (νv * conj νw) * SL * conj SR := by
  have hCC : C * conj C = 1 := by
    rw [Complex.mul_conj', hC]
    norm_num
  simp only [map_mul (starRingEnd ℂ)]
  calc
    _ = (ZMod.stdAddChar (t * (v / (P * L * D))) *
        conj (ZMod.stdAddChar (t * (w / (P * R * D))))) *
        (νv * conj νw) * (C * conj C) * SL * conj SR := by ring
    _ = _ := by
      rw [transfer_outside_additive P L R D v w s t hP hL hR hD hrel, hCC, mul_one]

/-- Left and right rows separate, while each shared outside row is paired
before its product is taken. -/
theorem transfer_phase_product {H Y : Type*} [Fintype H] [Fintype Y]
    (left right : H → ℂ) (outLeft outRight : Y → ℂ) :
    ((∏ h, left h) * ∏ y, outLeft y) * conj ((∏ h, right h) * ∏ y, outRight y) =
      (∏ h, left h) * (∏ h, conj (right h)) * ∏ y, outLeft y * conj (outRight y) := by
  rw [map_mul, map_prod, map_prod, Finset.prod_mul_distrib]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferGraphRows
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The row products of the actual transferred directed graph -/

namespace Ostmann

open scoped BigOperators

/-- This is the full left row, including the harmless zero diagonal
exponent. The cross-copy row is exactly the old incoming pivot column. -/
theorem transferredGraph_left_row {H Y : Type*} [Fintype H] [Fintype Y]
    {p : ℕ} (χ : DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (L R : H → ZMod p) (U : Y → ZMod p) (h : H) :
    (∏ j, χ (transferredLabels L R U j) ^ transferredGraph b (.inl (true, h)) j) =
      (∏ k, χ (L k) ^ b (some (.inl h)) (some (.inl k))) *
      (∏ k, χ (R k) ^ b (some (.inl h)) none) *
      (∏ y, χ (U y) ^ b (some (.inl h)) (some (.inr y))) := by
  rw [Fintype.prod_sum_type, Fintype.prod_prod_type, Fintype.prod_bool]
  simp only [transferredLabels, transferredGraph, transferCopySign, ite_true, if_true,
    Bool.true_eq_false, ite_false, if_false, one_mul]

/-- The conjugated right row has precisely the negated same-copy and
incoming-pivot exponents. -/
theorem transferredGraph_right_row {H Y : Type*} [Fintype H] [Fintype Y]
    {p : ℕ} (χ : DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (L R : H → ZMod p) (U : Y → ZMod p) (h : H) :
    (∏ j, χ (transferredLabels L R U j) ^ transferredGraph b (.inl (false, h)) j) =
      (∏ k, χ (L k) ^ (-b (some (.inl h)) none)) *
      (∏ k, χ (R k) ^ (-b (some (.inl h)) (some (.inl k)))) *
      (∏ y, χ (U y) ^ (-b (some (.inl h)) (some (.inr y)))) := by
  rw [Fintype.prod_sum_type, Fintype.prod_prod_type, Fintype.prod_bool]
  simp only [transferredLabels, transferredGraph, transferCopySign, ite_true, if_true,
    Bool.false_eq_true, ite_false, if_false, neg_one_mul]

/-- Shared outside rows lose every shared-to-shared edge. -/
theorem transferredGraph_outside_row {H Y : Type*} [Fintype H] [Fintype Y]
    {p : ℕ} (χ : DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (L R : H → ZMod p) (U : Y → ZMod p) (y : Y) :
    (∏ j, χ (transferredLabels L R U j) ^ transferredGraph b (.inr y) j) =
      (∏ k, χ (L k) ^ b (some (.inr y)) (some (.inl k))) *
      (∏ k, χ (R k) ^ (-b (some (.inr y)) (some (.inl k)))) := by
  rw [Fintype.prod_sum_type, Fintype.prod_prod_type, Fintype.prod_bool]
  simp only [transferredLabels, transferredGraph, transferCopySign, ite_true, if_true,
    Bool.false_eq_true, ite_false, if_false, one_mul, neg_one_mul, zpow_zero, Finset.prod_const_one, mul_one]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferGraphPhase
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identification of every surviving local factor with the new graph phase -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

/-- The complete retained factor at a left-slot prime becomes the left
local factor of the updated directed graph. -/
theorem transfer_left_graph_factor {H Y : Type*} [Fintype H] [Fintype Y]
    {p : ℕ} [Fact p.Prime] (χ : DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ) (h : H)
    (P D v s t : ZMod p) (L R : H → ZMod p) (U : Y → ZMod p) (ν : ℂ)
    (hP : P ≠ 0) (hD : D ≠ 0) (hR : (∏ k, R k) ≠ 0) (hs : s ≠ 0)
    (hrel : v * (∏ k, R k) = s * P) :
    ZMod.stdAddChar (t * (v / (P * D))) * ν *
      retainedGraphRow χ b (.inl h) P (Sum.elim L U) =
    ZMod.stdAddChar (t * (s / ((∏ k, R k) * D))) *
      (ν * χ (v / s) ^ b (some (.inl h)) none) *
      updatedGraphRow χ b (.inl (true, h)) L R U := by
  unfold retainedGraphRow updatedGraphRow
  rw [Fintype.prod_sum_type, transferredGraph_left_row]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have he := transfer_left_row χ P D v s t R ν
    (∏ k, χ (L k) ^ b (some (.inl h)) (some (.inl k)))
    (∏ y, χ (U y) ^ b (some (.inl h)) (some (.inr y)))
    (b (some (.inl h)) none) hP hD hR hs hrel
  calc
    _ = ZMod.stdAddChar (t * (v / (P * D))) * ν * χ P ^ b (some (.inl h)) none *
        (∏ k, χ (L k) ^ b (some (.inl h)) (some (.inl k))) *
        ∏ y, χ (U y) ^ b (some (.inl h)) (some (.inr y)) := by ring
    _ = _ := by rw [he]; ring

theorem transfer_right_graph_factor {H Y : Type*} [Fintype H] [Fintype Y]
    {p : ℕ} [Fact p.Prime] (χ : DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ) (h : H)
    (P D w s t : ZMod p) (L R : H → ZMod p) (U : Y → ZMod p) (ν : ℂ)
    (hP : P ≠ 0) (hD : D ≠ 0) (hL : (∏ k, L k) ≠ 0) (hs : s ≠ 0)
    (hrel : -w * (∏ k, L k) = s * P) :
    conj (ZMod.stdAddChar (t * (w / (P * D))) * ν *
      retainedGraphRow χ b (.inl h) P (Sum.elim R U)) =
    ZMod.stdAddChar (t * (s / ((∏ k, L k) * D))) *
      (conj ν * χ (-w / s) ^ (-b (some (.inl h)) none)) *
      updatedGraphRow χ b (.inl (false, h)) L R U := by
  unfold retainedGraphRow updatedGraphRow
  rw [Fintype.prod_sum_type, transferredGraph_right_row]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have he := transfer_right_row χ P D w s t L ν
    (∏ k, χ (R k) ^ b (some (.inl h)) (some (.inl k)))
    (∏ y, χ (U y) ^ b (some (.inl h)) (some (.inr y)))
    (b (some (.inl h)) none) hP hD hL hs hrel
  calc
    _ = conj (ZMod.stdAddChar (t * (w / (P * D))) * ν * χ P ^ b (some (.inl h)) none *
        (∏ k, χ (R k) ^ b (some (.inl h)) (some (.inl k))) *
        ∏ y, χ (U y) ^ b (some (.inl h)) (some (.inr y))) := by congr 1; ring
    _ = _ := by
      rw [he]
      simp only [map_prod (starRingEnd ℂ), conjugate_character_power]
      ring

/-- The common outside row has unit modulus on the actual coprime support;
the self-edge is allowed because its exponent is zero. -/
theorem transfer_common_row_norm_one {H Y : Type*} [Fintype H] [Fintype Y]
    {p : ℕ} (χ : DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ) (y : Y)
    (P : ZMod p) (U : Y → ZMod p) (hP : IsUnit P)
    (hU : ∀ z, z ≠ y → IsUnit (U z)) (hb : b (some (.inr y)) (some (.inr y)) = 0) :
    ‖χ P ^ b (some (.inr y)) none *
      ∏ z, χ (U z) ^ b (some (.inr y)) (some (.inr z))‖ = 1 := by
  classical
  obtain ⟨u, hu⟩ := hP
  rw [norm_mul, ← hu, norm_zpow, χ.unit_norm_eq_one, one_zpow, one_mul, norm_prod]
  apply Finset.prod_eq_one
  intro z _
  by_cases hz : z = y
  · subst z
    rw [hb, zpow_zero, norm_one]
  · obtain ⟨a, ha⟩ := hU z hz
    rw [← ha, norm_zpow, χ.unit_norm_eq_one, one_zpow]

/-- The shared-slot row cancels its entire common part. Its new incoming
powers are exactly those prescribed by `transferredGraph`. -/
theorem transfer_outside_graph_factor {H Y : Type*} [Fintype H] [Fintype Y]
    {p : ℕ} [Fact p.Prime] (χ : DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ) (y : Y)
    (P LP RP D v w s t : ZMod p) (L R : H → ZMod p) (U : Y → ZMod p)
    (νv νw : ℂ) (hP : P ≠ 0) (hL : LP ≠ 0) (hR : RP ≠ 0) (hD : D ≠ 0)
    (hcommon : ‖χ P ^ b (some (.inr y)) none *
      ∏ z, χ (U z) ^ b (some (.inr y)) (some (.inr z))‖ = 1)
    (hrel : v * RP - w * LP = s * P) :
    (ZMod.stdAddChar (t * (v / (P * LP * D))) * νv *
      retainedGraphRow χ b (.inr y) P (Sum.elim L U)) *
      conj (ZMod.stdAddChar (t * (w / (P * RP * D))) * νw *
        retainedGraphRow χ b (.inr y) P (Sum.elim R U)) =
    ZMod.stdAddChar (t * (s / (LP * RP * D))) * (νv * conj νw) *
      updatedGraphRow χ b (.inr y) L R U := by
  unfold retainedGraphRow updatedGraphRow
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, transferredGraph_outside_row]
  simp only [Sum.elim_inl, Sum.elim_inr]
  let C := χ P ^ b (some (.inr y)) none *
    ∏ z, χ (U z) ^ b (some (.inr y)) (some (.inr z))
  let SL := ∏ k, χ (L k) ^ b (some (.inr y)) (some (.inl k))
  let SR := ∏ k, χ (R k) ^ b (some (.inr y)) (some (.inl k))
  have he := transfer_outside_row P LP RP D v w s t νv νw C SL SR hP hL hR hD hcommon hrel
  calc
    _ = (ZMod.stdAddChar (t * (v / (P * LP * D))) * νv * C * SL) *
        conj (ZMod.stdAddChar (t * (w / (P * RP * D))) * νw * C * SR) := by
      dsimp [C, SL, SR]
      apply congrArg₂ (fun a b : ℂ => a * conj b) <;> ring
    _ = _ := by
      rw [he]
      dsimp [SL, SR]
      simp only [map_prod (starRingEnd ℂ), conjugate_character_power]
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferTupleCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact product and cofactor coordinates for the copied prime list -/

namespace Ostmann

open scoped BigOperators

theorem transferredLabels_prod {H Y : Type*} [Fintype H] [Fintype Y]
    (L R : H → ℕ) (U : Y → ℕ) :
    (∏ i, transferredLabels L R U i) = (∏ h, L h) * (∏ h, R h) * (∏ y, U y) := by
  rw [Fintype.prod_sum_type, Fintype.prod_prod_type, Fintype.prod_bool]
  rfl

theorem tupleCofactor_transferred_left {H Y : Type*} [Fintype H] [Fintype Y]
    (L R : H → ℕ) (U : Y → ℕ) (h : H) (hL : L h ≠ 0) :
    tupleCofactor (transferredLabels L R U) (.inl (true, h)) =
      tupleCofactor L h * (∏ k, R k) * ∏ y, U y := by
  apply mul_left_cancel₀ hL
  calc
    _ = ∏ i, transferredLabels L R U i := tupleCofactor_mul _ (.inl (true, h))
    _ = (∏ k, L k) * (∏ k, R k) * ∏ y, U y := transferredLabels_prod L R U
    _ = (L h * tupleCofactor L h) * (∏ k, R k) * ∏ y, U y := by rw [tupleCofactor_mul]
    _ = _ := by ring

theorem tupleCofactor_transferred_right {H Y : Type*} [Fintype H] [Fintype Y]
    (L R : H → ℕ) (U : Y → ℕ) (h : H) (hR : R h ≠ 0) :
    tupleCofactor (transferredLabels L R U) (.inl (false, h)) =
      (∏ k, L k) * tupleCofactor R h * ∏ y, U y := by
  apply mul_left_cancel₀ hR
  calc
    _ = ∏ i, transferredLabels L R U i := tupleCofactor_mul _ (.inl (false, h))
    _ = (∏ k, L k) * (∏ k, R k) * ∏ y, U y := transferredLabels_prod L R U
    _ = (∏ k, L k) * (R h * tupleCofactor R h) * ∏ y, U y := by rw [tupleCofactor_mul]
    _ = _ := by ring

theorem tupleCofactor_transferred_outside {H Y : Type*} [Fintype H] [Fintype Y]
    (L R : H → ℕ) (U : Y → ℕ) (y : Y) (hU : U y ≠ 0) :
    tupleCofactor (transferredLabels L R U) (.inr y) =
      (∏ h, L h) * (∏ h, R h) * tupleCofactor U y := by
  apply mul_left_cancel₀ hU
  calc
    _ = ∏ i, transferredLabels L R U i := tupleCofactor_mul _ (.inr y)
    _ = (∏ k, L k) * (∏ k, R k) * ∏ y, U y := transferredLabels_prod L R U
    _ = (∏ k, L k) * (∏ k, R k) * (U y * tupleCofactor U y) := by rw [tupleCofactor_mul]
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferAdditiveProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete additive phase after a transfer, on the actual prime list -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

section
variable {H Y : Type*} [Fintype H] [Fintype Y]
variable (L R : H → ℕ) (U : Y → ℕ)
variable [∀ h, Fact (L h).Prime] [∀ h, Fact (R h).Prime] [∀ y, Fact (U y).Prime]

theorem transfer_additive_product (t : ∀ p : ℕ, ZMod p) (M : ℕ) (v w s : ℤ)
    (hrel : v * (∏ h, R h) - w * (∏ h, L h) = s * M)
    (hLeft : ∀ h, M.Coprime (L h) ∧ (∏ k, R k).Coprime (L h) ∧
      (tupleCofactor L h * ∏ y, U y).Coprime (L h))
    (hRight : ∀ h, M.Coprime (R h) ∧ (∏ k, L k).Coprime (R h) ∧
      (tupleCofactor R h * ∏ y, U y).Coprime (R h))
    (hOutside : ∀ y, M.Coprime (U y) ∧ (∏ h, L h).Coprime (U y) ∧
      (∏ h, R h).Coprime (U y) ∧ (tupleCofactor U y).Coprime (U y)) :
    ((∏ h, ZMod.stdAddChar (t (L h) * ((v : ZMod (L h)) /
          ((M * (tupleCofactor L h * ∏ y, U y) : ℕ) : ZMod (L h))))) *
      ∏ y, ZMod.stdAddChar (t (U y) * ((v : ZMod (U y)) /
          ((M * (∏ h, L h) * tupleCofactor U y : ℕ) : ZMod (U y))))) *
      conj ((∏ h, ZMod.stdAddChar (t (R h) * ((w : ZMod (R h)) /
          ((M * (tupleCofactor R h * ∏ y, U y) : ℕ) : ZMod (R h))))) *
        ∏ y, ZMod.stdAddChar (t (U y) * ((w : ZMod (U y)) /
          ((M * (∏ h, R h) * tupleCofactor U y : ℕ) : ZMod (U y))))) =
    ∏ i, transferredAdditiveRow L R U t s i := by
  have hL (h : H) : ZMod.stdAddChar (t (L h) * ((v : ZMod (L h)) /
        ((M * (tupleCofactor L h * ∏ y, U y) : ℕ) : ZMod (L h)))) =
      transferredAdditiveRow L R U t s (.inl (true, h)) := by
    have he := transfer_left_additive_integer (L := ∏ k, L k) (R := ∏ k, R k)
      (M := M) (D := tupleCofactor L h * ∏ y, U y) v w s (t (L h))
      (Finset.dvd_prod_of_mem L (Finset.mem_univ h))
      (hLeft h).1 (hLeft h).2.1 (hLeft h).2.2 hrel
    simpa only [Nat.cast_mul, transferredAdditiveRow,
      tupleCofactor_transferred_left L R U h (Fact.out : (L h).Prime).ne_zero,
      mul_assoc, mul_left_comm, mul_comm] using he
  have hR (h : H) : conj (ZMod.stdAddChar (t (R h) * ((w : ZMod (R h)) /
        ((M * (tupleCofactor R h * ∏ y, U y) : ℕ) : ZMod (R h))))) =
      transferredAdditiveRow L R U t s (.inl (false, h)) := by
    have he := transfer_right_additive_integer (L := ∏ k, L k) (R := ∏ k, R k)
      (M := M) (D := tupleCofactor R h * ∏ y, U y) v w s (t (R h))
      (Finset.dvd_prod_of_mem R (Finset.mem_univ h))
      (hRight h).1 (hRight h).2.1 (hRight h).2.2 hrel
    simpa only [Nat.cast_mul, transferredAdditiveRow, Complex.star_def,
      tupleCofactor_transferred_right L R U h (Fact.out : (R h).Prime).ne_zero,
      mul_assoc, mul_left_comm, mul_comm] using he
  have hY (y : Y) :
      ZMod.stdAddChar (t (U y) * ((v : ZMod (U y)) /
        ((M * (∏ h, L h) * tupleCofactor U y : ℕ) : ZMod (U y)))) *
      conj (ZMod.stdAddChar (t (U y) * ((w : ZMod (U y)) /
        ((M * (∏ h, R h) * tupleCofactor U y : ℕ) : ZMod (U y))))) =
      transferredAdditiveRow L R U t s (.inr y) := by
    have he := transfer_outside_additive (M : ZMod (U y)) (∏ h, L h : ℕ) (∏ h, R h : ℕ)
      (tupleCofactor U y) v w s (t (U y))
      (zmod_natCast_ne_zero_of_coprime M (hOutside y).1)
      (zmod_natCast_ne_zero_of_coprime _ (hOutside y).2.1)
      (zmod_natCast_ne_zero_of_coprime _ (hOutside y).2.2.1)
      (zmod_natCast_ne_zero_of_coprime _ (hOutside y).2.2.2)
      (transfer_equation_mod_outside (U y) (∏ h, L h) (∏ h, R h) M v w s hrel)
    simpa only [Nat.cast_mul, Int.cast_natCast, transferredAdditiveRow,
      tupleCofactor_transferred_outside L R U y (Fact.out : (U y).Prime).ne_zero] using he
  rw [transfer_phase_product, Fintype.prod_sum_type, Fintype.prod_prod_type, Fintype.prod_bool]
  rw [show (∏ h, ZMod.stdAddChar (t (L h) * ((v : ZMod (L h)) /
        ((M * (tupleCofactor L h * ∏ y, U y) : ℕ) : ZMod (L h))))) =
      ∏ h, transferredAdditiveRow L R U t s (.inl (true, h)) by
        exact Finset.prod_congr rfl (fun h _ => hL h)]
  rw [show (∏ h, conj (ZMod.stdAddChar (t (R h) * ((w : ZMod (R h)) /
        ((M * (tupleCofactor R h * ∏ y, U y) : ℕ) : ZMod (R h)))))) =
      ∏ h, transferredAdditiveRow L R U t s (.inl (false, h)) by
        exact Finset.prod_congr rfl (fun h _ => hR h)]
  congr 1
  exact Finset.prod_congr rfl (fun y _ => hY y)

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferTupleSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local denominator units from the actual output tuple's coprimality -/

namespace Ostmann

open scoped BigOperators

theorem transferred_left_denominators {H Y : Type*} [Fintype H] [Fintype Y]
    (L R : H → ℕ) (U : Y → ℕ)
    (hc : Pairwise (fun i j => (transferredLabels L R U i).Coprime (transferredLabels L R U j)))
    (h : H) : (∏ k, R k).Coprime (L h) ∧
      (tupleCofactor L h * ∏ y, U y).Coprime (L h) := by
  have hR : (L h).Coprime (∏ k, R k) := Nat.coprime_prod_right_iff.mpr (by
    intro k _
    exact @hc (.inl (true, h)) (.inl (false, k)) (by simp))
  have hU : (L h).Coprime (∏ y, U y) := Nat.coprime_prod_right_iff.mpr (by
    intro y _
    exact @hc (.inl (true, h)) (.inr y) (by simp))
  have hL : Pairwise (fun h k => (L h).Coprime (L k)) := by
    intro h k hhk
    exact @hc (.inl (true, h)) (.inl (true, k)) (by simpa using hhk)
  exact ⟨hR.symm, (tupleCofactor_coprime L hL h).mul_left hU.symm⟩

theorem transferred_right_denominators {H Y : Type*} [Fintype H] [Fintype Y]
    (L R : H → ℕ) (U : Y → ℕ)
    (hc : Pairwise (fun i j => (transferredLabels L R U i).Coprime (transferredLabels L R U j)))
    (h : H) : (∏ k, L k).Coprime (R h) ∧
      (tupleCofactor R h * ∏ y, U y).Coprime (R h) := by
  have hL : (R h).Coprime (∏ k, L k) := Nat.coprime_prod_right_iff.mpr (by
    intro k _
    exact @hc (.inl (false, h)) (.inl (true, k)) (by simp))
  have hU : (R h).Coprime (∏ y, U y) := Nat.coprime_prod_right_iff.mpr (by
    intro y _
    exact @hc (.inl (false, h)) (.inr y) (by simp))
  have hR : Pairwise (fun h k => (R h).Coprime (R k)) := by
    intro h k hhk
    exact @hc (.inl (false, h)) (.inl (false, k)) (by simpa using hhk)
  exact ⟨hL.symm, (tupleCofactor_coprime R hR h).mul_left hU.symm⟩

theorem transferred_outside_denominators {H Y : Type*} [Fintype H] [Fintype Y]
    (L R : H → ℕ) (U : Y → ℕ)
    (hc : Pairwise (fun i j => (transferredLabels L R U i).Coprime (transferredLabels L R U j)))
    (y : Y) : (∏ h, L h).Coprime (U y) ∧ (∏ h, R h).Coprime (U y) ∧
      (tupleCofactor U y).Coprime (U y) := by
  have hL : (U y).Coprime (∏ h, L h) := Nat.coprime_prod_right_iff.mpr (by
    intro h _
    exact @hc (.inr y) (.inl (true, h)) (by simp))
  have hR : (U y).Coprime (∏ h, R h) := Nat.coprime_prod_right_iff.mpr (by
    intro h _
    exact @hc (.inr y) (.inl (false, h)) (by simp))
  have hU : Pairwise (fun y z => (U y).Coprime (U z)) := by
    intro y z hyz
    exact @hc (.inr y) (.inr z) (by simpa using hyz)
  exact ⟨hL.symm, hR.symm, tupleCofactor_coprime U hU y⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferCharacterProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete multiplicative phase and unary update on actual prime lists -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

section
variable {H Y : Type*} [Fintype H] [Fintype Y]
variable (L R : H → ℕ) (U : Y → ℕ)
variable [∀ h, Fact (L h).Prime] [∀ h, Fact (R h).Prime] [∀ y, Fact (U y).Prime]

theorem transfer_character_product
    (χH : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χY : Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (νL νR : H → ℂ) (νYL νYR : Y → ℂ) (M : ℕ) (v w s : ℤ)
    (hrel : v * (∏ h, R h) - w * (∏ h, L h) = s * M)
    (hc : Pairwise (fun i j => (transferredLabels L R U i).Coprime (transferredLabels L R U j)))
    (hM : ∀ i, M.Coprime (transferredLabels L R U i))
    (hs : ∀ i, IsUnit (s : ZMod (transferredLabels L R U i)))
    (hb : ∀ y, b (some (.inr y)) (some (.inr y)) = 0) :
    ((∏ h, νL h * retainedGraphRow (χH h (L h)) b (.inl h) (M : ZMod (L h))
        (Sum.elim (fun k => (L k : ZMod (L h))) (fun y => (U y : ZMod (L h))))) *
      ∏ y, νYL y * retainedGraphRow (χY y (U y)) b (.inr y) (M : ZMod (U y))
        (Sum.elim (fun k => (L k : ZMod (U y))) (fun z => (U z : ZMod (U y))))) *
      conj ((∏ h, νR h * retainedGraphRow (χH h (R h)) b (.inl h) (M : ZMod (R h))
        (Sum.elim (fun k => (R k : ZMod (R h))) (fun y => (U y : ZMod (R h))))) *
        ∏ y, νYR y * retainedGraphRow (χY y (U y)) b (.inr y) (M : ZMod (U y))
          (Sum.elim (fun k => (R k : ZMod (U y))) (fun z => (U z : ZMod (U y))))) =
    ∏ i, transferredCharacterFactor L R U χH χY b νL νR νYL νYR v w s i := by
  have hL (h : H) : νL h * retainedGraphRow (χH h (L h)) b (.inl h) (M : ZMod (L h))
      (Sum.elim (fun k => (L k : ZMod (L h))) (fun y => (U y : ZMod (L h)))) =
      transferredCharacterFactor L R U χH χY b νL νR νYL νYR v w s (.inl (true, h)) := by
    have he := transfer_left_graph_factor (χH h (L h)) b h (M : ZMod (L h)) 1 v s 0
      (fun k => (L k : ZMod (L h))) (fun k => (R k : ZMod (L h)))
      (fun y => (U y : ZMod (L h))) (νL h)
      (zmod_natCast_ne_zero_of_coprime M (hM (.inl (true, h)))) one_ne_zero
      (by simpa only [← Nat.cast_prod] using (zmod_natCast_ne_zero_of_coprime (p := L h)
        (∏ k, R k) (transferred_left_denominators L R U hc h).1))
      (isUnit_iff_ne_zero.mp (hs (.inl (true, h))))
      (by simpa only [← Nat.cast_prod] using (transfer_equation_mod_left (L h)
        (∏ k, L k) (∏ k, R k) M v w s (Finset.dvd_prod_of_mem L (Finset.mem_univ h)) hrel))
    simpa only [zero_mul, AddChar.map_zero_eq_one, one_mul, transferredCharacterFactor] using he
  have hR (h : H) : conj (νR h * retainedGraphRow (χH h (R h)) b (.inl h) (M : ZMod (R h))
      (Sum.elim (fun k => (R k : ZMod (R h))) (fun y => (U y : ZMod (R h))))) =
      transferredCharacterFactor L R U χH χY b νL νR νYL νYR v w s (.inl (false, h)) := by
    have he := transfer_right_graph_factor (χH h (R h)) b h (M : ZMod (R h)) 1 w s 0
      (fun k => (L k : ZMod (R h))) (fun k => (R k : ZMod (R h)))
      (fun y => (U y : ZMod (R h))) (νR h)
      (zmod_natCast_ne_zero_of_coprime M (hM (.inl (false, h)))) one_ne_zero
      (by simpa only [← Nat.cast_prod] using (zmod_natCast_ne_zero_of_coprime (p := R h)
        (∏ k, L k) (transferred_right_denominators L R U hc h).1))
      (isUnit_iff_ne_zero.mp (hs (.inl (false, h))))
      (by simpa only [← Nat.cast_prod] using (transfer_equation_mod_right (R h)
        (∏ k, L k) (∏ k, R k) M v w s (Finset.dvd_prod_of_mem R (Finset.mem_univ h)) hrel))
    simpa only [zero_mul, AddChar.map_zero_eq_one, one_mul, transferredCharacterFactor] using he
  have hY (y : Y) :
      (νYL y * retainedGraphRow (χY y (U y)) b (.inr y) (M : ZMod (U y))
        (Sum.elim (fun k => (L k : ZMod (U y))) (fun z => (U z : ZMod (U y))))) *
      conj (νYR y * retainedGraphRow (χY y (U y)) b (.inr y) (M : ZMod (U y))
        (Sum.elim (fun k => (R k : ZMod (U y))) (fun z => (U z : ZMod (U y))))) =
      transferredCharacterFactor L R U χH χY b νL νR νYL νYR v w s (.inr y) := by
    have hcommon := transfer_common_row_norm_one (χY y (U y)) b y (M : ZMod (U y))
      (fun z => (U z : ZMod (U y))) ((ZMod.isUnit_iff_coprime M (U y)).mpr (hM (.inr y)))
      (fun z hz => (ZMod.isUnit_iff_coprime (U z) (U y)).mpr
        (@hc (.inr z) (.inr y) (by simpa using hz))) (hb y)
    have he := transfer_outside_graph_factor (χY y (U y)) b y (M : ZMod (U y))
      (∏ h, L h : ℕ) (∏ h, R h : ℕ) 1 v w s 0
      (fun k => (L k : ZMod (U y))) (fun k => (R k : ZMod (U y)))
      (fun z => (U z : ZMod (U y))) (νYL y) (νYR y)
      (zmod_natCast_ne_zero_of_coprime M (hM (.inr y)))
      (zmod_natCast_ne_zero_of_coprime _ (transferred_outside_denominators L R U hc y).1)
      (zmod_natCast_ne_zero_of_coprime _ (transferred_outside_denominators L R U hc y).2.1)
      one_ne_zero hcommon
      (transfer_equation_mod_outside (U y) (∏ h, L h) (∏ h, R h) M v w s hrel)
    simpa only [zero_mul, AddChar.map_zero_eq_one, one_mul, transferredCharacterFactor] using he
  rw [transfer_phase_product, Fintype.prod_sum_type, Fintype.prod_prod_type, Fintype.prod_bool]
  rw [show (∏ h, νL h * retainedGraphRow (χH h (L h)) b (.inl h) (M : ZMod (L h))
      (Sum.elim (fun k => (L k : ZMod (L h))) (fun y => (U y : ZMod (L h))))) =
      ∏ h, transferredCharacterFactor L R U χH χY b νL νR νYL νYR v w s (.inl (true, h))
      by exact Finset.prod_congr rfl (fun h _ => hL h)]
  rw [show (∏ h, conj (νR h * retainedGraphRow (χH h (R h)) b (.inl h) (M : ZMod (R h))
      (Sum.elim (fun k => (R k : ZMod (R h))) (fun y => (U y : ZMod (R h)))))) =
      ∏ h, transferredCharacterFactor L R U χH χY b νL νR νYL νYR v w s (.inl (false, h))
      by exact Finset.prod_congr rfl (fun h _ => hR h)]
  congr 1
  exact Finset.prod_congr rfl (fun y _ => hY y)

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferCompletePhase
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full transfer phase identity on the actual copied tuple -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

/-- This identifies the entire off-diagonal phase, after removal of the
pivot's outgoing row. Its output is the actual directed graph update, with
all additive cofactors and new unary factors included. -/
theorem transfer_complete_phase {H Y : Type*} [Fintype H] [Fintype Y]
    (L R : H → ℕ) (U : Y → ℕ)
    [∀ h, Fact (L h).Prime] [∀ h, Fact (R h).Prime] [∀ y, Fact (U y).Prime]
    (t : ∀ p : ℕ, ZMod p)
    (χH : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χY : Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (νL νR : H → ℂ) (νYL νYR : Y → ℂ) (M : ℕ) (v w s : ℤ)
    (hrel : v * (∏ h, R h) - w * (∏ h, L h) = s * M)
    (hc : Pairwise (fun i j => (transferredLabels L R U i).Coprime (transferredLabels L R U j)))
    (hM : ∀ i, M.Coprime (transferredLabels L R U i))
    (hs : ∀ i, IsUnit (s : ZMod (transferredLabels L R U i)))
    (hb : ∀ y, b (some (.inr y)) (some (.inr y)) = 0) :
    retainedPrimePhase L U t χH χY b νL νYL M v *
      conj (retainedPrimePhase R U t χH χY b νR νYR M w) =
    ∏ i, transferredAdditiveRow L R U t s i *
      transferredCharacterFactor L R U χH χY b νL νR νYL νYR v w s i := by
  have hA := transfer_additive_product L R U t M v w s hrel
    (fun h => ⟨hM (.inl (true, h)), transferred_left_denominators L R U hc h⟩)
    (fun h => ⟨hM (.inl (false, h)), transferred_right_denominators L R U hc h⟩)
    (fun y => ⟨hM (.inr y), transferred_outside_denominators L R U hc y⟩)
  change retainedAdditiveBranch L U t M v * conj (retainedAdditiveBranch R U t M w) = _ at hA
  have hC := transfer_character_product L R U χH χY b νL νR νYL νYR M v w s hrel hc hM hs hb
  change retainedCharacterBranch L U χH χY b νL νYL M *
    conj (retainedCharacterBranch R U χH χY b νR νYR M) = _ at hC
  unfold retainedPrimePhase
  rw [map_mul (starRingEnd ℂ)]
  calc
    _ = (retainedAdditiveBranch L U t M v * conj (retainedAdditiveBranch R U t M w)) *
        (retainedCharacterBranch L U χH χY b νL νYL M *
          conj (retainedCharacterBranch R U χH χY b νR νYR M)) := by ring
    _ = _ := by rw [hA, hC, Finset.prod_mul_distrib]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GroupedPivotPhase
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing every constituent of a grouped pivot from the directed phase -/

namespace Ostmann

open scoped BigOperators Classical

/-- A regular outgoing row includes the cofactor, with its diagonal omitted. -/
theorem regular_prime_row_product {I : Type*} [Fintype I] (p : I → ℕ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (b : I → I → ℤ) (i : I) (ε : ℤ)
    (hself : b i i = 0) (hrow : ∀ j, j ≠ i → b i j = ε) :
    (∏ j, χ (p j : ZMod q) ^ b i j) = χ (tupleCofactor p i : ZMod q) ^ ε := by
  rw [← Finset.mul_prod_erase Finset.univ (fun j => χ (p j : ZMod q) ^ b i j)
    (Finset.mem_univ i), hself, zpow_zero, one_mul]
  simp only [tupleCofactor, Nat.cast_prod, map_prod]
  rw [← Finset.prod_zpow]
  exact Finset.prod_congr rfl (fun j hj => by rw [hrow j (Finset.mem_erase.mp hj).1])

/-- The incoming exponents are constant over all prime constituents of a pivot.
Thus their entire contribution uses only the product of those primes. -/
theorem grouped_incoming_row {K I : Type*} [Fintype K] [Fintype I]
    (P : K → ℕ) (Q : I → ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (g : (K ⊕ I) → (K ⊕ I) → ℤ)
    (b : Option I → Option I → ℤ) (i : I)
    (hpivot : ∀ k, g (.inr i) (.inl k) = b (some i) none)
    (hrest : ∀ j, g (.inr i) (.inr j) = b (some i) (some j)) :
    (∏ j, χ ((Sum.elim P Q j : ℕ) : ZMod q) ^ g (.inr i) j) =
      retainedGraphRow χ b i ((∏ k, P k : ℕ) : ZMod q)
        (fun j => (Q j : ZMod q)) := by
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, hpivot, hrest, retainedGraphRow]
  rw [Nat.cast_prod, character_product_power]

/-- Literal partition of the full directed phase. No cancellation or estimate
is assumed: every incoming pivot edge remains in the retained phase. -/
theorem directedPrimePhase_remove_grouped_pivot {K I : Type*} [Fintype K] [Fintype I]
    (p : K ⊕ I → ℕ) [∀ j, NeZero (p j)]
    (χ : ∀ j, DirichletCharacter ℂ (p j))
    (t : ∀ j, ZMod (p j)) (ν : (K ⊕ I) → ℂ)
    (g : (K ⊕ I) → (K ⊕ I) → ℤ) (b : Option I → Option I → ℤ)
    (ε : K → ℤ) (v : ℤ)
    (hself : ∀ k, g (.inl k) (.inl k) = 0)
    (hrow : ∀ k j, j ≠ .inl k → g (.inl k) j = ε k)
    (hpivot : ∀ i k, g (.inr i) (.inl k) = b (some i) none)
    (hrest : ∀ i j, g (.inr i) (.inr j) = b (some i) (some j)) :
    directedPrimePhase p χ t ν g v =
      (∏ k, ZMod.stdAddChar (t (.inl k) *
        (((tupleCofactor (fun k => p (.inl k)) k * ∏ i, p (.inr i) : ℕ) :
          ZMod (p (.inl k)))⁻¹ * (v : ZMod (p (.inl k))))) *
        ν (.inl k) *
        χ (.inl k) ((tupleCofactor (fun k => p (.inl k)) k * ∏ i, p (.inr i) : ℕ) :
          ZMod (p (.inl k))) ^ ε k) *
      retainedGroupedPhase (fun i => p (.inr i)) (fun i => χ (.inr i))
        (fun i => t (.inr i)) (fun i => ν (.inr i)) b (∏ k, p (.inl k)) v := by
  have hp : p = Sum.elim (fun k => p (.inl k)) (fun i => p (.inr i)) := by
    funext j
    cases j <;> rfl
  have hcoP (k : K) : tupleCofactor p (.inl k) =
      tupleCofactor (fun k => p (.inl k)) k * ∏ i, p (.inr i) := by
    conv_lhs => rw [hp]
    exact tupleCofactor_sum_left _ _ k (NeZero.ne _)
  have hcoQ (i : I) : tupleCofactor p (.inr i) =
      (∏ k, p (.inl k)) * tupleCofactor (fun i => p (.inr i)) i := by
    conv_lhs => rw [hp]
    exact tupleCofactor_sum_right _ _ i (NeZero.ne _)
  rw [directedPrimePhase, Fintype.prod_sum_type]
  congr 1
  · apply Finset.prod_congr rfl
    intro k _
    rw [regular_prime_row_product p (χ (.inl k)) g (.inl k) (ε k)
      (hself k) (hrow k), hcoP]
  · unfold retainedGroupedPhase
    apply Finset.prod_congr rfl
    intro i _
    rw [hcoQ]
    congr 1
    convert grouped_incoming_row (fun k => p (.inl k)) (fun j => p (.inr j))
      (χ (.inr i)) g b i (hpivot i) (hrest i) using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.prod_congr rfl
    intro j _
    cases j <;> rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RetainedGroupedPhase
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The retained grouped phase is the phase in the exact copy identity -/

namespace Ostmann

open scoped BigOperators Classical

theorem retainedGroupedPhase_split {H Y : Type*} [Fintype H] [Fintype Y]
    (q : H ⊕ Y → ℕ) [∀ i, Fact (q i).Prime]
    (χ : (H ⊕ Y) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (t : ∀ p : ℕ, ZMod p) (ν : H ⊕ Y → ℂ)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ) (M : ℕ) (v : ℤ) :
    retainedGroupedPhase q (fun i => χ i (q i)) (fun i => t (q i)) ν b M v =
      retainedPrimePhase (fun h => q (.inl h)) (fun y => q (.inr y)) t
        (fun h => χ (.inl h)) (fun y => χ (.inr y)) b
        (fun h => ν (.inl h)) (fun y => ν (.inr y)) M v := by
  have hq : q = Sum.elim (fun h => q (.inl h)) (fun y => q (.inr y)) := by
    funext i
    cases i <;> rfl
  have hcoH (h : H) : tupleCofactor q (.inl h) =
      tupleCofactor (fun h => q (.inl h)) h * ∏ y, q (.inr y) := by
    conv_lhs => rw [hq]
    exact tupleCofactor_sum_left _ _ h (NeZero.ne _)
  have hcoY (y : Y) : tupleCofactor q (.inr y) =
      (∏ h, q (.inl h)) * tupleCofactor (fun y => q (.inr y)) y := by
    conv_lhs => rw [hq]
    exact tupleCofactor_sum_right _ _ y (NeZero.ne _)
  have henv {p : ℕ} : (fun j => (q j : ZMod p)) =
      Sum.elim (fun h => (q (.inl h) : ZMod p)) (fun y => (q (.inr y) : ZMod p)) := by
    funext j
    cases j <;> rfl
  have hvD {p : ℕ} (D : ZMod p) : D⁻¹ * (v : ZMod p) = (v : ZMod p) * D⁻¹ := mul_comm _ _
  simp only [retainedGroupedPhase, Fintype.prod_sum_type, hcoH, hcoY,
    retainedPrimePhase, retainedAdditiveBranch, retainedCharacterBranch,
    henv, div_eq_mul_inv, hvD, mul_assoc, Finset.prod_mul_distrib]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferDirectedPhase
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The copied local factors form the next actual directed prime phase -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

/-- The previously proved complete transfer identity has exactly the directed
phase maintained by the iteration, with no residual local factors. -/
theorem transfer_directed_phase {H Y : Type*} [Fintype H] [Fintype Y]
    (q : (Bool × H) ⊕ Y → ℕ) [∀ i, Fact (q i).Prime]
    (t : ∀ p : ℕ, ZMod p)
    (χH : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χY : Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (νL νR : H → ℂ) (νYL νYR : Y → ℂ) (M : ℕ) (v w s : ℤ)
    (hrel : v * (∏ h, q (.inl (false, h))) - w * (∏ h, q (.inl (true, h))) = s * M)
    (hc : Pairwise (fun i j => (q i).Coprime (q j)))
    (hM : ∀ i, M.Coprime (q i))
    (hs : ∀ i, IsUnit (s : ZMod (q i)))
    (hb : ∀ y, b (some (.inr y)) (some (.inr y)) = 0) :
    retainedPrimePhase (fun h => q (.inl (true, h))) (fun y => q (.inr y)) t χH χY b
        νL νYL M v *
      conj (retainedPrimePhase (fun h => q (.inl (false, h))) (fun y => q (.inr y))
        t χH χY b νR νYR M w) =
      directedPrimePhase q (fun i => copiedSlotCharacter χH χY i (q i))
        (fun i => t (q i)) (copiedSlotUnary q χH b νL νR νYL νYR v w s)
        (transferredGraph b) s := by
  let L : H → ℕ := fun h => q (.inl (true, h))
  let R : H → ℕ := fun h => q (.inl (false, h))
  let U : Y → ℕ := fun y => q (.inr y)
  have heq : transferredLabels L R U = q := by
    funext i
    rcases i with ⟨b, h⟩ | y
    · cases b <;> rfl
    · rfl
  have hco (i) : tupleCofactor (transferredLabels L R U) i = tupleCofactor q i := by rw [heq]
  have ha (i) : transferredAdditiveRow L R U t s i =
      ZMod.stdAddChar (t (q i) * ((tupleCofactor q i : ZMod (q i))⁻¹ * (s : ZMod (q i)))) := by
    rcases i with ⟨b, h⟩ | y
    · cases b <;> simp only [transferredAdditiveRow, hco, L, R, div_eq_mul_inv, mul_comm]
    · simp only [transferredAdditiveRow, hco, U, div_eq_mul_inv, mul_comm]
  have henv {p : ℕ} : transferredLabels (fun h => (L h : ZMod p))
      (fun h => (R h : ZMod p)) (fun y => (U y : ZMod p)) = (fun i => (q i : ZMod p)) := by
    funext i
    rcases i with ⟨b, h⟩ | y
    · cases b <;> rfl
    · rfl
  have hchar (i) : transferredCharacterFactor L R U χH χY b νL νR νYL νYR v w s i =
      copiedSlotUnary q χH b νL νR νYL νYR v w s i *
        ∏ j, copiedSlotCharacter χH χY i (q i) (q j : ZMod (q i)) ^ transferredGraph b i j := by
    rcases i with ⟨c, h⟩ | y
    · cases c <;> simp only [transferredCharacterFactor, copiedSlotUnary,
        copiedSlotCharacter, updatedGraphRow, henv, L, R]
    · simp only [transferredCharacterFactor, copiedSlotUnary, copiedSlotCharacter,
        updatedGraphRow, henv, U]
  have hcp : Pairwise (fun i j => (transferredLabels L R U i).Coprime
      (transferredLabels L R U j)) := by simpa only [heq] using hc
  have hMp : ∀ i, M.Coprime (transferredLabels L R U i) := by simpa only [heq] using hM
  have hsp : ∀ i, IsUnit (s : ZMod (transferredLabels L R U i)) := by
    intro i
    rcases i with ⟨c, h⟩ | y
    · cases c <;> exact hs _
    · exact hs _
  have ht := transfer_complete_phase L R U t χH χY b νL νR νYL νYR M v w s
    hrel hcp hMp hsp hb
  refine ht.trans ?_
  unfold directedPrimePhase
  apply Finset.prod_congr rfl
  intro i _
  rw [ha, hchar]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferFrequencyRange
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual finite range of a transferred frequency -/

namespace Ostmann

open scoped BigOperators Classical

/-- The product ranges supply the frequency cutoff without rounding a
quotient or introducing an independent frequency assumption. -/
theorem transferred_frequency_bound (M L R B H V : ℕ) (s v w : ℤ)
    (hM : 0 < M) (hv : v.natAbs ≤ B) (hw : w.natAbs ≤ B)
    (hL : L ≤ H) (hR : R ≤ H)
    (hscale : 2 * B * H ≤ V * M)
    (hrel : v * R - w * L = s * M) : s.natAbs ≤ V := by
  have he : s.natAbs * M = (v * R - w * L).natAbs := by
    rw [hrel, Int.natAbs_mul, Int.natAbs_natCast]
  have hnum : (v * R - w * L).natAbs ≤ 2 * B * H := by
    calc
      _ ≤ (v * R).natAbs + (w * L).natAbs := Int.natAbs_sub_le _ _
      _ = v.natAbs * R + w.natAbs * L := by
        simp only [Int.natAbs_mul, Int.natAbs_natCast]
      _ ≤ B * H + B * H := Nat.add_le_add (Nat.mul_le_mul hv hR) (Nat.mul_le_mul hw hL)
      _ = 2 * B * H := by ring
  exact Nat.le_of_mul_le_mul_right ((he.trans_le hnum).trans hscale) hM

/-- One integer quotient contributes once, including its sign. -/
theorem transferred_frequency_sum (M : ℕ) (hM : 0 < M) (N : ℤ)
    (S : Finset ℤ) (hS : ∀ s : ℤ, s ≠ 0 → N = s * M → s ∈ S) (z : ℂ) :
    (if N ≠ 0 ∧ (M : ℤ) ∣ N then z else 0) =
      ∑ s ∈ S, if s ≠ 0 ∧ N = s * M then z else 0 := by
  have hM0 : (M : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM
  by_cases h : N ≠ 0 ∧ (M : ℤ) ∣ N
  · obtain ⟨s, hs, huniq⟩ := unique_transferred_frequency N M h.1 hM0 h.2
    rw [ite_eq_left h, Finset.sum_eq_single s]
    · rw [ite_eq_left hs]
    · intro t _ hts
      rw [ite_eq_right]
      intro ht
      exact hts (huniq t ht)
    · exact fun hnot => (hnot (hS s hs.1 hs.2)).elim
  · rw [ite_eq_right h]
    symm
    apply Finset.sum_eq_zero
    intro s _
    rw [ite_eq_right]
    rintro ⟨hs, he⟩
    apply h
    refine ⟨?_, ?_⟩
    · rw [he]
      exact mul_ne_zero hs hM0
    · rw [he]
      exact dvd_mul_left (M : ℤ) s

/-- A prime-product range is enough to cover every off-diagonal term by
its actual new root frequency. -/
theorem transferred_frequency_sum_bounded (M L R B H V : ℕ)
    (hM : 0 < M) (v w : ℤ) (hv : v.natAbs ≤ B) (hw : w.natAbs ≤ B)
    (hL : L ≤ H) (hR : R ≤ H) (hscale : 2 * B * H ≤ V * M) (z : ℂ) :
    (if v * R - w * L ≠ 0 ∧ (M : ℤ) ∣ v * R - w * L then z else 0) =
      ∑ s ∈ transferFrequencyRange V,
        if s ≠ 0 ∧ v * R - w * L = s * M then z else 0 := by
  apply transferred_frequency_sum M hM
  intro s _ hs
  exact (mem_transferFrequencyRange V s).mpr
    (transferred_frequency_bound M L R B H V s v w hM hv hw hL hR hscale hs)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferOutputSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coprimality and frequency units after the actual substitution -/

namespace Ostmann

/-- In the integer extension, the inherited coprimality with the erased
pivot implies precisely the common-prime unit condition used above. -/
theorem common_prime_pivot_unit (M L R : ℕ) (hLM : L.Coprime M)
    (q : ℕ) (_hq : q.Prime) (hqL : q ∣ L) (_hqR : q ∣ R) :
    IsCoprime (q : ℤ) (M : ℤ) := by
  have hqM : q.Coprime M := hLM.coprime_dvd_left hqL
  exact Int.isCoprime_iff_gcd_eq_one.mpr (by
    simpa only [Int.gcd_natCast_natCast] using hqM)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferCopiedSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The copied tuple inherits exactly the support required by the phase identity -/

namespace Ostmann

open scoped BigOperators

theorem transferredLabels_pairwise {H Y : Type*} [Fintype H] [Fintype Y]
    (L R : H → ℕ) (U : Y → ℕ)
    (hL : Pairwise (fun h k => (L h).Coprime (L k)))
    (hR : Pairwise (fun h k => (R h).Coprime (R k)))
    (hU : Pairwise (fun y z => (U y).Coprime (U z)))
    (hLR : (∏ h, L h).Coprime (∏ h, R h))
    (hLU : (∏ h, L h).Coprime (∏ y, U y))
    (hRU : (∏ h, R h).Coprime (∏ y, U y)) :
    Pairwise (fun i j => (transferredLabels L R U i).Coprime (transferredLabels L R U j)) := by
  have hLR' (h k : H) : (L h).Coprime (R k) :=
    (hLR.coprime_dvd_left (Finset.dvd_prod_of_mem L (Finset.mem_univ h))).coprime_dvd_right
      (Finset.dvd_prod_of_mem R (Finset.mem_univ k))
  have hLU' (h : H) (y : Y) : (L h).Coprime (U y) :=
    (hLU.coprime_dvd_left (Finset.dvd_prod_of_mem L (Finset.mem_univ h))).coprime_dvd_right
      (Finset.dvd_prod_of_mem U (Finset.mem_univ y))
  have hRU' (h : H) (y : Y) : (R h).Coprime (U y) :=
    (hRU.coprime_dvd_left (Finset.dvd_prod_of_mem R (Finset.mem_univ h))).coprime_dvd_right
      (Finset.dvd_prod_of_mem U (Finset.mem_univ y))
  intro i j hij
  cases i with
  | inl i =>
    obtain ⟨ti, h⟩ := i
    cases j with
    | inl j =>
      obtain ⟨tj, k⟩ := j
      cases ti <;> cases tj
      · exact hR (by simpa using hij)
      · exact (hLR' k h).symm
      · exact hLR' h k
      · exact hL (by simpa using hij)
    | inr y =>
      cases ti
      · exact hRU' h y
      · exact hLU' h y
  | inr y =>
    cases j with
    | inl j =>
      obtain ⟨t, h⟩ := j
      cases t
      · exact (hRU' h y).symm
      · exact (hLU' h y).symm
    | inr z => exact hU (by simpa using hij)

theorem transferredLabels_pivot_coprime {H Y : Type*} [Fintype H] [Fintype Y]
    (L R : H → ℕ) (U : Y → ℕ) (M : ℕ)
    (hL : M.Coprime (∏ h, L h)) (hR : M.Coprime (∏ h, R h))
    (hU : M.Coprime (∏ y, U y)) :
    ∀ i, M.Coprime (transferredLabels L R U i) := by
  intro i
  cases i with
  | inl i =>
    obtain ⟨t, h⟩ := i
    cases t
    · exact hR.coprime_dvd_right (Finset.dvd_prod_of_mem R (Finset.mem_univ h))
    · exact hL.coprime_dvd_right (Finset.dvd_prod_of_mem L (Finset.mem_univ h))
  | inr y => exact hU.coprime_dvd_right (Finset.dvd_prod_of_mem U (Finset.mem_univ y))

theorem prime_large_frequency_unit {p : ℕ} [Fact p.Prime] (s : ℤ)
    (hs : s ≠ 0) (hlarge : s.natAbs < p) : IsUnit (s : ZMod p) := by
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd s p).mp hz
  have hle := Int.natAbs_le_of_dvd_ne_zero hd hs
  simp only [Int.natAbs_natCast] at hle
  exact (not_le_of_gt hlarge) hle

theorem transferredLabels_frequency_unit {H Y : Type*}
    (L R : H → ℕ) (U : Y → ℕ)
    [∀ h, Fact (L h).Prime] [∀ h, Fact (R h).Prime] [∀ y, Fact (U y).Prime]
    (s : ℤ) (hs : s ≠ 0)
    (hL : ∀ h, s.natAbs < L h) (hR : ∀ h, s.natAbs < R h) (hU : ∀ y, s.natAbs < U y) :
    ∀ i, IsUnit (s : ZMod (transferredLabels L R U i)) := by
  intro i
  cases i with
  | inl i =>
    obtain ⟨t, h⟩ := i
    cases t
    · exact prime_large_frequency_unit (p := R h) s hs (hR h)
    · exact prime_large_frequency_unit (p := L h) s hs (hL h)
  | inr y => exact prime_large_frequency_unit (p := U y) s hs (hU y)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferPhaseSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Deriving all phase support conditions from the actual transfer ranges -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem prime_product_factors_large {I : Type*} [Fintype I]
    (p : I → ℕ) (hp : ∀ i, (p i).Prime) (V : ℕ) (hV : ∀ i, V < p i)
    (q : ℕ) (hq : q.Prime) (hdiv : q ∣ ∏ i, p i) : V < q := by
  obtain ⟨i, _, hi⟩ := (hq.prime.dvd_finsetProd_iff p).mp hdiv
  have he : q = p i := ((Nat.dvd_prime (hp i)).mp hi).resolve_left hq.ne_one
  rw [he]
  exact hV i

/-- The integer extension keeps its inherited unit conditions. The signed
substitution then supplies every support hypothesis of the phase identity. -/
theorem transfer_copied_support_of_ranges {H Y : Type*} [Fintype H] [Fintype Y]
    (L R : H → ℕ) (U : Y → ℕ)
    [∀ h, Fact (L h).Prime] [∀ h, Fact (R h).Prime] [∀ y, Fact (U y).Prime]
    (M B K V : ℕ) (v w s : ℤ) (hMpos : 0 < M) (hs : s ≠ 0)
    (hrel : v * (∏ h, R h) - w * (∏ h, L h) = s * M)
    (hv : v.natAbs ≤ B) (hw : w.natAbs ≤ B)
    (hLbound : (∏ h, L h) ≤ K) (hRbound : (∏ h, R h) ≤ K)
    (hscale : 2 * B * K ≤ V * M)
    (hL : Pairwise (fun h k => (L h).Coprime (L k)))
    (hR : Pairwise (fun h k => (R h).Coprime (R k)))
    (hU : Pairwise (fun y z => (U y).Coprime (U z)))
    (hLU : (∏ h, L h).Coprime (∏ y, U y)) (hRU : (∏ h, R h).Coprime (∏ y, U y))
    (hML : M.Coprime (∏ h, L h)) (hMR : M.Coprime (∏ h, R h)) (hMU : M.Coprime (∏ y, U y))
    (hlargeL : ∀ h, V < L h) (hlargeR : ∀ h, V < R h) (hlargeU : ∀ y, V < U y) :
    s.natAbs ≤ V ∧
      Pairwise (fun i j => (transferredLabels L R U i).Coprime (transferredLabels L R U j)) ∧
      (∀ i, M.Coprime (transferredLabels L R U i)) ∧
      (∀ i, IsUnit (s : ZMod (transferredLabels L R U i))) := by
  have hsV := transferred_frequency_bound M (∏ h, L h) (∏ h, R h) B K V s v w
    hMpos hv hw hLbound hRbound hscale hrel
  have hLR : (∏ h, L h).Coprime (∏ h, R h) :=
    transferred_products_coprime _ _ v w s M hs hrel
      (fun q hq hd _ => hsV.trans_lt (prime_product_factors_large L
        (fun h => Fact.out) V hlargeL q hq hd))
      (common_prime_pivot_unit M _ _ hML.symm)
  exact ⟨hsV, transferredLabels_pairwise L R U hL hR hU hLR hLU hRU,
    transferredLabels_pivot_coprime L R U M hML hMR hMU,
    transferredLabels_frequency_unit L R U s hs
      (fun h => hsV.trans_lt (hlargeL h)) (fun h => hsV.trans_lt (hlargeR h))
      (fun y => hsV.trans_lt (hlargeU y))⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_CopiedDirectedPhase
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The next directed phase with support derived from the original ranges -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem transfer_copiedDirectedPhase_of_ranges {H Y : Type*} [Fintype H] [Fintype Y]
    (L R : H → ℕ) (U : Y → ℕ)
    [∀ h, Fact (L h).Prime] [∀ h, Fact (R h).Prime] [∀ y, Fact (U y).Prime]
    (t : ∀ p : ℕ, ZMod p)
    (χH : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χY : Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (νL νR : H → ℂ) (νYL νYR : Y → ℂ) (M : ℕ) (v w s : ℤ)
    (hrel : v * (∏ h, R h) - w * (∏ h, L h) = s * M)
    (B K V : ℕ) (hMpos : 0 < M) (hs : s ≠ 0)
    (hv : v.natAbs ≤ B) (hw : w.natAbs ≤ B)
    (hLbound : (∏ h, L h) ≤ K) (hRbound : (∏ h, R h) ≤ K)
    (hscale : 2 * B * K ≤ V * M)
    (hL : Pairwise (fun h k => (L h).Coprime (L k)))
    (hR : Pairwise (fun h k => (R h).Coprime (R k)))
    (hU : Pairwise (fun y z => (U y).Coprime (U z)))
    (hLU : (∏ h, L h).Coprime (∏ y, U y)) (hRU : (∏ h, R h).Coprime (∏ y, U y))
    (hML : M.Coprime (∏ h, L h)) (hMR : M.Coprime (∏ h, R h)) (hMU : M.Coprime (∏ y, U y))
    (hlargeL : ∀ h, V < L h) (hlargeR : ∀ h, V < R h) (hlargeU : ∀ y, V < U y)
    (hb : ∀ y, b (some (.inr y)) (some (.inr y)) = 0) :
    retainedPrimePhase L U t χH χY b νL νYL M v *
      conj (retainedPrimePhase R U t χH χY b νR νYR M w) =
        copiedDirectedPhase L R U t χH χY b νL νR νYL νYR v w s := by
  let := transferredPrimeFact L R U
  obtain ⟨_, hc, hM, hsu⟩ := transfer_copied_support_of_ranges L R U M B K V v w s
    hMpos hs hrel hv hw hLbound hRbound hscale hL hR hU hLU hRU hML hMR hMU
    hlargeL hlargeR hlargeU
  exact transfer_directed_phase (transferredLabels L R U) t χH χY b νL νR νYL νYR
    M v w s hrel hc hM hsu hb

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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledRegularUnary
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frequency-independent multipliers of the regular copied rows -/

namespace Ostmann

open scoped ComplexConjugate

theorem regularUnary_left {p : ℕ} [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (κ : ℂ) (ε : ℤ) (v s : ZMod p) (hv : v ≠ 0) :
    regularUnary χ κ ε v * χ (v / s) ^ ε =
      regularUnary χ (regularCopiedMultiplier χ κ ε true) (transferCopySign true * ε) s := by
  simp only [regularUnary, regularCopiedMultiplier, ite_true, if_true, transferCopySign, one_mul]
  rw [mul_assoc, transfer_regular_unary χ v s hv ε]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PermutedAdditiveCancellation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common-center additive phases cancel under the actual matching -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem tupleCofactor_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (p : J → ℕ) (hp : ∀ j, p j ≠ 0) (i : I) :
    tupleCofactor (fun i => p (e i)) i = tupleCofactor p (e i) := by
  apply mul_left_cancel₀ (hp (e i))
  calc
    _ = ∏ j, p (e j) := tupleCofactor_mul _ i
    _ = ∏ j, p j := e.prod_comp p
    _ = _ := (tupleCofactor_mul p (e i)).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledAnchorGraph
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Anchor codes derived from the full copied-slot schedule -/

namespace Ostmann

open scoped Classical

theorem initialCompleteGraph_of_ne {I : Type*} {i j : I} (h : i ≠ j) :
    initialCompleteGraph i j = 1 := by simp [initialCompleteGraph, h]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduleGraphInvariants
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.copyScheduleVertexFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Regular rows and pivot columns on the surviving template slots -/

namespace Ostmann

theorem scheduledRegularRow_copy {I : Type*} (role : I → CopyScheduleRole)
    (g : I → I → ℤ) (pivot : ℕ → I) (n : ℕ) (i : CopyScheduleVertex I n)
    (ε : ℤ) (hr : ScheduledRegularRow role g pivot n i ε)
    (hc : (copyScheduleRole role n i).copiedAt n = true)
    (hp : CopyScheduleSurvives role n (copySchedulePositive n (pivot n)))
    (hne : copySchedulePositive n (pivot n) ≠ i) (b : Bool) :
    ScheduledRegularRow role g pivot (n + 1) (.inl (b, i)) (transferCopySign b * ε) := by
  intro j hj hji
  cases j with
  | inl q =>
    rcases q with ⟨c, k⟩
    change CopyScheduleSurvives role n k ∧ _ at hj
    rw [copyScheduleGraph_copy_copy]
    by_cases hbc : b = c
    · subst c
      rw [ite_eq_left rfl, hr k hj.1]
      intro he
      subst k
      exact hji rfl
    · rw [ite_eq_right hbc, hr _ hp hne]
  | inr k =>
    change CopyScheduleSurvives role n k ∧ _ ∧ _ at hj
    rw [copyScheduleGraph_copy_outside, hr k hj.1]
    intro he
    subst k
    have : (true : Bool) = false := hc.symm.trans hj.2.1
    cases this

/-- Every incoming row is constant on the constituents of a future pivot.
The targets are its actual positive copies, not a collapsed prime placeholder. -/
theorem copyScheduleGraph_pivot_common_column {I : Type*}
    (role : I → CopyScheduleRole) (pivot : ℕ → I)
    (k : ℕ) (a b : I) (ha : role a = .pivot k) (hb : role b = .pivot k)
    (n : ℕ) (hn : n ≤ k) (i : CopyScheduleVertex I n)
    (hi : CopyScheduleSurvives role n i) (hne : copyScheduleRole role n i ≠ .pivot k) :
    copyScheduleGraph initialCompleteGraph pivot n i (copySchedulePositive n a) =
      copyScheduleGraph initialCompleteGraph pivot n i (copySchedulePositive n b) := by
  induction n with
  | zero =>
    have hia : i ≠ a := fun he => hne (he ▸ ha)
    have hib : i ≠ b := fun he => hne (he ▸ hb)
    exact (initialCompleteGraph_of_ne hia).trans (initialCompleteGraph_of_ne hib).symm
  | succ n ih =>
    cases i with
    | inl p =>
      rcases p with ⟨c, i⟩
      change CopyScheduleSurvives role n i ∧ _ at hi
      cases c
      · rfl
      · change transferCopySign true * copyScheduleGraph initialCompleteGraph pivot n i
            (copySchedulePositive n a) =
          transferCopySign true * copyScheduleGraph initialCompleteGraph pivot n i
            (copySchedulePositive n b)
        apply congrArg (fun z => transferCopySign true * z)
        apply ih (by omega) i hi.1
        intro he
        apply hne
        change (copyScheduleRole role n i).afterCopy true = _
        rw [he]
        rfl
    | inr i =>
      change CopyScheduleSurvives role n i ∧ _ ∧ _ at hi
      change transferCopySign true * copyScheduleGraph initialCompleteGraph pivot n i
          (copySchedulePositive n a) =
        transferCopySign true * copyScheduleGraph initialCompleteGraph pivot n i
          (copySchedulePositive n b)
      exact congrArg (fun z => transferCopySign true * z) (ih (by omega) i hi.1 hne)

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

/-- The graph used by the exact local phase formula is the restriction of
our recursively constructed graph to the genuine surviving slots. -/
theorem scheduledRetainedGraph_update {I : Type*} (role : I → CopyScheduleRole)
    (g : I → I → ℤ) (pivot : ℕ → I) (n : ℕ)
    (i j : (Bool × CopyScheduleH role n) ⊕ CopyScheduleY role n) :
    transferredGraph (scheduledRetainedGraph role g pivot n) i j =
      copyScheduleGraph g pivot (n + 1)
        (scheduledOutputVertex role n i).val (scheduledOutputVertex role n j).val := by
  cases i with
  | inl i =>
    rcases i with ⟨b, i⟩
    cases j with
    | inl j => rcases j with ⟨c, j⟩; rfl
    | inr j => rfl
  | inr i =>
    cases j with
    | inl j => rcases j with ⟨c, j⟩; rfl
    | inr j => rfl

theorem scheduledRetainedGraph_diagonal {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n : ℕ) (i : Option (CopyScheduleH role n ⊕ CopyScheduleY role n)) :
    scheduledRetainedGraph role initialCompleteGraph pivot n i i = 0 :=
  copyScheduleGraph_diagonal initialCompleteGraph pivot initialCompleteGraph_self n _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_TransferCauchy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite Cauchy--Schwarz step in the history transfer -/

namespace Ostmann

open scoped BigOperators

theorem complex_pairing_sq_le {A : Type*} [Fintype A] (F G : A → ℂ) :
    ‖∑ a, F a * G a‖ ^ 2 ≤ (∑ a, ‖F a‖ ^ 2) * ∑ a, ‖G a‖ ^ 2 := by
  have hnorm : ‖∑ a, F a * G a‖ ≤ ∑ a, ‖F a‖ * ‖G a‖ := by
    simpa only [norm_mul] using norm_sum_le (Finset.univ : Finset A) (fun a => F a * G a)
  have hnonneg : 0 ≤ ∑ a, ‖F a‖ * ‖G a‖ :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset A)
    (fun a => ‖F a‖) (fun a => ‖G a‖)
  nlinarith [norm_nonneg (∑ a, F a * G a)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SubprobabilityTransfer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cauchy--Schwarz retains the internal distinctness restriction -/

namespace Ostmann

open scoped BigOperators

theorem subprobability_weighted_norm_sq_le {A : Type*} [Fintype A]
    (μ : A → ℝ) (hμ : ∀ a, 0 ≤ μ a) (hmass : ∑ a, μ a ≤ 1) (F : A → ℂ) :
    ‖∑ a, (μ a : ℂ) * F a‖ ^ 2 ≤ ∑ a, μ a * ‖F a‖ ^ 2 := by
  have hnorm : ‖∑ a, (μ a : ℂ) * F a‖ ≤ ∑ a, μ a * ‖F a‖ := by
    calc
      _ ≤ ∑ a, ‖(μ a : ℂ) * F a‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hμ _)]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset A)
    (fun a => Real.sqrt (μ a)) (fun a => Real.sqrt (μ a) * ‖F a‖)
  have hsq (a : A) : Real.sqrt (μ a) ^ 2 = μ a := Real.sq_sqrt (hμ a)
  have hprod (a : A) : Real.sqrt (μ a) * (Real.sqrt (μ a) * ‖F a‖) = μ a * ‖F a‖ := by
    rw [← mul_assoc, ← pow_two, hsq]
  simp only [mul_pow, hsq, hprod] at hCS
  have hpos : 0 ≤ ∑ a, μ a * ‖F a‖ ^ 2 :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (hμ a) (sq_nonneg _))
  have hbound := hCS.trans (mul_le_of_le_one_left hpos hmass)
  have hn : 0 ≤ ∑ a, μ a * ‖F a‖ :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (hμ a) (norm_nonneg _))
  nlinarith [norm_nonneg (∑ a, (μ a : ℂ) * F a)]

theorem subprobability_transfer_row_bound {A : Type*} [Fintype A] {T : A → Type*}
    [∀ a, Fintype (T a)] (μ : A → ℝ) (hμ : ∀ a, 0 ≤ μ a) (hmass : ∑ a, μ a ≤ 1)
    (row coefficient : ∀ a, T a → ℂ) (M : A → ℝ)
    (hrow : ∀ a, (∑ t, ‖row a t‖ ^ 2) ≤ M a) :
    ‖∑ a, (μ a : ℂ) * ∑ t, row a t * coefficient a t‖ ^ 2 ≤
      ∑ a, μ a * (M a * ∑ t, ‖coefficient a t‖ ^ 2) := by
  apply (subprobability_weighted_norm_sq_le μ hμ hmass _).trans
  apply Finset.sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_left _ (hμ a)
  exact (complex_pairing_sq_le (row a) (coefficient a)).trans
    (mul_le_mul_of_nonneg_right (hrow a) (Finset.sum_nonneg fun _ _ => sq_nonneg _))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteProductPrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite independent priors used for the arithmetic samples -/

namespace Ostmann

open scoped BigOperators

theorem productPrior_nonneg {A : Type*} {n : ℕ}
    (μ : Fin n → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (x : Fin n → A) :
    0 ≤ productPrior μ x := Finset.prod_nonneg fun i _ => hμ i (x i)

theorem productPrior_mass {A : Type*} [Fintype A] {n : ℕ}
    (μ : Fin n → A → ℝ) (hμ : ∀ i, ∑ a, μ i a = 1) :
    (∑ x : Fin n → A, productPrior μ x) = 1 := by
  unfold productPrior
  rw [← Fintype.prod_sum]
  simp only [hμ, Finset.prod_const_one]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HarmonicWordPriors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic laws for all word roles on one common prime sample space -/

namespace Ostmann

open scoped BigOperators Classical

theorem primeSubsetPrior_nonneg (P Q : Finset ℕ) (p : P) :
    0 ≤ primeSubsetPrior P Q p := by
  unfold primeSubsetPrior
  split_ifs
  · exact div_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => by positivity))
  · exact le_rfl

theorem primeSubsetPrior_support (P Q : Finset ℕ) (p : P)
    (hp : primeSubsetPrior P Q p ≠ 0) : (p : ℕ) ∈ Q := by
  by_contra hn
  simp [primeSubsetPrior, hn] at hp

theorem primeSubsetPrior_mass (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hm : (∑ q ∈ Q, (q : ℝ)⁻¹) ≠ 0) : (∑ p : P, primeSubsetPrior P Q p) = 1 := by
  unfold primeSubsetPrior
  rw [Finset.sum_coe_sort P (fun p => if p ∈ Q then
    (p : ℝ)⁻¹ / (∑ q ∈ Q, (q : ℝ)⁻¹) else 0), ← Finset.sum_filter]
  have hf : P.filter (fun p => p ∈ Q) = Q := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hQP h, h⟩⟩
  rw [hf, ← Finset.sum_div]
  exact div_self hm

theorem primeSubsetPrior_product (P : Finset ℕ) {n : ℕ} (Q : Fin n → Finset ℕ)
    (x : Fin n → P) (hx : productPrior (fun i => primeSubsetPrior P (Q i)) x ≠ 0) :
    productPrior (fun i => primeSubsetPrior P (Q i)) x =
      (∏ i, ∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹ * (∏ i, (x i : ℝ))⁻¹ := by
  have hs (i : Fin n) : (x i : ℕ) ∈ Q i :=
    primeSubsetPrior_support P (Q i) (x i) ((Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ i))
  unfold productPrior
  simp only [primeSubsetPrior, hs, ite_true, if_true, Finset.prod_div_distrib, Finset.prod_inv_distrib]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PivotResidueEquation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Equality of pivot residue keys is the exact transfer equation -/

namespace Ostmann

theorem pivot_residue_eq_iff (M L R : ℕ) (hLM : L.Coprime M) (hRM : R.Coprime M)
    (v w : ℤ) :
    (v : ZMod M) * (L : ZMod M)⁻¹ = (w : ZMod M) * (R : ZMod M)⁻¹ ↔
      (M : ℤ) ∣ v * R - w * L := by
  have hL := (ZMod.isUnit_iff_coprime L M).mpr hLM
  have hR := (ZMod.isUnit_iff_coprime R M).mpr hRM
  have hprod := hL.mul hR
  have he : ((v : ZMod M) * (L : ZMod M)⁻¹ - (w : ZMod M) * (R : ZMod M)⁻¹) *
      ((L : ZMod M) * R) = ((v * R - w * L : ℤ) : ZMod M) := by
    push_cast
    calc
      _ = (v : ZMod M) * ((L : ZMod M)⁻¹ * L) * R -
          (w : ZMod M) * ((R : ZMod M)⁻¹ * R) * L := by ring
      _ = _ := by rw [ZMod.inv_mul_of_unit _ hL, ZMod.inv_mul_of_unit _ hR]; ring
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · intro h
    rw [h, sub_self, zero_mul] at he
    exact he.symm
  · intro h
    rw [h] at he
    have hz := congrArg (fun a : ZMod M => a * ((L : ZMod M) * R)⁻¹) he
    rw [mul_assoc, ZMod.mul_inv_of_unit _ hprod, mul_one, zero_mul] at hz
    exact sub_eq_zero.mp hz

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PivotProductPrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original prior of an internally distinct pivot total -/

namespace Ostmann

open scoped BigOperators Classical

private theorem tupleImage_mem_iff_dvd (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} (e : Fin n ↪ P) (q : P) :
    q ∈ tupleImage e ↔ (q : ℕ) ∣ ∏ i, (e i : ℕ) := by
  constructor
  · intro hq
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hq
    rw [← hi]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  · intro hq
    obtain ⟨i, _, hi⟩ := ((hP _ q.property).prime.dvd_finsetProd_iff (fun i => (e i : ℕ))).mp hq
    have he : (q : ℕ) = (e i : ℕ) :=
      ((Nat.dvd_prime (hP _ (e i).property)).mp hi).resolve_left (hP _ q.property).ne_one
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, Subtype.ext he.symm⟩

private theorem tupleImage_eq_of_product_eq (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} (e f : Fin n ↪ P) (h : (∏ i, (e i : ℕ)) = ∏ i, (f i : ℕ)) :
    tupleImage e = tupleImage f := by
  ext q
  rw [tupleImage_mem_iff_dvd P hP, tupleImage_mem_iff_dvd P hP, h]

theorem card_distinct_prime_product_fiber (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (n M : ℕ) :
    ((Finset.univ : Finset (Fin n → P)).filter
      (fun x : Fin n → P => Function.Injective x ∧ (∏ i, (x i : ℕ)) = M)).card ≤ n.factorial := by
  let S := (Finset.univ : Finset (Fin n → P)).filter
    (fun x : Fin n → P => Function.Injective x ∧ (∏ i, (x i : ℕ)) = M)
  by_cases hs : S.Nonempty
  · obtain ⟨x, hx⟩ := hs
    have hxp := (Finset.mem_filter.mp hx).2
    let e : Fin n ↪ P := ⟨x, hxp.1⟩
    let f : S → {g : Fin n ↪ P // tupleImage g = tupleImage e} := fun y =>
      ⟨⟨y.val, (Finset.mem_filter.mp y.property).2.1⟩,
        tupleImage_eq_of_product_eq P hP _ e
          ((Finset.mem_filter.mp y.property).2.2.trans hxp.2.symm)⟩
    have hf : Function.Injective f := by
      intro y z hyz
      apply Subtype.ext
      exact congrArg (fun w : {g : Fin n ↪ P // tupleImage g = tupleImage e} => w.val.toFun) hyz
    have hcard : (tupleImage e).card = n := by
      rw [tupleImage, Finset.card_image_of_injective _ e.injective]
      simp
    have hc := Fintype.card_le_of_injective f hf
    rw [card_tupleImage_fiber n (tupleImage e) hcard] at hc
    change S.card ≤ n.factorial
    simpa only [Fintype.card_coe] using hc
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    change S.card ≤ n.factorial
    rw [he, Finset.card_empty]
    exact Nat.zero_le _

theorem harmonic_product_point_bound (P : Finset ℕ) {n : ℕ}
    (Q : Fin n → Finset ℕ) (x : Fin n → P) :
    productPrior (fun i => primeSubsetPrior P (Q i)) x ≤
      (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (∏ i, (x i : ℝ))⁻¹ := by
  by_cases hx : productPrior (fun i => primeSubsetPrior P (Q i)) x = 0
  · rw [hx]
    positivity
  · rw [primeSubsetPrior_product P Q x hx, Finset.prod_inv_distrib]

theorem harmonic_distinct_product_mass (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} (Q : Fin n → Finset ℕ) (S : Finset (Fin n → P))
    (hS : ∀ x ∈ S, Function.Injective x) (M : ℕ) :
    (∑ x ∈ S.filter (fun x => (∏ i, (x i : ℕ)) = M),
      productPrior (fun i => primeSubsetPrior P (Q i)) x) ≤
      (n.factorial : ℝ) * (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (M : ℝ)⁻¹ := by
  let T := S.filter (fun x => (∏ i, (x i : ℕ)) = M)
  have hc : T.card ≤ n.factorial := by
    apply (Finset.card_le_card (show T ⊆ (Finset.univ : Finset (Fin n → P)).filter
      (fun x : Fin n → P => Function.Injective x ∧ (∏ i, (x i : ℕ)) = M) from ?_)).trans
      (card_distinct_prime_product_fiber P hP n M)
    intro x hx
    obtain ⟨hxS, hxM⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hS x hxS, hxM⟩
  calc
    _ ≤ ∑ _x ∈ T, (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (M : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro x hx
      have hb := harmonic_product_point_bound P Q x
      have he : (∏ i, (x i : ℝ)) = (M : ℝ) := by
        exact_mod_cast (Finset.mem_filter.mp hx).2
      simpa only [he] using hb
    _ = (T.card : ℝ) * ((∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (M : ℝ)⁻¹) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      have hc' : (T.card : ℝ) ≤ n.factorial := by exact_mod_cast hc
      nlinarith [mul_le_mul_of_nonneg_right hc'
        (show 0 ≤ (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (M : ℝ)⁻¹ by positivity)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PivotIntegerTransfer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending an internally distinct pivot total to all integers -/

namespace Ostmann

open scoped BigOperators Classical

/-- The row can depend on the entire pivot tuple. Its coefficient depends
only on the total, so no character on the extended integer is introduced. -/
theorem pivot_integer_transfer (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} (Q : Fin n → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQ : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (S : Finset (Fin n → P)) (hS : ∀ x ∈ S, Function.Injective x)
    (T : Finset ℕ) (hT : ∀ x ∈ S, (∏ i, (x i : ℕ)) ∈ T)
    (row : ∀ x : Fin n → P, Fin (∏ i, (x i : ℕ)) → ℂ)
    (hrow : ∀ x ∈ S, ∀ u, ‖row x u‖ ≤ 1)
    (B : ∀ M : ℕ, Fin M → ℂ) :
    ‖∑ x ∈ S, (productPrior (fun i => primeSubsetPrior P (Q i)) x : ℂ) *
        ∑ u, row x u * B (∏ i, (x i : ℕ)) u‖ ^ 2 ≤
      ((n.factorial : ℝ) * ∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) *
        ∑ M ∈ T, ∑ u, ‖B M u‖ ^ 2 := by
  let μ := fun x : Fin n → P => productPrior (fun i => primeSubsetPrior P (Q i)) x
  let F := fun M : ℕ => ∑ u, ‖B M u‖ ^ 2
  let K := (n.factorial : ℝ) * ∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹
  have hμ : ∀ x, 0 ≤ μ x := fun x => productPrior_nonneg _ (fun i p => primeSubsetPrior_nonneg _ _ p) x
  have hF : ∀ M, 0 ≤ F M := fun M => Finset.sum_nonneg (fun u _ => sq_nonneg _)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hmass : (∑ x : S, μ x) ≤ 1 := by
    rw [Finset.sum_coe_sort S μ]
    calc
      _ ≤ ∑ x, μ x := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun x _ _ => hμ x)
      _ = 1 := productPrior_mass _ (fun i => primeSubsetPrior_mass P (Q i) (hQP i) (hQ i))
  have hr : ∀ x : S, (∑ u, ‖row x u‖ ^ 2) ≤ (∏ i, (x.val i : ℕ)) := by
    intro x
    calc
      _ ≤ ∑ _u : Fin (∏ i, (x.val i : ℕ)), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro u _
        have hh := hrow x x.property u
        nlinarith [norm_nonneg (row x u)]
      _ = _ := by simp
  have hcs := subprobability_transfer_row_bound (fun x : S => μ x) (fun x => hμ x) hmass
    (fun x : S => row x) (fun x : S => B (∏ i, (x.val i : ℕ)))
    (fun x : S => ((∏ i, (x.val i : ℕ)) : ℝ))
    (by simpa only [Nat.cast_prod] using hr)
  have hext : (∑ x ∈ S, μ x * ((∏ i, (x i : ℕ)) * F (∏ i, (x i : ℕ)))) ≤
      K * ∑ M ∈ T, F M := by
    rw [← Finset.sum_fiberwise_of_maps_to hT, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro M hMT
    calc
      _ = (∑ x ∈ S.filter (fun x => (∏ i, (x i : ℕ)) = M), μ x) * ((M : ℝ) * F M) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x hx
        rw [(Finset.mem_filter.mp hx).2]
      _ ≤ (K * (M : ℝ)⁻¹) * ((M : ℝ) * F M) := by
        exact mul_le_mul_of_nonneg_right (harmonic_distinct_product_mass P hP Q S hS M)
          (mul_nonneg (Nat.cast_nonneg M) (hF M))
      _ ≤ K * F M := by
        by_cases hM : M = 0
        · simp only [hM, Nat.cast_zero, inv_zero, mul_zero, zero_mul]
          exact mul_nonneg hK (hF 0)
        · have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM
          exact le_of_eq (by field_simp)
  have hcs' : ‖∑ x ∈ S, (μ x : ℂ) * ∑ u, row x u * B (∏ i, (x i : ℕ)) u‖ ^ 2 ≤
      ∑ x ∈ S, μ x * ((∏ i, (x i : ℕ)) * F (∏ i, (x i : ℕ))) := by
    have hs₁ := Finset.sum_coe_sort S (fun x : Fin n → P =>
      (μ x : ℂ) * ∑ u, row x u * B (∏ i, (x i : ℕ)) u)
    have hs₂ := Finset.sum_coe_sort S (fun x : Fin n → P =>
      μ x * ((∏ i, (x i : ℕ)) * F (∏ i, (x i : ℕ))))
    rw [← hs₁, ← hs₂]
    simpa only [Nat.cast_prod, F] using hcs
  exact hcs'.trans hext

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DiagonalTransfer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Grouping the transfer diagonal before expanding the square -/

namespace Ostmann

open scoped BigOperators Classical

/-- The key comprises the inherited product and its frequency. Ordered
arrangements with that key are summed inside the square. -/
theorem diagonal_grouped_identity {A K : Type*} [Fintype A] [Fintype K]
    (key : A → K) (z : A → ℂ) (w : K → ℂ) :
    (∑ a : A, ∑ b : A, if key a = key b then w (key a) * z a * star (z b) else 0) =
      ∑ k : K, w k * groupedCoefficient key z k * star (groupedCoefficient key z k) := by
  rw [Finset.sum_comm]
  symm
  unfold groupedCoefficient
  simp only [star_sum, Finset.sum_mul, Finset.mul_sum, apply_ite, star_zero,
    ite_mul, mul_zero, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : key b = key a <;> simp [h]

theorem diagonal_real_eq_sum_sq {A K : Type*} [Fintype A] [Fintype K]
    (key : A → K) (z : A → ℂ) (w : K → ℝ) :
    (∑ a : A, ∑ b : A,
      if key a = key b then (w (key a) : ℂ) * z a * star (z b) else 0).re =
      ∑ k : K, w k * ‖groupedCoefficient key z k‖ ^ 2 := by
  rw [diagonal_grouped_identity key z (fun k => (w k : ℂ))]
  simp only [mul_assoc, Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.re_sum, Complex.ofReal_re]

theorem diagonal_real_nonneg {A K : Type*} [Fintype A] [Fintype K]
    (key : A → K) (z : A → ℂ) (w : K → ℝ) (hw : ∀ k, 0 ≤ w k) :
    0 ≤ (∑ a : A, ∑ b : A,
      if key a = key b then (w (key a) : ℂ) * z a * star (z b) else 0).re := by
  rw [diagonal_real_eq_sum_sq]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (sq_nonneg _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PivotResidueGrouping
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Grouping the actual pivot row before the integer extension -/

namespace Ostmann

open scoped BigOperators Classical

theorem pivot_residue_grouping {A U : Type*} [Fintype A] [Fintype U]
    (key : A → U) (row : U → ℂ) (c : A → ℂ) :
    (∑ a, row (key a) * c a) = ∑ u, row u * groupedCoefficient key c u := by
  symm
  unfold groupedCoefficient
  simp only [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PivotSquareExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The grouped square has the actual transfer divisibility condition -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem pivotResidueKey_eq_iff (M : ℕ) [NeZero M] (L R : ℕ)
    (hL : L.Coprime M) (hR : R.Coprime M) (v w : ℤ) :
    pivotResidueKey M L v = pivotResidueKey M R w ↔ (M : ℤ) ∣ v * R - w * L := by
  unfold pivotResidueKey
  rw [(ZMod.finEquiv M).symm.injective.eq_iff, pivot_residue_eq_iff M L R hL hR]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PivotSquareSplit
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact diagonal and signed-frequency decomposition of a transfer -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

/-- A finite family has a nonnegative equal-key square even when its keys
range over an infinite type. -/
theorem finite_key_square_nonneg {A K : Type*} [Fintype A]
    (key : A → K) (c : A → ℂ) :
    0 ≤ (∑ a, ∑ b, if key a = key b then c a * conj (c b) else 0).re := by
  classical
  let T : Finset K := Finset.univ.image key
  let k : A → T := fun a => ⟨key a, Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩⟩
  have h := diagonal_real_nonneg k c (fun _ => 1) (fun _ => by norm_num)
  simpa only [Complex.ofReal_one, one_mul, k, Subtype.mk.injEq, Complex.star_def] using h

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

theorem validTransferredPivot_of_eq (T : Finset ℕ) (N s : ℤ) (hs : s ≠ 0)
    (M : ℕ) (hM : 0 < M) (hMT : M ∈ T) (h : N = s * M) :
    validTransferredPivot T N s := by
  refine ⟨hs, ?_, ?_, ?_⟩
  · rw [h]
    exact dvd_mul_right s M
  · rw [Int.ediv_eq_of_eq_mul_right hs h]
    exact_mod_cast hM
  · rw [reconstructedPivot_of_eq N s hs M h]
    exact hMT

theorem validTransferredPivot_equation (T : Finset ℕ) (N s : ℤ)
    (h : validTransferredPivot T N s) :
    N = s * reconstructedPivot N s := by
  rw [reconstructedPivot, Int.toNat_of_nonneg h.2.2.1.le]
  exact (Int.mul_ediv_cancel' h.2.1).symm

/-- The sum over positive integers has exactly one retained term. This
identity is valid for arbitrary coefficients, including all inherited weights. -/
theorem transferred_pivot_substitution (T : Finset ℕ)
    (hT : ∀ M ∈ T, 0 < M) (N s : ℤ) (f : ℕ → ℂ) :
    (∑ M ∈ T, if s ≠ 0 ∧ N = s * M then f M else 0) =
      if validTransferredPivot T N s then f (reconstructedPivot N s) else 0 := by
  by_cases h : validTransferredPivot T N s
  · rw [ite_eq_left h, Finset.sum_eq_single (reconstructedPivot N s)]
    · rw [ite_eq_left ⟨h.1, validTransferredPivot_equation T N s h⟩]
    · intro M _ hne
      rw [ite_eq_right]
      rintro ⟨hs, he⟩
      exact hne (reconstructedPivot_of_eq N s hs M he).symm
    · exact fun hn => (hn h.2.2.2).elim
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro M hMT
    rw [ite_eq_right]
    rintro ⟨hs, he⟩
    exact h (validTransferredPivot_of_eq T N s hs M (hT M hMT) hMT he)

/-- Expanded copied branches now carry only their reconstructed pivot,
with all integer range and sign tests retained as indicators. -/
theorem offDiagonal_pivot_substitution {A : Type*} [Fintype A]
    (T : Finset ℕ) (hT : ∀ M ∈ T, 0 < M) (S : Finset ℤ)
    (L : A → ℕ) (v : A → ℤ) (c : ℕ → A → ℂ) :
    (∑ M ∈ T, ∑ s ∈ S, ∑ a, ∑ b,
      if s ≠ 0 ∧ v a * L b - v b * L a = s * M then c M a * conj (c M b) else 0) =
    ∑ s ∈ S, ∑ a, ∑ b,
      if validTransferredPivot T (v a * L b - v b * L a) s
      then c (reconstructedPivot (v a * L b - v b * L a) s) a *
        conj (c (reconstructedPivot (v a * L b - v b * L a) s) b) else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  exact transferred_pivot_substitution T hT _ s (fun M => c M a * conj (c M b))

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

theorem frequencyRoot_mem_allFrequencyList (n : ℕ) (t : FrequencyTree ℤ n) :
    frequencyRoot n t ∈ allFrequencyList n t := by
  cases n <;> simp [allFrequencyList, frequencyRoot]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_CopyScheduleUnary
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual unary factors on the copied schedule -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

/-- The local unary produced by the proved transfer is the restriction of
this single recursively defined schedule unary. -/
theorem copyScheduleUnary_update {I : Type*} (role : I → CopyScheduleRole)
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (g : I → I → ℤ) (pivot : ℕ → I) (initial : I → ℤ → ℕ → ℂ)
    (n : ℕ) (t : FrequencyTree ℤ (n + 1))
    (q : (Bool × CopyScheduleH role n) ⊕ CopyScheduleY role n → ℕ)
    [∀ i, Fact (q i).Prime]
    (i : (Bool × CopyScheduleH role n) ⊕ CopyScheduleY role n) :
    copiedSlotUnary q (fun h => χ (copyScheduleOrigin n h.val))
      (scheduledRetainedGraph role g pivot n)
      (fun h => copyScheduleUnary χ g pivot initial n t.2.1 h.val (q (.inl (true, h))))
      (fun h => copyScheduleUnary χ g pivot initial n t.2.2 h.val (q (.inl (false, h))))
      (fun y => copyScheduleUnary χ g pivot initial n t.2.1 y.val (q (.inr y)))
      (fun y => copyScheduleUnary χ g pivot initial n t.2.2 y.val (q (.inr y)))
      (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) t.1 i =
    copyScheduleUnary χ g pivot initial (n + 1) t
      (scheduledOutputVertex role n i).val (q i) := by
  rcases i with ⟨c, h⟩ | y
  · have he : (scheduledOutputVertex role n (.inl (c, h))).val = .inl (c, h.val) := rfl
    rw [he]
    cases c <;> simp [copiedSlotUnary, copyScheduleUnary, scheduledRetainedGraph, div_eq_mul_inv]
  · rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DirectedPhaseReindex
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact reindexing of the directed phase and its cofactors -/

namespace Ostmann

open scoped BigOperators Classical

theorem directedPrimePhase_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (p : J → ℕ) [∀ j, NeZero (p j)]
    (χ : ∀ j, DirichletCharacter ℂ (p j)) (t : ∀ j, ZMod (p j))
    (ν : J → ℂ) (b : J → J → ℤ) (v : ℤ) :
    directedPrimePhase (fun i => p (e i)) (fun i => χ (e i)) (fun i => t (e i))
        (fun i => ν (e i)) (fun i j => b (e i) (e j)) v =
      directedPrimePhase p χ t ν b v := by
  unfold directedPrimePhase
  rw [← e.prod_comp (fun j => ZMod.stdAddChar
    (t j * ((tupleCofactor p j : ZMod (p j))⁻¹ * (v : ZMod (p j)))) *
      ν j * ∏ k, χ j (p k : ZMod (p j)) ^ b j k)]
  apply Finset.prod_congr rfl
  intro i _
  rw [tupleCofactor_equiv e p (fun j => NeZero.ne (p j)) i]
  dsimp only
  rw [e.prod_comp (fun j => χ (e i) (p j : ZMod (p (e i))) ^ b (e i) j)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledPrimePhase
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The directed phase on the actual surviving prime slots -/

namespace Ostmann

open scoped BigOperators Classical

theorem copiedSlotCharacter_schedule {I : Type*} (role : I → CopyScheduleRole)
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p) (n : ℕ)
    (i : (Bool × CopyScheduleH role n) ⊕ CopyScheduleY role n) :
    copiedSlotCharacter (fun h => χ (copyScheduleOrigin n h.val))
        (fun y => χ (copyScheduleOrigin n y.val)) i =
      χ (copyScheduleOrigin (n + 1) (scheduledOutputVertex role n i).val) := by
  rcases i with ⟨b, h⟩ | y <;> rfl

/-- The copied local phase is exactly the next phase on all surviving slots,
with the same original character attached to every copied prime coordinate. -/
theorem scheduledPrimePhase_step {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (g : I → I → ℤ) (pivot : ℕ → I) (initial : I → ℤ → ℕ → ℂ)
    (n : ℕ) (t : FrequencyTree ℤ (n + 1))
    (q : (Bool × CopyScheduleH role n) ⊕ CopyScheduleY role n → ℕ)
    [∀ i, Fact (q i).Prime] (center : ∀ p : ℕ, ZMod p) :
    directedPrimePhase q
      (fun i => copiedSlotCharacter (fun h => χ (copyScheduleOrigin n h.val))
        (fun y => χ (copyScheduleOrigin n y.val)) i (q i))
      (fun i => center (q i))
      (copiedSlotUnary q (fun h => χ (copyScheduleOrigin n h.val))
        (scheduledRetainedGraph role g pivot n)
        (fun h => copyScheduleUnary χ g pivot initial n t.2.1 h.val (q (.inl (true, h))))
        (fun h => copyScheduleUnary χ g pivot initial n t.2.2 h.val (q (.inl (false, h))))
        (fun y => copyScheduleUnary χ g pivot initial n t.2.1 y.val (q (.inr y)))
        (fun y => copyScheduleUnary χ g pivot initial n t.2.2 y.val (q (.inr y)))
        (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) t.1)
      (transferredGraph (scheduledRetainedGraph role g pivot n)) t.1 =
    scheduledPrimePhase role χ g pivot initial (n + 1) t
      (fun j => q (copyScheduleSurvivorEquiv role n j)) center := by
  let e := copyScheduleSurvivorEquiv role n
  rw [← directedPrimePhase_equiv e]
  unfold scheduledPrimePhase
  have hout (j : {i : CopyScheduleVertex I (n + 1) // CopyScheduleSurvives role (n + 1) i}) :
      (scheduledOutputVertex role n (e j)).val = j.val := by
    exact congrArg Subtype.val (e.symm_apply_apply j)
  have hc : (fun j => copiedSlotCharacter (fun h => χ (copyScheduleOrigin n h.val))
      (fun y => χ (copyScheduleOrigin n y.val)) (e j) (q (e j))) =
      (fun j => χ (copyScheduleOrigin (n + 1) j.val) (q (e j))) := by
    funext j
    rw [copiedSlotCharacter_schedule, hout]
  have hν : (fun j => copiedSlotUnary q (fun h => χ (copyScheduleOrigin n h.val))
      (scheduledRetainedGraph role g pivot n)
      (fun h => copyScheduleUnary χ g pivot initial n t.2.1 h.val (q (.inl (true, h))))
      (fun h => copyScheduleUnary χ g pivot initial n t.2.2 h.val (q (.inl (false, h))))
      (fun y => copyScheduleUnary χ g pivot initial n t.2.1 y.val (q (.inr y)))
      (fun y => copyScheduleUnary χ g pivot initial n t.2.2 y.val (q (.inr y)))
      (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) t.1 (e j)) =
      (fun j => copyScheduleUnary χ g pivot initial (n + 1) t j.val (q (e j))) := by
    funext j
    rw [copyScheduleUnary_update, hout]
  have hg : (fun i j => transferredGraph (scheduledRetainedGraph role g pivot n) (e i) (e j)) =
      (fun i j => copyScheduleGraph g pivot (n + 1) i.val j.val) := by
    funext i j
    rw [scheduledRetainedGraph_update, hout, hout]
  rw [hc, hν, hg]
  rfl

/-- The copied phase appearing in the exact arithmetic off-diagonal is
already the actual next schedule phase. -/
theorem copiedDirectedPhase_scheduled {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (g : I → I → ℤ) (pivot : ℕ → I) (initial : I → ℤ → ℕ → ℂ)
    (n : ℕ) (t : FrequencyTree ℤ (n + 1))
    (L R : CopyScheduleH role n → ℕ) (U : CopyScheduleY role n → ℕ)
    [∀ h, Fact (L h).Prime] [∀ h, Fact (R h).Prime] [∀ y, Fact (U y).Prime]
    (center : ∀ p : ℕ, ZMod p) :
    letI := transferredPrimeFact L R U
    copiedDirectedPhase L R U center
      (fun h => χ (copyScheduleOrigin n h.val))
      (fun y => χ (copyScheduleOrigin n y.val)) (scheduledRetainedGraph role g pivot n)
      (fun h => copyScheduleUnary χ g pivot initial n t.2.1 h.val (L h))
      (fun h => copyScheduleUnary χ g pivot initial n t.2.2 h.val (R h))
      (fun y => copyScheduleUnary χ g pivot initial n t.2.1 y.val (U y))
      (fun y => copyScheduleUnary χ g pivot initial n t.2.2 y.val (U y))
      (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) t.1 =
    scheduledPrimePhase role χ g pivot initial (n + 1) t
      (fun j => transferredLabels L R U (copyScheduleSurvivorEquiv role n j)) center := by
  let := transferredPrimeFact L R U
  exact scheduledPrimePhase_step role χ g pivot initial n t (transferredLabels L R U) center

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ReverseCopyMap
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reversing the literal copied-atom schedule

This construction is at the atom level: a current pivot group is one atom
carrying its total product. -/

namespace Ostmann

open scoped Classical

theorem reverseCopyLabelMap_copied {I σ : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (pivot : σ) (current : CopyScheduleAtoms role (n + 1) → σ)
    (i : CopyScheduleH role n) :
    reverseCopyLabelMap role n b pivot current ⟨i.val, i.property.1⟩ =
      current ⟨.inl (b, i.val), i.property⟩ := by
  simp only [reverseCopyLabelMap, i.property.2, dite_true]

theorem reverseCopyLabelMap_retained {I σ : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (pivot : σ) (current : CopyScheduleAtoms role (n + 1) → σ)
    (i : CopyScheduleY role n) :
    reverseCopyLabelMap role n b pivot current ⟨i.val, i.property.1⟩ =
      current ⟨.inr i.val, i.property⟩ := by
  simp only [reverseCopyLabelMap, i.property.2.1, Bool.false_eq_true, dite_false, i.property.2.2]

theorem reverseCopyLabelMap_erased {I σ : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (pivot : σ) (current : CopyScheduleAtoms role (n + 1) → σ)
    (i : CopyScheduleAtoms role n) (hi : copyScheduleRole role n i.val = .pivot n) :
    reverseCopyLabelMap role n b pivot current i = pivot := by
  simp [reverseCopyLabelMap, hi, CopyScheduleRole.copiedAt, CopyScheduleRole.erasedAt]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentWords
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact constituent words of the surviving grouped atoms -/

namespace Ostmann

open scoped BigOperators Classical

theorem scheduleConstituentWord_prod {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) (v : CopyScheduleAtoms role n)
    (q : SurvivingConstituent role size n → ℕ) :
    ((scheduleConstituentWord role size n v).map q).prod =
      ∏ k : Fin (size (copyScheduleOrigin n v.val)), q ((survivingConstituentEquiv role size n).symm ⟨v, k⟩) := by
  rw [scheduleConstituentWord, List.map_ofFn, List.prod_ofFn]
  rfl

/-- Constituent-level pairwise coprimality implies the exact top grouped
coprimality required by the full Fourier coefficient. -/
theorem scheduleConstituentWord_pairwise {I : Type*}
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (q : SurvivingConstituent role size n → ℕ)
    (hq : Pairwise (fun i j => (q i).Coprime (q j))) :
    Pairwise (fun v w : CopyScheduleAtoms role n =>
      ((scheduleConstituentWord role size n v).map q).prod.Coprime
        ((scheduleConstituentWord role size n w).map q).prod) := by
  intro v w hvw
  rw [scheduleConstituentWord_prod, scheduleConstituentWord_prod]
  apply Nat.coprime_fintype_prod_left_iff.mpr
  intro k
  apply Nat.coprime_fintype_prod_right_iff.mpr
  intro l
  apply hq
  intro he
  apply hvw
  exact congrArg Sigma.fst ((survivingConstituentEquiv role size n).symm.injective he)

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentAtomSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual constituent support implies the grouped root support -/

namespace Ostmann

open scoped BigOperators Classical

theorem scheduleConstituentWord_coprime_left {I : Type*}
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (q : SurvivingConstituent role size n → ℕ) (M : ℕ)
    (hM : ∀ i, M.Coprime (q i)) (v : CopyScheduleAtoms role n) :
    M.Coprime ((scheduleConstituentWord role size n v).map q).prod := by
  rw [scheduleConstituentWord_prod]
  exact Nat.coprime_fintype_prod_right_iff.mpr fun _ => hM _

theorem scheduleConstituentWord_coprime_right {I : Type*}
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (q : SurvivingConstituent role size n → ℕ) (M : ℕ)
    (hM : ∀ i, (q i).Coprime M) (v : CopyScheduleAtoms role n) :
    ((scheduleConstituentWord role size n v).map q).prod.Coprime M := by
  exact (scheduleConstituentWord_coprime_left role size n q M (fun i => (hM i).symm) v).symm

/-- Every coprimality and frequency-unit component of the next grouped guard
is supplied by the constituent-level arithmetic transfer. -/
theorem constituent_fullAtomRootGuard {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j)) (n : ℕ)
    (q : SurvivingConstituent role size (n + 1) → ℕ) (M : ℕ) (s : ℤ)
    (hq : Pairwise (fun i j => (q i).Coprime (q j)))
    (hM : ∀ i, M.Coprime (q i)) (hs : ∀ i, (q i).Coprime s.natAbs)
    (hrange : ∀ r ∈ ranges (n + 1), r.Holds
      (fun v => ((scheduleConstituentWord role size (n + 1) v).map q).prod)) :
    fullAtomRootGuard role ranges n
      (fun v => ((scheduleConstituentWord role size (n + 1) v).map q).prod) M s := by
  exact ⟨scheduleConstituentWord_pairwise role size (n + 1) q hq,
    scheduleConstituentWord_coprime_left role size (n + 1) q M hM,
    scheduleConstituentWord_coprime_right role size (n + 1) q s.natAbs hs, hrange⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SupportedPivotTransfer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pivot transfer with bounds imposed on the actual nonzero support -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

/-- The residue identity is needed only for pairs with nonzero coefficients.
Thus the original coprimality indicator stays inside the coefficient. -/
theorem pivot_square_split_on_support {A : Type*} [Fintype A]
    (M : ℕ) [NeZero M] (L : A → ℕ) (v : A → ℤ) (c : A → ℂ)
    (hL : ∀ a, c a ≠ 0 → (L a).Coprime M) :
    (∑ u : Fin M, ‖groupedCoefficient (fun a => pivotResidueKey M (L a) (v a)) c u‖ ^ 2) =
      (pivotDiagonal L v c).re + (pivotOffDiagonal M L v c).re := by
  have hh := diagonal_real_eq_sum_sq (fun a => pivotResidueKey M (L a) (v a)) c (fun _ => 1)
  simp only [Complex.ofReal_one, one_mul] at hh
  rw [← hh, ← Complex.add_re]
  congr 1
  unfold pivotDiagonal pivotOffDiagonal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  by_cases ha : c a = 0
  · simp [ha]
  by_cases hb : c b = 0
  · simp [hb]
  simp only [pivotResidueKey_eq_iff M (L a) (L b) (hL a ha) (hL b hb)]
  by_cases hz : v a * L b - v b * L a = 0
  · simp [hz]
  · by_cases hd : (M : ℤ) ∣ v a * L b - v b * L a <;> simp [hz, hd]

theorem pivotOffDiagonal_frequency_on_support {A : Type*} [Fintype A]
    (M B H V : ℕ) (hM : 0 < M) (L : A → ℕ) (v : A → ℤ) (c : A → ℂ)
    (hv : ∀ a, c a ≠ 0 → (v a).natAbs ≤ B)
    (hL : ∀ a, c a ≠ 0 → L a ≤ H) (hscale : 2 * B * H ≤ V * M) :
    pivotOffDiagonal M L v c = ∑ s ∈ transferFrequencyRange V,
      ∑ a, ∑ b, if s ≠ 0 ∧ v a * L b - v b * L a = s * M
        then c a * conj (c b) else 0 := by
  have he (a b : A) :
      (if v a * L b - v b * L a ≠ 0 ∧ (M : ℤ) ∣ v a * L b - v b * L a
        then c a * conj (c b) else 0) =
      ∑ s ∈ transferFrequencyRange V,
        if s ≠ 0 ∧ v a * L b - v b * L a = s * M then c a * conj (c b) else 0 := by
    by_cases ha : c a = 0
    · simp [ha]
    by_cases hb : c b = 0
    · simp [hb]
    exact transferred_frequency_sum_bounded M (L a) (L b) B H V hM (v a) (v b)
      (hv a ha) (hv b hb) (hL a ha) (hL b hb) hscale _
  unfold pivotOffDiagonal
  simp_rw [he]
  calc
    _ = ∑ a, ∑ s ∈ transferFrequencyRange V, ∑ b,
        if s ≠ 0 ∧ v a * L b - v b * L a = s * M then c a * conj (c b) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

/-- Positivity of the active product alone makes the zero-numerator part
a square. Frequency size is needed later to identify its prime matching,
but is not needed for this nonnegativity step. -/
theorem pivotDiagonal_nonneg_of_positive_support {A : Type*} [Fintype A]
    (L : A → ℕ) (v : A → ℤ) (c : A → ℂ)
    (hpos : ∀ a, c a ≠ 0 → 0 < L a) : 0 ≤ (pivotDiagonal L v c).re := by
  have hh := finite_key_square_nonneg (fun a => (v a : ℚ) / (L a : ℚ)) c
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  unfold pivotDiagonal
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases ha : c a = 0
  · simp [ha]
  by_cases hb : c b = 0
  · simp [hb]
  have hLa : (L a : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hpos a ha))
  have hLb : (L b : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hpos b hb))
  have he : v a * L b - v b * L a = 0 ↔
      (v a : ℚ) / (L a : ℚ) = (v b : ℚ) / (L b : ℚ) := by
    rw [div_eq_div_iff hLa hLb]
    constructor
    · intro h
      exact_mod_cast sub_eq_zero.mp h
    · intro h
      exact sub_eq_zero.mpr (by exact_mod_cast h)
  by_cases hz : v a * L b - v b * L a = 0
  · simp only [hz, he.mp hz, ite_true, if_true]
  · simp only [hz, mt he.mpr hz, ite_false, if_false]

/-- This is the extended integer sum with the original support left in its
coefficients. Every off-diagonal term has one forced positive pivot. -/
theorem sum_pivotOffDiagonal_substitution_on_support {A : Type*} [Fintype A]
    (T : Finset ℕ) (hT : ∀ M ∈ T, 0 < M) (B H V : ℕ)
    (L : A → ℕ) (v : A → ℤ) (c : ℕ → A → ℂ)
    (hv : ∀ M ∈ T, ∀ a, c M a ≠ 0 → (v a).natAbs ≤ B)
    (hL : ∀ M ∈ T, ∀ a, c M a ≠ 0 → L a ≤ H)
    (hscale : ∀ M ∈ T, 2 * B * H ≤ V * M) :
    (∑ M ∈ T, pivotOffDiagonal M L v (c M)) =
      ∑ s ∈ transferFrequencyRange V, ∑ a, ∑ b,
        if validTransferredPivot T (v a * L b - v b * L a) s
        then c (reconstructedPivot (v a * L b - v b * L a) s) a *
          conj (c (reconstructedPivot (v a * L b - v b * L a) s) b) else 0 := by
  calc
    _ = ∑ M ∈ T, ∑ s ∈ transferFrequencyRange V, ∑ a, ∑ b,
        if s ≠ 0 ∧ v a * L b - v b * L a = s * M then c M a * conj (c M b) else 0 := by
      apply Finset.sum_congr rfl
      intro M hMT
      exact pivotOffDiagonal_frequency_on_support M B H V (hT M hMT) L v (c M)
        (hv M hMT) (hL M hMT) (hscale M hMT)
    _ = _ := offDiagonal_pivot_substitution T hT (transferFrequencyRange V) L v c

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalPivotTransfer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The supported transfer from actual prime tuples to positive integers -/

namespace Ostmann

open scoped BigOperators Classical

/-- All coprimality and interval restrictions may remain in `c`. The
extended integer has no prime tuple or character attached to it. -/
theorem original_pivot_transfer_real {A : Type*} [Fintype A]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} (Q : Fin n → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQ : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (S : Finset (Fin n → P)) (hS : ∀ x ∈ S, Function.Injective x)
    (T : Finset ℕ) (hTpos : ∀ M ∈ T, 0 < M)
    (hT : ∀ x ∈ S, (∏ i, (x i : ℕ)) ∈ T)
    (row : ∀ x : Fin n → P, Fin (∏ i, (x i : ℕ)) → ℂ)
    (hrow : ∀ x ∈ S, ∀ u, ‖row x u‖ ≤ 1)
    (L : A → ℕ) (v : A → ℤ) (c : ℕ → A → ℂ)
    (hL : ∀ M ∈ T, ∀ a, c M a ≠ 0 → (L a).Coprime M) :
    ‖∑ x ∈ S, (productPrior (fun i => primeSubsetPrior P (Q i)) x : ℂ) *
      ∑ a, row x (primeTuplePivotKey P hP x (L a) (v a)) * c (∏ i, (x i : ℕ)) a‖ ^ 2 ≤
      ((n.factorial : ℝ) * ∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) *
        ((∑ M ∈ T, (pivotDiagonal L v (c M)).re) +
          (∑ M ∈ T, pivotOffDiagonal M L v (c M)).re) := by
  let B : (M : ℕ) → Fin M → ℂ := fun M =>
    if hM : 0 < M then
      groupedCoefficient (fun a => positiveIntegerPivotKey M hM (L a) (v a)) (c M)
    else fun _ => 0
  have he : (∑ x ∈ S, (productPrior (fun i => primeSubsetPrior P (Q i)) x : ℂ) *
      ∑ a, row x (primeTuplePivotKey P hP x (L a) (v a)) * c (∏ i, (x i : ℕ)) a) =
      ∑ x ∈ S, (productPrior (fun i => primeSubsetPrior P (Q i)) x : ℂ) *
        ∑ u, row x u * B (∏ i, (x i : ℕ)) u := by
    apply Finset.sum_congr rfl
    intro x _
    have hx := transferPrimeTupleProduct_pos P hP x
    simp only [B, dite_eq_left hx]
    congr 1
    exact pivot_residue_grouping (fun a => primeTuplePivotKey P hP x (L a) (v a))
      (row x) (c (∏ i, (x i : ℕ)))
  rw [he]
  have hb := pivot_integer_transfer P hP Q hQP hQ S hS T hT row hrow B
  apply hb.trans_eq
  congr 1
  calc
    _ = ∑ M ∈ T, ((pivotDiagonal L v (c M)).re + (pivotOffDiagonal M L v (c M)).re) := by
      apply Finset.sum_congr rfl
      intro M hMT
      have hM := hTpos M hMT
      let : NeZero M := ⟨Nat.ne_of_gt hM⟩
      simpa only [B, dite_eq_left hM, positiveIntegerPivotKey] using
        pivot_square_split_on_support M L v (c M) (hL M hMT)
    _ = _ := by rw [Finset.sum_add_distrib, Complex.re_sum]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PivotKeyReduction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reduction of the actual integer pivot key at each constituent prime -/

namespace Ostmann

open scoped BigOperators Classical

theorem pivotResidueKey_val (M : ℕ) [NeZero M] (L : ℕ) (v : ℤ) :
    ((pivotResidueKey M L v).val : ZMod M) = (v : ZMod M) * (L : ZMod M)⁻¹ := by
  cases M with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ M =>
    change (((v : ZMod (M + 1)) * (L : ZMod (M + 1))⁻¹).val : ZMod (M + 1)) = _
    exact ZMod.natCast_zmod_val _

/-- Key multiplication is valid already modulo the complete composite pivot. -/
theorem pivotResidueKey_mul (M : ℕ) [NeZero M] (L : ℕ) (v : ℤ)
    (hL : L.Coprime M) :
    ((pivotResidueKey M L v).val : ZMod M) * (L : ZMod M) = (v : ZMod M) := by
  rw [pivotResidueKey_val, mul_assoc,
    ZMod.inv_mul_of_unit _ ((ZMod.isUnit_iff_coprime L M).mpr hL), mul_one]

/-- The same key reduces correctly at every prime dividing the pivot. No
field structure on the composite pivot ring is used. -/
theorem pivotResidueKey_mul_at_divisor (M : ℕ) [NeZero M] (L : ℕ) (v : ℤ)
    {p : ℕ} (hp : p ∣ M) (hL : L.Coprime M) :
    ((pivotResidueKey M L v).val : ZMod p) * (L : ZMod p) = (v : ZMod p) := by
  have he := congrArg (ZMod.castHom hp (ZMod p)) (pivotResidueKey_mul M L v hL)
  simpa only [map_mul, map_natCast, map_intCast] using he

theorem positiveIntegerPivotKey_mul_at_divisor (M : ℕ) (hM : 0 < M)
    (L : ℕ) (v : ℤ) {p : ℕ} (hp : p ∣ M) (hL : L.Coprime M) :
    ((positiveIntegerPivotKey M hM L v).val : ZMod p) * (L : ZMod p) = (v : ZMod p) := by
  let : NeZero M := ⟨hM.ne'⟩
  exact pivotResidueKey_mul_at_divisor M L v hp hL

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GroupedResidueRow
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The entire outgoing pivot phase factors through the composite residue key -/

namespace Ostmann

open scoped BigOperators Classical

theorem groupedResidueRow_norm_le_one {K : Type*} [Fintype K] (P : K → ℕ)
    [∀ k, NeZero (P k)] (χ : ∀ k, DirichletCharacter ℂ (P k))
    (κ : K → ℂ) (hκ : ∀ k, ‖κ k‖ ≤ 1) (t : ∀ k, ZMod (P k))
    (Y : ℕ) (ε : K → ℤ) (u : Fin (∏ k, P k)) :
    ‖groupedResidueRow P χ κ t Y ε u‖ ≤ 1 :=
  pivotTupleRow_norm_le_one P χ κ hκ t _ _ _ ε

/-- A local outgoing factor is exactly the bounded residue row. The hypotheses
are the literal cofactor and unit conditions of the supported prime tuple. -/
theorem grouped_outgoing_local {p : ℕ} [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (κ : ℂ) (t : ZMod p)
    (D H Y M : ℕ) (hM : 0 < M) (v ε : ℤ)
    (hpM : p ∣ M) (hHM : H.Coprime M)
    (hD : (D : ZMod p) ≠ 0) (hY : (Y : ZMod p) ≠ 0)
    (hv : (v : ZMod p) ≠ 0) :
    ZMod.stdAddChar (t * (((D * H * Y : ℕ) : ZMod p)⁻¹ * (v : ZMod p))) *
      (κ * χ (v : ZMod p) ^ (-ε)) * χ ((D * H * Y : ℕ) : ZMod p) ^ ε =
    pivotLocalRow χ κ t (D : ZMod p) (Y : ZMod p)
      ((positiveIntegerPivotKey M hM H v).val : ZMod p) ε := by
  let u : ZMod p := (positiveIntegerPivotKey M hM H v).val
  have hrel : (v : ZMod p) = u * (H : ZMod p) :=
    (positiveIntegerPivotKey_mul_at_divisor M hM H v hpM hHM).symm
  have hH : (H : ZMod p) ≠ 0 := by
    have hc := hHM.of_dvd_right hpM
    exact isUnit_iff_ne_zero.mp ((ZMod.isUnit_iff_coprime H p).mpr hc)
  have hu : u ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hrel
    exact hv hrel
  have hh := pivotLocalRow_eq χ κ t (D : ZMod p) (Y : ZMod p) (H : ZMod p)
    (v : ZMod p) u ε hD hY hH hu hrel
  have hC : ((D * H * Y : ℕ) : ZMod p) = (D : ZMod p) * (Y : ZMod p) * (H : ZMod p) := by
    push_cast
    ring
  rw [hC]
  have hA : ((D : ZMod p) * (Y : ZMod p) * (H : ZMod p))⁻¹ * v =
      (v : ZMod p) / ((D : ZMod p) * (Y : ZMod p) * (H : ZMod p)) := by
    rw [div_eq_mul_inv, mul_comm]
  rw [hA]
  calc
    _ = ZMod.stdAddChar (t * ((v : ZMod p) / ((D : ZMod p) * (Y : ZMod p) * (H : ZMod p)))) * κ *
        (χ (v : ZMod p) ^ (-ε) * χ ((D : ZMod p) * (Y : ZMod p) * (H : ZMod p)) ^ ε) := by ring
    _ = _ := hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GroupedPhaseFactorization
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact phase factorization for a supported grouped pivot -/

namespace Ostmann

open scoped BigOperators Classical

/-- All constituents are retained. The pivot row uses the single residue v/H
modulo their product; the retained factor uses that product as an integer. -/
theorem directedPrimePhase_factor_grouped {K I : Type*} [Fintype K] [Fintype I]
    (p : K ⊕ I → ℕ) [∀ j, Fact (p j).Prime]
    (χ : ∀ j, DirichletCharacter ℂ (p j))
    (t : ∀ j, ZMod (p j)) (ν : (K ⊕ I) → ℂ)
    (g : (K ⊕ I) → (K ⊕ I) → ℤ) (b : Option I → Option I → ℤ)
    (κ : K → ℂ) (ε : K → ℤ) (H Y : ℕ) (v : ℤ)
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (hHY : (∏ i, p (.inr i)) = H * Y)
    (hv : ∀ k, (v : ZMod (p (.inl k))) ≠ 0)
    (hν : ∀ k, ν (.inl k) = κ k * χ (.inl k) (v : ZMod (p (.inl k))) ^ (-ε k))
    (hself : ∀ k, g (.inl k) (.inl k) = 0)
    (hrow : ∀ k j, j ≠ .inl k → g (.inl k) j = ε k)
    (hpivot : ∀ i k, g (.inr i) (.inl k) = b (some i) none)
    (hrest : ∀ i j, g (.inr i) (.inr j) = b (some i) (some j)) :
    directedPrimePhase p χ t ν g v =
      groupedResidueRow (fun k => p (.inl k)) (fun k => χ (.inl k)) κ
        (fun k => t (.inl k)) Y ε
        (positiveIntegerPivotKey (∏ k, p (.inl k))
          (groupedPivotProduct_pos (fun k => p (.inl k))) H v) *
      retainedGroupedPhase (fun i => p (.inr i)) (fun i => χ (.inr i))
        (fun i => t (.inr i)) (fun i => ν (.inr i)) b (∏ k, p (.inl k)) v := by
  have hcross (k : K) : (p (.inl k)).Coprime (H * Y) := by
    rw [← hHY]
    exact Nat.coprime_prod_right_iff.mpr fun i _ => hc (by intro he; cases he)
  have hHM : H.Coprime (∏ k, p (.inl k)) := by
    exact Nat.coprime_prod_right_iff.mpr fun k _ =>
      (hcross k).symm.of_dvd_left (Nat.dvd_mul_right H Y)
  have hD (k : K) : (tupleCofactor (fun k => p (.inl k)) k : ZMod (p (.inl k))) ≠ 0 := by
    have hcp : Pairwise (fun i j : K => (p (.inl i)).Coprime (p (.inl j))) := by
      intro i j hij
      exact hc (fun he => hij (Sum.inl.inj he))
    exact isUnit_iff_ne_zero.mp ((ZMod.isUnit_iff_coprime _ _).mpr
      (tupleCofactor_coprime _ hcp k))
  have hY (k : K) : (Y : ZMod (p (.inl k))) ≠ 0 := by
    exact isUnit_iff_ne_zero.mp ((ZMod.isUnit_iff_coprime _ _).mpr
      ((hcross k).symm.of_dvd_left (Nat.dvd_mul_left Y H)))
  rw [directedPrimePhase_remove_grouped_pivot p χ t ν g b ε v hself hrow hpivot hrest]
  congr 1
  unfold groupedResidueRow pivotTupleRow
  apply Finset.prod_congr rfl
  intro k _
  rw [hHY, hν]
  have he := grouped_outgoing_local (χ (.inl k)) (κ k) (t (.inl k))
    (tupleCofactor (fun k => p (.inl k)) k) H Y (∏ k, p (.inl k))
    (groupedPivotProduct_pos (fun k => p (.inl k))) v (ε k)
    (Finset.dvd_prod_of_mem _ (Finset.mem_univ k)) hHM (hD k) (hY k) (hv k)
  simpa only [mul_assoc] using he

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledPriorFubini
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact decomposition of the original prior at a scheduled pivot -/

namespace Ostmann

open scoped BigOperators Classical

/-- The retained outside prior occurs once, while the pivot and H priors
stay in their own independent blocks. -/
theorem scheduledPartitionAssignment_prior {I A : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n)
    (μ : {i : CopyScheduleVertex I n // CopyScheduleSurvives role n i} → A → ℝ)
    (u : CopyScheduleY role n → A) (x : Fin r → A) (l : CopyScheduleH role n → A) :
    (∏ i, μ i (scheduledPartitionAssignment role n r e u x l i)) =
      (∏ y, μ (enumeratedPartitionEquiv role n r e (.inr (.inr y))) (u y)) *
      (∏ i, μ (enumeratedPartitionEquiv role n r e (.inl i)) (x i)) *
      (∏ h, μ (enumeratedPartitionEquiv role n r e (.inr (.inl h))) (l h)) := by
  rw [← (enumeratedPartitionEquiv role n r e).prod_comp]
  simp only [scheduledPartitionAssignment_apply, Fintype.prod_sum_type,
    Sum.elim_inl, Sum.elim_inr]
  ring

/-- This is the precise finite Fubini identity used by the current amplitude;
it changes no marginal, including the common outside sample. -/
theorem scheduled_prior_fubini {I A : Type*} [Fintype I] [Fintype A]
    (role : I → CopyScheduleRole) (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n)
    (μ : {i : CopyScheduleVertex I n // CopyScheduleSurvives role n i} → A → ℝ)
    (F : ({i : CopyScheduleVertex I n // CopyScheduleSurvives role n i} → A) → ℂ) :
    (∑ a, ((∏ i, μ i (a i) : ℝ) : ℂ) * F a) =
      ∑ u : CopyScheduleY role n → A,
        ((∏ y, μ (enumeratedPartitionEquiv role n r e (.inr (.inr y))) (u y) : ℝ) : ℂ) *
        ∑ x : Fin r → A,
          ((∏ i, μ (enumeratedPartitionEquiv role n r e (.inl i)) (x i) : ℝ) : ℂ) *
          ∑ l : CopyScheduleH role n → A,
            ((∏ h, μ (enumeratedPartitionEquiv role n r e (.inr (.inl h))) (l h) : ℝ) : ℂ) *
              F (scheduledPartitionAssignment role n r e u x l) := by
  rw [← (scheduledPartitionAssignmentEquiv (A := A) role n r e).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  change ((∏ i, μ i (scheduledPartitionAssignment role n r e u x l i) : ℝ) : ℂ) * _ = _
  rw [scheduledPartitionAssignment_prior]
  change _ * F (scheduledPartitionAssignment role n r e u x l) = _
  push_cast
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_CopiedPriorFubini
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The copied H priors and the single retained Y prior -/

namespace Ostmann

open scoped BigOperators Classical

theorem scheduledCopiedAssignment_prior {I A : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ)
    (μ : {i : CopyScheduleVertex I (n + 1) // CopyScheduleSurvives role (n + 1) i} → A → ℝ)
    (u : CopyScheduleY role n → A) (l r : CopyScheduleH role n → A) :
    (∏ i, μ i (scheduledCopiedAssignment role n u l r i)) =
      (∏ y, μ (scheduledOutputVertex role n (.inr y)) (u y)) *
      (∏ h, μ (scheduledOutputVertex role n (.inl (true, h))) (l h)) *
      (∏ h, μ (scheduledOutputVertex role n (.inl (false, h))) (r h)) := by
  rw [← (copyScheduleSurvivorEquiv role n).symm.prod_comp]
  simp only [Fintype.prod_sum_type, Fintype.prod_prod_type, Fintype.prod_bool,
    scheduledOutputVertex, scheduledCopiedAssignment, Equiv.apply_symm_apply]
  ring

/-- The off-diagonal sum samples two independent H copies and retains one Y.
No second outside prior is inserted when passing to the next level. -/
theorem copied_prior_fubini {I A : Type*} [Fintype I] [Fintype A]
    (role : I → CopyScheduleRole) (n : ℕ)
    (μ : {i : CopyScheduleVertex I (n + 1) // CopyScheduleSurvives role (n + 1) i} → A → ℝ)
    (F : ({i : CopyScheduleVertex I (n + 1) // CopyScheduleSurvives role (n + 1) i} → A) → ℂ) :
    (∑ a, ((∏ i, μ i (a i) : ℝ) : ℂ) * F a) =
      ∑ u : CopyScheduleY role n → A,
        ((∏ y, μ (scheduledOutputVertex role n (.inr y)) (u y) : ℝ) : ℂ) *
        ∑ l : CopyScheduleH role n → A,
          ((∏ h, μ (scheduledOutputVertex role n (.inl (true, h))) (l h) : ℝ) : ℂ) *
          ∑ r : CopyScheduleH role n → A,
            ((∏ h, μ (scheduledOutputVertex role n (.inl (false, h))) (r h) : ℝ) : ℂ) *
              F (scheduledCopiedAssignment role n u l r) := by
  rw [← (scheduledCopiedAssignmentEquiv (A := A) role n).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  change ((∏ i, μ i (scheduledCopiedAssignment role n u l r i) : ℝ) : ℂ) * _ = _
  rw [scheduledCopiedAssignment_prior]
  change _ * F (scheduledCopiedAssignment role n u l r) = _
  push_cast
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledRolePrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The same original marginal follows every surviving copy -/

namespace Ostmann

open scoped BigOperators Classical

theorem scheduledRolePrior_copied {I A : Type*} (role : I → CopyScheduleRole)
    (μ : I → A → ℝ) (n : ℕ)
    (i : (Bool × CopyScheduleH role n) ⊕ CopyScheduleY role n) (a : A) :
    scheduledRolePrior role μ (n + 1) (scheduledOutputVertex role n i) a =
      match i with
      | .inl (_, h) => μ (copyScheduleOrigin n h.val) a
      | .inr y => μ (copyScheduleOrigin n y.val) a := by
  rcases i with ⟨b, h⟩ | y <;> rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentCopiedAssignment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Grouping the actual copied prime assignment -/

namespace Ostmann

open scoped BigOperators Classical

theorem constituentH_output {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) (b : Bool) (v : CopyScheduleH role n)
    (k : Fin (size (copyScheduleOrigin n v.val))) :
    (survivingConstituentEquiv role size (n + 1)).symm
        ⟨scheduledOutputVertex role n (.inl (b, v)), k⟩ =
      scheduledOutputVertex (fun i : Σ a, Fin (size a) => role i.1) n (.inl (b, constituentH role size n v k)) := by
  apply Subtype.ext
  rfl

theorem constituentY_output {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) (v : CopyScheduleY role n)
    (k : Fin (size (copyScheduleOrigin n v.val))) :
    (survivingConstituentEquiv role size (n + 1)).symm
        ⟨scheduledOutputVertex role n (.inr v), k⟩ =
      scheduledOutputVertex (fun i : Σ a, Fin (size a) => role i.1) n (.inr (constituentY role size n v k)) := by
  apply Subtype.ext
  rfl

theorem constituent_copied_assignment_word {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → ℕ)
    (l r : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → ℕ) (b : Bool) (v : CopyScheduleH role n) :
    ((scheduleConstituentWord role size (n + 1)
        (scheduledOutputVertex role n (.inl (b, v)))).map
      (scheduledCopiedAssignment (fun i : Σ a, Fin (size a) => role i.1) n u l r)).prod =
      ∏ k : Fin (size (copyScheduleOrigin n v.val)),
        (if b then l else r) (constituentH role size n v k) := by
  rw [scheduleConstituentWord_prod]
  apply Finset.prod_congr rfl
  intro k _
  change Fin (size (copyScheduleOrigin n v.val)) at k
  rw [constituentH_output role size n b v k]
  cases b
  · exact scheduledCopiedAssignment_right _ _ _ _ _ _
  · exact scheduledCopiedAssignment_left _ _ _ _ _ _

theorem constituent_retained_assignment_word {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → ℕ)
    (l r : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → ℕ) (v : CopyScheduleY role n) :
    ((scheduleConstituentWord role size (n + 1)
        (scheduledOutputVertex role n (.inr v))).map
      (scheduledCopiedAssignment (fun i : Σ a, Fin (size a) => role i.1) n u l r)).prod =
      ∏ k : Fin (size (copyScheduleOrigin n v.val)), u (constituentY role size n v k) := by
  rw [scheduleConstituentWord_prod]
  apply Finset.prod_congr rfl
  intro k _
  change Fin (size (copyScheduleOrigin n v.val)) at k
  rw [constituentY_output role size n v k]
  exact scheduledCopiedAssignment_outside _ _ _ _ _ _

/-- Taking products of the copied prime slots is exactly the atom assignment
used by the reverse transfer system. -/
theorem constituent_copied_assignment {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → ℕ)
    (l r : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → ℕ) :
    (fun v => ((scheduleConstituentWord role size (n + 1) v).map
        (scheduledCopiedAssignment (fun i : Σ a, Fin (size a) => role i.1) n u l r)).prod) =
      scheduledCopiedAssignment role n
        (fun y => ∏ k, u (constituentY role size n y k))
        (fun h => ∏ k, l (constituentH role size n h k))
        (fun h => ∏ k, r (constituentH role size n h k)) := by
  funext v
  obtain ⟨j, rfl⟩ := (copyScheduleSurvivorEquiv role n).symm.surjective v
  rcases j with ⟨b, h⟩ | y
  · cases b
    · exact (constituent_copied_assignment_word role size n u l r false h).trans
        (scheduledCopiedAssignment_right role n
          (fun y => ∏ k, u (constituentY role size n y k))
          (fun h => ∏ k, l (constituentH role size n h k))
          (fun h => ∏ k, r (constituentH role size n h k)) h).symm
    · exact (constituent_copied_assignment_word role size n u l r true h).trans
        (scheduledCopiedAssignment_left role n
          (fun y => ∏ k, u (constituentY role size n y k))
          (fun h => ∏ k, l (constituentH role size n h k))
          (fun h => ∏ k, r (constituentH role size n h k)) h).symm
  · exact (constituent_retained_assignment_word role size n u l r y).trans
      (scheduledCopiedAssignment_outside role n
        (fun y => ∏ k, u (constituentY role size n y k))
        (fun h => ∏ k, l (constituentH role size n h k))
        (fun h => ∏ k, r (constituentH role size n h k)) y).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InsertedAtomAssignment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Inserting the reconstructed composite pivot in either old branch -/

namespace Ostmann

open scoped Classical

theorem scheduledInsertedAtoms_pivot {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (P : ℕ) (l : CopyScheduleH role n → ℕ) (u : CopyScheduleY role n → ℕ)
    (p : CurrentPivotConstituent role n) :
    scheduledInsertedAtoms role n P l u (scheduledPartitionEquiv role n (.inl p)) = P := by
  simp only [scheduledInsertedAtoms, Equiv.symm_apply_apply]

theorem scheduledInsertedAtoms_H {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (P : ℕ) (l : CopyScheduleH role n → ℕ) (u : CopyScheduleY role n → ℕ)
    (h : CopyScheduleH role n) :
    scheduledInsertedAtoms role n P l u ⟨h.val, h.property.1⟩ = l h := by
  change scheduledInsertedAtoms role n P l u (scheduledPartitionEquiv role n (.inr (.inl h))) = _
  simp only [scheduledInsertedAtoms, Equiv.symm_apply_apply]

theorem scheduledInsertedAtoms_Y {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (P : ℕ) (l : CopyScheduleH role n → ℕ) (u : CopyScheduleY role n → ℕ)
    (y : CopyScheduleY role n) :
    scheduledInsertedAtoms role n P l u ⟨y.val, y.property.1⟩ = u y := by
  change scheduledInsertedAtoms role n P l u (scheduledPartitionEquiv role n (.inr (.inr y))) = _
  simp only [scheduledInsertedAtoms, Equiv.symm_apply_apply]

/-- The arithmetic reverse substitution uses precisely the old H branch,
the single common outside assignment, and the forced composite pivot. -/
theorem reverseCopiedAtoms_eq_inserted {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (P : ℕ)
    (u : CopyScheduleY role n → ℕ) (l r : CopyScheduleH role n → ℕ) :
    reverseCopyLabelMap role n b P (scheduledCopiedAssignment role n u l r) =
      scheduledInsertedAtoms role n P (if b then l else r) u := by
  funext i
  obtain ⟨j, rfl⟩ := (scheduledPartitionEquiv role n).surjective i
  rcases j with p | h | y
  · rw [reverseCopyLabelMap_erased role n b P _ _
      (copyScheduleRole_positive role p.val n p.property n), scheduledInsertedAtoms_pivot]
  · change reverseCopyLabelMap role n b P _ ⟨h.val, h.property.1⟩ = _
    apply (reverseCopyLabelMap_copied role n b P _ h).trans
    apply Eq.trans (show scheduledCopiedAssignment role n u l r
        (scheduledOutputVertex role n (.inl (b, h))) = (if b then l else r) h from ?_)
      (scheduledInsertedAtoms_H role n P (if b then l else r) u h).symm
    cases b
    · exact scheduledCopiedAssignment_right role n u l r h
    · exact scheduledCopiedAssignment_left role n u l r h
  · change reverseCopyLabelMap role n b P _ ⟨y.val, y.property.1⟩ = _
    exact (reverseCopyLabelMap_retained role n b P _ y).trans
      ((scheduledCopiedAssignment_outside role n u l r y).trans
        (scheduledInsertedAtoms_Y role n P (if b then l else r) u y).symm)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentPartitionAssignment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Grouping the current prime sample into its actual composite pivot -/

namespace Ostmann

open scoped BigOperators Classical

theorem copyConstituentEquiv_positive_inverse {I : Type*} (size : I → ℕ)
    (n : ℕ) (p : I) (k : Fin (size (copyScheduleOrigin n (copySchedulePositive n p)))) :
    (copyConstituentEquiv size n).symm ⟨copySchedulePositive n p, k⟩ =
      copySchedulePositive n ⟨p, ⟨k.val, by
        simpa only [copyScheduleOrigin_positive] using k.isLt⟩⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact congrArg (fun j => Sum.inl (true, j)) (ih k)

theorem constituent_pivot_entry {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) (p : I) (hp : role p = .pivot n)
    (hu : ∀ i, role i = .pivot n → i = p)
    (k : Fin (size (copyScheduleOrigin n (copySchedulePositive n p)))) :
    (survivingConstituentEquiv role size n).symm
        ⟨scheduledPartitionEquiv role n (.inl ⟨p, hp⟩), k⟩ =
      enumeratedPartitionEquiv (fun i : Σ a, Fin (size a) => role i.1) n (size p)
        (pivotConstituentEquiv role size n p hp hu)
        (.inl ⟨k.val, by simpa only [copyScheduleOrigin_positive] using k.isLt⟩) := by
  apply Subtype.ext
  exact copyConstituentEquiv_positive_inverse size n p k

/-- The current prime assignment groups to the inserted atom state. In
particular the pivot value is the product of all its original constituents. -/
theorem constituent_partition_assignment {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) (p : I) (hp : role p = .pivot n)
    (hu : ∀ i, role i = .pivot n → i = p)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → ℕ)
    (x : Fin (size p) → ℕ)
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → ℕ) :
    (fun v => ((scheduleConstituentWord role size n v).map
        (scheduledPartitionAssignment (fun i : Σ a, Fin (size a) => role i.1)
          n (size p) (pivotConstituentEquiv role size n p hp hu) u x l)).prod) =
      scheduledInsertedAtoms role n (∏ k, x k)
        (fun h => ∏ k, l (constituentH role size n h k))
        (fun y => ∏ k, u (constituentY role size n y k)) := by
  funext v
  obtain ⟨j, rfl⟩ := (scheduledPartitionEquiv role n).surjective v
  rcases j with q | h | y
  · obtain ⟨a, ha⟩ := q
    have he : a = p := hu a ha
    subst a
    rw [scheduledInsertedAtoms_pivot, scheduleConstituentWord_prod]
    apply Fintype.prod_equiv (finCongr (congrArg size (copyScheduleOrigin_positive n p)))
    intro k
    rw [constituent_pivot_entry role size n p hp hu k]
    exact scheduledPartitionAssignment_apply _ _ _ _ _ _ _ (.inl _)
  · rw [scheduleConstituentWord_prod]
    change _ = scheduledInsertedAtoms role n (∏ k, x k)
      (fun h => ∏ k, l (constituentH role size n h k))
      (fun y => ∏ k, u (constituentY role size n y k)) ⟨h.val, h.property.1⟩
    rw [scheduledInsertedAtoms_H]
    apply Finset.prod_congr rfl
    intro k _
    exact scheduledPartitionAssignment_apply _ _ _ _ _ _ _ (.inr (.inl (constituentH role size n h k)))
  · rw [scheduleConstituentWord_prod]
    change _ = scheduledInsertedAtoms role n (∏ k, x k)
      (fun h => ∏ k, l (constituentH role size n h k))
      (fun y => ∏ k, u (constituentY role size n y k)) ⟨y.val, y.property.1⟩
    rw [scheduledInsertedAtoms_Y]
    apply Finset.prod_congr rfl
    intro k _
    exact scheduledPartitionAssignment_apply _ _ _ _ _ _ _ (.inr (.inr (constituentY role size n y k)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FullCopiedWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full transferred weight in the actual two branch assignments -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

theorem scheduleAtomLeft_copied {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ)
    (u : CopyScheduleY role n → ℕ) (l r : CopyScheduleH role n → ℕ) :
    scheduleAtomLeft role ⟨n + 1, scheduledCopiedAssignment role n u l r⟩ = ∏ h, l h := rfl

theorem scheduleAtomRight_copied {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ)
    (u : CopyScheduleY role n → ℕ) (l r : CopyScheduleH role n → ℕ) :
    scheduleAtomRight role ⟨n + 1, scheduledCopiedAssignment role n u l r⟩ = ∏ h, r h := rfl

/-- The parent coefficient is exactly the product of the two inherited
coefficients at the forced pivot, with only the new root tests added. -/
theorem fullAtomTransferWeight_copied {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (n : ℕ)
    (u : CopyScheduleY role n → ℕ) (l r : CopyScheduleH role n → ℕ)
    (s : ℤ) (t t' : FrequencyTree ℤ n) (P : ℕ)
    (hP : ValidTransferNode (scheduleAtomSystem role childBound pivotBound)
      ⟨n + 1, scheduledCopiedAssignment role n u l r⟩
      s (frequencyRoot n t) (frequencyRoot n t') P) :
    fullAtomTransferWeight role childBound pivotBound ranges leaf (n + 1)
        (scheduledCopiedAssignment role n u l r) (s, t, t') =
      if fullAtomRootGuard role ranges n (scheduledCopiedAssignment role n u l r) P s then
        fullAtomTransferWeight role childBound pivotBound ranges leaf n
          (scheduledInsertedAtoms role n P l u) t *
        conj (fullAtomTransferWeight role childBound pivotBound ranges leaf n
          (scheduledInsertedAtoms role n P r u) t') else 0 := by
  rw [fullAtomTransferWeight_node role childBound pivotBound ranges leaf n _ _ P hP,
    reverseCopiedAtoms_eq_inserted, reverseCopiedAtoms_eq_inserted]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentPriorAssembly
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact original-prior assembly of the full constituent Fourier weight -/

namespace Ostmann

open scoped BigOperators Classical

theorem scheduledPartitionAssignment_map {I A B : Type*}
    (role : I → CopyScheduleRole) (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n)
    (f : A → B) (u : CopyScheduleY role n → A) (x : Fin r → A) (l : CopyScheduleH role n → A) :
    (fun i => f (scheduledPartitionAssignment role n r e u x l i)) =
      scheduledPartitionAssignment role n r e (f ∘ u) (f ∘ x) (f ∘ l) := by
  funext i
  obtain ⟨j, rfl⟩ := (enumeratedPartitionEquiv role n r e).surjective i
  simp only [scheduledPartitionAssignment_apply]
  rcases j with k | h | y <;> rfl

/-- The pivot tuple and both remaining coordinate blocks keep their original
marginals. The full coefficient depends on the pivot tuple only through its
product, as required by the arithmetic Cauchy step. -/
theorem constituent_weighted_prior_fubini {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ) (p : I)
    (hp : role p = .pivot n) (hu : ∀ i, role i = .pivot n → i = p)
    (P : Finset ℕ) (μ : SurvivingConstituent role size n → P → ℝ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (phase : (SurvivingConstituent role size n → P) → D → ℂ) :
    (∑ q : SurvivingConstituent role size n → P, ((∏ i, μ i (q i) : ℝ) : ℂ) *
      ∑ d, fullAtomTransferWeight role childBound pivotBound ranges leaf n
        (fun v => ((scheduleConstituentWord role size n v).map (fun i => (q i : ℕ))).prod)
        (hist d) * phase q d) =
    let e := pivotConstituentEquiv role size n p hp hu
    let ρ := fun i : Σ a, Fin (size a) => role i.1
    ∑ u : CopyScheduleY ρ n → P,
      ((∏ y, μ (enumeratedPartitionEquiv ρ n (size p) e (.inr (.inr y))) (u y) : ℝ) : ℂ) *
      ∑ x : Fin (size p) → P,
        ((∏ k, μ (enumeratedPartitionEquiv ρ n (size p) e (.inl k)) (x k) : ℝ) : ℂ) *
        ∑ l : CopyScheduleH ρ n → P,
          ((∏ h, μ (enumeratedPartitionEquiv ρ n (size p) e (.inr (.inl h))) (l h) : ℝ) : ℂ) *
          ∑ d, fullAtomTransferWeight role childBound pivotBound ranges leaf n
            (scheduledInsertedAtoms role n (∏ k, (x k : ℕ))
              (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
              (fun y => ∏ k, (u (constituentY role size n y k) : ℕ)))
            (hist d) * phase (scheduledPartitionAssignment ρ n (size p) e u x l) d := by
  dsimp only
  have hF := scheduled_prior_fubini (fun i : Σ a, Fin (size a) => role i.1)
    n (size p) (pivotConstituentEquiv role size n p hp hu) μ
    (fun q => ∑ d, fullAtomTransferWeight role childBound pivotBound ranges leaf n
      (fun v => ((scheduleConstituentWord role size n v).map (fun i => (q i : ℕ))).prod)
      (hist d) * phase q d)
  refine hF.trans ?_
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  congr 1
  have hmap := scheduledPartitionAssignment_map
    (fun i : Σ a, Fin (size a) => role i.1) n (size p)
    (pivotConstituentEquiv role size n p hp hu) (fun q : P => (q : ℕ)) u x l
  have hg := constituent_partition_assignment role size n p hp hu
    (fun y => (u y : ℕ)) (fun k => (x k : ℕ)) (fun h => (l h : ℕ))
  have hg' : (fun v => ((scheduleConstituentWord role size n v).map
      (fun i => ((scheduledPartitionAssignment (A := P) _ n (size p)
        (pivotConstituentEquiv role size n p hp hu) u x l i : P) : ℕ))).prod) =
      scheduledInsertedAtoms role n (∏ k, (x k : ℕ))
        (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
        (fun y => ∏ k, (u (constituentY role size n y k) : ℕ)) := by
    rw [hmap]
    exact hg
  rw [hg']

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_PrimeTupleResidueRow
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual harmonic-prior pivot row -/

namespace Ostmann

open scoped BigOperators Classical

theorem primeTupleResidueRow_norm_le_one (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} (χ : Fin n → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : Fin n → P → ℂ) (hκ : ∀ i p, ‖κ i p‖ ≤ 1) (t : ∀ p : ℕ, ZMod p)
    (Y : ℕ) (ε : Fin n → ℤ) (x : Fin n → P) (u : Fin (∏ i, (x i : ℕ))) :
    ‖primeTupleResidueRow P hP χ κ t Y ε x u‖ ≤ 1 := by
  let : ∀ i, Fact (x i : ℕ).Prime := fun i => ⟨hP (x i) (x i).property⟩
  exact groupedResidueRow_norm_le_one (fun i => (x i : ℕ)) (fun i => χ i (x i))
    (fun i => κ i (x i)) (fun i => hκ i (x i)) (fun i => t (x i)) Y ε u

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_AveragedArithmeticTransfer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining the complex off-diagonal through the outside average -/

namespace Ostmann

open scoped BigOperators

/-- The real-part form must be averaged before taking the norm of the next
amplitude. The original outside law may be a subprobability law. -/
theorem averaged_arithmetic_transfer {Y : Type*} [Fintype Y]
    (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y) (hmass : ∑ y, μ y ≤ 1)
    (η θ : Y → ℂ) (D : Y → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hlocal : ∀ y, ‖η y‖ ^ 2 ≤ C * (D y + (θ y).re)) :
    ‖∑ y, (μ y : ℂ) * η y‖ ^ 2 ≤
      C * ((∑ y, μ y * D y) + ‖∑ y, (μ y : ℂ) * θ y‖) := by
  have hRe : (∑ y, (μ y : ℂ) * θ y).re = ∑ y, μ y * (θ y).re := by
    simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  calc
    _ ≤ ∑ y, μ y * ‖η y‖ ^ 2 := subprobability_weighted_norm_sq_le μ hμ hmass η
    _ ≤ ∑ y, μ y * (C * (D y + (θ y).re)) :=
      Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hlocal y) (hμ y)
    _ = ∑ y, C * (μ y * D y + μ y * (θ y).re) := by
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = C * ((∑ y, μ y * D y) + ∑ y, μ y * (θ y).re) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ = C * ((∑ y, μ y * D y) + (∑ y, (μ y : ℂ) * θ y).re) := by rw [hRe]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl (Complex.re_le_norm _)) hC

/-- A concrete harmonic-prior loss bounded by exp(d) gives the normalized
transfer inequality used by the iteration theorem. -/
theorem normalized_arithmetic_transfer (η θ : ℂ) (D C d : ℝ)
    (hD : 0 ≤ D) (hC : C ≤ Real.exp d)
    (htransfer : ‖η‖ ^ 2 ≤ C * (D + ‖θ‖)) :
    Real.exp (-d) * ‖η‖ ^ 2 ≤ D + ‖θ‖ := by
  have hCD : Real.exp (-d) * C ≤ 1 := by
    calc
      _ ≤ Real.exp (-d) * Real.exp d := mul_le_mul_of_nonneg_left hC (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  calc
    _ ≤ Real.exp (-d) * (C * (D + ‖θ‖)) :=
      mul_le_mul_of_nonneg_left htransfer (Real.exp_pos _).le
    _ = (Real.exp (-d) * C) * (D + ‖θ‖) := by ring
    _ ≤ 1 * (D + ‖θ‖) := mul_le_mul_of_nonneg_right hCD (add_nonneg hD (norm_nonneg _))
    _ = _ := one_mul _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalAveragedTransfer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual averaged arithmetic step with its forced integer substitution -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

/-- The original prime-tuple prior, both Cauchy steps, and the entire
integer off-diagonal are included in this normalized transfer inequality. -/
theorem original_averaged_pivot_transfer {A Y : Type*} [Fintype A] [Fintype Y]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} (Q : Fin n → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQ : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (S : Finset (Fin n → P)) (hS : ∀ x ∈ S, Function.Injective x)
    (T : Finset ℕ) (hTpos : ∀ M ∈ T, 0 < M)
    (hT : ∀ x ∈ S, (∏ i, (x i : ℕ)) ∈ T)
    (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y) (hmass : ∑ y, μ y ≤ 1)
    (row : Y → (x : Fin n → P) → Fin (∏ i, (x i : ℕ)) → ℂ)
    (hrow : ∀ y x, x ∈ S → ∀ u, ‖row y x u‖ ≤ 1)
    (L : A → ℕ) (v : A → ℤ) (c : Y → ℕ → A → ℂ)
    (hcoprime : ∀ y M, M ∈ T → ∀ a, c y M a ≠ 0 → (L a).Coprime M)
    (hpositive : ∀ y M, M ∈ T → ∀ a, c y M a ≠ 0 → 0 < L a)
    (B H V : ℕ)
    (hv : ∀ y M, M ∈ T → ∀ a, c y M a ≠ 0 → (v a).natAbs ≤ B)
    (hL : ∀ y M, M ∈ T → ∀ a, c y M a ≠ 0 → L a ≤ H)
    (hscale : ∀ M ∈ T, 2 * B * H ≤ V * M)
    (d : ℝ) (hcost : ((n.factorial : ℝ) * ∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) ≤ Real.exp d) :
    Real.exp (-d) *
      ‖∑ y, (μ y : ℂ) * (∑ x ∈ S, (productPrior (fun i => primeSubsetPrior P (Q i)) x : ℂ) *
        ∑ a, row y x (primeTuplePivotKey P hP x (L a) (v a)) * c y (∏ i, (x i : ℕ)) a)‖ ^ 2 ≤
      (∑ y, μ y * (∑ M ∈ T, (pivotDiagonal L v (c y M)).re)) +
        ‖∑ y, (μ y : ℂ) * reconstructedOffDiagonal T V L v (c y)‖ := by
  let η : Y → ℂ := fun y => ∑ x ∈ S,
    (productPrior (fun i => primeSubsetPrior P (Q i)) x : ℂ) *
      ∑ a, row y x (primeTuplePivotKey P hP x (L a) (v a)) * c y (∏ i, (x i : ℕ)) a
  let D : Y → ℝ := fun y => ∑ M ∈ T, (pivotDiagonal L v (c y M)).re
  let θ : Y → ℂ := fun y => reconstructedOffDiagonal T V L v (c y)
  let K := (n.factorial : ℝ) * ∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹
  have hlocal (y : Y) : ‖η y‖ ^ 2 ≤ K * (D y + (θ y).re) := by
    have ht := original_pivot_transfer_real P hP Q hQP hQ S hS T hTpos hT
      (row y) (hrow y) L v (c y) (hcoprime y)
    have he := sum_pivotOffDiagonal_substitution_on_support T hTpos B H V L v (c y)
      (hv y) (hL y) hscale
    rw [he] at ht
    exact ht
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hD : 0 ≤ ∑ y, μ y * D y := by
    apply Finset.sum_nonneg
    intro y _
    apply mul_nonneg (hμ y)
    apply Finset.sum_nonneg
    intro M hMT
    exact pivotDiagonal_nonneg_of_positive_support L v (c y M) (hpositive y M hMT)
  exact normalized_arithmetic_transfer _ _ _ K d hD hcost
    (averaged_arithmetic_transfer μ hμ hmass η θ D K hK hlocal)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ReconstructedPhaseWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The forced-pivot off-diagonal is the actual next directed amplitude -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

private theorem branchPairwise_parts {H Y : Type*} [Fintype H] [Fintype Y]
    (L : H → ℕ) (U : Y → ℕ)
    (hc : Pairwise (fun i j => (Sum.elim L U i).Coprime (Sum.elim L U j))) :
    Pairwise (fun h k => (L h).Coprime (L k)) ∧
      Pairwise (fun y z => (U y).Coprime (U z)) ∧ (∏ h, L h).Coprime (∏ y, U y) := by
  refine ⟨fun h k hne => hc (fun he => hne (Sum.inl.inj he)),
    fun y z hne => hc (fun he => hne (Sum.inr.inj he)), ?_⟩
  exact Nat.coprime_fintype_prod_left_iff.mpr fun h =>
    Nat.coprime_fintype_prod_right_iff.mpr fun y => hc (i := .inl h) (j := .inr y) (by intro he; cases he)

/-- Only the original branch supports are hypotheses. Cross-copy distinctness
and the units at the new root are consequences of the equation and ranges. -/
theorem reconstructedOffDiagonal_eq_copiedWeightedAmplitude
    {A H Y : Type*} [Fintype A] [Fintype H] [Fintype Y]
    (L : A → H → ℕ) (U : Y → ℕ)
    [∀ a h, Fact (L a h).Prime] [∀ y, Fact (U y).Prime]
    (t : ∀ p : ℕ, ZMod p)
    (χH : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χY : Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (ν : A → H → ℂ) (νY : A → Y → ℂ) (v : A → ℤ)
    (W : ℕ → A → ℂ) (T : Finset ℕ) (B K V : ℕ)
    (hT : ∀ M ∈ T, 0 < M)
    (hsupport : ∀ M ∈ T, ∀ a, W M a ≠ 0 →
      Pairwise (fun i j => (Sum.elim (L a) U i).Coprime (Sum.elim (L a) U j)) ∧
      M.Coprime ((∏ h, L a h) * ∏ y, U y) ∧ (v a).natAbs ≤ B ∧ (∏ h, L a h) ≤ K)
    (hscale : ∀ M ∈ T, 2 * B * K ≤ V * M)
    (hlargeL : ∀ a h, V < L a h) (hlargeU : ∀ y, V < U y)
    (hb : ∀ y, b (some (.inr y)) (some (.inr y)) = 0) :
    reconstructedOffDiagonal T V (fun a => ∏ h, L a h) v
        (retainedWeightedCoefficient L U t χH χY b ν νY v W) =
      copiedWeightedAmplitude L U t χH χY b ν νY v W T V := by
  unfold reconstructedOffDiagonal copiedWeightedAmplitude
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro a' _
  dsimp only
  split_ifs with hvalid
  · let M := reconstructedPivot (v a * (∏ h, L a' h) - v a' * (∏ h, L a h)) s
    by_cases hWa : W M a = 0
    · dsimp only [M] at hWa
      simp only [retainedWeightedCoefficient, hWa, zero_mul]
    by_cases hWa' : W M a' = 0
    · dsimp only [M] at hWa'
      simp only [retainedWeightedCoefficient, hWa', zero_mul, map_zero, mul_zero]
    have hMT : M ∈ T := hvalid.2.2.2
    obtain ⟨hpA, hmA, hvA, hLA⟩ := hsupport M hMT a hWa
    obtain ⟨hpB, hmB, hvB, hLB⟩ := hsupport M hMT a' hWa'
    obtain ⟨hpL, hpU, hLU⟩ := branchPairwise_parts (L a) U hpA
    obtain ⟨hpR, _, hRU⟩ := branchPairwise_parts (L a') U hpB
    have he := transfer_copiedDirectedPhase_of_ranges (L a) (L a') U t χH χY b
      (ν a) (ν a') (νY a) (νY a') M (v a) (v a') s
      (validTransferredPivot_equation T _ s hvalid) B K V (hT M hMT) hvalid.1 hvA hvB hLA hLB
      (hscale M hMT) hpL hpR hpU hLU hRU
      (Nat.coprime_mul_iff_right.mp hmA).1 (Nat.coprime_mul_iff_right.mp hmB).1
      (Nat.coprime_mul_iff_right.mp hmA).2 (hlargeL a) (hlargeL a') hlargeU hb
    simp only [retainedWeightedCoefficient, map_mul (starRingEnd ℂ)]
    calc
      _ = (W M a * conj (W M a')) *
          (retainedPrimePhase (L a) U t χH χY b (ν a) (νY a) M (v a) *
            conj (retainedPrimePhase (L a') U t χH χY b (ν a') (νY a') M (v a'))) := by ring
      _ = _ := by rw [he]
  · rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalDirectedTransfer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An arithmetic transfer of the actual supported directed amplitude -/

namespace Ostmann

open scoped BigOperators Classical

/-- This is the normalized transfer inequality with its actual prime residue
row and its next copied directed amplitude, rather than an assumed recurrence. -/
theorem original_directed_transfer {A H Y Z : Type*}
    [Fintype A] [Fintype H] [Fintype Y] [Fintype Z]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {n : ℕ}
    (Q : Fin n → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQ : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (S : Finset (Fin n → P)) (hS : ∀ x ∈ S, Function.Injective x)
    (T : Finset ℕ) (hT : ∀ M ∈ T, 0 < M) (hST : ∀ x ∈ S, (∏ i, (x i : ℕ)) ∈ T)
    (χP : Fin n → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : Fin n → P → ℂ) (hκ : ∀ i p, ‖κ i p‖ ≤ 1) (ε : Fin n → ℤ)
    (L : A → H → ℕ) (U : Z → Y → ℕ)
    [∀ a h, Fact (L a h).Prime] [∀ z y, Fact (U z y).Prime]
    (t : ∀ p : ℕ, ZMod p)
    (χH : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χY : Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (ν : Z → A → H → ℂ) (νY : Z → A → Y → ℂ) (v : A → ℤ)
    (W : Z → ℕ → A → ℂ) (μ : Z → ℝ)
    (hμ : ∀ z, 0 ≤ μ z) (hμsum : ∑ z, μ z ≤ 1)
    (B K V : ℕ)
    (hsupport : ∀ z M, M ∈ T → ∀ a, W z M a ≠ 0 →
      Pairwise (fun i j => (Sum.elim (L a) (U z) i).Coprime (Sum.elim (L a) (U z) j)) ∧
      M.Coprime ((∏ h, L a h) * ∏ y, U z y) ∧ (v a).natAbs ≤ B ∧ (∏ h, L a h) ≤ K)
    (hscale : ∀ M ∈ T, 2 * B * K ≤ V * M)
    (hlargeL : ∀ a h, V < L a h) (hlargeU : ∀ z y, V < U z y)
    (hb : ∀ y, b (some (.inr y)) (some (.inr y)) = 0)
    (d : ℝ) (hcost : ((n.factorial : ℝ) * ∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) ≤ Real.exp d) :
    Real.exp (-d) *
      ‖groupedDirectedAmplitude P hP Q S χP κ ε L U t χH χY b ν νY v W μ‖ ^ 2 ≤
        (∑ z, μ z * ∑ M ∈ T,
          (pivotDiagonal (fun a => ∏ h, L a h) v
            (retainedWeightedCoefficient L (U z) t χH χY b (ν z) (νY z) v (W z) M)).re) +
        ‖∑ z, (μ z : ℂ) * copiedWeightedAmplitude L (U z) t χH χY b
          (ν z) (νY z) v (W z) T V‖ := by
  let c : Z → ℕ → A → ℂ := fun z =>
    retainedWeightedCoefficient L (U z) t χH χY b (ν z) (νY z) v (W z)
  have hW (z M a) (hc : c z M a ≠ 0) : W z M a ≠ 0 := by
    intro hz
    apply hc
    simp only [c, retainedWeightedCoefficient, hz, zero_mul]
  have hcop (z M) (hMT : M ∈ T) (a) (hc : c z M a ≠ 0) : (∏ h, L a h).Coprime M :=
    (Nat.coprime_mul_iff_right.mp (hsupport z M hMT a (hW z M a hc)).2.1).1.symm
  have hpos (z M) (_ : M ∈ T) (a) (_ : c z M a ≠ 0) : 0 < ∏ h, L a h :=
    Finset.prod_pos fun h _ => (Fact.out : (L a h).Prime).pos
  have hv (z M) (hMT : M ∈ T) (a) (hc : c z M a ≠ 0) : (v a).natAbs ≤ B :=
    (hsupport z M hMT a (hW z M a hc)).2.2.1
  have hL (z M) (hMT : M ∈ T) (a) (hc : c z M a ≠ 0) : (∏ h, L a h) ≤ K :=
    (hsupport z M hMT a (hW z M a hc)).2.2.2
  have ht := original_averaged_pivot_transfer P hP Q hQP hQ S hS T hT hST μ hμ hμsum
    (fun z => primeTupleResidueRow P hP χP κ t (∏ y, U z y) ε)
    (fun z x _ u => primeTupleResidueRow_norm_le_one P hP χP κ hκ t (∏ y, U z y) ε x u)
    (fun a => ∏ h, L a h) v c hcop hpos B K V hv hL hscale d hcost
  have hnext (z) : reconstructedOffDiagonal T V (fun a => ∏ h, L a h) v (c z) =
      copiedWeightedAmplitude L (U z) t χH χY b (ν z) (νY z) v (W z) T V :=
    reconstructedOffDiagonal_eq_copiedWeightedAmplitude L (U z) t χH χY b
      (ν z) (νY z) v (W z) T B K V hT (hsupport z) hscale hlargeL (hlargeU z) hb
  simpa only [hnext, groupedDirectedAmplitude, c] using ht

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledInputPhase
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual current phase under independent pivot/H/Y assignments -/

namespace Ostmann

open scoped BigOperators Classical

/-- Pairwise support on the retained branch and coprimality with the total
pivot already imply all the constituent-level cross checks. -/
theorem pivot_retained_pairwise {r : ℕ} {H Y : Type*} [Fintype H] [Fintype Y]
    (P : Fin r → ℕ) (L : H → ℕ) (U : Y → ℕ)
    (hP : Pairwise (fun i j => (P i).Coprime (P j)))
    (hLU : Pairwise (fun i j => (Sum.elim L U i).Coprime (Sum.elim L U j)))
    (hM : (∏ i, P i).Coprime ((∏ h, L h) * ∏ y, U y)) :
    Pairwise (fun i j => (Sum.elim P (Sum.elim L U) i).Coprime
      (Sum.elim P (Sum.elim L U) j)) := by
  have hM' : (∏ i, P i).Coprime (∏ j : H ⊕ Y, Sum.elim L U j) := by
    simpa only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr] using hM
  have hcross (i : Fin r) (j : H ⊕ Y) : (P i).Coprime (Sum.elim L U j) :=
    Nat.coprime_fintype_prod_right_iff.mp (Nat.coprime_fintype_prod_left_iff.mp hM' i) j
  intro i j hij
  rcases i with i | i <;> rcases j with j | j
  · exact hP (fun he => hij (congrArg Sum.inl he))
  · exact hcross i j
  · exact (hcross j i).symm
  · exact hLU (fun he => hij (congrArg Sum.inr he))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledSamplePhase
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual scheduled phase on a finite prime sample -/

namespace Ostmann

open scoped Classical

theorem scheduledPrimePhase_congr_labels {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (g : I → I → ℤ) (pivot : ℕ → I) (initial : I → ℤ → ℕ → ℂ)
    (n : ℕ) (t : FrequencyTree ℤ n)
    (p q : CopyScheduleAtoms role n → ℕ) [∀ i, Fact (p i).Prime] [∀ i, Fact (q i).Prime]
    (center : ∀ p : ℕ, ZMod p) (h : p = q) :
    scheduledPrimePhase role χ g pivot initial n t p center =
      scheduledPrimePhase role χ g pivot initial n t q center := by
  subst q
  rfl

/-- Finite Fubini and the arithmetic transfer evaluate literally the same
scheduled phase after the pivot/H/Y reindexing. -/
theorem scheduledSamplePhase_partition {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (n r : ℕ)
    (e : Fin r ≃ CurrentPivotConstituent role n) (t : FrequencyTree ℤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (u : CopyScheduleY role n → P) (x : Fin r → P) (l : CopyScheduleH role n → P)
    (center : ∀ p : ℕ, ZMod p) :
    letI : ∀ h, Fact (l h : ℕ).Prime := fun h => ⟨hP _ (l h).property⟩
    letI : ∀ y, Fact (u y : ℕ).Prime := fun y => ⟨hP _ (u y).property⟩
    scheduledSamplePhase role χ κ pivot n t P hP
        (scheduledPartitionAssignment role n r e u x l) center =
      sampledScheduledPhase role χ κ pivot n r e t P hP x
        (fun h => (l h : ℕ)) (fun y => (u y : ℕ)) center := by
  let : ∀ h, Fact (l h : ℕ).Prime := fun h => ⟨hP _ (l h).property⟩
  let : ∀ y, Fact (u y : ℕ).Prime := fun y => ⟨hP _ (u y).property⟩
  let : ∀ k, Fact (x k : ℕ).Prime := fun k => ⟨hP _ (x k).property⟩
  let := scheduledInputPrimeFact role n r e (fun k => (x k : ℕ))
    (fun h => (l h : ℕ)) (fun y => (u y : ℕ))
  let : ∀ i, Fact ((scheduledPartitionAssignment (A := P) role n r e u x l i : P) : ℕ).Prime :=
    fun i => ⟨hP _ (scheduledPartitionAssignment role n r e u x l i).property⟩
  unfold scheduledSamplePhase sampledScheduledPhase
  apply scheduledPrimePhase_congr_labels
  exact scheduledPartitionAssignment_map role n r e (fun q : P => (q : ℕ)) u x l

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentCopiedAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reassembling the next full amplitude with its unchanged original priors -/

namespace Ostmann

open scoped BigOperators Classical

theorem scheduledCopiedAssignment_map {I A B : Type*}
    (role : I → CopyScheduleRole) (n : ℕ) (f : A → B)
    (u : CopyScheduleY role n → A) (l r : CopyScheduleH role n → A) :
    (fun i => f (scheduledCopiedAssignment role n u l r i)) =
      scheduledCopiedAssignment role n (f ∘ u) (f ∘ l) (f ∘ r) := by
  funext i
  obtain ⟨j, rfl⟩ := (copyScheduleSurvivorEquiv role n).symm.surjective i
  rcases j with ⟨b, h⟩ | y
  · cases b <;> rfl
  · rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentBlockProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact products of all constituents in an H or Y block -/

namespace Ostmann

open scoped BigOperators Classical

theorem constituentH_product {I : Type*} [Fintype I] (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ)
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → ℕ) :
    (∏ h : CopyScheduleH role n, ∏ k, l (constituentH role size n h k)) = ∏ h, l h := by
  rw [← Fintype.prod_sigma (fun z : Σ h : CopyScheduleH role n, Fin (size (copyScheduleOrigin n h.val)) =>
    l (constituentH role size n z.1 z.2))]
  exact (constituentHEquiv role size n).prod_comp l

theorem constituentY_product {I : Type*} [Fintype I] (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → ℕ) :
    (∏ y : CopyScheduleY role n, ∏ k, u (constituentY role size n y k)) = ∏ y, u y := by
  rw [← Fintype.prod_sigma (fun z : Σ y : CopyScheduleY role n, Fin (size (copyScheduleOrigin n y.val)) =>
    u (constituentY role size n z.1 z.2))]
  exact (constituentYEquiv role size n).prod_comp u

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InsertedAtomSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual current weight supplies pivot coprimality and frequency units -/

namespace Ostmann

open scoped BigOperators Classical

theorem insertedAtoms_pivot_coprime {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (p : I) (hp : role p = .pivot n)
    (M : ℕ) (l : CopyScheduleH role n → ℕ) (u : CopyScheduleY role n → ℕ)
    (hpair : Pairwise (fun i j => (scheduledInsertedAtoms role n M l u i).Coprime
      (scheduledInsertedAtoms role n M l u j))) :
    M.Coprime ((∏ h, l h) * ∏ y, u y) := by
  have hL : M.Coprime (∏ h, l h) := by
    apply Nat.coprime_fintype_prod_right_iff.mpr
    intro h
    have hc := hpair (show scheduledPartitionEquiv role n (.inl ⟨p, hp⟩) ≠
        scheduledPartitionEquiv role n (.inr (.inl h)) from
      by
        intro he
        have hh := (scheduledPartitionEquiv role n).injective he
        cases hh)
    change (scheduledInsertedAtoms role n M l u (scheduledPartitionEquiv role n (.inl ⟨p, hp⟩))).Coprime
      (scheduledInsertedAtoms role n M l u ⟨h.val, h.property.1⟩) at hc
    rwa [scheduledInsertedAtoms_pivot, scheduledInsertedAtoms_H] at hc
  have hU : M.Coprime (∏ y, u y) := by
    apply Nat.coprime_fintype_prod_right_iff.mpr
    intro y
    have hc := hpair (show scheduledPartitionEquiv role n (.inl ⟨p, hp⟩) ≠
        scheduledPartitionEquiv role n (.inr (.inr y)) from
      by
        intro he
        have hh := (scheduledPartitionEquiv role n).injective he
        cases hh)
    change (scheduledInsertedAtoms role n M l u (scheduledPartitionEquiv role n (.inl ⟨p, hp⟩))).Coprime
      (scheduledInsertedAtoms role n M l u ⟨y.val, y.property.1⟩) at hc
    rwa [scheduledInsertedAtoms_pivot, scheduledInsertedAtoms_Y] at hc
  exact hL.mul_right hU

theorem constituentCurrentWeight_pivot_coprime {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ) (p : I) (hp : role p = .pivot n)
    (P : Finset ℕ) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D)
    (hw : constituentCurrentWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0) :
    M.Coprime ((∏ h, (a.1 h : ℕ)) * ∏ y, (u y : ℕ)) := by
  have hf := (mul_ne_zero_iff.mp hw).2
  have hs := (fullAtomTransferWeight_top_support role childBound pivotBound ranges leaf n _ (hist a.2) hf).1
  have hc := insertedAtoms_pivot_coprime role n p hp M
    (fun h => ∏ k, (a.1 (constituentH role size n h k) : ℕ))
    (fun y => ∏ k, (u (constituentY role size n y k) : ℕ)) hs
  rwa [constituentH_product role size n (fun h => (a.1 h : ℕ)),
    constituentY_product role size n (fun y => (u y : ℕ))] at hc

theorem constituentCurrentWeight_pivot_frequency_unit {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ) (p : I) (hp : role p = .pivot n)
    (P : Finset ℕ) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D)
    (hw : constituentCurrentWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0) :
    M.Coprime (frequencyRoot n (hist a.2)).natAbs := by
  have hf := (mul_ne_zero_iff.mp hw).2
  have hs := (fullAtomTransferWeight_top_support role childBound pivotBound ranges leaf n _ (hist a.2) hf).2
  have hc := hs (scheduledPartitionEquiv role n (.inl ⟨p, hp⟩))
  rwa [scheduledInsertedAtoms_pivot] at hc

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeTupleSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact constituent-prime support at the pivot/H/Y partition -/

namespace Ostmann

open scoped BigOperators Classical

theorem pivot_retained_pairwise_iff {H Y : Type*} [Fintype H] [Fintype Y]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {r : ℕ} (x : Fin r → P)
    (L : H → ℕ) (U : Y → ℕ) :
    Pairwise (fun i j =>
      (Sum.elim (fun k => (x k : ℕ)) (Sum.elim L U) i).Coprime
        (Sum.elim (fun k => (x k : ℕ)) (Sum.elim L U) j)) ↔
      Function.Injective x ∧
      Pairwise (fun i j => (Sum.elim L U i).Coprime (Sum.elim L U j)) ∧
      (∏ k, (x k : ℕ)).Coprime ((∏ h, L h) * ∏ y, U y) := by
  constructor
  · intro h
    have hi : Function.Injective x := by
      intro i j he
      by_contra hij
      have hc := h (show Sum.inl i ≠ Sum.inl j from fun he => hij (Sum.inl.inj he))
      change (x i : ℕ).Coprime (x j : ℕ) at hc
      rw [he] at hc
      have hone : (x j : ℕ) = 1 := by simpa only [Nat.coprime_self] using hc
      exact (hP _ (x j).property).ne_one hone
    have hb : Pairwise (fun i j => (Sum.elim L U i).Coprime (Sum.elim L U j)) := by
      intro i j hij
      exact h (show Sum.inr i ≠ Sum.inr j from fun he => hij (Sum.inr.inj he))
    have hm : (∏ k, (x k : ℕ)).Coprime (∏ j : H ⊕ Y, Sum.elim L U j) := by
      apply Nat.coprime_fintype_prod_left_iff.mpr
      intro i
      apply Nat.coprime_fintype_prod_right_iff.mpr
      intro j
      exact h (show Sum.inl i ≠ Sum.inr j from by
        intro he
        cases he)
    exact ⟨hi, hb, by simpa only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr] using hm⟩
  · rintro ⟨hi, hb, hm⟩
    apply pivot_retained_pairwise (fun k => (x k : ℕ)) L U _ hb hm
    intro i j hij
    apply (hP _ (x i).property).coprime_iff_not_dvd.mpr
    intro hd
    have he : (x i : ℕ) = (x j : ℕ) :=
      ((Nat.dvd_prime (hP _ (x j).property)).mp hd).resolve_left (hP _ (x i).property).ne_one
    exact hij (hi (Subtype.ext he))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentTransferWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original constituent support in the arithmetic coefficient -/

namespace Ostmann

open scoped BigOperators Classical

/-- Both coprimality clauses of the arithmetic transfer are now consequences
of the concrete coefficient's support. -/
theorem constituentTransferWeight_support {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ) (p : I) (hp : role p = .pivot n)
    (P : Finset ℕ) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D)
    (hw : constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0) :
    Pairwise (fun i j =>
      (Sum.elim (fun h => (a.1 h : ℕ)) (fun y => (u y : ℕ)) i).Coprime
        (Sum.elim (fun h => (a.1 h : ℕ)) (fun y => (u y : ℕ)) j)) ∧
      M.Coprime ((∏ h, (a.1 h : ℕ)) * ∏ y, (u y : ℕ)) ∧
      M.Coprime (frequencyRoot n (hist a.2)).natAbs := by
  unfold constituentTransferWeight at hw
  split_ifs at hw with hg
  · exact ⟨hg,
      constituentCurrentWeight_pivot_coprime role size n p hp P Q childBound pivotBound ranges leaf hist u M a hw,
      constituentCurrentWeight_pivot_frequency_unit role size n p hp P Q childBound pivotBound ranges leaf hist u M a hw⟩
  · exact False.elim (hw rfl)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentCopiedWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact product of the two arithmetic branch coefficients -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

/-- The two old coefficients multiply to the next full coefficient with
exactly two original H priors; no outside prior is squared here. -/
theorem constituentTransferWeight_product {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (P : Finset ℕ) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P)
    (l r : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P)
    (s : ℤ) (t t' : FrequencyTree ℤ n) (M : ℕ)
    (hP : ValidTransferNode (scheduleAtomSystem role childBound pivotBound)
      ⟨n + 1, copiedConstituentAtomValues role size n P u l r⟩
      s (frequencyRoot n t) (frequencyRoot n t') M)
    (hroot : fullAtomRootGuard role ranges n (copiedConstituentAtomValues role size n P u l r) M s)
    (hL : Pairwise (fun i j =>
      (Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ)) i).Coprime
        (Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ)) j)))
    (hR : Pairwise (fun i j =>
      (Sum.elim (fun h => (r h : ℕ)) (fun y => (u y : ℕ)) i).Coprime
        (Sum.elim (fun h => (r h : ℕ)) (fun y => (u y : ℕ)) j))) :
    constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (l, t) *
      conj (constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (r, t')) =
    (((∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (l h)) *
       (∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (r h)) : ℝ) : ℂ) *
      fullAtomTransferWeight role childBound pivotBound ranges leaf (n + 1)
        (copiedConstituentAtomValues role size n P u l r) (s, t, t') := by
  unfold constituentTransferWeight
  simp only [hL, hR, ite_true, if_true]
  unfold constituentCurrentWeight
  change _ = _ * fullAtomTransferWeight role childBound pivotBound ranges leaf (n + 1)
    (scheduledCopiedAssignment role n
      (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))
      (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
      (fun h => ∏ k, (r (constituentH role size n h k) : ℕ))) (s, t, t')
  unfold copiedConstituentAtomValues at hroot
  rw [fullAtomTransferWeight_copied role childBound pivotBound ranges leaf n _ _ _ s t t' M hP,
    ite_eq_left hroot]
  simp only [id_eq, map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledCopiedSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prime support of the actual copied assignment -/

namespace Ostmann

open scoped BigOperators Classical

/-- The retained tuple has separate H and Y support and coprime total products. -/
theorem retainedPairwise_parts {H Y : Type*} [Fintype H] [Fintype Y]
    (L : H → ℕ) (U : Y → ℕ)
    (h : Pairwise (fun i j => (Sum.elim L U i).Coprime (Sum.elim L U j))) :
    Pairwise (fun i j => (L i).Coprime (L j)) ∧
      Pairwise (fun i j => (U i).Coprime (U j)) ∧
      (∏ i, L i).Coprime (∏ j, U j) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    exact h (show Sum.inl i ≠ Sum.inl j from fun he => hij (Sum.inl.inj he))
  · intro i j hij
    exact h (show Sum.inr i ≠ Sum.inr j from fun he => hij (Sum.inr.inj he))
  · apply Nat.coprime_fintype_prod_left_iff.mpr
    intro i
    apply Nat.coprime_fintype_prod_right_iff.mpr
    intro j
    exact h (show Sum.inl i ≠ Sum.inr j from by intro he; cases he)

/-- Restricting a pairwise copied assignment to either retained branch
recovers its full H/Y coprimality, including cross terms. -/
theorem scheduledCopiedAssignment_pairwise_branch {I : Type*}
    (role : I → CopyScheduleRole) (n : ℕ)
    (L R : CopyScheduleH role n → ℕ) (U : CopyScheduleY role n → ℕ)
    (h : Pairwise (fun i j =>
      (scheduledCopiedAssignment role n U L R i).Coprime
        (scheduledCopiedAssignment role n U L R j))) (b : Bool) :
    Pairwise (fun i j =>
      (Sum.elim (if b then L else R) U i).Coprime (Sum.elim (if b then L else R) U j)) := by
  let f : CopyScheduleH role n ⊕ CopyScheduleY role n → _ :=
    fun i => scheduledOutputVertex role n (match i with
      | .inl a => .inl (b, a)
      | .inr y => .inr y)
  have hf : Function.Injective f := by
    intro i j hij
    have he := congrArg (copyScheduleSurvivorEquiv role n) hij
    dsimp only [f, scheduledOutputVertex] at he
    simp only [Equiv.apply_symm_apply] at he
    cases i with
    | inl a =>
      cases j with
      | inl a' => exact congrArg Sum.inl (congrArg Prod.snd (Sum.inl.inj he))
      | inr y => cases he
    | inr y =>
      cases j with
      | inl a => cases he
      | inr y' => exact congrArg Sum.inr (Sum.inr.inj he)
  have he (i) : scheduledCopiedAssignment role n U L R (f i) =
      Sum.elim (if b then L else R) U i := by
    cases i with
    | inl a => cases b <;> simp only [f, Bool.false_eq_true, ite_false, if_false, ite_true, if_true,
        scheduledCopiedAssignment_left, scheduledCopiedAssignment_right, Sum.elim_inl]
    | inr y => exact scheduledCopiedAssignment_outside role n U L R y
  intro i j hij
  rw [← he i, ← he j]
  exact h (hf.ne hij)

/-- Signed reconstruction, the original branch support and the prime cutoff
supply every prime-level test on the next copied assignment. -/
theorem scheduledCopiedAssignment_support {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ)
    (L R : CopyScheduleH role n → ℕ) (U : CopyScheduleY role n → ℕ)
    [∀ h, Fact (L h).Prime] [∀ h, Fact (R h).Prime] [∀ y, Fact (U y).Prime]
    (M B K V : ℕ) (v w s : ℤ) (hMpos : 0 < M) (hs : s ≠ 0)
    (hrel : v * (∏ h, R h) - w * (∏ h, L h) = s * M)
    (hv : v.natAbs ≤ B) (hw : w.natAbs ≤ B)
    (hLbound : (∏ h, L h) ≤ K) (hRbound : (∏ h, R h) ≤ K)
    (hscale : 2 * B * K ≤ V * M)
    (hL : Pairwise (fun i j => (Sum.elim L U i).Coprime (Sum.elim L U j)))
    (hR : Pairwise (fun i j => (Sum.elim R U i).Coprime (Sum.elim R U j)))
    (hML : M.Coprime ((∏ h, L h) * ∏ y, U y))
    (hMR : M.Coprime ((∏ h, R h) * ∏ y, U y))
    (hlargeL : ∀ h, V < L h) (hlargeR : ∀ h, V < R h) (hlargeU : ∀ y, V < U y) :
    let q := scheduledCopiedAssignment role n U L R
    s.natAbs ≤ V ∧ Pairwise (fun i j => (q i).Coprime (q j)) ∧
      (∀ i, M.Coprime (q i)) ∧ (∀ i, (q i).Coprime s.natAbs) := by
  obtain ⟨hLL, hUU, hLU⟩ := retainedPairwise_parts L U hL
  obtain ⟨hRR, _, hRU⟩ := retainedPairwise_parts R U hR
  obtain ⟨hsV, hpair, hM, hunit⟩ := transfer_copied_support_of_ranges L R U M B K V v w s
    hMpos hs hrel hv hw hLbound hRbound hscale hLL hRR hUU hLU hRU
    (Nat.coprime_mul_iff_right.mp hML).1 (Nat.coprime_mul_iff_right.mp hMR).1
    (Nat.coprime_mul_iff_right.mp hML).2 hlargeL hlargeR hlargeU
  have he (i) : scheduledCopiedAssignment role n U L R i =
      transferredLabels L R U (copyScheduleSurvivorEquiv role n i) := by
    unfold scheduledCopiedAssignment
    generalize copyScheduleSurvivorEquiv role n i = j
    rcases j with ⟨b, h⟩ | y
    · cases b <;> rfl
    · rfl
  refine ⟨hsV, ?_, ?_, ?_⟩
  · intro i j hij
    simp only [he]
    exact hpair ((copyScheduleSurvivorEquiv role n).injective.ne hij)
  · intro i
    rw [he]
    exact hM _
  · intro i
    rw [he]
    have hc := (ZMod.coe_int_isUnit_iff_isCoprime s _).mp (hunit (copyScheduleSurvivorEquiv role n i))
    have hg := Int.isCoprime_iff_gcd_eq_one.mp hc
    change Nat.gcd (transferredLabels L R U (copyScheduleSurvivorEquiv role n i)) s.natAbs = 1 at hg
    exact hg

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentCopiedSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual arithmetic coefficients supply the next full root guard -/

namespace Ostmann

open scoped BigOperators Classical

theorem copiedConstituentAtomValues_left {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ) (P : Finset ℕ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P)
    (l r : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) :
    scheduleAtomLeft role ⟨n + 1, copiedConstituentAtomValues role size n P u l r⟩ =
      ∏ h, (l h : ℕ) := by
  unfold copiedConstituentAtomValues
  rw [scheduleAtomLeft_copied, constituentH_product role size n (fun h => (l h : ℕ))]

theorem copiedConstituentAtomValues_right {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ) (P : Finset ℕ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P)
    (l r : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) :
    scheduleAtomRight role ⟨n + 1, copiedConstituentAtomValues role size n P u l r⟩ =
      ∏ h, (r h : ℕ) := by
  unfold copiedConstituentAtomValues
  rw [scheduleAtomRight_copied, constituentH_product role size n (fun h => (r h : ℕ))]

/-- No new support assumption is imposed on the next coefficient. Its
coprimality tests follow from nonzero old coefficients and the signed equation;
only the explicit numerical and interval cutoffs are needed. -/
theorem constituentTransferWeight_copied_support {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (p : I) (hp : role p = .pivot n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P)
    (l r : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P)
    (s : ℤ) (t t' : FrequencyTree ℤ n) (M K V : ℕ)
    (hl : constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (l, t) ≠ 0)
    (hr : constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (r, t') ≠ 0)
    (hs : s ≠ 0) (hMpos : 0 < M) (hMbound : M ≤ pivotBound n)
    (hrel : frequencyRoot n t * (∏ h, (r h : ℕ)) -
      frequencyRoot n t' * (∏ h, (l h : ℕ)) = s * M)
    (ht : (frequencyRoot n t).natAbs ≤ childBound n)
    (ht' : (frequencyRoot n t').natAbs ≤ childBound n)
    (hlK : (∏ h, (l h : ℕ)) ≤ K) (hrK : (∏ h, (r h : ℕ)) ≤ K)
    (hscale : 2 * childBound n * K ≤ V * M)
    (hlarge : ∀ q ∈ P, V < q)
    (hgap : 2 * pivotBound n * childBound n < ∏ h, (r h : ℕ))
    (hrange : ∀ a ∈ ranges (n + 1), a.Holds (copiedConstituentAtomValues role size n P u l r)) :
    ValidTransferNode (scheduleAtomSystem role childBound pivotBound)
      ⟨n + 1, copiedConstituentAtomValues role size n P u l r⟩
      s (frequencyRoot n t) (frequencyRoot n t') M ∧
    fullAtomRootGuard role ranges n (copiedConstituentAtomValues role size n P u l r) M s ∧
    Pairwise (fun i j =>
      ((scheduledCopiedAssignment (fun i : Σ a, Fin (size a) => role i.1) n u l r i : P) : ℕ).Coprime
        ((scheduledCopiedAssignment (fun i : Σ a, Fin (size a) => role i.1) n u l r j : P) : ℕ)) := by
  let ρ := fun i : Σ a, Fin (size a) => role i.1
  let : ∀ h, Fact (l h : ℕ).Prime := fun h => ⟨hP _ (l h).property⟩
  let : ∀ h, Fact (r h : ℕ).Prime := fun h => ⟨hP _ (r h).property⟩
  let : ∀ y, Fact (u y : ℕ).Prime := fun y => ⟨hP _ (u y).property⟩
  obtain ⟨hL, hML, _⟩ := constituentTransferWeight_support role size n p hp P Q
    childBound pivotBound ranges leaf id u M (l, t) hl
  obtain ⟨hR, hMR, hMw⟩ := constituentTransferWeight_support role size n p hp P Q
    childBound pivotBound ranges leaf id u M (r, t') hr
  obtain ⟨_, hpair, hM, hfreq⟩ := scheduledCopiedAssignment_support ρ n
    (fun h => (l h : ℕ)) (fun h => (r h : ℕ)) (fun y => (u y : ℕ))
    M (childBound n) K V (frequencyRoot n t) (frequencyRoot n t') s hMpos hs hrel
    ht ht' hlK hrK hscale hL hR hML hMR
    (fun h => hlarge _ (l h).property) (fun h => hlarge _ (r h).property)
    (fun y => hlarge _ (u y).property)
  have hRU : (∏ h, (r h : ℕ)).Coprime s.natAbs := by
    apply Nat.coprime_fintype_prod_left_iff.mpr
    intro h
    simpa only [scheduledCopiedAssignment_right] using
      hfreq (scheduledOutputVertex ρ n (.inl (false, h)))
  have hleft := copiedConstituentAtomValues_left role size n P u l r
  have hright := copiedConstituentAtomValues_right role size n P u l r
  have hnode : ValidTransferNode (scheduleAtomSystem role childBound pivotBound)
      ⟨n + 1, copiedConstituentAtomValues role size n P u l r⟩
      s (frequencyRoot n t) (frequencyRoot n t') M := by
    refine ⟨hs, ?_, ?_, hMpos, hMbound, ht, ht', ?_, hMw⟩
    · change IsCoprime s (scheduleAtomRight role ⟨n + 1, copiedConstituentAtomValues role size n P u l r⟩ : ℤ)
      rw [hright]
      apply Int.isCoprime_iff_gcd_eq_one.mpr
      change Nat.gcd s.natAbs (∏ h, (r h : ℕ)) = 1
      exact hRU.symm
    · change frequencyRoot n t * (scheduleAtomRight role ⟨n + 1, copiedConstituentAtomValues role size n P u l r⟩ : ℤ) -
        frequencyRoot n t' * (scheduleAtomLeft role ⟨n + 1, copiedConstituentAtomValues role size n P u l r⟩ : ℤ) = s * M
      rwa [hleft, hright]
    · change 2 * pivotBound n * childBound n < scheduleAtomRight role ⟨n + 1, copiedConstituentAtomValues role size n P u l r⟩
      rwa [hright]
  have hwords := constituent_copied_assignment role size n
    (fun y => (u y : ℕ)) (fun h => (l h : ℕ)) (fun h => (r h : ℕ))
  have hguard := constituent_fullAtomRootGuard role size ranges n
    (scheduledCopiedAssignment ρ n (fun y => (u y : ℕ)) (fun h => (l h : ℕ)) (fun h => (r h : ℕ)))
    M s hpair hM hfreq (by rw [hwords]; exact hrange)
  have hmap := scheduledCopiedAssignment_map ρ n (fun q : P => (q : ℕ)) u l r
  refine ⟨hnode, ?_, ?_⟩
  · rwa [hwords] at hguard
  · change Pairwise (fun i j =>
      ((fun i => ((scheduledCopiedAssignment ρ n u l r i : P) : ℕ)) i).Coprime
        ((fun i => ((scheduledCopiedAssignment ρ n u l r i : P) : ℕ)) j))
    rw [hmap]
    exact hpair

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FullAtomRangeSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original pivot interval remains present in full coefficient support -/

namespace Ostmann

open scoped Classical

theorem fullAtomTransferWeight_top_range {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (n : ℕ)
    (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (hw : fullAtomTransferWeight role childBound pivotBound ranges leaf n x t ≠ 0)
    (r : ScheduleAtomRange role n) (hr : r ∈ ranges n) : r.Holds x := by
  have hg := (fullAtomTransferWeight_support role childBound pivotBound ranges leaf n x t hw).1.2.2
  cases n with
  | zero => exact hg r hr
  | succ n => exact hg.1 r hr

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_AtomIntervalRanges
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete inherited intervals for every original atom role -/

namespace Ostmann

open scoped Classical

theorem atomInterval_holds_iff {I : Type*} (role : I → CopyScheduleRole)
    (lo hi : I → ℕ) (n : ℕ) (v : CopyScheduleAtoms role n) (x : CopyScheduleAtoms role n → ℕ) :
    (atomInterval role lo hi n v).Holds x ↔
      lo (copyScheduleOrigin n v.val) ≤ x v ∧ x v ≤ hi (copyScheduleOrigin n v.val) := by
  simp only [atomInterval, ScheduleAtomRange.Holds, List.map_singleton, List.prod_singleton,
    Set.mem_Icc, Nat.cast_le]

theorem atomIntervalRanges_holds_iff {I : Type*} [Fintype I] (role : I → CopyScheduleRole)
    (lo hi : I → ℕ) (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) :
    (∀ r ∈ atomIntervalRanges role lo hi n, r.Holds x) ↔
      ∀ v, lo (copyScheduleOrigin n v.val) ≤ x v ∧ x v ≤ hi (copyScheduleOrigin n v.val) := by
  constructor
  · intro h v
    apply (atomInterval_holds_iff role lo hi n v x).mp
    apply h
    exact List.mem_map.mpr ⟨v, Finset.mem_toList.mpr (Finset.mem_univ v), rfl⟩
  · intro h r hr
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hr
    exact (atomInterval_holds_iff role lo hi n v x).mpr (h v)

/-- Copying preserves the original atom origin and hence its exact interval. -/
theorem atomIntervalRanges_copied {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (lo hi : I → ℕ) (n M : ℕ)
    (u : CopyScheduleY role n → ℕ) (l r : CopyScheduleH role n → ℕ)
    (hL : ∀ a ∈ atomIntervalRanges role lo hi n,
      a.Holds (scheduledInsertedAtoms role n M l u))
    (hR : ∀ a ∈ atomIntervalRanges role lo hi n,
      a.Holds (scheduledInsertedAtoms role n M r u)) :
    ∀ a ∈ atomIntervalRanges role lo hi (n + 1),
      a.Holds (scheduledCopiedAssignment role n u l r) := by
  apply (atomIntervalRanges_holds_iff role lo hi (n + 1) _).mpr
  have hL' := (atomIntervalRanges_holds_iff role lo hi n _).mp hL
  have hR' := (atomIntervalRanges_holds_iff role lo hi n _).mp hR
  intro v
  obtain ⟨j, rfl⟩ := (copyScheduleSurvivorEquiv role n).symm.surjective v
  rcases j with ⟨b, h⟩ | y
  · cases b
    · have hh := hR' ⟨h.val, h.property.1⟩
      change lo (copyScheduleOrigin n h.val) ≤ r h ∧ r h ≤ hi (copyScheduleOrigin n h.val)
      simpa only [scheduledInsertedAtoms_H] using hh
    · have hh := hL' ⟨h.val, h.property.1⟩
      change lo (copyScheduleOrigin n h.val) ≤ l h ∧ l h ≤ hi (copyScheduleOrigin n h.val)
      simpa only [scheduledInsertedAtoms_H] using hh
  · have hh := hL' ⟨y.val, y.property.1⟩
    change lo (copyScheduleOrigin n y.val) ≤ u y ∧ u y ≤ hi (copyScheduleOrigin n y.val)
    simpa only [scheduledInsertedAtoms_Y] using hh

/-- Both old full coefficients enforce every new interval. This discharges
the interval clause in the actual guarded arithmetic step. -/
theorem fullAtomTransferWeight_copied_intervals {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (lo hi : I → ℕ)
    (childBound pivotBound : ℕ → ℕ) (leaf : ScheduleAtomState role → ℤ → ℂ)
    (n M : ℕ) (u : CopyScheduleY role n → ℕ) (l r : CopyScheduleH role n → ℕ)
    (t t' : FrequencyTree ℤ n)
    (hL : fullAtomTransferWeight role childBound pivotBound (atomIntervalRanges role lo hi) leaf n
      (scheduledInsertedAtoms role n M l u) t ≠ 0)
    (hR : fullAtomTransferWeight role childBound pivotBound (atomIntervalRanges role lo hi) leaf n
      (scheduledInsertedAtoms role n M r u) t' ≠ 0) :
    ∀ a ∈ atomIntervalRanges role lo hi (n + 1), a.Holds (scheduledCopiedAssignment role n u l r) := by
  exact atomIntervalRanges_copied role lo hi n M u l r
    (fun a ha => fullAtomTransferWeight_top_range role childBound pivotBound _ leaf n _ t hL a ha)
    (fun a ha => fullAtomTransferWeight_top_range role childBound pivotBound _ leaf n _ t' hR a ha)

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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentFrequencySupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frequency units for the actual supported arithmetic coefficient -/

namespace Ostmann

open scoped BigOperators Classical

theorem constituentTransferWeight_full_ne_zero {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (P : Finset ℕ) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D)
    (hw : constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0) :
    fullAtomTransferWeight role childBound pivotBound ranges leaf n
      (scheduledInsertedAtoms role n M
        (fun h => ∏ k, (a.1 (constituentH role size n h k) : ℕ))
        (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) (hist a.2) ≠ 0 := by
  unfold constituentTransferWeight at hw
  split_ifs at hw
  · exact (mul_ne_zero_iff.mp hw).2
  · exact False.elim (hw rfl)

theorem constituentTransferWeight_frequency_unit {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (P : Finset ℕ) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (hzero : ∀ x, fullAtomTransferWeight role childBound pivotBound ranges leaf 0 x (0 : ℤ) = 0)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D)
    (hw : constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0)
    (p : ℕ) [Fact p.Prime] (s : ℤ) (hs : s ∈ allFrequencyList n (hist a.2))
    (hsmall : s.natAbs < p) : (s : ZMod p) ≠ 0 := by
  have hf := constituentTransferWeight_full_ne_zero role size n P Q childBound pivotBound ranges leaf hist u M a hw
  have hn := fullAtomTransferWeight_all_frequencies_ne_zero role childBound pivotBound ranges leaf
    hzero n _ (hist a.2) hf s hs
  exact isUnit_iff_ne_zero.mp (prime_large_frequency_unit s hn hsmall)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeGuardedAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full constituent-prime guard in arithmetic amplitude coordinates -/

namespace Ostmann

open scoped BigOperators Classical

theorem scheduledPartitionAssignment_pairwise_iff {I A : Type*}
    (role : I → CopyScheduleRole) (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n)
    (f : A → ℕ) (u : CopyScheduleY role n → A) (x : Fin r → A) (l : CopyScheduleH role n → A) :
    Pairwise (fun i j => (f (scheduledPartitionAssignment role n r e u x l i)).Coprime
      (f (scheduledPartitionAssignment role n r e u x l j))) ↔
      Pairwise (fun i j => (f (Sum.elim x (Sum.elim l u) i)).Coprime
        (f (Sum.elim x (Sum.elim l u) j))) := by
  have he : Pairwise (fun i j =>
      (f (scheduledPartitionAssignment role n r e u x l (enumeratedPartitionEquiv role n r e i))).Coprime
      (f (scheduledPartitionAssignment role n r e u x l (enumeratedPartitionEquiv role n r e j)))) ↔
      Pairwise (fun i j => (f (scheduledPartitionAssignment role n r e u x l i)).Coprime
        (f (scheduledPartitionAssignment role n r e u x l j))) :=
    (enumeratedPartitionEquiv role n r e).bijective.pairwise_comp_iff
      (r := fun i j => (f (scheduledPartitionAssignment role n r e u x l i)).Coprime
        (f (scheduledPartitionAssignment role n r e u x l j)))
  simpa only [scheduledPartitionAssignment_apply] using he.symm

/-- The full prime guard separates exactly into an injective pivot tuple and
the retained branch guard. Pivot coprimality is supplied by the inherited
coefficient, so it is not added as a new hypothesis on the main theorem. -/
theorem primeGuardedCurrentAmplitude_eq_restricted {I A Z : Type*}
    [Fintype I] [Fintype A] [Fintype Z]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (n r : ℕ)
    (e : Fin r ≃ CurrentPivotConstituent role n) (hist : A → FrequencyTree ℤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : Fin r → Finset ℕ)
    (L : A → CopyScheduleH role n → ℕ) (U : Z → CopyScheduleY role n → ℕ)
    [∀ a h, Fact (L a h).Prime] [∀ z y, Fact (U z y).Prime]
    (center : ∀ p : ℕ, ZMod p) (W : Z → ℕ → A → ℂ) (μ : Z → ℝ)
    (hM : ∀ z (x : Fin r → P) a, W z (∏ i, (x i : ℕ)) a ≠ 0 →
      (∏ i, (x i : ℕ)).Coprime ((∏ h, L a h) * ∏ y, U z y)) :
    primeGuardedCurrentAmplitude role χ κ pivot n r e hist P hP Q L U center W μ =
      scheduledCurrentAmplitude role χ κ pivot n r e hist P hP Q
        (Finset.univ.filter Function.Injective) L U center
        (fun z M a => if Pairwise (fun i j =>
          (Sum.elim (L a) (U z) i).Coprime (Sum.elim (L a) (U z) j)) then W z M a else 0) μ := by
  unfold primeGuardedCurrentAmplitude scheduledCurrentAmplitude
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : Function.Injective x
  · simp only [hx, ite_true, if_true]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    by_cases hw : W z (∏ i, (x i : ℕ)) a = 0
    · simp only [hw, zero_mul, ite_self]
    · by_cases hb : Pairwise (fun i j => (Sum.elim (L a) (U z) i).Coprime (Sum.elim (L a) (U z) j))
      · have hf := (pivot_retained_pairwise_iff P hP x (L a) (U z)).mpr ⟨hx, hb, hM z x a hw⟩
        simp only [hf, hb, ite_true, if_true]
      · have hf : ¬ Pairwise (fun i j =>
            (Sum.elim (fun k => (x k : ℕ)) (Sum.elim (L a) (U z)) i).Coprime
              (Sum.elim (fun k => (x k : ℕ)) (Sum.elim (L a) (U z)) j)) :=
          fun h => hb ((pivot_retained_pairwise_iff P hP x (L a) (U z)).mp h).2.1
        simp only [hf, hb, ite_false, if_false, zero_mul]
  · simp only [hx, ite_false, if_false]
    have hz : (∑ a, if Pairwise (fun i j =>
        (Sum.elim (fun k => (x k : ℕ)) (Sum.elim (L a) (U z)) i).Coprime
          (Sum.elim (fun k => (x k : ℕ)) (Sum.elim (L a) (U z)) j)) then
        W z (∏ i, (x i : ℕ)) a *
          sampledScheduledPhase role χ κ pivot n r e (hist a) P hP x (L a) (U z) center else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      rw [pivot_retained_pairwise_iff P hP x (L a) (U z)]
      simp only [hx, false_and, ite_false, if_false]
    rw [hz, mul_zero]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentPrimeGuardedAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original-prior expectation with every constituent-prime guard -/

namespace Ostmann

open scoped BigOperators Classical

/-- This identifies the full original-prior expectation, including its actual
phase and every history guard, with the amplitude in the proved arithmetic step. -/
theorem constituentPrimeGuardedAmplitude_eq_current {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (p : I) (hp : role p = .pivot n) (hu : ∀ i, role i = .pivot n → i = p)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (center : ∀ p : ℕ, ZMod p) :
    let ρ := fun i : Σ a, Fin (size a) => role i.1
    letI : ∀ (a : (CopyScheduleH ρ n → P) × D) h, Fact (a.1 h : ℕ).Prime :=
      fun a h => ⟨hP _ (a.1 h).property⟩
    letI : ∀ (u : CopyScheduleY ρ n → P) y, Fact (u y : ℕ).Prime :=
      fun u y => ⟨hP _ (u y).property⟩
    constituentPrimeGuardedAmplitude role size χ κ pivot n P hP Q childBound pivotBound ranges leaf hist center =
      primeGuardedCurrentAmplitude ρ χ κ pivot n (size p) (pivotConstituentEquiv role size n p hp hu)
        (fun a => hist a.2) P hP (fun k => Q ⟨p, k⟩)
        (fun a h => (a.1 h : ℕ)) (fun u y => (u y : ℕ)) center
        (constituentCurrentWeight role size n P Q childBound pivotBound ranges leaf hist)
        (fun u => ∏ y, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) (u y)) := by
  let ρ := fun i : Σ a, Fin (size a) => role i.1
  let : ∀ (a : (CopyScheduleH ρ n → P) × D) h, Fact (a.1 h : ℕ).Prime :=
    fun a h => ⟨hP _ (a.1 h).property⟩
  let : ∀ (u : CopyScheduleY ρ n → P) y, Fact (u y : ℕ).Prime :=
    fun u y => ⟨hP _ (u y).property⟩
  have hF := constituent_weighted_prior_fubini role size n p hp hu P
    (scheduledRolePrior ρ (fun j => primeSubsetPrior P (Q j)) n)
    childBound pivotBound ranges leaf hist
    (fun q d => if Pairwise (fun i j => (q i : ℕ).Coprime (q j : ℕ)) then
      scheduledSamplePhase ρ χ κ pivot n (hist d) P hP q center else 0)
  change constituentPrimeGuardedAmplitude role size χ κ pivot n P hP Q
    childBound pivotBound ranges leaf hist center = _ at hF
  refine hF.trans ?_
  simp only [scheduledRolePrior, enumeratedPartitionEquiv_pivot,
    enumeratedPartitionEquiv_rest, copyScheduleOrigin_positive, Sum.elim_inl, Sum.elim_inr]
  unfold primeGuardedCurrentAmplitude constituentCurrentWeight productPrior
  simp only [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro d _
  dsimp only [ρ]
  have hsum (j : Fin (size p) ⊕ (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n ⊕
      CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n)) :
      ((Sum.elim x (Sum.elim l u) j : P) : ℕ) =
        Sum.elim (fun k => (x k : ℕ)) (Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ))) j := by
    rcases j with k | h | y <;> rfl
  have hg : (Pairwise (fun i j =>
      ((scheduledPartitionAssignment (fun i : Σ a, Fin (size a) => role i.1)
        n (size p) (pivotConstituentEquiv role size n p hp hu) u x l i : P) : ℕ).Coprime
      ((scheduledPartitionAssignment (fun i : Σ a, Fin (size a) => role i.1)
        n (size p) (pivotConstituentEquiv role size n p hp hu) u x l j : P) : ℕ))) ↔
      Pairwise (fun i j =>
        (Sum.elim (fun k => (x k : ℕ)) (Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ))) i).Coprime
        (Sum.elim (fun k => (x k : ℕ)) (Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ))) j)) := by
    have hh := scheduledPartitionAssignment_pairwise_iff (fun i : Σ a, Fin (size a) => role i.1)
      n (size p) (pivotConstituentEquiv role size n p hp hu) (fun q : P => (q : ℕ)) u x l
    simpa only [hsum] using hh
  rw [scheduledSamplePhase_partition]
  have hq (k) : Q (pivotConstituentEquiv role size n p hp hu k).val = Q ⟨p, k⟩ := rfl
  simp_rw [hq]
  split_ifs with hA hB hB
  · ring
  · exact False.elim (hB (hg.mp hA))
  · exact False.elim (hA (hg.mpr hB))
  · ring

/-- The fully guarded original expectation is exactly the amplitude to which
the proved arithmetic transfer applies. All prime-support predicates are retained. -/
theorem constituentPrimeGuardedAmplitude_eq_transfer {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (p : I) (hp : role p = .pivot n) (hu : ∀ i, role i = .pivot n → i = p)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (center : ∀ p : ℕ, ZMod p) :
    let ρ := fun i : Σ a, Fin (size a) => role i.1
    letI : ∀ (a : (CopyScheduleH ρ n → P) × D) h, Fact (a.1 h : ℕ).Prime :=
      fun a h => ⟨hP _ (a.1 h).property⟩
    letI : ∀ (u : CopyScheduleY ρ n → P) y, Fact (u y : ℕ).Prime :=
      fun u y => ⟨hP _ (u y).property⟩
    constituentPrimeGuardedAmplitude role size χ κ pivot n P hP Q childBound pivotBound ranges leaf hist center =
      scheduledCurrentAmplitude ρ χ κ pivot n (size p) (pivotConstituentEquiv role size n p hp hu)
        (fun a => hist a.2) P hP (fun k => Q ⟨p, k⟩) (Finset.univ.filter Function.Injective)
        (fun a h => (a.1 h : ℕ)) (fun u y => (u y : ℕ)) center
        (constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist)
        (fun u => ∏ y, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) (u y)) := by
  let ρ := fun i : Σ a, Fin (size a) => role i.1
  let : ∀ (a : (CopyScheduleH ρ n → P) × D) h, Fact (a.1 h : ℕ).Prime :=
    fun a h => ⟨hP _ (a.1 h).property⟩
  let : ∀ (u : CopyScheduleY ρ n → P) y, Fact (u y : ℕ).Prime :=
    fun u y => ⟨hP _ (u y).property⟩
  have he := constituentPrimeGuardedAmplitude_eq_current role size χ κ pivot n p hp hu
    P hP Q childBound pivotBound ranges leaf hist center
  refine he.trans ?_
  apply primeGuardedCurrentAmplitude_eq_restricted
  intro u x a hw
  exact constituentCurrentWeight_pivot_coprime role size n p hp P Q childBound pivotBound ranges
    leaf hist u (∏ i, (x i : ℕ)) a hw

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentGuardedCopiedAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reassembling the next full amplitude with its unchanged original priors -/

namespace Ostmann

open scoped BigOperators Classical

/-- The next global amplitude has exactly the two H priors and one Y prior
appearing after arithmetic transfer. All Fourier and arithmetic support stays
inside the same full coefficient. -/
theorem constituentPrimeGuardedAmplitude_copied {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ (n + 1))
    (center : ∀ p : ℕ, ZMod p) :
    constituentPrimeGuardedAmplitude role size χ κ pivot (n + 1) P hP Q
      childBound pivotBound ranges leaf hist center =
    let ρ := fun i : Σ a, Fin (size a) => role i.1
    ∑ u : CopyScheduleY ρ n → P,
      ((∏ y, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) (u y) : ℝ) : ℂ) *
      ∑ l : CopyScheduleH ρ n → P,
        ((∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (l h) : ℝ) : ℂ) *
        ∑ r : CopyScheduleH ρ n → P,
          ((∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (r h) : ℝ) : ℂ) *
          ∑ d, fullAtomTransferWeight role childBound pivotBound ranges leaf (n + 1)
            (scheduledCopiedAssignment role n
              (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))
              (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
              (fun h => ∏ k, (r (constituentH role size n h k) : ℕ))) (hist d) *
            (if Pairwise (fun i j =>
                ((scheduledCopiedAssignment ρ n u l r i : P) : ℕ).Coprime
                  ((scheduledCopiedAssignment ρ n u l r j : P) : ℕ)) then
              scheduledSamplePhase ρ χ κ pivot (n + 1) (hist d) P hP
                (scheduledCopiedAssignment ρ n u l r) center else 0) := by
  let ρ := fun i : Σ a, Fin (size a) => role i.1
  have hF := copied_prior_fubini ρ n
    (scheduledRolePrior ρ (fun j => primeSubsetPrior P (Q j)) (n + 1))
    (fun q => ∑ d, fullAtomTransferWeight role childBound pivotBound ranges leaf (n + 1)
      (fun v => ((scheduleConstituentWord role size (n + 1) v).map (fun i => (q i : ℕ))).prod)
      (hist d) * (if Pairwise (fun i j => (q i : ℕ).Coprime (q j : ℕ)) then
        scheduledSamplePhase ρ χ κ pivot (n + 1) (hist d) P hP q center else 0))
  change constituentPrimeGuardedAmplitude role size χ κ pivot (n + 1) P hP Q
    childBound pivotBound ranges leaf hist center = _ at hF
  refine hF.trans ?_
  simp only [scheduledRolePrior_copied]
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  have hmap := scheduledCopiedAssignment_map ρ n (fun q : P => (q : ℕ)) u l r
  have hg := constituent_copied_assignment role size n
    (fun y => (u y : ℕ)) (fun h => (l h : ℕ)) (fun h => (r h : ℕ))
  have hg' : (fun v => ((scheduleConstituentWord role size (n + 1) v).map
      (fun i => ((scheduledCopiedAssignment (A := P) ρ n u l r i : P) : ℕ))).prod) =
      scheduledCopiedAssignment role n
        (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))
        (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
        (fun h => ∏ k, (r (constituentH role size n h k) : ℕ)) := by
    rw [hmap]
    exact hg
  rw [hg']

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FullWeightForcedNode
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A nonzero full coefficient uses the forced integer pivot -/

namespace Ostmann

open scoped BigOperators Classical

theorem fullAtomTransferWeight_forced_node {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (n : ℕ)
    (x : CopyScheduleAtoms role (n + 1) → ℕ) (s : ℤ) (t t' : FrequencyTree ℤ n) (M : ℕ)
    (hs : s ≠ 0)
    (hrel : frequencyRoot n t * (scheduleAtomRight role ⟨n + 1, x⟩ : ℤ) -
      frequencyRoot n t' * (scheduleAtomLeft role ⟨n + 1, x⟩ : ℤ) = s * M)
    (hw : fullAtomTransferWeight role childBound pivotBound ranges leaf (n + 1) x (s, t, t') ≠ 0) :
    ValidTransferNode (scheduleAtomSystem role childBound pivotBound)
      ⟨n + 1, x⟩ s (frequencyRoot n t) (frequencyRoot n t') M ∧
      fullAtomRootGuard role ranges n x M s := by
  obtain ⟨hg, Q, hQ, _, _⟩ := fullAtomTransferWeight_support role childBound pivotBound ranges leaf
    (n + 1) x (s, t, t') hw
  have hMQ : (M : ℤ) = Q := mul_left_cancel₀ hs (hrel.symm.trans hQ.relation)
  have he : M = Q := Int.ofNat_inj.mp hMQ
  subst Q
  exact ⟨hQ, ((fullAtomWeightGuard_node role childBound pivotBound ranges n x (s, t, t') M hQ).mp hg).1⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentGuardedProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact guarded coefficient multiplication, including zero support -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

theorem constituentTransferWeight_product_guarded {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (p : I) (hp : role p = .pivot n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P)
    (l r : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P)
    (s : ℤ) (t t' : FrequencyTree ℤ n) (M K V : ℕ)
    (hs : s ≠ 0) (hMpos : 0 < M) (hMbound : M ≤ pivotBound n)
    (hrel : frequencyRoot n t * (∏ h, (r h : ℕ)) -
      frequencyRoot n t' * (∏ h, (l h : ℕ)) = s * M)
    (hcutL : constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (l, t) ≠ 0 →
      (frequencyRoot n t).natAbs ≤ childBound n ∧ (∏ h, (l h : ℕ)) ≤ K)
    (hcutR : constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (r, t') ≠ 0 →
      (frequencyRoot n t').natAbs ≤ childBound n ∧ (∏ h, (r h : ℕ)) ≤ K)
    (hscale : 2 * childBound n * K ≤ V * M)
    (hlarge : ∀ q ∈ P, V < q)
    (hgap : constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (l, t) ≠ 0 →
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (r, t') ≠ 0 →
      2 * pivotBound n * childBound n < ∏ h, (r h : ℕ))
    (hrange : constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (l, t) ≠ 0 →
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (r, t') ≠ 0 →
      ∀ a ∈ ranges (n + 1), a.Holds (copiedConstituentAtomValues role size n P u l r)) :
    constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (l, t) *
      conj (constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (r, t')) =
    (((∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (l h)) *
       (∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (r h)) : ℝ) : ℂ) *
      (if Pairwise (fun i j =>
        ((scheduledCopiedAssignment (fun i : Σ a, Fin (size a) => role i.1) n u l r i : P) : ℕ).Coprime
          ((scheduledCopiedAssignment (fun i : Σ a, Fin (size a) => role i.1) n u l r j : P) : ℕ)) then
        fullAtomTransferWeight role childBound pivotBound ranges leaf (n + 1)
          (copiedConstituentAtomValues role size n P u l r) (s, t, t') else 0) := by
  let ρ := fun i : Σ a, Fin (size a) => role i.1
  have hbranches (hq : Pairwise (fun i j =>
      ((scheduledCopiedAssignment ρ n u l r i : P) : ℕ).Coprime
        ((scheduledCopiedAssignment ρ n u l r j : P) : ℕ))) :
      Pairwise (fun i j => (Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ)) i).Coprime
        (Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ)) j)) ∧
      Pairwise (fun i j => (Sum.elim (fun h => (r h : ℕ)) (fun y => (u y : ℕ)) i).Coprime
        (Sum.elim (fun h => (r h : ℕ)) (fun y => (u y : ℕ)) j)) := by
    have hm := scheduledCopiedAssignment_map ρ n (fun q : P => (q : ℕ)) u l r
    change Pairwise (fun i j =>
      ((fun i => ((scheduledCopiedAssignment ρ n u l r i : P) : ℕ)) i).Coprime
        ((fun i => ((scheduledCopiedAssignment ρ n u l r i : P) : ℕ)) j)) at hq
    rw [hm] at hq
    exact ⟨scheduledCopiedAssignment_pairwise_branch ρ n _ _ _ hq true,
      scheduledCopiedAssignment_pairwise_branch ρ n _ _ _ hq false⟩
  by_cases hprod : constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (l, t) *
      conj (constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (r, t')) = 0
  · by_cases hq : Pairwise (fun i j =>
        ((scheduledCopiedAssignment ρ n u l r i : P) : ℕ).Coprime
          ((scheduledCopiedAssignment ρ n u l r j : P) : ℕ))
    · rw [ite_eq_left hq]
      by_cases hw : fullAtomTransferWeight role childBound pivotBound ranges leaf (n + 1)
          (copiedConstituentAtomValues role size n P u l r) (s, t, t') = 0
      · rw [hw, mul_zero, hprod]
      · have hrel' : frequencyRoot n t *
            (scheduleAtomRight role ⟨n + 1, copiedConstituentAtomValues role size n P u l r⟩ : ℤ) -
            frequencyRoot n t' *
            (scheduleAtomLeft role ⟨n + 1, copiedConstituentAtomValues role size n P u l r⟩ : ℤ) = s * M := by
          rwa [copiedConstituentAtomValues_right, copiedConstituentAtomValues_left]
        obtain ⟨hn, hg⟩ := fullAtomTransferWeight_forced_node role childBound pivotBound ranges leaf
          n (copiedConstituentAtomValues role size n P u l r) s t t' M hs hrel' hw
        obtain ⟨hL, hR⟩ := hbranches hq
        exact constituentTransferWeight_product role size n P Q childBound pivotBound ranges leaf
          u l r s t t' M hn hg hL hR
    · rw [ite_eq_right hq, mul_zero, hprod]
  · obtain ⟨hl, hr⟩ := mul_ne_zero_iff.mp hprod
    have hr' : constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (r, t') ≠ 0 := by
      intro hz
      exact hr (by rw [hz, map_zero])
    obtain ⟨hn, hg, hq⟩ := constituentTransferWeight_copied_support role size n p hp P hP Q
      childBound pivotBound ranges leaf u l r s t t' M K V hl hr' hs hMpos hMbound hrel
      (hcutL hl).1 (hcutR hr').1 (hcutL hl).2 (hcutR hr').2 hscale hlarge
      (hgap hl hr') (hrange hl hr')
    rw [ite_eq_left hq]
    obtain ⟨hL, hR⟩ := hbranches hq
    exact constituentTransferWeight_product role size n P Q childBound pivotBound ranges leaf
      u l r s t t' M hn hg hL hR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentNextSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The supported next coefficient retains the same positive integer pivot -/

namespace Ostmann

open scoped BigOperators Classical

theorem fullAtomTransferWeight_copied_validPivot {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (P : Finset ℕ) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P)
    (l r : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P)
    (s : ℤ) (t t' : FrequencyTree ℤ n) (T : Finset ℕ)
    (hT : ∀ M, 0 < M → M ≤ pivotBound n →
      fullAtomTransferWeight role childBound pivotBound ranges leaf n
        (scheduledInsertedAtoms role n M
          (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
          (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) t ≠ 0 → M ∈ T)
    (hw : fullAtomTransferWeight role childBound pivotBound ranges leaf (n + 1)
      (copiedConstituentAtomValues role size n P u l r) (s, t, t') ≠ 0) :
    validTransferredPivot T
      (frequencyRoot n t * (∏ h, (r h : ℕ)) - frequencyRoot n t' * (∏ h, (l h : ℕ))) s := by
  obtain ⟨hg, M, hM, _, _⟩ := fullAtomTransferWeight_support role childBound pivotBound ranges leaf
    (n + 1) (copiedConstituentAtomValues role size n P u l r) (s, t, t') hw
  have hroot := ((fullAtomWeightGuard_node role childBound pivotBound ranges n
    (copiedConstituentAtomValues role size n P u l r) (s, t, t') M hM).mp hg).1
  have hchild := hw
  unfold copiedConstituentAtomValues at hchild hroot
  rw [fullAtomTransferWeight_copied role childBound pivotBound ranges leaf n _ _ _ s t t' M hM,
    ite_eq_left hroot] at hchild
  apply validTransferredPivot_of_eq T _ s hM.root_ne_zero M hM.pivot_pos
    (hT M hM.pivot_pos hM.pivot_bound (mul_ne_zero_iff.mp hchild).1)
  have hr := hM.relation
  change frequencyRoot n t *
      (scheduleAtomRight role ⟨n + 1, copiedConstituentAtomValues role size n P u l r⟩ : ℤ) -
      frequencyRoot n t' *
      (scheduleAtomLeft role ⟨n + 1, copiedConstituentAtomValues role size n P u l r⟩ : ℤ) = s * M at hr
  rwa [copiedConstituentAtomValues_left, copiedConstituentAtomValues_right] at hr

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentReconstructedProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact coefficient reconstruction with the original integer-pivot tests -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

theorem constituentTransferWeight_reconstructed_product {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (p : I) (hp : role p = .pivot n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P)
    (l r : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P)
    (s : ℤ) (t t' : FrequencyTree ℤ n) (K V : ℕ) (T : Finset ℕ)
    (hTpos : ∀ M ∈ T, 0 < M) (hTbound : ∀ M ∈ T, M ≤ pivotBound n)
    (hTfull : ∀ M, 0 < M → M ≤ pivotBound n →
      fullAtomTransferWeight role childBound pivotBound ranges leaf n
        (scheduledInsertedAtoms role n M
          (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
          (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) t ≠ 0 → M ∈ T)
    (hcutL : ∀ M ∈ T,
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (l, t) ≠ 0 →
      (frequencyRoot n t).natAbs ≤ childBound n ∧ (∏ h, (l h : ℕ)) ≤ K)
    (hcutR : ∀ M ∈ T,
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (r, t') ≠ 0 →
      (frequencyRoot n t').natAbs ≤ childBound n ∧ (∏ h, (r h : ℕ)) ≤ K)
    (hscale : ∀ M ∈ T, 2 * childBound n * K ≤ V * M)
    (hlarge : ∀ q ∈ P, V < q)
    (hgap : ∀ M ∈ T,
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (l, t) ≠ 0 →
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (r, t') ≠ 0 →
      2 * pivotBound n * childBound n < ∏ h, (r h : ℕ))
    (hrange : ∀ M ∈ T,
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (l, t) ≠ 0 →
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (r, t') ≠ 0 →
      ∀ a ∈ ranges (n + 1), a.Holds (copiedConstituentAtomValues role size n P u l r)) :
    let N := frequencyRoot n t * (∏ h, (r h : ℕ)) - frequencyRoot n t' * (∏ h, (l h : ℕ))
    let M := reconstructedPivot N s
    (if validTransferredPivot T N s then
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (l, t) *
        conj (constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (r, t'))
      else 0) =
    (((∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (l h)) *
       (∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (r h)) : ℝ) : ℂ) *
      (if Pairwise (fun i j =>
        ((scheduledCopiedAssignment (fun i : Σ a, Fin (size a) => role i.1) n u l r i : P) : ℕ).Coprime
          ((scheduledCopiedAssignment (fun i : Σ a, Fin (size a) => role i.1) n u l r j : P) : ℕ)) then
        fullAtomTransferWeight role childBound pivotBound ranges leaf (n + 1)
          (copiedConstituentAtomValues role size n P u l r) (s, t, t') else 0) := by
  dsimp only
  by_cases hvalid : validTransferredPivot T
      (frequencyRoot n t * (∏ h, (r h : ℕ)) - frequencyRoot n t' * (∏ h, (l h : ℕ))) s
  · rw [ite_eq_left hvalid]
    exact constituentTransferWeight_product_guarded role size n p hp P hP Q
      childBound pivotBound ranges leaf u l r s t t' _ K V hvalid.1
      (hTpos _ hvalid.2.2.2) (hTbound _ hvalid.2.2.2)
      (validTransferredPivot_equation T _ s hvalid)
      (hcutL _ hvalid.2.2.2) (hcutR _ hvalid.2.2.2)
      (hscale _ hvalid.2.2.2) hlarge (hgap _ hvalid.2.2.2) (hrange _ hvalid.2.2.2)
  · rw [ite_eq_right hvalid]
    have hz : fullAtomTransferWeight role childBound pivotBound ranges leaf (n + 1)
        (copiedConstituentAtomValues role size n P u l r) (s, t, t') = 0 := by
      by_contra hn
      exact hvalid (fullAtomTransferWeight_copied_validPivot role size n P childBound pivotBound ranges leaf
        u l r s t t' T hTfull hn)
    simp only [hz, ite_self, mul_zero]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledCopiedAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The reconstructed off-diagonal on the actual next schedule -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem copiedWeightedAmplitude_eq_scheduledNextAmplitude {I A : Type*}
    [Fintype I] [Fintype A]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (g : I → I → ℤ) (pivot : ℕ → I) (initial : I → ℤ → ℕ → ℂ)
    (n : ℕ) (hist : A → FrequencyTree ℤ n)
    (L : A → CopyScheduleH role n → ℕ) (U : CopyScheduleY role n → ℕ)
    [∀ a h, Fact (L a h).Prime] [∀ y, Fact (U y).Prime]
    (center : ∀ p : ℕ, ZMod p) (W : ℕ → A → ℂ) (T : Finset ℕ) (V : ℕ) :
    copiedWeightedAmplitude L U center
      (fun h => χ (copyScheduleOrigin n h.val)) (fun y => χ (copyScheduleOrigin n y.val))
      (scheduledRetainedGraph role g pivot n)
      (fun a h => copyScheduleUnary χ g pivot initial n (hist a) h.val (L a h))
      (fun a y => copyScheduleUnary χ g pivot initial n (hist a) y.val (U y))
      (fun a => frequencyRoot n (hist a)) W T V =
    scheduledNextAmplitude role χ g pivot initial n hist L U center W T V := by
  unfold copiedWeightedAmplitude scheduledNextAmplitude
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro a' _
  dsimp only
  split_ifs
  · rw [copiedDirectedPhase_scheduled role χ g pivot initial n (s, hist a, hist a')]
  · rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledCopiedSamplePhase
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The copied arithmetic phase is the next finite-sample phase -/

namespace Ostmann

open scoped Classical

theorem scheduledSamplePhase_copied {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (n : ℕ) (t : FrequencyTree ℤ (n + 1))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (u : CopyScheduleY role n → P) (l r : CopyScheduleH role n → P)
    (center : ∀ p : ℕ, ZMod p) :
    letI : ∀ h, Fact (l h : ℕ).Prime := fun h => ⟨hP _ (l h).property⟩
    letI : ∀ h, Fact (r h : ℕ).Prime := fun h => ⟨hP _ (r h).property⟩
    letI : ∀ y, Fact (u y : ℕ).Prime := fun y => ⟨hP _ (u y).property⟩
    letI := transferredPrimeFact (fun h => (l h : ℕ)) (fun h => (r h : ℕ)) (fun y => (u y : ℕ))
    scheduledPrimePhase role χ initialCompleteGraph pivot (initialRegularUnary χ κ) (n + 1) t
      (fun i => transferredLabels (fun h => (l h : ℕ)) (fun h => (r h : ℕ)) (fun y => (u y : ℕ))
        (copyScheduleSurvivorEquiv role n i)) center =
    scheduledSamplePhase role χ κ pivot (n + 1) t P hP (scheduledCopiedAssignment role n u l r) center := by
  let : ∀ h, Fact (l h : ℕ).Prime := fun h => ⟨hP _ (l h).property⟩
  let : ∀ h, Fact (r h : ℕ).Prime := fun h => ⟨hP _ (r h).property⟩
  let : ∀ y, Fact (u y : ℕ).Prime := fun y => ⟨hP _ (u y).property⟩
  let := transferredPrimeFact (fun h => (l h : ℕ)) (fun h => (r h : ℕ)) (fun y => (u y : ℕ))
  let : ∀ i, Fact ((scheduledCopiedAssignment role n u l r i : P) : ℕ).Prime :=
    fun i => ⟨hP _ (scheduledCopiedAssignment role n u l r i).property⟩
  unfold scheduledSamplePhase
  apply scheduledPrimePhase_congr_labels
  funext i
  unfold scheduledCopiedAssignment
  generalize copyScheduleSurvivorEquiv role n i = j
  rcases j with ⟨b, h⟩ | y
  · cases b <;> rfl
  · rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentScheduledNext
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete reconstructed sum with actual original-prior coefficients -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

theorem constituentScheduledNextAmplitude_eq {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (p : I) (hp : role p = .pivot n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P)
    (center : ∀ p : ℕ, ZMod p) (K V : ℕ) (T : Finset ℕ)
    (hTpos : ∀ M ∈ T, 0 < M) (hTbound : ∀ M ∈ T, M ≤ pivotBound n)
    (hTfull : ∀ (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) d M, 0 < M → M ≤ pivotBound n →
      fullAtomTransferWeight role childBound pivotBound ranges leaf n
        (scheduledInsertedAtoms role n M
          (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
          (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) (hist d) ≠ 0 → M ∈ T)
    (hcut : ∀ M ∈ T, ∀ a,
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0 →
      (frequencyRoot n (hist a.2)).natAbs ≤ childBound n ∧ (∏ h, (a.1 h : ℕ)) ≤ K)
    (hscale : ∀ M ∈ T, 2 * childBound n * K ≤ V * M)
    (hlarge : ∀ q ∈ P, V < q)
    (hgap : ∀ M ∈ T, ∀ a a',
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0 →
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a' ≠ 0 →
      2 * pivotBound n * childBound n < ∏ h, (a'.1 h : ℕ))
    (hrange : ∀ M ∈ T, ∀ a a',
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0 →
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a' ≠ 0 →
      ∀ b ∈ ranges (n + 1), b.Holds (copiedConstituentAtomValues role size n P u a.1 a'.1)) :
    let ρ := fun i : Σ a, Fin (size a) => role i.1
    letI : ∀ (a : (CopyScheduleH ρ n → P) × D) h, Fact (a.1 h : ℕ).Prime :=
      fun a h => ⟨hP _ (a.1 h).property⟩
    letI : ∀ y, Fact (u y : ℕ).Prime := fun y => ⟨hP _ (u y).property⟩
    scheduledNextAmplitude ρ χ initialCompleteGraph pivot (initialRegularUnary χ κ)
      n (fun a => hist a.2) (fun a h => (a.1 h : ℕ)) (fun y => (u y : ℕ)) center
      (constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u) T V =
    ∑ s ∈ transferFrequencyRange V, ∑ l, ∑ d, ∑ r, ∑ d',
      (((∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (l h)) *
        (∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (r h)) : ℝ) : ℂ) *
      fullAtomTransferWeight role childBound pivotBound ranges leaf (n + 1)
        (copiedConstituentAtomValues role size n P u l r) (s, hist d, hist d') *
      (if Pairwise (fun i j =>
        ((scheduledCopiedAssignment ρ n u l r i : P) : ℕ).Coprime
          ((scheduledCopiedAssignment ρ n u l r j : P) : ℕ)) then
        scheduledSamplePhase ρ χ κ pivot (n + 1) (s, hist d, hist d') P hP
          (scheduledCopiedAssignment ρ n u l r) center else 0) := by
  let ρ := fun i : Σ a, Fin (size a) => role i.1
  let : ∀ (a : (CopyScheduleH ρ n → P) × D) h, Fact (a.1 h : ℕ).Prime :=
    fun a h => ⟨hP _ (a.1 h).property⟩
  let : ∀ y, Fact (u y : ℕ).Prime := fun y => ⟨hP _ (u y).property⟩
  unfold scheduledNextAmplitude
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro d' _
  have hc := constituentTransferWeight_reconstructed_product role size n p hp P hP Q
    childBound pivotBound ranges leaf u l r s (hist d) (hist d') K V T hTpos hTbound
    (hTfull l d) (fun M hM => hcut M hM (l, d)) (fun M hM => hcut M hM (r, d'))
    hscale hlarge (fun M hM => hgap M hM (l, d) (r, d'))
    (fun M hM => hrange M hM (l, d) (r, d'))
  have hphase := scheduledSamplePhase_copied ρ χ κ pivot n (s, hist d, hist d') P hP u l r center
  calc
    _ = (if validTransferredPivot T
          (frequencyRoot n (hist d) * (∏ h, (r h : ℕ)) -
           frequencyRoot n (hist d') * (∏ h, (l h : ℕ))) s then
          constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u
            (reconstructedPivot (frequencyRoot n (hist d) * (∏ h, (r h : ℕ)) -
              frequencyRoot n (hist d') * (∏ h, (l h : ℕ))) s) (l, d) *
          conj (constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u
            (reconstructedPivot (frequencyRoot n (hist d) * (∏ h, (r h : ℕ)) -
              frequencyRoot n (hist d') * (∏ h, (l h : ℕ))) s) (r, d')) else 0) *
        scheduledSamplePhase ρ χ κ pivot (n + 1) (s, hist d, hist d') P hP
          (scheduledCopiedAssignment ρ n u l r) center := by
      split_ifs
      · rw [hphase]
      · simp only [zero_mul]
    _ = _ := by
      have hwl (M) : constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M (l, d) =
          constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (l, hist d) := rfl
      have hwr (M) : constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M (r, d') =
          constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (r, hist d') := rfl
      simp_rw [hwl, hwr]
      rw [hc]
      split_ifs <;> ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_CopiedAmplitudeFubini
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite reordering of the two branch priors and three frequency indices -/

namespace Ostmann

open scoped BigOperators Classical

theorem copiedFrequency_sum {D : Type*} [Fintype D] (S : Finset ℤ)
    (F : ℤ → D → D → ℂ) :
    (∑ a : S × (D × D), F a.1 a.2.1 a.2.2) = ∑ s ∈ S, ∑ d, ∑ e, F s d e := by
  simp only [Fintype.sum_prod_type]
  exact Finset.sum_coe_sort S (fun s => ∑ d, ∑ e, F s d e)

theorem copied_prior_sum_reorder {H D : Type*} [Fintype H] [Fintype D]
    (S : Finset ℤ) (w : H → ℂ) (F : ℤ → H → D → H → D → ℂ) :
    (∑ l, w l * ∑ r, w r * ∑ s ∈ S, ∑ d, ∑ e, F s l d r e) =
      ∑ s ∈ S, ∑ l, ∑ d, ∑ r, ∑ e, w l * (w r * F s l d r e) := by
  symm
  calc
    _ = ∑ l, ∑ s ∈ S, ∑ d, ∑ r, ∑ e, w l * (w r * F s l d r e) := Finset.sum_comm
    _ = ∑ l, ∑ r, ∑ s ∈ S, ∑ d, ∑ e, w l * (w r * F s l d r e) := by
      apply Finset.sum_congr rfl
      intro l _
      calc
        _ = ∑ s ∈ S, ∑ r, ∑ d, ∑ e, w l * (w r * F s l d r e) := by
          apply Finset.sum_congr rfl
          intro s _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by simp only [Finset.mul_sum]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentGuardedNext
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The guarded next expectation is the actual arithmetic off-diagonal -/

namespace Ostmann

open scoped BigOperators Classical

theorem constituentPrimeGuardedAmplitude_next {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (p : I) (hp : role p = .pivot n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (center : ∀ p : ℕ, ZMod p) (K V : ℕ) (T : Finset ℕ)
    (hTpos : ∀ M ∈ T, 0 < M) (hTbound : ∀ M ∈ T, M ≤ pivotBound n)
    (hTfull : ∀ (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) d M, 0 < M → M ≤ pivotBound n →
      fullAtomTransferWeight role childBound pivotBound ranges leaf n
        (scheduledInsertedAtoms role n M
          (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
          (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) (hist d) ≠ 0 → M ∈ T)
    (hcut : ∀ u, ∀ M ∈ T, ∀ a,
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0 →
      (frequencyRoot n (hist a.2)).natAbs ≤ childBound n ∧ (∏ h, (a.1 h : ℕ)) ≤ K)
    (hscale : ∀ M ∈ T, 2 * childBound n * K ≤ V * M)
    (hlarge : ∀ q ∈ P, V < q)
    (hgap : ∀ u, ∀ M ∈ T, ∀ a a',
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0 →
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a' ≠ 0 →
      2 * pivotBound n * childBound n < ∏ h, (a'.1 h : ℕ))
    (hrange : ∀ u, ∀ M ∈ T, ∀ a a',
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0 →
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a' ≠ 0 →
      ∀ b ∈ ranges (n + 1), b.Holds (copiedConstituentAtomValues role size n P u a.1 a'.1)) :
    let ρ := fun i : Σ a, Fin (size a) => role i.1
    letI : ∀ (a : (CopyScheduleH ρ n → P) × D) h, Fact (a.1 h : ℕ).Prime :=
      fun a h => ⟨hP _ (a.1 h).property⟩
    letI : ∀ (u : CopyScheduleY ρ n → P) y, Fact (u y : ℕ).Prime :=
      fun u y => ⟨hP _ (u y).property⟩
    constituentPrimeGuardedAmplitude role size χ κ pivot (n + 1) P hP Q
      childBound pivotBound ranges leaf (copiedConstituentHistory hist V) center =
      ∑ u, ((∏ y, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) (u y) : ℝ) : ℂ) *
        scheduledNextAmplitude ρ χ initialCompleteGraph pivot (initialRegularUnary χ κ)
          n (fun a => hist a.2) (fun a h => (a.1 h : ℕ)) (fun y => (u y : ℕ)) center
          (constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u) T V := by
  let ρ := fun i : Σ a, Fin (size a) => role i.1
  let : ∀ (a : (CopyScheduleH ρ n → P) × D) h, Fact (a.1 h : ℕ).Prime :=
    fun a h => ⟨hP _ (a.1 h).property⟩
  let : ∀ (u : CopyScheduleY ρ n → P) y, Fact (u y : ℕ).Prime :=
    fun u y => ⟨hP _ (u y).property⟩
  rw [constituentPrimeGuardedAmplitude_copied]
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  rw [constituentScheduledNextAmplitude_eq role size χ κ pivot n p hp P hP Q
    childBound pivotBound ranges leaf hist u center K V T hTpos hTbound
    (hTfull u) (hcut u) hscale hlarge (hgap u) (hrange u)]
  let w (l : CopyScheduleH ρ n → P) : ℂ :=
    ((∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (l h) : ℝ) : ℂ)
  let F (s : ℤ) (l : CopyScheduleH ρ n → P) (d : D)
      (r : CopyScheduleH ρ n → P) (d' : D) : ℂ :=
    fullAtomTransferWeight role childBound pivotBound ranges leaf (n + 1)
      (copiedConstituentAtomValues role size n P u l r) (s, hist d, hist d') *
      (if Pairwise (fun i j =>
        ((scheduledCopiedAssignment ρ n u l r i : P) : ℕ).Coprime
          ((scheduledCopiedAssignment ρ n u l r j : P) : ℕ)) then
        scheduledSamplePhase ρ χ κ pivot (n + 1) (s, hist d, hist d') P hP
          (scheduledCopiedAssignment ρ n u l r) center else 0)
  simp only [Complex.ofReal_mul, mul_assoc]
  change (∑ l, w l * ∑ r, w r *
    ∑ a : (transferFrequencyRange V) × (D × D), F a.1.val l a.2.1 r a.2.2) =
    ∑ s ∈ transferFrequencyRange V, ∑ l, ∑ d, ∑ r, ∑ d', w l * (w r * F s l d r d')
  have hs (l r : CopyScheduleH ρ n → P) :=
    copiedFrequency_sum (transferFrequencyRange V) (fun s d d' => F s l d r d')
  simp_rw [hs]
  exact copied_prior_sum_reorder (transferFrequencyRange V) w F

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SupportedPivotTuples
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restricting pivot tuples to the support of their original harmonic priors -/

namespace Ostmann

open scoped BigOperators Classical

theorem mem_supportedPivotTuples (P : Finset ℕ) {r : ℕ} (Q : Fin r → Finset ℕ) (x : Fin r → P) :
    x ∈ supportedPivotTuples P Q ↔ Function.Injective x ∧ ∀ i, (x i : ℕ) ∈ Q i := by
  simp only [supportedPivotTuples, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Zero prior mass permits the exact restriction to the original prime cells. -/
theorem scheduledCurrentAmplitude_restrict_cells {I A Z : Type*}
    [Fintype I] [Fintype A] [Fintype Z]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (n r : ℕ)
    (e : Fin r ≃ CurrentPivotConstituent role n) (hist : A → FrequencyTree ℤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : Fin r → Finset ℕ) (S : Finset (Fin r → P))
    (L : A → CopyScheduleH role n → ℕ) (U : Z → CopyScheduleY role n → ℕ)
    [∀ a h, Fact (L a h).Prime] [∀ z y, Fact (U z y).Prime]
    (center : ∀ p : ℕ, ZMod p) (W : Z → ℕ → A → ℂ) (μ : Z → ℝ) :
    scheduledCurrentAmplitude role χ κ pivot n r e hist P hP Q S L U center W μ =
      scheduledCurrentAmplitude role χ κ pivot n r e hist P hP Q
        (S.filter (fun x => ∀ i, (x i : ℕ) ∈ Q i)) L U center W μ := by
  unfold scheduledCurrentAmplitude
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hq : ∀ i, (x i : ℕ) ∈ Q i
  · rw [ite_eq_left hq]
  · rw [ite_eq_right hq]
    have hz : productPrior (fun i => primeSubsetPrior P (Q i)) x = 0 := by
      by_contra hn
      apply hq
      intro i
      exact primeSubsetPrior_support P (Q i) (x i)
        ((Finset.prod_ne_zero_iff.mp hn) i (Finset.mem_univ i))
    simp only [hz, Complex.ofReal_zero, zero_mul]

theorem constituentPrimeGuardedAmplitude_eq_supported_transfer {I D : Type*}
    [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (p : I) (hp : role p = .pivot n) (hu : ∀ i, role i = .pivot n → i = p)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (center : ∀ p : ℕ, ZMod p) :
    let ρ := fun i : Σ a, Fin (size a) => role i.1
    letI : ∀ (a : (CopyScheduleH ρ n → P) × D) h, Fact (a.1 h : ℕ).Prime :=
      fun a h => ⟨hP _ (a.1 h).property⟩
    letI : ∀ (u : CopyScheduleY ρ n → P) y, Fact (u y : ℕ).Prime :=
      fun u y => ⟨hP _ (u y).property⟩
    constituentPrimeGuardedAmplitude role size χ κ pivot n P hP Q childBound pivotBound ranges leaf hist center =
      scheduledCurrentAmplitude ρ χ κ pivot n (size p) (pivotConstituentEquiv role size n p hp hu)
        (fun a => hist a.2) P hP (fun k => Q ⟨p, k⟩) (supportedPivotTuples P (fun k => Q ⟨p, k⟩))
        (fun a h => (a.1 h : ℕ)) (fun u y => (u y : ℕ)) center
        (constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist)
        (fun u => ∏ y, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) (u y)) := by
  let ρ := fun i : Σ a, Fin (size a) => role i.1
  let : ∀ (a : (CopyScheduleH ρ n → P) × D) h, Fact (a.1 h : ℕ).Prime :=
    fun a h => ⟨hP _ (a.1 h).property⟩
  let : ∀ (u : CopyScheduleY ρ n → P) y, Fact (u y : ℕ).Prime :=
    fun u y => ⟨hP _ (u y).property⟩
  rw [constituentPrimeGuardedAmplitude_eq_transfer role size χ κ pivot n p hp hu]
  apply scheduledCurrentAmplitude_restrict_cells

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentIntervalSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original atom intervals discharge the support clauses of the transfer -/

namespace Ostmann

open scoped BigOperators Classical

theorem fullAtomTransferWeight_inserted_pivot_bounds {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (lo hi : I → ℕ)
    (childBound pivotBound : ℕ → ℕ) (leaf : ScheduleAtomState role → ℤ → ℂ)
    (n : ℕ) (p : I) (hp : role p = .pivot n) (M : ℕ)
    (l : CopyScheduleH role n → ℕ) (u : CopyScheduleY role n → ℕ) (t : FrequencyTree ℤ n)
    (hw : fullAtomTransferWeight role childBound pivotBound (atomIntervalRanges role lo hi) leaf n
      (scheduledInsertedAtoms role n M l u) t ≠ 0) : lo p ≤ M ∧ M ≤ hi p := by
  let v := scheduledPartitionEquiv role n (.inl ⟨p, hp⟩)
  have hr : atomInterval role lo hi n v ∈ atomIntervalRanges role lo hi n :=
    List.mem_map.mpr ⟨v, Finset.mem_toList.mpr (Finset.mem_univ v), rfl⟩
  have hh := (atomInterval_holds_iff role lo hi n v _).mp
    (fullAtomTransferWeight_top_range role childBound pivotBound _ leaf n _ t hw _ hr)
  dsimp only [v] at hh
  rw [scheduledInsertedAtoms_pivot] at hh
  simpa only [scheduledPartitionEquiv_pivot, copyScheduleOrigin_positive] using hh

theorem constituentTransferWeight_copied_intervals {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (lo hi : I → ℕ) (n : ℕ)
    (P : Finset ℕ) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (leaf : ScheduleAtomState role → ℤ → ℂ)
    (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (a b : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D)
    (ha : constituentTransferWeight role size n P Q childBound pivotBound
      (atomIntervalRanges role lo hi) leaf hist u M a ≠ 0)
    (hb : constituentTransferWeight role size n P Q childBound pivotBound
      (atomIntervalRanges role lo hi) leaf hist u M b ≠ 0) :
    ∀ c ∈ atomIntervalRanges role lo hi (n + 1),
      c.Holds (copiedConstituentAtomValues role size n P u a.1 b.1) := by
  have hL := constituentTransferWeight_full_ne_zero role size n P Q childBound pivotBound
    (atomIntervalRanges role lo hi) leaf hist u M a ha
  have hR := constituentTransferWeight_full_ne_zero role size n P Q childBound pivotBound
    (atomIntervalRanges role lo hi) leaf hist u M b hb
  exact fullAtomTransferWeight_copied_intervals role lo hi childBound pivotBound leaf n M _ _ _
    (hist a.2) (hist b.2) hL hR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferIteration
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The reserved exponential lower bound through the transfers -/

namespace Ostmann

private theorem half_exponential_square (c q : ℝ) :
    Real.exp (-c) / 2 * Real.exp (-q) ^ 2 =
      Real.exp (-2 * q - c - Real.log 2) := by
  calc
    _ = (Real.exp (-c) * Real.exp (2 * -q)) / 2 := by
      rw [show Real.exp (2 * -q) = Real.exp (-q) ^ 2 by
        simpa only [Nat.cast_ofNat] using Real.exp_nat_mul (-q) 2]
      ring
    _ = Real.exp (-c + 2 * -q) / 2 := by rw [Real.exp_add]
    _ = Real.exp ((-c + 2 * -q) - Real.log 2) := by
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ = _ := by congr 1; ring

theorem transfer_half_lower (x y D B t c : ℝ) (ht : 0 ≤ t)
    (hbudget : c + Real.log 2 ≤ t)
    (hx : Real.exp (-B * t) ≤ x)
    (hD : D ≤ Real.exp (-(2 * B + 3) * t))
    (htransfer : Real.exp (-c) * x ^ 2 ≤ D + y) :
    Real.exp (-c) / 2 * x ^ 2 ≤ y := by
  have hsmall : Real.exp (-(2 * B + 3) * t) ≤
      Real.exp (-c) / 2 * Real.exp (-B * t) ^ 2 := by
    calc
      _ ≤ Real.exp (-2 * (B * t) - c - Real.log 2) :=
        Real.exp_le_exp.mpr (by nlinarith)
      _ = _ := by
        simpa only [neg_mul] using (half_exponential_square c (B * t)).symm
  have hxx : Real.exp (-B * t) ^ 2 ≤ x ^ 2 := by
    have hx0 := (Real.exp_pos (-B * t)).le
    nlinarith
  have hDx := hD.trans (hsmall.trans
    (mul_le_mul_of_nonneg_left hxx (by positivity)))
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_VariableTransferIteration
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The amplitude reserve with the actual, varying transfer losses -/

namespace Ostmann

open scoped BigOperators

private theorem half_sq_exp (d q : ℝ) :
    Real.exp (-d) / 2 * Real.exp (-q) ^ 2 =
      Real.exp (-d + 2 * -q - Real.log 2) := by
  rw [← Real.exp_nat_mul, div_mul_eq_mul_div, ← Real.exp_add,
    Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- Summing the actual losses before using the geometric reserve avoids a
uniform per-step loss assumption. The endpoint is finite, as in the paper. -/
theorem variable_transfer_iteration (k : ℕ) (η : ℕ → ℂ) (diag d : ℕ → ℝ)
    (B₀ m : ℝ) (hm : 0 ≤ m) (hd : ∀ j < k, 0 ≤ d j)
    (hbudget : ∑ j ∈ Finset.range k, (d j + Real.log 2) ≤ m)
    (hzero : Real.exp (-B₀ * m) ≤ ‖η 0‖)
    (hdiag : ∀ j < k, diag j ≤ Real.exp (-(2 * (B₀ + 1) + 3) * (2 : ℝ) ^ j * m))
    (htransfer : ∀ j < k, Real.exp (-d j) * ‖η j‖ ^ 2 ≤ diag j + ‖η (j + 1)‖) :
    ∀ j ≤ k, Real.exp (-(B₀ + 1) * (2 : ℝ) ^ j * m) ≤ ‖η j‖ := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hsum (j : ℕ) (hj : j ≤ k) :
      ∑ h ∈ Finset.range j, (d h + Real.log 2) ≤ m := by
    apply le_trans _ hbudget
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hj)
      (fun i hi _ => add_nonneg (hd i (Finset.mem_range.mp hi)) hlog)
  have hfine : ∀ j ≤ k,
      Real.exp (-((2 : ℝ) ^ j * (B₀ * m + ∑ h ∈ Finset.range j, (d h + Real.log 2)))) ≤ ‖η j‖ := by
    intro j
    induction j with
    | zero => intro _; simpa using hzero
    | succ j ih =>
      intro hj
      have hjk : j < k := by omega
      have hjle : j ≤ k := by omega
      have hprev := ih hjle
      have hcoarse : Real.exp (-(B₀ + 1) * ((2 : ℝ) ^ j * m)) ≤ ‖η j‖ := by
        apply le_trans (Real.exp_le_exp.mpr ?_) hprev
        have hs := mul_le_mul_of_nonneg_left (hsum j hjle) (show 0 ≤ (2 : ℝ) ^ j by positivity)
        nlinarith
      have hloss : d j + Real.log 2 ≤ m := by
        apply le_trans _ (hsum (j + 1) hj)
        have hnonneg : 0 ≤ ∑ h ∈ Finset.range j, (d h + Real.log 2) :=
          Finset.sum_nonneg fun h hh => add_nonneg (hd h (lt_of_lt_of_le (Finset.mem_range.mp hh) hjle)) hlog
        rw [Finset.sum_range_succ]
        linarith
      have ht : 0 ≤ (2 : ℝ) ^ j * m := by positivity
      have htbig : m ≤ (2 : ℝ) ^ j * m := le_mul_of_one_le_left hm (one_le_pow₀ (by norm_num))
      have hhalf := transfer_half_lower ‖η j‖ ‖η (j + 1)‖ (diag j) (B₀ + 1)
        ((2 : ℝ) ^ j * m) (d j) ht (hloss.trans htbig) hcoarse
        (by simpa only [mul_assoc] using hdiag j hjk) (htransfer j hjk)
      have hpow := pow_le_pow_left₀ (Real.exp_nonneg _) hprev 2
      apply le_trans _ hhalf
      apply le_trans _ (mul_le_mul_of_nonneg_left hpow (by positivity))
      rw [half_sq_exp]
      apply Real.exp_le_exp.mpr
      rw [Finset.sum_range_succ, pow_succ]
      have hscale : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
      have hl0 : 0 ≤ d j + Real.log 2 := add_nonneg (hd j hjk) hlog
      nlinarith
  intro j hj
  apply le_trans (Real.exp_le_exp.mpr ?_) (hfine j hj)
  have hs := mul_le_mul_of_nonneg_left (hsum j hj) (show 0 ≤ (2 : ℝ) ^ j by positivity)
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FinitePivotSchedule
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite pivot hypotheses for a finite-depth arithmetic schedule

Only the pivots through the current depth occur in these formulas. The
finite construction therefore supplies exactly those roles, without a
hypothesis requiring infinitely many roles in a finite type.
-/
namespace Ostmann
open scoped Classical BigOperators

theorem scheduledRegularRow_pivot_finite {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (i : I) (k : ℕ) (hi : role i = .pivot k)
    (n : ℕ) (hn : n ≤ k) (hpivot : ∀ j ≤ n, role (pivot j) = .pivot j) :
    ScheduledRegularRow role initialCompleteGraph pivot n (copySchedulePositive n i) 1 := by
  induction n with
  | zero =>
    intro j _ hji
    exact initialCompleteGraph_of_ne hji.symm
  | succ n ih =>
    have hnk : n < k := by omega
    have hpn := hpivot n (Nat.le_succ n)
    have hc : (copyScheduleRole role n (copySchedulePositive n i)).copiedAt n = true := by
      rw [copyScheduleRole_positive role i k hi]
      simpa [CopyScheduleRole.copiedAt] using hnk
    have hp := copyScheduleSurvives_positive role (pivot n) n hpn n le_rfl
    have hne : copySchedulePositive n (pivot n) ≠ copySchedulePositive n i := by
      intro he
      have h := congrArg (copyScheduleRole role n) he
      rw [copyScheduleRole_positive role (pivot n) n hpn, copyScheduleRole_positive role i k hi] at h
      have : n = k := CopyScheduleRole.pivot.inj h
      omega
    exact scheduledRegularRow_copy role initialCompleteGraph pivot n _ _
      (ih (by omega) (fun j hj => hpivot j (hj.trans (Nat.le_succ n)))) hc hp hne true

theorem copyScheduleUnary_pivot_finite {I : Type*} (role : I → CopyScheduleRole)
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p) (κ : I → ℕ → ℂ)
    (pivot : ℕ → I) (i : I) (k : ℕ) (hi : role i = .pivot k) (p : ℕ) [Fact p.Prime]
    (n : ℕ) (hn : n ≤ k) (hpivot : ∀ j ≤ n, role (pivot j) = .pivot j)
    (t : FrequencyTree ℤ n)
    (hfreq : ∀ s ∈ allFrequencyList n t, (s : ZMod p) ≠ 0) :
    copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ) n t
        (copySchedulePositive n i) p =
      regularUnary (χ i p) (κ i p) 1 ((frequencyRoot n t : ℤ) : ZMod p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hpn := hpivot n (Nat.le_succ n)
    have hpast : ∀ j ≤ n, role (pivot j) = .pivot j :=
      fun j hj => hpivot j (hj.trans (Nat.le_succ n))
    have hfreqL : ∀ s ∈ allFrequencyList n t.2.1, (s : ZMod p) ≠ 0 := by
      intro s hs
      exact hfreq s (List.mem_cons_of_mem _ (List.mem_append_left _ hs))
    have hg : copyScheduleGraph initialCompleteGraph pivot n (copySchedulePositive n i)
        (copySchedulePositive n (pivot n)) = 1 := by
      apply scheduledRegularRow_pivot_finite role pivot i k hi n (by omega) hpast
      · exact copyScheduleSurvives_positive role (pivot n) n hpn n le_rfl
      · intro he
        have hr := congrArg (copyScheduleRole role n) he
        rw [copyScheduleRole_positive role (pivot n) n hpn,
          copyScheduleRole_positive role i k hi] at hr
        have := CopyScheduleRole.pivot.inj hr
        omega
    change copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ) n t.2.1
        (copySchedulePositive n i) p *
      χ (copyScheduleOrigin n (copySchedulePositive n i)) p
        (((frequencyRoot n t.2.1 : ℤ) : ZMod p) * (t.1 : ZMod p)⁻¹) ^
        copyScheduleGraph initialCompleteGraph pivot n (copySchedulePositive n i)
          (copySchedulePositive n (pivot n)) = _
    rw [ih (by omega) hpast t.2.1 hfreqL, copyScheduleOrigin_positive, hg]
    simpa only [regularCopiedMultiplier, ite_true, if_true, transferCopySign, one_mul,
      div_eq_mul_inv, frequencyRoot] using
      regularUnary_left (χ i p) (κ i p) 1
        ((frequencyRoot n t.2.1 : ℤ) : ZMod p) (t.1 : ZMod p)
        (hfreqL _ (frequencyRoot_mem_allFrequencyList n t.2.1))

theorem scheduledRetainedGraph_pivot_column_finite {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n : ℕ) (hpivot : role (pivot n) = .pivot n)
    (p : I) (hp : role p = .pivot n) (i : CopyScheduleH role n ⊕ CopyScheduleY role n) :
    scheduledRetainedGraph role initialCompleteGraph pivot n (some i) none =
      copyScheduleGraph initialCompleteGraph pivot n
        (Sum.elim Subtype.val Subtype.val i) (copySchedulePositive n p) := by
  cases i with
  | inl i =>
    apply copyScheduleGraph_pivot_common_column role pivot n (pivot n) p hpivot hp n le_rfl i.val i.property.1
    intro he
    have hc := i.property.2
    rw [he] at hc
    simp [CopyScheduleRole.copiedAt] at hc
  | inr i =>
    apply copyScheduleGraph_pivot_common_column role pivot n (pivot n) p hpivot hp n le_rfl i.val i.property.1
    intro he
    have hc := i.property.2.2
    rw [he] at hc
    simp [CopyScheduleRole.erasedAt] at hc

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteScheduledPhase
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Current phase identities with only the finitely used pivot roles -/
namespace Ostmann
open scoped BigOperators Classical

theorem scheduledInputPhase_factor_finite {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (n r : ℕ)
    (hpivot : ∀ k ≤ n, role (pivot k) = .pivot k) (e : Fin r ≃ CurrentPivotConstituent role n) (t : FrequencyTree ℤ n)
    (P : Fin r → ℕ) (L : CopyScheduleH role n → ℕ) (U : CopyScheduleY role n → ℕ)
    [∀ i, Fact (P i).Prime] [∀ i, Fact (L i).Prime] [∀ i, Fact (U i).Prime]
    (center : ∀ p : ℕ, ZMod p)
    (hc : Pairwise (fun i j => (Sum.elim P (Sum.elim L U) i).Coprime
      (Sum.elim P (Sum.elim L U) j)))
    (hfreq : ∀ i, ∀ s ∈ allFrequencyList n t, (s : ZMod (P i)) ≠ 0) :
    letI := scheduledInputPrimeFact role n r e P L U
    scheduledPrimePhase role χ initialCompleteGraph pivot (initialRegularUnary χ κ) n t
      (scheduledInputLabels role n r e P L U) center =
      groupedResidueRow P (fun i => χ (e i).val (P i)) (fun i => κ (e i).val (P i))
        (fun i => center (P i)) (∏ y, U y) (fun _ => 1)
        (positiveIntegerPivotKey (∏ i, P i) (groupedPivotProduct_pos P)
          (∏ h, L h) (frequencyRoot n t)) *
      retainedPrimePhase L U center (fun h => χ (copyScheduleOrigin n h.val))
        (fun y => χ (copyScheduleOrigin n y.val)) (scheduledRetainedGraph role initialCompleteGraph pivot n)
        (fun h => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ) n t h.val (L h))
        (fun y => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ) n t y.val (U y))
        (∏ i, P i) (frequencyRoot n t) := by
  let := scheduledInputPrimeFact role n r e P L U
  let E := enumeratedPartitionEquiv role n r e
  let p : Fin r ⊕ (CopyScheduleH role n ⊕ CopyScheduleY role n) → ℕ := Sum.elim P (Sum.elim L U)
  let hp : ∀ i, Fact (p i).Prime := by
    intro i
    rcases i with i | h | y
    · exact inferInstanceAs (Fact (P i).Prime)
    · exact inferInstanceAs (Fact (L h).Prime)
    · exact inferInstanceAs (Fact (U y).Prime)
  let hpR : ∀ i, Fact (p (.inr i)).Prime := fun i => hp (.inr i)
  let ν := fun i => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
    n t (E i).val (p i)
  let g := fun i j => copyScheduleGraph initialCompleteGraph pivot n (E i).val (E j).val
  have hν (i : Fin r) : ν (.inl i) = κ (e i).val (p (.inl i)) *
      χ (copyScheduleOrigin n (E (.inl i)).val) (p (.inl i))
        ((frequencyRoot n t : ℤ) : ZMod (p (.inl i))) ^ (-(1 : ℤ)) := by
    change copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
      n t (copySchedulePositive n (e i).val) (P i) = _
    rw [copyScheduleUnary_pivot_finite role χ κ pivot (e i).val n (e i).property
      (P i) n le_rfl hpivot t (hfreq i)]
    simp only [regularUnary, E, enumeratedPartitionEquiv_pivot, copyScheduleOrigin_positive, p, Sum.elim_inl]
    rfl
  have hrow (i : Fin r) (j) (hji : j ≠ .inl i) : g (.inl i) j = 1 := by
    apply scheduledRegularRow_pivot_finite role pivot (e i).val n (e i).property n le_rfl hpivot
    · exact (E j).property
    · intro he
      exact hji (E.injective (Subtype.ext he))
  have hself (i : Fin r) : g (.inl i) (.inl i) = 0 :=
    copyScheduleGraph_diagonal initialCompleteGraph pivot initialCompleteGraph_self n _
  have hcolumn (i : CopyScheduleH role n ⊕ CopyScheduleY role n) (k : Fin r) :
      g (.inr i) (.inl k) =
        scheduledRetainedGraph role initialCompleteGraph pivot n (some i) none := by
    dsimp only [g, E]
    rw [enumeratedPartitionEquiv_rest, enumeratedPartitionEquiv_pivot]
    exact (scheduledRetainedGraph_pivot_column_finite role pivot n (hpivot n le_rfl) (e k).val (e k).property i).symm
  have hrest (i j : CopyScheduleH role n ⊕ CopyScheduleY role n) :
      g (.inr i) (.inr j) =
        scheduledRetainedGraph role initialCompleteGraph pivot n (some i) (some j) := by
    cases i <;> cases j <;> rfl
  have he := directedPrimePhase_factor_grouped p
    (fun i => χ (copyScheduleOrigin n (E i).val) (p i))
    (fun i => center (p i)) ν g (scheduledRetainedGraph role initialCompleteGraph pivot n)
    (fun i => κ (e i).val (P i)) (fun _ => 1) (∏ h, L h) (∏ y, U y) (frequencyRoot n t)
    hc (by simp only [p, Sum.elim_inr, Fintype.prod_sum_type, Sum.elim_inl])
    (fun i => hfreq i _ (frequencyRoot_mem_allFrequencyList n t)) hν hself hrow hcolumn hrest
  have hr := directedPrimePhase_equiv E.symm p
    (fun i => χ (copyScheduleOrigin n (E i).val) (p i)) (fun i => center (p i)) ν g
    (frequencyRoot n t)
  have hχ : (fun i => χ (copyScheduleOrigin n (E (E.symm i)).val) (p (E.symm i))) =
      (fun i => χ (copyScheduleOrigin n i.val) (p (E.symm i))) := by
    funext i
    rw [E.apply_symm_apply]
  have hu : (fun i => ν (E.symm i)) =
      (fun i => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
        n t i.val (p (E.symm i))) := by
    funext i
    dsimp only [ν]
    rw [E.apply_symm_apply]
  have hg : (fun i j => g (E.symm i) (E.symm j)) =
      (fun i j => copyScheduleGraph initialCompleteGraph pivot n i.val j.val) := by
    funext i j
    dsimp only [g]
    rw [E.apply_symm_apply, E.apply_symm_apply]
  rw [hχ, hu, hg] at hr
  have hr' : scheduledPrimePhase role χ initialCompleteGraph pivot (initialRegularUnary χ κ)
      n t (scheduledInputLabels role n r e P L U) center =
      directedPrimePhase p (fun i => χ (copyScheduleOrigin n (E i).val) (p i))
        (fun i => center (p i)) ν g (frequencyRoot n t) := hr
  rw [hr']
  rw [retainedGroupedPhase_split (fun i => p (.inr i))
    (fun i => χ (copyScheduleOrigin n (E (.inr i)).val)) center] at he
  simpa only [E, p, ν, g, enumeratedPartitionEquiv_pivot, enumeratedPartitionEquiv_rest,
    copyScheduleOrigin_positive, Sum.elim_inl, Sum.elim_inr] using he

/-- Pairwise support on the retained branch and coprimality with the total
pivot already imply all the constituent-level cross checks. -/

theorem sampledScheduledPhase_factor_finite {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (n r : ℕ)
    (hpivot : ∀ k ≤ n, role (pivot k) = .pivot k) (e : Fin r ≃ CurrentPivotConstituent role n) (t : FrequencyTree ℤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (x : Fin r → P) (hx : Function.Injective x)
    (L : CopyScheduleH role n → ℕ) (U : CopyScheduleY role n → ℕ)
    [∀ h, Fact (L h).Prime] [∀ y, Fact (U y).Prime]
    (center : ∀ p : ℕ, ZMod p)
    (hLU : Pairwise (fun i j => (Sum.elim L U i).Coprime (Sum.elim L U j)))
    (hM : (∏ i, (x i : ℕ)).Coprime ((∏ h, L h) * ∏ y, U y))
    (hfreq : ∀ i, ∀ s ∈ allFrequencyList n t, (s : ZMod (x i : ℕ)) ≠ 0) :
    sampledScheduledPhase role χ κ pivot n r e t P hP x L U center =
      primeTupleResidueRow P hP (fun i => χ (e i).val)
        (fun i p => κ (e i).val p) center (∏ y, U y) (fun _ => 1) x
        (primeTuplePivotKey P hP x (∏ h, L h) (frequencyRoot n t)) *
      retainedPrimePhase L U center (fun h => χ (copyScheduleOrigin n h.val))
        (fun y => χ (copyScheduleOrigin n y.val)) (scheduledRetainedGraph role initialCompleteGraph pivot n)
        (fun h => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ) n t h.val (L h))
        (fun y => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ) n t y.val (U y))
        (∏ i, (x i : ℕ)) (frequencyRoot n t) := by
  let : ∀ i, Fact (x i : ℕ).Prime := fun i => ⟨hP _ (x i).property⟩
  let := scheduledInputPrimeFact role n r e (fun i => (x i : ℕ)) L U
  have hcp : Pairwise (fun i j => (x i : ℕ).Coprime (x j : ℕ)) := by
    intro i j hij
    apply (hP _ (x i).property).coprime_iff_not_dvd.mpr
    intro hd
    have he : (x i : ℕ) = (x j : ℕ) :=
      ((Nat.dvd_prime (hP _ (x j).property)).mp hd).resolve_left (hP _ (x i).property).ne_one
    exact hij (hx (Subtype.ext he))
  have h := scheduledInputPhase_factor_finite role χ κ pivot n r hpivot e t
    (fun i => (x i : ℕ)) L U center (pivot_retained_pairwise _ L U hcp hLU hM) hfreq
  simpa only [sampledScheduledPhase, primeTupleResidueRow, primeTuplePivotKey] using h

theorem scheduledCurrentAmplitude_eq_grouped_finite {I A Z : Type*}
    [Fintype I] [Fintype A] [Fintype Z]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (n r : ℕ)
    (hpivot : ∀ k ≤ n, role (pivot k) = .pivot k) (e : Fin r ≃ CurrentPivotConstituent role n) (hist : A → FrequencyTree ℤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : Fin r → Finset ℕ) (S : Finset (Fin r → P))
    (hS : ∀ x ∈ S, Function.Injective x)
    (L : A → CopyScheduleH role n → ℕ) (U : Z → CopyScheduleY role n → ℕ)
    [∀ a h, Fact (L a h).Prime] [∀ z y, Fact (U z y).Prime]
    (center : ∀ p : ℕ, ZMod p) (W : Z → ℕ → A → ℂ) (μ : Z → ℝ)
    (hsupport : ∀ z x, x ∈ S → ∀ a, W z (∏ i, (x i : ℕ)) a ≠ 0 →
      Pairwise (fun i j => (Sum.elim (L a) (U z) i).Coprime (Sum.elim (L a) (U z) j)) ∧
      (∏ i, (x i : ℕ)).Coprime ((∏ h, L a h) * ∏ y, U z y) ∧
      ∀ i, ∀ s ∈ allFrequencyList n (hist a), (s : ZMod (x i : ℕ)) ≠ 0) :
    scheduledCurrentAmplitude role χ κ pivot n r e hist P hP Q S L U center W μ =
    groupedDirectedAmplitude P hP Q S (fun i => χ (e i).val)
      (fun i p => κ (e i).val p) (fun _ => 1) L U center
      (fun h => χ (copyScheduleOrigin n h.val)) (fun y => χ (copyScheduleOrigin n y.val))
      (scheduledRetainedGraph role initialCompleteGraph pivot n)
      (fun _z a h => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
        n (hist a) h.val (L a h))
      (fun z a y => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
        n (hist a) y.val (U z y)) (fun a => frequencyRoot n (hist a)) W μ := by
  unfold scheduledCurrentAmplitude groupedDirectedAmplitude
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  by_cases hW : W z (∏ i, (x i : ℕ)) a = 0
  · simp only [hW, retainedWeightedCoefficient, zero_mul, mul_zero]
  obtain ⟨hc, hM, hf⟩ := hsupport z x hx a hW
  rw [sampledScheduledPhase_factor_finite role χ κ pivot n r hpivot e (hist a) P hP x
    (hS x hx) (L a) (U z) center hc hM hf]
  unfold retainedWeightedCoefficient
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FiniteArithmeticStep
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original-prior arithmetic transfer through a finite schedule -/
namespace Ostmann
open scoped BigOperators Classical

theorem scheduled_arithmetic_transfer_finite {I A Z : Type*}
    [Fintype I] [Fintype A] [Fintype Z]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (n r : ℕ)
    (hpivot : ∀ k ≤ n, role (pivot k) = .pivot k) (e : Fin r ≃ CurrentPivotConstituent role n) (hist : A → FrequencyTree ℤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hκ : ∀ i p, p ∈ P → ‖κ i p‖ ≤ 1)
    (Q : Fin r → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQ : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (S : Finset (Fin r → P)) (hS : ∀ x ∈ S, Function.Injective x)
    (T : Finset ℕ) (hT : ∀ M ∈ T, 0 < M) (hST : ∀ x ∈ S, (∏ i, (x i : ℕ)) ∈ T)
    (L : A → CopyScheduleH role n → ℕ) (U : Z → CopyScheduleY role n → ℕ)
    [∀ a h, Fact (L a h).Prime] [∀ z y, Fact (U z y).Prime]
    (center : ∀ p : ℕ, ZMod p) (W : Z → ℕ → A → ℂ) (μ : Z → ℝ)
    (hμ : ∀ z, 0 ≤ μ z) (hμsum : ∑ z, μ z ≤ 1)
    (B K V : ℕ)
    (hsupport : ∀ z M, M ∈ T → ∀ a, W z M a ≠ 0 →
      Pairwise (fun i j => (Sum.elim (L a) (U z) i).Coprime (Sum.elim (L a) (U z) j)) ∧
      M.Coprime ((∏ h, L a h) * ∏ y, U z y) ∧
      (frequencyRoot n (hist a)).natAbs ≤ B ∧ (∏ h, L a h) ≤ K)
    (hfreq : ∀ z x, x ∈ S → ∀ a, W z (∏ i, (x i : ℕ)) a ≠ 0 →
      ∀ i, ∀ s ∈ allFrequencyList n (hist a), (s : ZMod (x i : ℕ)) ≠ 0)
    (hscale : ∀ M ∈ T, 2 * B * K ≤ V * M)
    (hlargeL : ∀ a h, V < L a h) (hlargeU : ∀ z y, V < U z y)
    (d : ℝ) (hcost : ((r.factorial : ℝ) * ∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) ≤ Real.exp d) :
    Real.exp (-d) *
      ‖scheduledCurrentAmplitude role χ κ pivot n r e hist P hP Q S L U center W μ‖ ^ 2 ≤
      (∑ z, μ z * ∑ M ∈ T,
        (pivotDiagonal (fun a => ∏ h, L a h) (fun a => frequencyRoot n (hist a))
          (retainedWeightedCoefficient L (U z) center
            (fun h => χ (copyScheduleOrigin n h.val)) (fun y => χ (copyScheduleOrigin n y.val))
            (scheduledRetainedGraph role initialCompleteGraph pivot n)
            (fun a h => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
              n (hist a) h.val (L a h))
            (fun a y => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
              n (hist a) y.val (U z y))
            (fun a => frequencyRoot n (hist a)) (W z) M)).re) +
      ‖∑ z, (μ z : ℂ) * scheduledNextAmplitude role χ initialCompleteGraph pivot
        (initialRegularUnary χ κ) n hist L (U z) center (W z) T V‖ := by
  have hcurrent := scheduledCurrentAmplitude_eq_grouped_finite role χ κ pivot n r hpivot e hist
    P hP Q S hS L U center W μ (by
      intro z x hx a ha
      have hs := hsupport z _ (hST x hx) a ha
      exact ⟨hs.1, hs.2.1, hfreq z x hx a ha⟩)
  rw [hcurrent]
  have ht := original_directed_transfer P hP Q hQP hQ S hS T hT hST
    (fun i => χ (e i).val) (fun i p => κ (e i).val p)
    (fun i p => hκ (e i).val p p.property) (fun _ => 1) L U center
    (fun h => χ (copyScheduleOrigin n h.val)) (fun y => χ (copyScheduleOrigin n y.val))
    (scheduledRetainedGraph role initialCompleteGraph pivot n)
    (fun z a h => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
      n (hist a) h.val (L a h))
    (fun z a y => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
      n (hist a) y.val (U z y)) (fun a => frequencyRoot n (hist a)) W μ hμ hμsum
    B K V hsupport hscale hlargeL hlargeU
    (fun y => scheduledRetainedGraph_diagonal role pivot n (some (.inr y))) d hcost
  simpa only [copiedWeightedAmplitude_eq_scheduledNextAmplitude] using ht

theorem constituentPrimeGuardedAmplitude_step_finite {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (hpivot : ∀ k ≤ n, role (pivot k).1 = .pivot k) (p : I) (hp : role p = .pivot n) (hu : ∀ i, role i = .pivot n → i = p)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (hκ : ∀ i q, q ∈ P → ‖κ i q‖ ≤ 1)
    (hQP : ∀ i, Q i ⊆ P) (hQ : ∀ i, (∑ q ∈ Q i, (q : ℝ)⁻¹) ≠ 0)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (center : ∀ p : ℕ, ZMod p) (K V : ℕ) (T : Finset ℕ)
    (hST : ∀ x : Fin (size p) → P, Function.Injective x → (∀ i, (x i : ℕ) ∈ Q ⟨p, i⟩) → (∏ i, (x i : ℕ)) ∈ T)
    (hzero : ∀ x, fullAtomTransferWeight role childBound pivotBound ranges leaf 0 x (0 : ℤ) = 0)
    (hsmall : ∀ d s, s ∈ allFrequencyList n (hist d) → ∀ q ∈ P, s.natAbs < q)
    (hTpos : ∀ M ∈ T, 0 < M) (hTbound : ∀ M ∈ T, M ≤ pivotBound n)
    (hTfull : ∀ (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) d M, 0 < M → M ≤ pivotBound n →
      fullAtomTransferWeight role childBound pivotBound ranges leaf n
        (scheduledInsertedAtoms role n M
          (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
          (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) (hist d) ≠ 0 → M ∈ T)
    (hcut : ∀ u, ∀ M ∈ T, ∀ a,
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0 →
      (frequencyRoot n (hist a.2)).natAbs ≤ childBound n ∧ (∏ h, (a.1 h : ℕ)) ≤ K)
    (hscale : ∀ M ∈ T, 2 * childBound n * K ≤ V * M)
    (hlarge : ∀ q ∈ P, V < q)
    (hgap : ∀ u, ∀ M ∈ T, ∀ a a',
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0 →
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a' ≠ 0 →
      2 * pivotBound n * childBound n < ∏ h, (a'.1 h : ℕ))
    (hrange : ∀ u, ∀ M ∈ T, ∀ a a',
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0 →
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a' ≠ 0 →
      ∀ b ∈ ranges (n + 1), b.Holds (copiedConstituentAtomValues role size n P u a.1 a'.1))
    (loss : ℝ) (hcost : (((size p).factorial : ℝ) *
      ∏ i : Fin (size p), (∑ q ∈ Q ⟨p, i⟩, (q : ℝ)⁻¹)⁻¹) ≤ Real.exp loss) :
    Real.exp (-loss) *
      ‖constituentPrimeGuardedAmplitude role size χ κ pivot n P hP Q
        childBound pivotBound ranges leaf hist center‖ ^ 2 ≤
      (∑ u, (∏ y, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) (u y)) *
        ∑ M ∈ T, (constituentPivotDiagonal role size χ κ pivot n P hP Q
          childBound pivotBound ranges leaf hist center u M).re) +
      ‖constituentPrimeGuardedAmplitude role size χ κ pivot (n + 1) P hP Q
        childBound pivotBound ranges leaf (copiedConstituentHistory hist V) center‖ := by
  let ρ := fun i : Σ a, Fin (size a) => role i.1
  let : ∀ (a : (CopyScheduleH ρ n → P) × D) h, Fact (a.1 h : ℕ).Prime :=
    fun a h => ⟨hP _ (a.1 h).property⟩
  let : ∀ (u : CopyScheduleY ρ n → P) y, Fact (u y : ℕ).Prime :=
    fun u y => ⟨hP _ (u y).property⟩
  let μ (u : CopyScheduleY ρ n → P) :=
    ∏ y, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) (u y)
  have hμ (u) : 0 ≤ μ u := Finset.prod_nonneg (fun _ _ => primeSubsetPrior_nonneg _ _ _)
  have hμsum : ∑ u, μ u = 1 := by
    rw [← Fintype.prod_sum]
    have hm (y : CopyScheduleY ρ n) :
        (∑ q : P, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) q) = 1 :=
      primeSubsetPrior_mass P _ (hQP _) (hQ _)
    simp only [hm, Finset.prod_const_one]
  have ht := scheduled_arithmetic_transfer_finite ρ χ κ pivot n (size p) hpivot
    (pivotConstituentEquiv role size n p hp hu) (fun a => hist a.2) P hP hκ
    (fun k => Q ⟨p, k⟩) (fun k => hQP ⟨p, k⟩) (fun k => hQ ⟨p, k⟩)
    (supportedPivotTuples P (fun k => Q ⟨p, k⟩))
    (fun x hx => ((mem_supportedPivotTuples _ _ _).mp hx).1)
    T hTpos (fun x hx => hST x ((mem_supportedPivotTuples _ _ _).mp hx).1
      ((mem_supportedPivotTuples _ _ _).mp hx).2)
    (fun a h => (a.1 h : ℕ)) (fun u y => (u y : ℕ)) center
    (constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist)
    μ hμ hμsum.le (childBound n) K V (by
      intro u M hM a ha
      have hs := constituentTransferWeight_support role size n p hp P Q childBound pivotBound ranges leaf hist u M a ha
      exact ⟨hs.1, hs.2.1, (hcut u M hM a ha).1, (hcut u M hM a ha).2⟩) (by
      intro u x _ a ha i s hs
      let : Fact (x i : ℕ).Prime := ⟨hP _ (x i).property⟩
      exact constituentTransferWeight_frequency_unit role size n P Q childBound pivotBound ranges leaf hist
        hzero u (∏ i, (x i : ℕ)) a ha (x i) s hs (hsmall a.2 s hs _ (x i).property))
    hscale (fun a h => hlarge _ (a.1 h).property) (fun u y => hlarge _ (u y).property) loss hcost
  have hc := constituentPrimeGuardedAmplitude_eq_supported_transfer role size χ κ pivot n p hp hu
    P hP Q childBound pivotBound ranges leaf hist center
  have hn := constituentPrimeGuardedAmplitude_next role size χ κ pivot n p hp P hP Q
    childBound pivotBound ranges leaf hist center K V T hTpos hTbound hTfull
    hcut hscale hlarge hgap hrange
  rw [← hc, ← hn] at ht
  exact ht

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentAtomProductBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Whole-atom interval bounds on the actual transfer support

In particular the word atom retains its selected bin, even though its prime
constituents range over a much wider interval.
-/
namespace Ostmann
open scoped Classical BigOperators

theorem constituentTransferWeight_atom_product_bounds {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (P : Finset ℕ) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (lo hi : I → ℕ)
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D)
    (hw : constituentTransferWeight role size n P Q childBound pivotBound
      (atomIntervalRanges role lo hi) leaf hist u M a ≠ 0) :
    (∏ h : CopyScheduleH role n, lo (copyScheduleOrigin n h.val)) ≤
      (∏ h, (a.1 h : ℕ)) ∧
    (∏ h, (a.1 h : ℕ)) ≤
      ∏ h : CopyScheduleH role n, hi (copyScheduleOrigin n h.val) := by
  have hf := constituentTransferWeight_full_ne_zero role size n P Q childBound pivotBound
    (atomIntervalRanges role lo hi) leaf hist u M a hw
  have hr := (atomIntervalRanges_holds_iff role lo hi n _).mp
    (fun r hr => fullAtomTransferWeight_top_range role childBound pivotBound
      (atomIntervalRanges role lo hi) leaf n _ (hist a.2) hf r hr)
  have hh (h : CopyScheduleH role n) :
      lo (copyScheduleOrigin n h.val) ≤
        ∏ k, (a.1 (constituentH role size n h k) : ℕ) ∧
      (∏ k, (a.1 (constituentH role size n h k) : ℕ)) ≤ hi (copyScheduleOrigin n h.val) := by
    simpa only [scheduledInsertedAtoms_H] using hr ⟨h.val, h.property.1⟩
  rw [← constituentH_product role size n (fun h => (a.1 h : ℕ))]
  exact ⟨Finset.prod_le_prod' (fun h _ => (hh h).1),
    Finset.prod_le_prod' (fun h _ => (hh h).2)⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FiniteAtomIntervalStep
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite transfer using the selected whole-word intervals -/
namespace Ostmann
open scoped Classical BigOperators

theorem constituentPrimeGuardedAmplitude_atom_interval_step {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (hpivot : ∀ k ≤ n, role (pivot k).1 = .pivot k) (p : I) (hp : role p = .pivot n) (hu : ∀ i, role i = .pivot n → i = p)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (hκ : ∀ i q, q ∈ P → ‖κ i q‖ ≤ 1)
    (hQP : ∀ i, Q i ⊆ P) (hQ : ∀ i, (∑ q ∈ Q i, (q : ℝ)⁻¹) ≠ 0)
    (lo hi : I → ℕ) (cellLo cellHi : (Σ i, Fin (size i)) → ℕ)
    (hcell : ∀ i q, q ∈ Q i → cellLo i ≤ q ∧ q ≤ cellHi i)
    (childBound pivotBound : ℕ → ℕ) (leaf : ScheduleAtomState role → ℤ → ℂ)
    (hist : D → FrequencyTree ℤ n) (center : ∀ p : ℕ, ZMod p) (K V : ℕ)
    (hpLo : 0 < lo p) (hpHi : hi p ≤ pivotBound n)
    (hcellLo : lo p ≤ ∏ k : Fin (size p), cellLo ⟨p, k⟩)
    (hcellHi : (∏ k : Fin (size p), cellHi ⟨p, k⟩) ≤ hi p)
    (hroot : ∀ d, (frequencyRoot n (hist d)).natAbs ≤ childBound n)
    (hzero : ∀ x, fullAtomTransferWeight role childBound pivotBound
      (atomIntervalRanges role lo hi) leaf 0 x (0 : ℤ) = 0)
    (hsmall : ∀ d s, s ∈ allFrequencyList n (hist d) → ∀ q ∈ P, s.natAbs < q)
    (hK : (∏ h : CopyScheduleH role n, hi (copyScheduleOrigin n h.val)) ≤ K)
    (hgap : 2 * pivotBound n * childBound n <
      ∏ h : CopyScheduleH role n, lo (copyScheduleOrigin n h.val))
    (hscale : 2 * childBound n * K ≤ V * lo p) (hlarge : ∀ q ∈ P, V < q)
    (loss : ℝ) (hcost : (((size p).factorial : ℝ) *
      ∏ i : Fin (size p), (∑ q ∈ Q ⟨p, i⟩, (q : ℝ)⁻¹)⁻¹) ≤ Real.exp loss) :
    Real.exp (-loss) *
      ‖constituentPrimeGuardedAmplitude role size χ κ pivot n P hP Q
        childBound pivotBound (atomIntervalRanges role lo hi) leaf hist center‖ ^ 2 ≤
      (∑ u, (∏ y, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) (u y)) *
        ∑ M ∈ Finset.Icc (lo p) (hi p), (constituentPivotDiagonal role size χ κ pivot n P hP Q
          childBound pivotBound (atomIntervalRanges role lo hi) leaf hist center u M).re) +
      ‖constituentPrimeGuardedAmplitude role size χ κ pivot (n + 1) P hP Q
        childBound pivotBound (atomIntervalRanges role lo hi) leaf (copiedConstituentHistory hist V) center‖ := by
  apply constituentPrimeGuardedAmplitude_step_finite role size χ κ pivot n hpivot p hp hu P hP Q
    hκ hQP hQ childBound pivotBound (atomIntervalRanges role lo hi) leaf hist center K V
    (Finset.Icc (lo p) (hi p))
  · intro x _ hx
    apply Finset.mem_Icc.mpr
    exact ⟨hcellLo.trans (Finset.prod_le_prod' (fun i _ => (hcell _ _ (hx i)).1)),
      (Finset.prod_le_prod' (fun i _ => (hcell _ _ (hx i)).2)).trans hcellHi⟩
  · exact hzero
  · exact hsmall
  · intro M hM
    exact hpLo.trans_le (Finset.mem_Icc.mp hM).1
  · intro M hM
    exact (Finset.mem_Icc.mp hM).2.trans hpHi
  · intro u l d M _ _ hw
    exact Finset.mem_Icc.mpr (fullAtomTransferWeight_inserted_pivot_bounds role lo hi
      childBound pivotBound leaf n p hp M _ _ (hist d) hw)
  · intro u M _ a ha
    have hh := constituentTransferWeight_atom_product_bounds role size n P Q childBound pivotBound
      lo hi leaf hist u M a ha
    exact ⟨hroot a.2, hh.2.trans hK⟩
  · intro M hM
    exact hscale.trans (Nat.mul_le_mul_left V (Finset.mem_Icc.mp hM).1)
  · exact hlarge
  · intro u M _ a b _ hb
    have hh := constituentTransferWeight_atom_product_bounds role size n P Q childBound pivotBound
      lo hi leaf hist u M b hb
    exact hgap.trans_le hh.1
  · intro u M _ a b ha hb
    exact constituentTransferWeight_copied_intervals role size lo hi n P Q childBound pivotBound
      leaf hist u M a b ha hb
  · exact hcost

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FiniteAtomIntervalIteration
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-depth iteration with whole-word interval support -/
namespace Ostmann
open scoped BigOperators Classical

theorem scheduled_constituent_atom_interval_step {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (j : ℕ) (hpivot : ∀ k ≤ j, role (pivot k).1 = .pivot k) (p : I) (hp : role p = .pivot j) (hu : ∀ i, role i = .pivot j → i = p)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (hκ : ∀ i q, q ∈ P → ‖κ i q‖ ≤ 1)
    (hQP : ∀ i, Q i ⊆ P) (hQ : ∀ i, (∑ q ∈ Q i, (q : ℝ)⁻¹) ≠ 0)
    (lo hi : I → ℕ) (cellLo cellHi : (Σ i, Fin (size i)) → ℕ)
    (hcell : ∀ i q, q ∈ Q i → cellLo i ≤ q ∧ q ≤ cellHi i)
    (V pivotBound : ℕ → ℕ) (hV : Monotone V)
    (leaf : ScheduleAtomState role → ℤ → ℂ) (center : ∀ p : ℕ, ZMod p)
    (hpLo : 0 < lo p) (hpHi : hi p ≤ pivotBound j)
    (hcellLo : lo p ≤ ∏ t : Fin (size p), cellLo ⟨p, t⟩)
    (hcellHi : (∏ t : Fin (size p), cellHi ⟨p, t⟩) ≤ hi p)
    (hzero : ∀ x, fullAtomTransferWeight role V pivotBound
      (atomIntervalRanges role lo hi) leaf 0 x (0 : ℤ) = 0)
    (hgap : 2 * pivotBound j * V j <
      ∏ h : CopyScheduleH role j, lo (copyScheduleOrigin j h.val))
    (hscale : 2 * V j *
      (∏ h : CopyScheduleH role j, hi (copyScheduleOrigin j h.val))
        ≤ V (j + 1) * lo p)
    (hlarge : ∀ q ∈ P, V (j + 1) < q)
    (loss : ℝ) (hcost : (((size p).factorial : ℝ) *
      ∏ i : Fin (size p), (∑ q ∈ Q ⟨p, i⟩, (q : ℝ)⁻¹)⁻¹) ≤ Real.exp loss) :
    Real.exp (-loss) * ‖scheduledConstituentAmplitude role size χ κ pivot P hP Q lo hi
      V pivotBound leaf center j‖ ^ 2 ≤
      scheduledConstituentDiagonal role size χ κ pivot P hP Q lo hi V pivotBound leaf center p j +
        ‖scheduledConstituentAmplitude role size χ κ pivot P hP Q lo hi V pivotBound leaf center (j + 1)‖ := by
  apply constituentPrimeGuardedAmplitude_atom_interval_step role size χ κ pivot j hpivot p hp hu P hP Q
    hκ hQP hQ lo hi cellLo cellHi hcell V pivotBound leaf (scheduledFrequencyHistory V j)
    center _ (V (j + 1)) hpLo hpHi hcellLo hcellHi
  · exact scheduledFrequencyHistory_root_bound V j
  · exact hzero
  · intro d s hs q hq
    exact (scheduledFrequencyHistory_all_bound V hV j d s hs).trans_lt
      ((hV (Nat.le_succ j)).trans_lt (hlarge q hq))
  · exact le_rfl
  · exact hgap
  · exact hscale
  · exact hlarge
  · exact hcost

/-- The initial reserve survives every actual arithmetic step once the
explicit diagonals and the sum of the actual losses have been bounded. -/
theorem scheduled_constituent_atom_interval_iteration {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (k : ℕ) (hpivot : ∀ j < k, role (pivot j).1 = .pivot j) (p : ℕ → I)
    (hp : ∀ j < k, role (p j) = .pivot j)
    (hu : ∀ j < k, ∀ i, role i = .pivot j → i = p j)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (hκ : ∀ i q, q ∈ P → ‖κ i q‖ ≤ 1)
    (hQP : ∀ i, Q i ⊆ P) (hQ : ∀ i, (∑ q ∈ Q i, (q : ℝ)⁻¹) ≠ 0)
    (lo hi : I → ℕ) (cellLo cellHi : (Σ i, Fin (size i)) → ℕ)
    (hcell : ∀ i q, q ∈ Q i → cellLo i ≤ q ∧ q ≤ cellHi i)
    (V pivotBound : ℕ → ℕ) (hV : Monotone V)
    (leaf : ScheduleAtomState role → ℤ → ℂ) (center : ∀ p : ℕ, ZMod p)
    (hpLo : ∀ j < k, 0 < lo (p j))
    (hpHi : ∀ j < k, hi (p j) ≤ pivotBound j)
    (hcellLo : ∀ j < k, lo (p j) ≤ ∏ t : Fin (size (p j)), cellLo ⟨p j, t⟩)
    (hcellHi : ∀ j < k, (∏ t : Fin (size (p j)), cellHi ⟨p j, t⟩) ≤ hi (p j))
    (hzero : ∀ x, fullAtomTransferWeight role V pivotBound
      (atomIntervalRanges role lo hi) leaf 0 x (0 : ℤ) = 0)
    (hgap : ∀ j < k, 2 * pivotBound j * V j <
      ∏ h : CopyScheduleH role j, lo (copyScheduleOrigin j h.val))
    (hscale : ∀ j < k, 2 * V j *
      (∏ h : CopyScheduleH role j, hi (copyScheduleOrigin j h.val))
        ≤ V (j + 1) * lo (p j))
    (hlarge : ∀ q ∈ P, V k < q)
    (loss : ℕ → ℝ) (hloss : ∀ j < k, 0 ≤ loss j)
    (hcost : ∀ j < k, (((size (p j)).factorial : ℝ) *
      ∏ i : Fin (size (p j)), (∑ q ∈ Q ⟨p j, i⟩, (q : ℝ)⁻¹)⁻¹) ≤ Real.exp (loss j))
    (B₀ m : ℝ) (hm : 0 ≤ m)
    (hbudget : ∑ j ∈ Finset.range k, (loss j + Real.log 2) ≤ m)
    (hinit : Real.exp (-B₀ * m) ≤
      ‖scheduledConstituentAmplitude role size χ κ pivot P hP Q lo hi V pivotBound leaf center 0‖)
    (hdiag : ∀ j < k, scheduledConstituentDiagonal role size χ κ pivot P hP Q lo hi
      V pivotBound leaf center (p j) j ≤
        Real.exp (-(2 * (B₀ + 1) + 3) * (2 : ℝ) ^ j * m)) :
    Real.exp (-(B₀ + 1) * (2 : ℝ) ^ k * m) ≤
      ‖scheduledConstituentAmplitude role size χ κ pivot P hP Q lo hi V pivotBound leaf center k‖ := by
  apply variable_transfer_iteration k
    (scheduledConstituentAmplitude role size χ κ pivot P hP Q lo hi V pivotBound leaf center)
    (fun j => scheduledConstituentDiagonal role size χ κ pivot P hP Q lo hi
      V pivotBound leaf center (p j) j) loss B₀ m hm hloss hbudget hinit hdiag
    (fun j hj => ?_) k le_rfl
  exact scheduled_constituent_atom_interval_step role size χ κ pivot j
    (fun t ht => hpivot t (by omega)) (p j) (hp j hj)
    (hu j hj) P hP Q hκ hQP hQ lo hi cellLo cellHi hcell V pivotBound hV leaf center
    (hpLo j hj) (hpHi j hj) (hcellLo j hj) (hcellHi j hj) hzero (hgap j hj) (hscale j hj)
    (fun q hq => (hV (by omega : j + 1 ≤ k)).trans_lt (hlarge q hq)) (loss j) (hcost j hj)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_BackwardTargets
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The backwards pivot-target recurrence

For coefficients `c_j = 2^j J + a_j - Delta_j`, the pivot target is `c_j`
plus the sum of all later pivot targets. This constructs the recurrence,
rather than assuming that its simultaneous equations have a solution.
-/

namespace Ostmann

theorem backwardTargets_get (cs : List ℝ) (i : ℕ) (hi : i < cs.length) :
    (backwardTargets cs)[i]'(by rw [backwardTargets_length]; exact hi) =
      cs[i] + ((backwardTargets cs).drop (i + 1)).sum := by
  induction cs generalizing i with
  | nil => simp at hi
  | cons c cs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simpa only [backwardTargets, List.getElem_cons_succ, List.drop_succ_cons] using
        ih i (by simpa using hi)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PivotTargetScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive pivot targets at the required logarithmic scale -/

namespace Ostmann

theorem pivotTargets_recurrence (k : ℕ) (J : ℝ) (a Δ : Fin k → ℝ) (i : Fin k) :
    (pivotTargets k J a Δ)[i.val]'(by
      simpa only [pivotTargets, backwardTargets_length, pivotCoefficients,
        List.length_ofFn] using i.isLt) =
      (2 : ℝ) ^ i.val * J + a i - Δ i +
        ((pivotTargets k J a Δ).drop (i.val + 1)).sum := by
  have hi : i.val < (pivotCoefficients k J a Δ).length := by
    simpa only [pivotCoefficients, List.length_ofFn] using i.isLt
  simpa [pivotTargets, pivotCoefficients] using
    backwardTargets_get (pivotCoefficients k J a Δ) i.val hi

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterScheduleRoles
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite role set used in the nonquadratic character argument

A positive word, finitely many pivot groups, two fresh anchors at each step,
and one filler have independent negative copies. Only the positive word,
pivots and anchors participate in the copy schedule.
-/
namespace Ostmann
open scoped Classical BigOperators

theorem characterPivotAtom_unique {k : ℕ} (j : Fin k) (v : CharacterRole k)
    (hv : characterRole k v = .pivot j.val) : v = characterPivotAtom j := by
  rcases v with ⟨b, c⟩
  cases b with
  | false => simp [characterRole, signedAtomRole] at hv
  | true =>
    cases c with
    | none => simp [characterRole, signedAtomRole, characterPositiveRole] at hv
    | some c =>
      rcases c with i | a | u
      · have hi : i = j := Fin.ext (CopyScheduleRole.pivot.inj hv)
        subst i
        rfl
      · simp [characterRole, signedAtomRole, characterPositiveRole] at hv
      · simp [characterRole, signedAtomRole, characterPositiveRole] at hv

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferGapRanges
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript's gaps give both frequency cutoffs and history rigidity -/

namespace Ostmann

open Filter
open scoped Topology

theorem transfer_gap_minus_error (Δ m : ℝ) (j : ℕ) :
    transferNextGap Δ m j - transferErrorScale Δ m j =
      2 * (4 : ℝ) ^ j * Real.sqrt m := by
  simp only [transferNextGap, transferErrorScale, pow_succ]
  ring

theorem transfer_error_reserve (Δ m : ℝ) (j : ℕ) :
    transferErrorScale Δ m (j + 1) -
        (transferErrorScale Δ m j + transferNextGap Δ m j) =
      2 * (4 : ℝ) ^ j * Real.sqrt m := by
  simp only [transferNextGap, transferErrorScale, pow_succ]
  ring

/-- A single sufficiently-large-m cutoff gives every transfer level its
fixed covering and integer-rounding reserve. -/
theorem eventually_transfer_reserve (C : ℝ) :
    ∀ᶠ m : ℝ in atTop, ∀ Δ : ℝ, ∀ j : ℕ,
      Real.log 4 + 2 * C < transferNextGap Δ m j - transferErrorScale Δ m j ∧
      Real.log 4 + 2 * C < transferErrorScale Δ m (j + 1) -
        (transferErrorScale Δ m j + transferNextGap Δ m j) := by
  filter_upwards [Real.tendsto_sqrt_atTop.eventually (eventually_gt_atTop
    ((Real.log 4 + 2 * C) / 2))] with m hm
  intro Δ j
  have hp : 1 ≤ (4 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hr := Real.sqrt_nonneg m
  have hh : Real.log 4 + 2 * C < 2 * (4 : ℝ) ^ j * Real.sqrt m := by nlinarith
  rw [transfer_gap_minus_error, transfer_error_reserve]
  exact ⟨hh, hh⟩

/-- The positive-product ranges make the determinant gap strict. -/
theorem transfer_integer_rigidity_gap (K B R : ℕ) (T Δ E C : ℝ)
    (hK : (K : ℝ) ≤ Real.exp (T + C)) (hB : (B : ℝ) ≤ Real.exp E)
    (hR : Real.exp (T + Δ - C) ≤ R) (hgap : Real.log 2 + 2 * C < Δ - E) :
    2 * K * B < R := by
  have h : (2 : ℝ) * K * B < R := by
    calc
      _ ≤ 2 * Real.exp (T + C) * Real.exp E := by gcongr
      _ = Real.exp (Real.log 2 + (T + C) + E) := by
        simp only [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ < Real.exp (T + Δ - C) := Real.exp_lt_exp.mpr (by linarith)
      _ ≤ R := hR
  exact_mod_cast h

/-- Rounding the new exponential frequency cutoff downward costs at most
one factor two, which is covered by the same square-root reserve. -/
theorem transfer_integer_frequency_cutoff (M H B V : ℕ) (T Δ E E' C : ℝ)
    (hM : Real.exp (T - C) ≤ M) (hH : (H : ℝ) ≤ Real.exp (T + Δ + C))
    (hB : (B : ℝ) ≤ Real.exp E) (hV : Real.exp E' ≤ 2 * V)
    (hgap : Real.log 4 + 2 * C + E + Δ ≤ E') :
    2 * B * H ≤ V * M := by
  have hhalf : Real.exp E' / 2 ≤ (V : ℝ) := by linarith
  have h : (2 : ℝ) * B * H ≤ V * M := by
    calc
      _ ≤ 2 * Real.exp E * Real.exp (T + Δ + C) := by gcongr
      _ = Real.exp (Real.log 2 + E + (T + Δ + C)) := by
        simp only [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ ≤ Real.exp (E' - Real.log 2 + (T - C)) := Real.exp_le_exp.mpr (by
        have hlog : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
          norm_num
        rw [hlog] at hgap
        linarith)
      _ = (Real.exp E' / 2) * Real.exp (T - C) := by
        rw [Real.exp_add, Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ ≤ V * M := mul_le_mul hhalf hM (Real.exp_pos _).le (Nat.cast_nonneg _)
  exact_mod_cast h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferRoundedCutoffs
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Natural cutoffs supplied by the transfer's exponential ranges -/

namespace Ostmann

open Filter
open scoped Topology

theorem natural_exp_cutoff_bounds (E : ℝ) (hE : Real.log 2 ≤ E) :
    0 < ⌊Real.exp E⌋₊ ∧ (⌊Real.exp E⌋₊ : ℝ) ≤ Real.exp E ∧
      Real.exp E ≤ 2 * (⌊Real.exp E⌋₊ : ℝ) := by
  have hexp : (2 : ℝ) ≤ Real.exp E := by
    calc
      _ = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp E := Real.exp_le_exp.mpr hE
  have hn : 1 ≤ ⌊Real.exp E⌋₊ := (Nat.one_le_floor_iff _).mpr (by linarith)
  have hnR : (1 : ℝ) ≤ ⌊Real.exp E⌋₊ := by exact_mod_cast hn
  exact ⟨hn, Nat.floor_le (Real.exp_pos _).le, by linarith [Nat.lt_floor_add_one (Real.exp E)]⟩

/-- The same explicit rounded cutoffs supply the strict determinant gap
and the next signed-frequency bound, at every transfer level. -/
theorem eventually_transfer_integer_ranges (C : ℝ) :
    ∀ᶠ m : ℝ in atTop, ∀ Δ : ℝ, 0 ≤ Δ → ∀ j : ℕ, ∀ T : ℝ,
      ∀ M R : ℕ,
      Real.exp (T - C) ≤ M → Real.exp (T + transferNextGap Δ m j - C) ≤ R →
      2 * naturalProductCap (T + C) * naturalTransferCutoff Δ m j < R ∧
      2 * naturalTransferCutoff Δ m j * naturalProductCap (T + transferNextGap Δ m j + C) ≤
        naturalTransferCutoff Δ m (j + 1) * M := by
  filter_upwards [eventually_transfer_reserve C,
    Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop (Real.log 2 / 2))] with m hm hsqrt
  intro Δ hΔ j T M R hM hR
  obtain ⟨hgap, hnext⟩ := hm Δ j
  have hlog : Real.log (2 : ℝ) ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
  have hfloor (x : ℝ) : (naturalProductCap x : ℝ) ≤ Real.exp x :=
    Nat.floor_le (Real.exp_pos _).le
  have hB : (naturalTransferCutoff Δ m j : ℝ) ≤ Real.exp (transferErrorScale Δ m j) :=
    Nat.floor_le (Real.exp_pos _).le
  have hE : Real.log 2 ≤ transferErrorScale Δ m (j + 1) := by
    have hp : 1 ≤ (4 : ℝ) ^ (j + 1) := one_le_pow₀ (by norm_num)
    have hD : 0 ≤ (2 : ℝ) ^ (j + 1) * Δ := mul_nonneg (by positivity) hΔ
    have hs0 := Real.sqrt_nonneg m
    unfold transferErrorScale
    nlinarith
  have hV := (natural_exp_cutoff_bounds (transferErrorScale Δ m (j + 1)) hE).2.2
  constructor
  · exact transfer_integer_rigidity_gap _ _ R T (transferNextGap Δ m j)
      (transferErrorScale Δ m j) C (hfloor _) hB hR (by linarith)
  · exact transfer_integer_frequency_cutoff M _ _ _ T (transferNextGap Δ m j)
      (transferErrorScale Δ m j) (transferErrorScale Δ m (j + 1)) C hM (hfloor _) hB hV
      (by linarith)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledFrequencyBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete rounded frequency family and its finite counting cost -/

namespace Ostmann

open scoped BigOperators Classical

theorem transferErrorScale_monotone (Δ m : ℝ) (hΔ : 0 ≤ Δ) : Monotone (transferErrorScale Δ m) := by
  apply monotone_nat_of_le_succ
  intro n
  have h2 : 0 ≤ (2 : ℝ) ^ n * Δ := mul_nonneg (by positivity) hΔ
  have h4 : 0 ≤ (4 : ℝ) ^ n * Real.sqrt m := mul_nonneg (by positivity) (Real.sqrt_nonneg m)
  simp only [transferErrorScale, pow_succ]
  nlinarith

theorem naturalTransferCutoff_monotone (Δ m : ℝ) (hΔ : 0 ≤ Δ) :
    Monotone (naturalTransferCutoff Δ m) := by
  intro a b hab
  exact Nat.floor_le_floor (Real.exp_le_exp.mpr (transferErrorScale_monotone Δ m hΔ hab))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RoundedScheduleRanges
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rounded exponential bounds for the actual active and copied products -/

namespace Ostmann

open Filter
open scoped Topology BigOperators

/-- The interval step's two integer inequalities follow from the original
logarithmic product ranges with one uniform large-parameter threshold. -/
theorem eventually_rounded_schedule_ranges (C : ℝ) :
    ∀ᶠ m : ℝ in atTop, ∀ Δ : ℝ, 0 ≤ Δ → ∀ j : ℕ, ∀ T : ℝ,
      ∀ M B L K : ℕ,
      Real.exp (T - C) ≤ M → B ≤ naturalProductCap (T + C) →
      Real.exp (T + transferNextGap Δ m j - C) ≤ L →
      K ≤ naturalProductCap (T + transferNextGap Δ m j + C) →
      2 * B * naturalTransferCutoff Δ m j < L ∧
      2 * naturalTransferCutoff Δ m j * K ≤ naturalTransferCutoff Δ m (j + 1) * M := by
  filter_upwards [eventually_transfer_integer_ranges C] with m hm
  intro Δ hΔ j T M B L K hM hB hL hK
  obtain ⟨hg, hs⟩ := hm Δ hΔ j T M L hM hL
  exact ⟨(Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hB)).trans_lt hg,
    (Nat.mul_le_mul_left _ hK).trans hs⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterHBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Product bounds retain the complete selected word bins -/
namespace Ostmann
open scoped Classical BigOperators
open Filter

theorem character_H_card_le {k n : ℕ} (hn : n < k) :
    Fintype.card (CopyScheduleH (characterRole k) n) ≤ 2 ^ n + k + 2 := by
  rw [← Fintype.card_congr (characterHEquiv hn)]
  change Fintype.card ((Fin n → Bool) ⊕ ({j : Fin k // n < j.val} ⊕ Bool)) ≤ _
  simp only [Fintype.card_sum, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have h := Fintype.card_subtype_le (fun j : Fin k => n < j.val)
  simp only [Fintype.card_fin] at h
  omega

theorem character_H_sum {k n : ℕ} (hn : n < k) (w : CharacterRole k → ℝ) :
    (∑ h : CopyScheduleH (characterRole k) n, w (copyScheduleOrigin n h.val)) =
      (2 : ℝ) ^ n * w (true, none) +
        ((∑ j : {j : Fin k // n < j.val}, w (characterPivotAtom j.val)) +
          ∑ b : Bool, w (characterAnchorAtom ⟨n, hn⟩ b)) := by
  rw [← (characterHEquiv hn).sum_comp]
  change (∑ x : CharacterHIndex k n,
    w (copyScheduleOrigin n (characterHCoordinate hn x).val)) = _
  simp only [characterHCoordinate_origin, Fintype.sum_sum_type, Finset.sum_const,
    Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

/-- A bounded error per selected atom costs only a constant depending on the
fixed depth, not on the number of primes in the word. -/
theorem character_H_product_bounds {k n : ℕ} (hn : n < k)
    (w : CharacterRole k → ℝ) (lo hi : CharacterRole k → ℕ)
    (c : ℝ) (hc : 0 ≤ c)
    (hlo : ∀ i, Real.exp (w i - c) ≤ lo i)
    (hhi : ∀ i, (hi i : ℝ) ≤ Real.exp (w i + c)) :
    let T := (2 : ℝ) ^ n * w (true, none) +
      ((∑ j : {j : Fin k // n < j.val}, w (characterPivotAtom j.val)) +
        ∑ b : Bool, w (characterAnchorAtom ⟨n, hn⟩ b))
    let C := ((2 : ℝ) ^ k + k + 2) * c
    Real.exp (T - C) ≤
      (∏ h : CopyScheduleH (characterRole k) n, lo (copyScheduleOrigin n h.val) : ℕ) ∧
    (∏ h : CopyScheduleH (characterRole k) n, hi (copyScheduleOrigin n h.val) : ℕ) ≤
      Real.exp (T + C) := by
  intro T C
  have hcard : (Fintype.card (CopyScheduleH (characterRole k) n) : ℝ) ≤
      (2 : ℝ) ^ k + k + 2 := by
    have h : (Fintype.card (CopyScheduleH (characterRole k) n) : ℝ) ≤
        (2 : ℝ) ^ n + k + 2 := by exact_mod_cast character_H_card_le hn
    have hp : (2 : ℝ) ^ n ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hn.le
    linarith
  have hcost := mul_le_mul_of_nonneg_right hcard hc
  have hsum : (∑ h : CopyScheduleH (characterRole k) n,
      w (copyScheduleOrigin n h.val)) = T := character_H_sum hn w
  constructor
  · calc
      Real.exp (T - C) ≤ Real.exp (T - Fintype.card (CopyScheduleH (characterRole k) n) * c) :=
        Real.exp_le_exp.mpr (by dsimp [C] at hcost ⊢; linarith)
      _ = ∏ h : CopyScheduleH (characterRole k) n, Real.exp (w (copyScheduleOrigin n h.val) - c) := by
        rw [← Real.exp_sum, Finset.sum_sub_distrib, hsum]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ _ := by
        rw [Nat.cast_prod]
        exact Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le) (fun i _ => hlo _)
  · calc
      _ ≤ ∏ h : CopyScheduleH (characterRole k) n, Real.exp (w (copyScheduleOrigin n h.val) + c) := by
        rw [Nat.cast_prod]
        exact Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i _ => hhi _)
      _ = Real.exp (T + Fintype.card (CopyScheduleH (characterRole k) n) * c) := by
        rw [← Real.exp_sum, Finset.sum_add_distrib, hsum]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ Real.exp (T + C) := Real.exp_le_exp.mpr (by dsimp [C] at hcost ⊢; linarith)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterTargetCenters
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual backwards targets give the copied block's exact center -/
namespace Ostmann
open scoped Classical BigOperators

private theorem sum_drop_eq_sum_later (s : List ℝ) (k : ℕ) (hlen : s.length = k) (n : ℕ) :
    (s.drop (n + 1)).sum =
      ∑ j : {j : Fin k // n < j.val}, s[j.val.val]'(by rw [hlen]; exact j.val.isLt) := by
  let e : Fin (s.drop (n + 1)).length ≃ {j : Fin k // n < j.val} :=
    { toFun := fun i => ⟨⟨n + 1 + i.val, by
        have hi := i.isLt
        simp only [List.length_drop, hlen] at hi
        omega⟩, by change n < n + 1 + i.val; omega⟩
      invFun := fun j => ⟨j.val.val - (n + 1), by
        simp only [List.length_drop, hlen]
        have hj := j.val.isLt
        have hn := j.property
        omega⟩
      left_inv := by intro i; apply Fin.ext; dsimp; omega
      right_inv := by intro j; apply Subtype.ext; apply Fin.ext; dsimp; have := j.property; omega }
  have hsum : (∑ i : Fin (s.drop (n + 1)).length, (s.drop (n + 1))[i.val]) =
      (s.drop (n + 1)).sum := by
    rw [← List.sum_ofFn, List.ofFn_getElem]
  rw [← hsum]
  apply Fintype.sum_equiv e
  intro i
  simp only [List.getElem_drop]
  rfl

theorem characterPivotTarget_future (k : ℕ) (J : ℝ) (a Δ : Fin k → ℝ) (n : ℕ) :
    ((pivotTargets k J a Δ).drop (n + 1)).sum =
      ∑ j : {j : Fin k // n < j.val}, characterPivotTarget k J a Δ j.val :=
  sum_drop_eq_sum_later _ k (by simp [pivotTargets, backwardTargets_length, pivotCoefficients]) n

/-- This is the equality log H = T_j + Delta_j used by the transfer.
It follows from the constructed backwards targets, not a range assumption. -/
theorem character_H_target_center {k n : ℕ} (hn : n < k) (J B z m F : ℝ)
    (a : Fin k → Bool → ℝ) :
    let Δ := fun j : Fin k => characterPivotGap B z m j.val
    let A := fun j => a j false + a j true
    let T := characterPivotTarget k J A Δ
    (∑ h : CopyScheduleH (characterRole k) n,
      characterLogCenter J T a F (copyScheduleOrigin n h.val)) =
        T ⟨n, hn⟩ + characterPivotGap B z m n := by
  intro Δ A T
  rw [character_H_sum hn]
  simp only [characterLogCenter, characterPivotAtom, characterAnchorAtom, Fintype.sum_bool]
  have ht := pivotTargets_recurrence k J A Δ ⟨n, hn⟩
  rw [characterPivotTarget_future] at ht
  change T ⟨n, hn⟩ = (2 : ℝ) ^ n * J + (a ⟨n, hn⟩ false + a ⟨n, hn⟩ true) -
    characterPivotGap B z m n + ∑ j : {j : Fin k // n < j.val}, T j.val at ht
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterIntervalGeometry
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The constructed character targets satisfy the two integer transfer inequalities -/
namespace Ostmann
open scoped Classical BigOperators
open Filter

/-- The threshold is uniform in the selected word bin, anchors and target
centers. Only the fixed depth and bounded cell errors enter it. -/
theorem eventual_character_interval_geometry (k : ℕ) (B z c : ℝ)
    (hB : 0 ≤ B) (hz : 1 ≤ z) (hc : 0 ≤ c) :
    ∀ᶠ m : ℝ in atTop, ∀ J : ℝ, ∀ a : Fin k → Bool → ℝ, ∀ F : ℝ,
    let Δ := fun j : Fin k => characterPivotGap B z m j.val
    let A := fun j => a j false + a j true
    let T := characterPivotTarget k J A Δ
    let w := characterLogCenter J T a F
    let C := characterRangeError k c
    ∀ lo hi : CharacterRole k → ℕ,
    (∀ i, Real.exp (w i - c) ≤ lo i) →
    (∀ i, (hi i : ℝ) ≤ Real.exp (w i + c)) →
    ∀ (n : ℕ) (hn : n < k),
      0 < lo (characterPivotAtom ⟨n, hn⟩) ∧
      hi (characterPivotAtom ⟨n, hn⟩) ≤ naturalProductCap (T ⟨n, hn⟩ + C) ∧
      2 * naturalProductCap (T ⟨n, hn⟩ + C) *
        naturalTransferCutoff (characterBaseGap B z m) m n <
          ∏ h : CopyScheduleH (characterRole k) n, lo (copyScheduleOrigin n h.val) ∧
      2 * naturalTransferCutoff (characterBaseGap B z m) m n *
          (∏ h : CopyScheduleH (characterRole k) n, hi (copyScheduleOrigin n h.val)) ≤
        naturalTransferCutoff (characterBaseGap B z m) m (n + 1) *
          lo (characterPivotAtom ⟨n, hn⟩) := by
  filter_upwards [eventually_rounded_schedule_ranges (characterRangeError k c),
    eventually_ge_atTop (0 : ℝ)] with m hm hm0
  intro J a F Δ A T w C lo hi hlo hhi n hn
  have hcC : c ≤ C := by
    have hp : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hh : 1 ≤ (2 : ℝ) ^ k + k + 2 := by
      have hk := Nat.cast_nonneg (α := ℝ) k
      linarith
    have hmul := mul_le_mul_of_nonneg_right hh hc
    change c ≤ ((2 : ℝ) ^ k + k + 2) * c
    simpa only [one_mul] using hmul
  have hcenter : (∑ h : CopyScheduleH (characterRole k) n,
      w (copyScheduleOrigin n h.val)) = T ⟨n, hn⟩ + characterPivotGap B z m n :=
    character_H_target_center hn J B z m F a
  have hproducts := character_H_product_bounds hn w lo hi c hc hlo hhi
  change Real.exp (_ - C) ≤ _ ∧ _ ≤ Real.exp (_ + C) at hproducts
  rw [← character_H_sum hn w, hcenter] at hproducts
  have hM : Real.exp (T ⟨n, hn⟩ - C) ≤ lo (characterPivotAtom ⟨n, hn⟩) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) (hlo (characterPivotAtom ⟨n, hn⟩))
    change T ⟨n, hn⟩ - C ≤ T ⟨n, hn⟩ - c
    linarith
  have hpivot : hi (characterPivotAtom ⟨n, hn⟩) ≤ naturalProductCap (T ⟨n, hn⟩ + C) := by
    apply Nat.le_floor
    exact (hhi (characterPivotAtom ⟨n, hn⟩)).trans
      (Real.exp_le_exp.mpr (by change T ⟨n, hn⟩ + c ≤ T ⟨n, hn⟩ + C; linarith))
  have hΔ : 0 ≤ characterBaseGap B z m :=
    mul_nonneg (add_nonneg hB (mul_nonneg (by norm_num) (Real.log_nonneg hz))) hm0
  have hL : Real.exp (T ⟨n, hn⟩ + transferNextGap (characterBaseGap B z m) m n - C) ≤
      (∏ h : CopyScheduleH (characterRole k) n, lo (copyScheduleOrigin n h.val) : ℕ) :=
    hproducts.1
  have hK : (∏ h : CopyScheduleH (characterRole k) n, hi (copyScheduleOrigin n h.val)) ≤
      naturalProductCap (T ⟨n, hn⟩ + transferNextGap (characterBaseGap B z m) m n + C) :=
    Nat.le_floor hproducts.2
  have hgeometry := hm (characterBaseGap B z m) hΔ n (T ⟨n, hn⟩ + 0)
    (lo (characterPivotAtom ⟨n, hn⟩)) (naturalProductCap (T ⟨n, hn⟩ + C))
    (∏ h : CopyScheduleH (characterRole k) n, lo (copyScheduleOrigin n h.val))
    (∏ h : CopyScheduleH (characterRole k) n, hi (copyScheduleOrigin n h.val))
    (by simpa only [add_zero] using hM) (by simp only [add_zero]; exact le_rfl)
    (by simpa only [add_zero] using hL) (by simpa only [add_zero] using hK)
  have hpos : 0 < lo (characterPivotAtom ⟨n, hn⟩) := by
    exact_mod_cast (Real.exp_pos _).trans_le hM
  exact ⟨hpos, hpivot, hgeometry.1, hgeometry.2⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterDiagonalGap
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original whole-word product pays the diagonal endpoint count -/
namespace Ostmann
open scoped Classical BigOperators

/-- Extract the reciprocal H product before summing the extended pivot.
The loss is only twice the fixed covering error. -/
theorem character_diagonal_product_gap {k n : ℕ} (hn : n < k)
    (J B z m F c : ℝ) (hc : 0 ≤ c) (a : Fin k → Bool → ℝ)
    (lo hi : CharacterRole k → ℕ)
    (hlo : ∀ i, Real.exp (characterLogCenter J
      (characterPivotTarget k J (fun j => a j false + a j true)
        (fun j => characterPivotGap B z m j.val)) a F i - c) ≤ lo i)
    (hhi : ∀ i, (hi i : ℝ) ≤ Real.exp (characterLogCenter J
      (characterPivotTarget k J (fun j => a j false + a j true)
        (fun j => characterPivotGap B z m j.val)) a F i + c)) :
    let T := characterPivotTarget k J (fun j => a j false + a j true)
      (fun j => characterPivotGap B z m j.val)
    let C := characterRangeError k c
    Real.exp (characterPivotGap B z m n - 2 * C) *
        (naturalProductCap (T ⟨n, hn⟩ + C) : ℝ) ≤
      ∏ h : CopyScheduleH (characterRole k) n, (lo (copyScheduleOrigin n h.val) : ℝ) := by
  intro T C
  let w := characterLogCenter J T a F
  have hp := (character_H_product_bounds hn w lo hi c hc hlo hhi).1
  change Real.exp (_ - C) ≤ _ at hp
  rw [← character_H_sum hn w, character_H_target_center hn J B z m F a] at hp
  rw [← Nat.cast_prod]
  apply le_trans _ hp
  calc
    _ ≤ Real.exp (characterPivotGap B z m n - 2 * C) * Real.exp (T ⟨n, hn⟩ + C) :=
      mul_le_mul_of_nonneg_left (Nat.floor_le (Real.exp_pos _).le) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterWordIntervals
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer word-bin endpoints have the same bounded errors as selected cells -/
namespace Ostmann
open scoped Classical

theorem initialWordAtomLower_word_gt_one {C : Type*} (j : ℕ) (hj : 0 < j)
    (lo : C → ℕ) (b : Bool) : 1 < initialWordAtomLower j lo (b, none) := by
  have he : (1 : ℝ) < Real.exp (j : ℝ) := Real.one_lt_exp_iff.mpr (by exact_mod_cast hj)
  have hh := he.trans_le (Nat.le_ceil (Real.exp (j : ℝ)))
  change 1 < ⌈Real.exp (j : ℝ)⌉₊
  exact_mod_cast hh

theorem character_word_interval_errors {k : ℕ} (j : ℕ) (c : ℝ) (hc : 1 ≤ c)
    (T : Fin k → ℝ) (a : Fin k → Bool → ℝ) (F : ℝ)
    (lo hi : CharacterCell k → ℕ)
    (hlo : ∀ v, Real.exp (characterLogCenter j T a F (true, some v) - c) ≤ lo v)
    (hhi : ∀ v, (hi v : ℝ) ≤ Real.exp (characterLogCenter j T a F (true, some v) + c)) :
    (∀ v, Real.exp (characterLogCenter j T a F v - c) ≤ initialWordAtomLower j lo v) ∧
    ∀ v, (initialWordAtomUpper j hi v : ℝ) ≤ Real.exp (characterLogCenter j T a F v + c) := by
  constructor
  · rintro ⟨b, v⟩
    cases v with
    | none =>
      change Real.exp ((j : ℝ) - c) ≤ (⌈Real.exp (j : ℝ)⌉₊ : ℝ)
      exact (Real.exp_le_exp.mpr (by linarith)).trans (Nat.le_ceil _)
    | some v => exact hlo v
  · rintro ⟨b, v⟩
    cases v with
    | none =>
      change ((⌈Real.exp ((j : ℝ) + 1)⌉₊ - 1 : ℕ) : ℝ) ≤ Real.exp ((j : ℝ) + c)
      have hp : 1 ≤ ⌈Real.exp ((j : ℝ) + 1)⌉₊ :=
        Nat.ceil_pos.mpr (Real.exp_pos _)
      rw [Nat.cast_sub hp, Nat.cast_one]
      have hh := Nat.ceil_lt_add_one (Real.exp_pos ((j : ℝ) + 1)).le
      apply le_trans (by linarith : (⌈Real.exp ((j : ℝ) + 1)⌉₊ : ℝ) - 1 ≤
        Real.exp ((j : ℝ) + 1))
      exact Real.exp_le_exp.mpr (by linarith)
    | some v => exact hhi v

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterWordGeometry
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original word bin and selected cell endpoints supply every transfer gap -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem eventual_character_word_geometry (k : ℕ) (B z c : ℝ)
    (hB : 0 ≤ B) (hz : 1 ≤ z) (hc : 1 ≤ c) :
    ∀ᶠ m : ℝ in atTop, ∀ J : ℕ, ∀ a : Fin k → Bool → ℝ, ∀ F : ℝ,
    let T := characterPivotTarget k J (fun j => a j false + a j true)
      (fun j => characterPivotGap B z m j.val)
    let C := characterRangeError k c
    ∀ cl ch : CharacterCell k → ℕ,
    (∀ v, Real.exp (characterLogCenter J T a F (true, some v) - c) ≤ cl v) →
    (∀ v, (ch v : ℝ) ≤ Real.exp (characterLogCenter J T a F (true, some v) + c)) →
    let lo := initialWordAtomLower J cl
    let hi := initialWordAtomUpper J ch
    ∀ (n : ℕ) (hn : n < k),
      0 < lo (characterPivotAtom ⟨n, hn⟩) ∧
      hi (characterPivotAtom ⟨n, hn⟩) ≤ naturalProductCap (T ⟨n, hn⟩ + C) ∧
      2 * naturalProductCap (T ⟨n, hn⟩ + C) *
        naturalTransferCutoff (characterBaseGap B z m) m n <
          ∏ h : CopyScheduleH (characterRole k) n, lo (copyScheduleOrigin n h.val) ∧
      2 * naturalTransferCutoff (characterBaseGap B z m) m n *
          (∏ h : CopyScheduleH (characterRole k) n, hi (copyScheduleOrigin n h.val)) ≤
        naturalTransferCutoff (characterBaseGap B z m) m (n + 1) *
          lo (characterPivotAtom ⟨n, hn⟩) ∧
      Real.exp (characterPivotGap B z m n - 2 * C) *
          (naturalProductCap (T ⟨n, hn⟩ + C) : ℝ) ≤
        ∏ h : CopyScheduleH (characterRole k) n, (lo (copyScheduleOrigin n h.val) : ℝ) := by
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  filter_upwards [eventual_character_interval_geometry k B z c hB hz hc0] with m hm
  intro J a F T C cl ch hlo hhi lo hi n hn
  have he := character_word_interval_errors J c hc T a F cl ch hlo hhi
  have hg := hm J a F lo hi he.1 he.2 n hn
  exact ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2,
    character_diagonal_product_gap hn J B z m F c hc0 a lo hi he.1 he.2⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PivotLossBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual factorial and harmonic-mass loss in the transfer iteration -/

namespace Ostmann

open scoped BigOperators Classical
open Filter

theorem pivotLogLoss_nonneg (n : ℕ) (C L : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L) :
    0 ≤ pivotLogLoss n C L := by
  have hn : (1 : ℝ) ≤ n.factorial := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n)
  exact add_nonneg (Real.log_nonneg hn) (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC) hL)

theorem harmonic_pivot_loss_le {n : ℕ} (Q : Fin n → Finset ℕ) (C L : ℝ)
    (hmass : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (C * L)) :
    ((n.factorial : ℝ) * ∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) ≤
      Real.exp (pivotLogLoss n C L) := by
  have hprod : (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) ≤ Real.exp ((n : ℝ) * C * L) := by
    calc
      _ ≤ ∏ _i : Fin n, Real.exp (C * L) :=
        Finset.prod_le_prod (fun _ _ => by positivity) (fun i _ => hmass i)
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          ← Real.exp_nat_mul]; congr 1; ring
  calc
    _ ≤ (n.factorial : ℝ) * Real.exp ((n : ℝ) * C * L) :=
      mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)
    _ = _ := by
      rw [pivotLogLoss, Real.exp_add, Real.exp_log (by exact_mod_cast Nat.factorial_pos n)]

/-- For fixed depth the factorial terms are constants in L. The selected
cell-role budget leaves enough room for all Cauchy losses and floor rounding. -/
theorem eventual_pivot_loss_budget (k : ℕ) (r : Fin k → ℕ) (C z : ℝ)
    (hC : 0 ≤ C) (hz : 0 < z) (hsmall : C * (∑ j, (r j : ℝ)) ≤ z / 4) :
    ∀ᶠ L : ℝ in atTop,
      (∀ j, 0 ≤ pivotLogLoss (r j) C L) ∧
      (∑ j, (pivotLogLoss (r j) C L + Real.log 2)) ≤ (⌊z * L⌋₊ : ℝ) := by
  let F := ∑ j, (Real.log ((r j).factorial : ℝ) + Real.log 2)
  filter_upwards [eventually_ge_atTop (max 0 (max (4 * F / z) (2 / z)))] with L hL
  have hL0 : 0 ≤ L := (le_max_left _ _).trans hL
  have hF : 4 * F / z ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have htwo : 2 / z ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hFL : F ≤ z * L / 4 := by
    have hh := (div_le_iff₀ hz).mp hF
    nlinarith
  have hzL : 2 ≤ z * L := by
    have hh := (div_le_iff₀ hz).mp htwo
    nlinarith
  refine ⟨fun j => pivotLogLoss_nonneg (r j) C L hC hL0, ?_⟩
  have hs : (∑ j, (pivotLogLoss (r j) C L + Real.log 2)) =
      C * (∑ j, (r j : ℝ)) * L + F := by
    dsimp [pivotLogLoss, F]
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
    ring
  rw [hs]
  have hc := mul_le_mul_of_nonneg_right hsmall hL0
  have hfloor := Nat.lt_floor_add_one (z * L)
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialGapRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Choosing the initial gap without changing the endpoint rate -/

namespace Ostmann

open Filter
open scoped BigOperators

theorem eventually_bulkCount (z : ℝ) (hz : 0 < z) (F : ℕ → Prop)
    (hF : ∀ᶠ m : ℕ in atTop, F m) :
    ∀ᶠ L : ℝ in atTop, F ⌊z * L⌋₊ := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp hF
  filter_upwards [eventually_ge_atTop ((M : ℝ) / z)] with L hL
  apply hM
  apply Nat.le_floor
  simpa only [mul_comm] using (div_le_iff₀ hz).mp hL

theorem eventually_bulkCount_bounds (z : ℝ) (hz : 0 < z) :
    ∀ᶠ L : ℝ in atTop, 0 < L ∧ 1 ≤ ⌊z * L⌋₊ ∧
      (⌊z * L⌋₊ : ℝ) ≤ z * L ∧ z * L ≤ 2 * ⌊z * L⌋₊ := by
  filter_upwards [eventually_ge_atTop (2 / z)] with L hL
  have h₂ : (2 : ℝ) ≤ z * L := by simpa only [mul_comm] using (div_le_iff₀ hz).mp hL
  have hLp : 0 < L := (div_pos (by norm_num : (0 : ℝ) < 2) hz).trans_le hL
  have hm : 1 ≤ ⌊z * L⌋₊ := (Nat.one_le_floor_iff (z * L)).mpr (by linarith)
  have hm' : (1 : ℝ) ≤ ⌊z * L⌋₊ := by exact_mod_cast hm
  exact ⟨hLp, hm, Nat.floor_le (by positivity), by linarith [Nat.lt_floor_add_one (z * L)]⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_InitialIntervalZero
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A nontrivial original interval removes the initial zero frequency -/
namespace Ostmann
open scoped Classical

theorem fullAtomTransferWeight_zero_of_interval {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (lo hi : I → ℕ)
    (childBound pivotBound : ℕ → ℕ) (leaf : ScheduleAtomState role → ℤ → ℂ)
    (i : I) (hi₁ : 1 < lo i) (x : CopyScheduleAtoms role 0 → ℕ) :
    fullAtomTransferWeight role childBound pivotBound (atomIntervalRanges role lo hi)
      leaf 0 x (0 : ℤ) = 0 := by
  by_contra h
  have hu := (fullAtomTransferWeight_top_support role childBound pivotBound
    (atomIntervalRanges role lo hi) leaf 0 x (0 : ℤ) h).2 ⟨i, trivial⟩
  have he : x ⟨i, trivial⟩ = 1 := by
    simpa only [frequencyRoot, Int.natAbs_zero, Nat.coprime_zero_right] using hu
  have hr := (atomIntervalRanges_holds_iff role lo hi 0 x).mp
    (fun r hr => fullAtomTransferWeight_top_range role childBound pivotBound
      (atomIntervalRanges role lo hi) leaf 0 x (0 : ℤ) h r hr)
  have hl := (hr ⟨i, trivial⟩).1
  change lo i ≤ x ⟨i, trivial⟩ at hl
  omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterAtomIteration
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Iteration with the selected word bin and actual character cell products -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- The transfer geometry and all pivot losses are derived from the chosen
cell endpoints. The remaining diagonal premise is the literal matching sum
estimated separately by the selected-bulk energy and cancellation theorems. -/
theorem eventual_character_atom_iteration_oai (k : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (hr : ∀ j, 0 < r j) (B B₀ z c Cmass : ℝ)
    (hB : 0 ≤ B) (hz : 1 ≤ z) (hc : 1 ≤ c) (hCmass : 0 ≤ Cmass)
    (hbudget : Cmass * (∑ j, (r j : ℝ)) ≤ z / 4) :
    ∀ᶠ L : ℝ in atTop,
    let m := ⌊z * L⌋₊
    ∀ (J : ℕ), 0 < J → ∀ (a : Fin k → Bool → ℝ) (F : ℝ),
    let T := characterPivotTarget k J (fun j => a j false + a j true)
      (fun j => characterPivotGap B z m j.val)
    let V := naturalTransferCutoff (characterBaseGap B z m) m
    let cap := characterPivotCap T (characterRangeError k c)
    ∀ (cellLo cellHi : (Σ v, Fin (characterSize m r f v)) → ℕ),
    let lo := initialWordAtomLower J (fun v => ∏ i, cellLo ⟨(true, some v), i⟩)
    let hi := initialWordAtomUpper J (fun v => ∏ i, cellHi ⟨(true, some v), i⟩)
    ∀ (χ : (Σ v, Fin (characterSize m r f v)) → ∀ p : ℕ, DirichletCharacter ℂ p)
      (κ : (Σ v, Fin (characterSize m r f v)) → ℕ → ℂ)
      (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
      (Q : (Σ v, Fin (characterSize m r f v)) → Finset ℕ)
      (leaf : ScheduleAtomState (characterRole k) → ℤ → ℂ) (center : ∀ p : ℕ, ZMod p),
    (∀ i q, q ∈ P → ‖κ i q‖ ≤ 1) →
    (∀ i, Q i ⊆ P) → (∀ i, (∑ q ∈ Q i, (q : ℝ)⁻¹) ≠ 0) →
    (∀ i q, q ∈ Q i → cellLo i ≤ q ∧ q ≤ cellHi i) →
    (∀ v, Real.exp (characterLogCenter J T a F (true, some v) - c) ≤
      ∏ i, cellLo ⟨(true, some v), i⟩) →
    (∀ v, (∏ i, cellHi ⟨(true, some v), i⟩ : ℕ) ≤
      Real.exp (characterLogCenter J T a F (true, some v) + c)) →
    (∀ j : Fin k, ∀ i : Fin (r j),
      (∑ q ∈ Q ⟨characterPivotAtom j, i⟩, (q : ℝ)⁻¹)⁻¹ ≤ Real.exp (Cmass * L)) →
    (∀ q ∈ P, V k < q) →
    (Real.exp (-B₀ * m) ≤ ‖scheduledConstituentAmplitude (characterRole k)
      (characterSize m r f) χ κ (characterPivot m r f hr) P hP Q lo hi V cap leaf center 0‖) →
    (∀ j < k, scheduledConstituentDiagonal (characterRole k) (characterSize m r f) χ κ
      (characterPivot m r f hr) P hP Q lo hi V cap leaf center (characterPivotRole k j) j ≤
        Real.exp (-(2 * (B₀ + 1) + 3) * (2 : ℝ) ^ j * m)) →
    Real.exp (-(B₀ + 1) * (2 : ℝ) ^ k * m) ≤
      ‖scheduledConstituentAmplitude (characterRole k) (characterSize m r f) χ κ
        (characterPivot m r f hr) P hP Q lo hi V cap leaf center k‖ := by
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have hg := eventually_bulkCount z hz0 _
    ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventual_character_word_geometry k B z c hB hz hc))
  filter_upwards [hg, eventual_pivot_loss_budget k r Cmass z hCmass hz0 hbudget,
    eventually_bulkCount_bounds z hz0] with L hgeom hloss hmbounds
  intro m J hJ a F T V cap cellLo cellHi lo hi χ κ P hP Q leaf center
    hκ hQP hQ hcell hlo hhi hmass hlarge hinit hdiag
  have hgeometry := hgeom J a F
    (fun v => ∏ i, cellLo ⟨(true, some v), i⟩)
    (fun v => ∏ i, cellHi ⟨(true, some v), i⟩) hlo hhi
  have hnonneg : 0 ≤ characterBaseGap B z m :=
    mul_nonneg (add_nonneg hB (mul_nonneg (by norm_num) (Real.log_nonneg hz)))
      (Nat.cast_nonneg m)
  have hV : Monotone V := naturalTransferCutoff_monotone _ _ hnonneg
  let loss : ℕ → ℝ := fun j => if h : j < k then pivotLogLoss (r ⟨j, h⟩) Cmass L else 0
  have hloss_eq (j : ℕ) (hj : j < k) : loss j = pivotLogLoss (r ⟨j, hj⟩) Cmass L := by
    simp only [loss, dite_eq_left hj]
  apply scheduled_constituent_atom_interval_iteration (loss := loss) (B₀ := B₀) (m := (m : ℝ)) (characterRole k) (characterSize m r f)
    χ κ (characterPivot m r f hr) k (characterPivot_role m r f hr) (characterPivotRole k)
    (fun j hj => by simp [hj]) (fun j hj v hv => by
      rw [characterPivotRole_eq hj]
      exact characterPivotAtom_unique ⟨j, hj⟩ v hv)
    P hP Q hκ hQP hQ lo hi cellLo cellHi hcell V cap hV leaf center
  · intro j hj
    simpa only [characterPivotRole_eq hj] using (hgeometry j hj).1
  · intro j hj
    simpa only [cap, T, characterPivotRole_eq hj, characterPivotCap_eq hj] using (hgeometry j hj).2.1
  · intro j hj
    rw [characterPivotRole_eq hj]
    exact le_rfl
  · intro j hj
    rw [characterPivotRole_eq hj]
    exact le_rfl
  · exact fullAtomTransferWeight_zero_of_interval (characterRole k) lo hi V cap leaf
      (true, none) (initialWordAtomLower_word_gt_one J hJ _ true)
  · intro j hj
    simpa only [cap, T, V, characterPivotCap_eq hj] using (hgeometry j hj).2.2.1
  · intro j hj
    simpa only [characterPivotRole_eq hj] using (hgeometry j hj).2.2.2.1
  · exact hlarge
  · intro j hj
    rw [hloss_eq j hj]
    exact hloss.1 ⟨j, hj⟩
  · intro j hj
    rw [hloss_eq j hj, characterPivotRole_eq hj]
    exact harmonic_pivot_loss_le (fun i => Q ⟨characterPivotAtom ⟨j, hj⟩, i⟩)
      Cmass L (hmass ⟨j, hj⟩)
  · exact Nat.cast_nonneg m
  · have he : (∑ j ∈ Finset.range k, (loss j + Real.log 2)) =
        ∑ j : Fin k, (pivotLogLoss (r j) Cmass L + Real.log 2) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j _
      rw [hloss_eq j.val j.isLt]
    rw [he]
    exact hloss.2
  · exact hinit
  · exact hdiag

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.eventual_character_atom_iteration_oai := @OAI.Ostmann.eventual_character_atom_iteration_oai
