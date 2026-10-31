-- Prove2me | solution 1 for OAI.Ostmann.eventual_character_anchor_decay
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:37:08.397139+00:00
-- url     : https://prove2.me/submissions/d3454254-2ff5-4b3e-b20f-11c3d45706c6

import Mathlib
import Definitions.Def_OAIQ095D006
import Definitions.Def_OAIQ095D007

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrequencyTreeSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing internal frequencies from the root downwards -/

namespace Ostmann

open scoped BigOperators

theorem frequencyTreeWeight_nonneg {A : Type} (K : A → A → A → ℝ) (W : A → ℝ)
    (hK : ∀ a b c, 0 ≤ K a b c) (hW : ∀ a, 0 ≤ W a)
    (n : ℕ) (x : FrequencyTree A n) : 0 ≤ frequencyTreeWeight K W n x := by
  induction n with
  | zero => exact hW x
  | succ n ih => exact mul_nonneg (mul_nonneg (hK _ _ _) (ih x.2.1)) (ih x.2.2)

/-- Each pair of parent frequencies is summed before either child pair.
Only the leaf mass remains after all internal frequencies are eliminated. -/
theorem frequencyTree_sum_le {A : Type} [Fintype A]
    (K : A → A → A → ℝ) (W : A → ℝ) (C : ℝ)
    (hK : ∀ a b c, 0 ≤ K a b c) (hW : ∀ a, 0 ≤ W a) (hC : 0 ≤ C)
    (hsum : ∀ b c, ∑ a : A, K a b c ≤ C) (n : ℕ) :
    (∑ x : FrequencyTree A n, frequencyTreeWeight K W n x) ≤
      C ^ (2 ^ n - 1) * (∑ a : A, W a) ^ (2 ^ n) := by
  induction n with
  | zero => simp [FrequencyTree, frequencyTreeWeight]
  | succ n ih =>
    have hweight := frequencyTreeWeight_nonneg K W hK hW n
    have hsum0 : 0 ≤ ∑ x : FrequencyTree A n, frequencyTreeWeight K W n x :=
      Finset.sum_nonneg fun x _ => hweight x
    have hbound0 : 0 ≤ C ^ (2 ^ n - 1) * (∑ a : A, W a) ^ (2 ^ n) :=
      mul_nonneg (pow_nonneg hC _) (pow_nonneg (Finset.sum_nonneg fun a _ => hW a) _)
    change (∑ x : A × FrequencyTree A n × FrequencyTree A n,
      K x.1 (frequencyRoot n x.2.1) (frequencyRoot n x.2.2) *
        frequencyTreeWeight K W n x.2.1 * frequencyTreeWeight K W n x.2.2) ≤ _
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    calc
      _ = ∑ x : FrequencyTree A n, ∑ y : FrequencyTree A n,
          (∑ a : A, K a (frequencyRoot n x) (frequencyRoot n y)) *
            frequencyTreeWeight K W n x * frequencyTreeWeight K W n y := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y _
        simp only [Finset.sum_mul]
      _ ≤ ∑ x : FrequencyTree A n, ∑ y : FrequencyTree A n,
          C * frequencyTreeWeight K W n x * frequencyTreeWeight K W n y := by
        exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hsum _ _) (hweight x)) (hweight y)
      _ = C * ((∑ x : FrequencyTree A n, frequencyTreeWeight K W n x) *
          (∑ y : FrequencyTree A n, frequencyTreeWeight K W n y)) := by
        simp only [← Finset.mul_sum, ← Finset.sum_mul]
        ring
      _ ≤ C * ((C ^ (2 ^ n - 1) * (∑ a : A, W a) ^ (2 ^ n)) *
          (C ^ (2 ^ n - 1) * (∑ a : A, W a) ^ (2 ^ n))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul ih ih hsum0 hbound0) hC
      _ = _ := by
        have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by omega
        have hone : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        have hnodes : 2 ^ (n + 1) - 1 = (2 ^ n - 1) + (2 ^ n - 1) + 1 := by omega
        rw [hnodes, hpow, pow_add, pow_add, pow_add, pow_one]
        ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ReducedFrequencySum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multiplicity of the reduced frequency modulus -/

namespace Ostmann

open scoped BigOperators

theorem reducedFrequency_mul_gcd (g s : ℕ) : reducedFrequency g s * s.gcd g = s :=
  Nat.div_mul_cancel (Nat.gcd_dvd_left s g)

theorem reducedFrequency_mem {N g s : ℕ} (hs : s ∈ Finset.Icc 1 N) :
    reducedFrequency g s ∈ Finset.Icc 1 N := by
  obtain ⟨hs₀, hsN⟩ := Finset.mem_Icc.mp hs
  have hg := Nat.gcd_pos_of_pos_left g (show 0 < s from hs₀)
  exact Finset.mem_Icc.mpr ⟨Nat.div_pos
    (Nat.le_of_dvd hs₀ (Nat.gcd_dvd_left s g)) hg, (Nat.div_le_self _ _).trans hsN⟩

/-- A fixed reduced modulus has at most one frequency for each divisor
of the gcd of the two child frequencies. -/
theorem reducedFrequency_fiber_card_le (N g a : ℕ) (hg : g ≠ 0) :
    ((Finset.Icc 1 N).filter fun s => reducedFrequency g s = a).card ≤ g.divisors.card := by
  apply Finset.card_le_card_of_injOn (fun s => s.gcd g)
  · intro s _
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right s g, hg⟩
  · intro s hs t ht heq
    change s.gcd g = t.gcd g at heq
    have hsa := (Finset.mem_filter.mp hs).2
    have hta := (Finset.mem_filter.mp ht).2
    calc
      s = reducedFrequency g s * s.gcd g := (reducedFrequency_mul_gcd g s).symm
      _ = reducedFrequency g t * t.gcd g := by rw [hsa, hta, heq]
      _ = t := reducedFrequency_mul_gcd g t

theorem sum_reducedFrequency_le (N g : ℕ) (hg : g ≠ 0)
    (F : ℕ → ℝ) (hF : ∀ a ∈ Finset.Icc 1 N, 0 ≤ F a) :
    (∑ s ∈ Finset.Icc 1 N, F (reducedFrequency g s)) ≤
      g.divisors.card * ∑ a ∈ Finset.Icc 1 N, F a := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun s hs => reducedFrequency_mem (g := g) hs)
    (fun s => F (reducedFrequency g s))]
  calc
    _ ≤ ∑ a ∈ Finset.Icc 1 N, (g.divisors.card : ℝ) * F a := by
      apply Finset.sum_le_sum
      intro a ha
      have heq : (∑ s ∈ (Finset.Icc 1 N).filter (fun s => reducedFrequency g s = a),
          F (reducedFrequency g s)) =
          (((Finset.Icc 1 N).filter (fun s => reducedFrequency g s = a)).card : ℝ) * F a := by
        calc
          _ = ∑ _s ∈ (Finset.Icc 1 N).filter (fun s => reducedFrequency g s = a), F a :=
            Finset.sum_congr rfl fun _ hs => congrArg F (Finset.mem_filter.mp hs).2
          _ = _ := by simp
      rw [heq]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast reducedFrequency_fiber_card_le N g a hg)
        (hF a ha)
    _ = _ := (Finset.mul_sum _ _ _).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SignedFrequencySum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Both signs in the internal-frequency sum -/

namespace Ostmann

open scoped BigOperators Classical

theorem natAbs_fiber_card_le_two (S : Finset ℤ) (a : ℕ) :
    (S.filter fun s => s.natAbs = a).card ≤ 2 := by
  have hsub : (S.filter fun s => s.natAbs = a) ⊆ {(a : ℤ), -(a : ℤ)} := by
    intro s hs
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      (Int.natAbs_eq_iff.mp (Finset.mem_filter.mp hs).2)
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_insert_le _ _).trans_eq (by simp))

theorem sum_signed_magnitudes_le (S : Finset ℤ) (N : ℕ)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (F : ℕ → ℝ) (hF : ∀ a ∈ Finset.Icc 1 N, 0 ≤ F a) :
    (∑ s ∈ S, F s.natAbs) ≤ 2 * ∑ a ∈ Finset.Icc 1 N, F a := by
  have hmem (s : ℤ) (hs : s ∈ S) : s.natAbs ∈ Finset.Icc 1 N :=
    Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr
      (Int.natAbs_ne_zero.mpr (hS s hs).1), (hS s hs).2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmem (fun s => F s.natAbs)]
  calc
    _ ≤ ∑ a ∈ Finset.Icc 1 N, 2 * F a := by
      apply Finset.sum_le_sum
      intro a ha
      have heq : (∑ s ∈ S.filter (fun s => s.natAbs = a), F s.natAbs) =
          ((S.filter (fun s => s.natAbs = a)).card : ℝ) * F a := by
        calc
          _ = ∑ _s ∈ S.filter (fun s => s.natAbs = a), F a :=
            Finset.sum_congr rfl fun _ hs => congrArg F (Finset.mem_filter.mp hs).2
          _ = _ := by simp
      rw [heq]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast natAbs_fiber_card_le_two S a) (hF a ha)
    _ = _ := (Finset.mul_sum _ _ _).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SequentialSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multiplying support bounds under the original independent prior

The test at a split can depend on the entire already exposed prefix. This
records the order of exposure, so future validity never changes its law.
-/

namespace Ostmann

open scoped BigOperators Classical

theorem sequentialSupport_nonneg {A : Type} (test : List A → A → Prop)
    (past : List A) (n : ℕ) (x : SplitSamples A n) :
    0 ≤ sequentialSupport test past n x := by
  induction n generalizing past with
  | zero => exact zero_le_one
  | succ n ih =>
    change 0 ≤ if test past x.1 then sequentialSupport test (x.1 :: past) n x.2 else 0
    split_ifs
    · exact ih _ _
    · exact le_rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SequentialProductSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Distinct frequency bounds at successive exposed splits -/

namespace Ostmann

open scoped BigOperators Classical

theorem sequentialSupport_average_le_product {A : Type} [Fintype A] [Nonempty A]
    (test : List A → A → Prop) (ρ : ℕ → ℝ) (hρ : ∀ i, 0 ≤ ρ i)
    (htest : ∀ past, (Fintype.card A : ℝ)⁻¹ *
      (∑ x : A, if test past x then (1 : ℝ) else 0) ≤ ρ past.length)
    (past : List A) (n : ℕ) :
    (Fintype.card A : ℝ)⁻¹ ^ n *
        (∑ x : SplitSamples A n, sequentialSupport test past n x) ≤
      ∏ i ∈ Finset.range n, ρ (past.length + i) := by
  induction n generalizing past with
  | zero => simp [sequentialSupport, SplitSamples]
  | succ n ih =>
    let B := ∏ i ∈ Finset.range n, ρ (past.length + 1 + i)
    have hB : 0 ≤ B := Finset.prod_nonneg fun i _ => hρ _
    have htail (a : A) : (Fintype.card A : ℝ)⁻¹ ^ n *
        (∑ x : SplitSamples A n, sequentialSupport test (a :: past) n x) ≤ B := by
      simpa only [List.length_cons, B] using ih (a :: past)
    change (Fintype.card A : ℝ)⁻¹ ^ (n + 1) *
      (∑ x : A × SplitSamples A n,
        if test past x.1 then sequentialSupport test (x.1 :: past) n x.2 else 0) ≤ _
    rw [Fintype.sum_prod_type, pow_succ]
    have heq : (∑ a : A, ∑ x : SplitSamples A n,
        if test past a then sequentialSupport test (a :: past) n x else 0) =
        ∑ a : A, (if test past a then (1 : ℝ) else 0) *
          (∑ x : SplitSamples A n, sequentialSupport test (a :: past) n x) := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : test past a <;> simp [ha]
    rw [heq]
    calc
      _ = (Fintype.card A : ℝ)⁻¹ *
          ∑ a : A, (if test past a then (1 : ℝ) else 0) *
            ((Fintype.card A : ℝ)⁻¹ ^ n *
              (∑ x : SplitSamples A n, sequentialSupport test (a :: past) n x)) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ ≤ (Fintype.card A : ℝ)⁻¹ *
          ∑ a : A, (if test past a then (1 : ℝ) else 0) * B := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
        exact Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (htail a) (by split_ifs <;> norm_num)
      _ = ((Fintype.card A : ℝ)⁻¹ *
          ∑ a : A, if test past a then (1 : ℝ) else 0) * B := by
        rw [← Finset.sum_mul, mul_assoc]
      _ ≤ ρ past.length * B := mul_le_mul_of_nonneg_right (htest past) hB
      _ = _ := by
        rw [Finset.prod_range_succ']
        simp only [Nat.add_zero]
        rw [mul_comm (ρ past.length)]
        dsimp [B]
        congr 1
        apply Finset.prod_congr rfl
        intro i _
        congr 1
        omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SquareCongruence
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Square congruences in the frequency support -/

namespace Ostmann

open scoped BigOperators Classical

theorem cyclic_square_fiber_card_le {G : Type*} [CommGroup G] [Fintype G]
    [IsCyclic G] (a : G) : Nat.card {x : G // x ^ 2 = a} ≤ 2 := by
  classical
  rw [Nat.card_eq_fintype_card]
  by_cases h : ∃ r : G, r ^ 2 = a
  · obtain ⟨r, rfl⟩ := h
    rw [Fintype.card_congr (squareFiberEquivOne r)]
    simpa only [Fintype.card_subtype] using (IsCyclic.card_pow_eq_one_le (α := G) (by decide : 0 < 2))
  · have hi : IsEmpty {x : G // x ^ 2 = a} := ⟨fun x => h ⟨x, x.property⟩⟩
    rw [Fintype.card_of_isEmpty]
    omega

/-- The odd-prime-power part of the manuscript's square-root bound follows
from Mathlib's proved cyclicity of the unit group. -/
theorem odd_prime_power_square_fiber_card_le (p n : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (a : (ZMod (p ^ n))ˣ) :
    Nat.card {x : (ZMod (p ^ n))ˣ // x ^ 2 = a} ≤ 2 := by
  let _ : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let _ : IsCyclic (ZMod (p ^ n))ˣ :=
    ZMod.isCyclic_units_of_prime_pow p Fact.out hp2 n
  exact cyclic_square_fiber_card_le a

theorem crt_square_fiber_card {I : Type*} [Fintype I]
    (q : I → ℕ) [∀ i, NeZero (q i)] [NeZero (∏ i, q i)]
    (hc : Pairwise (fun i j => (q i).Coprime (q j))) (a : (ZMod (∏ i, q i))ˣ) :
    Nat.card {x : (ZMod (∏ i, q i))ˣ // x ^ 2 = a} =
      ∏ i, Nat.card {x : (ZMod (q i))ˣ // x ^ 2 = crtUnitEquiv q hc a i} := by
  rw [Nat.card_congr (crtSquareFiberEquiv q hc a)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_pi]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_SquareKernelIndex
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Square-root counts from a cyclic subgroup of small index -/

namespace Ostmann

open scoped BigOperators Classical

private theorem cosetSquareInjection_injective {G : Type*} [CommGroup G]
    (H : Subgroup G) (r : G) (hr : r ^ 2 = 1) :
    Function.Injective (cosetSquareInjection H r hr) := by
  intro x y h
  apply Subtype.ext
  have hv := congrArg (fun z : {x : H // x ^ 2 = 1} => ((z.val : H) : G)) h
  change x.val / r = y.val / r at hv
  exact (div_left_inj).mp hv

/-- Each quotient class contains at most two square roots of one when the
subgroup is cyclic. This will supply the factor four at powers of two. -/
theorem square_kernel_card_le_two_index {G : Type*} [CommGroup G] [Fintype G]
    (H : Subgroup G) [IsCyclic H] :
    Nat.card {x : G // x ^ 2 = 1} ≤ 2 * Nat.card (G ⧸ H) := by
  let : Fintype (G ⧸ H) := Fintype.ofFinite _
  let S : Finset G := Finset.univ.filter fun x => x ^ 2 = 1
  have hf (q : G ⧸ H) : (S.filter (fun x : G => (x : G ⧸ H) = q)).card ≤ 2 := by
    by_cases hex : ∃ r : G, r ^ 2 = 1 ∧ (r : G ⧸ H) = q
    · obtain ⟨r, hr, rfl⟩ := hex
      have hbound := Fintype.card_le_of_injective (cosetSquareInjection H r hr)
        (cosetSquareInjection_injective H r hr)
      have heq : (S.filter fun x : G => (x : G ⧸ H) = (r : G ⧸ H)).card =
          Fintype.card {x : G // x ^ 2 = 1 ∧ (x : G ⧸ H) = (r : G ⧸ H)} := by
        simp only [Fintype.card_subtype, S, Finset.filter_filter]
      rw [heq]
      exact hbound.trans (by simpa only [Nat.card_eq_fintype_card] using
        cyclic_square_fiber_card_le (1 : H))
    · have he : S.filter (fun x : G => (x : G ⧸ H) = q) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        obtain ⟨hxS, hxq⟩ := Finset.mem_filter.mp hx
        exact hex ⟨x, (Finset.mem_filter.mp hxS).2, hxq⟩
      simp [he]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  change S.card ≤ _
  rw [Finset.card_eq_sum_card_fiberwise (t := Finset.univ)
    (f := fun x : G => (x : G ⧸ H)) (fun _ _ => Finset.mem_univ _)]
  calc
    _ ≤ ∑ _q : G ⧸ H, 2 := Finset.sum_le_sum fun q _ => hf q
    _ = _ := by simp [Nat.card_eq_fintype_card, mul_comm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_TwoPowerSquares
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The factor four for square roots modulo powers of two -/

namespace Ostmann

open scoped BigOperators Classical

theorem two_power_square_kernel_card_le (n : ℕ) :
    Nat.card {x : (ZMod (2 ^ n))ˣ // x ^ 2 = 1} ≤ 4 := by
  rcases n with _ | _ | n
  · let _ : IsCyclic (ZMod (2 ^ 0))ˣ := (ZMod.isCyclic_units_two_pow_iff 0).mpr (by decide)
    have h := cyclic_square_fiber_card_le (1 : (ZMod (2 ^ 0))ˣ)
    exact h.trans (by omega)
  · let _ : IsCyclic (ZMod (2 ^ 1))ˣ := (ZMod.isCyclic_units_two_pow_iff 1).mpr (by decide)
    have h := cyclic_square_fiber_card_le (1 : (ZMod (2 ^ 1))ˣ)
    exact h.trans (by omega)
  let G := (ZMod (2 ^ (n + 2)))ˣ
  have hu : IsUnit (5 : ZMod (2 ^ (n + 2))) := by
    exact (ZMod.isUnit_iff_coprime 5 _).mpr ((by decide : Nat.Coprime 5 2).pow_right _)
  let u : G := hu.unit
  let H : Subgroup G := Subgroup.zpowers u
  have ho : orderOf u = 2 ^ n := by
    rw [← orderOf_injective _ Units.coeHom_injective u, Units.coeHom_apply]
    change orderOf (hu.unit : ZMod (2 ^ (n + 2))) = 2 ^ n
    rw [IsUnit.unit_spec]
    exact ZMod.orderOf_five n
  have hH : Nat.card H = 2 ^ n := by
    change Nat.card (Subgroup.zpowers u) = _
    rw [Nat.card_zpowers, ho]
  have hG : Nat.card G = 2 ^ (n + 1) := by
    change Nat.card (ZMod (2 ^ (n + 2)))ˣ = _
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    simpa only [Nat.add_assoc, Nat.reduceAdd, Nat.reduceSub, mul_one]
      using Nat.totient_prime_pow_succ Nat.prime_two (n + 1)
  have hQ : Nat.card (G ⧸ H) = 2 := by
    have he := H.card_eq_card_quotient_mul_card_subgroup
    rw [hH, hG] at he
    apply Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ n)
    calc
      _ = 2 ^ (n + 1) := he.symm
      _ = 2 * 2 ^ n := by rw [pow_succ, mul_comm]
  have hbound := square_kernel_card_le_two_index H
  rw [hQ] at hbound
  exact hbound

theorem two_power_square_fiber_card_le (n : ℕ) (a : (ZMod (2 ^ n))ˣ) :
    Nat.card {x : (ZMod (2 ^ n))ˣ // x ^ 2 = a} ≤ 4 := by
  by_cases h : ∃ r : (ZMod (2 ^ n))ˣ, r ^ 2 = a
  · obtain ⟨r, rfl⟩ := h
    rw [Nat.card_congr (squareFiberEquivOne r)]
    exact two_power_square_kernel_card_le n
  · have hi : IsEmpty {x : (ZMod (2 ^ n))ˣ // x ^ 2 = a} := ⟨fun x => h ⟨x, x.property⟩⟩
    simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_PrimePowerSquares
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The simultaneous square-root budget over all prime-power factors -/

namespace Ostmann

open scoped BigOperators Classical

theorem prime_power_square_fiber_card_le (p n : ℕ) [Fact p.Prime]
    (a : (ZMod (p ^ n))ˣ) :
    Nat.card {x : (ZMod (p ^ n))ˣ // x ^ 2 = a} ≤ if p = 2 then 4 else 2 := by
  split_ifs with hp
  · subst p
    exact two_power_square_fiber_card_le n a
  · exact odd_prime_power_square_fiber_card_le p n hp a

theorem distinct_primes_square_budget {I : Type*} [Fintype I]
    (p : I → ℕ) (hp : Function.Injective p) :
    (∏ i, if p i = 2 then 4 else 2) ≤ 2 ^ (Fintype.card I + 1) := by
  by_cases htwo : ∃ i, p i = 2
  · obtain ⟨i, hi⟩ := htwo
    have hcard : 1 ≤ Fintype.card I := Fintype.card_pos_iff.mpr ⟨i⟩
    have hrest : (∏ j ∈ (Finset.univ : Finset I).erase i, if p j = 2 then 4 else 2) =
        2 ^ (Fintype.card I - 1) := by
      calc
        _ = ∏ _j ∈ (Finset.univ : Finset I).erase i, 2 := by
          apply Finset.prod_congr rfl
          intro j hj
          have hji := (Finset.mem_erase.mp hj).1
          have hj2 : p j ≠ 2 := fun hj2 => hji (hp (hj2.trans hi.symm))
          simp only [hj2, ↓reduceIte]
        _ = _ := by simp
    rw [← Finset.prod_erase_mul (Finset.univ : Finset I)
      (fun j => if p j = 2 then 4 else 2) (Finset.mem_univ i), hi, ite_eq_left rfl, hrest]
    have hexp : Fintype.card I - 1 + 2 = Fintype.card I + 1 := by omega
    calc
      _ = 2 ^ (Fintype.card I - 1 + 2) := by rw [pow_add]; norm_num
      _ ≤ _ := le_of_eq (by rw [hexp])
  · have hnone : ∀ i, p i ≠ 2 := by simpa using htwo
    simp only [hnone, ↓reduceIte, Finset.prod_const, Finset.card_univ]
    rw [pow_succ]
    omega

/-- For a modulus presented as a product of distinct prime powers, every
unit square has at most `2^(number of primes + 1)` roots. -/
theorem prime_powers_square_fiber_card_le {I : Type*} [Fintype I]
    (p n : I → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (p i ^ n i)]
    [NeZero (∏ i, p i ^ n i)] (hp : Function.Injective p)
    (hc : Pairwise (fun i j => (p i ^ n i).Coprime (p j ^ n j)))
    (a : (ZMod (∏ i, p i ^ n i))ˣ) :
    Nat.card {x : (ZMod (∏ i, p i ^ n i))ˣ // x ^ 2 = a} ≤
      2 ^ (Fintype.card I + 1) := by
  rw [crt_square_fiber_card (fun i => p i ^ n i) hc a]
  calc
    _ ≤ ∏ i, if p i = 2 then 4 else 2 := Finset.prod_le_prod' fun i _ =>
      prime_power_square_fiber_card_le (p i) (n i) _
    _ ≤ _ := distinct_primes_square_budget p hp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_UnitSquareRoots
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Square roots of units modulo the actual frequency modulus -/

namespace Ostmann

open scoped BigOperators Classical

theorem unit_square_fiber_card_le (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) :
    Nat.card {x : (ZMod q)ˣ // x ^ 2 = a} ≤ 2 ^ (q.primeFactors.card + 1) := by
  let I := q.primeFactors
  let p : I → ℕ := fun i => i
  let n : I → ℕ := fun i => q.factorization i
  let _ : ∀ i, Fact (p i).Prime := fun i => ⟨Nat.prime_of_mem_primeFactors i.property⟩
  let _ : ∀ i, NeZero (p i ^ n i) := fun i =>
    ⟨pow_ne_zero _ (Nat.prime_of_mem_primeFactors i.property).ne_zero⟩
  have hprod : (∏ i, p i ^ n i) = q := by
    change (∏ i : q.primeFactors, (i : ℕ) ^ q.factorization i) = q
    rw [Finset.prod_coe_sort q.primeFactors (fun i : ℕ => i ^ q.factorization i)]
    exact Nat.prod_factorization_pow_eq_self (NeZero.ne q)
  let _ : NeZero (∏ i, p i ^ n i) := ⟨by rw [hprod]; exact NeZero.ne q⟩
  have hinj : Function.Injective p := Subtype.val_injective
  have hc : Pairwise (fun i j => (p i ^ n i).Coprime (p j ^ n j)) := by
    intro i j hij
    exact ((Nat.coprime_primes (Fact.out : (p i).Prime) (Fact.out : (p j).Prime)).mpr
      (fun hp => hij (hinj hp))).pow _ _
  have hmain : ∀ b : (ZMod (∏ i, p i ^ n i))ˣ,
      Nat.card {x : (ZMod (∏ i, p i ^ n i))ˣ // x ^ 2 = b} ≤
        2 ^ (Fintype.card I + 1) :=
    prime_powers_square_fiber_card_le p n hinj hc
  rw [hprod] at hmain
  simpa only [I, Fintype.card_coe] using hmain a

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SquareRootProbability
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The divisor loss in the square-congruence probability -/

namespace Ostmann

open scoped BigOperators Classical

theorem two_pow_primeFactors_card_le_divisors_card (q : ℕ) (hq : q ≠ 0) :
    2 ^ q.primeFactors.card ≤ q.divisors.card := by
  rw [Nat.card_divisors hq]
  calc
    _ = ∏ _p ∈ q.primeFactors, 2 := by simp
    _ ≤ _ := by
      apply Finset.prod_le_prod'
      intro p hp
      have hmem : p ∈ q.factorization.support := by
        simpa only [Nat.support_factorization] using hp
      have hf := Finsupp.mem_support_iff.mp hmem
      omega

/-- The loss from unit sampling and the possible power of two is bounded
by two divisor factors, leaving the essential reciprocal-modulus decay. -/
theorem square_root_density_factor_le (q : ℕ) [NeZero q] :
    (2 : ℝ) ^ (q.primeFactors.card + 1) / q.totient ≤
      2 * (q.divisors.card : ℝ) ^ 2 / q := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hω : (2 : ℝ) ^ q.primeFactors.card ≤ q.divisors.card := by
    exact_mod_cast two_pow_primeFactors_card_le_divisors_card q (NeZero.ne q)
  have hd : (q : ℝ) ≤ q.divisors.card * (q.totient : ℝ) := by
    exact_mod_cast le_divisors_card_mul_totient q (NeZero.ne q)
  apply (div_le_div_iff₀ hφ hq).mpr
  calc
    _ ≤ (2 * (q.divisors.card : ℝ)) * q := by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_right (by nlinarith) hq.le
    _ ≤ (2 * (q.divisors.card : ℝ)) * (q.divisors.card * (q.totient : ℝ)) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = _ := by ring

/-- A Haar unit satisfies a prescribed square congruence with probability
at most `2*tau(q)^2/q`. This applies also to inconsistent congruences. -/
theorem unit_square_probability_le (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) :
    (Nat.card {x : (ZMod q)ˣ // x ^ 2 = a} : ℝ) / Fintype.card (ZMod q)ˣ ≤
      2 * (q.divisors.card : ℝ) ^ 2 / q := by
  rw [ZMod.card_units_eq_totient]
  apply le_trans _ (square_root_density_factor_le q)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast unit_square_fiber_card_le q a

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_UniformGroupReduction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform unit reduction to a divisor of the frequency modulus -/

namespace Ostmann

open scoped BigOperators Classical

theorem surjective_group_sum {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] (f : G →* H) (hf : Function.Surjective f) (F : H → ℝ) :
    (∑ x : G, F (f x)) = (Fintype.card f.ker : ℝ) * ∑ y : H, F y := by
  have hcard (y : H) : (Finset.univ.filter (fun x : G => f x = y)).card =
      Fintype.card f.ker := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr (MonoidHom.fiberEquivKerOfSurjective hf y)
  rw [← Finset.sum_fiberwise_of_maps_to (g := f) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _) (fun x => F (f x))]
  calc
    _ = ∑ y : H, (Fintype.card f.ker : ℝ) * F y := by
      apply Finset.sum_congr rfl
      intro y _
      calc
        _ = ∑ _x ∈ Finset.univ.filter (fun x : G => f x = y), F y :=
          Finset.sum_congr rfl fun _ hx => congrArg F (Finset.mem_filter.mp hx).2
        _ = _ := by simp [hcard]
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem surjective_group_average {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] (f : G →* H) (hf : Function.Surjective f) (F : H → ℝ) :
    (Fintype.card G : ℝ)⁻¹ * (∑ x : G, F (f x)) =
      (Fintype.card H : ℝ)⁻¹ * ∑ y : H, F y := by
  have hc : (Fintype.card G : ℝ) =
      (Fintype.card f.ker : ℝ) * Fintype.card H := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      using surjective_group_sum f hf (fun _ => (1 : ℝ))
  have hk : (Fintype.card f.ker : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [surjective_group_sum f hf F, hc, mul_inv_rev]
  field_simp

theorem unit_reduction_average {q Q : ℕ} [NeZero q] [NeZero Q] (h : q ∣ Q)
    (F : (ZMod q)ˣ → ℝ) :
    (Fintype.card (ZMod Q)ˣ : ℝ)⁻¹ *
        (∑ x : (ZMod Q)ˣ, F (ZMod.unitsMap h x)) =
      (Fintype.card (ZMod q)ˣ : ℝ)⁻¹ * ∑ y : (ZMod q)ˣ, F y :=
  surjective_group_average (ZMod.unitsMap h) (ZMod.unitsMap_surjective h) F

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SimultaneousSquares
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two simultaneous square congruences at a history split -/

namespace Ostmann

open scoped BigOperators Classical

theorem unitsMap_eq_iff_modEq {q Q : ℕ} [NeZero Q] (h : q ∣ Q)
    (x y : (ZMod Q)ˣ) :
    ZMod.unitsMap h x = ZMod.unitsMap h y ↔
      Nat.ModEq q (x : ZMod Q).val (y : ZMod Q).val := by
  rw [← Units.val_inj]
  change ZMod.castHom h (ZMod q) (x : ZMod Q) =
    ZMod.castHom h (ZMod q) (y : ZMod Q) ↔ _
  nth_rw 1 [← ZMod.natCast_zmod_val (x : ZMod Q), ← ZMod.natCast_zmod_val (y : ZMod Q)]
  simp only [map_natCast, ZMod.natCast_eq_natCast_iff]

theorem lcm_units_ext {a b : ℕ} [NeZero (a.lcm b)] (x y : (ZMod (a.lcm b))ˣ)
    (ha : ZMod.unitsMap (Nat.dvd_lcm_left a b) x = ZMod.unitsMap (Nat.dvd_lcm_left a b) y)
    (hb : ZMod.unitsMap (Nat.dvd_lcm_right a b) x = ZMod.unitsMap (Nat.dvd_lcm_right a b) y) :
    x = y := by
  have hma := (unitsMap_eq_iff_modEq (Nat.dvd_lcm_left a b) x y).mp ha
  have hmb := (unitsMap_eq_iff_modEq (Nat.dvd_lcm_right a b) x y).mp hb
  have hm := Nat.mod_lcm hma hmb
  apply Units.ext
  simpa only [ZMod.natCast_zmod_val] using
    (ZMod.natCast_eq_natCast_iff (x : ZMod (a.lcm b)).val
      (y : ZMod (a.lcm b)).val (a.lcm b)).mpr hm

theorem simultaneous_square_probability_le {a b : ℕ} [NeZero a] [NeZero b]
    [NeZero (a.lcm b)] (A : (ZMod a)ˣ) (B : (ZMod b)ˣ) :
    (Fintype.card (ZMod (a.lcm b))ˣ : ℝ)⁻¹ *
        (∑ x : (ZMod (a.lcm b))ˣ,
          if (ZMod.unitsMap (Nat.dvd_lcm_left a b) x) ^ 2 = A ∧
            (ZMod.unitsMap (Nat.dvd_lcm_right a b) x) ^ 2 = B then (1 : ℝ) else 0) ≤
      2 * ((a.lcm b).divisors.card : ℝ) ^ 2 / (a.lcm b) := by
  let P := fun x : (ZMod (a.lcm b))ˣ =>
    (ZMod.unitsMap (Nat.dvd_lcm_left a b) x) ^ 2 = A ∧
      (ZMod.unitsMap (Nat.dvd_lcm_right a b) x) ^ 2 = B
  by_cases hex : ∃ r, P r
  · obtain ⟨r, hr⟩ := hex
    have heq (x : (ZMod (a.lcm b))ˣ) : P x ↔ x ^ 2 = r ^ 2 := by
      constructor
      · intro hx
        apply lcm_units_ext
        · simp only [map_pow]
          exact hx.1.trans hr.1.symm
        · simp only [map_pow]
          exact hx.2.trans hr.2.symm
      · intro hx
        constructor
        · have ht := congrArg (ZMod.unitsMap (Nat.dvd_lcm_left a b)) hx
          rw [map_pow, map_pow] at ht
          exact ht.trans hr.1
        · have ht := congrArg (ZMod.unitsMap (Nat.dvd_lcm_right a b)) hx
          rw [map_pow, map_pow] at ht
          exact ht.trans hr.2
    change (Fintype.card (ZMod (a.lcm b))ˣ : ℝ)⁻¹ * (∑ x, if P x then 1 else 0) ≤ _
    simp_rw [heq]
    have hs : (∑ x : (ZMod (a.lcm b))ˣ, if x ^ 2 = r ^ 2 then (1 : ℝ) else 0) =
        (Nat.card {x : (ZMod (a.lcm b))ˣ // x ^ 2 = r ^ 2} : ℝ) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hs, mul_comm, ← div_eq_mul_inv]
    exact unit_square_probability_le (a.lcm b) (r ^ 2)
  · have hn : ∀ x, ¬P x := by simpa only [not_exists] using hex
    change (Fintype.card (ZMod (a.lcm b))ˣ : ℝ)⁻¹ * (∑ x, if P x then 1 else 0) ≤ _
    simp only [hn, ↓reduceIte, Finset.sum_const_zero, mul_zero]
    positivity

/-- The support probability under the original larger Haar modulus, before
conditioning on any history tests. -/
theorem reduced_simultaneous_square_probability_le {a b Q : ℕ}
    [NeZero a] [NeZero b] [NeZero Q]
    (ha : a ∣ Q) (hb : b ∣ Q) (A : (ZMod a)ˣ) (B : (ZMod b)ˣ) :
    (Fintype.card (ZMod Q)ˣ : ℝ)⁻¹ *
        (∑ x : (ZMod Q)ˣ,
          if (ZMod.unitsMap ha x) ^ 2 = A ∧ (ZMod.unitsMap hb x) ^ 2 = B then (1 : ℝ) else 0) ≤
      2 * ((a.lcm b).divisors.card : ℝ) ^ 2 / (a.lcm b) := by
  let _ : NeZero (a.lcm b) := ⟨Nat.lcm_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  have hL : a.lcm b ∣ Q := Nat.lcm_dvd ha hb
  have hleft (x : (ZMod Q)ˣ) : ZMod.unitsMap (Nat.dvd_lcm_left a b) (ZMod.unitsMap hL x) =
      ZMod.unitsMap ha x := DFunLike.congr_fun (ZMod.unitsMap_comp (Nat.dvd_lcm_left a b) hL) x
  have hright (x : (ZMod Q)ˣ) : ZMod.unitsMap (Nat.dvd_lcm_right a b) (ZMod.unitsMap hL x) =
      ZMod.unitsMap hb x := DFunLike.congr_fun (ZMod.unitsMap_comp (Nat.dvd_lcm_right a b) hL) x
  have heq := unit_reduction_average hL (fun x =>
    if (ZMod.unitsMap (Nat.dvd_lcm_left a b) x) ^ 2 = A ∧
      (ZMod.unitsMap (Nat.dvd_lcm_right a b) x) ^ 2 = B then (1 : ℝ) else 0)
  simp only [hleft, hright] at heq
  exact heq.trans_le (simultaneous_square_probability_le A B)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SplitSquareSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # From the actual split relation to its reduced square equation -/

namespace Ostmann

open scoped BigOperators Classical

theorem split_relation_gcd_eq {s v w x y : ℕ}
    (hx : x.Coprime s) (hy : y.Coprime s)
    (h : Nat.ModEq s (v * x) (w * y)) : v.gcd s = w.gcd s := by
  simpa only [hx.gcd_mul_right_cancel, hy.gcd_mul_right_cancel] using h.gcd_eq

theorem split_relation_divide_gcd {s v w x y : ℕ} (hs : s ≠ 0)
    (hgcd : v.gcd s = w.gcd s) :
    Nat.ModEq s (v * x) (w * y) ↔
      Nat.ModEq (s / v.gcd s) ((v / v.gcd s) * x) ((w / v.gcd s) * y) := by
  have hd : v.gcd s ≠ 0 := Nat.gcd_ne_zero_right hs
  have hdv : v.gcd s ∣ v := Nat.gcd_dvd_left v s
  have hdw : v.gcd s ∣ w := hgcd ▸ Nat.gcd_dvd_left w s
  have hds : v.gcd s ∣ s := Nat.gcd_dvd_right v s
  simpa only [← Nat.mul_assoc, Nat.mul_div_cancel' hds,
    Nat.mul_div_cancel' hdv, Nat.mul_div_cancel' hdw] using
    (Nat.ModEq.mul_left_cancel_iff' (a := (v / v.gcd s) * x)
      (b := (w / v.gcd s) * y) (m := s / v.gcd s) hd)

theorem unit_coefficient_equation_iff {s : ℕ} [NeZero s]
    (v w : ℕ) (x y : (ZMod s)ˣ) :
    (v : ZMod s) * x = (w : ZMod s) * y ↔
      Nat.ModEq s (v * (x : ZMod s).val) (w * (y : ZMod s).val) := by
  simpa only [Nat.cast_mul, ZMod.natCast_zmod_val] using
    ZMod.natCast_eq_natCast_iff (v * (x : ZMod s).val) (w * (y : ZMod s).val) s

theorem unit_coefficient_gcd_eq {s : ℕ} [NeZero s]
    (v w : ℕ) (x y : (ZMod s)ˣ)
    (h : (v : ZMod s) * x = (w : ZMod s) * y) : v.gcd s = w.gcd s :=
  split_relation_gcd_eq (ZMod.val_coe_unit_coprime x) (ZMod.val_coe_unit_coprime y)
    ((unit_coefficient_equation_iff v w x y).mp h)

theorem unit_coefficient_reduce {s : ℕ} [NeZero s]
    (v w : ℕ) (hgcd : v.gcd s = w.gcd s) (x y : (ZMod s)ˣ) :
    (v : ZMod s) * x = (w : ZMod s) * y ↔
      (v / v.gcd s : ZMod (s / v.gcd s)) *
          ZMod.unitsMap (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right v s)) x =
        (w / v.gcd s : ZMod (s / v.gcd s)) *
          ZMod.unitsMap (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right v s)) y := by
  rw [unit_coefficient_equation_iff,
    split_relation_divide_gcd (NeZero.ne s) hgcd]
  have hcast (u : (ZMod s)ˣ) :
      (ZMod.unitsMap (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right v s)) u :
          ZMod (s / v.gcd s)) = ((u : ZMod s).val : ZMod (s / v.gcd s)) := by
    change ZMod.castHom (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right v s)) _ (u : ZMod s) = _
    nth_rw 1 [← ZMod.natCast_zmod_val (u : ZMod s)]
    exact map_natCast _ _
  rw [hcast, hcast]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).symm.trans (by simp only [Nat.cast_mul])

/-- The parent product is already exposed. The child product remains the
uniform variable, and the split relation specifies its square. -/
theorem split_relation_iff_square {G : Type*} [CommGroup G]
    (A B P x : G) : A * (P / x) = B * x ↔ x ^ 2 = A * P / B := by
  constructor
  · intro h
    have hm := congrArg (fun y => y * x / B) h
    calc
      x ^ 2 = B * x * x / B := by rw [mul_assoc, mul_div_cancel_left, pow_two]
      _ = A * (P / x) * x / B := hm.symm
      _ = A * P / B := by rw [mul_assoc A, div_mul_cancel]
  · intro h
    have hm := congrArg (fun y => B * y / x) h
    calc
      A * (P / x) = B * (A * P / B) / x := by
        rw [mul_div_cancel, mul_div_assoc]
      _ = B * x ^ 2 / x := hm.symm
      _ = B * x := by rw [pow_two, ← mul_assoc, mul_div_cancel_right]

theorem unit_split_iff_square {s : ℕ} [NeZero s]
    (v w : ℕ) (hgcd : v.gcd s = w.gcd s) (A B P x : (ZMod s)ˣ) :
    (v : ZMod s) * (A * (P / x) : (ZMod s)ˣ) =
        (w : ZMod s) * (B * x : (ZMod s)ˣ) ↔
      (ZMod.unitsMap (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right v s)) x) ^ 2 =
        splitSquareTarget v w hgcd A B P := by
  let f := ZMod.unitsMap (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right v s))
  let h := reduced_split_coefficients_coprime (NeZero.ne s) hgcd
  have heq := split_relation_iff_square
    (ZMod.unitOfCoprime (v / v.gcd s) h.1 * f A)
    (ZMod.unitOfCoprime (w / v.gcd s) h.2 * f B) (f P) (f x)
  rw [← Units.val_inj] at heq
  apply (unit_coefficient_reduce v w hgcd (A * (P / x)) (B * x)).trans
  simpa only [f, splitSquareTarget, map_mul, map_div, Units.val_mul,
    Units.val_div_eq_div_val, ZMod.coe_unitOfCoprime, mul_assoc] using heq

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_JointSplitProbability
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The joint support bound for two genuine arithmetic history splits -/

namespace Ostmann

open scoped BigOperators Classical

theorem reduced_modulus_pos {s v : ℕ} (hs : s ≠ 0) : 0 < s / v.gcd s :=
  Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hs) (Nat.gcd_dvd_right v s))
    (Nat.gcd_pos_of_pos_right v (Nat.pos_of_ne_zero hs))

/-- The two histories share the random child product but may have different
parent products, pivots, and frequencies. No complete-history validity event
has been conditioned on in this average. -/
theorem joint_split_probability_le {s t Q : ℕ} [NeZero s] [NeZero t] [NeZero Q]
    (hs : s ∣ Q) (ht : t ∣ Q) (v w v' w' : ℕ)
    (hgcd : v.gcd s = w.gcd s) (hgcd' : v'.gcd t = w'.gcd t)
    (A B P : (ZMod s)ˣ) (A' B' P' : (ZMod t)ˣ) :
    (Fintype.card (ZMod Q)ˣ : ℝ)⁻¹ * (∑ x : (ZMod Q)ˣ,
      if (v : ZMod s) * (A * (P / ZMod.unitsMap hs x) : (ZMod s)ˣ) =
          (w : ZMod s) * (B * ZMod.unitsMap hs x : (ZMod s)ˣ) ∧
        (v' : ZMod t) * (A' * (P' / ZMod.unitsMap ht x) : (ZMod t)ˣ) =
          (w' : ZMod t) * (B' * ZMod.unitsMap ht x : (ZMod t)ˣ)
      then (1 : ℝ) else 0) ≤
      2 * (((s / v.gcd s).lcm (t / v'.gcd t)).divisors.card : ℝ) ^ 2 /
        (s / v.gcd s).lcm (t / v'.gcd t) := by
  let a := s / v.gcd s
  let b := t / v'.gcd t
  let _ : NeZero a := ⟨Nat.ne_of_gt (reduced_modulus_pos (v := v) (NeZero.ne s))⟩
  let _ : NeZero b := ⟨Nat.ne_of_gt (reduced_modulus_pos (v := v') (NeZero.ne t))⟩
  have ha : a ∣ s := Nat.div_dvd_of_dvd (Nat.gcd_dvd_right v s)
  have hb : b ∣ t := Nat.div_dvd_of_dvd (Nat.gcd_dvd_right v' t)
  have hleft (x : (ZMod Q)ˣ) :
      ZMod.unitsMap ha (ZMod.unitsMap hs x) = ZMod.unitsMap (ha.trans hs) x :=
    DFunLike.congr_fun (ZMod.unitsMap_comp ha hs) x
  have hright (x : (ZMod Q)ˣ) :
      ZMod.unitsMap hb (ZMod.unitsMap ht x) = ZMod.unitsMap (hb.trans ht) x :=
    DFunLike.congr_fun (ZMod.unitsMap_comp hb ht) x
  simp_rw [unit_split_iff_square v w hgcd, unit_split_iff_square v' w' hgcd',
    hleft, hright]
  exact reduced_simultaneous_square_probability_le (ha.trans hs) (hb.trans ht)
    (splitSquareTarget v w hgcd A B P) (splitSquareTarget v' w' hgcd' A' B' P')

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SignedSplitSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Signed frequencies in the actual split-support equations -/

namespace Ostmann

open scoped BigOperators Classical

theorem intCast_frequencySign (q : ℕ) (v : ℤ) :
    (v : ZMod q) = (v.natAbs : ZMod q) * frequencySignUnit q v := by
  by_cases hv : 0 ≤ v
  · have he := congrArg (Int.castRingHom (ZMod q)) (Int.eq_natAbs_of_nonneg hv)
    simpa only [frequencySignUnit, hv, ↓reduceIte, Units.val_one, mul_one,
      Int.coe_castRingHom, Int.cast_natCast] using he
  · have he := congrArg (Int.castRingHom (ZMod q))
      (Int.eq_neg_natAbs_of_nonpos (le_of_not_ge hv))
    simpa only [frequencySignUnit, hv, ↓reduceIte, Units.val_neg, Units.val_one,
      Int.coe_castRingHom, Int.cast_neg, Int.cast_natCast, mul_neg, mul_one] using he

theorem signed_coefficient_equation_iff {q : ℕ} (v w : ℤ) (x y : (ZMod q)ˣ) :
    (v : ZMod q) * x = (w : ZMod q) * y ↔
      (v.natAbs : ZMod q) * (frequencySignUnit q v * x : (ZMod q)ˣ) =
        (w.natAbs : ZMod q) * (frequencySignUnit q w * y : (ZMod q)ˣ) := by
  rw [intCast_frequencySign q v, intCast_frequencySign q w]
  simp only [Units.val_mul, mul_assoc]

theorem common_reduced_modulus {s v w : ℕ} (h : v.gcd s = w.gcd s) :
    reducedFrequency (v.gcd w) s = s / v.gcd s := by
  have hg : (v.gcd w).gcd s = v.gcd s := by
    rw [Nat.gcd_assoc, ← h, ← Nat.gcd_assoc, Nat.gcd_self]
  simp only [reducedFrequency, Nat.gcd_comm s, hg]

/-- Both signs are absorbed into fixed units, and impossible gcd patterns
contribute zero. Thus no soluble-pattern hypothesis is needed. -/
theorem signed_joint_split_probability_le {s t Q : ℕ} [NeZero s] [NeZero t] [NeZero Q]
    (hs : s ∣ Q) (ht : t ∣ Q) (v w v' w' : ℤ)
    (A B P : (ZMod s)ˣ) (A' B' P' : (ZMod t)ˣ) :
    (Fintype.card (ZMod Q)ˣ : ℝ)⁻¹ * (∑ x : (ZMod Q)ˣ,
      if (v : ZMod s) * (A * (P / ZMod.unitsMap hs x) : (ZMod s)ˣ) =
          (w : ZMod s) * (B * ZMod.unitsMap hs x : (ZMod s)ˣ) ∧
        (v' : ZMod t) * (A' * (P' / ZMod.unitsMap ht x) : (ZMod t)ˣ) =
          (w' : ZMod t) * (B' * ZMod.unitsMap ht x : (ZMod t)ˣ)
      then (1 : ℝ) else 0) ≤
      2 * (((reducedFrequency (v.natAbs.gcd w.natAbs) s).lcm
          (reducedFrequency (v'.natAbs.gcd w'.natAbs) t)).divisors.card : ℝ) ^ 2 /
        (reducedFrequency (v.natAbs.gcd w.natAbs) s).lcm
          (reducedFrequency (v'.natAbs.gcd w'.natAbs) t) := by
  simp_rw [signed_coefficient_equation_iff, ← mul_assoc]
  by_cases h : v.natAbs.gcd s = w.natAbs.gcd s
  · by_cases h' : v'.natAbs.gcd t = w'.natAbs.gcd t
    · rw [common_reduced_modulus h, common_reduced_modulus h']
      exact joint_split_probability_le hs ht v.natAbs w.natAbs v'.natAbs w'.natAbs h h'
        (frequencySignUnit s v * A) (frequencySignUnit s w * B) P
        (frequencySignUnit t v' * A') (frequencySignUnit t w' * B') P'
    · have hz (x : (ZMod Q)ˣ) : ¬((v'.natAbs : ZMod t) *
          ((frequencySignUnit t v' * A') * (P' / ZMod.unitsMap ht x) : (ZMod t)ˣ) =
        (w'.natAbs : ZMod t) *
          ((frequencySignUnit t w' * B') * ZMod.unitsMap ht x : (ZMod t)ˣ)) := by
        intro he
        exact h' (unit_coefficient_gcd_eq _ _ _ _ he)
      simp only [hz, and_false, ↓reduceIte, Finset.sum_const_zero, mul_zero]
      positivity
  · have hz (x : (ZMod Q)ˣ) : ¬((v.natAbs : ZMod s) *
          ((frequencySignUnit s v * A) * (P / ZMod.unitsMap hs x) : (ZMod s)ˣ) =
        (w.natAbs : ZMod s) *
          ((frequencySignUnit s w * B) * ZMod.unitsMap hs x : (ZMod s)ˣ)) := by
        intro he
        exact h (unit_coefficient_gcd_eq _ _ _ _ he)
    simp only [hz, false_and, ↓reduceIte, Finset.sum_const_zero, mul_zero]
    positivity

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TreeLeafProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Leaf-product fibers in a full binary tree -/

namespace Ostmann

open scoped BigOperators

theorem card_treeLeafTuple {U : Type*} [Fintype U] (n : ℕ) :
    Fintype.card (TreeLeafTuple U n) = Fintype.card U ^ (2 ^ n) := by
  induction n with
  | zero =>
    change Fintype.card U = Fintype.card U ^ (2 ^ 0)
    simp
  | succ n ih =>
    change Fintype.card (TreeLeafTuple U n × TreeLeafTuple U n) = _
    rw [Fintype.card_prod, ih, pow_succ (2 : ℕ), pow_mul, pow_two]

theorem card_treeLeafFiber {U : Type*} [CommGroup U] [Fintype U] (n : ℕ) (P : U) :
    Fintype.card (TreeLeafFiber U n P) = Fintype.card U ^ (2 ^ n - 1) := by
  induction n generalizing P with
  | zero => rw [Fintype.card_congr (treeLeafFiberZeroEquiv P)]; simp
  | succ n ih =>
    rw [Fintype.card_congr (treeLeafFiberSuccEquiv n P), Fintype.card_sigma]
    simp only [Fintype.card_prod, ih, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Nat.cast_id]
    rw [← pow_add, ← pow_succ']
    congr 1
    have h : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
    rw [pow_succ]
    omega

theorem sum_treeLeafTuple_by_product {U R : Type*} [CommGroup U] [Fintype U]
    [AddCommMonoid R] (n : ℕ) (f : TreeLeafTuple U n → R) :
    (∑ x : TreeLeafTuple U n, f x) = ∑ P : U, ∑ x : TreeLeafFiber U n P, f x.1 := by
  classical
  have h := (Equiv.sigmaFiberEquiv (treeLeafProduct (U := U) n)).sum_comp f
  change (∑ x : (Σ P : U, TreeLeafFiber U n P), f x.2.1) = _ at h
  simpa only [Fintype.sum_sigma] using h.symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TreeSplitCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent split coordinates on each actual leaf-product fiber -/

namespace Ostmann

open scoped BigOperators Classical

/-- Exact transport of the original conditional Haar average. -/
theorem treeLeafSplit_average {G : Type} [CommGroup G] [Fintype G]
    (n : ℕ) (P : G) (F : SplitSamples G (2 ^ n - 1) → ℝ) :
    (Fintype.card (TreeLeafFiber G n P) : ℝ)⁻¹ *
        (∑ x : TreeLeafFiber G n P, F (treeLeafSplitEquiv n P x)) =
      (Fintype.card G : ℝ)⁻¹ ^ (2 ^ n - 1) * ∑ y, F y := by
  rw [(treeLeafSplitEquiv n P).sum_comp, card_treeLeafFiber, Nat.cast_pow, inv_pow]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticSplitData
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed residue data at an exposed arithmetic split -/

namespace Ostmann

open scoped BigOperators Classical

theorem ArithmeticSplitData.pair_probability_le {Q : ℕ} [NeZero Q]
    (d e : ArithmeticSplitData Q) :
    (Fintype.card (ZMod Q)ˣ : ℝ)⁻¹ *
        (∑ x : (ZMod Q)ˣ, if d.test x ∧ e.test x then (1 : ℝ) else 0) ≤
      2 * ((d.reducedModulus.lcm e.reducedModulus).divisors.card : ℝ) ^ 2 /
        d.reducedModulus.lcm e.reducedModulus := by
  have h := signed_joint_split_probability_le d.frequency_dvd e.frequency_dvd
    d.leftFrequency d.rightFrequency e.leftFrequency e.rightFrequency
    d.leftFactor d.rightFactor d.parentProduct e.leftFactor e.rightFactor e.parentProduct
  convert h using 1
  · congr 1
    apply Finset.sum_congr rfl
    intro x _
    dsimp only [ArithmeticSplitData.test]
    split_ifs with ht
    · exact ite_eq_left ht
    · exact ite_eq_right ht
  · rfl

theorem arithmeticPairSplit_probability_le {Q : ℕ} [NeZero Q]
    (d : Option (ArithmeticSplitData Q × ArithmeticSplitData Q)) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ d₁ d₂, d = some (d₁, d₂) →
      2 * ((d₁.reducedModulus.lcm d₂.reducedModulus).divisors.card : ℝ) ^ 2 /
        d₁.reducedModulus.lcm d₂.reducedModulus ≤ B) :
    (Fintype.card (ZMod Q)ˣ : ℝ)⁻¹ *
        (∑ x : (ZMod Q)ˣ, if arithmeticPairSplitTest d x then (1 : ℝ) else 0) ≤ B := by
  cases d with
  | none => simpa only [arithmeticPairSplitTest, ↓reduceIte, Finset.sum_const_zero, mul_zero] using hB
  | some d =>
      have h := (d.1.pair_probability_le d.2).trans (hbound d.1 d.2 rfl)
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      dsimp only [arithmeticPairSplitTest]
      split_ifs with ht
      · exact ite_eq_left ht
      · exact ite_eq_right ht

/-- All residue data are functions of the exposed prefix alone. This
derives the product bound for the actual two-history congruence tests. -/
theorem arithmetic_sequential_support_le {Q : ℕ} [NeZero Q]
    (data : List (ZMod Q)ˣ → Option (ArithmeticSplitData Q × ArithmeticSplitData Q))
    (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hbound : ∀ past d e, data past = some (d, e) →
      2 * ((d.reducedModulus.lcm e.reducedModulus).divisors.card : ℝ) ^ 2 /
        d.reducedModulus.lcm e.reducedModulus ≤ B past.length)
    (n : ℕ) :
    (Fintype.card (ZMod Q)ˣ : ℝ)⁻¹ ^ n *
        (∑ x : SplitSamples (ZMod Q)ˣ n,
          sequentialSupport (fun past y => arithmeticPairSplitTest (data past) y) [] n x) ≤
      ∏ j ∈ Finset.range n, B j := by
  have h := sequentialSupport_average_le_product
    (fun past y => arithmeticPairSplitTest (data past) y) B hB
    (fun past => arithmeticPairSplit_probability_le (data past) (B past.length) (hB _)
      (hbound past)) [] n
  simpa only [List.length_nil, Nat.zero_add] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticSplitTreeSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multiplying the actual split probabilities at fixed frequencies -/

namespace Ostmann

open scoped BigOperators Classical

theorem ArithmeticSplitData.reducedModulus_eq {Q : ℕ} (d : ArithmeticSplitData Q)
    (f : NodeFrequencies) (h : d.hasFrequencies f) : d.reducedModulus = f.reducedModulus := by
  simp only [ArithmeticSplitData.reducedModulus, NodeFrequencies.reducedModulus, h.1, h.2.1, h.2.2]

theorem pairFrequencySupportBound_nonneg (D : ℝ) (f : NodeFrequencies × NodeFrequencies) :
    0 ≤ pairFrequencySupportBound D f := by unfold pairFrequencySupportBound; positivity

/-- The reduced moduli depend only on the fixed frequencies. All pivot
and unit data may still vary with the previously exposed split products. -/
theorem arithmetic_support_fixed_frequencies {Q : ℕ} [NeZero Q]
    (data : List (ZMod Q)ˣ → Option (ArithmeticSplitData Q × ArithmeticSplitData Q))
    (frequencies : ℕ → NodeFrequencies × NodeFrequencies) (D : ℝ) (_hD : 0 ≤ D)
    (hmatch : ∀ past d e, data past = some (d, e) →
      d.hasFrequencies (frequencies past.length).1 ∧
        e.hasFrequencies (frequencies past.length).2)
    (hdiv : ∀ j, (((frequencies j).1.reducedModulus.lcm
      (frequencies j).2.reducedModulus).divisors.card : ℝ) ≤ D)
    (n : ℕ) :
    (Fintype.card (ZMod Q)ˣ : ℝ)⁻¹ ^ n *
        (∑ x : SplitSamples (ZMod Q)ˣ n,
          sequentialSupport (fun past y => arithmeticPairSplitTest (data past) y) [] n x) ≤
      ∏ j ∈ Finset.range n, pairFrequencySupportBound D (frequencies j) := by
  apply arithmetic_sequential_support_le data _ (fun _ => pairFrequencySupportBound_nonneg _ _) _ n
  intro past d e hd
  obtain ⟨hdmatch, hematch⟩ := hmatch past d e hd
  rw [d.reducedModulus_eq _ hdmatch, e.reducedModulus_eq _ hematch]
  unfold pairFrequencySupportBound
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Nat.cast_nonneg _) (hdiv past.length) 2) (by norm_num)

/-- The same product estimate on the original uniformly sampled leaf
tuples, conditional only on their total product. -/
theorem arithmetic_leaf_support_fixed_frequencies {Q : ℕ} [NeZero Q]
    (data : List (ZMod Q)ˣ → Option (ArithmeticSplitData Q × ArithmeticSplitData Q))
    (frequencies : ℕ → NodeFrequencies × NodeFrequencies) (D : ℝ) (hD : 0 ≤ D)
    (hmatch : ∀ past d e, data past = some (d, e) →
      d.hasFrequencies (frequencies past.length).1 ∧
        e.hasFrequencies (frequencies past.length).2)
    (hdiv : ∀ j, (((frequencies j).1.reducedModulus.lcm
      (frequencies j).2.reducedModulus).divisors.card : ℝ) ≤ D)
    (n : ℕ) (P : (ZMod Q)ˣ) :
    (Fintype.card (TreeLeafFiber (ZMod Q)ˣ n P) : ℝ)⁻¹ *
        (∑ x : TreeLeafFiber (ZMod Q)ˣ n P,
          sequentialSupport (fun past y => arithmeticPairSplitTest (data past) y) []
            (2 ^ n - 1) (treeLeafSplitEquiv n P x)) ≤
      ∏ j ∈ Finset.range (2 ^ n - 1), pairFrequencySupportBound D (frequencies j) := by
  rw [treeLeafSplit_average]
  exact arithmetic_support_fixed_frequencies data frequencies D hD hmatch hdiv (2 ^ n - 1)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrequencyTreeNodes
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preorder frequency data and its exact product of split costs -/

namespace Ostmann

open scoped BigOperators Classical

theorem frequencyLeafWeight_nonneg {A : Type} (W : A → ℝ) (hW : ∀ a, 0 ≤ W a)
    (n : ℕ) (x : FrequencyTree A n) : 0 ≤ frequencyLeafWeight W n x := by
  induction n with
  | zero => exact hW x
  | succ n ih => exact mul_nonneg (ih _) (ih _)

theorem prod_range_list_getD {A : Type} (l : List A) (d : A) (f : A → ℝ) :
    (∏ j ∈ Finset.range l.length, f (l.getD j d)) = (l.map f).prod := by
  rw [← Fin.prod_univ_eq_prod_range]
  calc
    _ = ∏ i : Fin l.length, f l[i.val] := by
      apply Finset.prod_congr rfl
      intro i _
      rw [List.getD_eq_getElem l d i.isLt]
    _ = _ := Fin.prod_univ_fun_getElem l f

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticHistorySupportSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the original two-history congruence support over frequencies -/

namespace Ostmann

open scoped BigOperators Classical

theorem gcd_frequency_divisor_bound (S : Finset ℤ) (N : ℕ) (D : ℝ)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (hdiv : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D)
    (v : ℤ) (hv : v ∈ S) (w : ℤ) (_hw : w ∈ S) :
    ((v.natAbs.gcd w.natAbs).divisors.card : ℝ) ≤ D := by
  have hv0 : 0 < v.natAbs := Int.natAbs_pos.mpr (hS v hv).1
  have hN : 0 < N := hv0.trans_le (hS v hv).2
  apply hdiv
  · exact Nat.ne_of_gt (Nat.gcd_pos_of_pos_left _ hv0)
  · calc
      _ ≤ v.natAbs := Nat.gcd_le_left _ hv0
      _ ≤ N := (hS v hv).2
      _ ≤ N ^ 2 := by simpa only [pow_two] using Nat.le_mul_of_pos_right N hN

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticPrecision
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact loss of frequency precision at a reversing node -/

namespace Ostmann

theorem modEq_cancel_coprime_left (m u a b : ℤ) (hu : IsCoprime u m)
    (h : u * a ≡ u * b [ZMOD m]) : a ≡ b [ZMOD m] := by
  apply Int.modEq_iff_dvd.mpr
  apply hu.symm.dvd_of_dvd_mul_left
  have hd := h.dvd
  rwa [← mul_sub] at hd

/-- Division by `s` consumes one copy of `R`; division by its unit factor consumes none. -/
theorem reversal_residue_precision (R s u u' N N' p p' : ℤ) (k : ℕ)
    (hs : s ≠ 0) (hsR : s ∣ R) (hu : IsCoprime u R)
    (hN : N = s * u * p) (hN' : N' = s * u' * p')
    (hmod : N ≡ N' [ZMOD R ^ (k + 1)]) (humod : u ≡ u' [ZMOD R ^ k]) :
    p ≡ p' [ZMOD R ^ k] := by
  have hdiv : s * R ^ k ∣ N' - N := by
    apply dvd_trans _ hmod.dvd
    simpa only [pow_succ, mul_comm s] using mul_dvd_mul_left (R ^ k) hsR
  rw [hN', hN, show s * u' * p' - s * u * p = s * (u' * p' - u * p) by ring] at hdiv
  have hproducts : u * p ≡ u' * p' [ZMOD R ^ k] :=
    Int.modEq_iff_dvd.mpr (Int.dvd_of_mul_dvd_mul_left hs hdiv)
  apply modEq_cancel_coprime_left (R ^ k) u p p' hu.pow_right
  exact hproducts.trans (humod.symm.mul_right p')

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticResidueSplit
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the support data from an actual residue numerator -/

namespace Ostmann

open scoped Classical

theorem ArithmeticResidueSplit.toData_frequencies {Q : ℕ}
    (d : ArithmeticResidueSplit Q) (e : ArithmeticSplitData Q)
    (h : d.toData = some e) : e.hasFrequencies d.frequencies := by
  unfold ArithmeticResidueSplit.toData at h
  split_ifs at h with hL hR
  · cases Option.some.inj h
    exact ⟨rfl, rfl, rfl⟩

theorem ArithmeticResidueSplit.toData_test {Q : ℕ}
    (d : ArithmeticResidueSplit Q) (x : (ZMod Q)ˣ) :
    (∃ e, d.toData = some e ∧ e.test x) ↔ d.support x := by
  have hquot : ZMod.unitsMap d.frequency_dvd d.parentProduct /
      ZMod.unitsMap d.frequency_dvd x = ZMod.unitsMap d.frequency_dvd (d.parentProduct / x) :=
    (map_div (ZMod.unitsMap d.frequency_dvd) _ _).symm
  unfold ArithmeticResidueSplit.toData ArithmeticResidueSplit.support
  split_ifs with hL hR
  · simp only [Option.some.injEq, hL, hR, true_and]
    constructor
    · rintro ⟨e, rfl, h⟩
      dsimp only [ArithmeticSplitData.test] at h
      rw [hquot] at h
      simpa only [ArithmeticResidueSplit.numerator, ArithmeticResidueSplit.reduce,
        map_sub, map_mul, map_intCast, sub_eq_zero, Units.val_mul, IsUnit.unit_spec,
        ZMod.unitsMap, Units.coe_map, MonoidHom.coe_coe, mul_assoc] using h
    · intro h
      refine ⟨_, rfl, ?_⟩
      dsimp only [ArithmeticSplitData.test]
      rw [hquot]
      simpa only [ArithmeticResidueSplit.numerator, ArithmeticResidueSplit.reduce,
        map_sub, map_mul, map_intCast, sub_eq_zero, Units.val_mul, IsUnit.unit_spec,
        ZMod.unitsMap, Units.coe_map, MonoidHom.coe_coe, mul_assoc] using h
  · simp [hR]
  · simp [hL]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AdditiveFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Probability-normalized additive Fourier identities

These finite identities provide the normalization used in Section 6.
Fourier inversion is the library's discrete Fourier inversion theorem.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem stdAddChar_conj {p : ℕ} [NeZero p] (x : ZMod p) :
    conj (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  have hn : ‖ZMod.stdAddChar x‖ = 1 := by simp [ZMod.stdAddChar_apply]; exact Circle.norm_coe _
  rw [← Complex.inv_eq_conj hn, AddChar.map_neg_eq_inv]

theorem additiveFourier_inversion {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (x : ZMod p) :
    f x = ∑ a : ZMod p, additiveFourier f a * ZMod.stdAddChar (a * x) := by
  have hinv := congrFun (ZMod.dft.symm_apply_apply f) x
  rw [ZMod.invDFT_apply] at hinv
  calc
    f x = (p : ℂ)⁻¹ * ∑ a : ZMod p, ZMod.stdAddChar (a * x) * ZMod.dft f a := by
      simpa only [smul_eq_mul] using hinv.symm
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      simp only [additiveFourier]
      ring

theorem additiveFourier_conjugate_coefficient {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (a : ZMod p) :
    (∑ x : ZMod p, ZMod.stdAddChar (x * a) * conj (f x)) =
      (p : ℂ) * conj (additiveFourier f a) := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  rw [additiveFourier_apply]
  simp only [map_mul, map_inv₀, map_natCast, map_sum, stdAddChar_conj, neg_neg]
  rw [← mul_assoc, mul_inv_cancel₀ hp, one_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem additiveFourier_energy {p : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    (∑ x : ZMod p, ‖f x‖ ^ 2) =
      (p : ℝ) * ∑ a : ZMod p, ‖additiveFourier f a‖ ^ 2 := by
  have heq : (∑ x : ZMod p, f x * conj (f x)) =
      (p : ℂ) * ∑ a : ZMod p, additiveFourier f a * conj (additiveFourier f a) := by
    calc
      _ = ∑ x : ZMod p, ∑ a : ZMod p,
          additiveFourier f a * ZMod.stdAddChar (a * x) * conj (f x) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [← Finset.sum_mul, ← additiveFourier_inversion]
      _ = ∑ a : ZMod p, additiveFourier f a *
          ∑ x : ZMod p, ZMod.stdAddChar (x * a) * conj (f x) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [mul_comm x a]
        ring
      _ = _ := by
        simp_rw [additiveFourier_conjugate_coefficient]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
  simp_rw [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_sum] at heq
  exact_mod_cast heq

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PrimitiveGaussFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact primitive-character Fourier transform at composite modulus

This supplies the complete transform and Gauss normalization needed in the
quadratic Poisson step, using the proved library character identities.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem primitive_character_fourier {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (a : ZMod N) :
    additiveFourier χ a = (N : ℂ)⁻¹ * χ⁻¹ (-a) * gaussSum χ ZMod.stdAddChar := by
  rw [additiveFourier_apply]
  have heq : (∑ x : ZMod N, χ x * ZMod.stdAddChar (-(x * a))) =
      gaussSum χ ((ZMod.stdAddChar (N := N)).mulShift (-a)) := by
    simp only [gaussSum, AddChar.mulShift_apply]
    congr 1
    funext x
    rw [neg_mul, mul_comm a x]
  rw [heq, gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχ (-a)]
  ring

/-- Parseval gives the primitive Gauss-sum norm without a prime-modulus
restriction and without assuming a separate analytic input. -/
theorem primitive_gauss_norm_sq {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    ‖gaussSum χ (ZMod.stdAddChar (N := N))‖ ^ 2 = (N : ℝ) := by
  let E : ℝ := ∑ a : ZMod N, ‖χ a‖ ^ 2
  have hE : 0 < E := by
    have hh := Finset.single_le_sum (s := (Finset.univ : Finset (ZMod N)))
      (f := fun a => ‖χ a‖ ^ 2) (fun a _ => sq_nonneg ‖χ a‖) (Finset.mem_univ (1 : ZMod N))
    have h1 : (1 : ℝ) ≤ E := by simpa [E] using hh
    linarith
  have hinv : (∑ a : ZMod N, ‖χ⁻¹ (-a)‖ ^ 2) = E := by
    simp_rw [← MulChar.star_apply', norm_star]
    exact (Equiv.neg (ZMod N)).bijective.sum_comp (fun a => ‖χ a‖ ^ 2)
  have hfourier : (∑ a : ZMod N, ‖additiveFourier χ a‖ ^ 2) =
      (N : ℝ)⁻¹ ^ 2 * ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 * E := by
    rw [← hinv, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [primitive_character_fourier χ hχ a]
    simp only [Complex.norm_mul, norm_inv, Complex.norm_natCast, mul_pow]
    ring
  have heq := additiveFourier_energy χ
  rw [hfourier] at heq
  change E = (N : ℝ) * ((N : ℝ)⁻¹ ^ 2 * ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 * E) at heq
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  apply mul_right_cancel₀ hE.ne'
  field_simp [hN] at heq
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_IntegerIntervalDistribution
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary interval distribution for the external integer giant -/

namespace Ostmann

open scoped Classical
open MeasureTheory

theorem integer_interval_residue_error (lo hi q a : ℕ) (hlo : lo ≤ hi) (hq : 0 < q) :
    |(((Finset.Ioc lo hi).filter fun n => Nat.ModEq q n a).card : ℝ) -
      ((hi : ℝ) - lo) / q| ≤ 1 := by
  let A : ℚ := ((lo : ℚ) - a) / q
  let B : ℚ := ((hi : ℚ) - a) / q
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  have hAB : A ≤ B := by
    dsimp [A, B]
    exact div_le_div_of_nonneg_right
      (sub_le_sub_right (by exact_mod_cast hlo : (lo : ℚ) ≤ hi) a) hq'.le
  have hf := Int.floor_mono hAB
  have hcard := Nat.Ioc_filter_modEq_card lo hi hq a
  have hcast : (((Finset.Ioc lo hi).filter fun n => Nat.ModEq q n a).card : ℚ) =
      ((⌊B⌋ : ℤ) : ℚ) - ((⌊A⌋ : ℤ) : ℚ) := by
    rw [max_eq_left (sub_nonneg.mpr hf)] at hcard
    exact_mod_cast hcard
  have hA := Int.floor_le A
  have hA' := Int.lt_floor_add_one A
  have hB := Int.floor_le B
  have hB' := Int.lt_floor_add_one B
  have hrat : |(((Finset.Ioc lo hi).filter fun n => Nat.ModEq q n a).card : ℚ) -
      ((hi : ℚ) - lo) / q| ≤ 1 := by
    rw [hcast]
    have hid : ((hi : ℚ) - lo) / q = B - A := by dsimp [A, B]; ring
    rw [hid, abs_le]
    constructor <;> linarith
  have hr : ((|(((Finset.Ioc lo hi).filter fun n => Nat.ModEq q n a).card : ℚ) -
      ((hi : ℚ) - lo) / q| : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := Rat.cast_le.mpr hrat
  simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast, Rat.cast_one] using hr

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TupleCharacterPoisson
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Poisson summation and the initial graph phase of a character tuple -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap ComplexConjugate Classical

theorem primitiveGaussPhase_norm {p : ℕ} [NeZero p]
    (χ : DirichletCharacter ℂ p) (hχ : χ.IsPrimitive) :
    ‖primitiveGaussPhase χ‖ = 1 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast NeZero.pos p
  have hg := primitive_gauss_norm_sq χ hχ
  have he : ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt (p : ℝ) := by
    nlinarith [Real.sq_sqrt hp.le, Real.sqrt_nonneg (p : ℝ),
      norm_nonneg (gaussSum χ ZMod.stdAddChar)]
  rw [primitiveGaussPhase, norm_div, he, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_self (Real.sqrt_pos.mpr hp).ne']

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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AnchorPairCode
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Anchor codes from the actual graph update -/

namespace Ostmann

theorem anchorSignPair_determines_parity (α ε ε' : ℤ) (t t' : Bool)
    (hα : α = 1 ∨ α = -1)
    (h : anchorSignPair α ε t = anchorSignPair α ε' t') : ε = ε' := by
  rcases hα with rfl | rfl <;> cases t <;> cases t' <;>
    simp only [anchorSignPair, Bool.false_eq_true, ite_false, if_false, ite_true, if_true,
      Prod.mk.injEq, neg_one_mul, neg_neg, one_mul] at h <;> omega

theorem finiteAnchorCode_prefix_parity {n : ℕ} (α : Fin n → ℤ)
    (hα : ∀ j, α j = 1 ∨ α j = -1) (t t' : Fin n → Bool)
    (hcode : finiteAnchorCode α t = finiteAnchorCode α t') (j : Fin n) :
    copyPathParity (finiteCopyPath t) j = copyPathParity (finiteCopyPath t') j := by
  exact anchorSignPair_determines_parity _ _ _ _ _ (hα j) (congrFun hcode j)

/-- All code pairs determine the incoming parities; the final parity then
determines the last copy sign as well. -/
theorem finiteAnchorCode_final_injective {n : ℕ} (α : Fin n → ℤ)
    (hα : ∀ j, α j = 1 ∨ α j = -1) :
    Function.Injective (fun t : Fin n → Bool => (finiteAnchorCode α t, finalCopyParity t)) := by
  intro t t' he
  have hcode := congrArg Prod.fst he
  have hfinal := congrArg Prod.snd he
  funext j
  have hbefore := finiteAnchorCode_prefix_parity α hα t t' hcode j
  have hafter : copyPathParity (finiteCopyPath t) (j.val + 1) =
      copyPathParity (finiteCopyPath t') (j.val + 1) := by
    by_cases hj : j.val + 1 < n
    · exact finiteAnchorCode_prefix_parity α hα t t' hcode ⟨j.val + 1, hj⟩
    · have hjn : j.val + 1 = n := by omega
      simpa only [hjn, finalCopyParity] using hfinal
  simp only [copyPathParity, finiteCopyPath, j.isLt, dite_true, Fin.eta] at hafter
  rw [hbefore] at hafter
  apply transferCopySign_injective
  exact mul_right_cancel₀ (by rcases copyPathParity_sign (finiteCopyPath t') j with h | h <;> omega) hafter

/-- There are at most two paths with any fixed anchor code. -/
theorem card_anchorCode_fiber_le_two {n : ℕ} (α : Fin n → ℤ)
    (hα : ∀ j, α j = 1 ∨ α j = -1) (code : Fin n → ℤ × ℤ) :
    Fintype.card {t : Fin n → Bool // finiteAnchorCode α t = code} ≤ 2 := by
  classical
  let f : {t : Fin n → Bool // finiteAnchorCode α t = code} → Bool :=
    fun t => decide (finalCopyParity t.val = 1)
  have hf : Function.Injective f := by
    intro t t' he
    apply Subtype.ext
    apply finiteAnchorCode_final_injective α hα
    apply Prod.ext
    · exact t.property.trans t'.property.symm
    · have ht := copyPathParity_sign (finiteCopyPath t.val) n
      have ht' := copyPathParity_sign (finiteCopyPath t'.val) n
      change decide (finalCopyParity t.val = 1) = decide (finalCopyParity t'.val = 1) at he
      rcases ht with ht | ht <;> rcases ht' with ht' | ht' <;>
        simp only [finalCopyParity] at he ⊢ <;> simp_all
  simpa only [Fintype.card_bool] using Fintype.card_le_of_injective f hf

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteCellPrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact pushforward to log-cell and residue coordinates

The finite partition of each actual prime sample induces independent cell
priors. This is an equality, before any progression approximation is used.
-/

namespace Ostmann

open scoped BigOperators Classical

theorem cellPrior_nonneg {A B : Type*} [Fintype A]
    (μ : A → ℝ) (cell : A → B) (hμ : ∀ a, 0 ≤ μ a) (b : B) :
    0 ≤ cellPrior μ cell b := by
  apply Finset.sum_nonneg
  intro a _
  split
  · exact hμ a
  · exact le_rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HarmonicWordPriors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HistorySmoothFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The smooth factors in the expanded arithmetic histories

Compensation-prime powers and spectator transforms are excluded here,
as in the definition of Xi in Section 8 of the manuscript.
-/

namespace Ostmann

open scoped BigOperators

theorem archimedeanLeafFactor_norm_le (X M s cutoff B A : ℝ) (ψhat : ℝ → ℂ)
    (hcut : |cutoff| ≤ 1) (hψ : ∀ t, ‖ψhat t‖ ≤ B) (_hB : 0 ≤ B)
    (hratio : Real.sqrt (X / M) * B ≤ A) :
    ‖archimedeanLeafFactor X M s cutoff ψhat‖ ≤ A := by
  unfold archimedeanLeafFactor
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ (Real.sqrt (X / M) * 1) * B := mul_le_mul
      (mul_le_mul_of_nonneg_left hcut (Real.sqrt_nonneg _)) (hψ _)
      (norm_nonneg _) (by positivity)
    _ ≤ A := by simpa only [mul_one] using hratio

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_NormalizedFourierProfile
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounds for the actual normalized level-zero Fourier profile -/

namespace Ostmann

open scoped SchwartzMap

/-- Normalizing by X exactly recovers the original Fourier factor, before
its separate bounded support cutoff is applied. -/
theorem normalizedFourierProfile_original (ψ : ℝ → ℂ) (X M v : ℝ)
    (hX : X ≠ 0) (hM : M ≠ 0) :
    normalizedFourierProfile ψ v (M / X) = archimedeanLeafFactor X M v 1 ψ := by
  have hi : (M / X)⁻¹ = X / M := by field_simp
  have ha : -v * (M / X)⁻¹ = -v * X / M := by rw [hi]; ring
  have hs : (Real.sqrt (M / X))⁻¹ = Real.sqrt (X / M) := by rw [← Real.sqrt_inv, hi]
  simp only [normalizedFourierProfile, archimedeanLeafFactor, mul_one, hs, ha]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HistorySmoothBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exponential size of the smooth history factor -/

namespace Ostmann

theorem sqrt_ratio_le_exp (X M Δ C : ℝ) (hM : 0 < M)
    (hbound : X * Real.exp (Δ - C) ≤ M) :
    Real.sqrt (X / M) ≤ Real.exp ((C - Δ) / 2) := by
  have hexp : Real.exp (C - Δ) * Real.exp (Δ - C) = 1 := by
    rw [← Real.exp_add, show C - Δ + (Δ - C) = 0 by ring, Real.exp_zero]
  have hX : X ≤ Real.exp (C - Δ) * M := by
    calc
      X = Real.exp (C - Δ) * (X * Real.exp (Δ - C)) := by
        calc
          _ = X * (Real.exp (C - Δ) * Real.exp (Δ - C)) := by rw [hexp, mul_one]
          _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
  apply Real.sqrt_le_iff.mpr
  refine ⟨(Real.exp_pos _).le, ?_⟩
  have hsquare : Real.exp ((C - Δ) / 2) ^ 2 = Real.exp (C - Δ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hsquare]
  exact (div_le_iff₀ hM).mpr hX

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferFrequencyRigidity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniqueness of the two child frequencies and inserted pivot -/

namespace Ostmann

/-- Comparing two valid substitutions makes the child-frequency determinant
both divisible by the root frequency and too small to be nonzero. -/
theorem transfer_frequency_determinant_zero (L R P Q B K : ℕ) (s v w v' w' : ℤ)
    (hs : s ≠ 0) (hunit : IsCoprime s (R : ℤ))
    (hrel : v * R - w * L = s * P) (hrel' : v' * R - w' * L = s * Q)
    (hP : P ≤ K) (hQ : Q ≤ K) (hw : w.natAbs ≤ B) (hw' : w'.natAbs ≤ B)
    (hgap : 2 * K * B < R) : v * w' - v' * w = 0 := by
  let d := v * w' - v' * w
  let e := (P : ℤ) * w' - (Q : ℤ) * w
  have heq : (R : ℤ) * d = s * e := by
    dsimp [d, e]
    linear_combination w' * hrel - w * hrel'
  have hdiv : s ∣ d := hunit.dvd_of_dvd_mul_left ⟨e, heq⟩
  have heb : e.natAbs < R := by
    calc
      _ ≤ ((P : ℤ) * w').natAbs + ((Q : ℤ) * w).natAbs := Int.natAbs_sub_le _ _
      _ = P * w'.natAbs + Q * w.natAbs := by
        simp only [Int.natAbs_mul, Int.natAbs_natCast]
      _ ≤ K * B + K * B := Nat.add_le_add (Nat.mul_le_mul hP hw') (Nat.mul_le_mul hQ hw)
      _ = 2 * K * B := by ring
      _ < R := hgap
  by_contra hd
  have hd' : d ≠ 0 := hd
  have hle : s.natAbs ≤ d.natAbs := Int.natAbs_le_of_dvd_ne_zero hdiv hd'
  have ha := congrArg Int.natAbs heq
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at ha
  have hlt := Nat.mul_lt_mul_of_pos_left heb (Int.natAbs_pos.mpr hs)
  have hle' := Nat.mul_le_mul_left R hle
  nlinarith

/-- Coprimality with the frequencies rules out any nontrivial proportional
rescaling of the positive pivot. -/
theorem transfer_substitution_unique (L R P Q B K : ℕ) (s v w v' w' : ℤ)
    (hs : s ≠ 0) (hunit : IsCoprime s (R : ℤ))
    (hrel : v * R - w * L = s * P) (hrel' : v' * R - w' * L = s * Q)
    (hPpos : 0 < P) (hP : P ≤ K) (hQ : Q ≤ K)
    (hw : w.natAbs ≤ B) (hw' : w'.natAbs ≤ B)
    (hgap : 2 * K * B < R)
    (hPw : P.Coprime w.natAbs) (hQw : Q.Coprime w'.natAbs) :
    v = v' ∧ w = w' ∧ P = Q := by
  have hd := transfer_frequency_determinant_zero L R P Q B K s v w v' w'
    hs hunit hrel hrel' hP hQ hw hw' hgap
  have hcross : (P : ℤ) * w' = (Q : ℤ) * w := by
    have he : s * ((P : ℤ) * w' - (Q : ℤ) * w) = 0 := by
      calc
        _ = (R : ℤ) * (v * w' - v' * w) := by
          linear_combination -(w' * hrel - w * hrel')
        _ = 0 := by rw [hd, mul_zero]
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hs)
  have hcrossNat := congrArg Int.natAbs hcross
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at hcrossNat
  have hdPQ : P ∣ Q := hPw.dvd_of_dvd_mul_left (by
    rw [mul_comm w.natAbs Q, ← hcrossNat]
    exact dvd_mul_right P w'.natAbs)
  have hdQP : Q ∣ P := hQw.dvd_of_dvd_mul_left (by
    rw [mul_comm w'.natAbs P, hcrossNat]
    exact dvd_mul_right Q w.natAbs)
  have hPQ : P = Q := Nat.dvd_antisymm hdPQ hdQP
  have hwEq : w = w' := by
    rw [← hPQ] at hcross
    exact (mul_left_cancel₀ (by exact_mod_cast Nat.ne_of_gt hPpos) hcross).symm
  have hRpos : 0 < R := lt_of_le_of_lt (Nat.zero_le _) hgap
  have hvEq : v = v' := by
    have he : v * (R : ℤ) = v' * (R : ℤ) := by
      rw [← hwEq, ← hPQ] at hrel'
      linear_combination hrel - hrel'
    exact mul_right_cancel₀ (by exact_mod_cast Nat.ne_of_gt hRpos) he
  exact ⟨hvEq, hwEq, hPQ⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferHistoryUniqueness
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed top assignment and root frequency determine the full valid history -/

namespace Ostmann

/-- Inserted ancestor pivots are part of the state. Fixing their value at a
node therefore fixes both child states before the induction is applied. -/
theorem validTransferHistory_unique {State : Type*} (sys : TransferHistorySystem State)
    (n : ℕ) (σ : State) (x y : FrequencyTree ℤ n)
    (hx : ValidTransferHistory sys n σ x) (hy : ValidTransferHistory sys n σ y)
    (hroot : frequencyRoot n x = frequencyRoot n y) : x = y := by
  induction n generalizing σ with
  | zero => exact hroot
  | succ n ih =>
    obtain ⟨P, hP, hxL, hxR⟩ := hx
    obtain ⟨Q, hQ, hyL, hyR⟩ := hy
    have hr : x.1 = y.1 := hroot
    have hrelQ : frequencyRoot n y.2.1 * sys.rightProduct σ -
        frequencyRoot n y.2.2 * sys.leftProduct σ = x.1 * Q := by
      rw [hr]
      exact hQ.relation
    obtain ⟨hv, hw, hPQ⟩ := transfer_substitution_unique
      (sys.leftProduct σ) (sys.rightProduct σ) P Q (sys.childBound σ) (sys.pivotBound σ)
      x.1 (frequencyRoot n x.2.1) (frequencyRoot n x.2.2)
      (frequencyRoot n y.2.1) (frequencyRoot n y.2.2)
      hP.root_ne_zero hP.root_unit hP.relation hrelQ hP.pivot_pos hP.pivot_bound hQ.pivot_bound
      hP.right_bound hQ.right_bound hP.range_gap hP.pivot_unit hQ.pivot_unit
    subst Q
    have heL := ih (sys.leftState σ P) x.2.1 y.2.1 hxL hyL hv
    have heR := ih (sys.rightState σ P) x.2.2 y.2.2 hxR hyR hw
    exact Prod.ext hr (Prod.ext heL heR)

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

/-- Each squaring doubles the number of bottom weights and never adds an
absolute-value loss for a cutoff or an invalid arithmetic node. -/
theorem recursiveTransferWeight_square_le {State : Type*} (sys : TransferHistorySystem State)
    (leaf : State → ℤ → ℂ) (cutoff : State → ℤ → ℤ → ℤ → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hleaf : ∀ σ v, ‖leaf σ v‖ ^ 2 ≤ B)
    (hcut : ∀ σ s v w, |cutoff σ s v w| ≤ 1)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) :
    ‖recursiveTransferWeight sys leaf cutoff n σ t‖ ^ 2 ≤ B ^ (2 ^ n) := by
  induction n generalizing σ with
  | zero => simpa only [recursiveTransferWeight, pow_zero, pow_one] using hleaf σ t
  | succ n ih =>
    let P := historyPivot sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
    by_cases hP : ValidTransferNode sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P
    · rw [recursiveTransferWeight_node sys leaf cutoff n σ t P hP,
        norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs, mul_pow, mul_pow]
      have hc : |cutoff σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)| ^ 2 ≤ 1 := by
        simpa using pow_le_pow_left₀ (abs_nonneg _) (hcut σ t.1 _ _) 2
      calc
        _ ≤ (1 * B ^ (2 ^ n)) * B ^ (2 ^ n) :=
          mul_le_mul (mul_le_mul hc (ih _ _) (sq_nonneg _) (by norm_num))
            (ih _ _) (sq_nonneg _) (by positivity)
        _ = _ := by rw [one_mul, ← pow_add, pow_succ]; congr 1; omega
    · simp only [recursiveTransferWeight, P, hP, ite_false, if_false, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      positivity

/-- The manuscript's level-zero modulus window gives the full history
square bound, with exactly `2^n` copies of its exponent. -/
theorem recursiveTransferWeight_square_exp_le {State : Type*} (sys : TransferHistorySystem State)
    (leaf : State → ℤ → ℂ) (cutoff : State → ℤ → ℤ → ℤ → ℝ)
    (Δ K : ℝ) (hleaf : ∀ σ v, ‖leaf σ v‖ ^ 2 ≤ Real.exp (-Δ + K))
    (hcut : ∀ σ s v w, |cutoff σ s v w| ≤ 1)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) :
    ‖recursiveTransferWeight sys leaf cutoff n σ t‖ ^ 2 ≤
      Real.exp (-(2 ^ n : ℕ) * Δ + (2 ^ n : ℕ) * K) := by
  apply (recursiveTransferWeight_square_le sys leaf cutoff _ (Real.exp_pos _).le hleaf hcut n σ t).trans_eq
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- The leaf estimate is derived from the product window on every nonzero
cutoff, including its boundary. It is not a new norm hypothesis. -/
theorem archimedeanLeafFactor_square_exp_le (X M s c Δ C K : ℝ)
    (ψhat : ℝ → ℂ) (hc : |c| ≤ 1)
    (hψ : ∀ u, ‖ψhat u‖ ≤ Real.exp K)
    (hwindow : c ≠ 0 → 0 < M ∧ X * Real.exp (Δ - C) ≤ M) :
    ‖archimedeanLeafFactor X M s c ψhat‖ ^ 2 ≤ Real.exp (-Δ + (C + 2 * K)) := by
  by_cases hc0 : c = 0
  · simp only [archimedeanLeafFactor, hc0, mul_zero, Complex.ofReal_zero,
      zero_mul, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact (Real.exp_pos _).le
  · obtain ⟨hM, hMX⟩ := hwindow hc0
    have hratio : Real.sqrt (X / M) * Real.exp K ≤ Real.exp (K + (C - Δ) / 2) := by
      calc
        _ ≤ Real.exp ((C - Δ) / 2) * Real.exp K :=
          mul_le_mul_of_nonneg_right (sqrt_ratio_le_exp X M Δ C hM hMX) (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have hb := archimedeanLeafFactor_norm_le X M s c (Real.exp K)
      (Real.exp (K + (C - Δ) / 2)) ψhat hc hψ (Real.exp_pos _).le hratio
    apply (pow_le_pow_left₀ (norm_nonneg _) hb 2).trans_eq
    rw [← Real.exp_nat_mul]
    congr 1
    ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RecursiveNodeExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact preorder list of reconstructed arithmetic tests -/

namespace Ostmann

open scoped Classical

theorem transferNodeList_length {State : Type*} (sys : TransferHistorySystem State)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) :
    (transferNodeList sys n σ t).length = 2 ^ n - 1 := by
  induction n generalizing σ with
  | zero => rfl
  | succ n ih =>
    simp only [transferNodeList, List.length_cons, List.length_append, ih]
    have h := Nat.one_le_two_pow (n := n)
    rw [pow_succ]
    omega

/-- The pivot witness in the original definition is precisely the integer
reconstruction, so no existential choice changes the child states. -/
theorem validTransferHistory_reconstructed_iff {State : Type*}
    (sys : TransferHistorySystem State) (n : ℕ) (σ : State) (t : FrequencyTree ℤ (n + 1)) :
    ValidTransferHistory sys (n + 1) σ t ↔
      let P := historyPivot sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
      ValidTransferNode sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P ∧
        ValidTransferHistory sys n (sys.leftState σ P) t.2.1 ∧
        ValidTransferHistory sys n (sys.rightState σ P) t.2.2 := by
  constructor
  · rintro ⟨P, hp, hl, hr⟩
    rw [hp.historyPivot_eq]
    exact ⟨hp, hl, hr⟩
  · rintro ⟨hp, hl, hr⟩
    exact ⟨_, hp, hl, hr⟩

/-- All arithmetic support conditions in a complete history are the tests
of its explicitly reconstructed preorder node list. -/
theorem validTransferHistory_nodeList_iff {State : Type*}
    (sys : TransferHistorySystem State) (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) :
    ValidTransferHistory sys n σ t ↔ ∀ node ∈ transferNodeList sys n σ t, node.Valid sys := by
  induction n generalizing σ with
  | zero => simp [ValidTransferHistory, transferNodeList]
  | succ n ih =>
    rw [validTransferHistory_reconstructed_iff]
    simp only [transferNodeList, List.mem_cons, List.mem_append, or_imp,
      forall_and, forall_eq, ← ih]
    rfl

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

theorem copyScheduleUnary_norm_le_one {I : Type*}
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (g : I → I → ℤ) (pivot : ℕ → I) (initial : I → ℤ → ℕ → ℂ)
    (hinit : ∀ i v p, ‖initial i v p‖ ≤ 1)
    (n : ℕ) (t : FrequencyTree ℤ n) (i : CopyScheduleVertex I n) (p : ℕ) :
    ‖copyScheduleUnary χ g pivot initial n t i p‖ ≤ 1 := by
  induction n with
  | zero => exact hinit i t p
  | succ n ih =>
    rcases i with ⟨c, i⟩ | i
    · cases c
      · rw [copyScheduleUnary, norm_mul, Complex.norm_conj]
        exact (mul_le_mul (ih t.2.2 i) (character_zpow_norm_le_one _ _ _)
          (norm_nonneg _) (by norm_num)).trans (by norm_num)
      · rw [copyScheduleUnary, norm_mul]
        exact (mul_le_mul (ih t.2.1 i) (character_zpow_norm_le_one _ _ _)
          (norm_nonneg _) (by norm_num)).trans (by norm_num)
    · rw [copyScheduleUnary, norm_mul, Complex.norm_conj]
      exact (mul_le_mul (ih t.2.1 i) (ih t.2.2 i) (norm_nonneg _) (by norm_num)).trans (by norm_num)

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
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ResiduePopulationCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting bounded populations in their occupied residue classes -/

namespace Ostmann

open scoped BigOperators Classical

theorem nat_progression_population_card_le (S : Finset ℕ) (q D : ℕ) (hq : 0 < q)
    (hdiam : ∀ a ∈ S, ∀ b ∈ S, Nat.dist a b ≤ D)
    (hcongr : ∀ a ∈ S, ∀ b ∈ S, a ≡ b [MOD q]) :
    (S.card : ℝ) ≤ (D : ℝ) / q + 2 := by
  by_cases hS : S.Nonempty
  · let a := S.min' hS
    have ha : a ∈ S := Finset.min'_mem _ _
    have hsub : S.erase a ⊆ (Finset.Ioc a (a + D)).filter (fun n => n ≡ a [MOD q]) := by
      intro b hb
      obtain ⟨hne, hbS⟩ := Finset.mem_erase.mp hb
      have hab : a ≤ b := Finset.min'_le S b hbS
      have hd := hdiam a ha b hbS
      rw [Nat.dist_eq_sub_of_le hab] at hd
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, hcongr b hbS a ha⟩
    have hc : ((S.erase a).card : ℝ) ≤
        (((Finset.Ioc a (a + D)).filter (fun n => n ≡ a [MOD q])).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have he := (abs_le.mp (integer_interval_residue_error a (a + D) q a (by omega) hq)).2
    have hcard : (S.card : ℝ) = ((S.erase a).card : ℝ) + 1 := by
      exact_mod_cast (Finset.card_erase_add_one ha).symm
    rw [Nat.cast_add, add_sub_cancel_left] at he
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HarmonicResidueDomination
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coarse residue domination for the original harmonic prime priors

Only an upper bound is needed here. Dyadic interval counts give it without
any distribution theorem for primes, including at the boundary of a word bin.
-/

namespace Ostmann

open scoped BigOperators Classical

theorem harmonic_residue_block_le (S : Finset ℕ) (q N : ℕ)
    (hq : 0 < q) (hN : q ≤ N)
    (hrange : ∀ n ∈ S, N ≤ n ∧ n ≤ 2 * N)
    (hcongr : ∀ a ∈ S, ∀ b ∈ S, a ≡ b [MOD q]) :
    (∑ n ∈ S, (n : ℝ)⁻¹) ≤ 3 / q := by
  have hNpos : 0 < N := lt_of_lt_of_le hq hN
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  have hcard := nat_progression_population_card_le S q N hq
    (fun a ha b hb => by
      have ha' := hrange a ha
      have hb' := hrange b hb
      rcases le_total a b with hab | hba
      · rw [Nat.dist_eq_sub_of_le hab]; omega
      · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hba]; omega) hcongr
  have hi : (N : ℝ)⁻¹ ≤ (q : ℝ)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hqreal (show (q : ℝ) ≤ (N : ℝ) by exact_mod_cast hN)
  calc
    (∑ n ∈ S, (n : ℝ)⁻¹) ≤ ∑ _n ∈ S, (N : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      simpa only [one_div] using one_div_le_one_div_of_le hNreal
        (show (N : ℝ) ≤ (n : ℝ) by exact_mod_cast (hrange n hn).1)
    _ = (S.card : ℝ) * (N : ℝ)⁻¹ := by simp
    _ ≤ ((N : ℝ) / q + 2) * (N : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (q : ℝ)⁻¹ + 2 * (N : ℝ)⁻¹ := by
      field_simp
    _ ≤ 3 / q := by simp only [div_eq_mul_inv]; linarith

/-- The number of dyadic blocks, rather than the length of the prime range,
controls the harmonic mass of a residue class. -/
theorem harmonic_residue_dyadic_le (S : Finset ℕ) (q h J : ℕ)
    (hq : 0 < q) (hsmall : q ≤ 2 ^ h)
    (hrange : ∀ n ∈ S, 2 ^ h ≤ n ∧ n < 2 ^ (h + J))
    (hcongr : ∀ a ∈ S, ∀ b ∈ S, a ≡ b [MOD q]) :
    (∑ n ∈ S, (n : ℝ)⁻¹) ≤ 3 * J / q := by
  let block (j n : ℕ) : Prop := 2 ^ (h + j) ≤ n ∧ n < 2 ^ (h + j + 1)
  have hcover (n : ℕ) (hn : n ∈ S) : ∃ j ∈ Finset.range J, block j n := by
    have hnpos : n ≠ 0 := by have := (hrange n hn).1; have := Nat.two_pow_pos h; omega
    have hlo : h ≤ Nat.log 2 n :=
      (Nat.le_log_iff_pow_le (by norm_num) hnpos).mpr (hrange n hn).1
    have hhi : Nat.log 2 n < h + J :=
      (Nat.log_lt_iff_lt_pow (by norm_num) hnpos).mpr (hrange n hn).2
    refine ⟨Nat.log 2 n - h, Finset.mem_range.mpr (by omega), ?_⟩
    have he : h + (Nat.log 2 n - h) = Nat.log 2 n := by omega
    dsimp [block]
    rw [he]
    exact ⟨Nat.pow_log_le_self 2 hnpos, Nat.lt_pow_succ_log_self (by norm_num) n⟩
  calc
    (∑ n ∈ S, (n : ℝ)⁻¹) ≤
        ∑ n ∈ S, ∑ j ∈ Finset.range J, if block j n then (n : ℝ)⁻¹ else 0 := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨j, hj, hb⟩ := hcover n hn
      have hs := Finset.single_le_sum
        (f := fun j => if block j n then (n : ℝ)⁻¹ else 0)
        (fun j _ => by split_ifs <;> positivity) hj
      simpa only [ite_eq_left hb] using hs
    _ = ∑ j ∈ Finset.range J, ∑ n ∈ S.filter (block j), (n : ℝ)⁻¹ := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter]
    _ ≤ ∑ _j ∈ Finset.range J, 3 / (q : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      apply harmonic_residue_block_le _ q (2 ^ (h + j)) hq
      · exact hsmall.trans (Nat.pow_le_pow_right (by omega) (by omega))
      · intro n hn
        have hb := (Finset.mem_filter.mp hn).2
        exact ⟨hb.1, by have := hb.2; dsimp [block] at *; rw [pow_succ] at this; omega⟩
      · intro a ha b hb
        exact hcongr a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
    _ = 3 * J / q := by simp; ring

/-- Exact harmonic priors on arbitrary prime subsets obey the same bound.
No primality or interval closure of the selected subset is needed. -/
theorem primeSubsetPrior_residue_le (P S : Finset ℕ) (q h J : ℕ)
    (hq : 0 < q) (hsmall : q ≤ 2 ^ h)
    (hrange : ∀ n ∈ S, 2 ^ h ≤ n ∧ n < 2 ^ (h + J)) (a : ZMod q) :
    cellPrior (primeSubsetPrior P S) (fun p => ((p : ℕ) : ZMod q)) a ≤
      (∑ n ∈ S, (n : ℝ)⁻¹)⁻¹ * (3 * J / q) := by
  classical
  let T := P.filter (fun p => p ∈ S ∧ (p : ZMod q) = a)
  have hmass : 0 ≤ (∑ n ∈ S, (n : ℝ)⁻¹)⁻¹ := by positivity
  have hT := harmonic_residue_dyadic_le T q h J hq hsmall
    (fun n hn => hrange n (Finset.mem_filter.mp hn).2.1)
    (fun b hb c hc => (ZMod.natCast_eq_natCast_iff b c q).mp
      ((Finset.mem_filter.mp hb).2.2.trans (Finset.mem_filter.mp hc).2.2.symm))
  have heq : cellPrior (primeSubsetPrior P S) (fun p => ((p : ℕ) : ZMod q)) a =
      (∑ n ∈ S, (n : ℝ)⁻¹)⁻¹ * ∑ n ∈ T, (n : ℝ)⁻¹ := by
    let f (p : ℕ) : ℝ := if (p : ZMod q) = a then
      if p ∈ S then (p : ℝ)⁻¹ / (∑ n ∈ S, (n : ℝ)⁻¹) else 0 else 0
    have hf : cellPrior (primeSubsetPrior P S) (fun p => ((p : ℕ) : ZMod q)) a =
        ∑ p : P, f p := by
      unfold cellPrior
      apply Finset.sum_congr rfl
      intro p _
      dsimp [f, primeSubsetPrior]
      split_ifs <;> rfl
    rw [hf, Finset.sum_coe_sort P f]
    dsimp only [f]
    simp only [T, Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hpa : (p : ZMod q) = a <;> by_cases hpS : p ∈ S <;>
      simp [hpa, hpS, div_eq_mul_inv, mul_comm]
  rw [heq]
  exact mul_le_mul_of_nonneg_left hT hmass

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DyadicPrimeRange
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete dyadic covers of the prime ranges used by the prior comparison -/

namespace Ostmann

/-- A lower endpoint at least twice the modulus ensures every dyadic
interval in the cover is long enough for the uniform residue bound. -/
theorem dyadic_prime_range_cover (A B q : ℕ) (hq : 0 < q) (hA : 2 * q ≤ A)
    (S : Finset ℕ) (hS : ∀ p ∈ S, A ≤ p ∧ p ≤ B) :
    q ≤ 2 ^ Nat.log 2 A ∧
      ∀ p ∈ S, 2 ^ Nat.log 2 A ≤ p ∧ p < 2 ^ (Nat.log 2 A + (Nat.log 2 B + 1)) := by
  have hA0 : A ≠ 0 := by omega
  have hbound := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) A
  have hqpow : q ≤ 2 ^ Nat.log 2 A := by
    rw [pow_succ] at hbound
    omega
  refine ⟨hqpow, fun p hp => ⟨(Nat.pow_log_le_self 2 hA0).trans (hS p hp).1, ?_⟩⟩
  have hB := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) B
  apply ((hS p hp).2.trans_lt hB).trans_le
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- Even a doubly exponential prime endpoint needs only exponentially
many dyadic blocks. The constant is explicit and independent of the tree. -/
theorem dyadic_prime_range_count (B : ℕ) (C L : ℝ) (hC : 0 ≤ C) (hL : 1 ≤ L)
    (hB : (B : ℝ) ≤ Real.exp (Real.exp (C * L))) :
    ((Nat.log 2 B + 1 : ℕ) : ℝ) ≤
      Real.exp ((C + Real.log ((Real.log 2)⁻¹ + 1)) * L) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogB : Real.log B ≤ Real.exp (C * L) := by
    by_cases hB0 : B = 0
    · subst B
      simp only [Nat.cast_zero, Real.log_zero]
      exact (Real.exp_pos _).le
    · exact (Real.log_le_iff_le_exp (by exact_mod_cast Nat.pos_of_ne_zero hB0)).mpr hB
  have hnat : (Nat.log 2 B : ℝ) ≤ Real.log B / Real.log 2 := by
    simpa only [Real.logb, Nat.cast_ofNat] using Real.natLog_le_logb B 2
  have hexp1 : 1 ≤ Real.exp (C * L) := Real.one_le_exp (mul_nonneg hC (by linarith))
  have hconstant : 1 ≤ (Real.log 2)⁻¹ + 1 := by linarith [inv_pos.mpr hlog2]
  have hconstantpos : 0 < (Real.log 2)⁻¹ + 1 := lt_of_lt_of_le (by norm_num) hconstant
  have hlogconst : 0 ≤ Real.log ((Real.log 2)⁻¹ + 1) := Real.log_nonneg hconstant
  calc
    _ ≤ Real.log B / Real.log 2 + 1 := by push_cast; linarith
    _ ≤ Real.exp (C * L) / Real.log 2 + 1 := by gcongr
    _ ≤ ((Real.log 2)⁻¹ + 1) * Real.exp (C * L) := by
      rw [div_eq_mul_inv]
      nlinarith
    _ = Real.exp (Real.log ((Real.log 2)⁻¹ + 1) + C * L) := by
      rw [Real.exp_add, Real.exp_log hconstantpos]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_TotalAtomUnits
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledPriorFubini
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentPartitionAssignment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentPriorAssembly
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentBlockProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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

/-- All added guards are exact zero-one cutoffs and cannot increase energy. -/
theorem fullAtomTransferWeight_square_exp_le {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (Δ K : ℝ)
    (hleaf : ∀ σ v, ‖leaf σ v‖ ^ 2 ≤ Real.exp (-Δ + K))
    (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n) :
    ‖fullAtomTransferWeight role childBound pivotBound ranges leaf n x t‖ ^ 2 ≤
      Real.exp (-(2 ^ n : ℕ) * Δ + (2 ^ n : ℕ) * K) := by
  unfold fullAtomTransferWeight
  split_ifs
  · exact recursiveTransferWeight_square_exp_le _ leaf (fun _ _ _ _ => 1) Δ K hleaf
      (by intros; norm_num) n ⟨n, x⟩ t
  · simp only [norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact (Real.exp_pos _).le

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
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FullAtomFourierEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Energy of the actual Fourier weight from its initial modulus window -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

theorem normalizedFourier_window_square_exp_le (ψ : 𝓢(ℝ, ℂ))
    (X M v lo hi Δ C K : ℝ) (hX : 0 < X)
    (hlo : Real.exp (Δ - C) ≤ lo)
    (hψ : SchwartzMap.seminorm ℝ 0 0 ψ ≤ Real.exp K) :
    ‖(if M / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
        normalizedFourierProfile ψ v (M / X)‖ ^ 2 ≤
      Real.exp (-Δ + (C + 2 * K)) := by
  by_cases hm : M / X ∈ Set.Icc lo hi
  · have hMX : X * Real.exp (Δ - C) ≤ M := by
      simpa only [mul_comm] using (le_div_iff₀ hX).mp (hlo.trans hm.1)
    have hM : 0 < M := lt_of_lt_of_le (mul_pos hX (Real.exp_pos _)) hMX
    simp only [hm, ite_true, if_true, one_mul]
    rw [normalizedFourierProfile_original ψ X M v hX.ne' hM.ne']
    exact archimedeanLeafFactor_square_exp_le X M v 1 Δ C K ψ
      (by norm_num) (fun u => ((schwartz_profile_bounds ψ).1 u).trans hψ)
      (fun _ => ⟨hM, hMX⟩)
  · simp only [hm, ite_false, if_false, zero_mul, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact (Real.exp_pos _).le

/-- Every inherited support test is retained; the energy exponent comes solely
from the initial product window and the Fourier transform's Schwartz seminorm. -/
theorem fullAtomFourierWeight_square_exp_le {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi Δ C K : ℝ) (hX : 0 < X)
    (hlo : Real.exp (Δ - C) ≤ lo)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K)
    (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n) :
    ‖fullAtomTransferWeight role childBound pivotBound ranges
        (fun τ v => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
          normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X))
        n x t‖ ^ 2 ≤
      Real.exp (-(2 ^ n : ℕ) * Δ + (2 ^ n : ℕ) * (C + 2 * K)) := by
  apply fullAtomTransferWeight_square_exp_le role childBound pivotBound ranges _ Δ (C + 2 * K)
  intro τ v
  exact normalizedFourier_window_square_exp_le (𝓕 ψ) X (scheduleAtomTotal role τ)
    v lo hi Δ C K hX hlo hψ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SampledTupleAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite graph amplitude of an injective prime sample -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap Classical

theorem prime_character_isPrimitive (p : ℕ) (hp : p.Prime)
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) : χ.IsPrimitive := by
  let : NeZero p := ⟨hp.ne_zero⟩
  rcases (Nat.dvd_prime hp).mp χ.conductor_dvd_level with h | h
  · exact False.elim (hχ (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h))
  · exact h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialGaussMultipliers
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual bounded Gauss multipliers for every original prime role -/

namespace Ostmann
open scoped Classical

theorem primeGaussMultiplier_norm (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (p : ℕ) :
    ‖primeGaussMultiplier χ p‖ = 1 := by
  unfold primeGaussMultiplier
  split_ifs with hp
  · exact @primitiveGaussPhase_norm p ⟨hp.1.ne_zero⟩ _
      (prime_character_isPrimitive p hp.1 (χ p) hp.2)
  · exact norm_one

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledPhaseNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform modulus bounds for the literal scheduled prime phase -/

namespace Ostmann
open scoped Classical

theorem initialRegularUnary_norm_le_one {I : Type*}
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p) (κ : I → ℕ → ℂ)
    (hκ : ∀ i p, ‖κ i p‖ ≤ 1) (i : I) (v : ℤ) (p : ℕ) :
    ‖initialRegularUnary χ κ i v p‖ ≤ 1 := by
  unfold initialRegularUnary regularUnary
  rw [norm_mul]
  exact (mul_le_mul (hκ i p) (character_zpow_norm_le_one _ _ _)
    (norm_nonneg _) (by norm_num)).trans (by norm_num)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FiniteRootFibres
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Keeping the root frequency in the final counting measure -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate

/-- Expanding before taking norms leaves only equal-root pairs. -/
theorem rootFibreSum_pair {D K R : Type*} [Fintype D] [Fintype K] [Fintype R]
    (root : D → R) (root' : K → R) (F : D → ℂ) (G : K → ℂ) :
    (∑ s, rootFibreSum root s F * conj (rootFibreSum root' s G)) =
      ∑ d, ∑ k, if root d = root' k then F d * conj (G k) else 0 := by
  unfold rootFibreSum
  simp only [map_sum, Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  by_cases h : root d = root' k
  · simp only [h, ite_true, if_true]
  · simp only [h, Ne.symm h, ite_false, if_false, map_zero, mul_zero]

theorem rootFibreSum_weighted_pair {D K R X : Type*}
    [Fintype D] [Fintype K] [Fintype R] [Fintype X]
    (root : D → R) (root' : K → R) (μ : X → ℝ)
    (F : D → X → ℂ) (G : K → X → ℂ) :
    (∑ s, ∑ x, (μ x : ℂ) *
      (rootFibreSum root s (fun d => F d x) * conj (rootFibreSum root' s (fun k => G k x)))) =
      ∑ d, ∑ k, if root d = root' k then ∑ x, (μ x : ℂ) * (F d x * conj (G k x)) else 0 := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, rootFibreSum_pair, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : root d = root' k <;> simp only [h, ite_true, if_true, ite_false, if_false, mul_zero,
    Finset.sum_const_zero]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_UniformDivisorBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform subexponential divisor loss on the arithmetic moduli -/

namespace Ostmann

theorem divisors_subexponential_uniform (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ M : ℝ, ∀ m : ℝ, M ≤ m → ∀ n : ℕ, n ≠ 0 → (n : ℝ) ≤ Real.exp (C * m) →
      (n.divisors.card : ℝ) ≤ Real.exp (ε * m) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (C / ε)
  have hgap : 0 < ε * k - C := by
    have h := (div_lt_iff₀ hε).mp hk
    nlinarith
  have hk0 : k ≠ 0 := by
    intro hz
    simp only [hz, Nat.cast_zero, mul_zero] at hgap
    linarith
  obtain ⟨D, hD, hbound⟩ := exists_divisors_power_bound k
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D from hD)
  refine ⟨Real.log D / (ε * k - C), fun m hm n hn hnupper => ?_⟩
  have hlog : Real.log D + C * m ≤ ε * k * m := by
    have h := (div_le_iff₀ hgap).mp hm
    nlinarith
  have hpower : (n.divisors.card : ℝ) ^ k ≤ Real.exp (ε * m) ^ k := by
    calc
      _ ≤ (D : ℝ) * n := by exact_mod_cast hbound n hn
      _ ≤ (D : ℝ) * Real.exp (C * m) := mul_le_mul_of_nonneg_left hnupper hDpos.le
      _ = Real.exp (Real.log D + C * m) := by rw [Real.exp_add, Real.exp_log hDpos]
      _ ≤ Real.exp (ε * k * m) := Real.exp_le_exp.mpr hlog
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (Real.exp_pos _).le hk0).mp hpower

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrequencyBudgetRates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The frequency-tree cost is subexponential at fixed depth -/

namespace Ostmann

open Filter

theorem cubic_log_budget (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop, ∀ N : ℕ, (N : ℝ) ≤ Real.exp (C * m) →
      8 * (1 + Real.log N) ^ 3 ≤ Real.exp (ε * m) := by
  have he := ((isLittleO_pow_exp_pos_mul_atTop 3 hε).const_mul_left
    (8 * (1 + C) ^ 3)).bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [he, eventually_ge_atTop (1 : ℝ)] with m hm hm1 N hN
  have hm0 : 0 ≤ m := by linarith
  have hlog : Real.log N ≤ C * m := by
    by_cases hn : N = 0
    · subst N
      simpa using mul_nonneg hC hm0
    · exact (Real.log_le_iff_le_exp (by exact_mod_cast Nat.pos_of_ne_zero hn)).mpr hN
  have hlog0 := Real.log_natCast_nonneg N
  have hlin : 1 + Real.log N ≤ (1 + C) * m := by nlinarith
  have hpoly : 8 * (1 + C) ^ 3 * m ^ 3 ≤ Real.exp (ε * m) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ 8 * (1 + C) ^ 3 * m ^ 3), abs_of_pos (Real.exp_pos _), one_mul] using hm
  calc
    _ ≤ 8 * ((1 + C) * m) ^ 3 := by gcongr
    _ = 8 * (1 + C) ^ 3 * m ^ 3 := by ring
    _ ≤ _ := hpoly

/-- One value of `D` controls every frequency divisor and every joint
square modulus up to `exp(2*C*m)`, with the total cost at most `exp(epsilon*m)`. -/
theorem frequency_budget_subexponential (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop, ∃ D : ℝ, 0 ≤ D ∧
      (∀ n : ℕ, n ≠ 0 → (n : ℝ) ≤ Real.exp (2 * C * m) →
        (n.divisors.card : ℝ) ≤ D) ∧
      (∀ N : ℕ, (N : ℝ) ≤ Real.exp (C * m) →
        8 * D ^ 4 * (1 + Real.log N) ^ 3 ≤ Real.exp (ε * m)) := by
  obtain ⟨M, hM⟩ := divisors_subexponential_uniform (2 * C) (ε / 8)
    (by positivity) (by positivity)
  filter_upwards [eventually_ge_atTop M, cubic_log_budget C (ε / 2) hC (by positivity)]
    with m hm hpoly
  refine ⟨Real.exp ((ε / 8) * m), (Real.exp_pos _).le, hM m hm, fun N hN => ?_⟩
  have hexp : Real.exp ((ε / 8) * m) ^ 4 = Real.exp ((ε / 2) * m) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp]
  calc
    _ = Real.exp ((ε / 2) * m) * (8 * (1 + Real.log N) ^ 3) := by ring
    _ ≤ Real.exp ((ε / 2) * m) * Real.exp ((ε / 2) * m) :=
      mul_le_mul_of_nonneg_left (hpoly N hN) (Real.exp_pos _).le
    _ = Real.exp (ε * m) := by rw [← Real.exp_add]; congr 1; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SingleFrequencyTree
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The frequency budget for one squared history

Unlike a pair of histories, this sum has exactly one frequency at each leaf.
This is needed before the level-zero square-weight cancellation.
-/

namespace Ostmann

open scoped BigOperators Classical

theorem signed_reducedFrequency_sum_le (S : Finset ℤ) (N g : ℕ)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N) (hg : g ≠ 0) :
    (∑ s ∈ S, ((reducedFrequency g s.natAbs : ℕ) : ℝ)⁻¹) ≤
      2 * (g.divisors.card : ℝ) * (1 + Real.log N) := by
  have hh : (∑ a ∈ Finset.Icc 1 N, (a : ℝ)⁻¹) ≤ 1 + Real.log N := by
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using harmonic_le_one_add_log N
  calc
    _ ≤ 2 * ∑ a ∈ Finset.Icc 1 N, ((reducedFrequency g a : ℕ) : ℝ)⁻¹ :=
      sum_signed_magnitudes_le S N hS _ (fun _ _ => by positivity)
    _ ≤ 2 * ((g.divisors.card : ℝ) * ∑ a ∈ Finset.Icc 1 N, (a : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (sum_reducedFrequency_le N g hg
        (fun a => (a : ℝ)⁻¹) (fun _ _ => by positivity)) (by norm_num)
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_left hh (show 0 ≤ (g.divisors.card : ℝ) by positivity)
      nlinarith

theorem singleFrequencyKernel_sum_le (S : Finset ℤ) (N : ℕ) (D : ℝ)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (hdiv : ∀ v ∈ S, ∀ w ∈ S, ((v.natAbs.gcd w.natAbs).divisors.card : ℝ) ≤ D)
    (left right : S) :
    (∑ root : S, singleFrequencyKernel S D root left right) ≤
      4 * D ^ 3 * (1 + Real.log N) := by
  let g := (left : ℤ).natAbs.gcd (right : ℤ).natAbs
  have hg : g ≠ 0 := Nat.ne_of_gt (Nat.gcd_pos_of_pos_left _
    (Int.natAbs_pos.mpr (hS _ left.property).1))
  have hb := signed_reducedFrequency_sum_le S N g hS hg
  have hd : (g.divisors.card : ℝ) ≤ D := hdiv _ left.property _ right.property
  calc
    _ = 2 * D ^ 2 * (∑ s ∈ S, ((reducedFrequency g s.natAbs : ℕ) : ℝ)⁻¹) := by
      unfold singleFrequencyKernel
      simp only [div_eq_mul_inv, ← Finset.mul_sum]
      rw [Finset.sum_coe_sort S (fun s : ℤ => ((reducedFrequency g s.natAbs : ℕ) : ℝ)⁻¹)]
    _ ≤ 2 * D ^ 2 * (2 * (g.divisors.card : ℝ) * (1 + Real.log N)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ 2 * D ^ 2 * (2 * D * (1 + Real.log N)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by norm_num))
        (by have := Real.log_natCast_nonneg N; positivity)
    _ = _ := by ring

theorem singleFrequencyLeaf_sum_le (S : Finset ℤ) (V : ℕ)
    (hS : ∀ s ∈ S, s ≠ 0) :
    (∑ x : S, singleFrequencyLeaf S V x) ≤ 2 * V := by
  let T := S.filter fun s => s.natAbs ≤ V
  have hT : ∀ s ∈ T, s ≠ 0 ∧ s.natAbs ≤ V := by
    intro s hs
    exact ⟨hS s (Finset.mem_filter.mp hs).1, (Finset.mem_filter.mp hs).2⟩
  have hb := sum_signed_magnitudes_le T V hT (fun _ => (1 : ℝ)) (by intros; norm_num)
  unfold singleFrequencyLeaf
  rw [Finset.sum_coe_sort S (fun s : ℤ => if s.natAbs ≤ V then (1 : ℝ) else 0)]
  simpa [← Finset.sum_filter, T] using hb

theorem single_frequency_tree_sum_le (S : Finset ℤ) (N V n : ℕ) (D : ℝ)
    (hD : 0 ≤ D) (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (hdiv : ∀ v ∈ S, ∀ w ∈ S, ((v.natAbs.gcd w.natAbs).divisors.card : ℝ) ≤ D) :
    (∑ x : FrequencyTree S n,
      frequencyTreeWeight (singleFrequencyKernel S D) (singleFrequencyLeaf S V) n x) ≤
      (4 * D ^ 3 * (1 + Real.log N)) ^ (2 ^ n - 1) * (2 * (V : ℝ)) ^ (2 ^ n) := by
  have hC : 0 ≤ 4 * D ^ 3 * (1 + Real.log N) := by
    have := Real.log_natCast_nonneg N
    positivity
  apply (frequencyTree_sum_le (singleFrequencyKernel S D) (singleFrequencyLeaf S V)
    _ (by intros; unfold singleFrequencyKernel; positivity)
    (by intros; unfold singleFrequencyLeaf; split_ifs <;> norm_num) hC
    (singleFrequencyKernel_sum_le S N D hS hdiv) n).trans
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Finset.sum_nonneg fun x _ => by
      unfold singleFrequencyLeaf; split_ifs <;> norm_num)
      (singleFrequencyLeaf_sum_le S V (fun s hs => (hS s hs).1)) _) (pow_nonneg hC _)

theorem singleFrequencyTreeWeight_eq (S : Finset ℤ) (D : ℝ) (W : S → ℝ)
    (n : ℕ) (x : FrequencyTree S n) :
    frequencyTreeWeight (singleFrequencyKernel S D) W n x =
      ((singleFrequencySplitList S n x).map (singleFrequencySupportBound D)).prod *
        frequencyLeafWeight W n x := by
  induction n with
  | zero => simp [frequencyTreeWeight, singleFrequencySplitList, frequencyLeafWeight]
  | succ n ih =>
    simp only [frequencyTreeWeight, singleFrequencySplitList, frequencyLeafWeight,
      List.map_cons, List.map_append, List.prod_cons, List.prod_append, ih,
      singleFrequencySupportBound, singleFrequencyKernel, NodeFrequencies.reducedModulus]
    ring

theorem singleFrequencySplitList_modulus_mem (S : Finset ℤ) (N : ℕ)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N) (n : ℕ) (x : FrequencyTree S n)
    (f : NodeFrequencies) (hf : f ∈ singleFrequencySplitList S n x) :
    f.reducedModulus ∈ Finset.Icc 1 N := by
  induction n with
  | zero => simp [singleFrequencySplitList] at hf
  | succ n ih =>
    simp only [singleFrequencySplitList, List.mem_cons, List.mem_append] at hf
    rcases hf with rfl | hf | hf
    · exact reducedFrequency_mem (Finset.mem_Icc.mpr
        ⟨Int.natAbs_pos.mpr (hS _ x.1.property).1, (hS _ x.1.property).2⟩)
    · exact ih _ hf
    · exact ih _ hf

theorem singleTreeNodeFrequencies_divisor_bound (S : Finset ℤ) (N : ℕ) (D : ℝ)
    (hD : 0 ≤ D) (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (hdiv : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D)
    (n : ℕ) (x : FrequencyTree S n) (j : ℕ) :
    (((singleTreeNodeFrequencies S n x j).reducedModulus).divisors.card : ℝ) ≤ D := by
  by_cases hj : j < (singleFrequencySplitList S n x).length
  · have hmem : singleTreeNodeFrequencies S n x j ∈ singleFrequencySplitList S n x := by
      rw [singleTreeNodeFrequencies, List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    obtain ⟨hpos, hle⟩ := Finset.mem_Icc.mp (singleFrequencySplitList_modulus_mem S N hS n x _ hmem)
    apply hdiv _ (Nat.ne_of_gt hpos)
    exact hle.trans (by nlinarith)
  · rw [singleTreeNodeFrequencies, List.getD_eq_default _ _ (by omega)]
    simpa [emptyNodeFrequencies, NodeFrequencies.reducedModulus, reducedFrequency] using hD

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TreeProductDisintegration
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Disintegrating the original independent leaf law by its total product -/

namespace Ostmann

open scoped BigOperators

theorem sum_treeLeafTuple_dependent {G : Type} [CommGroup G] [Fintype G]
    (n : ℕ) (F : (P : G) → TreeLeafFiber G n P → ℝ) :
    (∑ x : TreeLeafTuple G n, F (treeLeafProduct n x) ⟨x, rfl⟩) =
      ∑ P : G, ∑ x : TreeLeafFiber G n P, F P x := by
  rw [sum_treeLeafTuple_by_product]
  apply Finset.sum_congr rfl
  intro P _
  apply Finset.sum_congr rfl
  rintro ⟨x, hx⟩ _
  cases hx
  rfl

theorem treeLeaf_average_by_product {G : Type} [CommGroup G] [Fintype G]
    (n : ℕ) (F : (P : G) → TreeLeafFiber G n P → ℝ) :
    (Fintype.card (TreeLeafTuple G n) : ℝ)⁻¹ *
        (∑ x : TreeLeafTuple G n, F (treeLeafProduct n x) ⟨x, rfl⟩) =
      (Fintype.card G : ℝ)⁻¹ * ∑ P : G,
        (Fintype.card (TreeLeafFiber G n P) : ℝ)⁻¹ * ∑ x, F P x := by
  rw [sum_treeLeafTuple_dependent]
  simp only [card_treeLeafTuple, card_treeLeafFiber, Nat.cast_pow]
  rw [← Finset.mul_sum, ← mul_assoc, ← mul_inv, ← pow_succ']
  have hcount : 2 ^ n - 1 + 1 = 2 ^ n := Nat.sub_add_cancel Nat.one_le_two_pow
  rw [hcount]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SingleHistorySupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact one-history arithmetic support under independent uniform leaves -/

namespace Ostmann

open scoped BigOperators Classical

theorem diagonalSplitData_test {Q : ℕ} (d : Option (ArithmeticSplitData Q))
    (x : (ZMod Q)ˣ) :
    arithmeticPairSplitTest (diagonalSplitData d) x ↔ singleArithmeticSplitTest d x := by
  cases d <;> simp [diagonalSplitData, arithmeticPairSplitTest, singleArithmeticSplitTest]

theorem singleArithmeticLeafSupport_nonneg {Q : ℕ} [NeZero Q]
    (n : ℕ) (data : (ZMod Q)ˣ → List (ZMod Q)ˣ → Option (ArithmeticSplitData Q))
    (x : TreeLeafTuple (ZMod Q)ˣ n) : 0 ≤ singleArithmeticLeafSupport n data x :=
  sequentialSupport_nonneg _ _ _ _

/-- The already proved joint root bound, applied twice to the same test,
loses no additional frequency choices or support conditions. -/
theorem single_arithmetic_leaf_support_le {Q : ℕ} [NeZero Q]
    (data : List (ZMod Q)ˣ → Option (ArithmeticSplitData Q))
    (frequencies : ℕ → NodeFrequencies) (D : ℝ) (hD : 0 ≤ D)
    (hmatch : ∀ past d, data past = some d → d.hasFrequencies (frequencies past.length))
    (hdiv : ∀ j, ((frequencies j).reducedModulus.divisors.card : ℝ) ≤ D)
    (n : ℕ) (P : (ZMod Q)ˣ) :
    (Fintype.card (TreeLeafFiber (ZMod Q)ˣ n P) : ℝ)⁻¹ *
      (∑ x : TreeLeafFiber (ZMod Q)ˣ n P,
        sequentialSupport (fun past y => singleArithmeticSplitTest (data past) y) []
          (2 ^ n - 1) (treeLeafSplitEquiv n P x)) ≤
      ∏ j ∈ Finset.range (2 ^ n - 1), singleFrequencySupportBound D (frequencies j) := by
  have hm : ∀ past d e, diagonalSplitData (data past) = some (d, e) →
      d.hasFrequencies (frequencies past.length) ∧
      e.hasFrequencies (frequencies past.length) := by
    intro past d e he
    cases hd : data past with
    | none => simp [diagonalSplitData, hd] at he
    | some f =>
      have heq : (f, f) = (d, e) := by simpa [diagonalSplitData, hd] using he
      have hf := hmatch past f hd
      cases heq
      exact ⟨hf, hf⟩
  have hb := arithmetic_leaf_support_fixed_frequencies
    (fun past => diagonalSplitData (data past)) (fun j => (frequencies j, frequencies j)) D hD hm
    (fun j => by simpa only [Nat.lcm_self] using hdiv j) n P
  simpa only [diagonalSplitData_test, pairFrequencySupportBound, Nat.lcm_self,
    singleFrequencySupportBound] using hb

/-- Pointwise in the frequency history and independent of the size of Q.
This permits the modulus to be chosen separately for each history. -/
theorem single_arithmetic_leaf_average_le {Q : ℕ} [NeZero Q]
    (S : Finset ℤ) (N n : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (hdiv : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D)
    (t : FrequencyTree S n)
    (data : (ZMod Q)ˣ → List (ZMod Q)ˣ → Option (ArithmeticSplitData Q))
    (hmatch : ∀ P past d, data P past = some d →
      d.hasFrequencies (singleTreeNodeFrequencies S n t past.length)) :
    (Fintype.card (TreeLeafTuple (ZMod Q)ˣ n) : ℝ)⁻¹ *
      (∑ x : TreeLeafTuple (ZMod Q)ˣ n, singleArithmeticLeafSupport n data x) ≤
      ((singleFrequencySplitList S n t).map (singleFrequencySupportBound D)).prod := by
  have hprod : (∏ j ∈ Finset.range (2 ^ n - 1),
      singleFrequencySupportBound D (singleTreeNodeFrequencies S n t j)) =
      ((singleFrequencySplitList S n t).map (singleFrequencySupportBound D)).prod := by
    rw [← singleFrequencySplitList_length S n t]
    exact prod_range_list_getD _ _ _
  unfold singleArithmeticLeafSupport
  rw [treeLeaf_average_by_product (G := (ZMod Q)ˣ) n
    (fun P x => sequentialSupport (fun past y => singleArithmeticSplitTest (data P past) y)
      [] (2 ^ n - 1) (treeLeafSplitEquiv n P x))]
  calc
    _ ≤ (Fintype.card (ZMod Q)ˣ : ℝ)⁻¹ * ∑ _P : (ZMod Q)ˣ,
        ((singleFrequencySplitList S n t).map (singleFrequencySupportBound D)).prod := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun P _ =>
        (single_arithmetic_leaf_support_le (data P) (singleTreeNodeFrequencies S n t) D hD
          (hmatch P) (singleTreeNodeFrequencies_divisor_bound S N D hD hS hdiv n t) n P).trans_eq hprod
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HarmonicUnitPriors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic prime residues compared with uniform unit residues -/

namespace Ostmann

open scoped BigOperators Classical

/-- The factor is the inverse harmonic normalizer times three times the
number of dyadic intervals. Boundary primes stay in the original prior. -/
theorem primeSubsetPrior_unit_residue_le (P S : Finset ℕ) (q h J : ℕ) [NeZero q]
    (hunit : ∀ p : P, (p : ℕ).Coprime q)
    (hsmall : q ≤ 2 ^ h)
    (hrange : ∀ n ∈ S, 2 ^ h ≤ n ∧ n < 2 ^ (h + J)) (a : (ZMod q)ˣ) :
    cellPrior (primeSubsetPrior P S) (fun p => ZMod.unitOfCoprime (p : ℕ) (hunit p)) a ≤
      ((∑ n ∈ S, (n : ℝ)⁻¹)⁻¹ * (3 * J)) * (Fintype.card (ZMod q)ˣ : ℝ)⁻¹ := by
  have hcell : cellPrior (primeSubsetPrior P S)
      (fun p => ZMod.unitOfCoprime (p : ℕ) (hunit p)) a =
      cellPrior (primeSubsetPrior P S) (fun p => ((p : ℕ) : ZMod q)) (a : ZMod q) := by
    unfold cellPrior
    apply Finset.sum_congr rfl
    intro p _
    have he : ZMod.unitOfCoprime (p : ℕ) (hunit p) = a ↔ ((p : ℕ) : ZMod q) = a := by
      rw [← Units.val_inj, ZMod.coe_unitOfCoprime]
    simp only [he]
    split_ifs <;> rfl
  rw [hcell]
  apply (primeSubsetPrior_residue_le P S q h J (NeZero.pos q) hsmall hrange a).trans
  have hcard : (Fintype.card (ZMod q)ˣ : ℝ) ≤ q := by
    exact_mod_cast (show Fintype.card (ZMod q)ˣ ≤ q by
      rw [ZMod.card_units_eq_totient]
      exact Nat.totient_le q)
  have hcpos : (0 : ℝ) < Fintype.card (ZMod q)ˣ := by
    exact_mod_cast Fintype.card_pos
  have hinv : (q : ℝ)⁻¹ ≤ (Fintype.card (ZMod q)ˣ : ℝ)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hcpos hcard
  calc
    _ = ((∑ n ∈ S, (n : ℝ)⁻¹)⁻¹ * (3 * J)) * (q : ℝ)⁻¹ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hinv (by positivity)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HarmonicProductDomination
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original independent harmonic priors on the leaves of a transfer tree -/

namespace Ostmann

open scoped BigOperators Classical

private theorem product_cellPrior_indexed {I A B : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (μ : I → A → ℝ) (cell : I → A → B) (y : I → B) :
    (∏ i, cellPrior (μ i) (cell i) (y i)) =
      ∑ x : I → A, if (fun i => cell i (x i)) = y then ∏ i, μ i (x i) else 0 := by
  classical
  unfold cellPrior
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases he : (fun i => cell i (x i)) = y
  · have hi (i : I) : cell i (x i) = y i := congrFun he i
    simp [hi]
  · have hi : ∃ i, cell i (x i) ≠ y i := by
      by_contra hn
      apply he
      funext i
      exact not_not.mp (not_exists.mp hn i)
    obtain ⟨i, hi⟩ := hi
    rw [ite_eq_right he]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

theorem indexed_cell_expectation_eq {I A B : Type*}
    [Fintype I] [DecidableEq I] [Fintype A] [Fintype B]
    (μ : I → A → ℝ) (cell : I → A → B) (F : (I → B) → ℝ) :
    (∑ x : I → A, (∏ i, μ i (x i)) * F (fun i => cell i (x i))) =
      ∑ y : I → B, (∏ i, cellPrior (μ i) (cell i) (y i)) * F y := by
  simp_rw [product_cellPrior_indexed, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]

/-- A pointwise upper bound for each residue class yields the product of
exactly one loss for each independently sampled leaf. -/
theorem indexed_cell_expectation_le {I A B : Type*}
    [Fintype I] [DecidableEq I] [Fintype A] [Fintype B]
    (μ : I → A → ℝ) (cell : I → A → B) (C : I → ℝ)
    (hμ : ∀ i a, 0 ≤ μ i a)
    (hcell : ∀ i b, cellPrior (μ i) (cell i) b ≤ C i * (Fintype.card B : ℝ)⁻¹)
    (F : (I → B) → ℝ) (hF : ∀ y, 0 ≤ F y) :
    (∑ x : I → A, (∏ i, μ i (x i)) * F (fun i => cell i (x i))) ≤
      (∏ i, C i) * ((Fintype.card (I → B) : ℝ)⁻¹ * ∑ y : I → B, F y) := by
  rw [indexed_cell_expectation_eq]
  have hprod (y : I → B) :
      (∏ i, cellPrior (μ i) (cell i) (y i)) ≤
        (∏ i, C i) * (Fintype.card (I → B) : ℝ)⁻¹ := by
    calc
      _ ≤ ∏ i, (C i * (Fintype.card B : ℝ)⁻¹) :=
        Finset.prod_le_prod (fun i _ => cellPrior_nonneg (μ i) (cell i) (hμ i) _) (fun i _ => hcell i _)
      _ = _ := by
        rw [Finset.prod_mul_distrib]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fun,
          Nat.cast_pow, inv_pow]
  calc
    _ ≤ ∑ y : I → B, ((∏ i, C i) * (Fintype.card (I → B) : ℝ)⁻¹) * F y :=
      Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_right (hprod y) (hF y)
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- This uses each leaf's actual harmonic subset, with all boundary primes
retained, and produces the original uniform-unit tree average. -/
theorem harmonic_leaf_residue_domination (P : Finset ℕ) (q n : ℕ) [NeZero q]
    (S : TreeLeafIndex n → Finset ℕ) (h J : TreeLeafIndex n → ℕ)
    (hunit : ∀ p : P, (p : ℕ).Coprime q)
    (hsmall : ∀ i, q ≤ 2 ^ h i)
    (hrange : ∀ i p, p ∈ S i → 2 ^ h i ≤ p ∧ p < 2 ^ (h i + J i))
    (F : TreeLeafTuple (ZMod q)ˣ n → ℝ) (hF : ∀ x, 0 ≤ F x) :
    (∑ x : TreeLeafIndex n → P, (∏ i, primeSubsetPrior P (S i) (x i)) *
      F ((treeLeafTupleEquiv (ZMod q)ˣ n).symm
        (fun i => ZMod.unitOfCoprime (x i : ℕ) (hunit (x i))))) ≤
      (∏ i, (∑ p ∈ S i, (p : ℝ)⁻¹)⁻¹ * (3 * J i)) *
        ((Fintype.card (TreeLeafTuple (ZMod q)ˣ n) : ℝ)⁻¹ * ∑ y, F y) := by
  have hb := indexed_cell_expectation_le
    (fun i => primeSubsetPrior P (S i))
    (fun _ p => ZMod.unitOfCoprime (p : ℕ) (hunit p))
    (fun i => (∑ p ∈ S i, (p : ℝ)⁻¹)⁻¹ * (3 * J i))
    (fun _ => primeSubsetPrior_nonneg _ _)
    (fun i b => primeSubsetPrior_unit_residue_le P (S i) q (h i) (J i)
      hunit (hsmall i) (hrange i) b)
    (fun y => F ((treeLeafTupleEquiv (ZMod q)ˣ n).symm y)) (fun y => hF _)
  rw [(treeLeafTupleEquiv (ZMod q)ˣ n).symm.sum_comp F] at hb
  rw [Fintype.card_congr (treeLeafTupleEquiv (ZMod q)ˣ n)]
  exact hb

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_HarmonicHistorySupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The arithmetic support bound under the original prime priors

The residue modulus is allowed to depend on the entire fixed frequency
history. Only the prime samples are averaged, with their original priors.
-/

namespace Ostmann

open scoped BigOperators Classical

theorem harmonic_history_support_le (P : Finset ℕ) (S : Finset ℤ) (N V n : ℕ)
    (D : ℝ) (hD : 0 ≤ D) (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (hdiv : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D)
    (Q : FrequencyTree S n → ℕ) [∀ t, NeZero (Q t)]
    (T : TreeLeafIndex n → Finset ℕ) (h J : TreeLeafIndex n → ℕ)
    (hunit : ∀ t, ∀ p : P, (p : ℕ).Coprime (Q t))
    (hsmall : ∀ t i, Q t ≤ 2 ^ h i)
    (hrange : ∀ i p, p ∈ T i → 2 ^ h i ≤ p ∧ p < 2 ^ (h i + J i))
    (data : (t : FrequencyTree S n) → (ZMod (Q t))ˣ →
      List (ZMod (Q t))ˣ → Option (ArithmeticSplitData (Q t)))
    (hmatch : ∀ t R past d, data t R past = some d →
      d.hasFrequencies (singleTreeNodeFrequencies S n t past.length)) :
    (∑ t : FrequencyTree S n, frequencyLeafWeight (singleFrequencyLeaf S V) n t *
      (∑ x : TreeLeafIndex n → P, (∏ i, primeSubsetPrior P (T i) (x i)) *
        singleArithmeticLeafSupport n (data t)
          ((treeLeafTupleEquiv (ZMod (Q t))ˣ n).symm
            (fun i => ZMod.unitOfCoprime (x i : ℕ) (hunit t (x i)))))) ≤
      (∏ i, (∑ p ∈ T i, (p : ℝ)⁻¹)⁻¹ * (3 * J i)) *
        ((4 * D ^ 3 * (1 + Real.log N)) ^ (2 ^ n - 1) *
          (2 * (V : ℝ)) ^ (2 ^ n)) := by
  let C := ∏ i, (∑ p ∈ T i, (p : ℝ)⁻¹)⁻¹ * (3 * J i)
  have hC : 0 ≤ C := Finset.prod_nonneg fun i _ => by positivity
  have hlocal (t : FrequencyTree S n) := harmonic_leaf_residue_domination P (Q t) n T h J
    (hunit t) (hsmall t) hrange (singleArithmeticLeafSupport n (data t))
    (singleArithmeticLeafSupport_nonneg n (data t))
  calc
    _ ≤ ∑ t : FrequencyTree S n, frequencyLeafWeight (singleFrequencyLeaf S V) n t *
        (C * ((singleFrequencySplitList S n t).map (singleFrequencySupportBound D)).prod) := by
      apply Finset.sum_le_sum
      intro t _
      apply mul_le_mul_of_nonneg_left _ (frequencyLeafWeight_nonneg _
        (fun _ => by unfold singleFrequencyLeaf; split_ifs <;> norm_num) n t)
      exact (hlocal t).trans (mul_le_mul_of_nonneg_left
        (single_arithmetic_leaf_average_le S N n D hD hS hdiv t (data t) (hmatch t)) hC)
    _ = C * ∑ t : FrequencyTree S n,
        frequencyTreeWeight (singleFrequencyKernel S D) (singleFrequencyLeaf S V) n t := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [singleFrequencyTreeWeight_eq]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (single_frequency_tree_sum_le S N V n D hD hS
      (gcd_frequency_divisor_bound S N D hS hdiv)) hC

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_LeafFrequencyBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The remaining leaf-frequency budget in the norm comparison -/

namespace Ostmann

theorem sqrt_cost_sublinear (A B ε : ℝ) (_hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ M : ℝ, ∀ m : ℝ, M ≤ m → A * Real.sqrt m + B ≤ ε * m := by
  refine ⟨max ((2 * A / ε) ^ 2) (2 * max B 0 / ε), fun m hm => ?_⟩
  have hmA : (2 * A / ε) ^ 2 ≤ m := (le_max_left _ _).trans hm
  have hmB : 2 * max B 0 / ε ≤ m := (le_max_right _ _).trans hm
  have hm0 : 0 ≤ m := (sq_nonneg _).trans hmA
  have hr := Real.le_sqrt_of_sq_le hmA
  have hA' : A ≤ ε / 2 * Real.sqrt m := by
    have h := (div_le_iff₀ hε).mp hr
    nlinarith
  have hprod := mul_le_mul_of_nonneg_right hA' (Real.sqrt_nonneg m)
  have hsq := Real.sq_sqrt hm0
  have hB' : B ≤ ε / 2 * m := by
    have h := (div_le_iff₀ hε).mp hmB
    have hmax := le_max_left B 0
    nlinarith
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SingleHistoryRates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cancellation of the single-history leaf frequency cost -/

namespace Ostmann

open Filter

/-- Unlike the two-history comparison, this cancels every leading copy
of Delta against the squared level-zero weight. -/
theorem single_leaf_frequency_cancellation (r V : ℕ) (Δ m K : ℝ)
    (hV : (V : ℝ) ≤ Real.exp (Δ + Real.sqrt m)) :
    (2 * (V : ℝ)) ^ r * Real.exp (-(r : ℝ) * Δ + K) ≤
      Real.exp ((r : ℝ) * Real.sqrt m + r * Real.log 2 + K) := by
  calc
    _ ≤ (2 * Real.exp (Δ + Real.sqrt m)) ^ r * Real.exp (-(r : ℝ) * Δ + K) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) _) (Real.exp_pos _).le
    _ = _ := by
      nth_rw 1 [show (2 : ℝ) = Real.exp (Real.log 2) by rw [Real.exp_log (by norm_num)]]
      rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

theorem single_leaf_frequency_budget_sublinear (r : ℕ) (K ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, ∀ m : ℝ, M ≤ m → ∀ Δ : ℝ, ∀ V : ℕ,
      (V : ℝ) ≤ Real.exp (Δ + Real.sqrt m) →
      (2 * (V : ℝ)) ^ r * Real.exp (-(r : ℝ) * Δ + K) ≤ Real.exp (ε * m) := by
  obtain ⟨M, hM⟩ := sqrt_cost_sublinear r (r * Real.log 2 + K) ε (by positivity) hε
  refine ⟨M, fun m hm Δ V hV => (single_leaf_frequency_cancellation r V Δ m K hV).trans ?_⟩
  apply Real.exp_le_exp.mpr
  linarith [hM m hm]

theorem single_frequency_budget_subexponential (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop, ∃ D : ℝ, 1 ≤ D ∧
      (∀ n : ℕ, n ≠ 0 → (n : ℝ) ≤ Real.exp (2 * C * m) → (n.divisors.card : ℝ) ≤ D) ∧
      (∀ N : ℕ, (N : ℝ) ≤ Real.exp (C * m) →
        4 * D ^ 3 * (1 + Real.log N) ≤ Real.exp (ε * m)) := by
  filter_upwards [frequency_budget_subexponential C ε hC hε,
    eventually_ge_atTop (0 : ℝ)] with m hm hm0
  obtain ⟨D, hD, hdiv, hcost⟩ := hm
  have hD1 : 1 ≤ D := by
    have h1 := hdiv 1 (by norm_num) (by simpa using Real.one_le_exp (mul_nonneg (by positivity) hm0))
    simpa using h1
  refine ⟨D, hD1, hdiv, fun N hN => ?_⟩
  have hL : 1 ≤ 1 + Real.log N := by linarith [Real.log_natCast_nonneg N]
  have hpD : D ^ 3 ≤ D ^ 4 := pow_le_pow_right₀ hD1 (by norm_num)
  have hpL : 1 + Real.log N ≤ (1 + Real.log N) ^ 3 := by
    simpa using pow_le_pow_right₀ hL (show 1 ≤ 3 by norm_num)
  apply le_trans _ (hcost N hN)
  calc
    _ ≤ 8 * D ^ 3 * (1 + Real.log N) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      exact mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hD 3)
    _ ≤ 8 * D ^ 4 * (1 + Real.log N) ^ 3 := by gcongr

/-- A single divisor bound works for every history and every permissible
frequency range. The numerical estimate is independent of its residue modulus. -/
theorem single_history_budget_parameters (n : ℕ) (K C ε : ℝ)
    (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop, ∃ D : ℝ, 0 ≤ D ∧
      (∀ q : ℕ, q ≠ 0 → (q : ℝ) ≤ Real.exp (2 * C * m) → (q.divisors.card : ℝ) ≤ D) ∧
      (∀ N V : ℕ, ∀ Δ : ℝ, (N : ℝ) ≤ Real.exp (C * m) →
        (V : ℝ) ≤ Real.exp (Δ + Real.sqrt m) →
        Real.exp (-(2 ^ n : ℕ) * Δ + K) *
          ((4 * D ^ 3 * (1 + Real.log N)) ^ (2 ^ n - 1) * (2 * (V : ℝ)) ^ (2 ^ n)) ≤
            Real.exp (ε * m)) := by
  let r : ℕ := 2 ^ n
  let δ : ℝ := ε / (2 * r)
  have hr : (0 : ℝ) < r := by exact_mod_cast Nat.two_pow_pos n
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδr : δ * r = ε / 2 := by dsimp [δ]; field_simp
  obtain ⟨M, hM⟩ := single_leaf_frequency_budget_sublinear r K (ε / 2) (by positivity)
  filter_upwards [single_frequency_budget_subexponential C δ hC hδ,
    eventually_ge_atTop M, eventually_ge_atTop (0 : ℝ)] with m hrate hm hm0
  obtain ⟨D, hD, hdiv, hcost⟩ := hrate
  have hD0 : 0 ≤ D := le_trans (by norm_num) hD
  refine ⟨D, hD0, hdiv, fun N V Δ hN hV => ?_⟩
  have hnode : (4 * D ^ 3 * (1 + Real.log N)) ^ (r - 1) ≤ Real.exp ((ε / 2) * m) := by
    calc
      _ ≤ Real.exp (δ * m) ^ (r - 1) := pow_le_pow_left₀ (by
        have := Real.log_natCast_nonneg N
        positivity) (hcost N hN) _
      _ = Real.exp ((r - 1 : ℕ) * (δ * m)) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hcount : ((r - 1 : ℕ) : ℝ) ≤ r := by exact_mod_cast Nat.sub_le r 1
        have hh := mul_le_mul_of_nonneg_right hcount (mul_nonneg hδ.le hm0)
        nlinarith [hδr]
  have hleaf := hM m hm Δ V hV
  calc
    _ = (4 * D ^ 3 * (1 + Real.log N)) ^ (r - 1) *
        ((2 * (V : ℝ)) ^ r * Real.exp (-(r : ℝ) * Δ + K)) := by ring
    _ ≤ Real.exp ((ε / 2) * m) * Real.exp ((ε / 2) * m) :=
      mul_le_mul hnode hleaf (by positivity) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HarmonicPriorCost
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The precise cost of replacing original bulk primes by unit residues -/

namespace Ostmann

open scoped BigOperators Classical

theorem harmonic_prior_product_cost (n : ℕ) (S : TreeLeafIndex n → Finset ℕ)
    (J : TreeLeafIndex n → ℕ) (a C L : ℝ) (ha : 0 < a)
    (hmass : ∀ i, a ≤ ∑ p ∈ S i, (p : ℝ)⁻¹)
    (hJ : ∀ i, (J i : ℝ) ≤ Real.exp (C * L)) :
    (∏ i, (∑ p ∈ S i, (p : ℝ)⁻¹)⁻¹ * (3 * J i)) ≤
      Real.exp ((2 ^ n : ℕ) * (Real.log (3 / a) + C * L)) := by
  have he : (3 / a) * Real.exp (C * L) = Real.exp (Real.log (3 / a) + C * L) := by
    rw [Real.exp_add, Real.exp_log (by positivity)]
  calc
    _ ≤ ∏ _i : TreeLeafIndex n, ((3 / a) * Real.exp (C * L)) := by
      apply Finset.prod_le_prod (fun i _ => by positivity)
      intro i _
      have hi : (∑ p ∈ S i, (p : ℝ)⁻¹)⁻¹ ≤ a⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le ha (hmass i)
      calc
        _ ≤ a⁻¹ * (3 * Real.exp (C * L)) :=
          mul_le_mul hi (mul_le_mul_of_nonneg_left (hJ i) (by norm_num))
            (by positivity) (by positivity)
        _ = _ := by ring
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, card_treeLeafIndex, he, ← Real.exp_nat_mul]

/-- Once L is at least one, the prior loss has an absolute coefficient
per leaf, independent of the transfer depth. -/
theorem harmonic_prior_product_cost_linear (n : ℕ) (S : TreeLeafIndex n → Finset ℕ)
    (J : TreeLeafIndex n → ℕ) (a C L : ℝ) (ha : 0 < a) (hL : 1 ≤ L)
    (hmass : ∀ i, a ≤ ∑ p ∈ S i, (p : ℝ)⁻¹)
    (hJ : ∀ i, (J i : ℝ) ≤ Real.exp (C * L)) :
    (∏ i, (∑ p ∈ S i, (p : ℝ)⁻¹)⁻¹ * (3 * J i)) ≤
      Real.exp ((C + max (Real.log (3 / a)) 0) * (2 ^ n : ℕ) * L) := by
  apply (harmonic_prior_product_cost n S J a C L ha hmass hJ).trans
  apply Real.exp_le_exp.mpr
  have hlog : Real.log (3 / a) ≤ max (Real.log (3 / a)) 0 * L := by
    have hh := mul_le_mul_of_nonneg_left hL (le_max_right (Real.log (3 / a)) 0)
    linarith [le_max_left (Real.log (3 / a)) 0]
  have hh := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ (2 ^ n : ℕ) by positivity)
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_HarmonicHistoryRates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The single-history arithmetic rate under the actual prime priors -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

/-- All growth and normalization hypotheses refer to the original prime
sets. The only arithmetic input is the proved bound for divisors. -/
theorem harmonic_history_support_rate (n : ℕ) (K C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop, ∀ N V : ℕ, ∀ Δ : ℝ, ∀ P : Finset ℕ, ∀ S : Finset ℤ,
      (N : ℝ) ≤ Real.exp (C * m) →
      (V : ℝ) ≤ Real.exp (Δ + Real.sqrt m) →
      (∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N) →
      ∀ Q : FrequencyTree S n → ℕ, ∀ [_hQ : ∀ t, NeZero (Q t)],
      ∀ T : TreeLeafIndex n → Finset ℕ, ∀ h J : TreeLeafIndex n → ℕ,
      ∀ hunit : ∀ t, ∀ p : P, (p : ℕ).Coprime (Q t),
      (∀ t i, Q t ≤ 2 ^ h i) →
      (∀ i p, p ∈ T i → 2 ^ h i ≤ p ∧ p < 2 ^ (h i + J i)) →
      ∀ a C₁ L : ℝ, 0 < a → 1 ≤ L →
      (∀ i, a ≤ ∑ p ∈ T i, (p : ℝ)⁻¹) →
      (∀ i, (J i : ℝ) ≤ Real.exp (C₁ * L)) →
      ∀ data : (t : FrequencyTree S n) → (ZMod (Q t))ˣ →
        List (ZMod (Q t))ˣ → Option (ArithmeticSplitData (Q t)),
      (∀ t R past d, data t R past = some d →
        d.hasFrequencies (singleTreeNodeFrequencies S n t past.length)) →
      Real.exp (-(2 ^ n : ℕ) * Δ + K) * harmonicHistorySupportSum P S V n Q T hunit data ≤
        Real.exp ((C₁ + max (Real.log (3 / a)) 0) * (2 ^ n : ℕ) * L + ε * m) := by
  filter_upwards [single_history_budget_parameters n K C ε hC hε] with m hm
  obtain ⟨D, hD, hdiv, hbudget⟩ := hm
  intro N V Δ P S hN hV hS Q _hQ T h J hunit hsmall hrange a C₁ L ha hL hmass hJ data hmatch
  have hdivN (q : ℕ) (hq : q ≠ 0) (hqN : q ≤ N ^ 2) : (q.divisors.card : ℝ) ≤ D := by
    apply hdiv q hq
    calc
      (q : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hqN
      _ ≤ Real.exp (C * m) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hN 2
      _ = Real.exp (2 * C * m) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hs := harmonic_history_support_le P S N V n D hD hS hdivN Q T h J hunit hsmall hrange data hmatch
  have hc := harmonic_prior_product_cost_linear n T J a C₁ L ha hL hmass hJ
  have hb := hbudget N V Δ hN hV
  unfold harmonicHistorySupportSum
  calc
    _ ≤ Real.exp (-(2 ^ n : ℕ) * Δ + K) *
        ((∏ i, (∑ p ∈ T i, (p : ℝ)⁻¹)⁻¹ * (3 * J i)) *
          ((4 * D ^ 3 * (1 + Real.log N)) ^ (2 ^ n - 1) * (2 * (V : ℝ)) ^ (2 ^ n))) :=
      mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
    _ = (∏ i, (∑ p ∈ T i, (p : ℝ)⁻¹)⁻¹ * (3 * J i)) *
        (Real.exp (-(2 ^ n : ℕ) * Δ + K) *
          ((4 * D ^ 3 * (1 + Real.log N)) ^ (2 ^ n - 1) * (2 * (V : ℝ)) ^ (2 ^ n))) := by ring
    _ ≤ Real.exp ((C₁ + max (Real.log (3 / a)) 0) * (2 ^ n : ℕ) * L) * Real.exp (ε * m) :=
      mul_le_mul hc hb (by
        have := Real.log_natCast_nonneg N
        positivity) (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_IntegerResidueSplit
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact integer reconstruction implies the adaptive residue test -/

namespace Ostmann

open scoped Classical

theorem intCast_frequency_zero (s : ℤ) : (s : ZMod s.natAbs) = 0 := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd s s.natAbs).mpr
  exact Int.natCast_dvd.mpr (dvd_refl _)

theorem intCast_isUnit_of_coprime_frequency (a s : ℤ) (ha : IsCoprime a s) :
    IsUnit (a : ZMod s.natAbs) := by
  have h := ha.map (Int.castRingHom (ZMod s.natAbs))
  simpa only [Int.coe_castRingHom, intCast_frequency_zero, isCoprime_zero_right] using h

theorem singleArithmeticSplitTest_toData {Q : ℕ} (d : ArithmeticResidueSplit Q)
    (x : (ZMod Q)ˣ) : singleArithmeticSplitTest d.toData x ↔ d.support x := by
  rw [← d.toData_test x]
  cases hd : d.toData <;> simp [singleArithmeticSplitTest]

/-- At a later split only the surviving residues of the previously
reconstructed coefficients are needed. Full-modulus equality is unnecessary. -/
theorem ArithmeticResidueSplit.support_of_reduced_integer_data {Q : ℕ}
    (d : ArithmeticResidueSplit Q) (x : (ZMod Q)ˣ)
    (A B l r P : ℤ) (L R : (ZMod d.frequencies.root.natAbs)ˣ)
    (hA : d.reduce d.leftFactor = A) (hB : d.reduce d.rightFactor = B)
    (hparent : ZMod.unitsMap d.frequency_dvd d.parentProduct = L * R)
    (hx : ZMod.unitsMap d.frequency_dvd x = L)
    (hL : (L : ZMod d.frequencies.root.natAbs) = l)
    (hR : (R : ZMod d.frequencies.root.natAbs) = r)
    (huA : IsCoprime A d.frequencies.root) (huB : IsCoprime B d.frequencies.root)
    (heq : d.frequencies.left * A * r - d.frequencies.right * B * l = d.frequencies.root * P) :
    d.support x := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hA]
    exact intCast_isUnit_of_coprime_frequency A d.frequencies.root huA
  · rw [hB]
    exact intCast_isUnit_of_coprime_frequency B d.frequencies.root huB
  · have hrel := congrArg (fun z : ℤ => (z : ZMod d.frequencies.root.natAbs)) heq
    simp only [Int.cast_sub, Int.cast_mul, intCast_frequency_zero, zero_mul] at hrel
    have hquot : ZMod.unitsMap d.frequency_dvd (d.parentProduct / x) = R := by
      rw [map_div, hparent, hx, mul_div_cancel_left]
    have hnum : d.reduce (d.numerator x) =
        (d.frequencies.left : ZMod d.frequencies.root.natAbs) * d.reduce d.leftFactor *
          (ZMod.unitsMap d.frequency_dvd (d.parentProduct / x) : (ZMod d.frequencies.root.natAbs)ˣ) -
        (d.frequencies.right : ZMod d.frequencies.root.natAbs) * d.reduce d.rightFactor *
          (ZMod.unitsMap d.frequency_dvd x : (ZMod d.frequencies.root.natAbs)ˣ) := by
      simp only [ArithmeticResidueSplit.reduce, ArithmeticResidueSplit.numerator,
        map_sub, map_mul, map_intCast, ZMod.unitsMap, Units.coe_map, MonoidHom.coe_coe]
    rw [hnum, hA, hB, hquot, hx, hL, hR]
    exact hrel

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_AncestorPivotPrecision
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exposed products determine all earlier ancestor pivots

A nonbulk coefficient is its fixed label product times a specified set of
inserted ancestor pivots. A division loses one power of the frequency product
along its branch, rather than one power for every node already visited.
-/

namespace Ostmann

open scoped BigOperators

theorem ancestorCoefficient_modEq {N : ℕ} (m C : ℤ) (A : Finset (Fin N))
    (p q : Fin N → ℤ) (h : ∀ i ∈ A, p i ≡ q i [ZMOD m]) :
    ancestorCoefficient C A p ≡ ancestorCoefficient C A q [ZMOD m] := by
  have hp : (∏ i ∈ A, p i) ≡ (∏ i ∈ A, q i) [ZMOD m] := by
    induction A using Finset.induction_on with
    | empty => exact .rfl
    | @insert i A hi ih =>
      simp only [Finset.prod_insert hi]
      exact (h i (Finset.mem_insert_self i A)).mul
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
  exact hp.mul_left C

/-- Among already exposed nodes, all reconstructed pivots are determined
at a precision depending only on their own ancestor depth. -/
theorem PivotDependencyScheme.pivot_prefix_precision {N : ℕ} (D : PivotDependencyScheme N)
    (R k J : ℕ) (hdepth : ∀ j, D.depth j ≤ k)
    (hs : ∀ j, (D.frequencies j).root ≠ 0)
    (hsR : ∀ j, (D.frequencies j).root.natAbs ∣ R)
    (L₁ R₁ p₁ L₂ R₂ p₂ : Fin N → ℤ)
    (heq₁ : D.equations L₁ R₁ p₁) (heq₂ : D.equations L₂ R₂ p₂)
    (hL : ∀ j, j.val < J → L₁ j ≡ L₂ j [ZMOD (R : ℤ) ^ (k + 2)])
    (hR : ∀ j, j.val < J → R₁ j ≡ R₂ j [ZMOD (R : ℤ) ^ (k + 2)]) :
    ∀ j, j.val < J → p₁ j ≡ p₂ j [ZMOD (R : ℤ) ^ (k + 1 - D.depth j)] := by
  intro j hj
  have hall : ∀ a : ℕ, ∀ j : Fin N, j.val = a → j.val < J →
      p₁ j ≡ p₂ j [ZMOD (R : ℤ) ^ (k + 1 - D.depth j)] := by
    intro a
    induction a using Nat.strong_induction_on with
    | h a ih =>
      intro j hja hj
      have hcoeff (C : ℤ) (A : Finset (Fin N))
          (hA : ∀ i ∈ A, i.val < j.val ∧ D.depth i < D.depth j) :
          ancestorCoefficient C A p₁ ≡ ancestorCoefficient C A p₂
            [ZMOD (R : ℤ) ^ (k + 2 - D.depth j)] := by
        apply ancestorCoefficient_modEq
        intro i hi
        obtain ⟨hij, hdij⟩ := hA i hi
        have hp := ih i.val (by omega) i rfl (by omega)
        exact hp.of_dvd (pow_dvd_pow (R : ℤ) (by have := hdepth i; have := hdepth j; omega))
      have hcL := hcoeff (D.fixedLeft j) (D.ancestorsLeft j) (D.earlierLeft j)
      have hcR := hcoeff (D.fixedRight j) (D.ancestorsRight j) (D.earlierRight j)
      have hlj := (hL j hj).of_dvd (pow_dvd_pow (R : ℤ) (Nat.sub_le (k + 2) (D.depth j)))
      have hrj := (hR j hj).of_dvd (pow_dvd_pow (R : ℤ) (Nat.sub_le (k + 2) (D.depth j)))
      have hnum := ((hcL.mul_left (D.frequencies j).left).mul hrj).sub
        ((hcR.mul_left (D.frequencies j).right).mul hlj)
      have hroot : (D.frequencies j).root ∣ (R : ℤ) :=
        Int.natAbs_dvd.mp (Int.natCast_dvd_natCast.mpr (hsR j))
      have hx := reversal_residue_precision (R : ℤ) (D.frequencies j).root 1 1
        ((D.frequencies j).left * D.leftCoefficient p₁ j * R₁ j -
          (D.frequencies j).right * D.rightCoefficient p₁ j * L₁ j)
        ((D.frequencies j).left * D.leftCoefficient p₂ j * R₂ j -
          (D.frequencies j).right * D.rightCoefficient p₂ j * L₂ j)
        (p₁ j) (p₂ j) (k + 1 - D.depth j) (hs j) hroot (isCoprime_one_left)
        (by simpa only [mul_one] using heq₁ j) (by simpa only [mul_one] using heq₂ j)
        (by
          have he : k + 1 - D.depth j + 1 = k + 2 - D.depth j := by have := hdepth j; omega
          rw [he]
          exact hnum) (.refl 1)
      exact hx
  exact hall j.val j rfl hj

/-- Before the current split is exposed, both coefficients are already
known modulo its root frequency. This is the measurability step needed by
the sequential uniform-root count. -/
theorem PivotDependencyScheme.coefficients_prefix_precision {N : ℕ}
    (D : PivotDependencyScheme N) (R k : ℕ) (j : Fin N)
    (hdepth : ∀ i, D.depth i ≤ k) (hs : ∀ i, (D.frequencies i).root ≠ 0)
    (hsR : ∀ i, (D.frequencies i).root.natAbs ∣ R)
    (L₁ R₁ p₁ L₂ R₂ p₂ : Fin N → ℤ)
    (heq₁ : D.equations L₁ R₁ p₁) (heq₂ : D.equations L₂ R₂ p₂)
    (hL : ∀ i, i.val < j.val → L₁ i ≡ L₂ i [ZMOD (R : ℤ) ^ (k + 2)])
    (hR : ∀ i, i.val < j.val → R₁ i ≡ R₂ i [ZMOD (R : ℤ) ^ (k + 2)]) :
    D.leftCoefficient p₁ j ≡ D.leftCoefficient p₂ j [ZMOD (D.frequencies j).root.natAbs] ∧
      D.rightCoefficient p₁ j ≡ D.rightCoefficient p₂ j [ZMOD (D.frequencies j).root.natAbs] := by
  have hp := D.pivot_prefix_precision R k j.val hdepth hs hsR L₁ R₁ p₁ L₂ R₂ p₂ heq₁ heq₂ hL hR
  have hcoeff (C : ℤ) (A : Finset (Fin N))
      (hA : ∀ i ∈ A, i.val < j.val ∧ D.depth i < D.depth j) :
      ancestorCoefficient C A p₁ ≡ ancestorCoefficient C A p₂
        [ZMOD (D.frequencies j).root.natAbs] := by
    apply ancestorCoefficient_modEq
    intro i hi
    obtain ⟨hij, _⟩ := hA i hi
    apply (hp i hij).of_dvd
    exact (Int.natCast_dvd_natCast.mpr (hsR j)).trans
      (dvd_pow_self (R : ℤ) (by have := hdepth i; omega))
  exact ⟨hcoeff _ _ (D.earlierLeft j), hcoeff _ _ (D.earlierRight j)⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ReverseAtomSources
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Distinct sources in the actual reverse atom substitution -/

namespace Ostmann
open scoped Classical

theorem reverseAtomSource_pivot {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (p : CurrentPivotConstituent role n) :
    reverseAtomSource role n b (scheduledPartitionEquiv role n (.inl p)) = none :=
  reverseCopyLabelMap_erased role n b none some _
    (copyScheduleRole_positive role p.val n p.property n)

theorem reverseAtomSource_H {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (h : CopyScheduleH role n) :
    reverseAtomSource role n b (scheduledPartitionEquiv role n (.inr (.inl h))) =
      some ⟨.inl (b, h.val), h.property⟩ :=
  reverseCopyLabelMap_copied role n b none some h

theorem reverseAtomSource_Y {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (y : CopyScheduleY role n) :
    reverseAtomSource role n b (scheduledPartitionEquiv role n (.inr (.inr y))) =
      some ⟨.inr y.val, y.property⟩ :=
  reverseCopyLabelMap_retained role n b none some y

/-- A unique pivot atom prevents any duplication in a reverse substitution.
In particular each previously inserted pivot occurs at most once in a branch. -/
theorem reverseAtomSource_injective {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool)
    (hu : ∀ i j, role i = .pivot n → role j = .pivot n → i = j) :
    Function.Injective (reverseAtomSource role n b) := by
  intro v w hvw
  obtain ⟨v, rfl⟩ := (scheduledPartitionEquiv role n).surjective v
  obtain ⟨w, rfl⟩ := (scheduledPartitionEquiv role n).surjective w
  rcases v with p | h | y <;> rcases w with q | h' | y'
  · congr 2
    exact Subtype.ext (hu p.val q.val p.property q.property)
  · rw [reverseAtomSource_pivot, reverseAtomSource_H] at hvw
    cases hvw
  · rw [reverseAtomSource_pivot, reverseAtomSource_Y] at hvw
    cases hvw
  · rw [reverseAtomSource_H, reverseAtomSource_pivot] at hvw
    cases hvw
  · rw [reverseAtomSource_H, reverseAtomSource_H] at hvw
    have he : h = h' := Subtype.ext (congrArg Prod.snd
      (Sum.inl.inj (congrArg Subtype.val (Option.some.inj hvw))))
    rw [he]
  · rw [reverseAtomSource_H, reverseAtomSource_Y] at hvw
    have he := congrArg Subtype.val (Option.some.inj hvw)
    cases he
  · rw [reverseAtomSource_Y, reverseAtomSource_pivot] at hvw
    cases hvw
  · rw [reverseAtomSource_Y, reverseAtomSource_H] at hvw
    have he := congrArg Subtype.val (Option.some.inj hvw)
    cases he
  · rw [reverseAtomSource_Y, reverseAtomSource_Y] at hvw
    have he : y = y' := Subtype.ext (Sum.inr.inj (congrArg Subtype.val (Option.some.inj hvw)))
    rw [he]

theorem reverseCopyLabelMap_source {I A : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (P : A) (x : CopyScheduleAtoms role (n + 1) → A)
    (v : CopyScheduleAtoms role n) :
    reverseCopyLabelMap role n b P x v = (reverseAtomSource role n b v).elim P x := by
  unfold reverseAtomSource reverseCopyLabelMap
  split_ifs <;> rfl

theorem reverseCopyLabelMap_injective {I A : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool)
    (hu : ∀ i j, role i = .pivot n → role j = .pivot n → i = j)
    (P : A) (current : CopyScheduleAtoms role (n + 1) → A)
    (hc : Function.Injective current) (hP : ∀ v, current v ≠ P) :
    Function.Injective (reverseCopyLabelMap role n b P current) := by
  have hmap : Function.Injective (fun z : Option (CopyScheduleAtoms role (n + 1)) => z.elim P current) := by
    intro a b h
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b => exact False.elim (hP b h.symm)
    | some a =>
      cases b with
      | none => exact False.elim (hP a h)
      | some b => exact congrArg some (hc h)
  intro v w h
  apply reverseAtomSource_injective role n b hu
  apply hmap
  simpa only [← reverseCopyLabelMap_source] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_AtomAncestorSources
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing finite ancestor products from distinct atom sources -/

namespace Ostmann
open scoped BigOperators Classical

theorem reverseCopyLabelMap_map {I A B : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (P : A) (current : CopyScheduleAtoms role (n + 1) → A)
    (f : A → B) (v : CopyScheduleAtoms role n) :
    f (reverseCopyLabelMap role n b P current v) =
      reverseCopyLabelMap role n b (f P) (fun w => f (current w)) v := by
  unfold reverseCopyLabelMap
  split_ifs <;> rfl

/-- No multiplicity bound is postulated: source injectivity gives exactly
the finite set product used by PivotDependencyScheme. -/
theorem atomSource_product {A B : Type*} [Fintype A] {d : ℕ}
    (source : A → B ⊕ Fin d) (hs : Function.Injective source)
    (C : B → ℤ) (p : Fin d → ℤ) :
    (∏ a, Sum.elim C p (source a)) =
      ancestorCoefficient (atomFixedProduct source C) (atomAncestorSet source) p := by
  rw [← Finset.prod_image (fun a _ b _ h => hs h)]
  rw [Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_AtomSourceDescent
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual reverse paths with freshly indexed ancestor pivot sources -/

namespace Ostmann
open scoped Classical

theorem advanceNatAtomSources_injective {I B : Type*} (role : I → CopyScheduleRole)
    (n d : ℕ) (b : Bool) (source : CopyScheduleAtoms role (n + 1) → B ⊕ ℕ)
    (hinj : Function.Injective source) (hs : ∀ v, AtomSourceBefore d (source v))
    (hu : ∀ i j, role i = .pivot n → role j = .pivot n → i = j) :
    Function.Injective (advanceNatAtomSources role n d b source) := by
  apply reverseCopyLabelMap_injective role n b hu _ source hinj
  intro v hv
  have h := hs v
  rw [hv] at h
  exact Nat.lt_irrefl d h

theorem descendAtomSources_injective {I B : Type*} (role : I → CopyScheduleRole)
    (h n d : ℕ) (path : Fin h → Bool) (source : CopyScheduleAtoms role (n + h) → B ⊕ ℕ)
    (hinj : Function.Injective source) (hs : ∀ v, AtomSourceBefore d (source v))
    (hu : ∀ j < n + h, ∀ a b, role a = .pivot j → role b = .pivot j → a = b) :
    Function.Injective (descendAtomSources role h n d path source) := by
  induction h generalizing d with
  | zero => exact hinj
  | succ h ih =>
    exact ih (d + 1) (Fin.tail path) _
      (advanceNatAtomSources_injective role (n + h) d (path 0) source hinj hs (hu _ (by omega)))
      (advanceNatAtomSources_before role (n + h) d (path 0) source hs)
      (fun j hj => hu j (by omega))

/-- Evaluating symbolic sources agrees exactly with the successive integer
substitutions. This equality does not discard any pivot or outside coordinate. -/
theorem descendAtomSources_eval {I B A : Type*} (role : I → CopyScheduleRole)
    (h n d : ℕ) (path : Fin h → Bool) (source : CopyScheduleAtoms role (n + h) → B ⊕ ℕ)
    (C : B → A) (p : ℕ → A) (v : CopyScheduleAtoms role n) :
    Sum.elim C p (descendAtomSources role h n d path source v) =
      descendAtomValues role h n d path p (fun w => Sum.elim C p (source w)) v := by
  induction h generalizing d with
  | zero => rfl
  | succ h ih =>
    change Sum.elim C p
      (descendAtomSources role h n (d + 1) (Fin.tail path)
        (advanceNatAtomSources role (n + h) d (path 0) source) v) = _
    rw [ih]
    congr 1
    funext w
    exact reverseCopyLabelMap_map role (n + h) (path 0) (.inr d) source (Sum.elim C p) w

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RecursiveFrequencySupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original leaf-frequency cutoffs in the recursive squared weights -/

namespace Ostmann

open scoped Classical

theorem frequencyRoot_map {A B : Type} (f : A → B) (n : ℕ) (x : FrequencyTree A n) :
    frequencyRoot n (frequencyTreeMap f n x) = f (frequencyRoot n x) := by
  cases n <;> rfl

theorem frequencyLeafWeight_map {A B : Type} (f : A → B) (W : B → ℝ)
    (n : ℕ) (x : FrequencyTree A n) :
    frequencyLeafWeight W n (frequencyTreeMap f n x) = frequencyLeafWeight (fun a => W (f a)) n x := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg₂ (· * ·) (ih x.2.1) (ih x.2.2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_PartitionMatching
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting labeled arrangements that respect paired partitions -/

namespace Ostmann

open scoped BigOperators Classical

theorem PartitionMatching.restrict_injective {A B C : Type*}
    {f : A → C} {g : B → C} :
    Function.Injective (fun e : PartitionMatching f g => e.restrict) := by
  intro e e' h
  apply Subtype.ext
  apply Equiv.ext
  intro a
  exact congrArg Subtype.val (Equiv.congr_fun (congrFun h (f a)) ⟨a, rfl⟩)

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledWordLeafCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One original word-prime coordinate at each arithmetic tree leaf -/

namespace Ostmann
open scoped BigOperators Classical

theorem wordLeafSlot_origin {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) (t : TreeLeafIndex n) :
    copyScheduleOrigin n (wordLeafSlot role i hi n t).val = i :=
  copyScheduleOrigin_path n _ i

/-- Reversal reads exactly the corresponding leaf prime; the inserted pivot
does not replace any of the chosen word coordinates. -/
theorem reverseCopyLabelMap_wordLeaf {I A : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) (b : Bool) (p : A)
    (x : CopyScheduleAtoms role (n + 1) → A) (t : TreeLeafIndex n) :
    reverseCopyLabelMap role n b p x (wordLeafSlot role i hi n t) =
      x (wordLeafSlot role i hi (n + 1) (if b then .inl t else .inr t)) := by
  have hc : (copyScheduleRole role n (wordLeafSlot role i hi n t).val).copiedAt n = true := by
    rw [wordLeafSlot_role]
    rfl
  rw [reverseCopyLabelMap, dite_eq_left hc]
  congr 1
  apply Subtype.ext
  cases b
  · exact (wordLeafSlot_right role i hi n t).symm
  · exact (wordLeafSlot_left role i hi n t).symm

theorem wordLeafPartition_leaf {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) (t : TreeLeafIndex n) :
    wordLeafPartition role i hi n (.inl t) = wordLeafSlot role i hi n t := rfl

theorem wordLeafPartition_outside {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) (v : WordLeafOutside role i hi n) :
    wordLeafPartition role i hi n (.inr v) = v.val := rfl

theorem scheduledPrimePrior_wordLeaf {I A : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word) (n : ℕ)
    (μ : I → A → ℝ) (y : WordLeafOutside role i hi n → A) (x : TreeLeafIndex n → A) :
    scheduledPrimePrior role n μ (wordLeafAssignment role i hi n y x) =
      (∏ v : WordLeafOutside role i hi n, μ (copyScheduleOrigin n v.val.val) (y v)) *
        ∏ t, μ i (x t) := by
  unfold scheduledPrimePrior
  rw [← (wordLeafPartition role i hi n).prod_comp]
  rw [Fintype.prod_sum_type]
  simp only [wordLeafPartition_leaf, wordLeafPartition_outside,
    wordLeafAssignment_leaf, wordLeafAssignment_outside, wordLeafSlot_origin]
  exact mul_comm _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledWordLeafPrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditioning on all primes except the selected original word leaves -/

namespace Ostmann
open scoped BigOperators Classical

theorem scheduled_wordLeaf_sum {I A : Type*} [Fintype I] [Fintype A]
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word) (n : ℕ)
    (μ : I → A → ℝ) (F : (CopyScheduleAtoms role n → A) → ℝ) :
    (∑ q, scheduledPrimePrior role n μ q * F q) =
      ∑ y : WordLeafOutside role i hi n → A,
        (∏ v : WordLeafOutside role i hi n, μ (copyScheduleOrigin n v.val.val) (y v)) *
          ∑ x : TreeLeafIndex n → A, (∏ t, μ i (x t)) *
            F (wordLeafAssignment role i hi n y x) := by
  rw [← (wordLeafAssignmentEquiv (A := A) role i hi n).sum_comp
    (fun q => scheduledPrimePrior role n μ q * F q)]
  simp only [Fintype.sum_prod_type, wordLeafAssignmentEquiv]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  change scheduledPrimePrior role n μ (wordLeafAssignment role i hi n y x) *
    F (wordLeafAssignment role i hi n y x) = _
  rw [scheduledPrimePrior_wordLeaf]
  ring

/-- A bound for each fixed assignment of the remaining primes averages
without any loss. The selected 2^n prime marginals remain the original ones. -/
theorem scheduled_wordLeaf_sum_le {I A D : Type*}
    [Fintype I] [Fintype A] [Fintype D]
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word) (n : ℕ)
    (μ : I → A → ℝ) (hμ : ∀ j a, 0 ≤ μ j a) (hmass : ∀ j, ∑ a, μ j a = 1)
    (F : D → (CopyScheduleAtoms role n → A) → ℝ) (B : ℝ)
    (hsection : ∀ y : WordLeafOutside role i hi n → A,
      (∑ d, ∑ x : TreeLeafIndex n → A, (∏ t, μ i (x t)) *
        F d (wordLeafAssignment role i hi n y x)) ≤ B) :
    (∑ d, ∑ q, scheduledPrimePrior role n μ q * F d q) ≤ B := by
  have hm : (∑ y : WordLeafOutside role i hi n → A,
      ∏ v : WordLeafOutside role i hi n, μ (copyScheduleOrigin n v.val.val) (y v)) = 1 := by
    rw [← Fintype.prod_sum]
    simp only [hmass, Finset.prod_const_one]
  simp_rw [scheduled_wordLeaf_sum role i hi n μ]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  calc
    _ ≤ ∑ y : WordLeafOutside role i hi n → A,
        (∏ v : WordLeafOutside role i hi n, μ (copyScheduleOrigin n v.val.val) (y v)) * B := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left (hsection y)
        (Finset.prod_nonneg (fun v _ => hμ _ _))
    _ = B := by rw [← Finset.sum_mul, hm, one_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledWordLeafProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected prime products in the two actual H branches -/

namespace Ostmann
open scoped BigOperators Classical

theorem copied_wordLeafHSlot {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) (b : Bool) (t : TreeLeafIndex n) :
    (⟨.inl (b, (wordLeafHSlot role i hi n t).val),
      (wordLeafHSlot role i hi n t).property⟩ : CopyScheduleAtoms role (n + 1)) =
      wordLeafSlot role i hi (n + 1) (if b then .inl t else .inr t) := by
  apply Subtype.ext
  cases b
  · exact (wordLeafSlot_right role i hi n t).symm
  · exact (wordLeafSlot_left role i hi n t).symm

/-- The actual H product factors into a fixed coefficient and the selected
leaf-prime product. This is an equality before any coprimality restriction. -/
theorem wordLeaf_H_product {I M : Type*} [Fintype I] [CommMonoid M]
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word) (n : ℕ) (b : Bool)
    (y : WordLeafOutside role i hi (n + 1) → M) (x : TreeLeafIndex (n + 1) → M) :
    (∏ h : CopyScheduleH role n,
      wordLeafAssignment role i hi (n + 1) y x ⟨.inl (b, h.val), h.property⟩) =
      (∏ h : WordLeafHOutside role i hi n, y (copiedWordLeafOutside role i hi n b h)) *
        ∏ t : TreeLeafIndex n, x (if b then .inl t else .inr t) := by
  rw [← (wordLeafHPartition role i hi n).prod_comp]
  rw [Fintype.prod_sum_type]
  have hleft :
      (∏ t : TreeLeafIndex n, wordLeafAssignment role i hi (n + 1) y x
        ⟨.inl (b, (wordLeafHPartition role i hi n (.inl t)).val),
          (wordLeafHPartition role i hi n (.inl t)).property⟩) =
        ∏ t : TreeLeafIndex n, x (if b then .inl t else .inr t) := by
    apply Finset.prod_congr rfl
    intro t _
    change wordLeafAssignment role i hi (n + 1) y x
      ⟨.inl (b, (wordLeafHSlot role i hi n t).val),
        (wordLeafHSlot role i hi n t).property⟩ = _
    rw [copied_wordLeafHSlot, wordLeafAssignment_leaf]
  have hright :
      (∏ h : WordLeafHOutside role i hi n, wordLeafAssignment role i hi (n + 1) y x
        ⟨.inl (b, (wordLeafHPartition role i hi n (.inr h)).val),
          (wordLeafHPartition role i hi n (.inr h)).property⟩) =
        ∏ h : WordLeafHOutside role i hi n, y (copiedWordLeafOutside role i hi n b h) := by
    apply Finset.prod_congr rfl
    intro h _
    exact wordLeafAssignment_outside role i hi (n + 1) y x
      (copiedWordLeafOutside role i hi n b h)
  rw [hleft, hright, mul_comm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedWordReversal
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reversal keeps unexposed leaf primes out of every outside coordinate -/

namespace Ostmann
open scoped Classical

theorem reverseCopyLabelMap_wordOutside_independent {I A : Type*}
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word) (n : ℕ) (b : Bool) (P : A)
    (y : WordLeafOutside role i hi (n + 1) → A)
    (x x' : TreeLeafIndex (n + 1) → A) (v : WordLeafOutside role i hi n) :
    reverseCopyLabelMap role n b P (wordLeafAssignment role i hi (n + 1) y x) v.val =
      reverseCopyLabelMap role n b P (wordLeafAssignment role i hi (n + 1) y x') v.val := by
  by_cases hc : (copyScheduleRole role n v.val.val).copiedAt n = true
  · let h : CopyScheduleH role n := ⟨v.val.val, v.val.property, hc⟩
    have hh : h ∉ Set.range (wordLeafHSlot role i hi n) := by
      rintro ⟨t, ht⟩
      apply v.property
      exact ⟨t, Subtype.ext (congrArg (fun h : CopyScheduleH role n => h.val) ht)⟩
    let z := copiedWordLeafOutside role i hi n b ⟨h, hh⟩
    rw [reverseCopyLabelMap, dite_eq_left hc, reverseCopyLabelMap, dite_eq_left hc]
    exact (wordLeafAssignment_outside role i hi (n + 1) y x z).trans
      (wordLeafAssignment_outside role i hi (n + 1) y x' z).symm
  · by_cases he : (copyScheduleRole role n v.val.val).erasedAt n = true
    · rw [reverseCopyLabelMap, dite_eq_right hc, dite_eq_left he,
        reverseCopyLabelMap, dite_eq_right hc, dite_eq_left he]
    · let z : WordLeafOutside role i hi (n + 1) :=
        ⟨⟨.inr v.val.val, v.val.property, Bool.eq_false_iff.mpr hc, Bool.eq_false_iff.mpr he⟩, by
          rintro ⟨t, ht⟩
          have hv := congrArg (fun a : CopyScheduleAtoms role (n + 1) => a.val) ht
          cases t with
          | inl t => rw [wordLeafSlot_left] at hv; cases hv
          | inr t => rw [wordLeafSlot_right] at hv; cases hv⟩
      rw [reverseCopyLabelMap, dite_eq_right hc, dite_eq_right he,
        reverseCopyLabelMap, dite_eq_right hc, dite_eq_right he]
      exact (wordLeafAssignment_outside role i hi (n + 1) y x z).trans
        (wordLeafAssignment_outside role i hi (n + 1) y x' z).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScaledWordLeaves
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selected prime factors through every actual ancestor substitution -/

namespace Ostmann
open scoped BigOperators Classical

theorem wordLeaf_reconstruct {I A : Type*}
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word) (n : ℕ)
    (base : CopyScheduleAtoms role n → A) :
    wordLeafAssignment role i hi n (fun v => base v.val)
      (fun t => base (wordLeafSlot role i hi n t)) = base := by
  funext v
  obtain ⟨v, rfl⟩ := (wordLeafPartition role i hi n).surjective v
  cases v with
  | inl t => exact wordLeafAssignment_leaf role i hi n _ _ t
  | inr v => exact wordLeafAssignment_outside role i hi n _ _ v

theorem wordLeafScale_leaf {I A : Type*} [Mul A]
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word) (n : ℕ)
    (base : CopyScheduleAtoms role n → A) (x : TreeLeafIndex n → A) (t : TreeLeafIndex n) :
    wordLeafScale role i hi n base x (wordLeafSlot role i hi n t) =
      base (wordLeafSlot role i hi n t) * x t :=
  wordLeafAssignment_leaf role i hi n _ _ t

theorem wordLeafScale_outside {I A : Type*} [Mul A]
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word) (n : ℕ)
    (base : CopyScheduleAtoms role n → A) (x : TreeLeafIndex n → A)
    (v : WordLeafOutside role i hi n) :
    wordLeafScale role i hi n base x v.val = base v.val :=
  wordLeafAssignment_outside role i hi n _ _ v

/-- The inserted pivot is unchanged; only its original selected leaves scale. -/
theorem reverseCopyLabelMap_wordLeafScale {I A : Type*} [Mul A]
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word) (n : ℕ)
    (b : Bool) (P : A) (base : CopyScheduleAtoms role (n + 1) → A)
    (x : TreeLeafIndex (n + 1) → A) :
    reverseCopyLabelMap role n b P (wordLeafScale role i hi (n + 1) base x) =
      wordLeafScale role i hi n (reverseCopyLabelMap role n b P base)
        (fun t => x (if b then .inl t else .inr t)) := by
  funext v
  obtain ⟨v, rfl⟩ := (wordLeafPartition role i hi n).surjective v
  cases v with
  | inl t =>
    rw [wordLeafPartition_leaf, reverseCopyLabelMap_wordLeaf, wordLeafScale_leaf,
      wordLeafScale_leaf, reverseCopyLabelMap_wordLeaf]
  | inr v =>
    rw [wordLeafPartition_outside, wordLeafScale_outside]
    unfold wordLeafScale
    rw [reverseCopyLabelMap_wordOutside_independent role i hi n b P
      (fun v => base v.val) _ (fun t => base (wordLeafSlot role i hi (n + 1) t)) v,
      wordLeaf_reconstruct]

/-- Unexposed prime factors follow precisely their own branches. -/
theorem descendAtomValues_wordLeafScale {I A : Type*} [Mul A]
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word)
    (h n d : ℕ) (path : Fin h → Bool) (p : ℕ → A)
    (base : CopyScheduleAtoms role (n + h) → A) (x : TreeLeafIndex (n + h) → A) :
    descendAtomValues role h n d path p (wordLeafScale role i hi (n + h) base x) =
      wordLeafScale role i hi n (descendAtomValues role h n d path p base)
        (descendLeafValues h n path x) := by
  induction h generalizing d with
  | zero => rfl
  | succ h ih =>
    change descendAtomValues role h n (d + 1) (Fin.tail path) p
      (reverseCopyLabelMap role (n + h) (path 0) (p d)
        (wordLeafScale role i hi (n + h + 1) base x)) = _
    rw [reverseCopyLabelMap_wordLeafScale, ih]
    rfl

/-- All remaining factors of the composite words stay in the coefficient. -/
theorem wordLeafScale_H_product {I A : Type*} [Fintype I] [CommMonoid A]
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word) (n : ℕ) (b : Bool)
    (base : CopyScheduleAtoms role (n + 1) → A) (x : TreeLeafIndex (n + 1) → A) :
    (∏ h : CopyScheduleH role n,
      wordLeafScale role i hi (n + 1) base x ⟨.inl (b, h.val), h.property⟩) =
      (∏ h : CopyScheduleH role n, base ⟨.inl (b, h.val), h.property⟩) *
        ∏ t : TreeLeafIndex n, x (if b then .inl t else .inr t) := by
  have hbase := wordLeaf_H_product role i hi n b
    (fun v => base v.val) (fun t => base (wordLeafSlot role i hi (n + 1) t))
  rw [wordLeaf_reconstruct] at hbase
  unfold wordLeafScale
  rw [wordLeaf_H_product, Finset.prod_mul_distrib, hbase]
  simp only [mul_assoc]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedConstituentWord
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One selected prime per composite word, under the original grouping -/

namespace Ostmann
open scoped BigOperators Classical

theorem wordLeafSlot_atom {I : Type*} (role : I → CopyScheduleRole) (size : I → ℕ)
    (i : Σ a, Fin (size a)) (hi : role i.1 = .word) (n : ℕ) (t : TreeLeafIndex n) :
    (survivingConstituentEquiv role size n
      (wordLeafSlot (fun j : Σ a, Fin (size a) => role j.1) i hi n t)).1 =
      wordLeafSlot role i.1 hi n t := by
  apply Subtype.ext
  change (copyConstituentEquiv size n (copySchedulePath n (treeLeafCopyPath n t) i)).1 = _
  rw [copyConstituentEquiv_atom, copyScheduleMap_path]
  rfl

theorem wordLeafSlot_constituent_exists {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (i : Σ a, Fin (size a)) (hi : role i.1 = .word)
    (n : ℕ) (t : TreeLeafIndex n) :
    ∃ k : Fin (size (copyScheduleOrigin n (wordLeafSlot role i.1 hi n t).val)),
      (survivingConstituentEquiv role size n).symm ⟨wordLeafSlot role i.1 hi n t, k⟩ =
        wordLeafSlot (fun j : Σ a, Fin (size a) => role j.1) i hi n t := by
  obtain ⟨⟨a, k⟩, hk⟩ := (survivingConstituentEquiv role size n).symm.surjective
    (wordLeafSlot (fun j : Σ a, Fin (size a) => role j.1) i hi n t)
  have ha := wordLeafSlot_atom role size i hi n t
  rw [← hk, Equiv.apply_symm_apply] at ha
  dsimp only at ha
  subst a
  exact ⟨k, hk⟩

theorem constituent_outside_selected_word {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (i : Σ a, Fin (size a)) (hi : role i.1 = .word) (n : ℕ)
    (a : WordLeafOutside role i.1 hi n)
    (k : Fin (size (copyScheduleOrigin n a.val.val))) :
    (survivingConstituentEquiv role size n).symm ⟨a.val, k⟩ ∉
      Set.range (wordLeafSlot (fun j : Σ b, Fin (size b) => role j.1) i hi n) := by
  rintro ⟨t, ht⟩
  apply a.property
  refine ⟨t, ?_⟩
  have ha := wordLeafSlot_atom role size i hi n t
  rw [ht, Equiv.apply_symm_apply] at ha
  exact ha.symm

theorem other_constituent_outside_selected_primes {I : Type*}
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (i : Σ a, Fin (size a)) (hi : role i.1 = .word) (n : ℕ) (t : TreeLeafIndex n)
    (k : Fin (size (copyScheduleOrigin n (wordLeafSlot role i.1 hi n t).val)))
    (hk : (survivingConstituentEquiv role size n).symm ⟨wordLeafSlot role i.1 hi n t, k⟩ =
      wordLeafSlot (fun j : Σ a, Fin (size a) => role j.1) i hi n t)
    (j : Fin (size (copyScheduleOrigin n (wordLeafSlot role i.1 hi n t).val))) (hjk : j ≠ k) :
    (survivingConstituentEquiv role size n).symm ⟨wordLeafSlot role i.1 hi n t, j⟩ ∉
      Set.range (wordLeafSlot (fun j : Σ a, Fin (size a) => role j.1) i hi n) := by
  rintro ⟨u, hu⟩
  have ha := wordLeafSlot_atom role size i hi n u
  rw [hu, Equiv.apply_symm_apply] at ha
  have hut : u = t := (wordLeafSlot role i.1 hi n).injective ha.symm
  subst u
  have he := (survivingConstituentEquiv role size n).symm.injective (hu.symm.trans hk.symm)
  exact hjk (eq_of_heq (Sigma.mk.inj_iff.mp he).2)

section
variable {I : Type*} (role : I → CopyScheduleRole) (size : I → ℕ)
variable (i : Σ a, Fin (size a)) (hi : role i.1 = .word) (n : ℕ)
variable (y : WordLeafOutside (fun j : Σ a, Fin (size a) => role j.1) i hi n → ℕ)
variable (x : TreeLeafIndex n → ℕ)

theorem grouped_wordLeaf_outside (a : WordLeafOutside role i.1 hi n) :
    ((scheduleConstituentWord role size n a.val).map
      (wordLeafAssignment (fun j : Σ a, Fin (size a) => role j.1) i hi n y x)).prod =
    ((scheduleConstituentWord role size n a.val).map
      (wordLeafAssignment (fun j : Σ a, Fin (size a) => role j.1) i hi n y (fun _ => 1))).prod := by
  rw [scheduleConstituentWord_prod, scheduleConstituentWord_prod]
  apply Finset.prod_congr rfl
  intro k _
  let z := (survivingConstituentEquiv role size n).symm ⟨a.val, k⟩
  let o : WordLeafOutside (fun j : Σ a, Fin (size a) => role j.1) i hi n :=
    ⟨z, constituent_outside_selected_word role size i hi n a k⟩
  exact (wordLeafAssignment_outside _ i hi n y x o).trans
    (wordLeafAssignment_outside _ i hi n y (fun _ => 1) o).symm

theorem grouped_wordLeaf_selected (t : TreeLeafIndex n) :
    ((scheduleConstituentWord role size n (wordLeafSlot role i.1 hi n t)).map
      (wordLeafAssignment (fun j : Σ a, Fin (size a) => role j.1) i hi n y x)).prod =
    ((scheduleConstituentWord role size n (wordLeafSlot role i.1 hi n t)).map
      (wordLeafAssignment (fun j : Σ a, Fin (size a) => role j.1) i hi n y (fun _ => 1))).prod * x t := by
  obtain ⟨k, hk⟩ := wordLeafSlot_constituent_exists role size i hi n t
  rw [scheduleConstituentWord_prod, scheduleConstituentWord_prod]
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ k, Fintype.prod_eq_mul_prod_subtype_ne _ k]
  rw [hk, wordLeafAssignment_leaf, wordLeafAssignment_leaf, one_mul]
  have he :
      (∏ j : {j : Fin (size (copyScheduleOrigin n (wordLeafSlot role i.1 hi n t).val)) // j ≠ k},
        wordLeafAssignment (fun j : Σ a, Fin (size a) => role j.1) i hi n y x
          ((survivingConstituentEquiv role size n).symm ⟨wordLeafSlot role i.1 hi n t, j.val⟩)) =
      ∏ j : {j : Fin (size (copyScheduleOrigin n (wordLeafSlot role i.1 hi n t).val)) // j ≠ k},
        wordLeafAssignment (fun j : Σ a, Fin (size a) => role j.1) i hi n y (fun _ => 1)
          ((survivingConstituentEquiv role size n).symm ⟨wordLeafSlot role i.1 hi n t, j.val⟩) := by
    apply Finset.prod_congr rfl
    intro j _
    let o : WordLeafOutside (fun j : Σ a, Fin (size a) => role j.1) i hi n :=
      ⟨_, other_constituent_outside_selected_primes role size i hi n t k hk j.val j.property⟩
    exact (wordLeafAssignment_outside _ i hi n y x o).trans
      (wordLeafAssignment_outside _ i hi n y (fun _ => 1) o).symm
  rw [he, mul_comm]

/-- Grouping introduces a fixed multiplier in each selected word, while
every other atom is independent of the unexposed selected primes. -/
theorem grouped_wordLeaf_assignment :
    (fun a : CopyScheduleAtoms role n => ((scheduleConstituentWord role size n a).map
      (wordLeafAssignment (fun j : Σ a, Fin (size a) => role j.1) i hi n y x)).prod) =
    wordLeafAssignment role i.1 hi n
      (fun a => ((scheduleConstituentWord role size n a.val).map
        (wordLeafAssignment (fun j : Σ a, Fin (size a) => role j.1) i hi n y (fun _ => 1))).prod)
      (fun t => ((scheduleConstituentWord role size n (wordLeafSlot role i.1 hi n t)).map
        (wordLeafAssignment (fun j : Σ a, Fin (size a) => role j.1) i hi n y (fun _ => 1))).prod * x t) := by
  funext a
  obtain ⟨z, rfl⟩ := (wordLeafPartition role i.1 hi n).surjective a
  cases z with
  | inl t =>
    rw [wordLeafPartition_leaf, wordLeafAssignment_leaf]
    exact grouped_wordLeaf_selected role size i hi n y x t
  | inr a =>
    rw [wordLeafPartition_outside, wordLeafAssignment_outside]
    exact grouped_wordLeaf_outside role size i hi n y x a

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentEnergyTransport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Averaging the selected-prime energy under every original constituent prior -/

namespace Ostmann
open scoped BigOperators Classical

theorem wordLeafAssignment_map {I A B : Type*}
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word) (n : ℕ)
    (y : WordLeafOutside role i hi n → A) (x : TreeLeafIndex n → A) (f : A → B) :
    (fun v => f (wordLeafAssignment role i hi n y x v)) =
      wordLeafAssignment role i hi n (fun v => f (y v)) (fun t => f (x t)) := by
  funext v
  obtain ⟨v, rfl⟩ := (wordLeafPartition role i hi n).surjective v
  cases v with
  | inl t => simp only [wordLeafPartition_leaf, wordLeafAssignment_leaf]
  | inr v => simp only [wordLeafPartition_outside, wordLeafAssignment_outside]

theorem constituent_wordLeaf_scale {I : Type*}
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (i : Σ a, Fin (size a)) (hi : role i.1 = .word) (n : ℕ)
    (y : WordLeafOutside (fun j : Σ a, Fin (size a) => role j.1) i hi n → ℕ)
    (x : TreeLeafIndex n → ℕ) :
    (fun a => ((scheduleConstituentWord role size n a).map
      (wordLeafAssignment (fun j : Σ a, Fin (size a) => role j.1) i hi n y x)).prod) =
      wordLeafScale role i.1 hi n (constituentWordLeafBase role size i hi n y) x :=
  grouped_wordLeaf_assignment role size i hi n y x

/-- Fixing all other constituent primes and applying a uniform selected-leaf
bound costs no factor. The measure is exactly the original product measure. -/
theorem constituent_energy_transport {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (i : Σ a, Fin (size a)) (hi : role i.1 = .word) (n : ℕ)
    (P : Finset ℕ) (cells : (Σ a, Fin (size a)) → Finset ℕ)
    (hsub : ∀ j, cells j ⊆ P) (hmass : ∀ j, (∑ p ∈ cells j, (p : ℝ)⁻¹) ≠ 0)
    (F : D → (CopyScheduleAtoms role n → ℕ) → ℝ) (B : ℝ)
    (hsection : ∀ base : CopyScheduleAtoms role n → ℕ,
      (∑ d, ∑ x : TreeLeafIndex n → P, (∏ t, primeSubsetPrior P (cells i) (x t)) *
        F d (wordLeafScale role i.1 hi n base (fun t => (x t : ℕ)))) ≤ B) :
    (∑ d, ∑ q : SurvivingConstituent role size n → P,
      scheduledPrimePrior (fun j : Σ a, Fin (size a) => role j.1) n
        (fun j => primeSubsetPrior P (cells j)) q *
        F d (fun a => ((scheduleConstituentWord role size n a).map (fun v => (q v : ℕ))).prod)) ≤ B := by
  apply scheduled_wordLeaf_sum_le (fun j : Σ a, Fin (size a) => role j.1) i hi n
    (fun j => primeSubsetPrior P (cells j))
    (fun j => primeSubsetPrior_nonneg P (cells j))
    (fun j => primeSubsetPrior_mass P (cells j) (hsub j) (hmass j))
  intro y
  have hb := hsection (constituentWordLeafBase role size i hi n (fun v => (y v : ℕ)))
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro x _
  congr 2
  have he := wordLeafAssignment_map (fun j : Σ a, Fin (size a) => role j.1) i hi n y x
    (fun q : P => (q : ℕ))
  simp_rw [congrFun he]
  exact constituent_wordLeaf_scale role size i hi n (fun v => (y v : ℕ)) (fun t => (x t : ℕ))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FixedPivotEnergyTransport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining selected-prime energy with an externally fixed composite pivot -/

namespace Ostmann
open scoped BigOperators Classical

/-- Replacing the current pivot never changes a selected original word prime. -/
theorem scheduledReplacePivot_wordLeafScale {I : Type*}
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word) (n M : ℕ)
    (base : CopyScheduleAtoms role n → ℕ) (x : TreeLeafIndex n → ℕ) :
    scheduledReplacePivot role n M (wordLeafScale role i hi n base x) =
      wordLeafScale role i hi n (scheduledReplacePivot role n M base) x := by
  funext v
  obtain ⟨v, rfl⟩ := (wordLeafPartition role i hi n).surjective v
  cases v with
  | inl t =>
    simp only [wordLeafPartition_leaf, scheduledReplacePivot, wordLeafSlot_role,
      CopyScheduleRole.erasedAt, Bool.false_eq_true, ↓reduceIte, wordLeafScale_leaf]
  | inr v =>
    simp only [wordLeafPartition_outside, scheduledReplacePivot, wordLeafScale_outside]

/-- The replaced assignment is exactly the original H/Y assignment with M inserted. -/
theorem scheduledReplacePivot_eq_inserted {I : Type*}
    (role : I → CopyScheduleRole) (n M : ℕ) (base : CopyScheduleAtoms role n → ℕ) :
    scheduledReplacePivot role n M base = scheduledInsertedAtoms role n M
      (fun h => base ⟨h.val, h.property.1⟩) (fun y => base ⟨y.val, y.property.1⟩) := by
  funext v
  obtain ⟨v, rfl⟩ := (scheduledPartitionEquiv role n).surjective v
  rcases v with p | h | y
  · rw [scheduledInsertedAtoms_pivot]
    simp [scheduledReplacePivot,
      copyScheduleRole_positive role p.val n p.property n, CopyScheduleRole.erasedAt]
  · change scheduledReplacePivot role n M base ⟨h.val, h.property.1⟩ = _
    rw [show scheduledInsertedAtoms role n M
        (fun h => base ⟨h.val, h.property.1⟩) (fun y => base ⟨y.val, y.property.1⟩)
        (scheduledPartitionEquiv role n (.inr (.inl h))) = base ⟨h.val, h.property.1⟩ by
      simp only [scheduledInsertedAtoms, Equiv.symm_apply_apply]]
    have he : (copyScheduleRole role n h.val).erasedAt n = false := by
      have hc := h.property.2
      cases hr : copyScheduleRole role n h.val <;>
        simp_all [CopyScheduleRole.copiedAt, CopyScheduleRole.erasedAt]
      omega
    simp only [scheduledReplacePivot, he, Bool.false_eq_true, ↓reduceIte]
  · change scheduledReplacePivot role n M base ⟨y.val, y.property.1⟩ = _
    rw [show scheduledInsertedAtoms role n M
        (fun h => base ⟨h.val, h.property.1⟩) (fun y => base ⟨y.val, y.property.1⟩)
        (scheduledPartitionEquiv role n (.inr (.inr y))) = base ⟨y.val, y.property.1⟩ by
      simp only [scheduledInsertedAtoms, Equiv.symm_apply_apply]]
    simp only [scheduledReplacePivot, y.property.2.2, Bool.false_eq_true, ↓reduceIte]

/-- The full original product prior can be retained while the pivot is fixed
externally. Its unused prime coordinates integrate out with total mass one. -/
theorem constituent_fixedPivot_energy_transport {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (i : Σ a, Fin (size a)) (hi : role i.1 = .word) (n M : ℕ)
    (P : Finset ℕ) (cells : (Σ a, Fin (size a)) → Finset ℕ)
    (hsub : ∀ j, cells j ⊆ P) (hmass : ∀ j, (∑ p ∈ cells j, (p : ℝ)⁻¹) ≠ 0)
    (F : D → (CopyScheduleAtoms role n → ℕ) → ℝ) (B : ℝ)
    (hsection : ∀ base : CopyScheduleAtoms role n → ℕ,
      (∑ d, ∑ x : TreeLeafIndex n → P, (∏ t, primeSubsetPrior P (cells i) (x t)) *
        F d (wordLeafScale role i.1 hi n base (fun t => (x t : ℕ)))) ≤ B) :
    (∑ d, ∑ q : SurvivingConstituent role size n → P,
      scheduledPrimePrior (fun j : Σ a, Fin (size a) => role j.1) n
        (fun j => primeSubsetPrior P (cells j)) q *
        F d (scheduledReplacePivot role n M
          (fun a => ((scheduleConstituentWord role size n a).map (fun v => (q v : ℕ))).prod))) ≤ B := by
  apply constituent_energy_transport role size i hi n P cells hsub hmass
    (fun d base => F d (scheduledReplacePivot role n M base)) B
  intro base
  simp_rw [scheduledReplacePivot_wordLeafScale]
  exact hsection (scheduledReplacePivot role n M base)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FixedPivotPrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact H/Y marginal after fixing the composite pivot -/

namespace Ostmann
open scoped BigOperators Classical

theorem scheduled_prior_fubini_real {I A : Type*} [Fintype I] [Fintype A]
    (role : I → CopyScheduleRole) (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n)
    (μ : CopyScheduleAtoms role n → A → ℝ) (F : (CopyScheduleAtoms role n → A) → ℝ) :
    (∑ q, (∏ i, μ i (q i)) * F q) =
      ∑ u : CopyScheduleY role n → A,
        (∏ y, μ (enumeratedPartitionEquiv role n r e (.inr (.inr y))) (u y)) *
        ∑ x : Fin r → A,
          (∏ i, μ (enumeratedPartitionEquiv role n r e (.inl i)) (x i)) *
          ∑ l : CopyScheduleH role n → A,
            (∏ h, μ (enumeratedPartitionEquiv role n r e (.inr (.inl h))) (l h)) *
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
  change (∏ i, μ i (scheduledPartitionAssignment role n r e u x l i)) *
    F (scheduledPartitionAssignment role n r e u x l) = _
  rw [scheduledPartitionAssignment_prior]
  ring

/-- Every pivot constituent is integrated out, leaving one copy of each H/Y law. -/
theorem constituent_fixedPivot_prior_fubini {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n M : ℕ) (p : I)
    (hp : role p = .pivot n) (hu : ∀ i, role i = .pivot n → i = p)
    (P : Finset ℕ) (μ : SurvivingConstituent role size n → P → ℝ)
    (hmass : ∀ i, ∑ a, μ i a = 1)
    (F : D → (CopyScheduleAtoms role n → ℕ) → ℝ) :
    (∑ d, ∑ q : SurvivingConstituent role size n → P,
      (∏ i, μ i (q i)) * F d (scheduledReplacePivot role n M
        (fun a => ((scheduleConstituentWord role size n a).map (fun v => (q v : ℕ))).prod))) =
    let e := pivotConstituentEquiv role size n p hp hu
    let ρ := fun i : Σ a, Fin (size a) => role i.1
    ∑ u : CopyScheduleY ρ n → P,
      (∏ y, μ (enumeratedPartitionEquiv ρ n (size p) e (.inr (.inr y))) (u y)) *
      ∑ l : CopyScheduleH ρ n → P,
        (∏ h, μ (enumeratedPartitionEquiv ρ n (size p) e (.inr (.inl h))) (l h)) *
        ∑ d, F d (scheduledInsertedAtoms role n M
          (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
          (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) := by
  let ρ := fun i : Σ a, Fin (size a) => role i.1
  let e := pivotConstituentEquiv role size n p hp hu
  have hgroup (u : CopyScheduleY ρ n → P) (x : Fin (size p) → P)
      (l : CopyScheduleH ρ n → P) :
      scheduledReplacePivot role n M
        (fun a => ((scheduleConstituentWord role size n a).map
          (fun v => ((scheduledPartitionAssignment (A := P) ρ n (size p) e u x l v : P) : ℕ))).prod) =
        scheduledInsertedAtoms role n M
          (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
          (fun y => ∏ k, (u (constituentY role size n y k) : ℕ)) := by
    have hmap := scheduledPartitionAssignment_map ρ n (size p) e (fun a : P => (a : ℕ)) u x l
    simp_rw [congrFun hmap]
    rw [constituent_partition_assignment role size n p hp hu]
    rw [scheduledReplacePivot_eq_inserted]
    simp_rw [scheduledInsertedAtoms_H, scheduledInsertedAtoms_Y]
    rfl
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hF := scheduled_prior_fubini_real ρ n (size p) e μ
    (fun q => ∑ d, F d (scheduledReplacePivot role n M
      (fun a => ((scheduleConstituentWord role size n a).map (fun v => (q v : ℕ))).prod)))
  refine hF.trans ?_
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  have hm : (∑ x : Fin (size p) → P,
      ∏ k, μ (enumeratedPartitionEquiv ρ n (size p) e (.inl k)) (x k)) = 1 := by
    rw [← Fintype.prod_sum]
    simp only [hmass, Finset.prod_const_one]
  simp_rw [hgroup]
  rw [← Finset.sum_mul, hm, one_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SplitPrefixProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing every current parent product from previously exposed splits -/

namespace Ostmann

theorem splitFrontierTrace_append {G : Type*} [Div G] [One G]
    (frontier : List (ℕ × G)) (xs ys : List G) :
    splitFrontierTrace frontier (xs ++ ys) = splitFrontierTrace frontier xs ++
      splitFrontierTrace (xs.foldl splitFrontierStep frontier) ys := by
  induction xs generalizing frontier with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, splitFrontierTrace, List.foldl_cons, ih]

theorem splitFrontier_after_actual {G : Type*} [CommGroup G]
    (n : ℕ) (x : TreeLeafTuple G n) (rest : List (ℕ × G)) :
    (actualSplitValues n x).foldl splitFrontierStep
      (pendingSplitBranch n (treeLeafProduct n x) rest) = rest := by
  induction n generalizing rest with
  | zero => rfl
  | succ n ih =>
    change (actualSplitValues n x.1 ++ actualSplitValues n x.2).foldl splitFrontierStep
      (pendingSplitBranch n (treeLeafProduct n x.1)
        (pendingSplitBranch n ((treeLeafProduct n x.1 * treeLeafProduct n x.2) /
          treeLeafProduct n x.1) rest)) = rest
    rw [mul_div_cancel_left, List.foldl_append, ih, ih]

theorem splitFrontierTrace_actual {G : Type*} [CommGroup G]
    (n : ℕ) (x : TreeLeafTuple G n) (rest : List (ℕ × G)) :
    splitFrontierTrace (pendingSplitBranch n (treeLeafProduct n x) rest)
      (actualSplitValues n x) = actualParentSplits n x := by
  induction n generalizing rest with
  | zero => rfl
  | succ n ih =>
    change (treeLeafProduct n x.1 * treeLeafProduct n x.2, treeLeafProduct n x.1) ::
      splitFrontierTrace (pendingSplitBranch n (treeLeafProduct n x.1)
        (pendingSplitBranch n ((treeLeafProduct n x.1 * treeLeafProduct n x.2) /
          treeLeafProduct n x.1) rest)) (actualSplitValues n x.1 ++ actualSplitValues n x.2) =
      (treeLeafProduct n x.1 * treeLeafProduct n x.2, treeLeafProduct n x.1) ::
        (actualParentSplits n x.1 ++ actualParentSplits n x.2)
    rw [mul_div_cancel_left, splitFrontierTrace_append, splitFrontier_after_actual, ih, ih]

/-- The stored prefix uses the same reverse chronological convention as
`sequentialSupport`: the most recently exposed split is the head. -/
theorem splitPrefixParent_eq_foldl {G : Type*} [Div G] [One G]
    (n : ℕ) (P : G) (past : List G) :
    splitPrefixParent n P past = currentSplitParent
      (past.reverse.foldl splitFrontierStep (pendingSplitBranch n P [])) := by
  rw [splitPrefixParent, List.foldr_eq_foldl_reverse]

theorem actualSplitValues_length {G : Type*} [CommGroup G]
    (n : ℕ) (x : TreeLeafTuple G n) : (actualSplitValues n x).length = 2 ^ n - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [actualSplitValues, List.length_cons, List.length_append, ih]
    have h := Nat.one_le_two_pow (n := n)
    rw [pow_succ]
    omega

theorem splitFrontierTrace_getD {G : Type*} [Div G] [One G]
    (frontier : List (ℕ × G)) (xs : List G) (j : ℕ) (hj : j < xs.length) :
    (splitFrontierTrace frontier xs).getD j (1, 1) =
      (currentSplitParent ((xs.take j).foldl splitFrontierStep frontier), xs.getD j 1) := by
  induction xs generalizing frontier j with
  | nil => simp at hj
  | cons x xs ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simpa only [splitFrontierTrace, List.getD_cons_succ, List.take_succ_cons, List.foldl_cons] using
        ih (splitFrontierStep frontier x) j (by simpa using hj)

/-- The actual parent product at a node is a function of the initial total
and the preceding split coordinates alone, with the same prefix convention
as the arithmetic support estimator. -/
theorem actualParentSplits_from_prefix {G : Type*} [CommGroup G]
    (n : ℕ) (x : TreeLeafTuple G n) (j : ℕ) (hj : j < 2 ^ n - 1) :
    (actualParentSplits n x).getD j (1, 1) =
      (splitPrefixParent n (treeLeafProduct n x) ((actualSplitValues n x).take j).reverse,
        (actualSplitValues n x).getD j 1) := by
  rw [← splitFrontierTrace_actual n x []]
  rw [splitFrontierTrace_getD _ _ j (by simpa only [actualSplitValues_length] using hj)]
  rw [splitPrefixParent_eq_foldl, List.reverse_reverse]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SplitSampleLists
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The checked split-coordinate equivalence records actual product splits -/

namespace Ostmann

theorem splitSampleList_cast_symm {G A : Type} (m n : ℕ) (h : m = n)
    (e : SplitSamples G m ≃ A) (he : (SplitSamples G n ≃ A) = (SplitSamples G m ≃ A)) (x : A) :
    splitSampleList n ((he.mpr e).symm x) = splitSampleList m (e.symm x) := by
  cases h
  rfl

theorem splitSampleList_cast_apply {G A : Type} (m n : ℕ) (h : m = n)
    (e : A ≃ SplitSamples G m) (he : (A ≃ SplitSamples G n) = (A ≃ SplitSamples G m)) (x : A) :
    splitSampleList n ((he.mpr e) x) = splitSampleList m (e x) := by
  cases h
  rfl

theorem splitSampleList_append {G : Type} (m n : ℕ)
    (x : SplitSamples G m) (y : SplitSamples G n) :
    splitSampleList (m + n) ((splitSamplesAppendEquiv G m n).symm (x, y)) =
      splitSampleList m x ++ splitSampleList n y := by
  induction m with
  | zero =>
    simp only [splitSamplesAppendEquiv]
    rw [splitSampleList_cast_symm n (0 + n) (Nat.zero_add n).symm]
    rfl
  | succ m ih =>
    simp only [splitSamplesAppendEquiv]
    rw [splitSampleList_cast_symm (m + n + 1) (m + 1 + n) (by omega)]
    change x.1 :: splitSampleList (m + n) ((splitSamplesAppendEquiv G m n).symm (x.2, y)) =
      (x.1 :: splitSampleList m x.2) ++ splitSampleList n y
    rw [ih]
    rfl

theorem splitSampleList_treeLeafSplit {G : Type} [CommGroup G]
    (n : ℕ) (P : G) (x : TreeLeafFiber G n P) :
    splitSampleList (2 ^ n - 1) (treeLeafSplitEquiv n P x) = actualSplitValues n x.1 := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    have hn : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have he : (2 ^ n - 1) + (2 ^ n - 1) + 1 = 2 ^ (n + 1) - 1 := by
      rw [pow_succ]
      omega
    simp only [treeLeafSplitEquiv]
    rw [splitSampleList_cast_apply _ _ he]
    change treeLeafProduct n x.1.1 ::
      splitSampleList ((2 ^ n - 1) + (2 ^ n - 1))
        ((splitSamplesAppendEquiv G (2 ^ n - 1) (2 ^ n - 1)).symm
          (treeLeafSplitEquiv n (treeLeafProduct n x.1.1) ⟨x.1.1, rfl⟩,
           treeLeafSplitEquiv n (P / treeLeafProduct n x.1.1) ⟨x.1.2, _⟩)) = _
    rw [splitSampleList_append, ih, ih]
    rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SequentialActualSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing all actual preorder node tests retains the whole support weight -/

namespace Ostmann

open scoped Classical

theorem sequentialSupport_eq_one_of_prefix {A : Type} [One A]
    (test : List A → A → Prop) (past : List A) (n : ℕ) (x : SplitSamples A n)
    (htest : ∀ j < n, test (((splitSampleList n x).take j).reverse ++ past)
      ((splitSampleList n x).getD j 1)) : sequentialSupport test past n x = 1 := by
  induction n generalizing past with
  | zero => rfl
  | succ n ih =>
    have h0 : test past x.1 := by simpa [splitSampleList] using htest 0 (by omega)
    change (if test past x.1 then sequentialSupport test (x.1 :: past) n x.2 else 0) = 1
    rw [ite_eq_left h0]
    apply ih
    intro j hj
    have ht := htest (j + 1) (by omega)
    simpa only [splitSampleList, List.take_succ_cons, List.reverse_cons,
      List.getD_cons_succ, List.append_assoc, List.singleton_append] using ht

/-- The support is evaluated on the original leaf tuple. Its tests are
checked at the actual parent/child product splits, in their true order. -/
theorem singleArithmeticLeafSupport_eq_one_of_actual_tests {Q : ℕ} [NeZero Q]
    (n : ℕ) (data : (ZMod Q)ˣ → List (ZMod Q)ˣ → Option (ArithmeticSplitData Q))
    (x : TreeLeafTuple (ZMod Q)ˣ n)
    (htest : ∀ j < 2 ^ n - 1,
      singleArithmeticSplitTest
        (data (treeLeafProduct n x) (((actualSplitValues n x).take j).reverse))
        ((actualSplitValues n x).getD j 1)) :
    singleArithmeticLeafSupport n data x = 1 := by
  unfold singleArithmeticLeafSupport
  apply sequentialSupport_eq_one_of_prefix
  intro j hj
  simpa only [List.append_nil, splitSampleList_treeLeafSplit] using htest j hj

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TreeSplitResidues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer bulk products and their exposed unit residues -/

namespace Ostmann

theorem actualChildProducts_length {G : Type*} [CommMonoid G]
    (n : ℕ) (x : TreeLeafTuple G n) : (actualChildProducts n x).length = 2 ^ n - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [actualChildProducts, List.length_cons, List.length_append, ih]
    have := Nat.one_le_two_pow (n := n)
    rw [pow_succ]
    omega

theorem actualParentSplits_childProducts {G : Type*} [CommMonoid G]
    (n : ℕ) (x : TreeLeafTuple G n) :
    actualParentSplits n x = (actualChildProducts n x).map (fun a => (a.1 * a.2, a.1)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [actualParentSplits, actualChildProducts, List.map_cons,
      List.map_append, ih, treeLeafProduct]

theorem actualChildProducts_from_prefix {G : Type} [CommGroup G]
    (n : ℕ) (x : TreeLeafTuple G n) (j : ℕ) (hj : j < 2 ^ n - 1) :
    (actualChildProducts n x).getD j (1, 1) =
      ((actualSplitValues n x).getD j 1,
        splitPrefixParent n (treeLeafProduct n x) ((actualSplitValues n x).take j).reverse /
          (actualSplitValues n x).getD j 1) := by
  have h := actualParentSplits_from_prefix n x j hj
  rw [actualParentSplits_childProducts] at h
  have hm := List.getD_map (actualChildProducts n x) (1, 1)
    (n := j) (fun a => (a.1 * a.2, a.1))
  simp only [one_mul] at hm
  rw [hm] at h
  change (((actualChildProducts n x).getD j (1, 1)).1 *
    ((actualChildProducts n x).getD j (1, 1)).2,
    ((actualChildProducts n x).getD j (1, 1)).1) = _ at h
  have hL := congrArg Prod.snd h
  have hP := congrArg Prod.fst h
  dsimp only at hL hP
  apply Prod.ext hL
  change ((actualChildProducts n x).getD j (1, 1)).2 =
    splitPrefixParent n (treeLeafProduct n x) ((actualSplitValues n x).take j).reverse /
      (actualSplitValues n x).getD j 1
  rw [← hL, ← hP, mul_div_cancel_left]

theorem treeIntegerResidues_product (Q n : ℕ) (a : TreeLeafTuple ℤ n)
    (u : TreeLeafTuple (ZMod Q)ˣ n) (h : treeIntegerResidues Q n a u) :
    ((treeLeafProduct n u : (ZMod Q)ˣ) : ZMod Q) = treeLeafProduct n a := by
  induction n with
  | zero => exact h
  | succ n ih =>
    change ((treeLeafProduct n u.1 * treeLeafProduct n u.2 : (ZMod Q)ˣ) : ZMod Q) = _
    rw [Units.val_mul, ih _ _ h.1, ih _ _ h.2]
    exact (Int.cast_mul _ _).symm

theorem treeIntegerResidues_children (Q n : ℕ) (a : TreeLeafTuple ℤ n)
    (u : TreeLeafTuple (ZMod Q)ˣ n) (h : treeIntegerResidues Q n a u) :
    (actualChildProducts n u).map (fun b => ((b.1 : ZMod Q), (b.2 : ZMod Q))) =
      (actualChildProducts n a).map (fun b => ((b.1 : ZMod Q), (b.2 : ZMod Q))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [actualChildProducts, List.map_cons, List.map_append,
      treeIntegerResidues_product Q n _ _ h.1, treeIntegerResidues_product Q n _ _ h.2,
      ih _ _ h.1, ih _ _ h.2]

theorem treeIntegerResidues_child (Q n : ℕ) (a : TreeLeafTuple ℤ n)
    (u : TreeLeafTuple (ZMod Q)ˣ n) (h : treeIntegerResidues Q n a u) (j : ℕ) :
    (((actualChildProducts n u).getD j (1, 1)).1 : ZMod Q) =
        ((actualChildProducts n a).getD j (1, 1)).1 ∧
    (((actualChildProducts n u).getD j (1, 1)).2 : ZMod Q) =
        ((actualChildProducts n a).getD j (1, 1)).2 := by
  have he := congrArg (fun l => l.getD j ((1 : ZMod Q), 1))
    (treeIntegerResidues_children Q n a u h)
  have hu := List.getD_map (actualChildProducts n u) (1, 1) (n := j)
    (fun b => ((b.1 : ZMod Q), (b.2 : ZMod Q)))
  have ha := List.getD_map (actualChildProducts n a) (1, 1) (n := j)
    (fun b => ((b.1 : ZMod Q), (b.2 : ZMod Q)))
  simp only [Units.val_one] at hu
  simp only [Int.cast_one] at ha
  rw [hu, ha] at he
  exact Prod.mk.inj he

/-- Agreement of the total and the exposed prefix fixes both child-product
residues at every earlier node, including nodes in right subtrees. -/
theorem exposed_prefix_children_eq {G : Type} [CommGroup G]
    (n : ℕ) (u v : TreeLeafTuple G n) (j : ℕ)
    (htotal : treeLeafProduct n u = treeLeafProduct n v)
    (hpast : (actualSplitValues n u).take j = (actualSplitValues n v).take j)
    (i : ℕ) (hi : i < j) (hj : j ≤ 2 ^ n - 1) :
    (actualChildProducts n u).getD i (1, 1) = (actualChildProducts n v).getD i (1, 1) := by
  have htake : (actualSplitValues n u).take i = (actualSplitValues n v).take i := by
    have ht := congrArg (List.take i) hpast
    simpa only [List.take_take, min_eq_left (Nat.le_of_lt hi)] using ht
  have hget : (actualSplitValues n u).getD i 1 = (actualSplitValues n v).getD i 1 := by
    have he := congrArg (fun l => l.getD i 1) hpast
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi] using he
  rw [actualChildProducts_from_prefix n u i (by omega),
    actualChildProducts_from_prefix n v i (by omega), htotal, htake, hget]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_AdaptivePivotCoefficients
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing coefficients from the already exposed product prefix -/

namespace Ostmann

open scoped Classical

theorem adaptivePivotCoefficients_witness (n Q : ℕ)
    (D : PivotDependencyScheme (2 ^ n - 1))
    (total : (ZMod Q)ˣ) (past : List (ZMod Q)ˣ)
    (hj : past.length < 2 ^ n - 1)
    (hex : ∃ a : SampledPivotHistory n Q, a.valid D ∧ a.matches total past) :
    ∃ a : SampledPivotHistory n Q, a.valid D ∧ a.matches total past ∧
      adaptivePivotCoefficients n Q D total past =
        ((D.leftCoefficient a.pivots ⟨past.length, hj⟩ : ZMod Q),
          (D.rightCoefficient a.pivots ⟨past.length, hj⟩ : ZMod Q)) := by
  refine ⟨Classical.choose hex, (Classical.choose_spec hex).1, (Classical.choose_spec hex).2, ?_⟩
  simp only [adaptivePivotCoefficients, dite_eq_left hj, dite_eq_left hex]

/-- Two completions of one prefix agree on the bulk products at every
previously exposed node. -/
theorem SampledPivotHistory.prefix_products {n Q : ℕ}
    (a b : SampledPivotHistory n Q) (total : (ZMod Q)ˣ) (past : List (ZMod Q)ˣ)
    (ha : a.matches total past) (hb : b.matches total past)
    (hj : past.length ≤ 2 ^ n - 1) (i : Fin (2 ^ n - 1)) (hi : i.val < past.length) :
    (a.leftProduct i : ZMod Q) = b.leftProduct i ∧
      (a.rightProduct i : ZMod Q) = b.rightProduct i := by
  have hpre : (actualSplitValues n a.residue).take past.length =
      (actualSplitValues n b.residue).take past.length := by
    exact List.reverse_injective (ha.2.trans hb.2.symm)
  have hc := exposed_prefix_children_eq n a.residue b.residue past.length
    (ha.1.trans hb.1.symm) hpre i.val hi hj
  have hca := treeIntegerResidues_child Q n a.bulk a.residue a.compatible i.val
  have hcb := treeIntegerResidues_child Q n b.bulk b.residue b.compatible i.val
  refine ⟨?_, ?_⟩
  · exact hca.1.symm.trans ((congrArg (fun p => (p.1 : ZMod Q)) hc).trans hcb.1)
  · exact hca.2.symm.trans ((congrArg (fun p => (p.2 : ZMod Q)) hc).trans hcb.2)

/-- The chosen completion gives the actual coefficients modulo the current
root frequency, even though its integer pivots may differ. -/
theorem adaptivePivotCoefficients_reduce (n R k : ℕ)
    (D : PivotDependencyScheme (2 ^ n - 1))
    (hdepth : ∀ i, D.depth i ≤ k) (hs : ∀ i, (D.frequencies i).root ≠ 0)
    (hsR : ∀ i, (D.frequencies i).root.natAbs ∣ R)
    (a : SampledPivotHistory n (R ^ (k + 2))) (ha : a.valid D)
    (total : (ZMod (R ^ (k + 2)))ˣ) (past : List (ZMod (R ^ (k + 2)))ˣ)
    (hm : a.matches total past) (hj : past.length < 2 ^ n - 1) :
    let j : Fin (2 ^ n - 1) := ⟨past.length, hj⟩
    let hd : (D.frequencies j).root.natAbs ∣ R ^ (k + 2) :=
      (hsR j).trans (dvd_pow_self R (by omega))
    ZMod.castHom hd (ZMod (D.frequencies j).root.natAbs)
        (adaptivePivotCoefficients n (R ^ (k + 2)) D total past).1 =
        D.leftCoefficient a.pivots j ∧
      ZMod.castHom hd (ZMod (D.frequencies j).root.natAbs)
        (adaptivePivotCoefficients n (R ^ (k + 2)) D total past).2 =
        D.rightCoefficient a.pivots j := by
  dsimp only
  obtain ⟨b, hb, hbm, hcoeff⟩ := adaptivePivotCoefficients_witness n (R ^ (k + 2)) D total past hj
    ⟨a, ha, hm⟩
  have hprod (i : Fin (2 ^ n - 1)) (hi : i.val < past.length) :=
    b.prefix_products a total past hbm hm (Nat.le_of_lt hj) i hi
  have hL (i : Fin (2 ^ n - 1)) (hi : i.val < past.length) :
      b.leftProduct i ≡ a.leftProduct i [ZMOD (R : ℤ) ^ (k + 2)] := by
    have h := (ZMod.intCast_eq_intCast_iff _ _ _).mp (hprod i hi).1
    simpa only [Nat.cast_pow] using h
  have hR (i : Fin (2 ^ n - 1)) (hi : i.val < past.length) :
      b.rightProduct i ≡ a.rightProduct i [ZMOD (R : ℤ) ^ (k + 2)] := by
    have h := (ZMod.intCast_eq_intCast_iff _ _ _).mp (hprod i hi).2
    simpa only [Nat.cast_pow] using h
  have h := D.coefficients_prefix_precision R k ⟨past.length, hj⟩ hdepth hs hsR
    b.leftProduct b.rightProduct b.pivots a.leftProduct a.rightProduct a.pivots hb.1 ha.1 hL hR
  rw [hcoeff]
  simp only [map_intCast]
  exact ⟨(ZMod.intCast_eq_intCast_iff _ _ _).mpr h.1,
    (ZMod.intCast_eq_intCast_iff _ _ _).mpr h.2⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_AdaptivePivotSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual integral histories pass the constructed adaptive split tests -/

namespace Ostmann

open scoped Classical

theorem adaptivePivotData_frequencies (n R k : ℕ)
    (D : PivotDependencyScheme (2 ^ n - 1))
    (hs : ∀ i, (D.frequencies i).root ≠ 0)
    (hsR : ∀ i, (D.frequencies i).root.natAbs ∣ R)
    (total : (ZMod (R ^ (k + 2)))ˣ) (past : List (ZMod (R ^ (k + 2)))ˣ)
    (hj : past.length < 2 ^ n - 1) (d : ArithmeticSplitData (R ^ (k + 2)))
    (hd : adaptivePivotData n R k D hs hsR total past = some d) :
    d.hasFrequencies (D.frequencies ⟨past.length, hj⟩) := by
  rw [adaptivePivotData, dite_eq_left hj] at hd
  exact ArithmeticResidueSplit.toData_frequencies _ _ hd

theorem SampledPivotHistory.matches_actual {n Q : ℕ} (a : SampledPivotHistory n Q)
    (j : ℕ) (hj : j ≤ 2 ^ n - 1) :
    a.matches (treeLeafProduct n a.residue) ((actualSplitValues n a.residue).take j).reverse := by
  constructor
  · rfl
  · simp only [List.length_reverse, List.length_take, actualSplitValues_length,
      min_eq_left hj]

/-- A valid actual history passes every test. The coefficients in that test
were constructed using only the root product and the preceding split prefix. -/
theorem adaptivePivotData_actual_test (n R k : ℕ)
    (D : PivotDependencyScheme (2 ^ n - 1))
    (hdepth : ∀ i, D.depth i ≤ k) (hs : ∀ i, (D.frequencies i).root ≠ 0)
    (hsR : ∀ i, (D.frequencies i).root.natAbs ∣ R)
    (a : SampledPivotHistory n (R ^ (k + 2))) (ha : a.valid D)
    (j : ℕ) (hj : j < 2 ^ n - 1) :
    singleArithmeticSplitTest
      (adaptivePivotData n R k D hs hsR (treeLeafProduct n a.residue)
        ((actualSplitValues n a.residue).take j).reverse)
      ((actualSplitValues n a.residue).getD j 1) := by
  let total := treeLeafProduct n a.residue
  let past := ((actualSplitValues n a.residue).take j).reverse
  have hlen : past.length = j := by
    simp only [past, List.length_reverse, List.length_take, actualSplitValues_length,
      min_eq_left (Nat.le_of_lt hj)]
  have hj' : past.length < 2 ^ n - 1 := by omega
  let d := adaptivePivotResidueSplit n R k D hs hsR total past hj'
  change singleArithmeticSplitTest (adaptivePivotData n R k D hs hsR total past) _
  rw [adaptivePivotData, dite_eq_left hj', singleArithmeticSplitTest_toData]
  change d.support _
  let i : Fin (2 ^ n - 1) := ⟨past.length, hj'⟩
  let c := (actualChildProducts n a.residue).getD j (1, 1)
  have hc := actualChildProducts_from_prefix n a.residue j hj
  have hcL : c.1 = (actualSplitValues n a.residue).getD j 1 := congrArg Prod.fst hc
  have hcP : splitPrefixParent n total past = c.1 * c.2 := by
    rw [show c = ((actualSplitValues n a.residue).getD j 1,
      splitPrefixParent n total past / (actualSplitValues n a.residue).getD j 1) from hc]
    dsimp only
    rw [mul_comm, div_mul_cancel]
  have hcoeff := adaptivePivotCoefficients_reduce n R k D hdepth hs hsR a ha
    total past (a.matches_actual j (Nat.le_of_lt hj)) hj'
  have hci := treeIntegerResidues_child (R ^ (k + 2)) n a.bulk a.residue a.compatible j
  have hL : (c.1 : ZMod (R ^ (k + 2))) = a.leftProduct i := by
    simpa only [c, SampledPivotHistory.leftProduct, i, hlen] using hci.1
  have hR : (c.2 : ZMod (R ^ (k + 2))) = a.rightProduct i := by
    simpa only [c, SampledPivotHistory.rightProduct, i, hlen] using hci.2
  apply d.support_of_reduced_integer_data _
    (D.leftCoefficient a.pivots i) (D.rightCoefficient a.pivots i)
    (a.leftProduct i) (a.rightProduct i) (a.pivots i)
    (ZMod.unitsMap d.frequency_dvd c.1) (ZMod.unitsMap d.frequency_dvd c.2)
  · exact hcoeff.1
  · exact hcoeff.2
  · change ZMod.unitsMap d.frequency_dvd (splitPrefixParent n total past) = _
    rw [hcP, map_mul]
  · rw [← hcL]
  · change ZMod.castHom d.frequency_dvd _ (c.1 : ZMod (R ^ (k + 2))) = _
    rw [hL, map_intCast]
  · change ZMod.castHom d.frequency_dvd _ (c.2 : ZMod (R ^ (k + 2))) = _
    rw [hR, map_intCast]
  · exact (ha.2 i).1
  · exact (ha.2 i).2
  · exact ha.1 i

/-- The entire original residue tuple remains in the arithmetic support. -/
theorem adaptivePivotData_actual_support (n R k : ℕ) [NeZero (R ^ (k + 2))]
    (D : PivotDependencyScheme (2 ^ n - 1))
    (hdepth : ∀ i, D.depth i ≤ k) (hs : ∀ i, (D.frequencies i).root ≠ 0)
    (hsR : ∀ i, (D.frequencies i).root.natAbs ∣ R)
    (a : SampledPivotHistory n (R ^ (k + 2))) (ha : a.valid D) :
    singleArithmeticLeafSupport n (adaptivePivotData n R k D hs hsR) a.residue = 1 := by
  apply singleArithmeticLeafSupport_eq_one_of_actual_tests
  exact adaptivePivotData_actual_test n R k D hdepth hs hsR a ha

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SampledHistoryEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The squared-history sum with its constructed arithmetic support -/

namespace Ostmann

open scoped BigOperators Classical

theorem sampledPrimeHistory_residue (P : Finset ℕ) (Q n : ℕ)
    (hunit : ∀ p : P, (p : ℕ).Coprime Q) (x : TreeLeafIndex n → P)
    (pivots : Fin (2 ^ n - 1) → ℤ) :
    (sampledPrimeHistory P Q n hunit x pivots).residue =
      (treeLeafTupleEquiv (ZMod Q)ˣ n).symm (fun i => ZMod.unitOfCoprime (x i : ℕ) (hunit (x i))) := by
  apply (treeLeafTupleEquiv (ZMod Q)ˣ n).injective
  funext i
  simp only [sampledPrimeHistory, treeLeafTupleEquiv_map, Equiv.apply_symm_apply]

/-- No new support probability is assumed: it is computed from the literal
integer reversal equations of each nonzero sampled history. -/
theorem sampled_history_square_sum_le (P : Finset ℕ) (S : Finset ℤ) (V n k : ℕ)
    (R : FrequencyTree S n → ℕ) [∀ t, NeZero (R t ^ (k + 2))]
    (D : FrequencyTree S n → PivotDependencyScheme (2 ^ n - 1))
    (hdepth : ∀ t i, (D t).depth i ≤ k)
    (hs : ∀ t i, ((D t).frequencies i).root ≠ 0)
    (hsR : ∀ t i, ((D t).frequencies i).root.natAbs ∣ R t)
    (T : TreeLeafIndex n → Finset ℕ)
    (hunit : ∀ t, ∀ p : P, (p : ℕ).Coprime (R t ^ (k + 2)))
    (pivots : FrequencyTree S n → (TreeLeafIndex n → P) → Fin (2 ^ n - 1) → ℤ)
    (W : FrequencyTree S n → (TreeLeafIndex n → P) → ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hsize : ∀ t x, ‖W t x‖ ^ 2 ≤ B * frequencyLeafWeight (singleFrequencyLeaf S V) n t)
    (hvalid : ∀ t x, W t x ≠ 0 →
      (sampledPrimeHistory P (R t ^ (k + 2)) n (hunit t) x (pivots t x)).valid (D t)) :
    (∑ t, ∑ x, (∏ i, primeSubsetPrior P (T i) (x i)) * ‖W t x‖ ^ 2) ≤
      B * harmonicHistorySupportSum P S V n (fun t => R t ^ (k + 2)) T hunit
        (fun t => adaptivePivotData n (R t) k (D t) (hs t) (hsR t)) := by
  unfold harmonicHistorySupportSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  rw [← mul_assoc, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  have hμ : 0 ≤ ∏ i, primeSubsetPrior P (T i) (x i) :=
    Finset.prod_nonneg (fun i _ => primeSubsetPrior_nonneg P (T i) (x i))
  by_cases hw : W t x = 0
  · simp only [hw, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
    exact mul_nonneg (mul_nonneg hB (frequencyLeafWeight_nonneg _
      (fun _ => by unfold singleFrequencyLeaf; split_ifs <;> norm_num) n t))
      (mul_nonneg hμ (singleArithmeticLeafSupport_nonneg n _ _))
  · have hp := adaptivePivotData_actual_support n (R t) k (D t) (hdepth t) (hs t) (hsR t)
      (sampledPrimeHistory P (R t ^ (k + 2)) n (hunit t) x (pivots t x)) (hvalid t x hw)
    rw [sampledPrimeHistory_residue] at hp
    rw [hp, mul_one]
    calc
      _ ≤ (∏ i, primeSubsetPrior P (T i) (x i)) *
          (B * frequencyLeafWeight (singleFrequencyLeaf S V) n t) :=
        mul_le_mul_of_nonneg_left (hsize t x) hμ
      _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SampledHistoryRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-prior squared-history rate from integer reversals -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem adaptivePivotData_history_frequencies (S : Finset ℤ) (n R k : ℕ)
    (t : FrequencyTree S n) (D : PivotDependencyScheme (2 ^ n - 1))
    (hs : ∀ i, (D.frequencies i).root ≠ 0)
    (hsR : ∀ i, (D.frequencies i).root.natAbs ∣ R)
    (hfreq : ∀ i, D.frequencies i = singleTreeNodeFrequencies S n t i.val)
    (total : (ZMod (R ^ (k + 2)))ˣ) (past : List (ZMod (R ^ (k + 2)))ˣ)
    (d : ArithmeticSplitData (R ^ (k + 2)))
    (hd : adaptivePivotData n R k D hs hsR total past = some d) :
    d.hasFrequencies (singleTreeNodeFrequencies S n t past.length) := by
  by_cases hj : past.length < 2 ^ n - 1
  · have h := adaptivePivotData_frequencies n R k D hs hsR total past hj d hd
    rwa [hfreq] at h
  · simp only [adaptivePivotData, hj, dite_false] at hd
    cases hd

/-- This is the squared-history estimate with actual prime sampling and
actual integer integrality/unit conditions. The adaptive-support event is
constructed, and is not an additional hypothesis. -/
theorem sampled_history_square_rate (n k : ℕ) (K C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop, ∀ N V : ℕ, ∀ Δ : ℝ, ∀ P : Finset ℕ, ∀ S : Finset ℤ,
      (N : ℝ) ≤ Real.exp (C * m) →
      (V : ℝ) ≤ Real.exp (Δ + Real.sqrt m) →
      (∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N) →
      ∀ R : FrequencyTree S n → ℕ, ∀ [_hQ : ∀ t, NeZero (R t ^ (k + 2))],
      ∀ D : FrequencyTree S n → PivotDependencyScheme (2 ^ n - 1),
      (∀ t i, (D t).depth i ≤ k) →
      ∀ _hs : ∀ t i, ((D t).frequencies i).root ≠ 0,
      ∀ _hsR : ∀ t i, ((D t).frequencies i).root.natAbs ∣ R t,
      (∀ t i, (D t).frequencies i = singleTreeNodeFrequencies S n t i.val) →
      ∀ T : TreeLeafIndex n → Finset ℕ, ∀ h J : TreeLeafIndex n → ℕ,
      ∀ hunit : ∀ t, ∀ p : P, (p : ℕ).Coprime (R t ^ (k + 2)),
      (∀ t i, R t ^ (k + 2) ≤ 2 ^ h i) →
      (∀ i p, p ∈ T i → 2 ^ h i ≤ p ∧ p < 2 ^ (h i + J i)) →
      ∀ a C₁ L : ℝ, 0 < a → 1 ≤ L →
      (∀ i, a ≤ ∑ p ∈ T i, (p : ℝ)⁻¹) →
      (∀ i, (J i : ℝ) ≤ Real.exp (C₁ * L)) →
      ∀ pivots : FrequencyTree S n → (TreeLeafIndex n → P) → Fin (2 ^ n - 1) → ℤ,
      ∀ W : FrequencyTree S n → (TreeLeafIndex n → P) → ℂ,
      (∀ t x, ‖W t x‖ ^ 2 ≤ Real.exp (-(2 ^ n : ℕ) * Δ + K) *
        frequencyLeafWeight (singleFrequencyLeaf S V) n t) →
      (∀ t x, W t x ≠ 0 →
        (sampledPrimeHistory P (R t ^ (k + 2)) n (hunit t) x (pivots t x)).valid (D t)) →
      (∑ t, ∑ x, (∏ i, primeSubsetPrior P (T i) (x i)) * ‖W t x‖ ^ 2) ≤
        Real.exp ((C₁ + max (Real.log (3 / a)) 0) * (2 ^ n : ℕ) * L + ε * m) := by
  filter_upwards [harmonic_history_support_rate n K C ε hC hε] with m hm
  intro N V Δ P S hN hV hS R _hQ D hdepth hs hsR hfreq T h J hunit hsmall hrange
    a C₁ L ha hL hmass hJ pivots W hsize hvalid
  have hb := sampled_history_square_sum_le P S V n k R D hdepth hs hsR T hunit pivots W
    (Real.exp (-(2 ^ n : ℕ) * Δ + K)) (Real.exp_pos _).le hsize hvalid
  exact hb.trans (hm N V Δ P S hN hV hS (fun t => R t ^ (k + 2)) T h J hunit hsmall hrange
    a C₁ L ha hL hmass hJ (fun t => adaptivePivotData n (R t) k (D t) (hs t) (hsR t))
    (fun t => adaptivePivotData_history_frequencies S n (R t) k t (D t) (hs t) (hsR t) (hfreq t)))

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledHistoryEmbedding
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Embedding the actual varying-cutoff histories without adding bottom frequencies -/

namespace Ostmann
open scoped BigOperators Classical

theorem scheduledHistoryEmbedding_map (V : ℕ → ℕ) (hV : Monotone V) (n : ℕ)
    (a : NonzeroScheduledHistory V n) :
    frequencyTreeMap Subtype.val n (scheduledHistoryEmbedding V hV n a) =
      scheduledFrequencyHistory V n a.val :=
  frequencyTreeInFinset_map _ _ _ _

theorem scheduledFrequencyHistory_leaf_cutoff (V : ℕ → ℕ) (n : ℕ)
    (a : ScheduledFrequencyIndex V n) :
    frequencyLeafWeight (fun v : ℤ => if v.natAbs ≤ V 0 then (1 : ℝ) else 0)
      n (scheduledFrequencyHistory V n a) = 1 := by
  induction n with
  | zero =>
    exact ite_eq_left (scheduledFrequencyHistory_root_bound V 0 a)
  | succ n ih =>
    change frequencyLeafWeight _ n (scheduledFrequencyHistory V n a.2.1) *
      frequencyLeafWeight _ n (scheduledFrequencyHistory V n a.2.2) = 1
    rw [ih, ih, mul_one]

theorem scheduledHistoryEmbedding_leaf_cutoff (V : ℕ → ℕ) (hV : Monotone V) (n : ℕ)
    (a : NonzeroScheduledHistory V n) :
    frequencyLeafWeight (singleFrequencyLeaf ((transferFrequencyRange (V n)).erase 0) (V 0))
      n (scheduledHistoryEmbedding V hV n a) = 1 := by
  have h := scheduledFrequencyHistory_leaf_cutoff V n a.val
  rw [← scheduledHistoryEmbedding_map V hV n a, frequencyLeafWeight_map] at h
  exact h

/-- Only internal frequencies are enlarged to the largest cutoff. Zero
frequencies contribute nothing, and every bottom frequency keeps cutoff V 0. -/
theorem scheduled_history_sum_le (V : ℕ → ℕ) (hV : Monotone V) (n : ℕ)
    (F : FrequencyTree ℤ n → ℝ) (hF : ∀ t, 0 ≤ F t)
    (hzero : ∀ a : ScheduledFrequencyIndex V n,
      ¬(∀ s ∈ allFrequencyList n (scheduledFrequencyHistory V n a), s ≠ 0) →
        F (scheduledFrequencyHistory V n a) = 0) :
    (∑ a, F (scheduledFrequencyHistory V n a)) ≤
      ∑ t : FrequencyTree ((transferFrequencyRange (V n)).erase 0) n,
        if frequencyLeafWeight (singleFrequencyLeaf ((transferFrequencyRange (V n)).erase 0)
          (V 0)) n t = 1 then F (frequencyTreeMap Subtype.val n t) else 0 := by
  let p := fun a : ScheduledFrequencyIndex V n =>
    ∀ s ∈ allFrequencyList n (scheduledFrequencyHistory V n a), s ≠ 0
  have hz : (∑ a : {a // ¬p a}, F (scheduledFrequencyHistory V n a.val)) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    exact hzero a.val a.property
  have hs := Fintype.sum_subtype_add_sum_subtype p
    (fun a => F (scheduledFrequencyHistory V n a))
  rw [hz, add_zero] at hs
  rw [← hs]
  let e := scheduledHistoryEmbedding V hV n
  let G := fun t : FrequencyTree ((transferFrequencyRange (V n)).erase 0) n =>
    if frequencyLeafWeight (singleFrequencyLeaf ((transferFrequencyRange (V n)).erase 0)
      (V 0)) n t = 1 then F (frequencyTreeMap Subtype.val n t) else 0
  have he (a : NonzeroScheduledHistory V n) : G (e a) = F (scheduledFrequencyHistory V n a.val) := by
    dsimp only [G, e]
    rw [scheduledHistoryEmbedding_leaf_cutoff, ite_eq_left rfl, scheduledHistoryEmbedding_map]
  change (∑ a : NonzeroScheduledHistory V n, F (scheduledFrequencyHistory V n a.val)) ≤ ∑ t, G t
  simp_rw [← he]
  rw [← Finset.sum_map]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
    intro t _ _
    dsimp only [G]
    split_ifs
    · exact hF _
    · exact le_rfl)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledFourierEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual Fourier energy with the original bottom-frequency cutoff -/

namespace Ostmann
open scoped BigOperators Classical SchwartzMap FourierTransform

theorem clippedFullAtomFourierWeight_square_le {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi Δ C K : ℝ) (hX : 0 < X)
    (hlo : Real.exp (Δ - C) ≤ lo)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K)
    (S : Finset ℤ) (V n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree S n) :
    ‖clippedFullAtomFourierWeight role childBound pivotBound ranges ψ X lo hi S V n x t‖ ^ 2 ≤
      Real.exp (-(2 ^ n : ℕ) * Δ + (2 ^ n : ℕ) * (C + 2 * K)) *
        frequencyLeafWeight (singleFrequencyLeaf S V) n t := by
  unfold clippedFullAtomFourierWeight
  split_ifs with hcut
  · rw [hcut, mul_one]
    exact fullAtomFourierWeight_square_exp_le role childBound pivotBound ranges
      ψ X lo hi Δ C K hX hlo hψ n x _
  · simp only [norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact mul_nonneg (Real.exp_pos _).le (frequencyLeafWeight_nonneg _
      (fun _ => by unfold singleFrequencyLeaf; split_ifs <;> norm_num) n t)

/-- Extending the internal frequency sets costs no multiplicity. All original
prime laws, bottom cutoffs and recursive support conditions remain in the sum. -/
theorem scheduled_full_fourier_energy_le {I A : Type*} [Fintype I] [Fintype A]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hX : 0 < X) (hlo : 1 < X * lo)
    (V : ℕ → ℕ) (hV : Monotone V) (n : ℕ)
    (μ : A → ℝ) (hμ : ∀ q, 0 ≤ μ q) (values : A → CopyScheduleAtoms role n → ℕ) :
    (∑ a : ScheduledFrequencyIndex V n, ∑ q, μ q *
      ‖fullAtomTransferWeight role childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo hi)
        n (values q) (scheduledFrequencyHistory V n a)‖ ^ 2) ≤
      ∑ t : FrequencyTree ((transferFrequencyRange (V n)).erase 0) n, ∑ q, μ q *
        ‖clippedFullAtomFourierWeight role childBound pivotBound ranges ψ X lo hi
          ((transferFrequencyRange (V n)).erase 0) (V 0) n (values q) t‖ ^ 2 := by
  have h := scheduled_history_sum_le V hV n
    (fun t => ∑ q, μ q * ‖fullAtomTransferWeight role childBound pivotBound ranges
      (scheduleFourierLeaf role ψ X lo hi) n (values q) t‖ ^ 2)
    (fun _ => Finset.sum_nonneg (fun q _ => mul_nonneg (hμ q) (sq_nonneg _)))
    (fun a ha => ?_)
  · apply h.trans_eq
    apply Finset.sum_congr rfl
    intro t _
    unfold clippedFullAtomFourierWeight
    split_ifs with hcut
    · rfl
    · simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero]
  · apply Finset.sum_eq_zero
    intro q _
    have hz : fullAtomTransferWeight role childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo hi) n (values q) (scheduledFrequencyHistory V n a) = 0 := by
      by_contra hw
      exact ha (fullAtomFourierWeight_all_frequencies_ne_zero role childBound pivotBound ranges
        ψ X lo hi hX hlo n (values q) _ hw)
    rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PreorderTransferPaths
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual reconstructed node at a preorder path -/

namespace Ostmann
open scoped Classical

/-- Path lookup and the literal preorder list name the same node. -/
theorem transferNodeList_get_path {State : Type*} (sys : TransferHistorySystem State)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) (path : List Bool)
    (hp : path.length < n) (fallback : ReconstructedTransferNode State) :
    (transferNodeList sys n σ t).getD (nodePathIndex n path) fallback =
      transferNodeAtPath sys n σ t path := by
  induction n generalizing σ path with
  | zero => simp at hp
  | succ n ih =>
    cases path with
    | nil => rfl
    | cons b path =>
      have hp' : path.length < n := by simpa using hp
      have hidx := nodePathIndex_lt n path hp'
      have hpow := Nat.one_le_two_pow (n := n)
      cases b
      · simp only [nodePathIndex, Bool.false_eq_true, ite_false, if_false, transferNodeList]
        rw [show 1 + nodePathIndex n path = nodePathIndex n path + 1 by omega,
          List.getD_cons_succ, List.getD_append _ _ _ _ (by
            rw [transferNodeList_length]; exact hidx)]
        exact ih _ _ path hp'
      · simp only [nodePathIndex, ite_true, if_true, transferNodeList]
        rw [show 2 ^ n + nodePathIndex n path = (2 ^ n - 1 + nodePathIndex n path) + 1 by omega,
          List.getD_cons_succ, List.getD_append_right _ _ _ _ (by
            rw [transferNodeList_length]; omega), transferNodeList_length]
        rw [show 2 ^ n - 1 + nodePathIndex n path - (2 ^ n - 1) = nodePathIndex n path by omega]
        exact ih _ _ path hp'

theorem transferNodeAtPath_valid {State : Type*} (sys : TransferHistorySystem State)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n)
    (hv : ValidTransferHistory sys n σ t) (path : List Bool) (hp : path.length < n) :
    (transferNodeAtPath sys n σ t path).Valid sys := by
  apply (validTransferHistory_nodeList_iff sys n σ t).mp hv
  rw [← transferNodeList_get_path sys n σ t path hp (transferNodeAtPath sys n σ t path)]
  rw [List.getD_eq_getElem _ _ (by rw [transferNodeList_length]; exact nodePathIndex_lt n path hp)]
  exact List.getElem_mem _

/-- The node's state is obtained by substituting just its proper ancestor
pivots, in their root-to-leaf order. -/
theorem replayNodeIndices_actual {State : Type*} (sys : TransferHistorySystem State)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) (path : List Bool)
    (hp : path.length < n) (d : ℕ) (p : ℕ → ℕ)
    (hanc : ∀ k < path.length, p (d + k) =
      (transferNodeAtPath sys n σ t (path.take k)).pivot sys) :
    replayNodeIndices sys path d p σ = (transferNodeAtPath sys n σ t path).state := by
  induction n generalizing σ path d with
  | zero => simp at hp
  | succ n ih =>
    cases path with
    | nil => rfl
    | cons b path =>
      have hp' : path.length < n := by simpa using hp
      have hroot : p d = historyPivot sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) := by
        simpa only [Nat.add_zero, List.take_zero, transferNodeAtPath,
          ReconstructedTransferNode.pivot] using hanc 0 (by simp)
      cases b
      · simp only [replayNodeIndices, Bool.false_eq_true, ite_false, if_false, transferNodeAtPath]
        rw [hroot]
        apply ih _ _ path hp' (d + 1)
        intro k hk
        have hh := hanc (k + 1) (by simpa using Nat.add_lt_add_right hk 1)
        simpa only [Nat.add_assoc, Nat.add_comm 1 k, List.take_succ_cons,
          transferNodeAtPath, Bool.false_eq_true, ite_false, if_false] using hh
      · simp only [replayNodeIndices, ite_true, if_true, transferNodeAtPath]
        rw [hroot]
        apply ih _ _ path hp' (d + 1)
        intro k hk
        have hh := hanc (k + 1) (by simpa using Nat.add_lt_add_right hk 1)
        simpa only [Nat.add_assoc, Nat.add_comm 1 k, List.take_succ_cons,
          transferNodeAtPath, ite_true, if_true] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SingleFrequencyModulus
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The modulus attached to one fixed frequency history -/

namespace Ostmann

open scoped BigOperators Classical

theorem historyFrequencyProduct_pos (S : Finset ℤ) (hS : ∀ s ∈ S, s ≠ 0)
    (n : ℕ) (t : FrequencyTree S n) : 0 < historyFrequencyProduct S n t := by
  induction n with
  | zero => exact Int.natAbs_pos.mpr (hS _ t.property)
  | succ n ih =>
      exact Nat.mul_pos
        (Nat.mul_pos (Int.natAbs_pos.mpr (hS _ t.1.property)) (ih _)) (ih _)

theorem historyFrequencyModulus_pos (S : Finset ℤ) (hS : ∀ s ∈ S, s ≠ 0)
    (n k : ℕ) (t : FrequencyTree S n) : 0 < historyFrequencyModulus S n k t :=
  pow_pos (historyFrequencyProduct_pos S hS n t) _

theorem historyFrequencyProduct_le (S : Finset ℤ) (N : ℕ)
    (hS : ∀ s ∈ S, s.natAbs ≤ N) (n : ℕ) (t : FrequencyTree S n) :
    historyFrequencyProduct S n t ≤ N ^ (2 ^ (n + 1) - 1) := by
  induction n with
  | zero => simpa [historyFrequencyProduct] using hS _ t.property
  | succ n ih =>
    have he : 2 ^ (n + 1 + 1) - 1 = 1 + (2 ^ (n + 1) - 1) + (2 ^ (n + 1) - 1) := by
      have hp : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
      rw [pow_succ]
      omega
    calc
      _ ≤ N * N ^ (2 ^ (n + 1) - 1) * N ^ (2 ^ (n + 1) - 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul (hS _ t.1.property) (ih _)) (ih _)
      _ = _ := by rw [he]; simp only [pow_add, pow_one]

theorem historyFrequencyModulus_le (S : Finset ℤ) (N : ℕ)
    (hS : ∀ s ∈ S, s.natAbs ≤ N) (n k : ℕ) (t : FrequencyTree S n) :
    historyFrequencyModulus S n k t ≤ N ^ ((2 ^ (n + 1) - 1) * (k + 2)) := by
  simpa only [historyFrequencyModulus, pow_mul] using
    Nat.pow_le_pow_left (historyFrequencyProduct_le S N hS n t) (k + 2)

theorem history_node_dvd_frequencyProduct (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (f : NodeFrequencies) (hf : f ∈ singleFrequencySplitList S n t) :
    f.root.natAbs ∣ historyFrequencyProduct S n t := by
  induction n with
  | zero => simp [singleFrequencySplitList] at hf
  | succ n ih =>
    simp only [singleFrequencySplitList, List.mem_cons, List.mem_append] at hf
    rcases hf with rfl | hf | hf
    · exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (ih _ hf) _) _
    · exact dvd_mul_of_dvd_right (ih _ hf) _

/-- All actual primes exceed the frequency range. Consequently they are
units for the full history modulus, including its precision exponent. -/
theorem prime_coprime_historyFrequencyModulus (S : Finset ℤ) (N p : ℕ)
    (hp : p.Prime) (hpN : N < p)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N) (n k : ℕ) (t : FrequencyTree S n) :
    p.Coprime (historyFrequencyModulus S n k t) := by
  have hfreq (s : S) : p.Coprime (s : ℤ).natAbs := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hd
    have hpos : 0 < (s : ℤ).natAbs := Int.natAbs_pos.mpr (hS _ s.property).1
    have hle := Nat.le_of_dvd hpos hd
    have hbound := (hS _ s.property).2
    omega
  have hprod : p.Coprime (historyFrequencyProduct S n t) := by
    induction n with
    | zero => exact hfreq t
    | succ n ih => exact (hfreq t.1).mul_right (ih t.2.1) |>.mul_right (ih t.2.2)
  exact hprod.pow_right (k + 2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledSourceScheme
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open scoped BigOperators Classical

theorem ancestorNodeIndex_injective (n : ℕ) (j : Fin (2 ^ n - 1)) :
    Function.Injective (ancestorNodeIndex n j) := by
  intro a b h
  have he := congrArg (fun i => (preorderNodePath n i).length) h
  rw [ancestorNodeIndex_path, ancestorNodeIndex_path, List.length_take, List.length_take,
    min_eq_left a.isLt.le, min_eq_left b.isLt.le] at he
  exact Fin.ext he

section
variable {I B : Type*} [Fintype I]
variable (role : I → CopyScheduleRole) (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
variable (left right : (j : Fin (2 ^ n - 1)) →
  CopyScheduleH role (n - ((preorderNodePath n j).length + 1)) →
    B ⊕ Fin (preorderNodePath n j).length)
variable (C : B → ℤ)

theorem scheduledSourceScheme_left
    (hinj : ∀ j, Function.Injective (left j))
    (p : Fin (2 ^ n - 1) → ℤ) (j : Fin (2 ^ n - 1)) :
    (scheduledSourceScheme role S n t left right C).leftCoefficient p j =
      ∏ h : CopyScheduleH role (n - ((preorderNodePath n j).length + 1)),
        Sum.elim C (fun a => p (ancestorNodeIndex n j a)) (left j h) := by
  change atomFixedProduct (left j) C *
    (∏ i ∈ (atomAncestorSet (left j)).image (ancestorNodeIndex n j), p i) = _
  rw [Finset.prod_image (ancestorNodeIndex_injective n j).injOn]
  exact (atomSource_product (left j) (hinj j) C (fun a => p (ancestorNodeIndex n j a))).symm

theorem scheduledSourceScheme_right
    (hinj : ∀ j, Function.Injective (right j))
    (p : Fin (2 ^ n - 1) → ℤ) (j : Fin (2 ^ n - 1)) :
    (scheduledSourceScheme role S n t left right C).rightCoefficient p j =
      ∏ h : CopyScheduleH role (n - ((preorderNodePath n j).length + 1)),
        Sum.elim C (fun a => p (ancestorNodeIndex n j a)) (right j h) := by
  change atomFixedProduct (right j) C *
    (∏ i ∈ (atomAncestorSet (right j)).image (ancestorNodeIndex n j), p i) = _
  rw [Finset.prod_image (ancestorNodeIndex_injective n j).injOn]
  exact (atomSource_product (right j) (hinj j) C (fun a => p (ancestorNodeIndex n j a))).symm

theorem scheduledSourceScheme_depth (j : Fin (2 ^ n - 1)) :
    (scheduledSourceScheme role S n t left right C).depth j ≤ n :=
  (preorderNodePath_length n j).le

theorem scheduledSourceScheme_root_ne_zero (hS : ∀ s ∈ S, s ≠ 0)
    (j : Fin (2 ^ n - 1)) :
    ((scheduledSourceScheme role S n t left right C).frequencies j).root ≠ 0 :=
  hS _ (singleTreeNodeFrequencies_root_mem S n t j.val j.isLt)

theorem scheduledSourceScheme_frequency_dvd (j : Fin (2 ^ n - 1)) :
    ((scheduledSourceScheme role S n t left right C).frequencies j).root.natAbs ∣
      historyFrequencyProduct S n t := by
  apply history_node_dvd_frequencyProduct S n t
  change singleTreeNodeFrequencies S n t j.val ∈ singleFrequencySplitList S n t
  rw [singleTreeNodeFrequencies, List.getD_eq_getElem _ _ (by
    simpa only [singleFrequencySplitList_length] using j.isLt)]
  exact List.getElem_mem _

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledNodeSources
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete ancestor-source environments at every scheduled tree node -/

namespace Ostmann
open scoped Classical

theorem boundAtomSources_unbound {A B : Type*} (d : ℕ) (source : A → B ⊕ ℕ)
    (hs : ∀ a, AtomSourceBefore d (source a)) (a : A) :
    Sum.map id Fin.val (boundAtomSources d source hs a) = source a := by
  unfold boundAtomSources
  split <;> rename_i v hv
  all_goals exact hv.symm

theorem boundAtomSources_injective {A B : Type*} (d : ℕ) (source : A → B ⊕ ℕ)
    (hs : ∀ a, AtomSourceBefore d (source a)) (hinj : Function.Injective source) :
    Function.Injective (boundAtomSources d source hs) := by
  intro a b h
  apply hinj
  have he := congrArg (Sum.map id Fin.val) h
  simpa only [boundAtomSources_unbound] using he

theorem boundAtomSources_eval {A B M : Type*} (d : ℕ) (source : A → B ⊕ ℕ)
    (hs : ∀ a, AtomSourceBefore d (source a)) (C : B → M) (p : ℕ → M) (a : A) :
    Sum.elim C (fun j : Fin d => p j.val) (boundAtomSources d source hs a) =
      Sum.elim C p (source a) := by
  unfold boundAtomSources
  split <;> rename_i v hv
  all_goals exact (congrArg (Sum.elim C p) hv).symm

theorem scheduledRawNodeSources_injective {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (j : Fin (2 ^ n - 1))
    (hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b) :
    Function.Injective (scheduledRawNodeSources role n j) := by
  apply descendAtomSources_injective role _ _ 0 _ _
    (Sum.inl_injective.comp (scheduledNodeRootEquiv role n j).injective) (fun _ => trivial)
  intro k hk
  rw [scheduledNodeLevel_add_depth] at hk
  exact hu k hk

theorem scheduledNodeSources_injective {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (j : Fin (2 ^ n - 1))
    (hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b) :
    Function.Injective (scheduledNodeSources role n j) :=
  boundAtomSources_injective _ _ _ (scheduledRawNodeSources_injective role n j hu)

theorem scheduledNodeHSources_injective {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (j : Fin (2 ^ n - 1))
    (hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b) :
    Function.Injective (scheduledNodeHSources role n b j) := by
  intro v w h
  have he := scheduledNodeSources_injective role n j hu h
  apply Subtype.ext
  exact congrArg Prod.snd (Sum.inl.inj (congrArg Subtype.val he))

/-- The finite source encoding evaluates to the actual assignment reached
by the ancestor substitutions along this node's path. -/
theorem scheduledNodeSources_eval {I A : Type*} [Zero A] (role : I → CopyScheduleRole)
    (n : ℕ) (j : Fin (2 ^ n - 1))
    (C : CopyScheduleAtoms role n → A) (p : Fin (2 ^ n - 1) → A)
    (v : CopyScheduleAtoms role (scheduledNodeLevel n j + 1)) :
    Sum.elim C (fun a => p (ancestorNodeIndex n j a)) (scheduledNodeSources role n j v) =
      scheduledNodeValues role n j C p v := by
  have hp : (fun a : Fin (preorderNodePath n j).length => nodeAncestorValues n j p a.val) =
      (fun a => p (ancestorNodeIndex n j a)) := by
    funext a
    exact dite_eq_left a.isLt
  rw [← hp]
  change Sum.elim C (fun a : Fin (preorderNodePath n j).length => nodeAncestorValues n j p a.val)
    (boundAtomSources _ _ _ v) = _
  rw [boundAtomSources_eval]
  exact descendAtomSources_eval role (preorderNodePath n j).length
    (scheduledNodeLevel n j + 1) 0 (scheduledReversePath n j)
    (fun w => Sum.inl (scheduledNodeRootEquiv role n j w)) C (nodeAncestorValues n j p) v

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledPreorderNodes
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preorder pivots reproduce the literal scheduled atom assignments -/

namespace Ostmann
open scoped Classical

theorem transferNodeArray_path {State : Type*} (sys : TransferHistorySystem State)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) (j : Fin (2 ^ n - 1)) :
    transferNodeArray sys n σ t j = transferNodeAtPath sys n σ t (preorderNodePath n j) := by
  unfold transferNodeArray
  rw [← nodePathIndex_preorderNodePath n j]
  exact transferNodeList_get_path sys n σ t _ (preorderNodePath_length n j) _

theorem transferNodeArray_valid {State : Type*} (sys : TransferHistorySystem State)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) (hv : ValidTransferHistory sys n σ t)
    (j : Fin (2 ^ n - 1)) : (transferNodeArray sys n σ t j).Valid sys := by
  rw [transferNodeArray_path]
  exact transferNodeAtPath_valid sys n σ t hv _ (preorderNodePath_length n j)

theorem replayNodeIndices_preorder {State : Type*} (sys : TransferHistorySystem State)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) (j : Fin (2 ^ n - 1)) :
    replayNodeIndices sys (preorderNodePath n j) 0
      (nodeAncestorValues n j (transferPivotArray sys n σ t)) σ =
        (transferNodeArray sys n σ t j).state := by
  rw [transferNodeArray_path]
  apply replayNodeIndices_actual sys n σ t _ (preorderNodePath_length n j)
  intro k hk
  simp only [Nat.zero_add, nodeAncestorValues, dite_eq_left hk, transferPivotArray]
  rw [transferNodeArray_path, ancestorNodeIndex_path]

theorem replayNodeIndices_schedule {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (path : List Bool) (n d : ℕ) (p : ℕ → ℕ)
    (C : CopyScheduleAtoms role (n + path.length) → ℕ) :
    replayNodeIndices (scheduleAtomSystem role childBound pivotBound) path d p
        ⟨n + path.length, C⟩ =
      ⟨n, descendAtomValues role path.length n d (reversePathOfList path) p C⟩ := by
  induction path generalizing d with
  | nil => rfl
  | cons b path ih =>
    have htail : Fin.tail (reversePathOfList (b :: path)) = reversePathOfList path := by
      funext j
      rfl
    cases b
    · change replayNodeIndices (scheduleAtomSystem role childBound pivotBound) path (d + 1) p
        ⟨n + path.length, reverseCopyLabelMap role (n + path.length) true (p d) C⟩ = _
      rw [ih]
      simp only [List.length_cons, descendAtomValues, htail]
      rfl
    · change replayNodeIndices (scheduleAtomSystem role childBound pivotBound) path (d + 1) p
        ⟨n + path.length, reverseCopyLabelMap role (n + path.length) false (p d) C⟩ = _
      rw [ih]
      simp only [List.length_cons, descendAtomValues, htail]
      rfl

/-- The source-environment assignment is precisely the state of the actual
preorder history node, with its actual reconstructed natural pivots. -/
theorem scheduledNodeValues_actual {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (n : ℕ) (C : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (j : Fin (2 ^ n - 1)) :
    (transferNodeArray (scheduleAtomSystem role childBound pivotBound) n ⟨n, C⟩ t j).state =
      ⟨scheduledNodeLevel n j + 1, scheduledNodeValues role n j C
        (transferPivotArray (scheduleAtomSystem role childBound pivotBound) n ⟨n, C⟩ t)⟩ := by
  rw [← replayNodeIndices_preorder]
  have hcast : (⟨scheduledNodeLevel n j + 1 + (preorderNodePath n j).length,
      fun v => C (scheduledNodeRootEquiv role n j v)⟩ : ScheduleAtomState role) = ⟨n, C⟩ := by
    have cast_state : ∀ {a b : ℕ} (e : a = b) (f : CopyScheduleAtoms role b → ℕ),
        (⟨a, fun v => f (Equiv.cast (congrArg (CopyScheduleAtoms role) e) v)⟩ :
          ScheduleAtomState role) = ⟨b, f⟩ := by
      intro a b e f
      subst b
      rfl
    exact cast_state (scheduledNodeLevel_add_depth n j) C
  rw [← hcast]
  exact replayNodeIndices_schedule role childBound pivotBound _ _ 0 _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_NodeBulkProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preorder child products of the selected original prime leaves -/

namespace Ostmann
open scoped BigOperators

theorem treeLeafProduct_indexed {G : Type*} [CommMonoid G]
    (n : ℕ) (x : TreeLeafIndex n → G) :
    treeLeafProduct n ((treeLeafTupleEquiv G n).symm x) = ∏ i, x i := by
  induction n with
  | zero =>
    change Unit → G at x
    change x () = ∏ i : Unit, x i
    exact (Fintype.prod_subsingleton x ()).symm
  | succ n ih =>
    change (TreeLeafIndex n ⊕ TreeLeafIndex n) → G at x
    change treeLeafProduct n ((treeLeafTupleEquiv G n).symm (fun i => x (.inl i))) *
      treeLeafProduct n ((treeLeafTupleEquiv G n).symm (fun i => x (.inr i))) = _
    rw [ih, ih]
    change _ = ∏ i : TreeLeafIndex n ⊕ TreeLeafIndex n, x i
    exact (Fintype.prod_sum_type x).symm

theorem actualChildProducts_get_path {G : Type*} [CommMonoid G]
    (n : ℕ) (x : TreeLeafTuple G n) (path : List Bool) (hp : path.length < n) :
    (actualChildProducts n x).getD (nodePathIndex n path) (1, 1) =
      childProductsAtPath n x path := by
  induction n generalizing path with
  | zero => simp at hp
  | succ n ih =>
    cases path with
    | nil => rfl
    | cons b path =>
      have hp' : path.length < n := by simpa using hp
      have hidx := nodePathIndex_lt n path hp'
      have hpow := Nat.one_le_two_pow (n := n)
      cases b
      · simp only [nodePathIndex, Bool.false_eq_true, ite_false, if_false, actualChildProducts]
        rw [show 1 + nodePathIndex n path = nodePathIndex n path + 1 by omega,
          List.getD_cons_succ, List.getD_append _ _ _ _ (by
            rw [actualChildProducts_length]; exact hidx)]
        exact ih _ path hp'
      · simp only [nodePathIndex, ite_true, if_true, actualChildProducts]
        rw [show 2 ^ n + nodePathIndex n path = (2 ^ n - 1 + nodePathIndex n path) + 1 by omega,
          List.getD_cons_succ, List.getD_append_right _ _ _ _ (by
            rw [actualChildProducts_length]; omega), actualChildProducts_length]
        rw [show 2 ^ n - 1 + nodePathIndex n path - (2 ^ n - 1) = nodePathIndex n path by omega]
        exact ih _ path hp'

theorem childProductsAtPath_descend {G : Type*} [CommMonoid G]
    (n : ℕ) (path : List Bool) (x : TreeLeafIndex (n + 1 + path.length) → G) :
    childProductsAtPath (n + 1 + path.length)
      ((treeLeafTupleEquiv G (n + 1 + path.length)).symm x) path =
        (∏ i : TreeLeafIndex n, descendLeafValues path.length (n + 1) (reversePathOfList path) x (.inl i),
         ∏ i : TreeLeafIndex n, descendLeafValues path.length (n + 1) (reversePathOfList path) x (.inr i)) := by
  induction path with
  | nil =>
    change (treeLeafProduct n ((treeLeafTupleEquiv G n).symm (fun i => x (.inl i))),
      treeLeafProduct n ((treeLeafTupleEquiv G n).symm (fun i => x (.inr i)))) = _
    rw [treeLeafProduct_indexed, treeLeafProduct_indexed]
    rfl
  | cons b path ih =>
    cases b
    · change childProductsAtPath (n + 1 + path.length)
        ((treeLeafTupleEquiv G (n + 1 + path.length)).symm (fun i => x (.inl i))) path = _
      rw [ih]
      rfl
    · change childProductsAtPath (n + 1 + path.length)
        ((treeLeafTupleEquiv G (n + 1 + path.length)).symm (fun i => x (.inr i))) path = _
      rw [ih]
      rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SampledPrimeProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal child products in the original prime-sampled history -/

namespace Ostmann
open scoped BigOperators Classical

theorem actualChildProducts_indexed_natCast (n : ℕ) (x : TreeLeafIndex n → ℕ) :
    actualChildProducts n ((treeLeafTupleEquiv ℤ n).symm (fun i => (x i : ℤ))) =
      (actualChildProducts n ((treeLeafTupleEquiv ℕ n).symm x)).map
        (fun z => ((z.1 : ℤ), (z.2 : ℤ))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (TreeLeafIndex n ⊕ TreeLeafIndex n) → ℕ at x
    let a : TreeLeafIndex n → ℕ := fun i => x (.inl i)
    let b : TreeLeafIndex n → ℕ := fun i => x (.inr i)
    change
      (treeLeafProduct n ((treeLeafTupleEquiv ℤ n).symm (fun i => (a i : ℤ))),
       treeLeafProduct n ((treeLeafTupleEquiv ℤ n).symm (fun i => (b i : ℤ)))) ::
        (actualChildProducts n ((treeLeafTupleEquiv ℤ n).symm (fun i => (a i : ℤ))) ++
         actualChildProducts n ((treeLeafTupleEquiv ℤ n).symm (fun i => (b i : ℤ)))) =
      ((treeLeafProduct n ((treeLeafTupleEquiv ℕ n).symm a),
        treeLeafProduct n ((treeLeafTupleEquiv ℕ n).symm b)) ::
        (actualChildProducts n ((treeLeafTupleEquiv ℕ n).symm a) ++
         actualChildProducts n ((treeLeafTupleEquiv ℕ n).symm b))).map
           (fun z : ℕ × ℕ => ((z.1 : ℤ), (z.2 : ℤ)))
    rw [List.map_cons, List.map_append, ih, ih]
    simp only [treeLeafProduct_indexed, Nat.cast_prod]

theorem sampledPrimeHistory_bulk_indexed (P : Finset ℕ) (Q n : ℕ)
    (hunit : ∀ p : P, (p : ℕ).Coprime Q) (x : TreeLeafIndex n → P)
    (pivots : Fin (2 ^ n - 1) → ℤ) :
    (sampledPrimeHistory P Q n hunit x pivots).bulk =
      (treeLeafTupleEquiv ℤ n).symm (fun i => ((x i : ℕ) : ℤ)) := by
  apply (treeLeafTupleEquiv ℤ n).injective
  funext i
  simp only [sampledPrimeHistory, treeLeafTupleEquiv_map, Equiv.apply_symm_apply]

theorem sampledPrimeHistory_childProducts (P : Finset ℕ) (Q n : ℕ)
    (hunit : ∀ p : P, (p : ℕ).Coprime Q) (x : TreeLeafIndex n → P)
    (pivots : Fin (2 ^ n - 1) → ℤ) (j : Fin (2 ^ n - 1)) :
    ((sampledPrimeHistory P Q n hunit x pivots).leftProduct j,
     (sampledPrimeHistory P Q n hunit x pivots).rightProduct j) =
      ((((actualChildProducts n ((treeLeafTupleEquiv ℕ n).symm (fun i => (x i : ℕ)))).getD j.val (1, 1)).1 : ℤ),
       (((actualChildProducts n ((treeLeafTupleEquiv ℕ n).symm (fun i => (x i : ℕ)))).getD j.val (1, 1)).2 : ℤ)) := by
  change (actualChildProducts n (sampledPrimeHistory P Q n hunit x pivots).bulk).getD j.val (1, 1) = _
  rw [sampledPrimeHistory_bulk_indexed, actualChildProducts_indexed_natCast]
  exact List.getD_map _ (1, 1) (fun z : ℕ × ℕ => ((z.1 : ℤ), (z.2 : ℤ)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledNodeFrequencies
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact frequency triple of each reconstructed scheduled node -/

namespace Ostmann

theorem transferNodeList_frequencies {State : Type*} (sys : TransferHistorySystem State)
    (S : Finset ℤ) (n : ℕ) (σ : State) (t : FrequencyTree S n) :
    (transferNodeList sys n σ (frequencyTreeMap Subtype.val n t)).map
      ReconstructedTransferNode.frequencies = singleFrequencySplitList S n t := by
  induction n generalizing σ with
  | zero => rfl
  | succ n ih =>
    simp only [transferNodeList, frequencyTreeMap, frequencyRoot_map, List.map_cons,
      List.map_append, ih, singleFrequencySplitList, ReconstructedTransferNode.frequencies]

theorem transferNodeArray_frequencies {State : Type*} (sys : TransferHistorySystem State)
    (S : Finset ℤ) (n : ℕ) (σ : State) (t : FrequencyTree S n) (j : Fin (2 ^ n - 1)) :
    (transferNodeArray sys n σ (frequencyTreeMap Subtype.val n t) j).frequencies =
      singleTreeNodeFrequencies S n t j.val := by
  have he := congrArg (fun L => L.getD j.val emptyNodeFrequencies)
    (transferNodeList_frequencies sys S n σ t)
  have hm := List.getD_map (transferNodeList sys n σ (frequencyTreeMap Subtype.val n t))
    ⟨σ, 0, 0, 0⟩ ReconstructedTransferNode.frequencies (n := j.val)
  exact hm.symm.trans he

/-- Validity at a node now uses the frequency triple of that exact preorder
entry, with no independently supplied node relation. -/
theorem scheduledNodeValues_valid {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (S : Finset ℤ) (n : ℕ) (C : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree S n)
    (hv : ValidTransferHistory (scheduleAtomSystem role childBound pivotBound) n ⟨n, C⟩
      (frequencyTreeMap Subtype.val n t)) (j : Fin (2 ^ n - 1)) :
    let p := transferPivotArray (scheduleAtomSystem role childBound pivotBound) n ⟨n, C⟩
      (frequencyTreeMap Subtype.val n t)
    let f := singleTreeNodeFrequencies S n t j.val
    ValidTransferNode (scheduleAtomSystem role childBound pivotBound)
      ⟨scheduledNodeLevel n j + 1, scheduledNodeValues role n j C p⟩
      f.root f.left f.right (p j) := by
  dsimp only
  have hh := transferNodeArray_valid (scheduleAtomSystem role childBound pivotBound) n ⟨n, C⟩
    (frequencyTreeMap Subtype.val n t) hv j
  have hf := transferNodeArray_frequencies (scheduleAtomSystem role childBound pivotBound) S n ⟨n, C⟩ t j
  have hs := scheduledNodeValues_actual role childBound pivotBound n C
    (frequencyTreeMap Subtype.val n t) j
  rw [ReconstructedTransferNode.Valid, hs] at hh
  have hroot := congrArg NodeFrequencies.root hf
  have hleft := congrArg NodeFrequencies.left hf
  have hright := congrArg NodeFrequencies.right hf
  exact hroot ▸ hleft ▸ hright ▸ hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledLeafProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two sampled prime products at each actual scheduled node -/

namespace Ostmann
open scoped BigOperators Classical

theorem scheduledNodeLeafValues_products {G : Type*} [CommMonoid G]
    (n : ℕ) (j : Fin (2 ^ n - 1)) (x : TreeLeafIndex n → G) :
    (actualChildProducts n ((treeLeafTupleEquiv G n).symm x)).getD j.val (1, 1) =
      (∏ i : TreeLeafIndex (scheduledNodeLevel n j), scheduledNodeLeafValues n j x (.inl i),
       ∏ i : TreeLeafIndex (scheduledNodeLevel n j), scheduledNodeLeafValues n j x (.inr i)) := by
  have hcast : ∀ {a b : ℕ} (e : a = b) (x : TreeLeafIndex b → G) (path : List Bool),
      childProductsAtPath a ((treeLeafTupleEquiv G a).symm
        (fun v => x (Equiv.cast (congrArg TreeLeafIndex e) v))) path =
      childProductsAtPath b ((treeLeafTupleEquiv G b).symm x) path := by
    intro a b e x path
    subst b
    rfl
  rw [← nodePathIndex_preorderNodePath n j,
    actualChildProducts_get_path n _ _ (preorderNodePath_length n j)]
  rw [← hcast (scheduledNodeLevel_add_depth n j) x (preorderNodePath n j)]
  exact childProductsAtPath_descend _ _ _

/-- Transporting the root index does not change which word leaves scale. -/
theorem wordLeafScale_cast {I G : Type*} [Mul G]
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word)
    {a b : ℕ} (e : a = b) (C : CopyScheduleAtoms role b → G) (x : TreeLeafIndex b → G) :
    (fun v => wordLeafScale role i hi b C x
      (Equiv.cast (congrArg (CopyScheduleAtoms role) e) v)) =
      wordLeafScale role i hi a
        (fun v => C (Equiv.cast (congrArg (CopyScheduleAtoms role) e) v))
        (fun v => x (Equiv.cast (congrArg TreeLeafIndex e) v)) := by
  subst b
  rfl

theorem scheduledNodeValues_wordLeafScale {I G : Type*} [Zero G] [Mul G]
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word)
    (n : ℕ) (j : Fin (2 ^ n - 1)) (C : CopyScheduleAtoms role n → G)
    (x : TreeLeafIndex n → G) (p : Fin (2 ^ n - 1) → G) :
    scheduledNodeValues role n j (wordLeafScale role i hi n C x) p =
      wordLeafScale role i hi (scheduledNodeLevel n j + 1)
        (scheduledNodeValues role n j C p) (scheduledNodeLeafValues n j x) := by
  unfold scheduledNodeValues scheduledNodeRootEquiv
  rw [wordLeafScale_cast role i hi (scheduledNodeLevel_add_depth n j),
    descendAtomValues_wordLeafScale]
  rfl

/-- These are exactly the two bulk factors used by `SampledPivotHistory`. -/
theorem scheduledNodeValues_H_product {I G : Type*} [Fintype I] [Zero G] [CommMonoid G]
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word)
    (n : ℕ) (j : Fin (2 ^ n - 1)) (b : Bool) (C : CopyScheduleAtoms role n → G)
    (x : TreeLeafIndex n → G) (p : Fin (2 ^ n - 1) → G) :
    (∏ a : CopyScheduleH role (scheduledNodeLevel n j),
      scheduledNodeValues role n j (wordLeafScale role i hi n C x) p
        ⟨.inl (b, a.val), a.property⟩) =
      (∏ a : CopyScheduleH role (scheduledNodeLevel n j),
        scheduledNodeValues role n j C p ⟨.inl (b, a.val), a.property⟩) *
        (if b then
          ((actualChildProducts n ((treeLeafTupleEquiv G n).symm x)).getD j.val (1, 1)).1
        else ((actualChildProducts n ((treeLeafTupleEquiv G n).symm x)).getD j.val (1, 1)).2) := by
  rw [scheduledNodeValues_wordLeafScale, wordLeafScale_H_product, scheduledNodeLeafValues_products]
  cases b <;> rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledNodeEquations
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open scoped BigOperators Classical

theorem scheduledActualSourceScheme_left_natCast {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (C : CopyScheduleAtoms role n → ℕ)
    (hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b)
    (p : Fin (2 ^ n - 1) → ℕ) (j : Fin (2 ^ n - 1)) :
    (scheduledActualSourceScheme role S n t (fun v => (C v : ℤ))).leftCoefficient
      (fun j => (p j : ℤ)) j =
        ((∏ a : CopyScheduleH role (scheduledNodeLevel n j),
          scheduledNodeValues role n j C p ⟨.inl (false, a.val), a.property⟩ : ℕ) : ℤ) := by
  unfold scheduledActualSourceScheme
  rw [scheduledSourceScheme_left role S n t _ _ _
    (fun j => scheduledNodeHSources_injective role n false j hu), Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro a _
  have he := scheduledNodeSources_eval role n j C p
    ⟨.inl (false, a.val), a.property⟩
  rw [← he]
  change Sum.elim (fun v => (C v : ℤ))
    (fun k => (p (ancestorNodeIndex n j k) : ℤ)) _ = _
  dsimp only [scheduledNodeHSources]
  cases scheduledNodeSources role n j ⟨.inl (false, a.val), a.property⟩ <;> rfl

theorem scheduledActualSourceScheme_right_natCast {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (C : CopyScheduleAtoms role n → ℕ)
    (hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b)
    (p : Fin (2 ^ n - 1) → ℕ) (j : Fin (2 ^ n - 1)) :
    (scheduledActualSourceScheme role S n t (fun v => (C v : ℤ))).rightCoefficient
      (fun j => (p j : ℤ)) j =
        ((∏ a : CopyScheduleH role (scheduledNodeLevel n j),
          scheduledNodeValues role n j C p ⟨.inl (true, a.val), a.property⟩ : ℕ) : ℤ) := by
  unfold scheduledActualSourceScheme
  rw [scheduledSourceScheme_right role S n t _ _ _
    (fun j => scheduledNodeHSources_injective role n true j hu), Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro a _
  have he := scheduledNodeSources_eval role n j C p
    ⟨.inl (true, a.val), a.property⟩
  rw [← he]
  change Sum.elim (fun v => (C v : ℤ))
    (fun k => (p (ancestorNodeIndex n j k) : ℤ)) _ = _
  dsimp only [scheduledNodeHSources]
  cases scheduledNodeSources role n j ⟨.inl (true, a.val), a.property⟩ <;> rfl

/-- Every equation is derived from the valid full arithmetic history. The
fixed coefficients depend on the remaining word factors and ancestor pivots. -/
theorem scheduled_scaled_history_equations {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (i : I) (hi : role i = .word) (S : Finset ℤ) (n : ℕ)
    (C : CopyScheduleAtoms role n → ℕ) (x : TreeLeafIndex n → ℕ)
    (t : FrequencyTree S n)
    (hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b)
    (hv : ValidTransferHistory (scheduleAtomSystem role childBound pivotBound) n
      ⟨n, wordLeafScale role i hi n C x⟩ (frequencyTreeMap Subtype.val n t)) :
    let p := transferPivotArray (scheduleAtomSystem role childBound pivotBound) n
      ⟨n, wordLeafScale role i hi n C x⟩ (frequencyTreeMap Subtype.val n t)
    (scheduledActualSourceScheme role S n t (fun v => (C v : ℤ))).equations
      (fun j => (((actualChildProducts n ((treeLeafTupleEquiv ℕ n).symm x)).getD j.val (1, 1)).1 : ℤ))
      (fun j => (((actualChildProducts n ((treeLeafTupleEquiv ℕ n).symm x)).getD j.val (1, 1)).2 : ℤ))
      (fun j => (p j : ℤ)) := by
  dsimp only
  intro j
  let p := transferPivotArray (scheduleAtomSystem role childBound pivotBound) n
    ⟨n, wordLeafScale role i hi n C x⟩ (frequencyTreeMap Subtype.val n t)
  have hvj := scheduledNodeValues_valid role childBound pivotBound S n
    (wordLeafScale role i hi n C x) t hv j
  have hr := hvj.relation
  change (singleTreeNodeFrequencies S n t j.val).left *
      ((∏ a : CopyScheduleH role (scheduledNodeLevel n j),
        scheduledNodeValues role n j (wordLeafScale role i hi n C x) p
          ⟨.inl (false, a.val), a.property⟩ : ℕ) : ℤ) -
    (singleTreeNodeFrequencies S n t j.val).right *
      ((∏ a : CopyScheduleH role (scheduledNodeLevel n j),
        scheduledNodeValues role n j (wordLeafScale role i hi n C x) p
          ⟨.inl (true, a.val), a.property⟩ : ℕ) : ℤ) =
      (singleTreeNodeFrequencies S n t j.val).root * (p j : ℤ) at hr
  rw [scheduledNodeValues_H_product, scheduledNodeValues_H_product] at hr
  simp only [Bool.false_eq_true, ite_false, if_false, ite_true, if_true, Nat.cast_mul] at hr
  change (singleTreeNodeFrequencies S n t j.val).left * _ * _ -
    (singleTreeNodeFrequencies S n t j.val).right * _ * _ =
      (singleTreeNodeFrequencies S n t j.val).root * (p j : ℤ)
  rw [scheduledActualSourceScheme_left_natCast role S n t C hu,
    scheduledActualSourceScheme_right_natCast role S n t C hu]
  simpa only [mul_assoc] using hr

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledNodeUnits
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original full-weight unit guards at every reconstructed preorder node -/

namespace Ostmann
open scoped Classical

theorem scheduleAtomUnitsValid_nodeList {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (n : ℕ) (C : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (hu : scheduleAtomUnitsValid role childBound pivotBound (totalAtomUnitRanges role) n C t) :
    ∀ node ∈ transferNodeList (scheduleAtomSystem role childBound pivotBound) n ⟨n, C⟩ t,
      ScheduleNodeUnits role node := by
  induction n with
  | zero => simp [transferNodeList]
  | succ n ih =>
    intro node hn
    simp only [transferNodeList, List.mem_cons, List.mem_append] at hn
    rcases hn with rfl | hn | hn
    · exact (totalAtomUnitRanges_iff role (n + 1) C t.1).mp hu.1
    · exact ih _ _ hu.2.1 _ hn
    · exact ih _ _ hu.2.2 _ hn

theorem scheduledNodeValues_units {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (S : Finset ℤ) (n : ℕ) (C : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree S n)
    (hu : scheduleAtomUnitsValid role childBound pivotBound (totalAtomUnitRanges role) n C
      (frequencyTreeMap Subtype.val n t)) (j : Fin (2 ^ n - 1)) :
    let p := transferPivotArray (scheduleAtomSystem role childBound pivotBound) n ⟨n, C⟩
      (frequencyTreeMap Subtype.val n t)
    ∀ v, (scheduledNodeValues role n j C p v).Coprime
      (singleTreeNodeFrequencies S n t j.val).root.natAbs := by
  have hn : transferNodeArray (scheduleAtomSystem role childBound pivotBound) n ⟨n, C⟩
      (frequencyTreeMap Subtype.val n t) j ∈
      transferNodeList (scheduleAtomSystem role childBound pivotBound) n ⟨n, C⟩
        (frequencyTreeMap Subtype.val n t) := by
    unfold transferNodeArray
    rw [List.getD_eq_getElem _ _ (by rw [transferNodeList_length]; exact j.isLt)]
    exact List.getElem_mem _
  have h := scheduleAtomUnitsValid_nodeList role childBound pivotBound n C
    (frequencyTreeMap Subtype.val n t) hu _ hn
  have hs := scheduledNodeValues_actual role childBound pivotBound n C
    (frequencyTreeMap Subtype.val n t) j
  have hf := congrArg NodeFrequencies.root
    (transferNodeArray_frequencies (scheduleAtomSystem role childBound pivotBound) S n ⟨n, C⟩ t j)
  unfold ScheduleNodeUnits at h
  rw [hs] at h
  exact hf ▸ h

/-- Nonzero full weights already contain all validity and frequency-unit
conditions used by the sampled-history estimate. -/
theorem fullAtomTransferWeight_valid_units {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (n : ℕ)
    (C : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (hw : fullAtomTransferWeight role childBound pivotBound ranges leaf n C t ≠ 0) :
    ValidTransferHistory (scheduleAtomSystem role childBound pivotBound) n ⟨n, C⟩ t ∧
      scheduleAtomUnitsValid role childBound pivotBound (totalAtomUnitRanges role) n C t := by
  unfold fullAtomTransferWeight at hw
  split_ifs at hw with hg
  · exact ⟨recursiveTransferWeight_nonzero_valid _ _ _ _ _ _ hw, hg.2.1⟩
  · exact False.elim (hw rfl)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledSampledValidity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual full weights give valid original-prime sampled histories -/

namespace Ostmann
open scoped BigOperators Classical

theorem scheduled_scaled_history_coefficient_units {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (i : I) (hi : role i = .word) (S : Finset ℤ) (n : ℕ)
    (C : CopyScheduleAtoms role n → ℕ) (x : TreeLeafIndex n → ℕ)
    (t : FrequencyTree S n)
    (hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b)
    (hunits : scheduleAtomUnitsValid role childBound pivotBound (totalAtomUnitRanges role) n
      (wordLeafScale role i hi n C x) (frequencyTreeMap Subtype.val n t)) :
    let p := transferPivotArray (scheduleAtomSystem role childBound pivotBound) n
      ⟨n, wordLeafScale role i hi n C x⟩ (frequencyTreeMap Subtype.val n t)
    ∀ j, IsCoprime
        ((scheduledActualSourceScheme role S n t (fun v => (C v : ℤ))).leftCoefficient
          (fun j => (p j : ℤ)) j) (singleTreeNodeFrequencies S n t j.val).root ∧
      IsCoprime
        ((scheduledActualSourceScheme role S n t (fun v => (C v : ℤ))).rightCoefficient
          (fun j => (p j : ℤ)) j) (singleTreeNodeFrequencies S n t j.val).root := by
  intro p j
  have hall := scheduledNodeValues_units role childBound pivotBound S n
    (wordLeafScale role i hi n C x) t hunits j
  have hc (b : Bool) :
      (∏ a : CopyScheduleH role (scheduledNodeLevel n j),
        scheduledNodeValues role n j C p ⟨.inl (b, a.val), a.property⟩).Coprime
          (singleTreeNodeFrequencies S n t j.val).root.natAbs := by
    have hprod := Nat.coprime_fintype_prod_left_iff.mpr
      (fun a : CopyScheduleH role (scheduledNodeLevel n j) => hall ⟨.inl (b, a.val), a.property⟩)
    rw [scheduledNodeValues_H_product] at hprod
    exact (Nat.coprime_mul_iff_left.mp hprod).1
  constructor
  · rw [scheduledActualSourceScheme_left_natCast role S n t C hu]
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    exact hc false
  · rw [scheduledActualSourceScheme_right_natCast role S n t C hu]
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    exact hc true

/-- No equation or unit condition is added to the analytic assumptions: both
are obtained from the actual nonzero full coefficient and its original guards. -/
theorem fullAtomTransferWeight_sampled_valid {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ)
    (i : I) (hi : role i = .word) (S : Finset ℤ) (n : ℕ)
    (C : CopyScheduleAtoms role n → ℕ) (P : Finset ℕ) (Q : ℕ)
    (hunit : ∀ p : P, (p : ℕ).Coprime Q) (x : TreeLeafIndex n → P)
    (t : FrequencyTree S n)
    (hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b)
    (hw : fullAtomTransferWeight role childBound pivotBound ranges leaf n
      (wordLeafScale role i hi n C (fun j => (x j : ℕ))) (frequencyTreeMap Subtype.val n t) ≠ 0) :
    let p := transferPivotArray (scheduleAtomSystem role childBound pivotBound) n
      ⟨n, wordLeafScale role i hi n C (fun j => (x j : ℕ))⟩ (frequencyTreeMap Subtype.val n t)
    (sampledPrimeHistory P Q n hunit x (fun j => (p j : ℤ))).valid
      (scheduledActualSourceScheme role S n t (fun v => (C v : ℤ))) := by
  intro p
  obtain ⟨hv, hunits⟩ := fullAtomTransferWeight_valid_units role childBound pivotBound ranges leaf n
    (wordLeafScale role i hi n C (fun j => (x j : ℕ))) _ hw
  constructor
  · intro j
    have heq := scheduled_scaled_history_equations role childBound pivotBound i hi S n C
      (fun j => (x j : ℕ)) t hu hv j
    have hp := sampledPrimeHistory_childProducts P Q n hunit x (fun j => (p j : ℤ)) j
    have hL := congrArg Prod.fst hp
    have hR := congrArg Prod.snd hp
    dsimp only at hL hR
    change _ * _ * _ - _ * _ * _ = _ * _
    rw [hL, hR]
    exact heq
  · exact scheduled_scaled_history_coefficient_units role childBound pivotBound i hi S n C
      (fun j => (x j : ℕ)) t hu hunits

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledSampledEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sharp squared-history estimate for the actual scheduled Fourier weight -/

namespace Ostmann
open Filter
open scoped BigOperators Classical SchwartzMap FourierTransform

/-- The original prime law is retained. Both the integer equations and the
coefficient units come from the full weight; only published analytic estimates
and the explicit prime-cell size conditions remain for the final application. -/
theorem uniform_scheduled_clipped_square_rate (n : ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (C₀ K C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K) :
    ∀ᶠ m : ℝ in atTop,
      ∀ {I : Type*} [Fintype I],
      ∀ (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
        (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
        (i : I) (hi : role i = .word)
        (_hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b),
      ∀ N V : ℕ, ∀ Δ X lo upper : ℝ,
      ∀ P : Finset ℕ, ∀ S : Finset ℤ,
      (N : ℝ) ≤ Real.exp (C * m) →
      (V : ℝ) ≤ Real.exp (Δ + Real.sqrt m) →
      (∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N) →
      (∀ p ∈ P, p.Prime ∧ N < p) →
      0 < X → Real.exp (Δ - C₀) ≤ lo →
      ∀ T : Finset ℕ, ∀ h J : ℕ,
      (∀ t : FrequencyTree S n, historyFrequencyModulus S n n t ≤ 2 ^ h) →
      (∀ p ∈ T, 2 ^ h ≤ p ∧ p < 2 ^ (h + J)) →
      ∀ a C₁ L : ℝ, 0 < a → 1 ≤ L →
      a ≤ ∑ p ∈ T, (p : ℝ)⁻¹ → (J : ℝ) ≤ Real.exp (C₁ * L) →
      ∀ base : CopyScheduleAtoms role n → ℕ,
      (∑ t : FrequencyTree S n, ∑ x : TreeLeafIndex n → P,
        (∏ j, primeSubsetPrior P T (x j)) *
          ‖clippedFullAtomFourierWeight role childBound pivotBound ranges ψ X lo upper S V n
            (wordLeafScale role i hi n base (fun j => (x j : ℕ))) t‖ ^ 2) ≤
        Real.exp ((C₁ + max (Real.log (3 / a)) 0) * (2 ^ n : ℕ) * L + ε * m) := by
  filter_upwards [sampled_history_square_rate n n ((2 ^ n : ℕ) * (C₀ + 2 * K)) C ε hC hε]
    with m hm
  intro I instI role childBound pivotBound ranges i hi hu N V Δ X lo upper P S hN hV hS hP hX hlo T h J hsmall hrange a C₁ L ha hL hmass hJ base
  let R := historyFrequencyProduct S n
  let D := fun t : FrequencyTree S n =>
    scheduledActualSourceScheme role S n t (fun v => (base v : ℤ))
  let hunit : ∀ t : FrequencyTree S n, ∀ p : P, (p : ℕ).Coprime (R t ^ (n + 2)) :=
    fun t p => prime_coprime_historyFrequencyModulus S N p (hP p p.property).1
      (hP p p.property).2 hS n n t
  have : ∀ t : FrequencyTree S n, NeZero (R t ^ (n + 2)) := fun t =>
    ⟨Nat.ne_of_gt (historyFrequencyModulus_pos S (fun s hs => (hS s hs).1) n n t)⟩
  let pivots := fun (t : FrequencyTree S n) (x : TreeLeafIndex n → P) (j : Fin (2 ^ n - 1)) =>
    ((transferPivotArray (scheduleAtomSystem role childBound pivotBound) n
      ⟨n, wordLeafScale role i hi n base (fun j => (x j : ℕ))⟩
      (frequencyTreeMap Subtype.val n t) j : ℕ) : ℤ)
  let W := fun (t : FrequencyTree S n) (x : TreeLeafIndex n → P) =>
    clippedFullAtomFourierWeight role childBound pivotBound ranges ψ X lo upper S V n
      (wordLeafScale role i hi n base (fun j => (x j : ℕ))) t
  apply hm N V Δ P S hN hV hS R D
    (fun t j => scheduledSourceScheme_depth role S n t _ _ _ j)
    (fun t j => scheduledSourceScheme_root_ne_zero role S n t _ _ _
      (fun s hs => (hS s hs).1) j)
    (fun t j => scheduledSourceScheme_frequency_dvd role S n t _ _ _ j)
    (fun _ _ => rfl) (fun _ => T) (fun _ => h) (fun _ => J) hunit
    (fun t _ => hsmall t) (fun _ p hp => hrange p hp)
    a C₁ L ha hL (fun _ => hmass) (fun _ => hJ) pivots W
  · intro t x
    exact clippedFullAtomFourierWeight_square_le role childBound pivotBound ranges ψ X lo upper
      Δ C₀ K hX hlo hψ S V n _ t
  · intro t x hx
    have hfull : fullAtomTransferWeight role childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo upper) n
        (wordLeafScale role i hi n base (fun j => (x j : ℕ)))
        (frequencyTreeMap Subtype.val n t) ≠ 0 := by
      unfold W clippedFullAtomFourierWeight at hx
      split_ifs at hx
      · exact hx
      · exact False.elim (hx rfl)
    exact fullAtomTransferWeight_sampled_valid role childBound pivotBound ranges
      (scheduleFourierLeaf role ψ X lo upper) i hi S n base P (R t ^ (n + 2))
      (hunit t) x t hu hfull

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FixedPivotScheduledEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sharp original-prior energy with the current composite pivot fixed externally -/

namespace Ostmann
open Filter
open scoped BigOperators Classical SchwartzMap FourierTransform

theorem uniform_constituent_fixedPivot_scheduled_square_rate (n : ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (C₀ K C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K) :
    ∀ᶠ m : ℝ in atTop,
      ∀ {I : Type*} [Fintype I],
      ∀ (role : I → CopyScheduleRole) (size : I → ℕ)
        (childBound pivotBound : ℕ → ℕ)
        (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
        (i : Σ a, Fin (size a)) (_hi : role i.1 = .word)
        (_hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b),
      ∀ V : ℕ → ℕ, ∀ Δ X lo upper : ℝ, ∀ M : ℕ,
      ∀ P : Finset ℕ, ∀ cells : (Σ a, Fin (size a)) → Finset ℕ,
      Monotone V → (V n : ℝ) ≤ Real.exp (C * m) →
      (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt m) →
      (∀ p ∈ P, p.Prime ∧ V n < p) →
      0 < X → 1 < X * lo → Real.exp (Δ - C₀) ≤ lo →
      (∀ j, cells j ⊆ P) → (∀ j, (∑ p ∈ cells j, (p : ℝ)⁻¹) ≠ 0) →
      ∀ h J : ℕ,
      (∀ t : FrequencyTree ((transferFrequencyRange (V n)).erase 0) n,
        historyFrequencyModulus ((transferFrequencyRange (V n)).erase 0) n n t ≤ 2 ^ h) →
      (∀ p ∈ cells i, 2 ^ h ≤ p ∧ p < 2 ^ (h + J)) →
      ∀ a C₁ L : ℝ, 0 < a → 1 ≤ L →
      a ≤ ∑ p ∈ cells i, (p : ℝ)⁻¹ → (J : ℝ) ≤ Real.exp (C₁ * L) →
      (∑ d : ScheduledFrequencyIndex V n, ∑ q : SurvivingConstituent role size n → P,
        scheduledPrimePrior (fun j : Σ a, Fin (size a) => role j.1) n
          (fun j => primeSubsetPrior P (cells j)) q *
          ‖fullAtomTransferWeight role childBound pivotBound ranges
            (scheduleFourierLeaf role ψ X lo upper) n
            (scheduledReplacePivot role n M
              (fun a => ((scheduleConstituentWord role size n a).map (fun v => (q v : ℕ))).prod))
            (scheduledFrequencyHistory V n d)‖ ^ 2) ≤
        Real.exp ((C₁ + max (Real.log (3 / a)) 0) * (2 ^ n : ℕ) * L + ε * m) := by
  filter_upwards [uniform_scheduled_clipped_square_rate n ψ C₀ K C ε hC hε hψ] with m hm
  intro I instI role size childBound pivotBound ranges i hi hu V Δ X lo upper M P cells hV hN hV₀ hP hX hXlo hlo hsub hmass h J hsmall hrange a C₁ L ha hL hcell hJ
  let S := (transferFrequencyRange (V n)).erase 0
  have hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ V n := by
    intro s hs
    exact ⟨(Finset.mem_erase.mp hs).1,
      (mem_transferFrequencyRange _ _).mp (Finset.mem_erase.mp hs).2⟩
  have he := scheduled_full_fourier_energy_le role childBound pivotBound ranges ψ X lo upper
    hX hXlo V hV n
    (fun q : SurvivingConstituent role size n → P =>
      scheduledPrimePrior (fun j : Σ a, Fin (size a) => role j.1) n
        (fun j => primeSubsetPrior P (cells j)) q)
    (fun q => Finset.prod_nonneg fun _ _ => primeSubsetPrior_nonneg _ _ _)
    (fun q => scheduledReplacePivot role n M
      (fun a => ((scheduleConstituentWord role size n a).map (fun v => (q v : ℕ))).prod))
  apply he.trans
  apply constituent_fixedPivot_energy_transport role size i hi n M P cells hsub hmass
    (fun t base => ‖clippedFullAtomFourierWeight role childBound pivotBound ranges ψ X lo upper
      S (V 0) n base t‖ ^ 2)
  intro base
  exact hm role childBound pivotBound ranges i.1 hi hu (V n) (V 0) Δ X lo upper P S hN hV₀ hS hP hX hlo
    (cells i) h J hsmall hrange a C₁ L ha hL hcell hJ base

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

/-- At fixed depth the whole rounded frequency family has an exponential
bound linear in the word length, with its square-root reserve absorbed. -/
theorem eventual_rounded_frequency_card (n : ℕ) (d : ℝ) (hd : 0 ≤ d) :
    ∀ᶠ m : ℝ in atTop, ∀ j ≤ n,
      ((transferFrequencyRange (naturalTransferCutoff (d * m) m j)).card : ℝ) ≤
        Real.exp (((2 : ℝ) ^ n * d + 1) * m) := by
  obtain ⟨M, hM⟩ := sqrt_cost_sublinear (2 * (4 : ℝ) ^ n) (Real.log 3) 1
    (by positivity) (by norm_num)
  filter_upwards [eventually_ge_atTop M, eventually_ge_atTop (0 : ℝ)] with m hm hm0 j hj
  have hb := hM m hm
  have h2 : (2 : ℝ) ^ j ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hj
  have h4 : (4 : ℝ) ^ j ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) hj
  have he : 0 ≤ transferErrorScale (d * m) m j := by unfold transferErrorScale; positivity
  have hfloor : (naturalTransferCutoff (d * m) m j : ℝ) ≤
      Real.exp (transferErrorScale (d * m) m j) := Nat.floor_le (Real.exp_pos _).le
  have hone : 1 ≤ Real.exp (transferErrorScale (d * m) m j) := Real.one_le_exp he
  rw [card_transferFrequencyRange]
  push_cast
  calc
    _ ≤ 3 * Real.exp (transferErrorScale (d * m) m j) := by linarith
    _ = Real.exp (Real.log 3 + transferErrorScale (d * m) m j) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      unfold transferErrorScale
      have ha := mul_le_mul_of_nonneg_right h2 (mul_nonneg hd hm0)
      have hc := mul_le_mul_of_nonneg_right h4 (Real.sqrt_nonneg m)
      nlinarith

/-- The rate theorem's square-root parameter is four times the actual word
length, so it covers the literal `2 sqrt(m)` bottom-frequency reserve. -/
theorem rounded_bottom_frequency_bound (Δ m : ℝ) :
    (naturalTransferCutoff Δ m 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) := by
  have h := Nat.floor_le (Real.exp_pos (transferErrorScale Δ m 0)).le
  change (naturalTransferCutoff Δ m 0 : ℝ) ≤ _
  apply h.trans_eq
  congr 1
  simp only [transferErrorScale, pow_zero, one_mul]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_NaturalFixedPivotEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed-pivot energy at the manuscript's actual rounded cutoffs -/

namespace Ostmann
open Filter
open scoped BigOperators Classical SchwartzMap FourierTransform

theorem uniform_constituent_natural_fixedPivot_energy (n : ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (C₀ K d ε : ℝ) (hd : 0 ≤ d) (hε : 0 < ε)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K) :
    ∀ᶠ m : ℝ in atTop,
      ∀ {I : Type*} [Fintype I],
      ∀ (role : I → CopyScheduleRole) (size : I → ℕ)
        (childBound pivotBound : ℕ → ℕ)
        (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
        (i : Σ a, Fin (size a)) (_hi : role i.1 = .word)
        (_hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b),
      ∀ X lo upper : ℝ, ∀ M : ℕ,
      ∀ P : Finset ℕ, ∀ cells : (Σ a, Fin (size a)) → Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ naturalTransferCutoff (d * m) m n < p) →
      0 < X → 1 < X * lo → Real.exp (d * m - C₀) ≤ lo →
      (∀ j, cells j ⊆ P) → (∀ j, (∑ p ∈ cells j, (p : ℝ)⁻¹) ≠ 0) →
      ∀ h J : ℕ,
      naturalTransferCutoff (d * m) m n ^ ((2 ^ (n + 1) - 1) * (n + 2)) ≤ 2 ^ h →
      (∀ p ∈ cells i, 2 ^ h ≤ p ∧ p < 2 ^ (h + J)) →
      ∀ a C₁ L : ℝ, 0 < a → 1 ≤ L →
      a ≤ ∑ p ∈ cells i, (p : ℝ)⁻¹ → (J : ℝ) ≤ Real.exp (C₁ * L) →
      (∑ j : ScheduledFrequencyIndex (naturalTransferCutoff (d * m) m) n,
        ∑ q : SurvivingConstituent role size n → P,
        scheduledPrimePrior (fun j : Σ a, Fin (size a) => role j.1) n
          (fun j => primeSubsetPrior P (cells j)) q *
          ‖fullAtomTransferWeight role childBound pivotBound ranges
            (scheduleFourierLeaf role ψ X lo upper) n
            (scheduledReplacePivot role n M
              (fun a => ((scheduleConstituentWord role size n a).map (fun v => (q v : ℕ))).prod))
            (scheduledFrequencyHistory (naturalTransferCutoff (d * m) m) n j)‖ ^ 2) ≤
        Real.exp ((C₁ + max (Real.log (3 / a)) 0) * (2 ^ n : ℕ) * L + ε * m) := by
  let C := (2 : ℝ) ^ n * d + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hrate := uniform_constituent_fixedPivot_scheduled_square_rate n
    ψ C₀ K C (ε / 4) hC (by positivity) hψ
  have hrate' := (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 4)).eventually hrate
  filter_upwards [hrate', eventual_rounded_frequency_card n d hd, eventually_ge_atTop (0 : ℝ)]
    with m hm hc hm0
  intro I instI role size childBound pivotBound ranges i hi hu X lo upper M P cells hP hX hXlo hlo hsub hmass h J hsmall hrange a C₁ L ha hL hcell hJ
  let V := naturalTransferCutoff (d * m) m
  have hV : Monotone V := naturalTransferCutoff_monotone _ _ (mul_nonneg hd hm0)
  have hN : (V n : ℝ) ≤ Real.exp (C * (4 * m)) := by
    have hn := hc n le_rfl
    have hnat : (V n : ℝ) ≤ ((transferFrequencyRange (V n)).card : ℝ) := by
      rw [card_transferFrequencyRange]
      push_cast
      linarith [show (0 : ℝ) ≤ (V n : ℝ) from Nat.cast_nonneg _]
    exact hnat.trans (hn.trans (Real.exp_le_exp.mpr (by
      change C * m ≤ C * (4 * m)
      have h4 : m ≤ 4 * m := by linarith
      exact mul_le_mul_of_nonneg_left h4 hC)))
  have hv0 : (V 0 : ℝ) ≤ Real.exp (d * m + Real.sqrt (4 * m)) := rounded_bottom_frequency_bound _ _
  have hmod (t : FrequencyTree ((transferFrequencyRange (V n)).erase 0) n) :
      historyFrequencyModulus ((transferFrequencyRange (V n)).erase 0) n n t ≤ 2 ^ h := by
    apply (historyFrequencyModulus_le _ (V n) _ n n t).trans hsmall
    intro s hs
    exact (mem_transferFrequencyRange _ _).mp (Finset.mem_erase.mp hs).2
  have hb := hm role size childBound pivotBound ranges i hi hu V (d * m) X lo upper M P cells hV hN hv0 hP hX hXlo hlo hsub hmass
    h J hmod hrange a C₁ L ha hL hcell hJ
  have he : ε / 4 * (4 * m) = ε * m := by ring
  simpa only [id_eq, he, V] using hb

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentUniqueRootEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unique histories remove multiplicity from the actual final energy -/

namespace Ostmann
open scoped BigOperators Classical

private theorem norm_sum_sq_of_unique {D : Type*} [Fintype D] (F : D → ℂ)
    (hu : ∀ d e, F d ≠ 0 → F e ≠ 0 → d = e) :
    ‖∑ d, F d‖ ^ 2 = ∑ d, ‖F d‖ ^ 2 := by
  by_cases hf : ∃ d, F d ≠ 0
  · obtain ⟨d, hd⟩ := hf
    have he (e) (hne : e ≠ d) : F e = 0 := by
      by_contra h
      exact hne (hu e d h hd)
    rw [Fintype.sum_eq_single d he, Fintype.sum_eq_single d]
    intro e hne
    simp only [he e hne, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  · push Not at hf
    simp only [hf, Finset.sum_const_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]

theorem rootFibreSum_energy_of_unique {D R : Type*} [Fintype D] [Fintype R]
    (root : D → R) (F : D → ℂ)
    (hu : ∀ d e, F d ≠ 0 → F e ≠ 0 → root d = root e → d = e) :
    (∑ s, ‖rootFibreSum root s F‖ ^ 2) = ∑ d, ‖F d‖ ^ 2 := by
  have hi (s : R) : ‖rootFibreSum root s F‖ ^ 2 =
      ∑ d, if root d = s then ‖F d‖ ^ 2 else 0 := by
    unfold rootFibreSum
    rw [norm_sum_sq_of_unique]
    · apply Finset.sum_congr rfl
      intro d _
      split_ifs <;> simp
    · intro d e hd he
      have hds : root d = s := by by_contra h; simp only [h, ite_false, if_false, ne_eq, not_true_eq_false] at hd
      have hes : root e = s := by by_contra h; simp only [h, ite_false, if_false, ne_eq, not_true_eq_false] at he
      exact hu d e (by simpa only [hds, ite_true, if_true] using hd)
        (by simpa only [hes, ite_true, if_true] using he) (hds.trans hes.symm)
  simp_rw [hi]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_MatchedDiagonalEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining one branch's original prior in the matched diagonal -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

private theorem matched_energy_point (a b A₀ x y : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (haA₀ : a ≤ A₀) (hbA₀ : b ≤ A₀) :
    a * b * x * y ≤ A₀ / 2 * (a * x ^ 2 + b * y ^ 2) := by
  have hsq := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x - y))
  have hx := mul_le_mul_of_nonneg_left hbA₀ (mul_nonneg ha (sq_nonneg x))
  have hy := mul_le_mul_of_nonneg_left haA₀ (mul_nonneg hb (sq_nonneg y))
  nlinarith only [hsq, hx, hy]

/-- The other branch's point weight is bounded only on simultaneous support.
Each resulting square retains its own original sampling law. -/
theorem matched_diagonal_energy {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (μ : A → ℝ) (ν : B → ℝ) (W : A → ℂ) (Z : B → ℂ)
    (θ : A → ℂ) (A₀ : ℝ) (hA₀ : 0 ≤ A₀)
    (hμ : ∀ a, 0 ≤ μ a) (hν : ∀ b, 0 ≤ ν b) (hθ : ∀ a, ‖θ a‖ ≤ 1)
    (hpoint : ∀ a, W a ≠ 0 → Z (e a) ≠ 0 → μ a ≤ A₀ ∧ ν (e a) ≤ A₀) :
    ‖∑ a, ((μ a * ν (e a) : ℝ) : ℂ) * W a * conj (Z (e a)) * θ a‖ ≤
      A₀ / 2 * ((∑ a, μ a * ‖W a‖ ^ 2) + ∑ b, ν b * ‖Z b‖ ^ 2) := by
  have hp (a : A) : μ a * ν (e a) * ‖W a‖ * ‖Z (e a)‖ ≤
      A₀ / 2 * (μ a * ‖W a‖ ^ 2 + ν (e a) * ‖Z (e a)‖ ^ 2) := by
    have hμa := hμ a
    have hνa := hν (e a)
    by_cases hW : W a = 0
    · simp only [hW, norm_zero, mul_zero, zero_mul, zero_pow (by decide : 2 ≠ 0), zero_add]
      positivity
    by_cases hZ : Z (e a) = 0
    · simp only [hZ, norm_zero, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
      positivity
    exact matched_energy_point _ _ _ _ _ (hμ a) (hν (e a))
      (hpoint a hW hZ).1 (hpoint a hW hZ).2
  calc
    _ ≤ ∑ a, ‖((μ a * ν (e a) : ℝ) : ℂ) * W a * conj (Z (e a)) * θ a‖ := norm_sum_le _ _
    _ ≤ ∑ a, μ a * ν (e a) * ‖W a‖ * ‖Z (e a)‖ := by
      apply Finset.sum_le_sum
      intro a _
      simp only [norm_mul, Complex.norm_conj, Complex.norm_real,
        Real.norm_of_nonneg (mul_nonneg (hμ a) (hν (e a)))]
      exact mul_le_of_le_one_right
        (mul_nonneg (mul_nonneg (mul_nonneg (hμ a) (hν (e a))) (norm_nonneg _))
          (norm_nonneg _)) (hθ a)
    _ ≤ ∑ a, A₀ / 2 * (μ a * ‖W a‖ ^ 2 + ν (e a) * ‖Z (e a)‖ ^ 2) :=
      Finset.sum_le_sum fun a _ => hp a
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, e.sum_comp (fun b => ν b * ‖Z b‖ ^ 2)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentUnweighted
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentCoreEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unique-history energy of the actual fixed-pivot character core -/

namespace Ostmann
open scoped BigOperators Classical

theorem retainedGraphRow_norm_le_one {I : Type*} [Fintype I] {p : ℕ}
    (χ : DirichletCharacter ℂ p) (b : Option I → Option I → ℤ)
    (i : I) (M : ZMod p) (x : I → ZMod p) :
    ‖retainedGraphRow χ b i M x‖ ≤ 1 := by
  unfold retainedGraphRow
  rw [norm_mul, norm_prod]
  calc
    _ ≤ (1 : ℝ) * 1 := mul_le_mul (character_zpow_norm_le_one _ _ _)
      (Finset.prod_le_one (fun _ _ => norm_nonneg _)
        (fun _ _ => character_zpow_norm_le_one _ _ _))
      (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) zero_le_one
    _ = 1 := one_mul 1

theorem retainedCharacterBranch_norm_le_one {H Y : Type*} [Fintype H] [Fintype Y]
    (L : H → ℕ) (U : Y → ℕ) [∀ h, Fact (L h).Prime] [∀ y, Fact (U y).Prime]
    (χH : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χY : Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (νH : H → ℂ) (νY : Y → ℂ) (M : ℕ)
    (hH : ∀ h, ‖νH h‖ ≤ 1) (hY : ∀ y, ‖νY y‖ ≤ 1) :
    ‖retainedCharacterBranch L U χH χY b νH νY M‖ ≤ 1 := by
  unfold retainedCharacterBranch
  rw [norm_mul, norm_prod, norm_prod]
  calc
    _ ≤ (1 : ℝ) * 1 := mul_le_mul ?_ ?_
      (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) zero_le_one
    _ = 1 := one_mul 1
  · apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
    intro h _
    rw [norm_mul]
    exact (mul_le_mul (hH h) (retainedGraphRow_norm_le_one _ _ _ _ _)
      (norm_nonneg _) zero_le_one).trans (one_mul 1).le
  · apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
    intro y _
    rw [norm_mul]
    exact (mul_le_mul (hY y) (retainedGraphRow_norm_le_one _ _ _ _ _)
      (norm_nonneg _) zero_le_one).trans (one_mul 1).le

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
theorem constituentCharacterCore_norm_le_full (hκ : ∀ i p, ‖κ i p‖ ≤ 1)
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) (d : D) :
    ‖constituentCharacterCore role size χ κ pivot n P hP childBound pivotBound ranges leaf hist u M (l, d)‖ ≤
      ‖fullAtomTransferWeight role childBound pivotBound ranges leaf n
        (scheduledInsertedAtoms role n M
          (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
          (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) (hist d)‖ := by
  let : ∀ h, Fact (l h : ℕ).Prime := fun h => ⟨hP _ (l h).property⟩
  let : ∀ y, Fact (u y : ℕ).Prime := fun y => ⟨hP _ (u y).property⟩
  unfold constituentCharacterCore
  rw [norm_mul]
  have hb := retainedCharacterBranch_norm_le_one (fun h => (l h : ℕ)) (fun y => (u y : ℕ))
    (fun h => χ (copyScheduleOrigin n h.val)) (fun y => χ (copyScheduleOrigin n y.val))
    (scheduledRetainedGraph (fun i : Σ a, Fin (size a) => role i.1) initialCompleteGraph pivot n)
    _ _ M
    (fun h => copyScheduleUnary_norm_le_one χ initialCompleteGraph pivot _
      (initialRegularUnary_norm_le_one χ κ hκ) n (hist d) h.val (l h))
    (fun y => copyScheduleUnary_norm_le_one χ initialCompleteGraph pivot _
      (initialRegularUnary_norm_le_one χ κ hκ) n (hist d) y.val (u y))
  apply (mul_le_of_le_one_right (norm_nonneg _) hb).trans
  unfold constituentUnweightedTransferWeight
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using norm_nonneg _

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SeparatedMatchingCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting bad bulk matchings while retaining every nonbulk slot -/

namespace Ostmann
open scoped Classical

theorem separatedMatching_pair_injective {A B : Type*} :
    Function.Injective (fun e : PartitionMatching (@sumSide A B) (@sumSide A B) =>
      (separatedMatchingLeft e, separatedMatchingRight e)) := by
  intro e f h
  apply PartitionMatching.restrict_injective
  funext side
  apply Equiv.ext
  intro x
  cases side with
  | false =>
    obtain ⟨b, rfl⟩ := (sumSideRightEquiv A B).surjective x
    have he := congrArg (fun z => (sumSideRightEquiv A B) (z.2 b)) h
    simpa only [separatedMatchingRight, Equiv.trans_apply, Equiv.apply_symm_apply] using he
  | true =>
    obtain ⟨a, rfl⟩ := (sumSideLeftEquiv A B).surjective x
    have he := congrArg (fun z => (sumSideLeftEquiv A B) (z.1 a)) h
    simpa only [separatedMatchingLeft, Equiv.trans_apply, Equiv.apply_symm_apply] using he

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
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_NaturalHistoryEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual rounded character cutoff in the fixed-pivot energy -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem uniform_constituent_natural_history_energy (n : ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (C₀ K d ε : ℝ) (hd : 0 ≤ d) (hε : 0 < ε)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K) :
    ∀ᶠ m : ℝ in atTop,
    ∀ {I : Type*} [Fintype I] (role : I → CopyScheduleRole) (size : I → ℕ)
      (childBound pivotBound : ℕ → ℕ)
      (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
      (i : Σ a, Fin (size a)) (_hi : role i.1 = .word)
      (_hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b)
      (p : I) (_hp : role p = .pivot n) (_hunique : ∀ j, role j = .pivot n → j = p)
      (X lo upper : ℝ) (M : ℕ)
      (P : Finset ℕ) (cells : (Σ a, Fin (size a)) → Finset ℕ),
      (∀ p ∈ P, p.Prime ∧ naturalTransferCutoff (d * m) m n < p) →
      0 < X → 1 < X * lo → Real.exp (d * m - C₀) ≤ lo →
      (∀ j, cells j ⊆ P) → (∀ j, (∑ p ∈ cells j, (p : ℝ)⁻¹) ≠ 0) →
      ∀ h J : ℕ,
      naturalTransferCutoff (d * m) m n ^ ((2 ^ (n + 1) - 1) * (n + 2)) ≤ 2 ^ h →
      (∀ p ∈ cells i, 2 ^ h ≤ p ∧ p < 2 ^ (h + J)) →
      ∀ a C₁ L : ℝ, 0 < a → 1 ≤ L →
      a ≤ ∑ p ∈ cells i, (p : ℝ)⁻¹ → (J : ℝ) ≤ Real.exp (C₁ * L) →
      constituentHistoryEnergy role size n P cells childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo upper)
        (scheduledFrequencyHistory (naturalTransferCutoff (d * m) m) n) M ≤
        Real.exp ((C₁ + max (Real.log (3 / a)) 0) * (2 ^ n : ℕ) * L + ε * m) := by
  filter_upwards [uniform_constituent_natural_fixedPivot_energy n ψ C₀ K d ε hd hε hψ]
    with m hm
  intro I instI role size childBound pivotBound ranges i hi hu p hp hunique X lo upper M P cells
    hP hX hXlo hlo hsub hmass h J hsmall hrange a C₁ L ha hL hcell hJ
  have he := hm role size childBound pivotBound ranges i hi hu X lo upper M P cells
    hP hX hXlo hlo hsub hmass h J hsmall hrange a C₁ L ha hL hcell hJ
  have hf := constituent_fixedPivot_prior_fubini role size n M p hp hunique P
    (fun j => primeSubsetPrior P (cells (copyScheduleOrigin n j.val)))
    (fun j => primeSubsetPrior_mass P _ (hsub _) (hmass _))
    (fun t v => ‖fullAtomTransferWeight role childBound pivotBound ranges
      (scheduleFourierLeaf role ψ X lo upper) n v
      (scheduledFrequencyHistory (naturalTransferCutoff (d * m) m) n t)‖ ^ 2)
  have hbound := (le_of_eq hf.symm).trans he
  simp only [enumeratedPartitionEquiv_rest, Sum.elim_inl, Sum.elim_inr] at hbound
  apply le_trans (le_of_eq ?_) hbound
  unfold constituentHistoryEnergy
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_NonbulkHarmonicBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The nonbulk normalization costs only its actual surviving slots -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem nonbulkCombinatorialCost_pos (n B : ℕ) : 0 < nonbulkCombinatorialCost n B := by
  unfold nonbulkCombinatorialCost
  positivity

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SupportedMatchedHistoryEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Matched history energy using only its nonzero support -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate

theorem permuted_root_energy_on_support {A R : Type*} [Fintype A] [Fintype R]
    (e : Equiv.Perm A) (μ : A → ℝ) (F : R → A → ℂ) (A₀ : ℝ)
    (hA₀ : 0 ≤ A₀) (hμ : ∀ a, 0 ≤ μ a) (hbound : ∀ s a, F s a ≠ 0 → μ a ≤ A₀) :
    ‖∑ s, ∑ a, ((μ a * μ (e a) : ℝ) : ℂ) * F s a * conj (F s (e a))‖ ≤
      A₀ * ∑ s, ∑ a, μ a * ‖F s a‖ ^ 2 := by
  have hs (s : R) := matched_diagonal_energy e μ μ (F s) (F s) (fun _ => 1) A₀
    hA₀ hμ hμ (fun _ => by simp) (fun a ha he => ⟨hbound s a ha, hbound s (e a) he⟩)
  simp only [mul_one] at hs
  calc
    _ ≤ ∑ s, ‖∑ a, ((μ a * μ (e a) : ℝ) : ℂ) * F s a * conj (F s (e a))‖ := norm_sum_le _ _
    _ ≤ ∑ s, A₀ / 2 * ((∑ a, μ a * ‖F s a‖ ^ 2) + ∑ a, μ a * ‖F s a‖ ^ 2) :=
      Finset.sum_le_sum fun s _ => hs s
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib]; ring

/-- Root equality is retained in the diagonal. Uniqueness removes the entire
frequency-history multiplicity from its square-energy estimate. -/
theorem permuted_history_energy_on_support {A D R : Type*}
    [Fintype A] [Fintype D] [Fintype R]
    (e : Equiv.Perm A) (μ : A → ℝ) (root : D → R) (F : D → A → ℂ) (A₀ : ℝ)
    (hA₀ : 0 ≤ A₀) (hμ : ∀ a, 0 ≤ μ a) (hbound : ∀ a d, F d a ≠ 0 → μ a ≤ A₀)
    (hunique : ∀ a d d', F d a ≠ 0 → F d' a ≠ 0 → root d = root d' → d = d') :
    ‖∑ d, ∑ d', if root d = root d' then
      ∑ a, ((μ a * μ (e a) : ℝ) : ℂ) * (F d a * conj (F d' (e a))) else 0‖ ≤
      A₀ * ∑ d, ∑ a, μ a * ‖F d a‖ ^ 2 := by
  rw [← rootFibreSum_weighted_pair root root (fun a => μ a * μ (e a)) F
    (fun d a => F d (e a))]
  have h := permuted_root_energy_on_support e μ (fun s a => rootFibreSum root s (fun d => F d a))
    A₀ hA₀ hμ (by
      intro s a ha
      by_contra hn
      have hz (d : D) : F d a = 0 := by
        by_contra hd
        exact hn (hbound a d hd)
      exact ha (by simp [rootFibreSum, hz]))
  simp only [mul_assoc] at h
  apply h.trans_eq
  congr 1
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, rootFibreSum_energy_of_unique root _ (hunique _), Finset.mul_sum]
  exact Finset.sum_comm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AnchorMatchingCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The number of code-preserving bulk matchings -/

namespace Ostmann

open scoped BigOperators Classical

theorem card_anchor_slot_fiber_le {n m : ℕ} (α : Fin n → ℤ)
    (hα : ∀ j, α j = 1 ∨ α j = -1) (code : Fin n → ℤ × ℤ) :
    Fintype.card {x : (Fin n → Bool) × Fin m // finiteAnchorCode α x.1 = code} ≤ 2 * m := by
  calc
    _ = Fintype.card ({t : Fin n → Bool // finiteAnchorCode α t = code} × Fin m) :=
      Fintype.card_congr (slotFiberEquiv (finiteAnchorCode α) m code)
    _ = Fintype.card {t : Fin n → Bool // finiteAnchorCode α t = code} * m := by
      rw [Fintype.card_prod, Fintype.card_fin]
    _ ≤ _ := Nat.mul_le_mul_right m (card_anchorCode_fiber_le_two α hα code)

/-- Each of the `2^n * m` labeled bulk slots has at most `2*m` possible
counterparts. Injectivity of the matching can only reduce the count. -/
theorem card_anchor_matching_le {n m : ℕ} (α : Fin n → ℤ)
    (hα : ∀ j, α j = 1 ∨ α j = -1) :
    Fintype.card (PartitionMatching
      (fun x : (Fin n → Bool) × Fin m => finiteAnchorCode α x.1)
      (fun x : (Fin n → Bool) × Fin m => finiteAnchorCode α x.1)) ≤
      (2 * m) ^ (2 ^ n * m) := by
  let D := (Fin n → Bool) × Fin m
  let code : D → (Fin n → ℤ × ℤ) := fun x => finiteAnchorCode α x.1
  let f : PartitionMatching code code → ∀ x : D, {y : D // code y = code x} :=
    fun e x => ⟨e.val x, e.property x⟩
  have hf : Function.Injective f := by
    intro e e' he
    apply Subtype.ext
    apply Equiv.ext
    intro x
    exact congrArg Subtype.val (congrFun he x)
  calc
    _ ≤ Fintype.card (∀ x : D, {y : D // code y = code x}) :=
      Fintype.card_le_of_injective f hf
    _ = ∏ x : D, Fintype.card {y : D // code y = code x} := Fintype.card_pi
    _ ≤ ∏ _x : D, 2 * m := Finset.prod_le_prod' fun x _ =>
      card_anchor_slot_fiber_le α hα (code x)
    _ = _ := by simp [D]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledActiveCharacters
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.copyScheduleVertexFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Only original positive roles can occur in the active H block -/

namespace Ostmann

theorem copyScheduleRole_origin_outside {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (v : CopyScheduleVertex I n) (hv : role (copyScheduleOrigin n v) = .outside) :
    copyScheduleRole role n v = .outside := by
  induction n with
  | zero => exact hv
  | succ n ih =>
    rcases v with ⟨b, v⟩ | v
    · change (copyScheduleRole role n v).afterCopy b = .outside
      have h := ih v hv
      rw [h]
      rfl
    · exact ih v hv

theorem copyScheduleH_origin_not_outside {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (h : CopyScheduleH role n) : role (copyScheduleOrigin n h.val) ≠ .outside := by
  intro he
  have hh := h.property.2
  rw [copyScheduleRole_origin_outside role n h.val he] at hh
  cases hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ActiveNonbulkCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting only original active nonword slots

Outside slots cannot enter H. In particular the negative copy of the whole
word must not be charged to the nonbulk harmonic normalization.
-/
namespace Ostmann
open scoped Classical

theorem survivorTrace_origin_injective {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (i j : CopyScheduleVertex I n)
    (hi : CopyScheduleSurvives role n i) (hj : CopyScheduleSurvives role n j)
    (ht : survivorTrace n i = survivorTrace n j)
    (ho : copyScheduleOrigin n i = copyScheduleOrigin n j) : i = j := by
  induction n with
  | zero => exact ho
  | succ n ih =>
    cases i with
    | inl ib =>
      rcases ib with ⟨b, i⟩
      cases j with
      | inl jb =>
        rcases jb with ⟨c, j⟩
        have ht' : survivorTrace n i = survivorTrace n j := by
          funext t
          simpa only [survivorTrace, Fin.snoc_castSucc] using congrFun ht t.castSucc
        have hbc : b = c := by
          simpa only [survivorTrace, Fin.snoc_last] using congrFun ht (Fin.last n)
        have hij := ih i j hi.1 hj.1 ht' ho
        subst j
        subst c
        rfl
      | inr j =>
        have ht' : survivorTrace n i = survivorTrace n j := by
          funext t
          simpa only [survivorTrace, Fin.snoc_castSucc] using congrFun ht t.castSucc
        have hij := ih i j hi.1 hj.1 ht' ho
        subst j
        exact False.elim (Bool.noConfusion (hi.2.symm.trans hj.2.1))
    | inr i =>
      cases j with
      | inl jb =>
        rcases jb with ⟨b, j⟩
        have ht' : survivorTrace n i = survivorTrace n j := by
          funext t
          simpa only [survivorTrace, Fin.snoc_castSucc] using congrFun ht t.castSucc
        have hij := ih i j hi.1 hj.1 ht' ho
        subst j
        exact False.elim (Bool.noConfusion (hj.2.symm.trans hi.2.1))
      | inr j =>
        have ht' : survivorTrace n i = survivorTrace n j := by
          funext t
          simpa only [survivorTrace, Fin.snoc_castSucc] using congrFun ht t.castSucc
        have hij := ih i j hi.1 hj.1 ht' ho
        subst j
        rfl

theorem copyScheduleRole_origin_word {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (i : CopyScheduleVertex I n) (hi : role (copyScheduleOrigin n i) = .word) :
    copyScheduleRole role n i = .word := by
  induction n with
  | zero => exact hi
  | succ n ih =>
    rcases i with ⟨b, i⟩ | i
    · change (copyScheduleRole role n i).afterCopy b = .word
      rw [ih i hi]
      rfl
    · exact ih i hi

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AnchorNonbulkBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nonbulk normalization at the manuscript's exponential bulk scale -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem eventual_anchor_nonbulk_cost (n B : ℕ) (c ε z : ℝ)
    (_hc : 0 ≤ c) (hε : 0 < ε) (hz : 0 < z)
    (hbudget : 4 * c * B ≤ ε * z) :
    ∀ᶠ L : ℝ in atTop, ∀ (m : ℕ), z * L / 2 ≤ (m : ℝ) →
      nonbulkCombinatorialCost n B * Real.exp (c * L * (2 ^ n * B : ℕ)) ≤
        Real.exp (ε * (2 ^ n : ℕ) * (m : ℝ)) := by
  let F := nonbulkCombinatorialCost n B
  let r : ℝ := (2 ^ n : ℕ)
  have hF : 0 < F := nonbulkCombinatorialCost_pos n B
  have hr : 0 < r := by dsimp [r]; positivity
  have hden : 0 < ε * r * z := mul_pos (mul_pos hε hr) hz
  filter_upwards [eventually_ge_atTop (4 * Real.log F / (ε * r * z)),
    eventually_ge_atTop (0 : ℝ)] with L hL hL0
  intro m hm
  have hLL : 4 * Real.log F ≤ ε * r * z * L := by nlinarith [(div_le_iff₀ hden).mp hL]
  have hM := mul_le_mul_of_nonneg_left hm (mul_pos hε hr).le
  have hlog : Real.log F ≤ ε / 2 * r * m := by nlinarith
  have hb := mul_le_mul_of_nonneg_right hbudget hL0
  have hb' := mul_le_mul_of_nonneg_left hb hr.le
  have hcost : c * L * (2 ^ n * B : ℕ) ≤ ε / 2 * r * m := by
    rw [Nat.cast_mul]
    change c * L * (r * B) ≤ _
    nlinarith
  change F * _ ≤ _
  rw [← Real.exp_log hF, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterDiagonalBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A depth-independent choice of the Section 4 diagonal gap constant -/
namespace Ostmann

/-- The bulk normalization costs `log 2 + log z`, while the prescribed gap
contains `20 log z`. The same choice of B works at every fixed depth. -/
theorem character_anchor_diagonal_small
    (B B₁ C z m gap energy prefactor : ℝ) (n : ℕ)
    (hz : 1 ≤ z) (hm : 0 ≤ m)
    (hB : 2 * B₁ + C + Real.log 2 + 6 ≤ B)
    (hgap : (B + 20 * Real.log z - 1) * (2 ^ n : ℕ) * m ≤ gap)
    (henergy : energy ≤ C * (2 ^ n : ℕ) * m)
    (hprefactor : prefactor ≤ Real.exp ((2 ^ n : ℕ) * m)) :
    Real.exp (-gap) * prefactor *
      Real.exp ((Real.log 2 + Real.log z) * (2 ^ n : ℕ) * m + energy) ≤
        Real.exp (-(2 * B₁ + 4) * (2 ^ n : ℕ) * m) := by
  have hrm : 0 ≤ (2 ^ n : ℕ) * m := mul_nonneg (Nat.cast_nonneg _) hm
  have hlog : 0 ≤ Real.log z := Real.log_nonneg hz
  have hb := mul_le_mul_of_nonneg_right hB hrm
  have hz' := mul_nonneg hlog hrm
  calc
    _ ≤ Real.exp (-gap) * Real.exp ((2 ^ n : ℕ) * m) *
        Real.exp ((Real.log 2 + Real.log z) * (2 ^ n : ℕ) * m + energy) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprefactor (Real.exp_nonneg _))
        (Real.exp_nonneg _)
    _ = Real.exp (-gap + (2 ^ n : ℕ) * m +
        ((Real.log 2 + Real.log z) * (2 ^ n : ℕ) * m + energy)) := by
      rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

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
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterHBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
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
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
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
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterDiagonalGap
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
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

/-- A fixed covering loss is absorbed by one unit of the linear gap coefficient. -/
theorem character_diagonal_gap_reserve (n : ℕ) (B z m C : ℝ)
    (hm : 0 ≤ m) (hC : 2 * C ≤ m) :
    (B + 20 * Real.log z - 1) * (2 ^ n : ℕ) * m ≤
      characterPivotGap B z m n - 2 * C := by
  have hp : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hh := mul_le_mul_of_nonneg_right hp hm
  have hs : 0 ≤ (4 : ℝ) ^ (n + 1) * Real.sqrt m := by positivity
  simp only [characterPivotGap, characterBaseGap, Nat.cast_pow, Nat.cast_ofNat]
  nlinarith

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
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterPrimeFrequency
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Natural character-frequency cutoffs lie below the actual prime ranges -/
namespace Ostmann
open Filter

/-- A fixed depth has a linear exponent, including the rounded bottom cutoff
with its original factor two in front of sqrt(m). -/
theorem transferErrorScale_linear_bound (k j : ℕ) (d m : ℝ)
    (hj : j ≤ k) (hd : 0 ≤ d) (hm : 1 ≤ m) :
    transferErrorScale (d * m) m j ≤ ((2 : ℝ) ^ k * d + 2 * (4 : ℝ) ^ k) * m := by
  have hs : Real.sqrt m ≤ m := (Real.sqrt_le_iff).mpr ⟨by linarith, by nlinarith⟩
  have htwo : (2 : ℝ) ^ j ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hj
  have hfour : (4 : ℝ) ^ j ≤ 4 ^ k := pow_le_pow_right₀ (by norm_num) hj
  have hfirst := mul_le_mul_of_nonneg_right htwo (mul_nonneg hd (by linarith : 0 ≤ m))
  have hsecond := mul_le_mul hfour hs (Real.sqrt_nonneg _) (by positivity : (0 : ℝ) ≤ 4 ^ k)
  unfold transferErrorScale
  nlinarith only [hfirst, hsecond]

/-- This supplies both the prime-frequency separation and the finite powers
of the cutoff used for denominator removal in the selected energy estimate. -/
theorem eventual_natural_cutoff_power_lt (k r : ℕ) (d z α c : ℝ)
    (hd : 0 ≤ d) (_hz : 0 ≤ z) (hα : 0 < α) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ m : ℝ, 1 ≤ m → m ≤ z * L → ∀ j ≤ k,
      (((naturalTransferCutoff (d * m) m j) ^ r : ℕ) : ℝ) <
        Real.exp (c * Real.exp (α * L)) := by
  let D := (2 : ℝ) ^ k * d + 2 * (4 : ℝ) ^ k
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hb := ((isLittleO_pow_exp_pos_mul_atTop 1 hα).const_mul_left ((r : ℝ) * D * z)).bound
    (by positivity : 0 < c / 2)
  filter_upwards [hb] with L hL m hm hmL j hj
  have hlin : (r : ℝ) * D * z * L < c * Real.exp (α * L) := by
    have hh : |(r : ℝ) * D * z * L| ≤ c / 2 * Real.exp (α * L) := by
      simpa only [Real.norm_eq_abs, pow_one, abs_of_pos (Real.exp_pos _)] using hL
    have hn := le_abs_self ((r : ℝ) * D * z * L)
    nlinarith only [hh, hn, Real.exp_pos (α * L), hc]
  have hscale := transferErrorScale_linear_bound k j d m hj hd hm
  have hm' := mul_le_mul_of_nonneg_left hmL (mul_nonneg (Nat.cast_nonneg r) hD)
  have he : (r : ℝ) * transferErrorScale (d * m) m j < c * Real.exp (α * L) := by
    change transferErrorScale (d * m) m j ≤ D * m at hscale
    have hs := mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg (α := ℝ) r)
    nlinarith only [hs, hm', hlin]
  calc
    _ = (naturalTransferCutoff (d * m) m j : ℝ) ^ r := by simp only [Nat.cast_pow]
    _ ≤ (Real.exp (transferErrorScale (d * m) m j)) ^ r :=
      pow_le_pow_left₀ (Nat.cast_nonneg _)
        (Nat.floor_le (Real.exp_pos _).le) r
    _ = Real.exp ((r : ℝ) * transferErrorScale (d * m) m j) := (Real.exp_nat_mul _ _).symm
    _ < _ := Real.exp_lt_exp.mpr he

theorem eventual_natural_cutoff_below_primes (k : ℕ) (d z α c : ℝ)
    (hd : 0 ≤ d) (hz : 0 ≤ z) (hα : 0 < α) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ m : ℝ, 1 ≤ m → m ≤ z * L →
      ∀ p : ℕ, Real.exp (c * Real.exp (α * L)) ≤ p →
        ∀ j ≤ k, naturalTransferCutoff (d * m) m j < p := by
  filter_upwards [eventual_natural_cutoff_power_lt k 1 d z α c hd hz hα hc] with L hL
  intro m hm hmL p hp j hj
  have hh := (hL m hm hmL j hj).trans_le hp
  simpa only [pow_one, Nat.cast_lt] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterEnergyPrimeRange
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dyadic data for the actual prime-cell energy theorem -/
namespace Ostmann
open Filter

 theorem naturalTransferCutoff_pos (d m : ℝ) (hd : 0 ≤ d) (hm : 0 ≤ m) (j : ℕ) :
    0 < naturalTransferCutoff (d * m) m j := by
  apply Nat.floor_pos.mpr
  apply Real.one_le_exp_iff.mpr
  unfold transferErrorScale
  positivity

theorem eventual_twice_natural_cutoff_power_le (k r : ℕ) (d z α : ℝ)
    (hd : 0 ≤ d) (hz : 0 ≤ z) (hα : 0 < α) :
    ∀ᶠ L : ℝ in atTop, ∀ m : ℝ, 1 ≤ m → m ≤ z * L →
      ∀ A : ℕ, Real.exp (Real.exp (α * L)) ≤ A → ∀ j ≤ k,
        2 * naturalTransferCutoff (d * m) m j ^ r ≤ A := by
  have hg : ∀ᶠ L : ℝ in atTop, 2 * Real.log 2 ≤ Real.exp (α * L) :=
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hα)).eventually
      (eventually_ge_atTop _)
  filter_upwards [hg, eventual_natural_cutoff_power_lt k r d z α (1 / 2)
    hd hz hα (by norm_num)] with L hg hcut
  intro m hm hmL A hA j hj
  have he : 2 * Real.exp ((1 / 2 : ℝ) * Real.exp (α * L)) ≤
      Real.exp (Real.exp (α * L)) := by
    calc
      _ = Real.exp (Real.log 2 + (1 / 2 : ℝ) * Real.exp (α * L)) := by
        rw [Real.exp_add, Real.exp_log (by norm_num)]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hc := mul_le_mul_of_nonneg_left (hcut m hm hmL j hj).le (by norm_num : (0 : ℝ) ≤ 2)
  have hf := hc.trans (he.trans hA)
  exact_mod_cast hf

/-- Both dyadic endpoints are explicit ceilings/floors of the physical prime
range. The finite denominator power is below the first dyadic point. -/
theorem eventual_character_energy_prime_range (k r : ℕ) (d z α β : ℝ)
    (hd : 0 ≤ d) (hz : 0 ≤ z) (hα : 0 < α) (hβ : 0 ≤ β) :
    ∀ᶠ L : ℝ in atTop, ∀ m : ℝ, 1 ≤ m → m ≤ z * L →
      ∀ S : Finset ℕ,
      (∀ p ∈ S, Real.exp (Real.exp (α * L)) ≤ p ∧
        (p : ℝ) ≤ Real.exp (Real.exp (β * L))) →
      ∃ h J : ℕ,
        (∀ j ≤ k, naturalTransferCutoff (d * m) m j ^ r ≤ 2 ^ h) ∧
        (∀ p ∈ S, 2 ^ h ≤ p ∧ p < 2 ^ (h + J)) ∧
        (J : ℝ) ≤ Real.exp ((β + Real.log ((Real.log 2)⁻¹ + 1)) * L) := by
  filter_upwards [eventual_twice_natural_cutoff_power_le k r d z α hd hz hα,
    eventually_ge_atTop (1 : ℝ)] with L hcut hL
  intro m hm hmL S hS
  let A : ℕ := ⌈Real.exp (Real.exp (α * L))⌉₊
  let B : ℕ := ⌊Real.exp (Real.exp (β * L))⌋₊
  have hbounds : ∀ p ∈ S, A ≤ p ∧ p ≤ B := by
    intro p hp
    exact ⟨Nat.ceil_le.mpr (hS p hp).1, Nat.le_floor (hS p hp).2⟩
  have hA : Real.exp (Real.exp (α * L)) ≤ (A : ℝ) := Nat.le_ceil _
  have hq (j : ℕ) : 0 < naturalTransferCutoff (d * m) m j ^ r :=
    pow_pos (naturalTransferCutoff_pos d m hd (by linarith) j) r
  have hranges (j : ℕ) (hj : j ≤ k) := dyadic_prime_range_cover A B
    (naturalTransferCutoff (d * m) m j ^ r) (hq j) (hcut m hm hmL A hA j hj) S hbounds
  refine ⟨Nat.log 2 A, Nat.log 2 B + 1, fun j hj => (hranges j hj).1,
    (hranges 0 (Nat.zero_le _)).2, ?_⟩
  exact dyadic_prime_range_count B β L hβ hL (Nat.floor_le (Real.exp_nonneg _))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterScheduleCounts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact active nonbulk count in the finite character schedule -/
namespace Ostmann
open scoped Classical BigOperators

theorem characterActiveSlot_card {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ) :
    Fintype.card {i : Σ v, Fin (characterSize m r f v) //
      characterRole k i.1 ≠ .word ∧ characterRole k i.1 ≠ .outside} =
        (∑ j, r j) + 2 * k := by
  rw [← Fintype.card_congr (characterActiveSlotEquiv m r f)]
  simp [Fintype.card_sigma, Nat.mul_comm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedBulkCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
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

theorem selectedSeparatedMatching_injective {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) :
    Function.Injective (selectedSeparatedMatching role n m bulk hbulk) := by
  intro e f h
  apply Subtype.ext
  apply Equiv.ext
  intro a
  obtain ⟨x, rfl⟩ := (selectedSplitHCoordinates role n m bulk hbulk).surjective a
  have he := congrArg (fun e => selectedSplitHCoordinates role n m bulk hbulk (e.val x)) h
  simpa only [selectedSeparatedMatching, Equiv.trans_apply, Equiv.apply_symm_apply] using he

/-- An H slot over an original bulk position is one of the selected leaves. -/
theorem mem_selectedBulkH_of_origin {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (h : CopyScheduleH role n) (i : Fin m) (hi : copyScheduleOrigin n h.val = bulk i) :
    h ∈ Set.range (selectedBulkH role n m bulk hbulk) := by
  have hw : copyScheduleRole role n h.val = .word :=
    copyScheduleRole_origin_word role n h.val (hi ▸ hbulk i)
  obtain ⟨t, j, hj, he⟩ := surviving_word_is_path role n h.val h.property.1 hw
  have hji : j = bulk i := by
    have hh := congrArg (copyScheduleOrigin n) he
    simpa only [copyScheduleOrigin_path, hi] using hh.symm
  subst j
  refine ⟨((scheduledPathEnumeration n).symm t, i), ?_⟩
  apply Subtype.ext
  change copySchedulePath n (scheduledPathEnumeration n ((scheduledPathEnumeration n).symm t))
    (bulk i) = h.val
  simpa only [Equiv.apply_symm_apply] using he.symm

theorem selectedNonbulkH_card_active {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ) (bulk : Fin m ↪ I)
    (hbulk : ∀ i, role (bulk i) = .word) :
    Fintype.card (SelectedNonbulkH role n m bulk hbulk) ≤
      2 ^ n * Fintype.card {i : I // i ∉ Set.range bulk ∧ role i ≠ .outside} := by
  let code : SelectedNonbulkH role n m bulk hbulk →
      (Fin n → Bool) × {i : I // i ∉ Set.range bulk ∧ role i ≠ .outside} :=
    fun h => (survivorTrace n h.val.val, ⟨copyScheduleOrigin n h.val.val, by
      constructor
      · rintro ⟨i, hi⟩
        exact h.property (mem_selectedBulkH_of_origin role n m bulk hbulk h.val i hi.symm)
      · exact copyScheduleH_origin_not_outside role n h.val⟩)
  have hc : Function.Injective code := by
    intro i j h
    apply Subtype.ext
    apply Subtype.ext
    exact survivorTrace_origin_injective role n i.val.val j.val.val i.val.property.1
      j.val.property.1 (congrArg Prod.fst h) (congrArg (fun z => z.2.val) h)
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    using Fintype.card_le_of_injective code hc

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterSelectedBulk
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original m bulk primes exclude the one top prime of each word -/
namespace Ostmann
open scoped Classical BigOperators

theorem character_word_not_bulk {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (i : Σ v, Fin (characterSize m r f v))
    (hw : characterRole k i.1 = .word) (hb : i ∉ Set.range (characterBulk m r f)) :
    i = characterTop m r f := by
  obtain ⟨t, ht⟩ := (characterWordEquiv m r f).surjective ⟨i, hw⟩
  have hti : (⟨(true, none), t⟩ : Σ v, Fin (characterSize m r f v)) = i :=
    congrArg Subtype.val ht
  rw [← hti] at hb ⊢
  by_cases hz : t = 0
  · subst t
    rfl
  · obtain ⟨j, hj⟩ := Fin.eq_succ_of_ne_zero hz
    subst t
    exact False.elim (hb ⟨j, rfl⟩)

/-- Before copying, exactly one further word slot is outside the bulk. -/
theorem character_original_nonbulk_card {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ) :
    Fintype.card {i : Σ v, Fin (characterSize m r f v) //
      i ∉ Set.range (characterBulk m r f) ∧ characterRole k i.1 ≠ .outside} ≤
        1 + ((∑ j, r j) + 2 * k) := by
  let A := {i : Σ v, Fin (characterSize m r f v) //
    characterRole k i.1 ≠ .word ∧ characterRole k i.1 ≠ .outside}
  let g : {i : Σ v, Fin (characterSize m r f v) //
      i ∉ Set.range (characterBulk m r f) ∧ characterRole k i.1 ≠ .outside} → Option A :=
    fun i => if h : characterRole k i.val.1 = .word then none
      else some ⟨i.val, h, i.property.2⟩
  have hg : Function.Injective g := by
    intro i j h
    by_cases hi : characterRole k i.val.1 = .word
    · by_cases hj : characterRole k j.val.1 = .word
      · apply Subtype.ext
        exact (character_word_not_bulk m r f i.val hi i.property.1).trans
          (character_word_not_bulk m r f j.val hj j.property.1).symm
      · simp [g, hi, hj] at h
    · by_cases hj : characterRole k j.val.1 = .word
      · simp [g, hi, hj] at h
      · have hh := Option.some.inj (show
          some (⟨i.val, hi, i.property.2⟩ : A) = some ⟨j.val, hj, j.property.2⟩ by
            simpa only [g, dite_eq_right hi, dite_eq_right hj] using h)
        exact Subtype.ext (congrArg (fun x : A => x.val) hh)
  have hc := Fintype.card_le_of_injective g hg
  simpa only [Fintype.card_option, A, characterActiveSlot_card, Nat.add_comm] using hc

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterFullPrimeCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original signed product law from its word and nonword prime cells -/
namespace Ostmann
open scoped Classical BigOperators

theorem characterFullPrimeCells_subset {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (P : Finset ℕ) (Q : Fin (m + 1) → Finset ℕ)
    (R : (v : CharacterCell k) → Fin (characterCellSize r f v) → Finset ℕ)
    (hQ : ∀ i, Q i ⊆ P) (hR : ∀ v i, R v i ⊆ P) :
    ∀ i, characterFullPrimeCells m r f Q R i ⊆ P := by
  rintro ⟨⟨b, v⟩, i⟩
  cases v with
  | none => exact hQ i
  | some v => exact hR v i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterPriorMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic mass floors for every original signed character marginal -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- The bulk has linear mass, the top shell has fixed positive mass, and all
remaining selected cells already have the proved exponential mass floor. -/
theorem eventual_full_character_mass_floor (a b C : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hC : 0 < C) :
    ∀ᶠ L : ℝ in atTop, ∀ (k m : ℕ) (r : Fin k → ℕ) (f : ℕ)
      (Q : Fin (m + 1) → Finset ℕ)
      (R : (v : CharacterCell k) → Fin (characterCellSize r f v) → Finset ℕ),
      b ≤ ∑ p ∈ Q 0, (p : ℝ)⁻¹ →
      (∀ i : Fin m, a * L ≤ ∑ p ∈ Q i.succ, (p : ℝ)⁻¹) →
      (∀ v i, Real.exp (-C * L) ≤ ∑ p ∈ R v i, (p : ℝ)⁻¹) →
      ∀ i, Real.exp (-C * L) ≤
        ∑ p ∈ characterFullPrimeCells m r f Q R i, (p : ℝ)⁻¹ := by
  have he : ∀ᶠ L : ℝ in atTop, Real.exp (-C * L) ≤ min a b :=
    ((Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hC)).eventually_le_const (lt_min ha hb)).mono (by
        intro L hL
        simpa only [Function.comp_apply, id_eq, neg_mul] using hL)
  filter_upwards [he, eventually_ge_atTop (1 : ℝ)] with L he hL
  intro k m r f Q R htop hbulk hrest
  have hword (i : Fin (m + 1)) : Real.exp (-C * L) ≤ ∑ p ∈ Q i, (p : ℝ)⁻¹ := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (he.trans (min_le_right _ _)).trans htop
    · have hh : a ≤ a * L := by nlinarith only [ha, hL]
      exact ((he.trans (min_le_left _ _)).trans hh).trans (hbulk j)
  rintro ⟨⟨sgn, v⟩, i⟩
  cases v with
  | none => exact hword i
  | some v => exact hrest v i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedAnchorBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected-bulk normalization includes the top slots exactly once per path -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem eventual_selected_anchor_nonbulk_cost (n B : ℕ) (c ε z : ℝ)
    (hc : 0 ≤ c) (hε : 0 < ε) (hz : 0 < z)
    (hbudget : 4 * c * B ≤ ε * z) :
    ∀ᶠ L : ℝ in atTop, ∀ {I : Type*} [Fintype I]
      (role : I → CopyScheduleRole) (m : ℕ) (bulk : Fin m ↪ I)
      (hbulk : ∀ i, role (bulk i) = .word),
      z * L / 2 ≤ (m : ℝ) →
      Fintype.card {i : I // i ∉ Set.range bulk ∧ role i ≠ .outside} ≤ B →
      ∀ mass : CopyScheduleH role n → ℝ,
      (∀ h : SelectedNonbulkH role n m bulk hbulk, Real.exp (-c * L) ≤ mass h.val) →
      (Fintype.card (SelectedNonbulkH role n m bulk hbulk)).factorial *
        (∏ h : SelectedNonbulkH role n m bulk hbulk, (mass h.val)⁻¹) ≤
          Real.exp (ε * (2 ^ n : ℕ) * (m : ℝ)) := by
  filter_upwards [eventual_anchor_nonbulk_cost n B c ε z hc hε hz hbudget,
    eventually_ge_atTop (0 : ℝ)] with L hL hL0
  intro I instI role m bulk hbulk hm hB mass hmass
  have hN : Fintype.card (SelectedNonbulkH role n m bulk hbulk) ≤ 2 ^ n * B :=
    (selectedNonbulkH_card_active role n m bulk hbulk).trans (Nat.mul_le_mul_left _ hB)
  have hf : ((Fintype.card (SelectedNonbulkH role n m bulk hbulk)).factorial : ℝ) ≤
      nonbulkCombinatorialCost n B := by
    have hfac : ((Fintype.card (SelectedNonbulkH role n m bulk hbulk)).factorial : ℝ) ≤
        (2 ^ n * B).factorial := by exact_mod_cast Nat.factorial_le hN
    have hA : (1 : ℝ) ≤ (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ (2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) from
        Nat.one_le_iff_ne_zero.mpr (by positivity))
    unfold nonbulkCombinatorialCost
    exact hfac.trans (le_mul_of_one_le_left (by positivity) hA)
  have hp : (∏ h : SelectedNonbulkH role n m bulk hbulk, (mass h.val)⁻¹) ≤
      Real.exp (c * L * (2 ^ n * B : ℕ)) := by
    calc
      _ ≤ ∏ _h : SelectedNonbulkH role n m bulk hbulk, Real.exp (c * L) := by
        apply Finset.prod_le_prod
        · intro h _
          exact inv_nonneg.mpr ((Real.exp_pos _).le.trans (hmass h))
        · intro h _
          have he := one_div_le_one_div_of_le (Real.exp_pos (-c * L)) (hmass h)
          simpa only [one_div, show -c * L = -(c * L) by ring, Real.exp_neg,
            inv_inv] using he
      _ = Real.exp (c * L * Fintype.card (SelectedNonbulkH role n m bulk hbulk)) := by
        simp only [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast hN)
        (mul_nonneg hc hL0))
  exact (mul_le_mul hf hp
    (Finset.prod_nonneg (fun h _ => inv_nonneg.mpr ((Real.exp_pos _).le.trans (hmass h))))
    (nonbulkCombinatorialCost_pos n B).le).trans (hL m hm)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterNonbulkBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual character top, pivot and anchor normalizers fit the cell budget -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem eventual_selected_nonbulk_cost (n B : ℕ) (c ε z : ℝ)
    (hc : 0 ≤ c) (hε : 0 < ε) (hz : 0 < z)
    (hbudget : 4 * c * B ≤ ε * z) :
    ∀ᶠ L : ℝ in atTop, ∀ {I : Type*} [Fintype I]
      (ρ : I → CopyScheduleRole) (m : ℕ) (bulk : Fin m ↪ I)
      (hbulk : ∀ i, ρ (bulk i) = .word),
      z * L / 2 ≤ (m : ℝ) →
      Nat.card {i : I // i ∉ Set.range bulk ∧ ρ i ≠ .outside} ≤ B →
      ∀ mass : CopyScheduleH ρ n → ℝ,
      (∀ h : SelectedNonbulkH ρ n m bulk hbulk, Real.exp (-c * L) ≤ mass h.val) →
      selectedNonbulkCost ρ n m bulk hbulk mass ≤
        Real.exp (ε * (2 ^ n : ℕ) * (m : ℝ)) := by
  filter_upwards [eventual_selected_anchor_nonbulk_cost n B c ε z hc hε hz hbudget] with L hL
  intro I instI ρ m bulk hbulk hm hcard mass hmass
  exact hL ρ m bulk hbulk hm (by simpa only [Nat.card_eq_fintype_card] using hcard) mass hmass

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledRootIndex
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The root frequency as an element of its actual finite cutoff range -/

namespace Ostmann

theorem scheduledRootIndex_eq_iff (V : ℕ → ℕ) (n : ℕ) (d d' : ScheduledFrequencyIndex V n) :
    scheduledRootIndex V n d = scheduledRootIndex V n d' ↔
      frequencyRoot n (scheduledFrequencyHistory V n d) =
        frequencyRoot n (scheduledFrequencyHistory V n d') := Subtype.ext_iff

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HarmonicTupleProductBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A tuple's actual product controls its original harmonic point mass -/
namespace Ostmann
open scoped Classical BigOperators

theorem harmonicTuple_point_product {H : Type*} [Fintype H]
    (P : Finset ℕ) (Q : H → Finset ℕ) (x : H → P) :
    (∏ h, primeSubsetPrior P (Q h) (x h)) ≤
      (∏ h, (∑ q ∈ Q h, (q : ℝ)⁻¹)⁻¹) * (∏ h, (x h : ℝ))⁻¹ := by
  calc
    _ ≤ ∏ h, (∑ q ∈ Q h, (q : ℝ)⁻¹)⁻¹ * (x h : ℝ)⁻¹ := by
      apply Finset.prod_le_prod (fun _ _ => primeSubsetPrior_nonneg _ _ _)
      intro h _
      unfold primeSubsetPrior
      split_ifs
      · rw [div_eq_mul_inv, mul_comm]
      · positivity
    _ = _ := by simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib]

theorem harmonicTuple_point_le_product_lower {H : Type*} [Fintype H]
    (P : Finset ℕ) (Q : H → Finset ℕ) (x : H → P) (lower : ℝ)
    (hlower : 0 < lower) (hprod : lower ≤ ∏ h, (x h : ℝ)) :
    (∏ h, primeSubsetPrior P (Q h) (x h)) ≤
      (∏ h, (∑ q ∈ Q h, (q : ℝ)⁻¹)⁻¹) * lower⁻¹ := by
  apply (harmonicTuple_point_product P Q x).trans
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun _ _ => by positivity))
  exact inv_anti₀ hlower hprod

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentSupportedMatchingEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The diagonal uses the actual supported product lower bound -/
namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

/-- This holds for every matching, including the bad component-rich ones.
Its small factor is the exact counterpart harmonic normalizer and product
lower endpoint. The retained square has its original H prime law. -/
theorem constituent_matching_energy_on_product {I D R : Type*}
    [Fintype I] [Fintype D] [Fintype R]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (hκ : ∀ i p, ‖κ i p‖ ≤ 1)
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (hhist : Function.Injective hist) (root : D → R)
    (hroot : ∀ d d', root d = root d' → frequencyRoot n (hist d) = frequencyRoot n (hist d'))
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n))
    (lower : ℝ) (hlower : 0 < lower)
    (hproduct : ∀ (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) (d : D),
      fullAtomTransferWeight role childBound pivotBound ranges leaf n
        (scheduledInsertedAtoms role n M
          (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
          (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) (hist d) ≠ 0 →
      lower ≤ ∏ h, (l h : ℝ)) :
    ‖∑ d : D, ∑ d' : D, if root d = root d' then
      ∑ l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P,
        constituentCharacterCoefficient role size χ κ pivot n P hP Q
          childBound pivotBound ranges leaf hist u M (l, d) *
        conj (constituentCharacterCoefficient role size χ κ pivot n P hP Q
          childBound pivotBound ranges leaf hist u M (l ∘ e.symm, d')) else 0‖ ≤
      ((∏ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
          (∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)⁻¹) * lower⁻¹) *
      ∑ d : D, ∑ l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P,
        (∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (l h)) *
        ‖fullAtomTransferWeight role childBound pivotBound ranges leaf n
          (scheduledInsertedAtoms role n M
            (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
            (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) (hist d)‖ ^ 2 := by
  let H := CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n
  let μ := fun l : H → P => ∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (l h)
  let A₀ := (∏ h : H, (∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)⁻¹) * lower⁻¹
  have hA₀ : 0 ≤ A₀ := by
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun _ _ => by positivity)
    · exact inv_nonneg.mpr hlower.le
  let E : Equiv.Perm (H → P) :=
    { toFun := fun l => l ∘ e.symm
      invFun := fun l => l ∘ e
      left_inv := by intro l; funext h; simp
      right_inv := by intro l; funext h; simp }
  let F := fun d l => constituentCharacterCore role size χ κ pivot n P hP
    childBound pivotBound ranges leaf hist u M (l, d)
  have he := permuted_history_energy_on_support E μ root F A₀ hA₀
    (fun _ => Finset.prod_nonneg (fun _ _ => primeSubsetPrior_nonneg _ _ _))
    (by
      intro l d hd
      have hfull := (norm_pos_iff.mpr hd).trans_le
        (constituentCharacterCore_norm_le_full role size χ κ pivot n P hP childBound
          pivotBound ranges leaf hist u M hκ l d)
      exact harmonicTuple_point_le_product_lower P _ l lower hlower
        (hproduct l d (norm_pos_iff.mp hfull)))
    (fun l d d' hd hd' hr => hhist (validTransferHistory_unique
      (scheduleAtomSystem role childBound pivotBound) n _ _ _
      (constituentCharacterCore_nonzero_valid role size χ κ pivot n P hP childBound pivotBound
        ranges leaf hist u M l d hd)
      (constituentCharacterCore_nonzero_valid role size χ κ pivot n P hP childBound pivotBound
        ranges leaf hist u M l d' hd') (hroot d d' hr)))
  have hpair (l : H → P) (d d' : D) :
      constituentCharacterCoefficient role size χ κ pivot n P hP Q
        childBound pivotBound ranges leaf hist u M (l, d) *
      conj (constituentCharacterCoefficient role size χ κ pivot n P hP Q
        childBound pivotBound ranges leaf hist u M (l ∘ e.symm, d')) =
      ((μ l * μ (E l) : ℝ) : ℂ) * (F d l * conj (F d' (E l))) := by
    rw [constituentCharacterCoefficient_factor, constituentCharacterCoefficient_factor]
    simp only [map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
    dsimp only [μ, E, Equiv.coe_fn_mk, F]
    ring
  simp_rw [hpair]
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ hA₀
  apply Finset.sum_le_sum
  intro d _
  apply Finset.sum_le_sum
  intro l _
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
    (constituentCharacterCore_norm_le_full role size χ κ pivot n P hP childBound pivotBound
      ranges leaf hist u M hκ l d) 2) (Finset.prod_nonneg (fun _ _ => primeSubsetPrior_nonneg _ _ _))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentSupportedMatchingAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Averaging matching families with the original single outside prime law -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate

theorem constituent_matching_family_energy_on_product {I D R : Type*}
    [Fintype I] [Fintype D] [Fintype R]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (hκ : ∀ i p, ‖κ i p‖ ≤ 1)
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (hhist : Function.Injective hist) (root : D → R)
    (hroot : ∀ d d', root d = root d' → frequencyRoot n (hist d) = frequencyRoot n (hist d'))
    (M : ℕ)
    (S : Finset (Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)))
    (lower : ℝ) (hlower : 0 < lower)
    (hproduct : ∀ (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P)
      (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) (d : D),
      fullAtomTransferWeight role childBound pivotBound ranges leaf n
        (scheduledInsertedAtoms role n M
          (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
          (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) (hist d) ≠ 0 →
      lower ≤ ∏ h, (l h : ℝ)) :
    ‖∑ u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P,
      ((∏ y, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) (u y) : ℝ) : ℂ) *
      ∑ e ∈ S, ∑ d : D, ∑ d' : D, if root d = root d' then
      ∑ l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P,
        constituentCharacterCoefficient role size χ κ pivot n P hP Q
          childBound pivotBound ranges leaf hist u M (l, d) *
        conj (constituentCharacterCoefficient role size χ κ pivot n P hP Q
          childBound pivotBound ranges leaf hist u M (l ∘ e.symm, d')) else 0‖ ≤
      (S.card : ℝ) * ((∏ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
          (∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)⁻¹) * lower⁻¹) *
      ∑ u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P,
        (∏ y, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) (u y)) *
        ∑ d : D, ∑ l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P,
        (∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (l h)) *
        ‖fullAtomTransferWeight role childBound pivotBound ranges leaf n
          (scheduledInsertedAtoms role n M
            (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
            (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) (hist d)‖ ^ 2 := by
  let H := CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n
  let Y := CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n
  let μ := fun u : Y → P => ∏ y, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) (u y)
  let A₀ := (∏ h : H, (∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)⁻¹) * lower⁻¹
  let F := fun (e : Equiv.Perm H) (u : Y → P) =>
    ∑ d : D, ∑ d' : D, if root d = root d' then ∑ l : H → P,
      constituentCharacterCoefficient role size χ κ pivot n P hP Q
        childBound pivotBound ranges leaf hist u M (l, d) *
      conj (constituentCharacterCoefficient role size χ κ pivot n P hP Q
        childBound pivotBound ranges leaf hist u M (l ∘ e.symm, d')) else 0
  let E := fun u : Y → P => ∑ d : D, ∑ l : H → P,
    (∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (l h)) *
    ‖fullAtomTransferWeight role childBound pivotBound ranges leaf n
      (scheduledInsertedAtoms role n M
        (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
        (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) (hist d)‖ ^ 2
  have hμ (u) : 0 ≤ μ u := Finset.prod_nonneg (fun _ _ => primeSubsetPrior_nonneg _ _ _)
  have hf (e : Equiv.Perm H) (u : Y → P) : ‖F e u‖ ≤ A₀ * E u :=
    constituent_matching_energy_on_product role size χ κ pivot hκ n P hP Q childBound pivotBound
      ranges leaf hist hhist root hroot u M e lower hlower (hproduct u)
  change ‖∑ u : Y → P, (μ u : ℂ) * ∑ e ∈ S, F e u‖ ≤
    (S.card : ℝ) * A₀ * ∑ u, μ u * E u
  calc
    _ ≤ ∑ u : Y → P, ‖(μ u : ℂ) * ∑ e ∈ S, F e u‖ := norm_sum_le _ _
    _ ≤ ∑ u : Y → P, μ u * ∑ e ∈ S, ‖F e u‖ := by
      apply Finset.sum_le_sum
      intro u _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hμ u)]
      exact mul_le_mul_of_nonneg_left (norm_sum_le S _) (hμ u)
    _ ≤ ∑ u : Y → P, μ u * ∑ _e ∈ S, A₀ * E u := by
      apply Finset.sum_le_sum
      intro u _
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun e _ => hf e u)) (hμ u)
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      simp_rw [show ∀ u : Y → P, μ u * ((S.card : ℝ) * (A₀ * E u)) =
        ((S.card : ℝ) * A₀) * (μ u * E u) by intro u; ring]
      exact (Finset.mul_sum _ _ _).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentSupportedFamilyEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-prior matching energy after the external pivot is summed -/

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

theorem constituentMatchingFamily_norm_on_product {R : Type*} [Fintype R]
    (hκ : ∀ i p, ‖κ i p‖ ≤ 1) (hhist : Function.Injective hist) (root : D → R)
    (hroot : ∀ d d', root d = root d' ↔ frequencyRoot n (hist d) = frequencyRoot n (hist d'))
    (M : ℕ)
    (S : Finset (Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)))
    (lower : ℝ) (hlower : 0 < lower)
    (hproduct : ∀ (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P)
      (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) (d : D),
      fullAtomTransferWeight role childBound pivotBound ranges leaf n
        (scheduledInsertedAtoms role n M
          (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
          (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) (hist d) ≠ 0 →
      lower ≤ ∏ h, (l h : ℝ)) :
    ‖constituentMatchingFamily role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist S M‖ ≤
      (S.card : ℝ) * ((∏ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
        (∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)⁻¹) * lower⁻¹) *
        constituentHistoryEnergy role size n P Q childBound pivotBound ranges leaf hist M := by
  have h := constituent_matching_family_energy_on_product role size χ κ pivot hκ n P hP Q
    childBound pivotBound ranges leaf hist hhist root (fun d d' hd => (hroot d d').mp hd)
    M S lower hlower hproduct
  simpa only [constituentMatchingFamily, primeMatchingContribution, constituentHistoryEnergy, hroot, finite_univ_canonical] using h

theorem constituentMatchingFamily_interval_on_product {R : Type*} [Fintype R]
    (hκ : ∀ i p, ‖κ i p‖ ≤ 1) (hhist : Function.Injective hist) (root : D → R)
    (hroot : ∀ d d', root d = root d' ↔ frequencyRoot n (hist d) = frequencyRoot n (hist d'))
    (S : Finset (Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)))
    (a b : ℕ) (ha : 0 < a) (gap E lower : ℝ) (hE : 0 ≤ E) (hlower : 0 < lower)
    (hgap : Real.exp gap * (b : ℝ) ≤ lower)
    (hproduct : ∀ M ∈ Finset.Icc a b, ∀ (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P)
      (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) (d : D),
      fullAtomTransferWeight role childBound pivotBound ranges leaf n
        (scheduledInsertedAtoms role n M
          (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
          (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) (hist d) ≠ 0 →
      lower ≤ ∏ h, (l h : ℝ))
    (henergy : ∀ M ∈ Finset.Icc a b,
      constituentHistoryEnergy role size n P Q childBound pivotBound ranges leaf hist M ≤ E) :
    (∑ M ∈ Finset.Icc a b,
      (constituentMatchingFamily role size χ κ pivot n P hP Q
        childBound pivotBound ranges leaf hist S M).re) ≤
      Real.exp (-gap) * ((S.card : ℝ) *
        ∏ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
          (∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)⁻¹) * E := by
  let Z : ℝ := ∏ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
    (∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)⁻¹
  have hZ : 0 ≤ Z := Finset.prod_nonneg fun h _ => inv_nonneg.mpr
    (Finset.sum_nonneg fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p))
  apply finite_pivot_sum_bound a b ha
    (fun M => constituentMatchingFamily role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist S M)
    ((S.card : ℝ) * Z) E gap (mul_nonneg (Nat.cast_nonneg _) hZ) hE Unit (fun _ => lower) (fun _ => hlower) (by simpa using hgap)
  intro M hM
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_unit, pow_one]
  calc
    _ ≤ (S.card : ℝ) * (Z * lower⁻¹) *
        constituentHistoryEnergy role size n P Q childBound pivotBound ranges leaf hist M :=
      constituentMatchingFamily_norm_on_product role size χ κ pivot n P hP Q childBound pivotBound
        ranges leaf hist hκ hhist root hroot M S lower hlower (hproduct M hM)
    _ ≤ (S.card : ℝ) * (Z * lower⁻¹) * E :=
      mul_le_mul_of_nonneg_left (henergy M hM) (mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg hZ (inv_nonneg.mpr hlower.le)))
    _ = _ := by ring

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FullAtomProductBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Whole-atom products on every nonzero fixed-pivot history -/
namespace Ostmann
open scoped Classical BigOperators

theorem fullAtomTransferWeight_inserted_H_product_bounds {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (childBound pivotBound : ℕ → ℕ) (lo hi : I → ℕ)
    (leaf : ScheduleAtomState role → ℤ → ℂ) (t : FrequencyTree ℤ n)
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → ℕ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → ℕ) (M : ℕ)
    (hw : fullAtomTransferWeight role childBound pivotBound (atomIntervalRanges role lo hi) leaf n
      (scheduledInsertedAtoms role n M
        (fun h => ∏ k, l (constituentH role size n h k))
        (fun y => ∏ k, u (constituentY role size n y k))) t ≠ 0) :
    (∏ h : CopyScheduleH role n, lo (copyScheduleOrigin n h.val)) ≤ (∏ h, l h) ∧
      (∏ h, l h) ≤ ∏ h : CopyScheduleH role n, hi (copyScheduleOrigin n h.val) := by
  have hr := (atomIntervalRanges_holds_iff role lo hi n _).mp
    (fun r hr => fullAtomTransferWeight_top_range role childBound pivotBound
      (atomIntervalRanges role lo hi) leaf n _ t hw r hr)
  have hh (h : CopyScheduleH role n) :
      lo (copyScheduleOrigin n h.val) ≤ ∏ k, l (constituentH role size n h k) ∧
      (∏ k, l (constituentH role size n h k)) ≤ hi (copyScheduleOrigin n h.val) := by
    simpa only [scheduledInsertedAtoms_H] using hr ⟨h.val, h.property.1⟩
  rw [← constituentH_product role size n l]
  exact ⟨Finset.prod_le_prod' (fun h _ => (hh h).1),
    Finset.prod_le_prod' (fun h _ => (hh h).2)⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledAnchorMatchingCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Code-preserving matchings of the actual scheduled bulk slots -/

namespace Ostmann
open scoped Classical

theorem card_scheduled_bulk_anchor_matching (n m : ℕ) :
    Fintype.card (PartitionMatching (@scheduledBulkAnchorCode n m)
      (@scheduledBulkAnchorCode n m)) ≤ (2 * m) ^ (2 ^ n * m) := by
  let g := (scheduledPathEnumeration n).prodCongr (Equiv.refl (Fin m))
  let f : PartitionMatching (@scheduledBulkAnchorCode n m) (@scheduledBulkAnchorCode n m) →
      PartitionMatching (fun x : (Fin n → Bool) × Fin m => finiteAnchorCode (fun _ => 1) x.1)
        (fun x : (Fin n → Bool) × Fin m => finiteAnchorCode (fun _ => 1) x.1) :=
    fun e => ⟨(g.symm.trans e.val).trans g, by
      intro x
      have h := e.property (g.symm x)
      simpa [scheduledBulkAnchorCode, g] using h⟩
  have hf : Function.Injective f := by
    intro e e' he
    apply Subtype.ext
    apply Equiv.ext
    intro x
    have h := congrArg (fun z => g.symm (z.val (g x))) he
    simpa only [f, Equiv.trans_apply, Equiv.symm_apply_apply] using h
  exact (Fintype.card_le_of_injective f hf).trans
    (card_anchor_matching_le (fun _ => 1) (fun _ => Or.inl rfl))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledAnchorHarmonicBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original-prior cost of code-preserving matchings -/
namespace Ostmann
open scoped Classical BigOperators

theorem anchor_harmonic_entropy (r m : ℕ) (L z : ℝ)
    (hL : 0 < L) (hz : 0 < z) (hm : (m : ℝ) ≤ z * L) :
    ((2 * m : ℕ) : ℝ) ^ (r * m) * (L⁻¹) ^ (r * m) ≤
      Real.exp ((Real.log 2 + Real.log z) * (r * m : ℕ)) := by
  have hratio : (m : ℝ) * L⁻¹ ≤ z := by
    have hh := mul_le_mul_of_nonneg_right hm (inv_nonneg.mpr hL.le)
    simpa only [mul_assoc, mul_inv_cancel₀ hL.ne', mul_one] using hh
  have hbase : ((2 * m : ℕ) : ℝ) * L⁻¹ ≤ 2 * z := by
    push_cast
    nlinarith
  calc
    _ = (((2 * m : ℕ) : ℝ) * L⁻¹) ^ (r * m) := (mul_pow _ _ _).symm
    _ ≤ (2 * z) ^ (r * m) := pow_le_pow_left₀ (by positivity) hbase _
    _ = _ := by
      rw [← Real.exp_log (show 0 < 2 * z by positivity), ← Real.exp_nat_mul,
        Real.log_mul (by norm_num) hz.ne']
      congr 1
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedAnchorMatchingCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Code-preserving matchings of the selected bulk, excluding the top slot -/
namespace Ostmann
open scoped Classical

theorem selected_anchor_matching_count {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) :
    Fintype.card {e : PartitionMatching (selectedBulkLabel role n m bulk hbulk)
      (selectedBulkLabel role n m bulk hbulk) // PreservesSelectedAnchorCode role n m bulk hbulk e} ≤
      (2 * m) ^ (2 ^ n * m) * (Fintype.card (SelectedNonbulkH role n m bulk hbulk)).factorial := by
  let f : {e : PartitionMatching (selectedBulkLabel role n m bulk hbulk) (selectedBulkLabel role n m bulk hbulk) //
      PreservesSelectedAnchorCode role n m bulk hbulk e} →
      PartitionMatching (@scheduledBulkAnchorCode n m) (@scheduledBulkAnchorCode n m) ×
        Equiv.Perm (SelectedNonbulkH role n m bulk hbulk) :=
    fun e => (⟨separatedMatchingLeft (selectedSeparatedMatching role n m bulk hbulk e.val), e.property⟩,
      separatedMatchingRight (selectedSeparatedMatching role n m bulk hbulk e.val))
  have hf : Function.Injective f := by
    intro e e' h
    apply Subtype.ext
    apply selectedSeparatedMatching_injective role n m bulk hbulk
    apply separatedMatching_pair_injective
    have hl : separatedMatchingLeft (selectedSeparatedMatching role n m bulk hbulk e.val) =
        separatedMatchingLeft (selectedSeparatedMatching role n m bulk hbulk e'.val) :=
      congrArg (fun z => z.1.val) h
    have hr : separatedMatchingRight (selectedSeparatedMatching role n m bulk hbulk e.val) =
        separatedMatchingRight (selectedSeparatedMatching role n m bulk hbulk e'.val) :=
      congrArg Prod.snd h
    exact Prod.ext hl hr
  have hc := Fintype.card_le_of_injective f hf
  rw [Fintype.card_prod, Fintype.card_perm] at hc
  exact hc.trans (Nat.mul_le_mul_right _ (card_scheduled_bulk_anchor_matching n m))

theorem selectedAnchorMatchingSet_card_le {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) :
    (selectedAnchorMatchingSet role n m bulk hbulk).card ≤
      (2 * m) ^ (2 ^ n * m) * (Fintype.card (SelectedNonbulkH role n m bulk hbulk)).factorial :=
  (Finset.card_image_le.trans_eq (by simp)).trans (selected_anchor_matching_count role n m bulk hbulk)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedAnchorHarmonicBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic normalization for the selected bulk and complementary top slots -/
namespace Ostmann
open scoped Classical BigOperators

theorem selected_harmonic_normalization_bound {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (bulk : Fin m ↪ I) (hrole : ∀ i, role (bulk i) = .word)
    (mass : CopyScheduleH role n → ℝ) (L : ℝ) (hL : 0 < L)
    (hmass : ∀ h, 0 < mass h)
    (hbulk : ∀ x, L ≤ mass (selectedBulkCoordinates role n m bulk hrole x).val) :
    (∏ h, (mass h)⁻¹) ≤ (L⁻¹) ^ (2 ^ n * m) *
      ∏ h : SelectedNonbulkH role n m bulk hrole, (mass h.val)⁻¹ := by
  rw [← Equiv.prod_comp (selectedSplitHCoordinates role n m bulk hrole), Fintype.prod_sum_type]
  change (∏ x : Fin (2 ^ n) × Fin m, (mass (selectedBulkCoordinates role n m bulk hrole x).val)⁻¹) *
      (∏ h : SelectedNonbulkH role n m bulk hrole, (mass h.val)⁻¹) ≤ _
  apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun h _ => (inv_pos.mpr (hmass h.val)).le))
  calc
    _ ≤ ∏ _x : Fin (2 ^ n) × Fin m, L⁻¹ := by
      apply Finset.prod_le_prod
      · intro x _; exact (inv_pos.mpr (hmass _)).le
      · intro x _; simpa only [one_div] using one_div_le_one_div_of_le hL (hbulk x)
    _ = _ := by simp

theorem selected_anchor_harmonic_bound {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (bulk : Fin m ↪ I) (hrole : ∀ i, role (bulk i) = .word)
    (mass : CopyScheduleH role n → ℝ) (L z : ℝ) (hL : 0 < L) (hz : 0 < z)
    (hm : (m : ℝ) ≤ z * L) (hmass : ∀ h, 0 < mass h)
    (hbulk : ∀ x, L ≤ mass (selectedBulkCoordinates role n m bulk hrole x).val) :
    ((selectedAnchorMatchingSet role n m bulk hrole).card : ℝ) * (∏ h, (mass h)⁻¹) ≤
      (Fintype.card (SelectedNonbulkH role n m bulk hrole)).factorial *
        (∏ h : SelectedNonbulkH role n m bulk hrole, (mass h.val)⁻¹) *
        Real.exp ((Real.log 2 + Real.log z) * (2 ^ n * m : ℕ)) := by
  let R : ℝ := ∏ h : SelectedNonbulkH role n m bulk hrole, (mass h.val)⁻¹
  have hR : 0 ≤ R := Finset.prod_nonneg (fun h _ => (inv_pos.mpr (hmass h.val)).le)
  have hc : ((selectedAnchorMatchingSet role n m bulk hrole).card : ℝ) ≤
      ((2 * m : ℕ) : ℝ) ^ (2 ^ n * m) *
        (Fintype.card (SelectedNonbulkH role n m bulk hrole)).factorial := by
    exact_mod_cast selectedAnchorMatchingSet_card_le role n m bulk hrole
  have hp := selected_harmonic_normalization_bound role n m bulk hrole mass L hL hmass hbulk
  calc
    _ ≤ (((2 * m : ℕ) : ℝ) ^ (2 ^ n * m) *
        (Fintype.card (SelectedNonbulkH role n m bulk hrole)).factorial) *
        ((L⁻¹) ^ (2 ^ n * m) * R) :=
      mul_le_mul hc hp (Finset.prod_nonneg (fun h _ => (inv_pos.mpr (hmass h)).le)) (by positivity)
    _ = (Fintype.card (SelectedNonbulkH role n m bulk hrole)).factorial * R *
        (((2 * m : ℕ) : ℝ) ^ (2 ^ n * m) * (L⁻¹) ^ (2 ^ n * m)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (anchor_harmonic_entropy (2 ^ n) m L z hL hz hm)
      (mul_nonneg (by positivity) hR)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedAnchorProductBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual code-preserving contribution after summing the external pivot -/

namespace Ostmann
open scoped Classical BigOperators

theorem selected_anchor_diagonal_on_product {I D R : Type*}
    [Fintype I] [Fintype D] [Fintype R]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n m : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (hκ : ∀ i p, ‖κ i p‖ ≤ 1) (hhist : Function.Injective hist) (root : D → R)
    (hroot : ∀ d d', root d = root d' ↔ frequencyRoot n (hist d) = frequencyRoot n (hist d'))
    (bulk : Fin m ↪ (Σ a, Fin (size a)))
    (hrole : ∀ i, role (bulk i).1 = .word)
    (lo hi : I → ℕ) (hranges : ranges = atomIntervalRanges role lo hi)
    (a b : ℕ) (ha : 0 < a) (gap E L z : ℝ)
    (hlower : 0 < ∏ h : CopyScheduleH role n, (lo (copyScheduleOrigin n h.val) : ℝ))
    (hgap : Real.exp gap * (b : ℝ) ≤ ∏ h : CopyScheduleH role n, (lo (copyScheduleOrigin n h.val) : ℝ))
    (hL : 0 < L) (hz : 0 < z) (hm : (m : ℝ) ≤ z * L)
    (hmass : ∀ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
      0 < ∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)
    (hbulk : ∀ x, L ≤ ∑ p ∈ Q (copyScheduleOrigin n
      (selectedBulkCoordinates (fun i : Σ a, Fin (size a) => role i.1) n m bulk hrole x).val.val),
        (p : ℝ)⁻¹)
    (henergy : ∀ M ∈ Finset.Icc a b,
      constituentHistoryEnergy role size n P Q childBound pivotBound ranges leaf hist M ≤
        Real.exp E) :
    (∑ M ∈ Finset.Icc a b,
      (constituentMatchingFamily role size χ κ pivot n P hP Q childBound pivotBound ranges
        leaf hist (selectedAnchorMatchingSet
          (fun i : Σ a, Fin (size a) => role i.1) n m bulk hrole) M).re) ≤
      Real.exp (-gap) *
        (Fintype.card (SelectedNonbulkH (fun i : Σ a, Fin (size a) => role i.1) n m bulk hrole)).factorial *
        (∏ h : SelectedNonbulkH (fun i : Σ a, Fin (size a) => role i.1) n m bulk hrole,
          (∑ p ∈ Q (copyScheduleOrigin n h.val.val), (p : ℝ)⁻¹)⁻¹) *
        Real.exp ((Real.log 2 + Real.log z) * (2 ^ n * m : ℕ) + E) := by
  have h₁ := constituentMatchingFamily_interval_on_product role size χ κ pivot n P hP Q
    childBound pivotBound ranges leaf hist hκ hhist root hroot
    (selectedAnchorMatchingSet (fun i : Σ a, Fin (size a) => role i.1) n m bulk hrole)
    a b ha gap (Real.exp E) (∏ h : CopyScheduleH role n, (lo (copyScheduleOrigin n h.val) : ℝ))
    (Real.exp_pos _).le hlower hgap (by
      intro M _ u l d hw
      subst ranges
      have hb := (fullAtomTransferWeight_inserted_H_product_bounds role size n
        childBound pivotBound lo hi leaf (hist d) (fun h => (l h : ℕ))
        (fun y => (u y : ℕ)) M hw).1
      exact_mod_cast hb) henergy
  have h₂ := selected_anchor_harmonic_bound
    (fun i : Σ a, Fin (size a) => role i.1) n m bulk hrole
    (fun h => ∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)
    L z hL hz hm hmass hbulk
  calc
    _ ≤ _ := h₁
    _ = Real.exp (-gap) *
        (((selectedAnchorMatchingSet
          (fun i : Σ a, Fin (size a) => role i.1) n m bulk hrole).card : ℝ) *
          (∏ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
            (∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)⁻¹) *
          Real.exp E) := by ring
    _ ≤ Real.exp (-gap) *
        (((Fintype.card (SelectedNonbulkH (fun i : Σ a, Fin (size a) => role i.1) n m bulk hrole)).factorial *
          (∏ h : SelectedNonbulkH (fun i : Σ a, Fin (size a) => role i.1) n m bulk hrole,
            (∑ p ∈ Q (copyScheduleOrigin n h.val.val), (p : ℝ)⁻¹)⁻¹) *
          Real.exp ((Real.log 2 + Real.log z) * (2 ^ n * m : ℕ))) *
          Real.exp E) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right h₂ (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = _ := by rw [Real.exp_add]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedAnchorNaturalEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The code-preserving diagonal from actual selected-prime energy data -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem uniform_selected_anchor_natural_energy (n : ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (C₀ K d ε : ℝ) (hd : 0 ≤ d) (hε : 0 < ε)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K) :
    ∀ᶠ M : ℝ in atTop,
    let V := naturalTransferCutoff (d * M) M
    ∀ {I : Type*} [Fintype I] (role : I → CopyScheduleRole) (size : I → ℕ)
      (χ : (Σ a, Fin (size a)) → ∀ p : ℕ, DirichletCharacter ℂ p)
      (κ : (Σ a, Fin (size a)) → ℕ → ℂ) (pivot : ℕ → (Σ a, Fin (size a)))
      (_hκ : ∀ i p, ‖κ i p‖ ≤ 1)
      (childBound pivotBound : ℕ → ℕ)
      (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
      (i : Σ a, Fin (size a)) (_hi : role i.1 = .word)
      (_hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b)
      (p : I) (_hp : role p = .pivot n) (_hunique : ∀ j, role j = .pivot n → j = p)
      (m : ℕ) (bulk : Fin m ↪ (Σ a, Fin (size a)))
    (hrole : ∀ i, role (bulk i).1 = .word)
      (X lo upper : ℝ)
      (P : Finset ℕ) (cells : (Σ a, Fin (size a)) → Finset ℕ)
      (hP : ∀ p ∈ P, p.Prime ∧ V n < p)
      (_hX : 0 < X) (_hXlo : 1 < X * lo) (_hlo : Real.exp (d * M - C₀) ≤ lo)
      (_hsub : ∀ j, cells j ⊆ P) (_hmass : ∀ j, 0 < ∑ p ∈ cells j, (p : ℝ)⁻¹)
      (h J : ℕ)
      (_hsmall : V n ^ ((2 ^ (n + 1) - 1) * (n + 2)) ≤ 2 ^ h)
      (_hrange : ∀ p ∈ cells i, 2 ^ h ≤ p ∧ p < 2 ^ (h + J))
      (a C₁ L z : ℝ) (_ha : 0 < a) (_hL : 1 ≤ L)
      (_hcell : a ≤ ∑ p ∈ cells i, (p : ℝ)⁻¹) (_hJ : (J : ℝ) ≤ Real.exp (C₁ * L))
      (_hz : 0 < z) (_hm : (m : ℝ) ≤ z * L)
      (_hbulk : ∀ x, L ≤ ∑ p ∈ cells (copyScheduleOrigin n
        (selectedBulkCoordinates (fun i : Σ a, Fin (size a) => role i.1) n m bulk hrole x).val.val), (p : ℝ)⁻¹)
      (atomLo atomHi : I → ℕ) (_hranges : ranges = atomIntervalRanges role atomLo atomHi)
      (_hpositive : 0 < ∏ h : CopyScheduleH role n, (atomLo (copyScheduleOrigin n h.val) : ℝ))
      (A B : ℕ) (_hA : 0 < A) (gap : ℝ) (_hgap : Real.exp gap * (B : ℝ) ≤ ∏ h : CopyScheduleH role n, (atomLo (copyScheduleOrigin n h.val) : ℝ)),
      (∑ N ∈ Finset.Icc A B,
        (constituentMatchingFamily role size χ κ pivot n P (fun p hp => (hP p hp).1) cells
          childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo upper)
          (scheduledFrequencyHistory V n)
          (selectedAnchorMatchingSet (fun i : Σ a, Fin (size a) => role i.1) n m bulk hrole) N).re) ≤
      Real.exp (-gap) *
        (Fintype.card (SelectedNonbulkH (fun i : Σ a, Fin (size a) => role i.1) n m bulk hrole)).factorial *
        (∏ h : SelectedNonbulkH (fun i : Σ a, Fin (size a) => role i.1) n m bulk hrole,
          (∑ p ∈ cells (copyScheduleOrigin n h.val.val), (p : ℝ)⁻¹)⁻¹) *
        Real.exp ((Real.log 2 + Real.log z) * (2 ^ n * m : ℕ) +
          ((C₁ + max (Real.log (3 / a)) 0) * (2 ^ n : ℕ) * L + ε * M)) := by
  filter_upwards [uniform_constituent_natural_history_energy n ψ C₀ K d ε hd hε hψ] with M hE
  intro V I instI role size χ κ pivot hκ childBound pivotBound ranges i hi hu p hp hunique m bulk hrole
    X lo upper P cells hP hX hXlo hlo hsub hmass h J hsmall hrange a C₁ L z ha hL
    hcell hJ hz hm hbulk atomLo atomHi hranges hpositive A B hA gap hgap
  apply selected_anchor_diagonal_on_product role size χ κ pivot n m P (fun p hp => (hP p hp).1) cells
    childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo upper) (scheduledFrequencyHistory V n)
    hκ (scheduledFrequencyHistory_injective V n) (scheduledRootIndex V n)
    (scheduledRootIndex_eq_iff V n) bulk hrole atomLo atomHi hranges A B hA gap
    ((C₁ + max (Real.log (3 / a)) 0) * (2 ^ n : ℕ) * L + ε * M) L z
    hpositive hgap (lt_of_lt_of_le zero_lt_one hL) hz hm (fun _ => hmass _) hbulk
  intro N _
  exact hE role size childBound pivotBound ranges i hi hu p hp hunique X lo upper N P cells
    hP hX hXlo hlo hsub (fun j => (hmass j).ne') h J hsmall hrange a C₁ L ha hL hcell hJ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedNaturalAnchorDecay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual natural-cutoff anchor diagonal fits the character iteration -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem eventual_selected_natural_anchor_decay (n Bnb : ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (C₀ K d ε c B B₁ C₁ a z : ℝ)
    (hd : 0 ≤ d) (hε : 0 < ε) (hc : 0 ≤ c) (ha : 0 < a)
    (hC₁ : 0 ≤ C₁) (hz : 1 ≤ z)
    (hbudget : 4 * c * Bnb ≤ z)
    (hB : 2 * B₁ + (C₁ + max (Real.log (3 / a)) 0 + ε) + Real.log 2 + 6 ≤ B)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K) :
    ∃ M₀ : ℝ, ∀ᶠ L : ℝ in atTop, ∀ m : ℕ, M₀ ≤ (m : ℝ) →
    let M := (m : ℝ)
    let V := naturalTransferCutoff (d * M) M
    ∀ {I : Type*} [Fintype I] (role : I → CopyScheduleRole) (size : I → ℕ)
      (χ : (Σ a, Fin (size a)) → ∀ p : ℕ, DirichletCharacter ℂ p)
      (κ : (Σ a, Fin (size a)) → ℕ → ℂ) (pivot : ℕ → (Σ a, Fin (size a)))
      (_hκ : ∀ i p, ‖κ i p‖ ≤ 1)
      (childBound pivotBound : ℕ → ℕ)
      (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
      (i : Σ a, Fin (size a)) (_hi : role i.1 = .word)
      (_hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b)
      (p : I) (_hp : role p = .pivot n) (_hunique : ∀ j, role j = .pivot n → j = p)
      (bulk : Fin m ↪ (Σ a, Fin (size a)))
    (hrole : ∀ i, role (bulk i).1 = .word)
      (X lo upper : ℝ)
      (P : Finset ℕ) (cells : (Σ a, Fin (size a)) → Finset ℕ)
      (hP : ∀ p ∈ P, p.Prime ∧ V n < p)
      (_hX : 0 < X) (_hXlo : 1 < X * lo) (_hlo : Real.exp (d * M - C₀) ≤ lo)
      (_hsub : ∀ j, cells j ⊆ P) (_hmass : ∀ j, 0 < ∑ p ∈ cells j, (p : ℝ)⁻¹)
      (h J : ℕ)
      (_hsmall : V n ^ ((2 ^ (n + 1) - 1) * (n + 2)) ≤ 2 ^ h)
      (_hrange : ∀ p ∈ cells i, 2 ^ h ≤ p ∧ p < 2 ^ (h + J))
      (_hL : 1 ≤ L) (_hLM : L ≤ M)
      (_hcell : a ≤ ∑ p ∈ cells i, (p : ℝ)⁻¹) (_hJ : (J : ℝ) ≤ Real.exp (C₁ * L))
      (_hm : (m : ℝ) ≤ z * L) (_hmlo : z * L / 2 ≤ (m : ℝ))
      (_hbulk : ∀ x, L ≤ ∑ p ∈ cells (copyScheduleOrigin n
        (selectedBulkCoordinates (fun i : Σ a, Fin (size a) => role i.1) n m bulk hrole x).val.val), (p : ℝ)⁻¹)
      (atomLo atomHi : I → ℕ) (_hranges : ranges = atomIntervalRanges role atomLo atomHi)
      (_hpositive : 0 < ∏ h : CopyScheduleH role n, (atomLo (copyScheduleOrigin n h.val) : ℝ))
      (A top : ℕ) (_hA : 0 < A) (gap : ℝ) (_hgap : Real.exp gap * (top : ℝ) ≤ ∏ h : CopyScheduleH role n, (atomLo (copyScheduleOrigin n h.val) : ℝ))
      (_hgaprate : (B + 20 * Real.log z - 1) * (2 ^ n : ℕ) * M ≤ gap)
      (_hcard : Nat.card {i : Σ a, Fin (size a) //
        i ∉ Set.range bulk ∧ role i.1 ≠ .outside} ≤ Bnb)
      (_hmassnb : ∀ h : SelectedNonbulkH (fun i : Σ a, Fin (size a) => role i.1)
        n m bulk hrole, Real.exp (-c * L) ≤
          ∑ p ∈ cells (copyScheduleOrigin n h.val.val), (p : ℝ)⁻¹),
      (∑ N ∈ Finset.Icc A top,
        (constituentMatchingFamily role size χ κ pivot n P (fun p hp => (hP p hp).1) cells
          childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo upper)
          (scheduledFrequencyHistory V n)
          (selectedAnchorMatchingSet (fun i : Σ a, Fin (size a) => role i.1) n m bulk hrole) N).re) ≤
        Real.exp (-(2 * B₁ + 4) * (2 ^ n : ℕ) * M) := by
  obtain ⟨M₀, hM₀⟩ := (eventually_atTop.mp
    (uniform_selected_anchor_natural_energy n ψ C₀ K d ε hd hε hψ))
  refine ⟨M₀, ?_⟩
  filter_upwards [eventual_selected_nonbulk_cost n Bnb c 1 z hc (by norm_num)
    (lt_of_lt_of_le zero_lt_one hz) (by simpa only [one_mul] using hbudget)] with L hnb
  intro m hm₀ M V I instI role size χ κ pivot hκ childBound pivotBound ranges i hi hu p hp hunique
    bulk hrole X lo upper P cells hP hX hXlo hlo hsub hmass h J hsmall hrange hL hLM
    hcell hJ hm hmlo hbulk atomLo atomHi hranges hpositive A top hA gap hgap hgaprate hcard hmassnb
  have he := hM₀ M hm₀ role size χ κ pivot hκ childBound pivotBound ranges i hi hu p hp hunique
    m bulk hrole X lo upper P cells hP hX hXlo hlo hsub hmass h J hsmall hrange
    a C₁ L z ha hL hcell hJ (lt_of_lt_of_le zero_lt_one hz) hm hbulk
    atomLo atomHi hranges hpositive A top hA gap hgap
  have hn := hnb (fun i : Σ a, Fin (size a) => role i.1) m bulk hrole hmlo hcard
    (fun h => ∑ p ∈ cells (copyScheduleOrigin n h.val), (p : ℝ)⁻¹) hmassnb
  simp only [one_mul] at hn
  have hpow : (1 : ℝ) ≤ (2 ^ n : ℕ) := by exact_mod_cast Nat.one_le_two_pow
  have henergy :
      (C₁ + max (Real.log (3 / a)) 0) * (2 ^ n : ℕ) * L + ε * M ≤
        (C₁ + max (Real.log (3 / a)) 0 + ε) * (2 ^ n : ℕ) * M := by
    have hfirst := mul_le_mul_of_nonneg_left hLM
      (mul_nonneg (add_nonneg hC₁ (le_max_right (Real.log (3 / a)) 0)) (Nat.cast_nonneg (α := ℝ) (2 ^ n)))
    have hsecond := mul_le_mul_of_nonneg_left hpow (mul_nonneg hε.le (Nat.cast_nonneg m))
    change ε * M * 1 ≤ ε * M * (2 ^ n : ℕ) at hsecond
    nlinarith only [hfirst, hsecond]
  have hsmall := character_anchor_diagonal_small B B₁
    (C₁ + max (Real.log (3 / a)) 0 + ε) z M gap
    ((C₁ + max (Real.log (3 / a)) 0) * (2 ^ n : ℕ) * L + ε * M)
    (selectedNonbulkCost (fun i : Σ a, Fin (size a) => role i.1) n m bulk hrole
      (fun h => ∑ p ∈ cells (copyScheduleOrigin n h.val), (p : ℝ)⁻¹))
    n hz (Nat.cast_nonneg m) hB hgaprate henergy hn
  exact he.trans (by simpa only [selectedNonbulkCost, Nat.cast_mul, mul_assoc] using hsmall)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterAnchorDecay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The code-preserving diagonal for the constructed character cells

The energy length is the actual bulk density times L. This retains a bulk
mass of a L rather than assuming the stronger, generally false, bound L.
-/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem le_characterRangeError (k : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    c ≤ characterRangeError k c := by
  have hp : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hk := Nat.cast_nonneg (α := ℝ) k
  have hh : 1 ≤ (2 : ℝ) ^ k + k + 2 := by linarith
  exact (one_mul c).symm.trans_le (mul_le_mul_of_nonneg_right hh hc)

theorem eventual_character_anchor_decay_oai (k n Bnb : ℕ) (hn : n < k)
    (ψ : 𝓢(ℝ, ℂ)) (K B B₁ z c a b Cmass α β ε : ℝ)
    (hB : 1 ≤ B) (hz : 1 ≤ z) (hc : 1 ≤ c)
    (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hCmass : 0 < Cmass)
    (hα : 0 < α) (hβ : 0 ≤ β) (hε : 0 < ε)
    (hbudget : 4 * Cmass * Bnb ≤ z)
    (hgap : 2 * B₁ +
      ((β + Real.log ((Real.log 2)⁻¹ + 1)) / a + max (Real.log 3) 0 + ε) +
      Real.log 2 + 6 ≤ B + 20 * Real.log a)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K) :
    ∃ M₀ : ℝ, ∀ᶠ L : ℝ in atTop, ∀ m : ℕ, M₀ ≤ (m : ℝ) → L ≤ m →
      (m : ℝ) ≤ z * L → z * L ≤ 2 * m →
      ∀ (r : Fin k → ℕ) (f : ℕ) (hr : ∀ j, 0 < r j),
      1 + ((∑ j, r j) + 2 * k) ≤ Bnb →
      ∀ (P U : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
        (Q : Fin (m + 1) → Finset ℕ)
        (R : (v : CharacterCell k) → Fin (characterCellSize r f v) → Finset ℕ),
      (∀ i : Fin m, Q i.succ = U) →
      (∀ i, Q i ⊆ P) → (∀ v i, R v i ⊆ P) →
      b ≤ ∑ p ∈ Q 0, (p : ℝ)⁻¹ → a * L ≤ ∑ p ∈ U, (p : ℝ)⁻¹ →
      (∀ v i, Real.exp (-Cmass * L) ≤ ∑ p ∈ R v i, (p : ℝ)⁻¹) →
      (∀ p ∈ P, Real.exp (Real.exp (α * L)) ≤ p) →
      (∀ p ∈ U, (p : ℝ) ≤ Real.exp (Real.exp (β * L))) →
      ∀ (J : ℕ), 0 < J → ∀ (anchor : Fin k → Bool → ℝ) (F logX : ℝ), 0 < logX →
      let Δ := characterBaseGap B z m
      let T := characterPivotTarget k J (fun j => anchor j false + anchor j true)
        (fun j => characterPivotGap B z m j.val)
      ∀ lower upper : CharacterCell k → ℕ,
      (∀ v, Real.exp (characterLogCenter J T anchor F (true, some v) - c) ≤ lower v) →
      (∀ v, (upper v : ℝ) ≤ Real.exp (characterLogCenter J T anchor F (true, some v) + c)) →
      ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p),
      let lo := initialWordAtomLower J lower
      let hi := initialWordAtomUpper J upper
      let χ₀ := signedAtomCharacter (initialWordSize (m + 1) (characterCellSize r f)) χ
      let Q₀ := characterFullPrimeCells m r f Q R
      let V := naturalTransferCutoff Δ m
      let cap := characterPivotCap T (characterRangeError k c)
      let p := characterPivotAtom ⟨n, hn⟩
      (∑ N ∈ Finset.Icc (lo p) (hi p),
        (constituentMatchingFamily (characterRole k) (characterSize m r f) χ₀
          (fun i => primeGaussMultiplier (χ₀ i)) (characterPivot m r f hr) n P hP Q₀
          V cap (atomIntervalRanges (characterRole k) lo hi)
          (scheduleFourierLeaf (characterRole k) ψ (Real.exp logX)
            (Real.exp (Δ - (Fintype.card (CharacterRole k) : ℝ) * c))
            (Real.exp (Δ + (Fintype.card (CharacterRole k) : ℝ) * c)))
          (scheduledFrequencyHistory V n)
          (selectedAnchorMatchingSet
            (fun i : Σ v, Fin (characterSize m r f v) => characterRole k i.1)
            n m (characterBulk m r f) (characterBulk_role m r f)) N).re) ≤
        Real.exp (-(2 * B₁ + 4) * (2 ^ n : ℕ) * (m : ℝ)) := by
  let d := B + 20 * Real.log z
  let C₀ := (Fintype.card (CharacterRole k) : ℝ) * c
  let C₁ := β + Real.log ((Real.log 2)⁻¹ + 1)
  have hz0 : 0 < z := by linarith
  have hd1 : 1 ≤ d := by dsimp [d]; linarith [Real.log_nonneg hz]
  have hd : 0 ≤ d := by linarith
  have hC₁ : 0 ≤ C₁ := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hi : 0 ≤ (Real.log 2)⁻¹ := inv_nonneg.mpr hlog2.le
    exact add_nonneg hβ (Real.log_nonneg (by linarith))
  have hza : 1 ≤ z / a := (le_div_iff₀ ha).mpr (by linarith)
  have hbudget' : 4 * (Cmass / a) * Bnb ≤ z / a := by
    calc
      _ = (4 * Cmass * Bnb) / a := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hbudget ha.le
  obtain ⟨M₁, hdec⟩ := eventual_selected_natural_anchor_decay n Bnb ψ C₀ K d ε
    (Cmass / a) (B + 20 * Real.log a) B₁ (C₁ / a) 1 (z / a)
    hd hε (div_nonneg hCmass.le ha.le) (by norm_num) (div_nonneg hC₁ ha.le)
    hza hbudget' (by simpa only [div_one] using hgap) hψ
  refine ⟨max M₁ (max 1 (max C₀ (2 * characterRangeError k c))), ?_⟩
  have hscaled := (tendsto_id.const_mul_atTop ha).eventually hdec
  simp only [id_eq] at hscaled
  filter_upwards [hscaled, eventual_full_character_mass_floor a b Cmass ha hb hCmass,
    eventual_character_energy_prime_range k ((2 ^ (n + 1) - 1) * (n + 2))
      d z α β hd hz0.le hα hβ,
    eventual_natural_cutoff_below_primes k d z α 1 hd hz0.le hα (by norm_num),
    eventually_ge_atTop (1 / a)] with L hdec hmass hdyadic hsep hLa
  intro m hM hLM hmL hLm r f hr hcount P U hP Q R hQ hQP hRP htop hbulk hR
    hmin hmax J hJ anchor F logX hlogX Δ T lower upper hlower hupper χ
    lo hi χ₀ Q₀ V cap p
  have hm1 : (1 : ℝ) ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hM)
  have hM₁ : M₁ ≤ (m : ℝ) := (le_max_left _ _).trans hM
  have hC₀m : C₀ ≤ (m : ℝ) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hM))
  have hCm : 2 * characterRangeError k c ≤ (m : ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hM))
  have haL : 1 ≤ a * L := by simpa only [mul_comm] using (div_le_iff₀ ha).mp hLa
  have hL0 : 0 ≤ L := (div_pos zero_lt_one ha).le.trans hLa
  have haLm : a * L ≤ (m : ℝ) :=
    (mul_le_of_le_one_left hL0 ha1).trans hLM
  have heza : z / a * (a * L) = z * L := by field_simp
  have hmL' : (m : ℝ) ≤ z / a * (a * L) := by rwa [heza]
  have hLm' : z / a * (a * L) / 2 ≤ (m : ℝ) := by
    have he : z / a * (a * L) = z * L := by field_simp
    rw [he]
    linarith
  have hall := hmass k m r f Q R htop (fun i => by simpa only [hQ] using hbulk) hR
  have hpos (i) : 0 < ∑ q ∈ Q₀ i, (q : ℝ)⁻¹ := (Real.exp_pos _).trans_le (hall i)
  have hsub := characterFullPrimeCells_subset m r f P Q R hQP hRP
  have hU : U ⊆ P := by
    have hms : 0 < m := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hm1)
    simpa only [hQ] using hQP (⟨0, hms⟩ : Fin m).succ
  obtain ⟨hh, JJ, hmod, hrange, hJJ⟩ := hdyadic (m : ℝ) hm1 hmL U
    (fun q hq => ⟨hmin q (hU hq), hmax q hq⟩)
  have hlarge (q : ℕ) (hq : q ∈ P) : V n < q := by
    exact hsep _ hm1 hmL q (by simpa only [one_mul] using hmin q hq) n hn.le
  have hw := character_word_interval_errors J c hc T anchor F lower upper hlower hupper
  have hpositive : 0 < ∏ h : CopyScheduleH (characterRole k) n,
      (lo (copyScheduleOrigin n h.val) : ℝ) :=
    Finset.prod_pos (fun h _ => (Real.exp_pos _).trans_le (hw.1 _))
  have hA : 0 < lo p := by exact_mod_cast (Real.exp_pos _).trans_le (hw.1 p)
  have hproduct := character_diagonal_product_gap hn J B z m F c (by linarith) anchor
    lo hi hw.1 hw.2
  have hcap : hi p ≤ cap n := by
    dsimp only [cap]
    rw [characterPivotCap_eq hn]
    apply Nat.le_floor
    exact (hw.2 p).trans (Real.exp_le_exp.mpr (by
      change T ⟨n, hn⟩ + c ≤ T ⟨n, hn⟩ + characterRangeError k c
      linarith only [le_characterRangeError k c (by linarith)]))
  have hproduct' : Real.exp (characterPivotGap B z m n - 2 * characterRangeError k c) *
      (hi p : ℝ) ≤ ∏ h : CopyScheduleH (characterRole k) n,
        (lo (copyScheduleOrigin n h.val) : ℝ) := by
    apply (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcap) (Real.exp_nonneg _)).trans
    simpa only [cap, characterPivotCap_eq hn] using hproduct
  have hgaprate := character_diagonal_gap_reserve n B z m (characterRangeError k c)
    (Nat.cast_nonneg _) hCm
  have hlogs : B + 20 * Real.log a + 20 * Real.log (z / a) - 1 = d - 1 := by
    rw [Real.log_div hz0.ne' ha.ne']
    dsimp [d]
    ring
  have hlogap : 1 ≤ Real.exp (Δ - C₀) := Real.one_le_exp_iff.mpr (by
    have hdM := mul_le_mul_of_nonneg_right hd1 (Nat.cast_nonneg (α := ℝ) m)
    change 0 ≤ d * m - C₀
    linarith)
  have hXlo : 1 < Real.exp logX * Real.exp (Δ - C₀) := by
    have hX := Real.one_lt_exp_iff.mpr hlogX
    nlinarith only [hX, hlogap]
  have huniq : ∀ j < n, ∀ u v, characterRole k u = .pivot j →
      characterRole k v = .pivot j → u = v := by
    intro j hj u v hu hv
    exact (characterPivotAtom_unique ⟨j, hj.trans hn⟩ u hu).trans
      (characterPivotAtom_unique ⟨j, hj.trans hn⟩ v hv).symm
  have hms : 0 < m := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hm1)
  let i : Fin m := ⟨0, hms⟩
  have hcard : Nat.card {i : Σ v, Fin (characterSize m r f v) //
      i ∉ Set.range (characterBulk m r f) ∧ characterRole k i.1 ≠ .outside} ≤ Bnb := by
    rw [Nat.card_eq_fintype_card]
    exact (character_original_nonbulk_card m r f).trans hcount
  have hCscale : C₁ / a * (a * L) = C₁ * L := by field_simp
  apply hdec m hM₁ (characterRole k) (characterSize m r f) χ₀
    (fun i => primeGaussMultiplier (χ₀ i)) (characterPivot m r f hr)
    (fun i p => (primeGaussMultiplier_norm _ _).le) V cap
    (atomIntervalRanges (characterRole k) lo hi) (characterBulk m r f i) rfl huniq
    p rfl (fun j hj => characterPivotAtom_unique ⟨n, hn⟩ j hj)
    (characterBulk m r f) (characterBulk_role m r f)
    (Real.exp logX) (Real.exp (Δ - C₀)) (Real.exp (Δ + C₀)) P Q₀
    (fun p hp => ⟨hP p hp, hlarge p hp⟩) (Real.exp_pos _) hXlo le_rfl hsub hpos
    hh JJ (hmod n hn.le) (by simpa only [Q₀, characterFullPrimeCells_bulk, hQ] using hrange)
    haL haLm (by simpa only [Q₀, characterFullPrimeCells_bulk, hQ] using haL.trans hbulk)
    (by rw [hCscale]; exact hJJ) hmL' hLm'
    (fun x => by
      have ho := copyScheduleOrigin_path n (scheduledPathEnumeration n x.1) (characterBulk m r f x.2)
      change a * L ≤ ∑ q ∈ Q₀ (copyScheduleOrigin n
        (selectedBulkCoordinates _ n m _ _ x).val.val), (q : ℝ)⁻¹
      rw [show copyScheduleOrigin n (selectedBulkCoordinates _ n m _ _ x).val.val =
        characterBulk m r f x.2 from ho]
      simpa only [Q₀, characterFullPrimeCells_bulk, hQ] using hbulk)
    lo hi rfl hpositive (lo p) (hi p) hA
    (characterPivotGap B z m n - 2 * characterRangeError k c)
    hproduct'
    (by simpa only [hlogs] using hgaprate)
    hcard
    (fun h => by
      have he : -(Cmass / a) * (a * L) = -Cmass * L := by field_simp
      rw [he]
      exact hall _)

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.eventual_character_anchor_decay_oai := @OAI.Ostmann.eventual_character_anchor_decay_oai
