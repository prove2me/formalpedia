-- Prove2me | solution 1 for OAI.Ostmann.PublishedProgressionInput.movingPattern_diagonal_ideal_integral_rate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:19:41.540094+00:00
-- url     : https://prove2.me/submissions/598a523d-9405-4e72-80b7-173db2a805f2

import Mathlib
import Definitions.Def_OAIQ095D008
import Theorems.Thm_OAI_Ostmann_PublishedProgressionInput_movingPattern_original_mixed_prime_norm_arithmetic_rate

section
-- module Solutions.OAIQ095_OS.Compat
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib d13f23b's `Finset.sum_le_sum_of_injOn`; ours has no such lemma (LipschitzHilbert, oaiq-090). -/
theorem sum_le_sum_of_injOn {ι κ M : Type*} [DecidableEq κ] [AddCommMonoid M] [PartialOrder M]
    [IsOrderedAddMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M} (e : ι → κ)
    (he : Set.InjOn e s) (hest : s.image e ⊆ t) (hf : ∀ i ∈ s, f i ≤ g (e i))
    (hg : ∀ j ∈ t, j ∉ s.image e → 0 ≤ g j) : ∑ i ∈ s, f i ≤ ∑ j ∈ t, g j := by
  calc ∑ i ∈ s, f i ≤ ∑ i ∈ s, g (e i) := Finset.sum_le_sum hf
    _ = ∑ j ∈ s.image e, g j := (Finset.sum_image he).symm
    _ ≤ ∑ j ∈ t, g j := Finset.sum_le_sum_of_subset_of_nonneg hest hg
end OAICompat434

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

theorem reducedFrequency_mem {N g s : ℕ} (hs : s ∈ Finset.Icc 1 N) :
    reducedFrequency g s ∈ Finset.Icc 1 N := by
  obtain ⟨hs₀, hsN⟩ := Finset.mem_Icc.mp hs
  have hg := Nat.gcd_pos_of_pos_left g (show 0 < s from hs₀)
  exact Finset.mem_Icc.mpr ⟨Nat.div_pos
    (Nat.le_of_dvd hs₀ (Nat.gcd_dvd_left s g)) hg, (Nat.div_le_self _ _).trans hsN⟩

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

theorem sum_treeLeafFiber_succ {U R : Type*} [CommGroup U] [Fintype U]
    [AddCommMonoid R] (n : ℕ) (P : U) (f : TreeLeafTuple U (n + 1) → R) :
    (∑ x : TreeLeafFiber U (n + 1) P, f x.1) =
      ∑ m : U, ∑ a : TreeLeafFiber U n m, ∑ b : TreeLeafFiber U n (P / m),
        f (a.1, b.1) := by
  have h := (treeLeafFiberSuccEquiv n P).symm.sum_comp (fun x => f x.1)
  change (∑ x : (Σ m : U, TreeLeafFiber U n m × TreeLeafFiber U n (P / m)),
    f (x.2.1.1, x.2.2.1)) = _ at h
  simpa only [Fintype.sum_sigma, Fintype.sum_prod_type] using h.symm

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
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SquarePullback
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The factor two in square pullbacks

The finite-fiber bound and Cauchy--Schwarz estimate used in the manuscript's
equation `tree-square-pullback`. Multiplicative characters are extended by zero
at zero, as in the manuscript. Evaluations in these lemmas are at units.
-/

namespace Ostmann

open scoped BigOperators

attribute [local instance] OAI.Ostmann.instDecidableEqMulCharZModComplex_solutions
private theorem square_fiber_card_le_two {ι K : Type*} [Field K] [DecidableEq K]
    (s : Finset ι) (f : ι → K) (hf : Function.Injective f) (y : K) :
    (s.filter fun x => f x ^ 2 = y).card ≤ 2 := by
  classical
  let t := s.filter fun x => f x ^ 2 = y
  by_cases ht : t.Nonempty
  · obtain ⟨a, ha⟩ := ht
    have haeq : f a ^ 2 = y := (Finset.mem_filter.mp ha).2
    have hsub : t.image f ⊆ {f a, -f a} := by
      intro z hz
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
      have hbeq : f b ^ 2 = y := (Finset.mem_filter.mp hb).2
      simpa only [Finset.mem_insert, Finset.mem_singleton] using
        (sq_eq_sq_iff_eq_or_eq_neg.mp (hbeq.trans haeq.symm))
    calc
      t.card = (t.image f).card := (Finset.card_image_of_injective t hf).symm
      _ ≤ ({f a, -f a} : Finset K).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two
  · have : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    change t.card ≤ 2
    simp only [this, Finset.card_empty, Nat.zero_le]

/-- Squaring has at most two preimages among the units of a prime field. -/
theorem unit_square_fiber_card_le_two {p : ℕ} [Fact p.Prime]
    (s : Finset (ZMod p)ˣ) (u : (ZMod p)ˣ) :
    (s.filter fun x => x ^ 2 = u).card ≤ 2 := by
  classical
  have heq : (s.filter fun x => x ^ 2 = u) =
      s.filter (fun x : (ZMod p)ˣ => (x : ZMod p) ^ 2 = (u : ZMod p)) := by
    ext x
    simp only [Finset.mem_filter, ← Units.val_pow_eq_pow_val, Units.val_inj]
  rw [heq]
  exact square_fiber_card_le_two s (fun x : (ZMod p)ˣ => (x : ZMod p))
    Units.val_injective (u : ZMod p)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_BottomPairCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coordinates for a bottom pair of the finite-field tree

The change of variables in §6 sends `(d,t)` to `(dt/(t-1),d/(t-1))`.
On its valid domain this is a bijection with the ordered distinct nonzero
pairs. It is the change of variables used in the bottom-pair second moment.
-/

namespace Ostmann

variable {K : Type*} [Field K]

theorem pair_coordinate_difference (d t : K) (ht : t ≠ 1) :
    d * t / (t - 1) - d / (t - 1) = d := by
  have hden : t - 1 ≠ 0 := sub_ne_zero.mpr ht
  field_simp

theorem pair_coordinates_reconstruct (x z : K) (hz : z ≠ 0) (hxz : x ≠ z) :
    ((x - z) * (x / z) / (x / z - 1), (x - z) / (x / z - 1)) = (x, z) := by
  have hden : x / z - 1 ≠ 0 := by
    intro h
    have : x / z = 1 := sub_eq_zero.mp h
    exact hxz ((div_eq_one_iff_eq hz).mp this)
  have hsub : x - z ≠ 0 := sub_ne_zero.mpr hxz
  apply Prod.ext <;> dsimp
  · field_simp [hsub]
  · field_simp [hsub]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TreeCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rational coordinates at a tree split

These identities are equations `tree-difference-ratio`, `tree-held-square`,
and `tree-p-square` of the manuscript. Nonzero hypotheses state precisely
that the reconstructed node is valid.
-/

namespace Ostmann

theorem reconstructedEntry_relation {K : Type*} [Field K]
    (s sL sR u HL HR : K) (hs : s ≠ 0) (hu : u ≠ 0) :
    reconstructedEntry s sL sR u HL HR * (s * u) = sL * HR - sR * HL := by
  exact div_mul_cancel₀ _ (mul_ne_zero hs hu)

theorem tree_child_difference {K : Type*} [Field K]
    (s sL sR D u HL HR P : K)
    (hD : D ≠ 0) (hu : u ≠ 0) (hL : HL ≠ 0) (hR : HR ≠ 0) (hP : P ≠ 0)
    (hrel : P * (s * u) = sL * HR - sR * HL) :
    childArgument sL D u HL P - childArgument sR D u HR P = parentArgument s D HL HR := by
  unfold childArgument parentArgument
  field_simp
  linear_combination -hrel

theorem tree_child_ratio {K : Type*} [Field K]
    (sL sR D u HL HR P : K)
    (hsR : sR ≠ 0) (hD : D ≠ 0) (hu : u ≠ 0)
    (hL : HL ≠ 0) (hR : HR ≠ 0) (hP : P ≠ 0) :
    childArgument sL D u HL P / childArgument sR D u HR P = (sL / sR) * (HR / HL) := by
  unfold childArgument
  field_simp

/-- Exposing a child product makes its ratio an inverse square of the free product. -/
theorem tree_product_ratio {G : Type*} [CommGroup G]
    (sL sR XL XR CL CR P m : G) :
    (sL / sR) * ((XR * CR * (P / m)) / (XL * CL * m)) =
      ((sL / sR) * (XR * CR * P / (XL * CL))) * (m⁻¹) ^ 2 := by
  simp [div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm]

/-- Difference and ratio identify the child arguments with the sampling coordinates. -/
theorem children_eq_pair_coordinates {K : Type*} [Field K]
    (x z d t : K) (hz : z ≠ 0) (hd : d ≠ 0)
    (hdiff : x - z = d) (hratio : x / z = t) :
    (x, z) = (d * t / (t - 1), d / (t - 1)) := by
  have hxz : x ≠ z := by intro h; apply hd; rw [← hdiff, h, sub_self]
  rw [← hdiff, ← hratio]
  exact (pair_coordinates_reconstruct x z hz hxz).symm

/-- The rational tree formulas produce exactly the pair used by the density model. -/
theorem tree_children_eq_pair_coordinates {K : Type*} [Field K]
    (s sL sR D u HL HR P : K)
    (hs : s ≠ 0) (hsR : sR ≠ 0) (hD : D ≠ 0) (hu : u ≠ 0)
    (hL : HL ≠ 0) (hR : HR ≠ 0) (hP : P ≠ 0)
    (hrel : P * (s * u) = sL * HR - sR * HL) :
    (childArgument sL D u HL P, childArgument sR D u HR P) =
      (parentArgument s D HL HR * ((sL / sR) * (HR / HL)) /
        ((sL / sR) * (HR / HL) - 1),
       parentArgument s D HL HR / ((sL / sR) * (HR / HL) - 1)) := by
  apply children_eq_pair_coordinates
  · exact div_ne_zero hsR (by simp only [ne_eq, mul_eq_zero, hD, hP, hu, hR, or_self, not_false_eq_true])
  · exact div_ne_zero hs (mul_ne_zero (mul_ne_zero hD hL) hR)
  · exact tree_child_difference s sL sR D u HL HR P hD hu hL hR hP hrel
  · exact tree_child_ratio sL sR D u HL HR P hsR hD hu hL hR hP

/-- A reconstructed node is invalid precisely at the singular child ratio. -/
theorem reconstructedEntry_zero_iff_ratio_one {K : Type*} [Field K]
    (s sL sR u HL HR : K) (hs : s ≠ 0) (hsR : sR ≠ 0)
    (hu : u ≠ 0) (hL : HL ≠ 0) :
    reconstructedEntry s sL sR u HL HR = 0 ↔ (sL / sR) * (HR / HL) = 1 := by
  have hden : sR * HL ≠ 0 := mul_ne_zero hsR hL
  have heq : (sL / sR) * (HR / HL) = (sL * HR) / (sR * HL) := by ring
  rw [heq, div_eq_one_iff_eq hden]
  unfold reconstructedEntry
  rw [div_eq_zero_iff, or_iff_left (mul_ne_zero hs hu), sub_eq_zero]

/-- At a fixed node product the root argument is independent of the free split. -/
theorem tree_parent_fixed_product {K : Type*} [Field K]
    (s D XL XR CL CR P m : K) (hm : m ≠ 0) :
    parentArgument s D (XL * CL * m) (XR * CR * (P / m)) =
      s / (D * XL * CL * XR * CR * P) := by
  unfold parentArgument
  congr 1
  field_simp

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

/-- Additive Parseval with the manuscript's probability convention. -/
theorem additiveFourier_parseval {p : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    (∑ a : ZMod p, ‖additiveFourier f a‖ ^ 2) =
      (p : ℝ)⁻¹ * ∑ x : ZMod p, ‖f x‖ ^ 2 := by
  rw [additiveFourier_energy f]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  rw [← mul_assoc, inv_mul_cancel₀ hp, one_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AffineAction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Identifying the Fourier matrix of the affine action

The finite matrix from `AffineFourier` is the action of
`F(t) ↦ ∑ c(a,b) F(at+b)` on nonzero additive frequencies.
-/

namespace Ostmann

open scoped BigOperators

theorem sum_units_eq_sum_of_zero {p : ℕ} [Fact p.Prime]
    {R : Type*} [AddCommMonoid R] (F : ZMod p → R) (hF : F 0 = 0) :
    (∑ u : (ZMod p)ˣ, F u) = ∑ x : ZMod p, F x := by
  classical
  calc
    _ = ∑ x ∈ (Finset.univ : Finset (ZMod p)).erase 0, F x := by
      apply Finset.sum_bij (fun (u : (ZMod p)ˣ) _ => (u : ZMod p))
      · intro u _
        exact Finset.mem_erase.mpr ⟨Units.ne_zero u, Finset.mem_univ _⟩
      · intro u _ v _ huv
        exact Units.val_injective huv
      · intro x hx
        refine ⟨Units.mk0 x (Finset.mem_erase.mp hx).1, Finset.mem_univ _, rfl⟩
      · intro _ _
        rfl
    _ = ∑ x : ZMod p, F x := by
      simpa only [hF, add_zero] using
        Finset.sum_erase_add (Finset.univ : Finset (ZMod p)) F (Finset.mem_univ 0)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_BottomPairMellin
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The bottom-pair Mellin coefficient is an autocorrelation

This is equation `tree-P-definition`. The difference parameter is a unit;
the exceptional ratio `t = 1` is assigned value zero. The function being
correlated is twisted by the conjugate multiplicative character.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem ratioInvolution_involutive {p : ℕ} [Fact p.Prime] :
    Function.Involutive (ratioInvolution (p := p)) := by
  intro t
  by_cases ht : t = 1
  · simp [ratioInvolution, ht]
  · have hden : t - 1 ≠ 0 := sub_ne_zero.mpr ht
    have hquot : t / (t - 1) ≠ 1 := by
      intro h
      have heq := (div_eq_one_iff_eq hden).mp h
      have : (1 : ZMod p) = 0 := by linear_combination heq
      exact one_ne_zero this
    simp only [ratioInvolution, ht, ite_false, if_false, hquot]
    field_simp
    ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SquareAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Domination of a uniform square-coset average

The square map on the unit group has fibers of size at most two. Its
pushforward therefore has density at most two against the uniform law.
-/

namespace Ostmann

open scoped BigOperators

theorem sum_square_coset_le_twice {p : ℕ} [Fact p.Prime]
    (K : (ZMod p)ˣ) (f : (ZMod p)ˣ → ℝ) (hf : ∀ u, 0 ≤ f u) :
    (∑ z : (ZMod p)ˣ, f (K * z ^ 2)) ≤ 2 * ∑ u : (ZMod p)ˣ, f u := by
  classical
  have hmaps : ∀ z ∈ (Finset.univ : Finset (ZMod p)ˣ),
      K * z ^ 2 ∈ (Finset.univ : Finset (ZMod p)ˣ) := fun _ _ => Finset.mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun z => f (K * z ^ 2)), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u _
  have heq : (Finset.univ.filter (fun z : (ZMod p)ˣ => K * z ^ 2 = u)) =
      Finset.univ.filter (fun z : (ZMod p)ˣ => z ^ 2 = K⁻¹ * u) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      rw [← h, ← mul_assoc, inv_mul_cancel, one_mul]
    · intro h
      rw [h, ← mul_assoc, mul_inv_cancel, one_mul]
  have hsum : (∑ z ∈ Finset.univ.filter (fun z : (ZMod p)ˣ => K * z ^ 2 = u),
      f (K * z ^ 2)) =
      ((Finset.univ.filter (fun z : (ZMod p)ˣ => z ^ 2 = K⁻¹ * u)).card : ℝ) * f u := by
    calc
      _ = ∑ _z ∈ Finset.univ.filter (fun z : (ZMod p)ˣ => K * z ^ 2 = u), f u := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [(Finset.mem_filter.mp hz).2]
      _ = _ := by simp only [heq, Finset.sum_const, nsmul_eq_mul]
  rw [hsum]
  apply mul_le_mul_of_nonneg_right _ (hf u)
  exact_mod_cast unit_square_fiber_card_le_two Finset.univ (K⁻¹ * u)

/-- Inverting the sampling coordinate preserves the same square-coset bound. -/
theorem sum_inverse_square_coset_le_twice {p : ℕ} [Fact p.Prime]
    (K : (ZMod p)ˣ) (f : (ZMod p)ˣ → ℝ) (hf : ∀ u, 0 ≤ f u) :
    (∑ z : (ZMod p)ˣ, f (K * (z⁻¹) ^ 2)) ≤ 2 * ∑ u : (ZMod p)ˣ, f u := by
  have h := (Equiv.inv (ZMod p)ˣ).bijective.sum_comp
    (fun z => f (K * z ^ 2))
  change (∑ z : (ZMod p)ˣ, f (K * (z⁻¹) ^ 2)) = _ at h
  rw [h]
  exact sum_square_coset_le_twice K f hf

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PairDensity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Density of one tree split

Given the parent difference, a split coordinate produces the child ratio
as a fixed unit times its inverse square. Each valid child pair therefore
has multiplicity at most two. Zero weights at zero discard invalid nodes.
-/

namespace Ostmann

open scoped BigOperators

/-- A full-field sum in ratio coordinates is exactly the difference convolution. -/
theorem pair_ratio_sum_eq {p : ℕ} [Fact p.Prime]
    (d : (ZMod p)ˣ) (f g : ZMod p → ℝ) (hf : f 0 = 0) (hg : g 0 = 0) :
    (∑ t : (ZMod p)ˣ, if t = 1 then 0 else
      f ((d : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1)) *
        g ((d : ZMod p) / ((t : ZMod p) - 1))) =
      ∑ x : ZMod p, f x * g (x - d) := by
  classical
  let H : ZMod p → ℝ := fun t => if t = 1 then 0 else
    f ((d : ZMod p) * t / (t - 1)) * g ((d : ZMod p) / (t - 1))
  have hH0 : H 0 = 0 := by simp [H, hf]
  have hunit (t : (ZMod p)ˣ) : (if t = 1 then 0 else
      f ((d : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1)) *
        g ((d : ZMod p) / ((t : ZMod p) - 1))) = H t := by
    have ht : (t : ZMod p) = 1 ↔ t = 1 := by
      constructor
      · intro h; exact Units.ext h
      · intro h; simp [h]
    simp only [H, ht]
  let e : ZMod p ≃ ZMod p :=
    (Function.Involutive.toPerm _ ratioInvolution_involutive).trans
      (Equiv.mulLeft₀ (d : ZMod p) (Units.ne_zero d))
  have he (t : ZMod p) : H t = f (e t) * g (e t - d) := by
    change H t = f ((d : ZMod p) * ratioInvolution t) *
      g ((d : ZMod p) * ratioInvolution t - d)
    by_cases ht : t = 1
    · simp [H, ratioInvolution, ht, hg]
    · have hdif : (d : ZMod p) * t / (t - 1) - d =
          (d : ZMod p) / (t - 1) := by
        have h := pair_coordinate_difference (d : ZMod p) t ht
        linear_combination h
      simp only [H, ht, ite_false, if_false, ratioInvolution, ← mul_div_assoc, hdif]
  simp_rw [hunit]
  rw [sum_units_eq_sum_of_zero H hH0]
  simp_rw [he]
  exact e.bijective.sum_comp (fun x => f x * g (x - d))

/-- Counting form of the conditional density bound at one internal node. -/
theorem pair_inverse_square_density {p : ℕ} [Fact p.Prime]
    (d K : (ZMod p)ˣ) (f g : ZMod p → ℝ)
    (hf : f 0 = 0) (hg : g 0 = 0)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x) :
    (∑ m : (ZMod p)ˣ,
      let t := K * (m⁻¹) ^ 2
      if t = 1 then 0 else
        f ((d : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1)) *
          g ((d : ZMod p) / ((t : ZMod p) - 1))) ≤
      2 * ∑ x : ZMod p, f x * g (x - d) := by
  let H : (ZMod p)ˣ → ℝ := fun t => if t = 1 then 0 else
    f ((d : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1)) *
      g ((d : ZMod p) / ((t : ZMod p) - 1))
  have hn (t : (ZMod p)ˣ) : 0 ≤ H t := by
    dsimp [H]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (hfn _) (hgn _)
  have h := sum_inverse_square_coset_le_twice K H hn
  rw [show (∑ t : (ZMod p)ˣ, H t) = ∑ x : ZMod p, f x * g (x - d) from
    pair_ratio_sum_eq d f g hf hg] at h
  exact h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RationalNodeDensity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The density bound for an actual reconstructed node

The fixed parent product makes its argument independent of the split.
The reconstructed entry vanishes exactly when the child ratio is one.
Thus the inverse-square density estimate applies to the actual formulas,
with the manuscript's invalid-node convention.
-/

namespace Ostmann

open scoped BigOperators

theorem rationalNodeValue_eq_ratio {p : ℕ} [Fact p.Prime]
    (s sL sR D u XL XR CL CR P : (ZMod p)ˣ)
    (f g : ZMod p → ℝ) (m : (ZMod p)ˣ) :
    rationalNodeValue s sL sR D u XL XR CL CR P f g m =
      let d := rationalNodeArgument s D XL XR CL CR P
      let t := rationalNodeRatioConstant sL sR XL XR CL CR P * (m⁻¹) ^ 2
      if t = 1 then 0 else
        f ((d : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1)) *
          g ((d : ZMod p) / ((t : ZMod p) - 1)) := by
  classical
  let HL : (ZMod p)ˣ := XL * CL * m
  let HR : (ZMod p)ˣ := XR * CR * (P / m)
  let v := reconstructedEntry (s : ZMod p) sL sR u HL HR
  let d := rationalNodeArgument s D XL XR CL CR P
  let t := rationalNodeRatioConstant sL sR XL XR CL CR P * (m⁻¹) ^ 2
  have ht : (sL : ZMod p) / sR * ((HR : ZMod p) / HL) = (t : ZMod p) := by
    have h : (sL / sR) * (HR / HL) = t :=
      tree_product_ratio sL sR XL XR CL CR P m
    exact_mod_cast h
  have hd : parentArgument (s : ZMod p) D HL HR = (d : ZMod p) := by
    dsimp [HL, HR, d, rationalNodeArgument]
    simp only [Units.val_mul, Units.val_div_eq_div_val]
    exact tree_parent_fixed_product (s : ZMod p) D XL XR CL CR P m (Units.ne_zero m)
  have hv : v = 0 ↔ t = 1 := by
    have h := reconstructedEntry_zero_iff_ratio_one (s : ZMod p) sL sR u HL HR
      (Units.ne_zero s) (Units.ne_zero sR) (Units.ne_zero u) (Units.ne_zero HL)
    rw [ht] at h
    constructor
    · intro hz
      exact Units.ext (h.mp hz)
    · intro h1
      apply h.mpr
      simp only [h1, Units.val_one]
  change (if v = 0 then 0 else
    f (childArgument sL D u HL v) * g (childArgument sR D u HR v)) =
      if t = 1 then 0 else
        f ((d : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1)) *
          g ((d : ZMod p) / ((t : ZMod p) - 1))
  by_cases hv0 : v = 0
  · simp only [hv0, hv.mp hv0, ite_true, if_true]
  · have ht1 : t ≠ 1 := fun h => hv0 (hv.mpr h)
    simp only [hv0, ht1, ite_false, if_false]
    have hpair := tree_children_eq_pair_coordinates (s : ZMod p) sL sR D u HL HR v
      (Units.ne_zero s) (Units.ne_zero sR) (Units.ne_zero D) (Units.ne_zero u)
      (Units.ne_zero HL) (Units.ne_zero HR) hv0
      (reconstructedEntry_relation (s : ZMod p) sL sR u HL HR (Units.ne_zero s) (Units.ne_zero u))
    rw [ht, hd] at hpair
    exact congrArg (fun xz : ZMod p × ZMod p => f xz.1 * g xz.2) hpair

/-- Conditional counting density of one actual rational tree split. -/
theorem rationalNodeValue_sum_le {p : ℕ} [Fact p.Prime]
    (s sL sR D u XL XR CL CR P : (ZMod p)ˣ)
    (f g : ZMod p → ℝ) (hf : f 0 = 0) (hg : g 0 = 0)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x) :
    (∑ m : (ZMod p)ˣ, rationalNodeValue s sL sR D u XL XR CL CR P f g m) ≤
      2 * ∑ x : ZMod p, f x * g (x - rationalNodeArgument s D XL XR CL CR P) := by
  simp_rw [rationalNodeValue_eq_ratio]
  exact pair_inverse_square_density _ _ f g hf hg hfn hgn

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_DifferenceMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Means of nonnegative difference convolutions

Removing the zero difference can only decrease the sum. This supplies
the mean bounds for the nonnegative quartet majorants in Section 6.
-/

namespace Ostmann

open scoped BigOperators

theorem differenceMoment_nonneg {p : ℕ} [NeZero p]
    (f g : ZMod p → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (y : ZMod p) :
    0 ≤ differenceMoment f g y :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (hf _) (hg _))

theorem sum_differenceMoment {p : ℕ} [NeZero p] (f g : ZMod p → ℝ) :
    (∑ y : ZMod p, differenceMoment f g y) =
      (∑ x : ZMod p, f x) * ∑ z : ZMod p, g z := by
  have hshift (x : ZMod p) : (∑ y : ZMod p, g (x - y)) = ∑ z : ZMod p, g z := by
    simpa [sub_eq_add_neg] using
      ((Equiv.neg (ZMod p)).trans (Equiv.addLeft x)).bijective.sum_comp g
  unfold differenceMoment
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hshift]
  rw [Finset.sum_mul]

theorem sum_units_differenceMoment_le {p : ℕ} [Fact p.Prime]
    (f g : ZMod p → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    (∑ y : (ZMod p)ˣ, differenceMoment f g y) ≤
      (∑ x : ZMod p, f x) * ∑ z : ZMod p, g z := by
  classical
  rw [← sum_differenceMoment]
  exact OAI.sum_le_sum_of_injOn (fun y : (ZMod p)ˣ => (y : ZMod p))
    Units.val_injective.injOn (Finset.subset_univ _) (fun _ _ => le_rfl)
    (fun y _ _ => differenceMoment_nonneg f g hf hg y)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_TreeDensity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Iterating the elementary tree density estimate

A split plan allows the remaining unit parameters to depend on every
previous split coordinate. The bound is uniform over those choices.
The separate rational-coordinate lemmas identify the manuscript's tree
with this inverse-square split law on valid ancestor data.
-/

namespace Ostmann

open scoped BigOperators

theorem treeDensityMajorant_zero {p : ℕ} [Fact p.Prime] (w : ZMod p → ℝ) (n : ℕ) :
    treeDensityMajorant w n 0 = 0 := by
  cases n <;> simp [treeDensityMajorant]

theorem treeDensityMajorant_nonneg {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (hw : ∀ x, 0 ≤ w x) (n : ℕ) (d : ZMod p) :
    0 ≤ treeDensityMajorant w n d := by
  induction n generalizing d with
  | zero => simp only [treeDensityMajorant]; split_ifs; exact le_rfl; exact hw d
  | succ n ih =>
    simp only [treeDensityMajorant]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (by positivity) (differenceMoment_nonneg _ _ ih ih d)

theorem treeDensityMajorant_mean_le {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (hw : ∀ x, 0 ≤ w x) (E : ℝ)
    (hE : (∑ d : (ZMod p)ˣ, w d) / (Fintype.card (ZMod p)ˣ : ℝ) ≤ E) (n : ℕ) :
    (∑ d : (ZMod p)ˣ, treeDensityMajorant w n d) /
      (Fintype.card (ZMod p)ˣ : ℝ) ≤ binaryMomentBound E n := by
  have hU : 0 < (Fintype.card (ZMod p)ˣ : ℝ) := by exact_mod_cast Fintype.card_pos
  induction n with
  | zero =>
    simpa only [treeDensityMajorant, Units.ne_zero, ite_false, if_false, binaryMomentBound] using hE
  | succ n ih =>
    have hzero := treeDensityMajorant_zero w n
    have hsum := sum_units_eq_sum_of_zero (treeDensityMajorant w n) hzero
    have hnn : 0 ≤ (∑ d : (ZMod p)ˣ, treeDensityMajorant w n d) /
        (Fintype.card (ZMod p)ˣ : ℝ) := by
      apply div_nonneg _ hU.le
      exact Finset.sum_nonneg fun d _ => treeDensityMajorant_nonneg w hw n d
    calc
      _ = (2 / (Fintype.card (ZMod p)ˣ : ℝ)) *
          (∑ d : (ZMod p)ˣ,
            differenceMoment (treeDensityMajorant w n) (treeDensityMajorant w n) d) /
            (Fintype.card (ZMod p)ˣ : ℝ) := by
        simp only [treeDensityMajorant, Units.ne_zero, ite_false, if_false, ← Finset.mul_sum]
      _ ≤ (2 / (Fintype.card (ZMod p)ˣ : ℝ)) *
          ((∑ x : ZMod p, treeDensityMajorant w n x) ^ 2) /
            (Fintype.card (ZMod p)ˣ : ℝ) := by
        apply div_le_div_of_nonneg_right _ hU.le
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [pow_two] using sum_units_differenceMoment_le
          (treeDensityMajorant w n) (treeDensityMajorant w n)
          (treeDensityMajorant_nonneg w hw n) (treeDensityMajorant_nonneg w hw n)
      _ = 2 * ((∑ d : (ZMod p)ˣ, treeDensityMajorant w n d) /
          (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 := by rw [← hsum]; ring
      _ ≤ 2 * binaryMomentBound E n ^ 2 := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnn ih 2) (by norm_num)
      _ = _ := rfl

/-- The recursive density bound in closed form. -/
theorem binaryMomentBound_eq (E : ℝ) (n : ℕ) :
    binaryMomentBound E n = (2 * E) ^ (2 ^ n) / 2 := by
  induction n with
  | zero => simp [binaryMomentBound]
  | succ n ih =>
    rw [binaryMomentBound, ih, pow_succ (2 : ℕ), pow_mul]
    ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_RationalTree
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Recursive rational tree data

The product coefficient is an index of the data type. At every split,
its child indices encode exactly the consistency conditions on the
fixed constants in `src36`.
-/

namespace Ostmann

open scoped BigOperators

theorem rationalTreeArgument_child {p : ℕ} [Fact p.Prime]
    (s D u X C m v : (ZMod p)ˣ) :
    (rationalTreeArgument s (u * C) D v X m : ZMod p) =
      childArgument (s : ZMod p) D u ((X * C * m : (ZMod p)ˣ) : ZMod p) v := by
  simp only [rationalTreeArgument, childArgument, Units.val_div_eq_div_val, Units.val_mul]
  congr 1
  ring

theorem rationalTreeArgument_node {p : ℕ} [Fact p.Prime]
    (s CL CR D XL XR P : (ZMod p)ˣ) :
    rationalTreeArgument s (CL * CR) D XL XR P = rationalNodeArgument s D XL XR CL CR P := by
  unfold rationalTreeArgument rationalNodeArgument
  congr 1
  simp only [mul_left_comm, mul_comm]

theorem rationalTreeMoment_nonneg {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (hw : ∀ x, 0 ≤ w x) (D : (ZMod p)ˣ)
    {n : ℕ} {C : (ZMod p)ˣ} (T : RationalTreeData (ZMod p)ˣ n C)
    (XL XR P : (ZMod p)ˣ) : 0 ≤ rationalTreeMoment w D T XL XR P := by
  induction T generalizing XL XR P with
  | leaf s C => exact hw _
  | node s CL CR u left right ihL ihR =>
    simp only [rationalTreeMoment]
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro m _
    dsimp
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (ihL _ _ _) (ihR _ _ _)

/-- The actual recursive rational-node moment is bounded by the uniform density majorant. -/
theorem rationalTreeMoment_le_majorant {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (hw : ∀ x, 0 ≤ w x) (D : (ZMod p)ˣ)
    {n : ℕ} {C : (ZMod p)ˣ} (T : RationalTreeData (ZMod p)ˣ n C)
    (XL XR P : (ZMod p)ˣ) :
    rationalTreeMoment w D T XL XR P ≤
      treeDensityMajorant w n (rationalTreeArgument T.frequency C D XL XR P) := by
  induction T generalizing XL XR P with
  | leaf s C =>
    simp only [rationalTreeMoment, RationalTreeData.frequency, treeDensityMajorant,
      Units.ne_zero, ite_false, if_false, le_refl]
  | @node n s CL CR u left right ihL ihR =>
    have harg := rationalTreeArgument_node s CL CR D XL XR P
    change _ ≤ treeDensityMajorant w (n + 1) (rationalTreeArgument s (CL * CR) D XL XR P)
    rw [harg]
    simp only [treeDensityMajorant, Units.ne_zero, ite_false, if_false]
    calc
      _ ≤ (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
          ∑ m : (ZMod p)ˣ, rationalNodeValue s left.frequency right.frequency D u XL XR CL CR P
            (treeDensityMajorant w n) (treeDensityMajorant w n) m := by
        unfold rationalTreeMoment
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro m _
        dsimp [rationalNodeValue]
        split_ifs with hv
        · exact le_rfl
        · have hL := ihL (Units.mk0 _ hv) XL m
          have hR := ihR (Units.mk0 _ hv) XR (P / m)
          rw [rationalTreeArgument_child] at hL hR
          exact mul_le_mul hL hR (rationalTreeMoment_nonneg w hw D right _ _ _)
            (treeDensityMajorant_nonneg w hw n _)
      _ ≤ (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
          (2 * ∑ x : ZMod p, treeDensityMajorant w n x *
            treeDensityMajorant w n (x - rationalNodeArgument s D XL XR CL CR P)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact rationalNodeValue_sum_le s left.frequency right.frequency D u XL XR CL CR P
          _ _ (treeDensityMajorant_zero w n) (treeDensityMajorant_zero w n)
          (treeDensityMajorant_nonneg w hw n) (treeDensityMajorant_nonneg w hw n)
      _ = _ := by unfold differenceMoment; ring

theorem rationalTreeMoment_mean_le {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (hw : ∀ x, 0 ≤ w x) (E : ℝ)
    (hE : (∑ d : (ZMod p)ˣ, w d) / (Fintype.card (ZMod p)ˣ : ℝ) ≤ E)
    (D : (ZMod p)ˣ) {n : ℕ} {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ n C) (XL XR : (ZMod p)ˣ) :
    (∑ P : (ZMod p)ˣ, rationalTreeMoment w D T XL XR P) /
      (Fintype.card (ZMod p)ˣ : ℝ) ≤ binaryMomentBound E n := by
  calc
    _ ≤ (∑ P : (ZMod p)ˣ,
        treeDensityMajorant w n (rationalTreeArgument T.frequency C D XL XR P)) /
          (Fintype.card (ZMod p)ˣ : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum fun P _ => rationalTreeMoment_le_majorant w hw D T XL XR P
    _ = (∑ d : (ZMod p)ˣ, treeDensityMajorant w n d) /
          (Fintype.card (ZMod p)ˣ : ℝ) := by
      congr 1
      exact (rationalTreeArgumentEquiv T.frequency C D XL XR).sum_comp
        (fun d => treeDensityMajorant w n d)
    _ ≤ _ := treeDensityMajorant_mean_le w hw E hE n

/-- The actual rational tree, averaged in its root product, satisfies `src37`. -/
theorem rationalTreeMoment_l2_bound {p : ℕ} [Fact p.Prime]
    (hp : 3 ≤ p) (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (D : (ZMod p)ˣ) {n : ℕ} {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ n C) (XL XR : (ZMod p)ˣ) :
    (∑ P : (ZMod p)ˣ, rationalTreeMoment (fun x => ‖g x‖ ^ 2) D T XL XR P) /
      (Fintype.card (ZMod p)ˣ : ℝ) ≤ (3 : ℝ) ^ (2 ^ n) := by
  have hpr : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hU : (Fintype.card (ZMod p)ˣ : ℝ) = (p : ℝ) - 1 := by
    rw [ZMod.card_units, Nat.cast_sub (Fact.out : p.Prime).one_lt.le, Nat.cast_one]
  have hsum := sum_units_eq_sum_of_zero (fun x => ‖g x‖ ^ 2) (by simp [hg])
  have hE : (∑ d : (ZMod p)ˣ, ‖g d‖ ^ 2) /
      (Fintype.card (ZMod p)ˣ : ℝ) ≤ 3 / 2 := by
    rw [hU, hsum]
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < p - 1)).mpr
    linarith
  have h := rationalTreeMoment_mean_le (fun x => ‖g x‖ ^ 2) (fun _ => sq_nonneg _)
    (3 / 2) hE D T XL XR
  rw [binaryMomentBound_eq] at h
  norm_num only [show (2 : ℝ) * (3 / 2) = 3 by norm_num] at h
  exact h.trans (by have := pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (2 ^ n); linarith)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_RationalTreeLeaves
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The rational tree under independent uniform leaf sampling -/

namespace Ostmann

open scoped BigOperators

theorem rationalTreeLeafValue_fiber_sum {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (D : (ZMod p)ˣ) {n : ℕ} {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ n C) (XL XR P : (ZMod p)ˣ) :
    (∑ x : TreeLeafFiber (ZMod p)ˣ n P, rationalTreeLeafValue w D T XL XR x.1) =
      (Fintype.card (ZMod p)ˣ : ℝ) ^ (2 ^ n - 1) * rationalTreeMoment w D T XL XR P := by
  induction T generalizing XL XR P with
  | leaf s C =>
    have he : ∀ x : TreeLeafFiber (ZMod p)ˣ 0 P, (x.1 : (ZMod p)ˣ) = P :=
      fun x => x.property
    simp only [rationalTreeLeafValue, he, Finset.sum_const, Finset.card_univ,
      card_treeLeafFiber, pow_zero, Nat.sub_self, pow_zero, one_smul, one_mul,
      rationalTreeMoment]
  | @node n s CL CR u left right ihL ihR =>
    rw [sum_treeLeafFiber_succ]
    have hterm (m : (ZMod p)ˣ) :
        (∑ a : TreeLeafFiber (ZMod p)ˣ n m,
          ∑ b : TreeLeafFiber (ZMod p)ˣ n (P / m),
            rationalTreeLeafValue w D (.node s CL CR u left right) XL XR (a.1, b.1)) =
        ((Fintype.card (ZMod p)ˣ : ℝ) ^ (2 ^ n - 1)) ^ 2 *
          (let HL : (ZMod p)ˣ := XL * CL * m
           let HR : (ZMod p)ˣ := XR * CR * (P / m)
           let v := reconstructedEntry (s : ZMod p) left.frequency right.frequency u HL HR
           if hv : v = 0 then 0 else
             rationalTreeMoment w D left (Units.mk0 v hv) XL m *
               rationalTreeMoment w D right (Units.mk0 v hv) XR (P / m)) := by
      have hfib {Q : (ZMod p)ˣ} (x : TreeLeafFiber (ZMod p)ˣ n Q) :
          treeLeafProduct n x.1 = Q := x.property
      simp only [rationalTreeLeafValue, hfib]
      dsimp
      split_ifs with hv
      · simp
      · let v := reconstructedEntry (s : ZMod p) left.frequency right.frequency u
          ((XL : ZMod p) * CL * m) ((XR : ZMod p) * CR * (P / m : (ZMod p)ˣ))
        let V : (ZMod p)ˣ := Units.mk0 v hv
        change (∑ a : TreeLeafFiber (ZMod p)ˣ n m,
          ∑ b : TreeLeafFiber (ZMod p)ˣ n (P / m),
            rationalTreeLeafValue w D left V XL a.1 *
            rationalTreeLeafValue w D right V XR b.1) = _
        rw [← Fintype.sum_mul_sum
          (fun a : TreeLeafFiber (ZMod p)ˣ n m => rationalTreeLeafValue w D left V XL a.1)
          (fun b : TreeLeafFiber (ZMod p)ˣ n (P / m) => rationalTreeLeafValue w D right V XR b.1)]
        rw [ihL, ihR]
        ring
    simp_rw [hterm]
    rw [← Finset.mul_sum]
    simp only [rationalTreeMoment]
    have hU : (Fintype.card (ZMod p)ˣ : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have hn : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
    have hexp : 2 ^ (n + 1) - 1 = (2 ^ n - 1) * 2 + 1 := by
      rw [pow_succ]
      omega
    rw [hexp]
    conv_rhs => arg 1; rw [pow_succ, pow_mul]
    field_simp

theorem rationalTreeLeafValue_mean_eq {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (D : (ZMod p)ˣ) {n : ℕ} {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ n C) (XL XR : (ZMod p)ˣ) :
    (∑ x : TreeLeafTuple (ZMod p)ˣ n, rationalTreeLeafValue w D T XL XR x) /
      (Fintype.card (TreeLeafTuple (ZMod p)ˣ n) : ℝ) =
    (∑ P : (ZMod p)ˣ, rationalTreeMoment w D T XL XR P) /
      (Fintype.card (ZMod p)ˣ : ℝ) := by
  rw [sum_treeLeafTuple_by_product]
  simp_rw [rationalTreeLeafValue_fiber_sum]
  rw [← Finset.mul_sum, card_treeLeafTuple, Nat.cast_pow]
  have hU : (Fintype.card (ZMod p)ˣ : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hn : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
  conv_lhs => rhs; rw [← Nat.sub_add_cancel hn, pow_succ]
  field_simp

/-- The first part of the tree comparison: independent uniform leaves give the `3^r` bound. -/
theorem rationalTreeLeafValue_l2_bound {p : ℕ} [Fact p.Prime]
    (hp : 3 ≤ p) (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (D : (ZMod p)ˣ) {n : ℕ} {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ n C) (XL XR : (ZMod p)ˣ) :
    (∑ x : TreeLeafTuple (ZMod p)ˣ n,
      rationalTreeLeafValue (fun y => ‖g y‖ ^ 2) D T XL XR x) /
      (Fintype.card (TreeLeafTuple (ZMod p)ˣ n) : ℝ) ≤ (3 : ℝ) ^ (2 ^ n) := by
  rw [rationalTreeLeafValue_mean_eq]
  exact rationalTreeMoment_l2_bound hp g hg henergy D T XL XR

theorem norm_rationalTreeAmplitude_sq {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) {n : ℕ} {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ n C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool n) (m : TreeLeafTuple (ZMod p)ˣ n) :
    ‖rationalTreeAmplitude g D T XL XR c m‖ ^ 2 =
      rationalTreeLeafValue (fun y => ‖g y‖ ^ 2) D T XL XR m := by
  induction T generalizing XL XR with
  | leaf s C =>
    cases c <;> simp [rationalTreeAmplitude, rationalTreeLeafValue]
  | node s CL CR u left right ihL ihR =>
    simp only [rationalTreeAmplitude, rationalTreeLeafValue]
    split_ifs
    · simp
    · rw [norm_mul, mul_pow, ihL, ihR]

/-- Equation `src37`, with the actual reconstructed-node diagram and uniform independent leaves. -/
theorem rationalTreeAmplitude_l2_bound {p : ℕ} [Fact p.Prime]
    (hp : 3 ≤ p) (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (D : (ZMod p)ˣ) {n : ℕ} {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ n C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool n) :
    (∑ m : TreeLeafTuple (ZMod p)ˣ n, ‖rationalTreeAmplitude g D T XL XR c m‖ ^ 2) /
      (Fintype.card (TreeLeafTuple (ZMod p)ˣ n) : ℝ) ≤ (3 : ℝ) ^ (2 ^ n) := by
  simp_rw [norm_rationalTreeAmplitude_sq]
  exact rationalTreeLeafValue_l2_bound hp g hg henergy D T XL XR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TreeLeafIndex
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Labeled leaves and bottom quartets of a full binary tree -/

namespace Ostmann

open scoped BigOperators

theorem indexedRationalAmplitude_l2_bound {p : ℕ} [Fact p.Prime]
    (hp : 3 ≤ p) (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (D : (ZMod p)ˣ) {n : ℕ} {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ n C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool n) :
    (∑ m : TreeLeafIndex n → (ZMod p)ˣ, ‖indexedRationalAmplitude g D T XL XR c m‖ ^ 2) /
      (Fintype.card (TreeLeafIndex n → (ZMod p)ˣ) : ℝ) ≤ (3 : ℝ) ^ (2 ^ n) := by
  have hsum := (treeLeafTupleEquiv (ZMod p)ˣ n).symm.sum_comp
    (fun m => ‖rationalTreeAmplitude g D T XL XR c m‖ ^ 2)
  have hcard := Fintype.card_congr (treeLeafTupleEquiv (ZMod p)ˣ n)
  change (∑ m : TreeLeafIndex n → (ZMod p)ˣ,
    ‖rationalTreeAmplitude g D T XL XR c ((treeLeafTupleEquiv (ZMod p)ˣ n).symm m)‖ ^ 2) /
    (Fintype.card (TreeLeafIndex n → (ZMod p)ˣ) : ℝ) ≤ _
  rw [hsum, ← hcard]
  exact rationalTreeAmplitude_l2_bound hp g hg henergy D T XL XR c

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SpectatorNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absolute spectator correlations for the norm comparison -/

namespace Ostmann

open scoped BigOperators

/-- The same second-moment bound on both factors controls their absolute
correlation. This form avoids introducing a square-root loss. -/
theorem uniform_absolute_pair_le {A : Type*} [Fintype A] [Nonempty A]
    (F G : A → ℂ) (B : ℝ)
    (hF : (∑ x, ‖F x‖ ^ 2) / (Fintype.card A : ℝ) ≤ B)
    (hG : (∑ x, ‖G x‖ ^ 2) / (Fintype.card A : ℝ) ≤ B) :
    (∑ x, ‖F x * star (G x)‖) / (Fintype.card A : ℝ) ≤ B := by
  have hpoint (x : A) : 2 * ‖F x * star (G x)‖ ≤ ‖F x‖ ^ 2 + ‖G x‖ ^ 2 := by
    rw [norm_mul, norm_star]
    nlinarith [sq_nonneg (‖F x‖ - ‖G x‖)]
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset A)) => hpoint x)
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  have hc : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hc).mpr
  have hF' := (div_le_iff₀ hc).mp hF
  have hG' := (div_le_iff₀ hc).mp hG
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SpectatorProductNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full spectator cost under its independent residue law -/

namespace Ostmann

open scoped BigOperators Classical

theorem product_uniform_mean {I : Type*} [Fintype I] {A : I → Type*}
    [∀ i, Fintype (A i)] (F : ∀ i, A i → ℝ) :
    (Fintype.card (∀ i, A i) : ℝ)⁻¹ * (∑ x : ∀ i, A i, ∏ i, F i (x i)) =
      ∏ i, (Fintype.card (A i) : ℝ)⁻¹ * ∑ a, F i a := by
  rw [← Fintype.prod_sum, Fintype.card_pi, Nat.cast_prod,
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]

theorem product_uniform_mean_le {I : Type*} [Fintype I] {A : I → Type*}
    [∀ i, Fintype (A i)] (F : ∀ i, A i → ℝ) (hF : ∀ i a, 0 ≤ F i a)
    (B : I → ℝ) (hB : ∀ i, (Fintype.card (A i) : ℝ)⁻¹ * ∑ a, F i a ≤ B i) :
    (Fintype.card (∀ i, A i) : ℝ)⁻¹ * (∑ x : ∀ i, A i, ∏ i, F i (x i)) ≤ ∏ i, B i := by
  rw [product_uniform_mean]
  exact Finset.prod_le_prod (fun i _ => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun a _ => hF i a)) (fun i _ => hB i)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized Fourier transform of the actual centered density -/

namespace Ostmann

open scoped BigOperators

theorem densityFourier_energy {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ a : ZMod q, ‖densityFourier f a‖ ^ 2) = ∑ x : ZMod q, ‖f x‖ ^ 2 := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  simp only [densityFourier, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (Nat.cast_nonneg q)]
  rw [← Finset.mul_sum, additiveFourier_parseval, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingGiantSamples
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the moving-giant tree from the sampled compensation slots

Each reversing node samples four positions per leaf of either child. Their
products are inserted into both child regular lists. The constructor proves
the required product consistency; it does not ask for a pre-existing diagram.
-/

namespace Ostmann
open scoped BigOperators

/-- Unit conditions for the diagram follow from the actual sampled products
and original frequency bounds. They are independent of the bulk variables. -/
theorem buildMovingGiantTree_units {q n : ℕ} [Fact q.Prime] (t : FrequencyTree ℤ n)
    (small : TreeLeafTuple ℕ n) (samples : MovingGiantSamples n)
    (hfreq : movingGiantFrequencyUnits q n t)
    (hsmall : ((treeLeafProduct n small : ℕ) : ZMod q) ≠ 0)
    (hsamples : samples.UnitsAt q) :
    (buildMovingGiantTree n t small samples).UnitsAt q := by
  induction samples with
  | leaf => exact ⟨hfreq, hsmall⟩
  | @node n samples left right ihL ihR =>
    have hparts : ((treeLeafProduct n small.1 : ℕ) : ZMod q) ≠ 0 ∧
        ((treeLeafProduct n small.2 : ℕ) : ZMod q) ≠ 0 := by
      simpa only [treeLeafProduct, Nat.cast_mul, mul_ne_zero_iff] using hsmall
    refine ⟨hfreq.1, hparts.1, hparts.2, hsamples.1, ?_, ?_⟩
    · rw [MovingGiantTree.castConstant_units]
      apply ihL _ _ hfreq.2.1 _ hsamples.2.1
      rw [multiplySmallLeaves_product, Nat.cast_mul]
      exact mul_ne_zero hsamples.1 hparts.1
    · rw [MovingGiantTree.castConstant_units]
      apply ihR _ _ hfreq.2.2 _ hsamples.2.2
      rw [multiplySmallLeaves_product, Nat.cast_mul]
      exact mul_ne_zero hsamples.1 hparts.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampleValues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The labelled sampler evaluates to the actual natural prime sampler -/

namespace Ostmann
open scoped BigOperators

theorem movingNaturalProduct_append {σ : Type*} (value : σ → ℕ) (x y : List σ) :
    MovingSlotReversal.naturalProduct value (x ++ y) =
      MovingSlotReversal.naturalProduct value x * MovingSlotReversal.naturalProduct value y := by
  simp only [MovingSlotReversal.naturalProduct, List.map_append, List.prod_append]

theorem movingSlotValues_flatten {σ : Type*} (value : σ → ℕ) (n : ℕ)
    (x : TreeLeafTuple (List σ) n) :
    MovingSlotReversal.naturalProduct value (flattenMovingSlots n x) =
      treeLeafProduct n (movingSlotValues value n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [flattenMovingSlots, MovingSlotReversal.naturalProduct, List.map_append,
      List.prod_append, movingSlotValues, treeLeafProduct]
    exact congrArg₂ (· * ·) (ih x.1) (ih x.2)

theorem movingSlotValues_append {σ : Type*} (value : σ → ℕ) (n : ℕ)
    (x y : TreeLeafTuple (List σ) n) :
    movingSlotValues value n (appendMovingSlotLeaves n x y) =
      multiplySmallLeaves n (movingSlotValues value n x) (movingSlotValues value n y) := by
  induction n with
  | zero =>
    simp only [movingSlotValues, appendMovingSlotLeaves, multiplySmallLeaves,
      MovingSlotReversal.naturalProduct, List.map_append, List.prod_append]
  | succ n ih => exact Prod.ext (ih x.1 y.1) (ih x.2 y.2)

theorem movingCompensationValues_product {σ : Type*} (value : σ → ℕ) (n : ℕ)
    (x : TreeLeafTuple (Fin 4 → σ) n) :
    movingSlotValues value n (movingCompensationSlots n x) =
      compensationLeafProducts n (movingCompensationValues value n x) := by
  induction n with
  | zero =>
    change ((List.ofFn (show Fin 4 → σ from x)).map value).prod = ∏ i : Fin 4, value (x i)
    rw [List.map_ofFn, List.prod_ofFn]
    rfl
  | succ n ih => exact Prod.ext (ih x.1) (ih x.2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSlotSystem
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original recursive weight on moving-giant states

A reconstructed pivot is the composite `u*p`; only its quotient `p` becomes
the new giant. The compensation primes remain in the regular child lists.
-/

namespace Ostmann
open scoped Classical

theorem MovingSlotData.Follows.root {σ : Type*} {n : ℕ} {T : MovingSlotData σ n}
    {t : FrequencyTree ℤ n} (h : T.Follows t) : T.frequency = frequencyRoot n t := by
  cases T with
  | leaf => exact h
  | node => exact h.1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRealSmooth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single real smooth kernel for the two original giant coordinates -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate SchwartzMap

theorem MovingSlotReversal.continuous_realPivot {σ : Type*}
    (value : σ → ℕ) (s : MovingSlotReversal σ) {A : Type*} [TopologicalSpace A]
    (L R : A → ℝ) (hL : Continuous L) (hR : Continuous R) :
    Continuous (fun x => s.realPivot value (L x) (R x)) := by
  unfold realPivot
  exact ((continuous_const.mul hR).sub (continuous_const.mul hL)).div_const _

theorem MovingSlotData.continuous_realLeafModuli {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) {A : Type*} [TopologicalSpace A]
    (L R : A → ℝ) (hL : Continuous L) (hR : Continuous R) (i : TreeLeafIndex n) :
    Continuous (fun x => T.realLeafModuli value (L x) (R x) i) := by
  induction T generalizing L R with
  | leaf => exact (hL.mul hR).mul_const _
  | node s CL CR u left right ihL ihR =>
    have hp := (MovingSlotData.step s CL CR u left right false).continuous_realPivot value L R hL hR
    cases i with
    | inl i => exact ihL _ L hp hL i
    | inr i => exact ihR _ R hp hR i

theorem continuous_movingRealFourierWeight {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) {A : Type*} [TopologicalSpace A]
    (L R : A → ℝ) (hL : Continuous L) (hR : Continuous R) :
    Continuous (fun x => movingRealFourierWeight value T ψ X lo hi hlo hhi (L x) (R x)) := by
  apply continuous_finsetProd
  intro i _
  have hc := (fourierPolynomialFactor Polynomial.X ψ (T.leafFrequencies i) lo hi hlo hhi).continuous_value.comp
    ((T.continuous_realLeafModuli value L R hL hR i).div_const X)
  dsimp only
  split_ifs
  · exact Complex.continuous_conj.comp hc
  · exact hc

theorem continuous_movingRealNodeCutoff {σ : Type*} (value : σ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    {n : ℕ} (T : MovingSlotData σ n) {A : Type*} [TopologicalSpace A]
    (L R : A → ℝ) (hL : Continuous L) (hR : Continuous R) :
    Continuous (fun x => movingRealNodeCutoff value φ G T (L x) (R x)) := by
  have hp (g : ℝ) : Continuous (fun x => (positiveLogCutoff φ g x : ℂ)) := by
    have he (x : ℝ) := logCutoffPolynomialFactor_value Polynomial.X φ g B D hB hD hφ hlip hout x
    simp only [Polynomial.eval_X] at he
    exact ((logCutoffPolynomialFactor Polynomial.X φ g B D hB hD hφ hlip).continuous_value).congr he
  induction T generalizing L R with
  | leaf => exact continuous_const
  | @node n s CL CR u left right ihL ihR =>
    have hc := (MovingSlotData.step s CL CR u left right false).continuous_realPivot value L R hL hR
    exact (((hp (G (n + 1))).comp hc).mul (ihL _ L hc hL)).mul (ihR _ R hc hR)

theorem continuous_movingRealSmoothWeight {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ B)
    (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    {A : Type*} [TopologicalSpace A] (L R : A → ℝ) (hL : Continuous L) (hR : Continuous R) :
    Continuous (fun x => movingRealSmoothWeight value T ψ X lo hi hlo hhi φ G (L x) (R x)) :=
  (continuous_movingRealFourierWeight value T ψ X lo hi hlo hhi L R hL hR).mul
    (continuous_movingRealNodeCutoff value φ G B D hB hD hφ hlip hout T L R hL hR)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRealKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurability and uniform bounds for the original two-giant kernel -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate SchwartzMap
open MeasureTheory

theorem HistoryFormula.continuous_realEval {σ : Type*} (F : HistoryFormula σ) :
    Continuous F.realEval := by
  unfold realEval
  simp only [MvPolynomial.eval₂_eq_eval_map]
  exact (MvPolynomial.continuous_eval _).div_const _

theorem WordTransferGuard.isClosed_archimedeanAt {σ : Type*} (g : WordTransferGuard σ) :
    IsClosed {x | g.archimedeanAt x} :=
  (isClosed_le continuous_const g.pivot.continuous_realEval).inter
    ((isClosed_le g.pivot.continuous_realEval continuous_const).inter
      (isClosed_le continuous_const g.rightProduct.continuous_realEval))

theorem isClosed_movingArchimedeanGate (nodes : List MovingFormulaNode) :
    IsClosed {x | movingArchimedeanGate nodes x} := by
  induction nodes with
  | nil => simpa only [movingArchimedeanGate, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, Set.ofPred_true] using isClosed_univ
  | cons f nodes ih =>
    simpa only [movingArchimedeanGate, List.forall_mem_cons, Set.ofPred_and] using
      f.guard.isClosed_archimedeanAt.inter ih

theorem continuous_topGiantReal : Continuous (fun x : ℝ × ℝ => topGiantReal x.1 x.2) := by
  apply continuous_pi
  intro b
  cases b
  · exact continuous_fst
  · exact continuous_snd

theorem measurable_movingRealGateWeight {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (nodes : List MovingFormulaNode) (X lo hi : ℝ) :
    Measurable (fun x : ℝ × ℝ => movingRealGateWeight value T nodes X lo hi (topGiantReal x.1 x.2)) := by
  have ha : Measurable (fun x : ℝ × ℝ => movingArchimedeanFlag nodes (topGiantReal x.1 x.2)) := by
    apply Measurable.ite _ measurable_const measurable_const
    exact ((isClosed_movingArchimedeanGate nodes).preimage continuous_topGiantReal).measurableSet
  have hw : Measurable (fun x : ℝ × ℝ => movingRealWindowFlag value T X lo hi x.1 x.2) := by
    apply Measurable.ite _ measurable_const measurable_const
    have hc : IsClosed {x : ℝ × ℝ | ∀ i, T.realLeafModuli value x.1 x.2 i / X ∈ Set.Icc lo hi} := by
      simpa only [Set.ofPred_forall, Set.preimage] using isClosed_iInter (fun i : TreeLeafIndex n =>
        isClosed_Icc.preimage ((T.continuous_realLeafModuli value Prod.fst Prod.snd
          continuous_fst continuous_snd i).div_const X))
    exact hc.measurableSet
  exact ha.mul hw

theorem measurable_movingRealKernel {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (nodes : List MovingFormulaNode) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ B)
    (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (hout : ∀ x, 1 ≤ |x| → φ x = 0) :
    Measurable (fun x : ℝ × ℝ => movingRealKernel value T nodes ψ X lo hi hlo hhi φ G x.1 x.2) :=
  (measurable_movingRealGateWeight value T nodes X lo hi).mul
    (continuous_movingRealSmoothWeight value T ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout
      Prod.fst Prod.snd continuous_fst continuous_snd).measurable

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingKernelPair
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal product of the two histories in a diagonal comparison -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators Classical ComplexConjugate SchwartzMap

theorem measurable_movingRealKernelPair {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ B)
    (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (hout : ∀ x, 1 ≤ |x| → φ x = 0) :
    Measurable (fun z : ℝ × ℝ => movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G z.1 z.2) := by
  have h0 := measurable_movingRealKernel value (T false) (nodes false) ψ X lo hi hlo hhi φ G
    B D hB hD hφ hlip hout
  have h1 := measurable_movingRealKernel value (T true) (nodes true) ψ X lo hi hlo hhi φ G
    B D hB hD hφ hlip hout
  exact h0.mul (Complex.continuous_conj.measurable.comp h1)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_ReciprocalPolynomialFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized counterpart ratio is an admissible smooth factor -/

namespace Ostmann

open scoped BigOperators

theorem reciprocalPolynomialFactor_original (P : Polynomial ℝ) (hi : ℝ)
    (hhi : 1 ≤ hi) (x X M : ℝ) (hX : X ≠ 0) (hM : M ≠ 0)
    (hP : P.eval x = M / X) (hrange : M / X ∈ Set.Icc (1 : ℝ) hi) :
    (reciprocalPolynomialFactor P hi hhi).value x = Complex.ofReal (X / M) := by
  rw [ClippedPolynomialFactor.value_of_mem _ x (by
    change P.eval x ∈ Set.Icc (1 : ℝ) hi
    rw [hP]
    exact hrange)]
  change Complex.ofReal ((P.eval x)⁻¹) = _
  rw [hP]
  congr 1
  field_simp

theorem reciprocalPolynomialFactor_budget (P : Polynomial ℝ) (hi : ℝ) (hhi : 1 ≤ hi) :
    2 * (reciprocalPolynomialFactor P hi hhi).bound +
      (reciprocalPolynomialFactor P hi hhi).lip *
        ((reciprocalPolynomialFactor P hi hhi).hi - (reciprocalPolynomialFactor P hi hhi).lo) =
      hi + 1 := by
  dsimp only [reciprocalPolynomialFactor]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GiantReciprocalFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized reciprocal giant factor in the diagonal multiplier -/

namespace Ostmann

theorem giantReciprocalFactor_budget (P : Polynomial ℝ) (G : ℝ) :
    2 * (giantReciprocalFactor P G).bound + (giantReciprocalFactor P G).lip *
      ((giantReciprocalFactor P G).hi - (giantReciprocalFactor P G).lo) = 1 + Real.exp 2 := by
  rw [giantReciprocalFactor, reciprocalPolynomialFactor_budget, add_comm]

theorem giantReciprocalFactor_value (P : Polynomial ℝ) (G x : ℝ)
    (hx : P.eval x ∈ Set.Icc (Real.exp (G - 1)) (Real.exp (G + 1))) :
    (Real.exp 1 : ℂ) * (giantReciprocalFactor P G).value x = (Real.exp G / P.eval x : ℝ) := by
  have hlo : 0 < Real.exp (G - 1) := Real.exp_pos _
  have hp : 0 < P.eval x := hlo.trans_le hx.1
  have hrange : P.eval x / Real.exp (G - 1) ∈ Set.Icc (1 : ℝ) (Real.exp 2) := by
    refine ⟨(one_le_div hlo).mpr hx.1, ?_⟩
    calc
      _ ≤ Real.exp (G + 1) / Real.exp (G - 1) := div_le_div_of_nonneg_right hx.2 hlo.le
      _ = _ := by rw [← Real.exp_sub]; congr 1; ring
  rw [giantReciprocalFactor, reciprocalPolynomialFactor_original _ _ _ x
    (Real.exp (G - 1)) (P.eval x) hlo.ne' hp.ne'
    (by simp only [Polynomial.eval_mul, Polynomial.eval_C, div_eq_mul_inv, mul_comm]) hrange,
    ← Complex.ofReal_mul]
  apply congrArg (fun a : ℝ => (a : ℂ))
  rw [← mul_div_assoc, ← Real.exp_add, show 1 + (G - 1) = G by ring]

/-- Multiplication by the actual giant cutoff makes the clipped reciprocal
identical to the manuscript's reciprocal everywhere, including zero terms. -/
theorem giantReciprocalFactor_cutoff (P : Polynomial ℝ) (φ : ℝ → ℝ)
    (G B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (x : ℝ) :
    (logCutoffPolynomialFactor P φ G B D hB hD hφ hlip).value x *
      ((Real.exp 1 : ℂ) * (giantReciprocalFactor P G).value x) =
        (positiveLogCutoff φ G (P.eval x) : ℂ) * (Real.exp G / P.eval x : ℝ) := by
  rw [logCutoffPolynomialFactor_value P φ G B D hB hD hφ hlip hout x]
  by_cases hz : positiveLogCutoff φ G (P.eval x) = 0
  · simp only [hz, Complex.ofReal_zero, zero_mul]
  · have hx : 0 < P.eval x := by
      by_contra hn
      exact hz (by simp only [positiveLogCutoff, ite_eq_right hn])
    have hn : φ (Real.log (P.eval x) - G) ≠ 0 := by
      simpa only [positiveLogCutoff, ite_eq_left hx] using hz
    have hr : |Real.log (P.eval x) - G| < 1 := lt_of_not_ge (fun h => hn (hout _ h))
    have hbounds : P.eval x ∈ Set.Icc (Real.exp (G - 1)) (Real.exp (G + 1)) := by
      have h := abs_lt.mp hr
      constructor
      · rw [← Real.exp_log hx]
        exact Real.exp_le_exp.mpr (by linarith)
      · rw [← Real.exp_log hx]
        exact Real.exp_le_exp.mpr (by linarith)
    rw [giantReciprocalFactor_value P G x hbounds]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GiantOuterFactors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal two outer cutoff priors and the diagonal reciprocal factor -/

namespace Ostmann
open scoped BigOperators Classical

/-- Both actual cutoff priors are retained. In the diagonal environment the
remaining factor is precisely exp(G_R)/R, including all off-support zeros. -/
theorem giantOuterFactors_value (L R : Polynomial ℝ) (φ : ℝ → ℝ)
    (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (x : ℝ) :
    (giantOuterScalar diagonal : ℂ) *
      smoothPolynomialWeight (giantOuterFactors L R φ Jleft Jright B D hB hD hφ hlip diagonal) x =
        (positiveLogCutoff φ Jleft (L.eval x) : ℂ) * (positiveLogCutoff φ Jright (R.eval x) : ℂ) *
          (if diagonal then ((Real.exp Jright / R.eval x : ℝ) : ℂ) else 1) := by
  have hL := logCutoffPolynomialFactor_value L φ Jleft B D hB hD hφ hlip hout x
  have hR := logCutoffPolynomialFactor_value R φ Jright B D hB hD hφ hlip hout x
  have hone : onePolynomialFactor.value x = 1 := rfl
  have hrec := giantReciprocalFactor_cutoff R φ Jright B D hB hD hφ hlip hout x
  cases diagonal
  · simp only [giantOuterScalar, Bool.false_eq_true, ite_false, if_false, Complex.ofReal_one,
      giantOuterFactors, smoothPolynomialWeight, Fin.prod_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Fin.prod_univ_zero, mul_one, one_mul, hL, hR, hone]
  · simp only [giantOuterScalar, ite_true, if_true, giantOuterFactors, smoothPolynomialWeight,
      Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Fin.prod_univ_zero, mul_one]
    calc
      _ = (logCutoffPolynomialFactor L φ Jleft B D hB hD hφ hlip).value x *
          ((logCutoffPolynomialFactor R φ Jright B D hB hD hφ hlip).value x *
            ((Real.exp 1 : ℂ) * (giantReciprocalFactor R Jright).value x)) := by ring
      _ = _ := by rw [hL, hrec]; ring

theorem giantOuterFactors_budget (L R : Polynomial ℝ) (φ : ℝ → ℝ)
    (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (diagonal : Bool) :
    smoothPolynomialBudget (giantOuterFactors L R φ Jleft Jright B D hB hD hφ hlip diagonal) =
      (2 * B + D * (Real.exp 2 - 1)) ^ 2 * (if diagonal then 1 + Real.exp 2 else 2) := by
  have hL := logCutoffPolynomialFactor_budget L φ Jleft B D hB hD hφ hlip
  have hR := logCutoffPolynomialFactor_budget R φ Jright B D hB hD hφ hlip
  cases diagonal
  · simp only [giantOuterFactors, Bool.false_eq_true, ite_false, if_false, smoothPolynomialBudget,
      Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Fin.prod_univ_zero, mul_one, onePolynomialFactor]
    rw [hL, hR]
    ring
  · simp only [giantOuterFactors, ite_true, if_true, smoothPolynomialBudget,
      Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Fin.prod_univ_zero, mul_one]
    rw [hL, hR, giantReciprocalFactor_budget]
    ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOuterKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two-history kernel with its original outer priors and diagonal ratio -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators Classical ComplexConjugate SchwartzMap

theorem giantOuterWeight_polynomial (L R : Polynomial ℝ) (φ : ℝ → ℝ)
    (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (x : ℝ) :
    giantOuterWeight φ Jleft Jright diagonal (L.eval x) (R.eval x) =
      (giantOuterScalar diagonal : ℂ) *
        smoothPolynomialWeight (giantOuterFactors L R φ Jleft Jright B D hB hD hφ hlip diagonal) x :=
  (giantOuterFactors_value L R φ Jleft Jright B D hB hD hφ hlip hout diagonal x).symm

theorem giantOuterWeight_norm (φ : ℝ → ℝ) (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (L R : ℝ) :
    ‖giantOuterWeight φ Jleft Jright diagonal L R‖ ≤
      giantOuterScalar diagonal * (2 * B + D * (Real.exp 2 - 1)) ^ 2 *
        (if diagonal then 1 + Real.exp 2 else 2) := by
  have hs : 0 ≤ giantOuterScalar diagonal := by cases diagonal <;> simp [giantOuterScalar, (Real.exp_pos _).le]
  have hv := giantOuterWeight_polynomial (Polynomial.C L) (Polynomial.C R) φ Jleft Jright B D
    hB hD hφ hlip hout diagonal 0
  simp only [Polynomial.eval_C] at hv
  rw [hv, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs]
  have h := mul_le_mul_of_nonneg_left (smoothPolynomialWeight_norm
    (giantOuterFactors (Polynomial.C L) (Polynomial.C R) φ Jleft Jright B D hB hD hφ hlip diagonal) 0) hs
  rw [giantOuterFactors_budget] at h
  simpa only [mul_assoc] using h

theorem measurable_giantOuterWeight (φ : ℝ → ℝ) (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) :
    Measurable (fun z : ℝ × ℝ => giantOuterWeight φ Jleft Jright diagonal z.1 z.2) := by
  have hc (J : ℝ) : Measurable (fun x => (positiveLogCutoff φ J x : ℂ)) := by
    have he (x : ℝ) := logCutoffPolynomialFactor_value Polynomial.X φ J B D hB hD hφ hlip hout x
    simp only [Polynomial.eval_X] at he
    exact ((logCutoffPolynomialFactor Polynomial.X φ J B D hB hD hφ hlip).continuous_value.congr he).measurable
  have hratio : Measurable (fun z : ℝ × ℝ => if diagonal then ((Real.exp Jright / z.2 : ℝ) : ℂ) else 1) := by
    cases diagonal
    · exact measurable_const
    · exact Complex.continuous_ofReal.measurable.comp (measurable_const.div measurable_snd)
  exact ((hc Jleft).comp measurable_fst |>.mul ((hc Jright).comp measurable_snd)).mul hratio

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_GiantDensitySum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Moving the finite residue average inside the common real integral -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators Classical

theorem double_integral_finset_sum {A : Type*} (S : Finset A)
    (μ ν : Measure ℝ) (F : A → ℝ → ℝ → ℂ)
    (hinner : ∀ a ∈ S, ∀ x, Integrable (F a x) ν)
    (houter : ∀ a ∈ S, Integrable (fun x => ∫ y, F a x y ∂ν) μ) :
    (∫ x, ∫ y, ∑ a ∈ S, F a x y ∂ν ∂μ) =
      ∑ a ∈ S, ∫ x, ∫ y, F a x y ∂ν ∂μ := by
  have hin (x : ℝ) : (∫ y, ∑ a ∈ S, F a x y ∂ν) =
      ∑ a ∈ S, ∫ y, F a x y ∂ν :=
    integral_finsetSum S (fun a ha => hinner a ha x)
  simp_rw [hin]
  exact integral_finsetSum S houter

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RealSlotEvaluation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real bulk coordinates in the original smooth moving tree -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap ComplexConjugate

theorem realSlotProduct_nat {σ : Type*} (value : σ → ℕ) (slots : List σ) :
    realSlotProduct (fun j => (value j : ℝ)) slots =
      (MovingSlotReversal.naturalProduct value slots : ℝ) := by
  induction slots with
  | nil => simp [realSlotProduct, MovingSlotReversal.naturalProduct]
  | cons j slots ih => simpa only [realSlotProduct, MovingSlotReversal.naturalProduct,
      List.map_cons, List.prod_cons, Nat.cast_mul] using congrArg ((value j : ℝ) * ·) ih

theorem MovingSlotReversal.realValuePivot_nat {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℕ) (L R : ℝ) :
    s.realValuePivot (fun j => (value j : ℝ)) L R = s.realPivot value L R := by
  simp only [realValuePivot, realPivot, realSlotProduct_nat]

theorem MovingSlotData.realValueLeafModuli_nat {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : ℝ) (j : TreeLeafIndex n) :
    T.realValueLeafModuli (fun i => (value i : ℝ)) L R j = T.realLeafModuli value L R j := by
  induction T generalizing L R with
  | leaf => simp only [realValueLeafModuli, realLeafModuli, realSlotProduct_nat]
  | node s CL CR u left right ihL ihR =>
    cases j with
    | inl j => simp only [realValueLeafModuli, realLeafModuli, MovingSlotReversal.realValuePivot_nat, ihL]
    | inr j => simp only [realValueLeafModuli, realLeafModuli, MovingSlotReversal.realValuePivot_nat, ihR]

theorem realValueNodeCutoff_nat {σ : Type*} (value : σ → ℕ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : ℝ) :
    realValueNodeCutoff (fun i => (value i : ℝ)) φ G T L R = movingRealNodeCutoff value φ G T L R := by
  induction T generalizing L R with
  | leaf => rfl
  | node s CL CR u left right ihL ihR =>
    simp only [realValueNodeCutoff, movingRealNodeCutoff, MovingSlotReversal.realValuePivot_nat, ihL, ihR]

/-- The extension agrees exactly with the original function at every natural
prime tuple, including points where a cutoff vanishes. -/
theorem realValueSmoothWeight_nat {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ) (L R : ℝ) :
    realValueSmoothWeight (fun i => (value i : ℝ)) T ψ X lo hi hlo hhi φ G L R =
      movingRealSmoothWeight value T ψ X lo hi hlo hhi φ G L R := by
  simp only [realValueSmoothWeight, movingRealSmoothWeight, realValueFourierWeight,
    movingRealFourierWeight, realValueNodeCutoff_nat, MovingSlotData.realValueLeafModuli_nat]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFrequencyResidues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frequency residues with compensation factors inverted

Unlike the signed integer recursion, this recursion divides only by the
frequency. Compensation factors are inverted modulo a frequency power, so
no internal prime enters its period. One power is consumed per reversal.
-/

namespace Ostmann
open scoped Classical

theorem coprime_bezout_inverse_modEq (u R : ℤ) (hu : IsCoprime u R) (k : ℕ) :
    u * Int.gcdA u (R ^ k) ≡ 1 [ZMOD R ^ k] := by
  have h := Int.gcd_eq_gcd_ab u (R ^ k)
  have hg : Int.gcd u (R ^ k) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hu.pow_right
  rw [hg] at h
  apply Int.modEq_iff_dvd.mpr
  refine ⟨Int.gcdB u (R ^ k), ?_⟩
  linear_combination h

theorem movingNaturalProduct_coprime {σ : Type*} (value : σ → ℕ) (slots : List σ)
    (R : ℤ) (h : ∀ i ∈ slots, IsCoprime (value i : ℤ) R) :
    IsCoprime (MovingSlotReversal.naturalProduct value slots : ℤ) R := by
  induction slots with
  | nil => simpa [MovingSlotReversal.naturalProduct] using (isCoprime_one_left (x := R))
  | cons i slots ih =>
    simpa only [MovingSlotReversal.naturalProduct, List.map_cons, List.prod_cons, Nat.cast_mul] using
      (h i List.mem_cons_self).mul_left (ih (fun j hj => h j (List.mem_cons_of_mem i hj)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingModularSpectator
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Spectator evaluation without internal primes in the period

At a spectator prime the entire reversal denominator is a unit. The field
recursion therefore depends only on the two spectator residues, even though
the original recursion used integer division by compensation products.
-/

namespace Ostmann
open scoped Classical

theorem movingModularSpectator_norm {σ : Type*} (value : σ → ℕ)
    (q : ℕ) [Fact q.Prime] (g : ZMod q → ℂ) (D : (ZMod q)ˣ)
    (B : ℝ) (hB : 0 ≤ B) (hg : ∀ z, ‖g z‖ ≤ B)
    {n : ℕ} (T : MovingSlotData σ n) (x y : ZMod q) :
    ‖movingModularSpectator value q g D T x y‖ ≤ B ^ (2 ^ n) := by
  induction T generalizing x y with
  | leaf => simpa only [movingModularSpectator, pow_zero, pow_one] using hg _
  | @node n s CL CR U left right ihL ihR =>
    rw [movingModularSpectator]
    split_ifs
    · simpa only [norm_zero] using pow_nonneg hB (2 ^ (n + 1))
    · rw [norm_mul, norm_star]
      calc
        _ ≤ B ^ (2 ^ n) * B ^ (2 ^ n) :=
          mul_le_mul (ihL _ _) (ihR _ _) (norm_nonneg _) (pow_nonneg hB _)
        _ = B ^ (2 ^ (n + 1)) := by rw [← pow_add, pow_succ]; congr 1; omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFieldGiant
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual moving-giant recursion directly over the spectator field -/

namespace Ostmann
open scoped Classical ComplexConjugate

/-- This is a field identity on all bulk residues, so the later averaging
does not require an integer lift satisfying the original division tests. -/
theorem MovingGiantTree.exists_field_diagram {q : ℕ} [Fact q.Prime]
    {n C : ℕ} (T : MovingGiantTree n C) (hT : T.UnitsAt q) :
    ∃ (U : (ZMod q)ˣ) (R : RationalTreeData (ZMod q)ˣ n U),
      (C : ZMod q) = U ∧ (T.frequency : ZMod q) = R.frequency ∧
      ∀ (g : ZMod q → ℂ) (D A B : (ZMod q)ˣ)
        (z : TreeLeafTuple (ZMod q)ˣ n) (b : Bool),
        (if b then conj (movingFieldGiantAmplitude g D T A B z)
          else movingFieldGiantAmplitude g D T A B z) =
          rationalTreeAmplitude g D R A B (transferConjugations n b) z := by
  induction T with
  | leaf s C =>
    let S : (ZMod q)ˣ := Units.mk0 (s : ZMod q) hT.1
    let U : (ZMod q)ˣ := Units.mk0 (C : ZMod q) hT.2
    refine ⟨U, .leaf S U, rfl, rfl, ?_⟩
    intro g D A B z b
    have he : (s : ZMod q) / ((D : ZMod q) * A * B * C * (show (ZMod q)ˣ from z)) =
        (rationalTreeArgument S U D A B z : ZMod q) := by
      simp only [rationalTreeArgument, Units.val_div_eq_div_val, Units.val_mul,
        S, U, Units.val_mk0]
    cases b <;> simp only [movingFieldGiantAmplitude, he, rationalTreeAmplitude,
      transferConjugations, Bool.false_eq_true, ↓reduceIte, Complex.star_def]
  | @node n s CL CR u left right ihL ihR =>
    obtain ⟨hs, hCL, hCR, hu, hl, hr⟩ := hT
    let S : (ZMod q)ˣ := Units.mk0 (s : ZMod q) hs
    let A₀ : (ZMod q)ˣ := Units.mk0 (CL : ZMod q) hCL
    let B₀ : (ZMod q)ˣ := Units.mk0 (CR : ZMod q) hCR
    let U₀ : (ZMod q)ˣ := Units.mk0 (u : ZMod q) hu
    obtain ⟨UL, L, hUL, hfL, hL⟩ := ihL hl
    obtain ⟨UR, R, hUR, hfR, hR⟩ := ihR hr
    have eL : UL = U₀ * A₀ := by
      apply Units.ext
      simpa only [U₀, A₀, Units.val_mul, Units.val_mk0, Nat.cast_mul] using hUL.symm
    have eR : UR = U₀ * B₀ := by
      apply Units.ext
      simpa only [U₀, B₀, Units.val_mul, Units.val_mk0, Nat.cast_mul] using hUR.symm
    subst UL
    subst UR
    refine ⟨A₀ * B₀, .node S A₀ B₀ U₀ L R, ?_, rfl, ?_⟩
    · simp only [Nat.cast_mul, Units.val_mul, Units.val_mk0, A₀, B₀]
    intro g D A B z b
    let v := reconstructedEntry (s : ZMod q) (left.frequency : ZMod q)
      (right.frequency : ZMod q) (u : ZMod q)
      ((A : ZMod q) * CL * (treeLeafProduct n z.1 : (ZMod q)ˣ))
      ((B : ZMod q) * CR * (treeLeafProduct n z.2 : (ZMod q)ˣ))
    have hrec : reconstructedEntry (S : ZMod q) L.frequency R.frequency U₀
        ((A * A₀ * treeLeafProduct n z.1 : (ZMod q)ˣ) : ZMod q)
        ((B * B₀ * treeLeafProduct n z.2 : (ZMod q)ˣ) : ZMod q) = v := by
      simp only [v, hfL, hfR, S, U₀, A₀, B₀, Units.val_mul, Units.val_mk0]
    by_cases hv : v = 0
    · cases b <;> simp only [movingFieldGiantAmplitude, show
        reconstructedEntry (s : ZMod q) (left.frequency : ZMod q) (right.frequency : ZMod q)
          (u : ZMod q) ((A : ZMod q) * CL * (treeLeafProduct n z.1 : (ZMod q)ˣ))
          ((B : ZMod q) * CR * (treeLeafProduct n z.2 : (ZMod q)ˣ)) = 0 from hv,
        ↓reduceIte, map_zero, rationalTreeAmplitude, hrec, hv, Bool.false_eq_true, dite_true]
    · let V : (ZMod q)ˣ := Units.mk0 v hv
      have hleft := hL g D V A z.1 b
      have hright := hR g D V B z.2 (!b)
      have hV : Units.mk0
          (reconstructedEntry (S : ZMod q) L.frequency R.frequency U₀
            ((A * A₀ * treeLeafProduct n z.1 : (ZMod q)ˣ) : ZMod q)
            ((B * B₀ * treeLeafProduct n z.2 : (ZMod q)ˣ) : ZMod q))
          (by rw [hrec]; exact hv) = V := Units.ext hrec
      simp only [movingFieldGiantAmplitude, show
        reconstructedEntry (s : ZMod q) (left.frequency : ZMod q) (right.frequency : ZMod q)
          (u : ZMod q) ((A : ZMod q) * CL * (treeLeafProduct n z.1 : (ZMod q)ˣ))
          ((B : ZMod q) * CR * (treeLeafProduct n z.2 : (ZMod q)ˣ)) ≠ 0 from hv,
        ↓reduceIte, rationalTreeAmplitude, transferConjugations]
      rw [dite_eq_right (by rw [hrec]; exact hv), hV, ← hleft, ← hright]
      cases b <;> simp [V, v]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkSlotFieldBridge
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original labelled bulk slots produce the quartet leaf arrays -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem treeNaturalLift_iff_indexed {q : ℕ} (n : ℕ)
    (x : TreeLeafTuple ℕ n) (y : TreeLeafTuple (ZMod q)ˣ n) :
    TreeNaturalLift n x y ↔ ∀ j : TreeLeafIndex n,
      (treeLeafTupleEquiv ℕ n x j : ZMod q) = (treeLeafTupleEquiv (ZMod q)ˣ n y j : ZMod q) := by
  induction n with
  | zero =>
    constructor
    · intro h _; exact h
    · intro h; exact h ()
  | succ n ih =>
    constructor
    · rintro ⟨hL, hR⟩ (j | j)
      · exact (ih x.1 y.1).mp hL j
      · exact (ih x.2 y.2).mp hR j
    · intro h
      exact ⟨(ih x.1 y.1).mpr (fun j => h (.inl j)),
        (ih x.2 y.2).mpr (fun j => h (.inr j))⟩

theorem movingSlotValues_indexed {σ : Type*} (value : σ → ℕ) (n : ℕ)
    (s : TreeLeafTuple (List σ) n) (j : TreeLeafIndex n) :
    treeLeafTupleEquiv ℕ n (movingSlotValues value n s) j =
      MovingSlotReversal.naturalProduct value (treeLeafTupleEquiv (List σ) n s j) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases j with
    | inl j => exact ih s.1 j
    | inr j => exact ih s.2 j

theorem bulkSlotLeaves_naturalLift {σ : Type*} {q : ℕ} (value : σ → ℕ)
    (n m : ℕ) (slot : TreeLeafIndex n × Fin m → σ)
    (z : TreeLeafIndex n × Fin m → (ZMod q)ˣ)
    (hz : ∀ j, (value (slot j) : ZMod q) = (z j : ZMod q)) :
    TreeNaturalLift n (movingSlotValues value n (bulkSlotLeaves n m slot))
      ((treeLeafTupleEquiv (ZMod q)ˣ n).symm (bulkBlockProduct z)) := by
  rw [treeNaturalLift_iff_indexed]
  intro j
  rw [movingSlotValues_indexed]
  simp only [bulkSlotLeaves, Equiv.apply_symm_apply, MovingSlotReversal.naturalProduct,
    List.map_ofFn, List.prod_ofFn, Nat.cast_prod, bulkBlockProduct, Units.coe_prod]
  exact Finset.prod_congr rfl (fun i _ => hz (j, i))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkSpectatorNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absolute bounds under the original independent bulk-slot law -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem bulkBlockProductHom_surjective {L G : Type*} [Fintype L] [CommGroup G]
    {m : ℕ} (hm : 0 < m) : Function.Surjective (bulkBlockProductHom (L := L) (G := G) m) := by
  intro y
  let j₀ : Fin m := ⟨0, hm⟩
  refine ⟨fun s => if s.2 = j₀ then y s.1 else 1, ?_⟩
  ext l
  simp [bulkBlockProductHom, bulkBlockProduct]

/-- A nonempty set of independent slots gives a uniform product in each
leaf. This is the marginal used before exposing any frequency conditions. -/
theorem bulkBlockProduct_average {L G : Type*} [Fintype L] [CommGroup G] [Fintype G]
    {m : ℕ} (hm : 0 < m) (F : (L → G) → ℝ) :
    (Fintype.card (L × Fin m → G) : ℝ)⁻¹ * ∑ x : L × Fin m → G, F (bulkBlockProduct x) =
      (Fintype.card (L → G) : ℝ)⁻¹ * ∑ y, F y :=
  surjective_group_average (bulkBlockProductHom m) (bulkBlockProductHom_surjective hm) F

theorem SpectatorDiagram.bulk_l2_bound {p n m : ℕ} [Fact p.Prime]
    (d : SpectatorDiagram p n) (hp : 3 ≤ p) (hm : 0 < m)
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : ∑ x : ZMod p, ‖g x‖ ^ 2 ≤ (p : ℝ)) :
    (∑ x : TreeLeafIndex n × Fin m → (ZMod p)ˣ, ‖d.bulkValue g x‖ ^ 2) /
      (Fintype.card (TreeLeafIndex n × Fin m → (ZMod p)ˣ) : ℝ) ≤ (3 : ℝ) ^ (2 ^ n) := by
  change (∑ x, ‖indexedRationalAmplitude g d.D d.tree d.XL d.XR d.conjugations
    (bulkBlockProduct x)‖ ^ 2) / _ ≤ _
  have h := bulkBlockProduct_average (L := TreeLeafIndex n) (G := (ZMod p)ˣ) (m := m) hm
    (fun x => ‖indexedRationalAmplitude g d.D d.tree d.XL d.XR d.conjugations x‖ ^ 2)
  have hb := indexedRationalAmplitude_l2_bound hp g hg henergy d.D d.tree d.XL d.XR d.conjugations
  simp only [finite_univ_canonical, Fintype.card_eq_nat_card] at h hb ⊢
  rw [div_eq_mul_inv, mul_comm]
  calc
    _ = _ := h
    _ ≤ _ := by
      rw [mul_comm, ← div_eq_mul_inv]
      exact hb

theorem spectator_bulk_absolute_le {p n m : ℕ} [Fact p.Prime]
    (hp : 3 ≤ p) (hm : 0 < m) (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : ∑ x : ZMod p, ‖g x‖ ^ 2 ≤ (p : ℝ))
    (d₁ d₂ : SpectatorDiagram p n) (e : Equiv.Perm (TreeLeafIndex n × Fin m)) :
    (Fintype.card (TreeLeafIndex n × Fin m → (ZMod p)ˣ) : ℝ)⁻¹ *
      ∑ x, ‖d₁.bulkValue g x * conj (d₂.bulkValue g (x ∘ e.symm))‖ ≤ (3 : ℝ) ^ (2 ^ n) := by
  let E : (TreeLeafIndex n × Fin m → (ZMod p)ˣ) ≃
      (TreeLeafIndex n × Fin m → (ZMod p)ˣ) :=
    { toFun := fun x => x ∘ e.symm
      invFun := fun x => x ∘ e
      left_inv := by intro x; ext j; simp
      right_inv := by intro x; ext j; simp }
  have hsum := E.sum_comp (fun x => ‖d₂.bulkValue g x‖ ^ 2)
  have h₂ := d₂.bulk_l2_bound hp hm g hg henergy
  rw [← hsum] at h₂
  have h := uniform_absolute_pair_le
    (fun x => d₁.bulkValue g x) (fun x => d₂.bulkValue g (x ∘ e.symm))
    ((3 : ℝ) ^ (2 ^ n)) (d₁.bulk_l2_bound hp hm g hg henergy) h₂
  simpa only [div_eq_mul_inv, mul_comm, starRingEnd_apply] using h

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

theorem frequencySplitList_length (S : Finset ℤ) (n : ℕ) (x : FrequencyTree (S × S) n) :
    (frequencySplitList S n x).length = 2 ^ n - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [frequencySplitList, List.length_cons, List.length_append, ih]
    have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [pow_succ]
    omega

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

theorem pairedNodeFrequencies_moduli_bounds (S : Finset ℤ) (N : ℕ)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N) (root left right : S × S) :
    (pairedNodeFrequencies S root left right).1.reducedModulus ∈ Finset.Icc 1 N ∧
      (pairedNodeFrequencies S root left right).2.reducedModulus ∈ Finset.Icc 1 N := by
  constructor
  · apply reducedFrequency_mem
    exact Finset.mem_Icc.mpr ⟨Int.natAbs_pos.mpr (hS _ root.1.property).1,
      (hS _ root.1.property).2⟩
  · apply reducedFrequency_mem
    exact Finset.mem_Icc.mpr ⟨Int.natAbs_pos.mpr (hS _ root.2.property).1,
      (hS _ root.2.property).2⟩

theorem frequencySplitList_moduli_bounds (S : Finset ℤ) (N : ℕ)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N) (n : ℕ) (x : FrequencyTree (S × S) n)
    (f : NodeFrequencies × NodeFrequencies) (hf : f ∈ frequencySplitList S n x) :
    f.1.reducedModulus ∈ Finset.Icc 1 N ∧ f.2.reducedModulus ∈ Finset.Icc 1 N := by
  induction n with
  | zero => simp [frequencySplitList] at hf
  | succ n ih =>
    simp only [frequencySplitList, List.mem_cons, List.mem_append] at hf
    rcases hf with rfl | hf | hf
    · exact pairedNodeFrequencies_moduli_bounds S N hS _ _ _
    · exact ih _ hf
    · exact ih _ hf

theorem treeNodeFrequencies_divisor_bound (S : Finset ℤ) (N : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (hdiv : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D)
    (n : ℕ) (x : FrequencyTree (S × S) n) (j : ℕ) :
    (((treeNodeFrequencies S n x j).1.reducedModulus.lcm
      (treeNodeFrequencies S n x j).2.reducedModulus).divisors.card : ℝ) ≤ D := by
  by_cases hj : j < (frequencySplitList S n x).length
  · have hmem : treeNodeFrequencies S n x j ∈ frequencySplitList S n x := by
      rw [treeNodeFrequencies, List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    obtain ⟨ha, hb⟩ := frequencySplitList_moduli_bounds S N hS n x _ hmem
    apply hdiv
    · exact Nat.lcm_ne_zero (Nat.ne_of_gt (Finset.mem_Icc.mp ha).1)
        (Nat.ne_of_gt (Finset.mem_Icc.mp hb).1)
    · exact (Nat.lcm_le_mul (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp hb).1).trans (by
        rw [pow_two]
        exact Nat.mul_le_mul (Finset.mem_Icc.mp ha).2 (Finset.mem_Icc.mp hb).2)
  · rw [treeNodeFrequencies, List.getD_eq_default _ _ (by omega)]
    simpa [emptyNodeFrequencies, NodeFrequencies.reducedModulus, reducedFrequency] using hD

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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HistoryGiantSources
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two current giants refer only to previously reconstructed pivots -/

namespace Ostmann

open scoped Classical

theorem evolveGiantSources_eval (p : ℕ → ℤ) (d : ℕ)
    (g : HistoryGiantSource × HistoryGiantSource) (path : List Bool) :
    ((evolveGiantSources d g path).1.eval p, (evolveGiantSources d g path).2.eval p) =
      evolveGiantValues p d (g.1.eval p, g.2.eval p) path := by
  induction path generalizing d g with
  | nil => rfl
  | cons b path ih =>
    rw [evolveGiantSources, ih, evolveGiantValues]
    cases b <;> rfl

theorem HistoryGiantSource.coefficient (n : ℕ) (j : Fin (2 ^ n - 1))
    (p : Fin (2 ^ n - 1) → ℤ) (C : ℤ) (s : HistoryGiantSource)
    (hs : s.knownBefore (preorderNodePath n j).length) :
    ancestorCoefficient (C * s.fixedFactor)
      ((s.ancestorLevels (preorderNodePath n j) hs).image (ancestorNodeIndex n j)) p =
      C * s.nodeValue n j p hs := by
  cases s with
  | fixed c => simp [ancestorCoefficient, fixedFactor, ancestorLevels, nodeValue]
  | ancestor i => simp [ancestorCoefficient, fixedFactor, ancestorLevels, nodeValue]

theorem forwardTreeAncestorScheme_left (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (XL XR : ℤ) (CL CR : List Bool → ℤ) (p : Fin (2 ^ n - 1) → ℤ)
    (j : Fin (2 ^ n - 1)) :
    (forwardTreeAncestorScheme S n t XL XR CL CR).leftCoefficient p j =
      CR (preorderNodePath n j) *
        (historyGiantSources XL XR (preorderNodePath n j)).2.nodeValue n j p
          (historyGiantSources_known XL XR _).2 :=
  HistoryGiantSource.coefficient n j p _ _ _

theorem forwardTreeAncestorScheme_right (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (XL XR : ℤ) (CL CR : List Bool → ℤ) (p : Fin (2 ^ n - 1) → ℤ)
    (j : Fin (2 ^ n - 1)) :
    (forwardTreeAncestorScheme S n t XL XR CL CR).rightCoefficient p j =
      CL (preorderNodePath n j) *
        (historyGiantSources XL XR (preorderNodePath n j)).1.nodeValue n j p
          (historyGiantSources_known XL XR _).1 :=
  HistoryGiantSource.coefficient n j p _ _ _

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

/-- A bound uniform in the exposed product is also a bound for the
original independent leaf samples. -/
theorem treeLeaf_average_le {G : Type} [CommGroup G] [Fintype G]
    (n : ℕ) (F : (P : G) → TreeLeafFiber G n P → ℝ) (B : ℝ)
    (hF : ∀ P, (Fintype.card (TreeLeafFiber G n P) : ℝ)⁻¹ * ∑ x, F P x ≤ B) :
    (Fintype.card (TreeLeafTuple G n) : ℝ)⁻¹ *
        (∑ x : TreeLeafTuple G n, F (treeLeafProduct n x) ⟨x, rfl⟩) ≤ B := by
  rw [treeLeaf_average_by_product]
  calc
    _ ≤ (Fintype.card G : ℝ)⁻¹ * ∑ _P : G, B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun P _ => hF P) (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = B := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]

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

theorem SampledPivotHistory.matches_actual {n Q : ℕ} (a : SampledPivotHistory n Q)
    (j : ℕ) (hj : j ≤ 2 ^ n - 1) :
    a.matches (treeLeafProduct n a.residue) ((actualSplitValues n a.residue).take j).reverse := by
  constructor
  · rfl
  · simp only [List.length_reverse, List.length_take, actualSplitValues_length,
      min_eq_left hj]

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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingBulkPreorder
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The moving construction and the exposed bulk tree use one preorder -/

namespace Ostmann
open scoped Classical

theorem movingBulkProducts_get_path {σ : Type*} (value : σ → ℕ) (n : ℕ)
    (bulk : TreeLeafTuple (List σ) n) (path : List Bool) (hp : path.length < n) :
    movingBulkProducts value n bulk path =
      (actualChildProducts n (movingSlotValues value n bulk)).getD
        (nodePathIndex n path) (1, 1) := by
  induction n generalizing path with
  | zero => simp at hp
  | succ n ih =>
    cases path with
    | nil =>
      simp only [movingBulkProducts, nodePathIndex, movingSlotValues, actualChildProducts,
        List.getD_cons_zero, movingSlotValues_flatten]
    | cons b path =>
      have hp' : path.length < n := by simpa using hp
      have hidx := nodePathIndex_lt n path hp'
      have hpow := Nat.one_le_two_pow (n := n)
      cases b
      · simp only [movingBulkProducts, nodePathIndex, Bool.false_eq_true, ite_false, if_false,
          movingSlotValues, actualChildProducts]
        rw [show 1 + nodePathIndex n path = nodePathIndex n path + 1 by omega,
          List.getD_cons_succ, List.getD_append _ _ _ _ (by
            rw [actualChildProducts_length]; exact hidx)]
        exact ih bulk.1 path hp'
      · simp only [movingBulkProducts, nodePathIndex, ite_true, if_true,
          movingSlotValues, actualChildProducts]
        rw [show 2 ^ n + nodePathIndex n path = (2 ^ n - 1 + nodePathIndex n path) + 1 by omega,
          List.getD_cons_succ, List.getD_append_right _ _ _ _ (by
            rw [actualChildProducts_length]; omega), actualChildProducts_length]
        rw [show 2 ^ n - 1 + nodePathIndex n path - (2 ^ n - 1) = nodePathIndex n path by omega]
        exact ih bulk.2 path hp'

theorem movingBulkProducts_preorder {σ : Type*} (value : σ → ℕ) (n : ℕ)
    (bulk : TreeLeafTuple (List σ) n) (j : Fin (2 ^ n - 1)) :
    movingBulkProducts value n bulk (preorderNodePath n j) =
      (actualChildProducts n (movingSlotValues value n bulk)).getD j.val (1, 1) := by
  rw [movingBulkProducts_get_path value n bulk _ (preorderNodePath_length n j),
    nodePathIndex_preorderNodePath]

theorem treeLeafProduct_intCast (n : ℕ) (x : TreeLeafTuple ℕ n) :
    treeLeafProduct n (treeLeafMap (fun a : ℕ => (a : ℤ)) n x) =
      ((treeLeafProduct n x : ℕ) : ℤ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [treeLeafProduct, treeLeafMap, ih, Nat.cast_mul]

theorem actualChildProducts_intCast (n : ℕ) (x : TreeLeafTuple ℕ n) :
    actualChildProducts n (treeLeafMap (fun a : ℕ => (a : ℤ)) n x) =
      (actualChildProducts n x).map (fun a => ((a.1 : ℤ), (a.2 : ℤ))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [treeLeafMap, actualChildProducts, treeLeafProduct_intCast, ih,
      List.map_cons, List.map_append]

theorem movingBulkProducts_preorder_intCast {σ : Type*} (value : σ → ℕ) (n : ℕ)
    (bulk : TreeLeafTuple (List σ) n) (j : Fin (2 ^ n - 1)) :
    let b := movingBulkProducts value n bulk (preorderNodePath n j)
    ((b.1 : ℤ), (b.2 : ℤ)) =
      (actualChildProducts n (treeLeafMap (fun a : ℕ => (a : ℤ)) n
        (movingSlotValues value n bulk))).getD j.val (1, 1) := by
  rw [actualChildProducts_intCast, movingBulkProducts_preorder]
  exact (List.getD_map _ (1, 1) (fun a : ℕ × ℕ => ((a.1 : ℤ), (a.2 : ℤ)))).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingNodeUnits
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coefficient units forced by the original local support masks -/

namespace Ostmann
open scoped Classical

theorem MovingSlotData.frequency_dvd_product {σ : Type*} {n : ℕ} (T : MovingSlotData σ n) :
    T.frequency ∣ T.frequencyProduct := by
  cases T with
  | leaf => exact dvd_refl _
  | node => exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ModularCompensatedPrecision
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prefix precision after retaining only the frequency congruences

The frequency model in the arithmetic replacement divides by compensation
factors modulo the remaining power. Its equations are congruences, with one
power lost at each branch level.
-/

namespace Ostmann
open scoped BigOperators

theorem PivotDependencyScheme.modular_compensated_pivot_prefix_precision {N : ℕ} (D : PivotDependencyScheme N)
    (R k J : ℕ) (U : Fin N → ℤ) (hU : ∀ j, IsCoprime (U j) (R : ℤ)) (hdepth : ∀ j, D.depth j ≤ k)
    (hs : ∀ j, (D.frequencies j).root ≠ 0)
    (hsR : ∀ j, (D.frequencies j).root.natAbs ∣ R)
    (L₁ R₁ p₁ L₂ R₂ p₂ : Fin N → ℤ)
    (heq₁ : D.modularCompensatedEquations R k U L₁ R₁ p₁) (heq₂ : D.modularCompensatedEquations R k U L₂ R₂ p₂)
    (hL : ∀ j, j.val < J → L₁ j ≡ L₂ j [ZMOD (R : ℤ) ^ (k + 2)])
    (hR : ∀ j, j.val < J → R₁ j ≡ R₂ j [ZMOD (R : ℤ) ^ (k + 2)]) :
    ∀ j, j.val < J → p₁ j ≡ p₂ j [ZMOD (R : ℤ) ^ (k - D.depth j)] := by
  intro j hj
  have hall : ∀ a : ℕ, ∀ j : Fin N, j.val = a → j.val < J →
      p₁ j ≡ p₂ j [ZMOD (R : ℤ) ^ (k - D.depth j)] := by
    intro a
    induction a using Nat.strong_induction_on with
    | h a ih =>
      intro j hja hj
      have hcoeff (C : ℤ) (A : Finset (Fin N))
          (hA : ∀ i ∈ A, i.val < j.val ∧ D.depth i < D.depth j) :
          ancestorCoefficient C A p₁ ≡ ancestorCoefficient C A p₂
            [ZMOD (R : ℤ) ^ (k + 1 - D.depth j)] := by
        apply ancestorCoefficient_modEq
        intro i hi
        obtain ⟨hij, hdij⟩ := hA i hi
        have hp := ih i.val (by omega) i rfl (by omega)
        exact hp.of_dvd (pow_dvd_pow (R : ℤ) (by have := hdepth i; have := hdepth j; omega))
      have hcL := hcoeff (D.fixedLeft j) (D.ancestorsLeft j) (D.earlierLeft j)
      have hcR := hcoeff (D.fixedRight j) (D.ancestorsRight j) (D.earlierRight j)
      have hlj := (hL j hj).of_dvd (pow_dvd_pow (R : ℤ) (by omega : k + 1 - D.depth j ≤ k + 2))
      have hrj := (hR j hj).of_dvd (pow_dvd_pow (R : ℤ) (by omega : k + 1 - D.depth j ≤ k + 2))
      have hnum := ((hcL.mul_left (D.frequencies j).left).mul hrj).sub
        ((hcR.mul_left (D.frequencies j).right).mul hlj)
      have hroot : (D.frequencies j).root ∣ (R : ℤ) :=
        Int.natAbs_dvd.mp (Int.natCast_dvd_natCast.mpr (hsR j))
      have hproducts := (heq₁ j).symm.trans (hnum.trans (heq₂ j))
      have hx := reversal_residue_precision (R : ℤ) (D.frequencies j).root (U j) (U j)
        ((D.frequencies j).root * U j * p₁ j)
        ((D.frequencies j).root * U j * p₂ j)
        (p₁ j) (p₂ j) (k - D.depth j) (hs j) hroot (hU j) rfl rfl
        (by
          have he : k - D.depth j + 1 = k + 1 - D.depth j := by
            have := hdepth j
            omega
          rw [he]
          exact hproducts) (.refl (U j))
      exact hx
  exact hall j.val j rfl hj

/-- Before the current split is exposed, both coefficients are already
known modulo its root frequency. This is the measurability step needed by
the sequential uniform-root count. -/
theorem PivotDependencyScheme.modular_compensated_coefficients_prefix_precision {N : ℕ}
    (D : PivotDependencyScheme N) (R k : ℕ) (U : Fin N → ℤ)
    (hU : ∀ i, IsCoprime (U i) (R : ℤ)) (j : Fin N)
    (hdepth : ∀ i, D.depth i ≤ k) (hs : ∀ i, (D.frequencies i).root ≠ 0)
    (hsR : ∀ i, (D.frequencies i).root.natAbs ∣ R)
    (L₁ R₁ p₁ L₂ R₂ p₂ : Fin N → ℤ)
    (heq₁ : D.modularCompensatedEquations R k U L₁ R₁ p₁) (heq₂ : D.modularCompensatedEquations R k U L₂ R₂ p₂)
    (hL : ∀ i, i.val < j.val → L₁ i ≡ L₂ i [ZMOD (R : ℤ) ^ (k + 2)])
    (hR : ∀ i, i.val < j.val → R₁ i ≡ R₂ i [ZMOD (R : ℤ) ^ (k + 2)]) :
    D.leftCoefficient p₁ j ≡ D.leftCoefficient p₂ j [ZMOD (D.frequencies j).root.natAbs] ∧
      D.rightCoefficient p₁ j ≡ D.rightCoefficient p₂ j [ZMOD (D.frequencies j).root.natAbs] := by
  have hp := D.modular_compensated_pivot_prefix_precision R k j.val U hU hdepth hs hsR L₁ R₁ p₁ L₂ R₂ p₂ heq₁ heq₂ hL hR
  have hcoeff (C : ℤ) (A : Finset (Fin N))
      (hA : ∀ i ∈ A, i.val < j.val ∧ D.depth i < D.depth j) :
      ancestorCoefficient C A p₁ ≡ ancestorCoefficient C A p₂
        [ZMOD (D.frequencies j).root.natAbs] := by
    apply ancestorCoefficient_modEq
    intro i hi
    obtain ⟨hij, hdij⟩ := hA i hi
    apply (hp i hij).of_dvd
    exact (Int.natCast_dvd_natCast.mpr (hsR j)).trans
      (dvd_pow_self (R : ℤ) (by have := hdepth j; omega))
  exact ⟨hcoeff _ _ (D.earlierLeft j), hcoeff _ _ (D.earlierRight j)⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ModularAdaptiveCoefficients
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Adaptive coefficients for the frequency-only arithmetic model -/

namespace Ostmann

open scoped Classical

theorem modularAdaptiveCoefficients_witness (n R k : ℕ)
    (D : PivotDependencyScheme (2 ^ n - 1)) (U : Fin (2 ^ n - 1) → ℤ)
    (total : (ZMod (R ^ (k + 2)))ˣ) (past : List (ZMod (R ^ (k + 2)))ˣ)
    (hj : past.length < 2 ^ n - 1)
    (hex : ∃ a : SampledPivotHistory n (R ^ (k + 2)), a.modularValid D R k U ∧ a.matches total past) :
    ∃ a : SampledPivotHistory n (R ^ (k + 2)), a.modularValid D R k U ∧ a.matches total past ∧
      modularAdaptiveCoefficients n R k D U total past =
        ((D.leftCoefficient a.pivots ⟨past.length, hj⟩ : ZMod (R ^ (k + 2))),
          (D.rightCoefficient a.pivots ⟨past.length, hj⟩ : ZMod (R ^ (k + 2)))) := by
  refine ⟨Classical.choose hex, (Classical.choose_spec hex).1, (Classical.choose_spec hex).2, ?_⟩
  simp only [modularAdaptiveCoefficients, dite_eq_left hj, dite_eq_left hex]

/-- The chosen completion gives the actual coefficients modulo the current
root frequency, even though its integer pivots may differ. -/
theorem modularAdaptiveCoefficients_reduce (n R k : ℕ)
    (D : PivotDependencyScheme (2 ^ n - 1)) (U : Fin (2 ^ n - 1) → ℤ)
    (hU : ∀ i, IsCoprime (U i) (R : ℤ))
    (hdepth : ∀ i, D.depth i ≤ k) (hs : ∀ i, (D.frequencies i).root ≠ 0)
    (hsR : ∀ i, (D.frequencies i).root.natAbs ∣ R)
    (a : SampledPivotHistory n (R ^ (k + 2))) (ha : a.modularValid D R k U)
    (total : (ZMod (R ^ (k + 2)))ˣ) (past : List (ZMod (R ^ (k + 2)))ˣ)
    (hm : a.matches total past) (hj : past.length < 2 ^ n - 1) :
    let j : Fin (2 ^ n - 1) := ⟨past.length, hj⟩
    let hd : (D.frequencies j).root.natAbs ∣ R ^ (k + 2) :=
      (hsR j).trans (dvd_pow_self R (by omega))
    ZMod.castHom hd (ZMod (D.frequencies j).root.natAbs)
        (modularAdaptiveCoefficients n R k D U total past).1 =
        D.leftCoefficient a.pivots j ∧
      ZMod.castHom hd (ZMod (D.frequencies j).root.natAbs)
        (modularAdaptiveCoefficients n R k D U total past).2 =
        D.rightCoefficient a.pivots j := by
  dsimp only
  obtain ⟨b, hb, hbm, hcoeff⟩ := modularAdaptiveCoefficients_witness n R k D U total past hj
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
  have h := D.modular_compensated_coefficients_prefix_precision R k U hU ⟨past.length, hj⟩ hdepth hs hsR
    b.leftProduct b.rightProduct b.pivots a.leftProduct a.rightProduct a.pivots hb.1 ha.1 hL hR
  rw [hcoeff]
  simp only [map_intCast]
  exact ⟨(ZMod.intCast_eq_intCast_iff _ _ _).mpr h.1,
    (ZMod.intCast_eq_intCast_iff _ _ _).mpr h.2⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ModularAdaptiveSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frequency-congruence histories pass the adaptive split tests -/

namespace Ostmann

open scoped Classical

theorem modularAdaptiveData_frequencies (n R k : ℕ)
    (D : PivotDependencyScheme (2 ^ n - 1)) (U : Fin (2 ^ n - 1) → ℤ)
    (hs : ∀ i, (D.frequencies i).root ≠ 0)
    (hsR : ∀ i, (D.frequencies i).root.natAbs ∣ R)
    (total : (ZMod (R ^ (k + 2)))ˣ) (past : List (ZMod (R ^ (k + 2)))ˣ)
    (hj : past.length < 2 ^ n - 1) (d : ArithmeticSplitData (R ^ (k + 2)))
    (hd : modularAdaptiveData n R k D U hs hsR total past = some d) :
    d.hasFrequencies (D.frequencies ⟨past.length, hj⟩) := by
  rw [modularAdaptiveData, dite_eq_left hj] at hd
  exact ArithmeticResidueSplit.toData_frequencies _ _ hd

/-- A valid actual history passes every test. The coefficients in that test
were constructed using only the root product and the preceding split prefix. -/
theorem modularAdaptiveData_actual_test (n R k : ℕ)
    (D : PivotDependencyScheme (2 ^ n - 1)) (U : Fin (2 ^ n - 1) → ℤ)
    (hU : ∀ i, IsCoprime (U i) (R : ℤ))
    (hdepth : ∀ i, D.depth i ≤ k) (hs : ∀ i, (D.frequencies i).root ≠ 0)
    (hsR : ∀ i, (D.frequencies i).root.natAbs ∣ R)
    (a : SampledPivotHistory n (R ^ (k + 2))) (ha : a.modularValid D R k U)
    (j : ℕ) (hj : j < 2 ^ n - 1) :
    singleArithmeticSplitTest
      (modularAdaptiveData n R k D U hs hsR (treeLeafProduct n a.residue)
        ((actualSplitValues n a.residue).take j).reverse)
      ((actualSplitValues n a.residue).getD j 1) := by
  let total := treeLeafProduct n a.residue
  let past := ((actualSplitValues n a.residue).take j).reverse
  have hlen : past.length = j := by
    simp only [past, List.length_reverse, List.length_take, actualSplitValues_length,
      min_eq_left (Nat.le_of_lt hj)]
  have hj' : past.length < 2 ^ n - 1 := by omega
  let d := modularAdaptiveResidueSplit n R k D U hs hsR total past hj'
  change singleArithmeticSplitTest (modularAdaptiveData n R k D U hs hsR total past) _
  rw [modularAdaptiveData, dite_eq_left hj', singleArithmeticSplitTest_toData]
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
  have hcoeff := modularAdaptiveCoefficients_reduce n R k D U hU hdepth hs hsR a ha
    total past (a.matches_actual j (Nat.le_of_lt hj)) hj'
  have hci := treeIntegerResidues_child (R ^ (k + 2)) n a.bulk a.residue a.compatible j
  have hL : (c.1 : ZMod (R ^ (k + 2))) = a.leftProduct i := by
    simpa only [c, SampledPivotHistory.leftProduct, i, hlen] using hci.1
  have hR : (c.2 : ZMod (R ^ (k + 2))) = a.rightProduct i := by
    simpa only [c, SampledPivotHistory.rightProduct, i, hlen] using hci.2
  let N := (D.frequencies i).left * D.leftCoefficient a.pivots i * a.rightProduct i -
    (D.frequencies i).right * D.rightCoefficient a.pivots i * a.leftProduct i
  have hd : (D.frequencies i).root ∣ N := by
    have hm := (ha.1 i).of_dvd
      ((Int.natAbs_dvd.mp (Int.natCast_dvd_natCast.mpr (hsR i))).trans
        (dvd_pow_self (R : ℤ) (by have := hdepth i; omega)))
    exact hm.dvd_iff.mpr (dvd_mul_right _ _ |>.trans (dvd_mul_right _ _))
  apply d.support_of_reduced_integer_data _
    (D.leftCoefficient a.pivots i) (D.rightCoefficient a.pivots i)
    (a.leftProduct i) (a.rightProduct i) (N / (D.frequencies i).root)
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
  · exact (Int.mul_ediv_cancel' hd).symm

/-- The entire original residue tuple remains in the arithmetic support. -/
theorem modularAdaptiveData_actual_support (n R k : ℕ) [NeZero (R ^ (k + 2))]
    (D : PivotDependencyScheme (2 ^ n - 1)) (U : Fin (2 ^ n - 1) → ℤ)
    (hU : ∀ i, IsCoprime (U i) (R : ℤ))
    (hdepth : ∀ i, D.depth i ≤ k) (hs : ∀ i, (D.frequencies i).root ≠ 0)
    (hsR : ∀ i, (D.frequencies i).root.natAbs ∣ R)
    (a : SampledPivotHistory n (R ^ (k + 2))) (ha : a.modularValid D R k U) :
    singleArithmeticLeafSupport n (modularAdaptiveData n R k D U hs hsR) a.residue = 1 := by
  apply singleArithmeticLeafSupport_eq_one_of_actual_tests
  exact modularAdaptiveData_actual_test n R k D U hU hdepth hs hsR a ha

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrequencyModelPaths
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Paths in the frequency-only arithmetic recursion

These states follow `movingFrequencyGate`, whose pivots invert the fixed
compensation modulo a power of the frequency modulus.
-/

namespace Ostmann
open scoped Classical

theorem frequencyModelAtPath_level {σ : Type*} (value : σ → ℕ) (R : ℤ)
    (n : ℕ) (T : MovingSlotData σ n) (x y : ℤ) (path : List Bool) (hp : path.length < n) :
    (frequencyModelAtPath value R n T x y path).level + path.length = n := by
  induction n generalizing x y path with
  | zero => simp at hp
  | succ n ih =>
    cases T with
    | node s CL CR U l r =>
      cases path with
      | nil => rfl
      | cons b path =>
        have hp' : path.length < n := by simpa using hp
        cases b <;> simp only [frequencyModelAtPath, Bool.false_eq_true, ite_false, if_false, ite_true, if_true,
          List.length_cons]
        · have := ih l ((MovingSlotData.step s CL CR U l r false).frequencyPivot value R (n + 1) x y) x path hp'; omega
        · have := ih r ((MovingSlotData.step s CL CR U l r false).frequencyPivot value R (n + 1) x y) y path hp'; omega

theorem frequencyModelAtPath_gate {σ : Type*} (value : σ → ℕ) (R : ℤ)
    (n : ℕ) (T : MovingSlotData σ n) (x y : ℤ) (path : List Bool)
    (h : movingFrequencyGate value R T x y) :
    let z := frequencyModelAtPath value R n T x y path
    movingFrequencyGate value R z.data z.leftGiant z.rightGiant := by
  induction n generalizing x y path with
  | zero => cases T; exact h
  | succ n ih =>
    cases T with
    | node s CL CR U l r =>
      cases path with
      | nil => exact h
      | cons b path =>
        cases b
        · exact ih l _ x path h.2.2.1
        · exact ih r _ y path h.2.2.2

theorem frequencyModelAtPath_frequencies {σ : Type*} (value : σ → ℕ) (R : ℤ)
    (S : Finset ℤ) (n : ℕ) (T : MovingSlotData σ n) (t : FrequencyTree S n)
    (hT : T.Follows (frequencyTreeMap Subtype.val n t))
    (x y : ℤ) (path : List Bool) (hp : path.length < n) :
    (frequencyModelAtPath value R n T x y path).frequencies =
      singleTreeNodeFrequencies S n t (nodePathIndex n path) := by
  induction n generalizing x y path with
  | zero => simp at hp
  | succ n ih =>
    cases T with
    | node s CL CR U l r =>
      cases path with
      | nil =>
        change NodeFrequencies.mk s l.frequency r.frequency = _
        rw [hT.1, hT.2.1.root, hT.2.2.root]
        simp only [frequencyTreeMap, frequencyRoot_map, nodePathIndex,
          singleTreeNodeFrequencies, singleFrequencySplitList, List.getD_cons_zero]
      | cons b path =>
        have hp' : path.length < n := by simpa using hp
        have hidx := nodePathIndex_lt n path hp'
        have hlen := singleFrequencySplitList_length S n t.2.1
        cases b
        · change (frequencyModelAtPath value R n l _ x path).frequencies = _
          rw [ih l t.2.1 hT.2.1 _ x path hp']
          unfold singleTreeNodeFrequencies
          simp only [nodePathIndex, Bool.false_eq_true, ite_false, if_false, singleFrequencySplitList]
          rw [show 1 + nodePathIndex n path = nodePathIndex n path + 1 by omega,
            List.getD_cons_succ, List.getD_append _ _ _ _ (by simpa only [hlen] using hidx)]
        · change (frequencyModelAtPath value R n r _ y path).frequencies = _
          rw [ih r t.2.2 hT.2.2 _ y path hp']
          unfold singleTreeNodeFrequencies
          simp only [nodePathIndex, ite_true, if_true, singleFrequencySplitList]
          rw [show 2 ^ n + nodePathIndex n path = (2 ^ n - 1 + nodePathIndex n path) + 1 by
              have := Nat.one_le_two_pow (n := n); omega,
            List.getD_cons_succ, List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen]
          rw [show 2 ^ n - 1 + nodePathIndex n path - (2 ^ n - 1) = nodePathIndex n path by omega]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrequencyModelCoefficients
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed factors and ancestor coefficients of the frequency model -/

namespace Ostmann
open scoped Classical

theorem frequencyModelAtPath_giants {σ : Type*} (value : σ → ℕ) (R : ℤ)
    (n : ℕ) (T : MovingSlotData σ n) (x y : ℤ) (path : List Bool) (hp : path.length < n)
    (d : ℕ) (p : ℕ → ℤ)
    (hanc : ∀ k < path.length, p (d + k) =
      (frequencyModelAtPath value R n T x y (path.take k)).pivot value R) :
    let z := frequencyModelAtPath value R n T x y path
    (z.leftGiant, z.rightGiant) = evolveGiantValues p d (x, y) path := by
  induction n generalizing x y path d with
  | zero => simp at hp
  | succ n ih =>
    cases T with
    | node s CL CR U l r =>
      cases path with
      | nil => rfl
      | cons b path =>
        have hp' : path.length < n := by simpa using hp
        let q := (MovingSlotData.step s CL CR U l r false).frequencyPivot value R (n + 1) x y
        have hq : p d = q := by
          simpa only [Nat.add_zero, List.take_zero, frequencyModelAtPath,
            FrequencyModelState.pivot] using hanc 0 (by simp)
        cases b <;> simp only [frequencyModelAtPath, Bool.false_eq_true, ite_false, if_false, ite_true, if_true]
        · rw [evolveGiantValues, hq]
          apply ih l q x path hp' (d + 1)
          intro k hk
          have h := hanc (k + 1) (by simpa using Nat.add_lt_add_right hk 1)
          simpa only [Nat.add_assoc, Nat.add_comm 1 k, List.take_succ_cons,
            frequencyModelAtPath, Bool.false_eq_true, ite_false, if_false] using h
        · rw [evolveGiantValues, hq]
          apply ih r q y path hp' (d + 1)
          intro k hk
          have h := hanc (k + 1) (by simpa using Nat.add_lt_add_right hk 1)
          simpa only [Nat.add_assoc, Nat.add_comm 1 k, List.take_succ_cons,
            frequencyModelAtPath, ite_true, if_true] using h

theorem frequencyModelPivots_sources {σ : Type*} (value : σ → ℕ) (R : ℤ)
    (n : ℕ) (T : MovingSlotData σ n) (x y : ℤ) (j : Fin (2 ^ n - 1)) :
    let p := frequencyModelPivots value R n T x y
    let z := frequencyModelAtPath value R n T x y (preorderNodePath n j)
    (z.leftGiant, z.rightGiant) =
      ((historyGiantSources x y (preorderNodePath n j)).1.nodeValue n j p
        (historyGiantSources_known x y _).1,
       (historyGiantSources x y (preorderNodePath n j)).2.nodeValue n j p
        (historyGiantSources_known x y _).2) := by
  dsimp only
  let p := frequencyModelPivots value R n T x y
  let q := fun k => if hk : k < (preorderNodePath n j).length then
    p (ancestorNodeIndex n j ⟨k, hk⟩) else 0
  have h := frequencyModelAtPath_giants value R n T x y (preorderNodePath n j)
    (preorderNodePath_length n j) 0 q (by
      intro k hk
      simp only [Nat.zero_add, q, dite_eq_left hk, p, frequencyModelPivots, ancestorNodeIndex_path])
  have heval := evolveGiantSources_eval q 0 (.fixed x, .fixed y) (preorderNodePath n j)
  change _ = evolveGiantValues q 0 (x, y) (preorderNodePath n j) at heval
  rw [← heval] at h
  change _ = ((historyGiantSources x y (preorderNodePath n j)).1.eval q,
    (historyGiantSources x y (preorderNodePath n j)).2.eval q) at h
  rw [h]
  have he (s : HistoryGiantSource) (hs : s.knownBefore (preorderNodePath n j).length) :
      s.eval q = s.nodeValue n j p hs := by
    cases s with
    | fixed c => rfl
    | ancestor i =>
      change (if hi : i < (preorderNodePath n j).length then
        p (ancestorNodeIndex n j ⟨i, hi⟩) else 0) = _
      change i < (preorderNodePath n j).length at hs
      rw [dite_eq_left hs]
      rfl
  exact Prod.ext (he _ (historyGiantSources_known x y _).1)
    (he _ (historyGiantSources_known x y _).2)

theorem frequencyModelAtPath_products {σ : Type*} (value : σ → ℕ) (R : ℤ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (a : MovingSampleSlots σ n) (x y : ℤ) (path : List Bool) (hp : path.length < n) :
    let z := frequencyModelAtPath value R n (buildMovingSlotData n t small bulk a) x y path
    let c := movingFrameConstants value n small a path
    let b := movingBulkProducts value n bulk path
    z.compensation value = c.compensation ∧
      z.leftProduct value = z.leftGiant * c.leftSmall * b.1 ∧
      z.rightProduct value = z.rightGiant * c.rightSmall * b.2 := by
  induction n generalizing x y path with
  | zero => simp at hp
  | succ n ih =>
    cases a with
    | node a l r =>
      cases path with
      | nil =>
        simp only [frequencyModelAtPath, buildMovingSlotData, movingFrameConstants,
          movingBulkProducts, FrequencyModelState.compensation, FrequencyModelState.leftProduct,
          FrequencyModelState.rightProduct, movingNaturalProduct_append, Nat.cast_mul,
          mul_assoc, and_self]
      | cons b path =>
        have hp' : path.length < n := by simpa using hp
        cases b
        · exact ih t.2.1 (appendMovingSlotLeaves n (movingCompensationSlots n a) small.1)
            bulk.1 l _ x path hp'
        · exact ih t.2.2 (appendMovingSlotLeaves n (movingCompensationSlots n a) small.2)
            bulk.2 r _ y path hp'

theorem frequencyModelNode_products {σ : Type*} (value : σ → ℕ) (R : ℤ)
    (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (small bulk : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n)
    (x y : ℤ) (j : Fin (2 ^ n - 1)) :
    let tz := frequencyTreeMap Subtype.val n t
    let T := buildMovingSlotData n tz small bulk a
    let p := frequencyModelPivots value R n T x y
    let D := frequencyModelAncestorScheme value S n t small a x y
    let z := frequencyModelAtPath value R n T x y (preorderNodePath n j)
    let b := (actualChildProducts n (treeLeafMap (fun q : ℕ => (q : ℤ)) n
      (movingSlotValues value n bulk))).getD j.val (1, 1)
    z.compensation value = movingSampleCompensation value n small a j ∧
      z.leftProduct value = D.rightCoefficient p j * b.1 ∧
      z.rightProduct value = D.leftCoefficient p j * b.2 := by
  dsimp only
  have hf := frequencyModelAtPath_products value R n (frequencyTreeMap Subtype.val n t)
    small bulk a x y (preorderNodePath n j) (preorderNodePath_length n j)
  have hg := frequencyModelPivots_sources value R n
    (buildMovingSlotData n (frequencyTreeMap Subtype.val n t) small bulk a) x y j
  have hb := movingBulkProducts_preorder_intCast value n bulk j
  have hl := congrArg Prod.fst hg
  have hr := congrArg Prod.snd hg
  have hbl := congrArg Prod.fst hb
  have hbr := congrArg Prod.snd hb
  dsimp only at hl hr hbl hbr
  refine ⟨hf.1, ?_, ?_⟩
  · rw [hf.2.1]
    change _ = (forwardTreeAncestorScheme S n t x y _ _).rightCoefficient _ j * _
    rw [forwardTreeAncestorScheme_right, ← hl, ← hbl]
    ring
  · rw [hf.2.2]
    change _ = (forwardTreeAncestorScheme S n t x y _ _).leftCoefficient _ j * _
    rw [forwardTreeAncestorScheme_left, ← hr, ← hbr]
    ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrequencyModelValidity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original frequency gate supplies modular adaptive validity -/

namespace Ostmann
open scoped Classical

theorem FrequencyModelState.compensation_coprime {σ : Type*} (value : σ → ℕ) (R : ℤ)
    (hsmall : ∀ i, IsCoprime (value i : ℤ) R) (z : FrequencyModelState σ) :
    IsCoprime (z.compensation value) R := by
  rcases z with ⟨n, T, x, y⟩
  cases T with
  | leaf => exact isCoprime_one_left
  | node s CL CR U l r => exact movingNaturalProduct_coprime value U R (fun i _ => hsmall i)

theorem FrequencyModelState.relation {σ : Type*} (value : σ → ℕ) (R : ℤ)
    (z : FrequencyModelState σ)
    (hU : IsCoprime (z.compensation value) R)
    (hg : movingFrequencyGate value R z.data z.leftGiant z.rightGiant) :
    z.frequencies.left * z.rightProduct value - z.frequencies.right * z.leftProduct value ≡
      z.frequencies.root * z.compensation value * z.pivot value R [ZMOD R ^ z.level] := by
  rcases z with ⟨n, T, x, y⟩
  cases T with
  | leaf => simp [FrequencyModelState.frequencies, FrequencyModelState.leftProduct,
      FrequencyModelState.rightProduct, FrequencyModelState.pivot]
  | @node n s CL CR U l r =>
    let step := MovingSlotData.step s CL CR U l r false
    let N := step.signedNumerator value x y
    let u : ℤ := MovingSlotReversal.naturalProduct value U
    have hd : s ∣ N := hg.2.1
    have hu : IsCoprime u R := hU
    have hinv := coprime_bezout_inverse_modEq u R hu (n + 1)
    change N ≡ s * u * ((N / s) * Int.gcdA u (R ^ (n + 1))) [ZMOD R ^ (n + 1)]
    calc
      N = s * (N / s) := (Int.mul_ediv_cancel' hd).symm
      _ ≡ (s * (N / s)) * (u * Int.gcdA u (R ^ (n + 1))) [ZMOD R ^ (n + 1)] := by
        simpa only [mul_one] using hinv.symm.mul_left (s * (N / s))
      _ = _ := by ring

theorem FrequencyModelState.products_units {σ : Type*} (value : σ → ℕ)
    (R : ℤ) (z : FrequencyModelState σ)
    (hsmall : ∀ i, IsCoprime (value i : ℤ) z.frequencies.root)
    (hg : movingFrequencyGate value R z.data z.leftGiant z.rightGiant) :
    IsCoprime (z.leftProduct value) z.frequencies.root ∧
      IsCoprime (z.rightProduct value) z.frequencies.root := by
  have hlocal : movingFrequencyLocalUnits z.data z.leftGiant z.rightGiant := by
    rcases z with ⟨n, T, x, y⟩
    cases T
    · exact hg
    · exact hg.1
  rcases z with ⟨n, T, x, y⟩
  cases T with
  | leaf => exact ⟨isCoprime_one_left, isCoprime_one_left⟩
  | node s CL CR U l r =>
    have hl := hlocal.1.of_isCoprime_of_dvd_right
      (MovingSlotData.frequency_dvd_product (.node s CL CR U l r))
    have hr := hlocal.2.of_isCoprime_of_dvd_right
      (MovingSlotData.frequency_dvd_product (.node s CL CR U l r))
    exact ⟨hl.mul_left (movingNaturalProduct_coprime value CL s (fun i _ => hsmall i)),
      hr.mul_left (movingNaturalProduct_coprime value CR s (fun i _ => hsmall i))⟩

theorem frequencyModel_modularEquations {σ : Type*} (value : σ → ℕ) (R : ℕ)
    (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (small bulk : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) (x y : ℤ)
    (hsmall : ∀ i, IsCoprime (value i : ℤ) (R : ℤ))
    (hg : movingFrequencyGate value R
      (buildMovingSlotData n (frequencyTreeMap Subtype.val n t) small bulk a) x y) :
    let T := buildMovingSlotData n (frequencyTreeMap Subtype.val n t) small bulk a
    let b := actualChildProducts n (treeLeafMap (fun q : ℕ => (q : ℤ)) n
      (movingSlotValues value n bulk))
    (frequencyModelAncestorScheme value S n t small a x y).modularCompensatedEquations R (n - 1)
      (movingSampleCompensation value n small a)
      (fun j => (b.getD j.val (1, 1)).1) (fun j => (b.getD j.val (1, 1)).2)
      (frequencyModelPivots value R n T x y) := by
  dsimp only
  intro j
  let T := buildMovingSlotData n (frequencyTreeMap Subtype.val n t) small bulk a
  let z := frequencyModelAtPath value R n T x y (preorderNodePath n j)
  have hgate := frequencyModelAtPath_gate value R n T x y (preorderNodePath n j) hg
  have he := z.relation value R (z.compensation_coprime value R hsmall) hgate
  have hp := frequencyModelNode_products value R S n t small bulk a x y j
  have hf := frequencyModelAtPath_frequencies value R S n T t
    (buildMovingSlotData_follows n _ small bulk a) x y (preorderNodePath n j)
    (preorderNodePath_length n j)
  have hl := frequencyModelAtPath_level value R n T x y (preorderNodePath n j)
    (preorderNodePath_length n j)
  rw [nodePathIndex_preorderNodePath] at hf
  change z.level + (preorderNodePath n j).length = n at hl
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) (preorderNodePath_length n j)
  have helevel : z.level = n - 1 + 1 - (preorderNodePath n j).length := by omega
  change z.frequencies.left * z.rightProduct value - z.frequencies.right * z.leftProduct value ≡
    z.frequencies.root * z.compensation value * z.pivot value R [ZMOD (R : ℤ) ^ z.level] at he
  rw [hp.1, hp.2.1, hp.2.2, hf, helevel] at he
  simpa only [frequencyModelAncestorScheme, forwardTreeAncestorScheme, treeAncestorScheme,
    frequencyModelPivots, mul_assoc] using he

/-- Unit factors are retained from the exact local frequency gates. -/
theorem frequencyModel_coefficient_units {σ : Type*} (value : σ → ℕ) (R : ℕ)
    (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (small bulk : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) (x y : ℤ)
    (hsmall : ∀ i, IsCoprime (value i : ℤ) (R : ℤ))
    (hR : ∀ j : Fin (2 ^ n - 1), (singleTreeNodeFrequencies S n t j.val).root.natAbs ∣ R)
    (hg : movingFrequencyGate value R
      (buildMovingSlotData n (frequencyTreeMap Subtype.val n t) small bulk a) x y)
    (j : Fin (2 ^ n - 1)) :
    let T := buildMovingSlotData n (frequencyTreeMap Subtype.val n t) small bulk a
    let D := frequencyModelAncestorScheme value S n t small a x y
    let p := frequencyModelPivots value R n T x y
    IsCoprime (D.leftCoefficient p j) (D.frequencies j).root ∧
      IsCoprime (D.rightCoefficient p j) (D.frequencies j).root := by
  dsimp only
  let T := buildMovingSlotData n (frequencyTreeMap Subtype.val n t) small bulk a
  let z := frequencyModelAtPath value R n T x y (preorderNodePath n j)
  have hf := frequencyModelAtPath_frequencies value R S n T t
    (buildMovingSlotData_follows n _ small bulk a) x y (preorderNodePath n j)
    (preorderNodePath_length n j)
  rw [nodePathIndex_preorderNodePath] at hf
  have hroot := congrArg NodeFrequencies.root hf
  have hd : z.frequencies.root ∣ (R : ℤ) := by
    rw [hroot]
    exact Int.natAbs_dvd.mp (Int.natCast_dvd_natCast.mpr
      (hR j))
  have hu := z.products_units value R
    (fun i => (hsmall i).of_isCoprime_of_dvd_right hd)
    (frequencyModelAtPath_gate value R n T x y (preorderNodePath n j) hg)
  have hp := frequencyModelNode_products value R S n t small bulk a x y j
  rw [hp.2.1, hp.2.2, hroot] at hu
  exact ⟨hu.2.of_mul_left_left, hu.1.of_mul_left_left⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingAdaptiveSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructed adaptive support for the original moving-giant sampler -/

namespace Ostmann
open scoped Classical

theorem movingFrameConstants_compensation_coprime {σ : Type*} (value : σ → ℕ)
    (R : ℤ) (hsmall : ∀ i, IsCoprime (value i : ℤ) R) (n : ℕ)
    (small : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) (path : List Bool) :
    IsCoprime ((movingFrameConstants value n small a path).compensation : ℤ) R := by
  induction n generalizing path with
  | zero =>
    cases a
    change IsCoprime (1 : ℤ) R
    exact isCoprime_one_left
  | succ n ih =>
    cases a with
    | node a l r =>
      cases path with
      | nil => exact movingNaturalProduct_coprime value _ R (fun i _ => hsmall i)
      | cons b path => cases b <;> apply ih

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrequencyModelAdaptiveSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructed split support for the arithmetic frequency gate -/

namespace Ostmann
open scoped Classical

theorem frequencyModelHistory_valid {σ : Type*} (value : σ → ℕ)
    (R : ℕ) (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (small bulk : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) (x y : ℤ)
    (hsmall : ∀ i, IsCoprime (value i : ℤ) (R : ℤ)) (hR : ∀ j : Fin (2 ^ n - 1), (singleTreeNodeFrequencies S n t j.val).root.natAbs ∣ R)
    (z : TreeLeafTuple (ZMod (R ^ (n - 1 + 2)))ˣ n)
    (hz : treeIntegerResidues (R ^ (n - 1 + 2)) n
      (treeLeafMap (fun q : ℕ => (q : ℤ)) n (movingSlotValues value n bulk)) z)
    (hg : movingFrequencyGate value R
      (buildMovingSlotData n (frequencyTreeMap Subtype.val n t) small bulk a) x y) :
    (frequencyModelHistory value R n (frequencyTreeMap Subtype.val n t) small bulk a x y z hz).modularValid
      (frequencyModelAncestorScheme value S n t small a x y) R (n - 1)
      (movingSampleCompensation value n small a) := by
  constructor
  · exact frequencyModel_modularEquations value R S n t small bulk a x y hsmall hg
  · intro j
    exact frequencyModel_coefficient_units value R S n t small bulk a x y hsmall hR hg j

theorem frequencyModelAdaptiveData_frequencies {σ : Type*} (value : σ → ℕ)
    (S : Finset ℤ) (n R : ℕ) (t : FrequencyTree S n)
    (hS : ∀ s ∈ S, s ≠ 0) (hR : ∀ j : Fin (2 ^ n - 1), (singleTreeNodeFrequencies S n t j.val).root.natAbs ∣ R)
    (small : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) (x y : ℤ)
    (total : (ZMod (R ^ (n - 1 + 2)))ˣ) (past : List (ZMod (R ^ (n - 1 + 2)))ˣ)
    (d : ArithmeticSplitData (R ^ (n - 1 + 2)))
    (hd : frequencyModelAdaptiveData value S n R t hS hR small a x y total past = some d) :
    d.hasFrequencies (singleTreeNodeFrequencies S n t past.length) := by
  by_cases hj : past.length < 2 ^ n - 1
  · exact modularAdaptiveData_frequencies n R (n - 1)
      (frequencyModelAncestorScheme value S n t small a x y)
      (movingSampleCompensation value n small a) _ _ total past hj d hd
  · simp only [frequencyModelAdaptiveData, modularAdaptiveData, hj, dite_false] at hd
    cases hd

/-- Every residue tuple accepted by the existing frequency gate lies in the
constructed sequential support. No prime-line or integer-integrality test
has been reintroduced. -/
theorem frequencyModelAdaptiveData_support {σ : Type*} (value : σ → ℕ)
    (S : Finset ℤ) (n R : ℕ) [NeZero (R ^ (n - 1 + 2))] (t : FrequencyTree S n)
    (hS : ∀ s ∈ S, s ≠ 0) (hR : ∀ j : Fin (2 ^ n - 1), (singleTreeNodeFrequencies S n t j.val).root.natAbs ∣ R)
    (small bulk : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) (x y : ℤ)
    (hsmall : ∀ i, IsCoprime (value i : ℤ) (R : ℤ))
    (z : TreeLeafTuple (ZMod (R ^ (n - 1 + 2)))ˣ n)
    (hz : treeIntegerResidues (R ^ (n - 1 + 2)) n
      (treeLeafMap (fun q : ℕ => (q : ℤ)) n (movingSlotValues value n bulk)) z)
    (hg : movingFrequencyGate value R
      (buildMovingSlotData n (frequencyTreeMap Subtype.val n t) small bulk a) x y) :
    singleArithmeticLeafSupport n
      (frequencyModelAdaptiveData value S n R t hS hR small a x y) z = 1 := by
  apply modularAdaptiveData_actual_support n R (n - 1)
    (frequencyModelAncestorScheme value S n t small a x y)
    (movingSampleCompensation value n small a)
    (fun i => movingFrameConstants_compensation_coprime value R hsmall n small a
      (preorderNodePath n i))
    (fun i => Nat.le_pred_of_lt (preorderNodePath_length n i))
    (fun i => hS _ (singleTreeNodeFrequencies_root_mem S n t i.val i.isLt))
    hR
    (frequencyModelHistory value R n (frequencyTreeMap Subtype.val n t) small bulk a x y z hz)
  exact frequencyModelHistory_valid value R S n t small bulk a x y hsmall hR z hz hg

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_WeightedArithmeticSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining a bounded integrand in the arithmetic support sum -/

namespace Ostmann

open scoped BigOperators Classical

theorem arithmeticLeafSupport_nonneg {Q : ℕ} [NeZero Q]
    (n : ℕ) (data : (ZMod Q)ˣ → List (ZMod Q)ˣ →
      Option (ArithmeticSplitData Q × ArithmeticSplitData Q))
    (x : TreeLeafTuple (ZMod Q)ˣ n) : 0 ≤ arithmeticLeafSupport n data x :=
  sequentialSupport_nonneg _ _ _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_CompensatedPairSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Paired adaptive support on the same original bulk variables -/

namespace Ostmann
open scoped Classical

theorem pairArithmeticData_test {Q : ℕ} (d e : Option (ArithmeticSplitData Q))
    (x : (ZMod Q)ˣ) :
    arithmeticPairSplitTest (pairArithmeticData d e) x ↔
      singleArithmeticSplitTest d x ∧ singleArithmeticSplitTest e x := by
  cases d <;> cases e <;> simp [pairArithmeticData, arithmeticPairSplitTest, singleArithmeticSplitTest]

theorem sequentialSupport_and {A : Type} (p q : List A → A → Prop)
    (past : List A) (n : ℕ) (x : SplitSamples A n) :
    sequentialSupport (fun past y => p past y ∧ q past y) past n x =
      sequentialSupport p past n x * sequentialSupport q past n x := by
  induction n generalizing past with
  | zero => simp [sequentialSupport]
  | succ n ih =>
    simp only [sequentialSupport]
    by_cases hp : p past x.1 <;> by_cases hq : q past x.1 <;>
      simp only [hp, hq, and_self, and_true, and_false,
        ite_true, if_true, ite_false, if_false, zero_mul, mul_zero, ih]

theorem arithmeticLeafSupport_pair {Q : ℕ} [NeZero Q] (n : ℕ)
    (d e : (ZMod Q)ˣ → List (ZMod Q)ˣ → Option (ArithmeticSplitData Q))
    (x : TreeLeafTuple (ZMod Q)ˣ n) :
    arithmeticLeafSupport n (fun total past => pairArithmeticData (d total past) (e total past)) x =
      singleArithmeticLeafSupport n d x * singleArithmeticLeafSupport n e x := by
  unfold arithmeticLeafSupport singleArithmeticLeafSupport
  simp only [pairArithmeticData_test]
  exact sequentialSupport_and _ _ _ _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_PairedFrequencyProjection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two actual frequency histories inside a paired tree -/

namespace Ostmann
open scoped Classical

theorem frequencySplitList_projection (S : Finset ℤ) (n : ℕ) (b : Bool)
    (t : FrequencyTree (S × S) n) :
    singleFrequencySplitList S n (frequencyPairProjection S n b t) =
      (frequencySplitList S n t).map (fun p => if b then p.2 else p.1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hl := ih t.2.1
    have hr := ih t.2.2
    dsimp only [frequencyPairProjection] at hl hr
    simp only [frequencyPairProjection, frequencyTreeMap, singleFrequencySplitList,
      frequencySplitList, List.map_cons, List.map_append, frequencyRoot_map,
      hl, hr]
    cases b <;> rfl

theorem treeNodeFrequencies_projection (S : Finset ℤ) (n : ℕ) (b : Bool)
    (t : FrequencyTree (S × S) n) (j : ℕ) :
    singleTreeNodeFrequencies S n (frequencyPairProjection S n b t) j =
      if b then (treeNodeFrequencies S n t j).2 else (treeNodeFrequencies S n t j).1 := by
  unfold singleTreeNodeFrequencies treeNodeFrequencies
  rw [frequencySplitList_projection]
  have h := List.getD_map (frequencySplitList S n t)
    (emptyNodeFrequencies, emptyNodeFrequencies) (fun p => if b then p.2 else p.1) (n := j)
  cases b <;> simpa only [Bool.false_eq_true, ite_false, if_false, ite_true, if_true] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrequencyModelPairSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Paired support for the two actual arithmetic frequency gates -/

namespace Ostmann
open scoped Classical

theorem frequencyModelPairData_frequencies {σ : Type*} (value : σ → ℕ)
    (S : Finset ℤ) (n R : ℕ) (t : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0) (hR : ∀ b (j : Fin (2 ^ n - 1)),
    (singleTreeNodeFrequencies S n (frequencyPairProjection S n b t) j.val).root.natAbs ∣ R)
    (small : Bool → TreeLeafTuple (List σ) n) (a : Bool → MovingSampleSlots σ n) (x y : ℤ)
    (total : (ZMod (R ^ (n - 1 + 2)))ˣ) (past : List (ZMod (R ^ (n - 1 + 2)))ˣ)
    (d e : ArithmeticSplitData (R ^ (n - 1 + 2)))
    (hde : frequencyModelPairData value S n R t hS hR small a x y total past = some (d, e)) :
    d.hasFrequencies (treeNodeFrequencies S n t past.length).1 ∧
      e.hasFrequencies (treeNodeFrequencies S n t past.length).2 := by
  let A := fun b => frequencyModelAdaptiveData value S n R (frequencyPairProjection S n b t)
    hS (hR b) (small b) (a b) x y total past
  change pairArithmeticData (A false) (A true) = some (d, e) at hde
  cases hd : A false with
  | none => simp [pairArithmeticData, hd] at hde
  | some d' =>
    cases he : A true with
    | none => simp [pairArithmeticData, he] at hde
    | some e' =>
      have h : d' = d ∧ e' = e := by
        simpa only [pairArithmeticData, hd, he, Option.some.injEq, Prod.mk.injEq] using hde
      rcases h with ⟨rfl, rfl⟩
      have hL := frequencyModelAdaptiveData_frequencies value S n R
        (frequencyPairProjection S n false t) hS (hR false) (small false) (a false) x y total past d' hd
      have hR' := frequencyModelAdaptiveData_frequencies value S n R
        (frequencyPairProjection S n true t) hS (hR true) (small true) (a true) x y total past e' he
      simpa only [treeNodeFrequencies_projection, Bool.false_eq_true, ite_false, if_false, ite_true, if_true]
        using And.intro hL hR'

/-- The same tuple of bulk residues tests both histories, under the original
unit law. Only the two frequency gates are hypotheses. -/
theorem frequencyModelPairData_support {σ : Type*} (value : σ → ℕ)
    (S : Finset ℤ) (n R : ℕ) [NeZero (R ^ (n - 1 + 2))] (t : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0) (hR : ∀ b (j : Fin (2 ^ n - 1)),
    (singleTreeNodeFrequencies S n (frequencyPairProjection S n b t) j.val).root.natAbs ∣ R)
    (small : Bool → TreeLeafTuple (List σ) n) (bulk : TreeLeafTuple (List σ) n)
    (a : Bool → MovingSampleSlots σ n) (x y : ℤ)
    (hsmall : ∀ i, IsCoprime (value i : ℤ) (R : ℤ))
    (z : TreeLeafTuple (ZMod (R ^ (n - 1 + 2)))ˣ n)
    (hz : treeIntegerResidues (R ^ (n - 1 + 2)) n
      (treeLeafMap (fun q : ℕ => (q : ℤ)) n (movingSlotValues value n bulk)) z)
    (hg : ∀ b, movingFrequencyGate value R
      (buildMovingSlotData n
        (frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t))
        (small b) bulk (a b)) x y) :
    arithmeticLeafSupport n (frequencyModelPairData value S n R t hS hR small a x y) z = 1 := by
  change arithmeticLeafSupport n (fun total past => pairArithmeticData
    (frequencyModelAdaptiveData value S n R (frequencyPairProjection S n false t)
      hS (hR false) (small false) (a false) x y total past)
    (frequencyModelAdaptiveData value S n R (frequencyPairProjection S n true t)
      hS (hR true) (small true) (a true) x y total past)) z = 1
  rw [arithmeticLeafSupport_pair,
    frequencyModelAdaptiveData_support value S n R (frequencyPairProjection S n false t)
      hS (hR false) (small false) bulk (a false) x y hsmall z hz (hg false),
    frequencyModelAdaptiveData_support value S n R (frequencyPairProjection S n true t)
      hS (hR true) (small true) bulk (a true) x y hsmall z hz (hg true), one_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrozenMovingSamples
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.movingSampleSlotsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual low-tier samples stay fixed when bulk slots vary -/

namespace Ostmann
open scoped Classical

theorem movingSlotValues_congr {σ : Type*} (v w : σ → ℕ) (n : ℕ)
    (small : TreeLeafTuple (List σ) n)
    (h : ∀ i ∈ flattenMovingSlots n small, v i = w i) :
    movingSlotValues v n small = movingSlotValues w n small := by
  induction n with
  | zero =>
    unfold movingSlotValues MovingSlotReversal.naturalProduct
    congr 1
    exact List.map_congr_left h
  | succ n ih =>
    exact Prod.ext
      (ih small.1 (fun i hi => h i (List.mem_append_left _ hi)))
      (ih small.2 (fun i hi => h i (List.mem_append_right _ hi)))

theorem movingCompensationValues_congr {σ : Type*} (v w : σ → ℕ) (n : ℕ)
    (samples : TreeLeafTuple (Fin 4 → σ) n)
    (h : ∀ i ∈ flattenMovingSlots n (movingCompensationSlots n samples), v i = w i) :
    movingCompensationValues v n samples = movingCompensationValues w n samples := by
  induction n with
  | zero =>
    funext i
    apply h
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  | succ n ih =>
    exact Prod.ext
      (ih samples.1 (fun i hi => h i (List.mem_append_left _ hi)))
      (ih samples.2 (fun i hi => h i (List.mem_append_right _ hi)))

/-- All internal samples have lower tier than the current bulk. This proves
equality of the complete sampled tree, including its shared child samples. -/
theorem MovingSampleSlots.values_eq_of_levels {σ : Type*} (tier : σ → ℕ)
    (v w : σ → ℕ) (k : ℕ) (heq : ∀ i, tier i < k → v i = w i)
    {n : ℕ} (samples : MovingSampleSlots σ n) (hn : n ≤ k)
    (hlevels : samples.Levels tier) : samples.values v = samples.values w := by
  induction samples with
  | leaf => rfl
  | @node n s left right ihL ihR =>
    change MovingGiantSamples.node (movingCompensationValues v n s) (left.values v) (right.values v) =
      MovingGiantSamples.node (movingCompensationValues w n s) (left.values w) (right.values w)
    congr 1
    · apply movingCompensationValues_congr
      intro i hi
      apply heq
      rw [hlevels.1 i hi]
      omega
    · exact ihL (by omega) hlevels.2.1
    · exact ihR (by omega) hlevels.2.2

/-- Replacing precisely the selected bulk coordinates preserves both sources
of nonbulk data used to construct the field diagram. -/
theorem frozenMoving_nonbulk_values {σ J : Type*} (tier : σ → ℕ)
    (base value : σ → ℕ) (e : J ↪ σ) (n : ℕ)
    (he : ∀ j, n ≤ tier (e j))
    (hv : ∀ i ∉ Set.range e, value i = base i)
    (small : TreeLeafTuple (List σ) n) (samples : MovingSampleSlots σ n)
    (hsmall : ∀ i ∈ flattenMovingSlots n small, i ∉ Set.range e)
    (hsamples : samples.Levels tier) :
    movingSlotValues value n small = movingSlotValues base n small ∧
      samples.values value = samples.values base := by
  refine ⟨movingSlotValues_congr value base n small (fun i hi => hv i (hsmall i hi)), ?_⟩
  apply samples.values_eq_of_levels tier value base n _ (le_refl _) hsamples
  intro i hi
  apply hv
  rintro ⟨j, rfl⟩
  exact (not_lt_of_ge (he j)) hi

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrequencyModelFrozen
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Adaptive arithmetic data is fixed while the bulk residues vary -/

namespace Ostmann
open scoped Classical

theorem movingFrameConstants_congr {σ : Type*} (v w : σ → ℕ) (n : ℕ)
    (small : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n)
    (hsmall : movingSlotValues v n small = movingSlotValues w n small)
    (ha : a.values v = a.values w) (path : List Bool) :
    movingFrameConstants v n small a path = movingFrameConstants w n small a path := by
  induction a generalizing path with
  | leaf => rfl
  | @node n a l r ihL ihR =>
    have hsL := congrArg Prod.fst hsmall
    have hsR := congrArg Prod.snd hsmall
    dsimp only [movingSlotValues] at hsL hsR
    have hc : movingCompensationValues v n a = movingCompensationValues w n a := by
      injection ha
    have hl : l.values v = l.values w := by injection ha
    have hr : r.values v = r.values w := by injection ha
    have hu : movingSlotValues v n (movingCompensationSlots n a) =
        movingSlotValues w n (movingCompensationSlots n a) := by
      rw [movingCompensationValues_product, movingCompensationValues_product, hc]
    cases path with
    | nil =>
      simp only [movingFrameConstants, movingSlotValues_flatten, hsL, hsR, hu]
    | cons b path =>
      have hleft : movingSlotValues v n (appendMovingSlotLeaves n (movingCompensationSlots n a) small.1) =
          movingSlotValues w n (appendMovingSlotLeaves n (movingCompensationSlots n a) small.1) := by
        rw [movingSlotValues_append, movingSlotValues_append, hu, hsL]
      have hright : movingSlotValues v n (appendMovingSlotLeaves n (movingCompensationSlots n a) small.2) =
          movingSlotValues w n (appendMovingSlotLeaves n (movingCompensationSlots n a) small.2) := by
        rw [movingSlotValues_append, movingSlotValues_append, hu, hsR]
      cases b
      · exact ihL _ hleft hl path
      · exact ihR _ hright hr path

theorem frequencyModelAncestorScheme_congr {σ : Type*} (v w : σ → ℕ)
    (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (small : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) (x y : ℤ)
    (hsmall : movingSlotValues v n small = movingSlotValues w n small)
    (ha : a.values v = a.values w) :
    frequencyModelAncestorScheme v S n t small a x y =
      frequencyModelAncestorScheme w S n t small a x y := by
  unfold frequencyModelAncestorScheme
  congr 1
  · funext path
    rw [movingFrameConstants_congr v w n small a hsmall ha path]
  · funext path
    rw [movingFrameConstants_congr v w n small a hsmall ha path]

theorem movingSampleCompensation_congr {σ : Type*} (v w : σ → ℕ) (n : ℕ)
    (small : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n)
    (hsmall : movingSlotValues v n small = movingSlotValues w n small)
    (ha : a.values v = a.values w) :
    movingSampleCompensation v n small a = movingSampleCompensation w n small a := by
  funext j
  unfold movingSampleCompensation
  rw [movingFrameConstants_congr v w n small a hsmall ha]

theorem frequencyModelAdaptiveData_congr {σ : Type*} (v w : σ → ℕ)
    (S : Finset ℤ) (n R : ℕ) (t : FrequencyTree S n)
    (hS : ∀ s ∈ S, s ≠ 0) (hR : ∀ j : Fin (2 ^ n - 1), (singleTreeNodeFrequencies S n t j.val).root.natAbs ∣ R)
    (small : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) (x y : ℤ)
    (hsmall : movingSlotValues v n small = movingSlotValues w n small)
    (ha : a.values v = a.values w) :
    frequencyModelAdaptiveData v S n R t hS hR small a x y =
      frequencyModelAdaptiveData w S n R t hS hR small a x y := by
  unfold frequencyModelAdaptiveData
  have aux {D E : PivotDependencyScheme (2 ^ n - 1)}
      {U V : Fin (2 ^ n - 1) → ℤ} (he : D = E) (hu : U = V)
      (hsD : ∀ i, (D.frequencies i).root ≠ 0) (hsE : ∀ i, (E.frequencies i).root ≠ 0)
      (hrD : ∀ i, (D.frequencies i).root.natAbs ∣ R)
      (hrE : ∀ i, (E.frequencies i).root.natAbs ∣ R) :
      modularAdaptiveData n R (n - 1) D U hsD hrD =
        modularAdaptiveData n R (n - 1) E V hsE hrE := by
    subst E
    subst V
    rfl
  exact aux (frequencyModelAncestorScheme_congr v w S n t small a x y hsmall ha)
    (movingSampleCompensation_congr v w n small a hsmall ha) _ _ _ _

theorem frequencyModelPairData_congr {σ : Type*} (v w : σ → ℕ)
    (S : Finset ℤ) (n R : ℕ) (t : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0) (hR : ∀ b (j : Fin (2 ^ n - 1)),
    (singleTreeNodeFrequencies S n (frequencyPairProjection S n b t) j.val).root.natAbs ∣ R)
    (small : Bool → TreeLeafTuple (List σ) n) (a : Bool → MovingSampleSlots σ n) (x y : ℤ)
    (hsmall : ∀ b, movingSlotValues v n (small b) = movingSlotValues w n (small b))
    (ha : ∀ b, (a b).values v = (a b).values w) :
    frequencyModelPairData v S n R t hS hR small a x y =
      frequencyModelPairData w S n R t hS hR small a x y := by
  funext total past
  unfold frequencyModelPairData
  rw [frequencyModelAdaptiveData_congr v w S n R _ hS (hR false) (small false) (a false) x y
      (hsmall false) (ha false),
    frequencyModelAdaptiveData_congr v w S n R _ hS (hR true) (small true) (a true) x y
      (hsmall true) (ha true)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrequencyBulkSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The frequency core under the original independent bulk-slot law -/

namespace Ostmann
open scoped Classical BigOperators

theorem treeIntegerResidues_of_naturalLift {Q : ℕ} (n : ℕ)
    (a : TreeLeafTuple ℕ n) (z : TreeLeafTuple (ZMod Q)ˣ n)
    (h : TreeNaturalLift n a z) :
    treeIntegerResidues Q n (treeLeafMap (fun q : ℕ => (q : ℤ)) n a) z := by
  induction n with
  | zero => simpa only [treeIntegerResidues, treeLeafMap, Int.cast_natCast] using h.symm
  | succ n ih => exact ⟨ih a.1 z.1 h.1, ih a.2 z.2 h.2⟩

theorem bulkUnitRepresentative_coprime {σ J : Type*} (base : σ → ℕ) (slot : J ↪ σ)
    (R Q : ℕ) [NeZero Q] (hRQ : R ∣ Q)
    (hbase : ∀ i ∉ Set.range slot, IsCoprime (base i : ℤ) (R : ℤ))
    (z : J → (ZMod Q)ˣ) (i : σ) :
    IsCoprime ((Function.extend slot (fun j => (z j).val.val) base i : ℕ) : ℤ) (R : ℤ) := by
  by_cases hi : ∃ j, slot j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [slot.injective.extend_apply]
    have hc : IsCoprime ((z j).val.val : ℤ) (Q : ℤ) := by
      apply IsCoprime.symm
      apply (ZMod.coe_int_isUnit_iff_isCoprime _ Q).mp
      simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using (z j).isUnit
    exact hc.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr hRQ)
  · rw [Function.extend_apply' _ base i hi]
    exact hbase i hi

/-- Keep the support indicator while taking the norm of the actual core.
The adaptive data uses the fixed nonbulk values; only the bulk law varies. -/
theorem frequencyModelBulkCore_norm_support {σ : Type*}
    (base : σ → ℕ) (tier : σ → ℕ) (S : Finset ℤ) (n m R : ℕ)
    [NeZero (R ^ (n - 1 + 2))] (t : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0) (hR : ∀ b (j : Fin (2 ^ n - 1)),
    (singleTreeNodeFrequencies S n (frequencyPairProjection S n b t) j.val).root.natAbs ∣ R)
    (slot : (TreeLeafIndex n × Fin m) ↪ σ)
    (small : Bool → TreeLeafTuple (List σ) n) (a : Bool → MovingSampleSlots σ n)
    (hslot : ∀ j, n ≤ tier (slot j))
    (hsmall : ∀ b i, i ∈ flattenMovingSlots n (small b) → i ∉ Set.range slot)
    (ha : ∀ b, (a b).Levels tier)
    (hbase : ∀ i ∉ Set.range slot, IsCoprime (base i : ℤ) (R : ℤ))
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (E : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℤ → ℤ → ℝ)
    (x y : ℤ) (z : TreeLeafIndex n × Fin m → (ZMod (R ^ (n - 1 + 2)))ˣ) :
    let value := Function.extend slot (fun j => (z j).val.val) base
    let T := fun b => buildMovingSlotData n
      (frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t))
      (small b) (bulkSlotLeaves n m slot) (a b)
    let Z := (treeLeafTupleEquiv (ZMod (R ^ (n - 1 + 2)))ˣ n).symm (bulkBlockProduct z)
    ‖movingFrequencyCore value F E T R x y‖ ≤
      (‖movingDataWeight (F false) (E false) (T false)‖ *
        ‖movingDataWeight (F true) (E true) (T true)‖) *
      arithmeticLeafSupport n (frequencyModelPairData base S n R t hS hR small a x y) Z := by
  intro value T Z
  have hfixed (b : Bool) := frozenMoving_nonbulk_values tier base value slot n hslot
    (fun i hi => Function.extend_apply' _ base i hi) (small b) (a b) (hsmall b) (ha b)
  have hdata := frequencyModelPairData_congr value base S n R t hS hR small a x y
    (fun b => (hfixed b).1) (fun b => (hfixed b).2)
  have hunit := bulkUnitRepresentative_coprime base slot R (R ^ (n - 1 + 2))
    (dvd_pow_self R (by omega)) hbase z
  have hz : treeIntegerResidues (R ^ (n - 1 + 2)) n
      (treeLeafMap (fun q : ℕ => (q : ℤ)) n (movingSlotValues value n (bulkSlotLeaves n m slot))) Z :=
    treeIntegerResidues_of_naturalLift n _ _ (bulkSlotLeaves_naturalLift value n m slot z
      (fun j => by
        change ((Function.extend slot (fun j => (z j).val.val) base (slot j) : ℕ) : ZMod (R ^ (n - 1 + 2))) = _
        rw [slot.injective.extend_apply, ZMod.natCast_zmod_val]))
  by_cases hg : ∀ b, movingFrequencyGate value R (T b) x y
  · have hs := frequencyModelPairData_support value S n R t hS hR small
      (bulkSlotLeaves n m slot) a x y hunit Z hz hg
    rw [hdata] at hs
    rw [hs, mul_one]
    rw [movingFrequencyCore, ite_eq_left hg, norm_mul, Complex.norm_conj]
  · rw [movingFrequencyCore, ite_eq_right hg, norm_zero]
    exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (arithmeticLeafSupport_nonneg n _ Z)

/-- Passing from individual bulk slots to their leaf products is an exact
uniform averaging identity. -/
theorem arithmeticLeafSupport_bulk_average {Q : ℕ} [NeZero Q] (n m : ℕ) (hm : 0 < m)
    (data : (ZMod Q)ˣ → List (ZMod Q)ˣ → Option (ArithmeticSplitData Q × ArithmeticSplitData Q)) :
    (Fintype.card (TreeLeafIndex n × Fin m → (ZMod Q)ˣ) : ℝ)⁻¹ *
      (∑ z : TreeLeafIndex n × Fin m → (ZMod Q)ˣ, arithmeticLeafSupport n data
        ((treeLeafTupleEquiv (ZMod Q)ˣ n).symm (bulkBlockProduct z))) =
      (Fintype.card (TreeLeafTuple (ZMod Q)ˣ n) : ℝ)⁻¹ *
        ∑ z : TreeLeafTuple (ZMod Q)ˣ n, arithmeticLeafSupport n data z := by
  have h := bulkBlockProduct_average (L := TreeLeafIndex n) (G := (ZMod Q)ˣ) (m := m) hm
    (fun z => arithmeticLeafSupport n data ((treeLeafTupleEquiv (ZMod Q)ˣ n).symm z))
  let e := treeLeafTupleEquiv (ZMod Q)ˣ n
  have he := e.symm.sum_comp (arithmeticLeafSupport n data)
  have hc := Fintype.card_congr e
  simp only [finite_univ_canonical, Fintype.card_eq_nat_card] at h he hc ⊢
  rw [← hc, he] at h
  exact h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSeparatedAverageNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete norm budgets for the retained arithmetic averages -/

namespace Ostmann
open scoped Classical BigOperators

private theorem finiteMean_norm_le {A : Type*} [Fintype A] [Nonempty A]
    (f : A → ℂ) (B : ℝ) (hf : ∀ a, ‖f a‖ ≤ B) :
    ‖(Fintype.card A : ℂ)⁻¹ * ∑ a, f a‖ ≤ B := by
  have hcard : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (Fintype.card A : ℝ)⁻¹ * ∑ _a : A, B :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => hf a))
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = B := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

theorem pageGiantWeight_norm_le_two (input : PublishedProgressionInput) (Q q a : ℕ)
    (y : ℝ) (hy : 0 ≤ y) : ‖pageGiantWeight input Q q a y‖ ≤ 2 := by
  have h := pageMultiplier_bounds
    (fun a => pageCoefficient (pageAtModulus q (selectedPageZero input Q)) a)
    (pageBeta (pageAtModulus q (selectedPageZero input Q))) y
    (pageCoefficient_abs_le_one _) (pageBeta_le_one _) hy a
  rw [pageGiantWeight, Complex.norm_real, Real.norm_of_nonneg h.1]
  exact h.2

theorem movingFrequencyPageAverage_norm_le {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (R : ℤ) (r : ℕ) [NeZero r] (input : PublishedProgressionInput) (Q : ℕ)
    (y : ℝ) (hy : 0 ≤ y) :
    ‖movingFrequencyPageAverage value outside F E T nodes R r input Q y‖ ≤
      2 * (‖movingDataWeight (F false) (E false) (T false)‖ *
        ‖movingDataWeight (F true) (E true) (T true)‖) := by
  apply finiteMean_norm_le
  intro z
  have hf : ‖movingFrequencyPairFactor value outside F E T nodes R z.1.val z.2.val.val‖ ≤
      ‖movingDataWeight (F false) (E false) (T false)‖ *
        ‖movingDataWeight (F true) (E true) (T true)‖ := by
    unfold movingFrequencyPairFactor
    split_ifs
    · simp only [norm_mul, Complex.norm_conj, le_refl]
    · exact (norm_zero : ‖(0 : ℂ)‖ = 0) ▸ mul_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [norm_mul]
  calc
    _ ≤ (‖movingDataWeight (F false) (E false) (T false)‖ *
        ‖movingDataWeight (F true) (E true) (T true)‖) * 2 :=
      mul_le_mul hf (pageGiantWeight_norm_le_two input Q r z.2.val.val y hy)
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := mul_comm _ _

theorem movingSpectatorHaarAverage_norm_le {σ : Type*} (value : σ → ℕ)
    (q : ℕ) [Fact q.Prime] (g : ZMod q → ℂ) (D : Bool → (ZMod q)ˣ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (B : ℝ) (hB : 0 ≤ B)
    (hg : ∀ z, ‖g z‖ ≤ B) :
    ‖movingSpectatorHaarAverage value q g D T‖ ≤ B ^ (2 ^ (n + 1)) := by
  apply finiteMean_norm_le
  intro z
  rw [movingSpectatorPairFactor, norm_mul, Complex.norm_conj]
  calc
    _ ≤ B ^ (2 ^ n) * B ^ (2 ^ n) :=
      mul_le_mul (movingModularSpectator_norm value q g (D false) B hB hg (T false) z.1 z.2)
        (movingModularSpectator_norm value q g (D true) B hB hg (T true) z.1 z.2)
        (norm_nonneg _) (pow_nonneg hB _)
    _ = _ := by rw [← pow_add, pow_succ]; congr 1; omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrequencyBulkNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sharp arithmetic probability retained in the bulk frequency norm -/

namespace Ostmann
open scoped Classical BigOperators

theorem arithmeticLeafSupport_mean_le {Q : ℕ} [NeZero Q]
    (S : Finset ℤ) (N n : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (hdiv : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D)
    (t : FrequencyTree (S × S) n)
    (data : (ZMod Q)ˣ → List (ZMod Q)ˣ → Option (ArithmeticSplitData Q × ArithmeticSplitData Q))
    (hmatch : ∀ P past d e, data P past = some (d, e) →
      d.hasFrequencies (treeNodeFrequencies S n t past.length).1 ∧
        e.hasFrequencies (treeNodeFrequencies S n t past.length).2) :
    (Fintype.card (TreeLeafTuple (ZMod Q)ˣ n) : ℝ)⁻¹ *
        (∑ z : TreeLeafTuple (ZMod Q)ˣ n, arithmeticLeafSupport n data z) ≤
      ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod := by
  have he : (∏ j ∈ Finset.range (2 ^ n - 1),
      pairFrequencySupportBound D (treeNodeFrequencies S n t j)) =
      ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod := by
    rw [← frequencySplitList_length S n t]
    exact prod_range_list_getD _ _ _
  unfold arithmeticLeafSupport
  apply treeLeaf_average_le (G := (ZMod Q)ˣ) n
    (fun P x => sequentialSupport (fun past y => arithmeticPairSplitTest (data P past) y)
      [] (2 ^ n - 1) (treeLeafSplitEquiv n P x)) _
  intro P
  exact (arithmetic_leaf_support_fixed_frequencies (data P) (treeNodeFrequencies S n t)
    D hD (hmatch P) (treeNodeFrequencies_divisor_bound S N D hD hS hdiv n t) n P).trans_eq he

theorem uniform_average_norm_average_mul_le {A B : Type*} [Fintype A] [Fintype B] [Nonempty B]
    (f : A → B → ℂ) (w : B → ℂ) (C K : ℝ) (hC : 0 ≤ C)
    (hw : ∀ b, ‖w b‖ ≤ C)
    (hf : ∀ b, (Fintype.card A : ℝ)⁻¹ * ∑ a, ‖f a b‖ ≤ K) :
    (Fintype.card A : ℝ)⁻¹ *
      (∑ a, ‖(Fintype.card B : ℂ)⁻¹ * ∑ b, f a b * w b‖) ≤ C * K := by
  have hpoint (a : A) : ‖(Fintype.card B : ℂ)⁻¹ * ∑ b, f a b * w b‖ ≤
      (Fintype.card B : ℝ)⁻¹ * ∑ b, C * ‖f a b‖ := by
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro b _
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hw b) (norm_nonneg _)).trans_eq (mul_comm _ _)
  calc
    _ ≤ (Fintype.card A : ℝ)⁻¹ *
        ∑ a, (Fintype.card B : ℝ)⁻¹ * ∑ b, C * ‖f a b‖ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => hpoint a)
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = (Fintype.card B : ℝ)⁻¹ * ∑ b, C * ((Fintype.card A : ℝ)⁻¹ * ∑ a, ‖f a b‖) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ (Fintype.card B : ℝ)⁻¹ * ∑ _b : B, C * K := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      exact Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hf b) hC
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]

section
variable {σ : Type*} (base : σ → ℕ) (tier : σ → ℕ) (S : Finset ℤ) (n m R : ℕ)
  [NeZero (R ^ (n - 1 + 2))] (t : FrequencyTree (S × S) n)
  (hS : ∀ s ∈ S, s ≠ 0) (hR : ∀ b (j : Fin (2 ^ n - 1)),
    (singleTreeNodeFrequencies S n (frequencyPairProjection S n b t) j.val).root.natAbs ∣ R)
  (slot : (TreeLeafIndex n × Fin m) ↪ σ)
  (small : Bool → TreeLeafTuple (List σ) n) (a : Bool → MovingSampleSlots σ n)
  (hslot : ∀ j, n ≤ tier (slot j))
  (hsmall : ∀ b i, i ∈ flattenMovingSlots n (small b) → i ∉ Set.range slot)
  (ha : ∀ b, (a b).Levels tier)
  (hbase : ∀ i ∉ Set.range slot, IsCoprime (base i : ℤ) (R : ℤ))
  (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
  (E : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℤ → ℤ → ℝ)
  (N : ℕ) (D : ℝ) (hD : 0 ≤ D) (hN : ∀ s ∈ S, s.natAbs ≤ N)
  (hdiv : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D)
  (hm : 0 < m)

include hslot hsmall ha hbase hS hR hD hN hdiv hm in
/-- The original bulk unit law gives the product of the simultaneous
quadratic-root bounds. The coefficient contains the literal data weights. -/
theorem frequencyModelBulkCore_mean_le (x y : ℤ) :
    let T := fun b => buildMovingSlotData n
      (frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t))
      (small b) (bulkSlotLeaves n m slot) (a b)
    (Fintype.card (TreeLeafIndex n × Fin m → (ZMod (R ^ (n - 1 + 2)))ˣ) : ℝ)⁻¹ *
        (∑ z : TreeLeafIndex n × Fin m → (ZMod (R ^ (n - 1 + 2)))ˣ,
          ‖movingFrequencyCore (Function.extend slot (fun j => (z j).val.val) base) F E T R x y‖) ≤
      (‖movingDataWeight (F false) (E false) (T false)‖ *
        ‖movingDataWeight (F true) (E true) (T true)‖) *
      ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod := by
  intro T
  let data := frequencyModelPairData base S n R t hS hR small a x y
  let amp := ‖movingDataWeight (F false) (E false) (T false)‖ *
    ‖movingDataWeight (F true) (E true) (T true)‖
  have hs := arithmeticLeafSupport_mean_le S N n D hD (fun s hs => ⟨hS s hs, hN s hs⟩)
    hdiv t data (frequencyModelPairData_frequencies base S n R t hS hR small a x y)
  calc
    _ ≤ (Fintype.card (TreeLeafIndex n × Fin m → (ZMod (R ^ (n - 1 + 2)))ˣ) : ℝ)⁻¹ *
        ∑ z : TreeLeafIndex n × Fin m → (ZMod (R ^ (n - 1 + 2)))ˣ,
          amp * arithmeticLeafSupport n data
            ((treeLeafTupleEquiv (ZMod (R ^ (n - 1 + 2)))ˣ n).symm (bulkBlockProduct z)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      exact Finset.sum_le_sum fun z _ =>
        frequencyModelBulkCore_norm_support base tier S n m R t hS hR slot small a hslot hsmall ha hbase F E x y z
    _ = amp * ((Fintype.card (TreeLeafIndex n × Fin m → (ZMod (R ^ (n - 1 + 2)))ˣ) : ℝ)⁻¹ *
        ∑ z : TreeLeafIndex n × Fin m → (ZMod (R ^ (n - 1 + 2)))ˣ,
          arithmeticLeafSupport n data
            ((treeLeafTupleEquiv (ZMod (R ^ (n - 1 + 2)))ˣ n).symm (bulkBlockProduct z))) := by
      rw [← Finset.mul_sum]
      ring
    _ = amp * ((Fintype.card (TreeLeafTuple (ZMod (R ^ (n - 1 + 2)))ˣ n) : ℝ)⁻¹ *
        ∑ z : TreeLeafTuple (ZMod (R ^ (n - 1 + 2)))ˣ n, arithmeticLeafSupport n data z) := by
      rw [arithmeticLeafSupport_bulk_average n m hm data]
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (mul_nonneg (norm_nonneg _) (norm_nonneg _))

include hslot hsmall ha hbase hS hR hD hN hdiv hm in
/-- Discarding the Page multiplier costs only two and preserves every
frequency split saving under the original bulk law. -/
theorem frequencyModelBulkPage_mean_le (input : PublishedProgressionInput)
    (Q : ℕ) (Y : ℝ) (hY : 0 ≤ Y) :
    let T := fun b => buildMovingSlotData n
      (frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t))
      (small b) (bulkSlotLeaves n m slot) (a b)
    (Fintype.card (TreeLeafIndex n × Fin m → (ZMod (R ^ (n - 1 + 2)))ˣ) : ℝ)⁻¹ *
        (∑ z : TreeLeafIndex n × Fin m → (ZMod (R ^ (n - 1 + 2)))ˣ,
          ‖movingFrequencyCorePageAverage (Function.extend slot (fun j => (z j).val.val) base)
            F E T R (R ^ (n - 1 + 2)) input Q Y‖) ≤
      2 * ((‖movingDataWeight (F false) (E false) (T false)‖ *
        ‖movingDataWeight (F true) (E true) (T true)‖) *
      ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod) := by
  intro T
  have h := uniform_average_norm_average_mul_le
    (A := TreeLeafIndex n × Fin m → (ZMod (R ^ (n - 1 + 2)))ˣ)
    (B := ZMod (R ^ (n - 1 + 2)) × (ZMod (R ^ (n - 1 + 2)))ˣ)
    (fun z (xy : ZMod (R ^ (n - 1 + 2)) × (ZMod (R ^ (n - 1 + 2)))ˣ) =>
      movingFrequencyCore (Function.extend slot (fun j => (z j).val.val) base) F E T R
        xy.1.val xy.2.val.val)
    (fun xy => pageGiantWeight input Q (R ^ (n - 1 + 2)) xy.2.val.val Y)
    2 ((‖movingDataWeight (F false) (E false) (T false)‖ *
      ‖movingDataWeight (F true) (E true) (T true)‖) *
      ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod) (by norm_num)
    (fun xy => pageGiantWeight_norm_le_two input Q (R ^ (n - 1 + 2)) _ Y hY)
    (fun xy => frequencyModelBulkCore_mean_le base tier S n m R t hS hR slot small a
      hslot hsmall ha hbase F E N D hD hN hdiv hm xy.1.val xy.2.val.val)
  simpa only [movingFrequencyCorePageAverage] using h

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_NormalizedResidueIndicator
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript's normalized residue indicators and additive transforms -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

theorem residueVariance_pos {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (hS : S.Nonempty) (hSp : S.card < p) : 0 < residueVariance S := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hd : 0 < residueDensity S := div_pos (by exact_mod_cast hS.card_pos) hp
  have hd1 : residueDensity S < 1 := (div_lt_one hp).mpr (by exact_mod_cast hSp)
  exact mul_pos hd (sub_pos.mpr hd1)

theorem centeredDensity_sq_sum {p : ℕ} [NeZero p] (S : Finset (ZMod p)) :
    (∑ x : ZMod p, centeredDensity S x ^ 2) = (p : ℝ) * residueVariance S := by
  let σ := residueDensity S
  have hsq (x : ZMod p) : centeredDensity S x ^ 2 =
      (if x ∈ S then 1 - 2 * σ else 0) + σ ^ 2 := by
    dsimp [centeredDensity, σ, residueDensity]
    split <;> ring
  simp_rw [hsq]
  rw [Finset.sum_add_distrib]
  have hsum : (∑ x : ZMod p, if x ∈ S then (1 - 2 * σ) else 0) = S.card * (1 - 2 * σ) := by simp; ring
  rw [hsum]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hσ : (p : ℝ) * σ = S.card := by dsimp [σ, residueDensity]; field_simp
  change _ = (p : ℝ) * (σ * (1 - σ))
  rw [← hσ]
  ring

theorem normalizedResidueIndicator_sum {p : ℕ} [NeZero p] (S : Finset (ZMod p)) :
    (∑ x : ZMod p, normalizedResidueIndicator S x) = 0 := by
  simp only [normalizedResidueIndicator, ← Complex.ofReal_sum, ← Finset.sum_div,
    centeredDensity_sum, zero_div, Complex.ofReal_zero]

theorem normalizedResidueIndicator_energy {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (hS : S.Nonempty) (hSp : S.card < p) :
    (∑ x : ZMod p, ‖normalizedResidueIndicator S x‖ ^ 2) = p := by
  have hv := residueVariance_pos S hS hSp
  simp only [normalizedResidueIndicator, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    div_pow, ← Finset.sum_div, Real.sq_sqrt hv.le, centeredDensity_sq_sum]
  exact mul_div_cancel_right₀ (p : ℝ) hv.ne'

theorem normalizedResidueTransform_zero {p : ℕ} [NeZero p] (S : Finset (ZMod p)) :
    normalizedResidueTransform S 0 = 0 := by
  simp only [normalizedResidueTransform, densityFourier, additiveFourier_apply,
    mul_zero, neg_zero, AddChar.map_zero_eq_one, mul_one, normalizedResidueIndicator_sum]

theorem normalizedResidueTransform_energy {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (hS : S.Nonempty) (hSp : S.card < p) :
    (∑ x : ZMod p, ‖normalizedResidueTransform S x‖ ^ 2) = p := by
  rw [normalizedResidueTransform, densityFourier_energy, normalizedResidueIndicator_energy S hS hSp]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrozenSpectatorAbsolute
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absolute spectator moments under the unchanged bulk-unit law -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem frozenBulkSpectatorPair_absolute_mean_le {σ : Type*} {q : ℕ} [Fact q.Prime]
    (hq : 3 ≤ q) (base : σ → ℕ) (n m : ℕ) (hm : 0 < m)
    (t : Bool → FrequencyTree ℤ n)
    (small : Bool → TreeLeafTuple (List σ) n) (samples : Bool → MovingSampleSlots σ n)
    (hfreq : ∀ b, movingGiantFrequencyUnits q n (t b))
    (hsmall : ∀ b, ((treeLeafProduct n (movingSlotValues base n (small b)) : ℕ) : ZMod q) ≠ 0)
    (hsamples : ∀ b, ((samples b).values base).UnitsAt q)
    (D : Bool → (ZMod q)ˣ) (e : Equiv.Perm (TreeLeafIndex n × Fin m))
    (g : ZMod q → ℂ) (hg : g 0 = 0) (henergy : ∑ x : ZMod q, ‖g x‖ ^ 2 ≤ (q : ℝ))
    (a : (ZMod q)ˣ × (ZMod q)ˣ) :
    (Fintype.card (TreeLeafIndex n × Fin m → (ZMod q)ˣ) : ℝ)⁻¹ *
      (∑ z : TreeLeafIndex n × Fin m → (ZMod q)ˣ,
        ‖frozenBulkSpectatorPair base n m t small samples D e g a z‖) ≤ (3 : ℝ) ^ (2 ^ n) := by
  have hex (b : Bool) := (buildMovingGiantTree n (t b)
    (movingSlotValues base n (small b)) ((samples b).values base)).exists_field_diagram
      (buildMovingGiantTree_units (t b) _ _ (hfreq b) (hsmall b) (hsamples b))
  choose U R _ _ hR using hex
  let d (b : Bool) : SpectatorDiagram q n :=
    ⟨D b, U b, R b, a.1, a.2, transferConjugations n false⟩
  have he (z : TreeLeafIndex n × Fin m → (ZMod q)ˣ) :
      frozenBulkSpectatorPair base n m t small samples D e
        g a z =
      (d false).bulkValue g z *
        conj ((d true).bulkValue g (z ∘ e.symm)) := by
    unfold frozenBulkSpectatorPair
    rw [show movingFieldGiantAmplitude g (D false)
        (buildMovingGiantTree n (t false) (movingSlotValues base n (small false))
          ((samples false).values base)) a.1 a.2 _ = _ from
        hR false g (D false) a.1 a.2 _ false,
      show movingFieldGiantAmplitude g (D true)
        (buildMovingGiantTree n (t true) (movingSlotValues base n (small true))
          ((samples true).values base)) a.1 a.2 _ = _ from
        hR true g (D true) a.1 a.2 _ false]
    rfl
  simp_rw [he]
  exact spectator_bulk_absolute_le hq hm g hg henergy (d false) (d true) e

theorem frozenBulkSpectatorHaar_absolute_mean_le {σ : Type*} {q : ℕ} [Fact q.Prime]
    (hq : 3 ≤ q) (base : σ → ℕ) (n m : ℕ) (hm : 0 < m)
    (t : Bool → FrequencyTree ℤ n)
    (small : Bool → TreeLeafTuple (List σ) n) (samples : Bool → MovingSampleSlots σ n)
    (hfreq : ∀ b, movingGiantFrequencyUnits q n (t b))
    (hsmall : ∀ b, ((treeLeafProduct n (movingSlotValues base n (small b)) : ℕ) : ZMod q) ≠ 0)
    (hsamples : ∀ b, ((samples b).values base).UnitsAt q)
    (D : Bool → (ZMod q)ˣ) (e : Equiv.Perm (TreeLeafIndex n × Fin m))
    (g : ZMod q → ℂ) (hg : g 0 = 0) (henergy : ∑ x : ZMod q, ‖g x‖ ^ 2 ≤ (q : ℝ)) :
    (Fintype.card (TreeLeafIndex n × Fin m → (ZMod q)ˣ) : ℝ)⁻¹ *
      (∑ z : TreeLeafIndex n × Fin m → (ZMod q)ˣ,
        ‖frozenBulkSpectatorHaar base n m t small samples D e g z‖) ≤ (3 : ℝ) ^ (2 ^ n) := by
  let F := frozenBulkSpectatorPair base n m t small samples D e g
  have hmean := uniform_average_norm_average_mul_le
    (A := TreeLeafIndex n × Fin m → (ZMod q)ˣ)
    (B := (ZMod q)ˣ × (ZMod q)ˣ) (fun z a => F a z) (fun _ => 1) 1 ((3 : ℝ) ^ (2 ^ n))
    (by norm_num) (fun _ => by simp)
    (fun a => frozenBulkSpectatorPair_absolute_mean_le hq base n m hm t small samples
      hfreq hsmall hsamples D e g hg henergy a)
  simp only [mul_one, one_mul] at hmean
  have hratio : ‖(Fintype.card (ZMod q)ˣ : ℂ) / (q : ℂ)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
    apply (div_le_one (by positivity : (0 : ℝ) < q)).mpr
    exact_mod_cast (ZMod.card_units q ▸ Nat.sub_le q 1)
  apply le_trans _ hmean
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_le_sum
  intro z _
  rw [frozenBulkSpectatorHaar, norm_mul]
  exact (mul_le_mul_of_nonneg_right hratio (norm_nonneg _)).trans_eq (one_mul _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkResidueAbsolute
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nonnegative norm comparison after bulk CRT separation -/

namespace Ostmann
open scoped Classical BigOperators

theorem uniform_equiv_product_average_real {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C]
    (e : A ≃ B × C) (f : B → ℝ) (g : C → ℝ) :
    (Fintype.card A : ℝ)⁻¹ * (∑ a, f (e a).1 * g (e a).2) =
      ((Fintype.card B : ℝ)⁻¹ * ∑ b, f b) *
        ((Fintype.card C : ℝ)⁻¹ * ∑ c, g c) := by
  rw [e.sum_comp (fun z => f z.1 * g z.2), Fintype.card_congr e,
    Fintype.card_prod, Nat.cast_mul, mul_inv_rev, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  ring

/-- Page factors at every original bulk slot cost at most two. The frequency
and spectator averages still retain their independent CRT coordinates. -/
theorem bulk_residue_absolute_mean_le {I J : Type*} [Fintype I] [Fintype J]
    (r : ℕ) [NeZero r] (p : I → ℕ) [∀ i, NeZero (p i)]
    [NeZero (∏ i, bulkResidueModuli r p i)]
    (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
    (P : PublishedProgressionInput) (Q : ℕ) (Y : J → ℝ) (hY : ∀ j, 0 ≤ Y j)
    (F : (J → (ZMod r)ˣ) → ℂ) (G : ∀ i, (J → (ZMod (p i))ˣ) → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (C : I → ℝ)
    (hF : (Fintype.card (J → (ZMod r)ˣ) : ℝ)⁻¹ * ∑ a, ‖F a‖ ≤ B)
    (hG : ∀ i, (Fintype.card (J → (ZMod (p i))ˣ) : ℝ)⁻¹ * ∑ a, ‖G i a‖ ≤ C i) :
    (Fintype.card (J → (ZMod (∏ i, bulkResidueModuli r p i))ˣ) : ℝ)⁻¹ *
      (∑ x : J → (ZMod (∏ i, bulkResidueModuli r p i))ˣ,
        ‖(F (bulkResidueEquiv r p hc x).1 *
          ∏ j, pageGiantWeight P Q (∏ i, bulkResidueModuli r p i) (x j).val.val (Y j)) *
          ∏ i, G i ((bulkResidueEquiv r p hc x).2 i)‖) ≤
      (2 : ℝ) ^ Fintype.card J * (B * ∏ i, C i) := by
  let e := bulkResidueEquiv (J := J) r p hc
  have hpage (x : J → (ZMod (∏ i, bulkResidueModuli r p i))ˣ) :
      ‖∏ j, pageGiantWeight P Q (∏ i, bulkResidueModuli r p i) (x j).val.val (Y j)‖ ≤
        (2 : ℝ) ^ Fintype.card J := by
    rw [norm_prod]
    exact (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ =>
      pageGiantWeight_norm_le_two P Q _ _ _ (hY j))).trans_eq (by simp)
  have hspec := product_uniform_mean_le (fun i a => ‖G i a‖) (fun _ _ => norm_nonneg _)
    C hG
  have hspec0 : 0 ≤ (Fintype.card (∀ i, J → (ZMod (p i))ˣ) : ℝ)⁻¹ *
      ∑ a : ∀ i, J → (ZMod (p i))ˣ, ∏ i, ‖G i (a i)‖ := by positivity
  calc
    _ ≤ (Fintype.card (J → (ZMod (∏ i, bulkResidueModuli r p i))ˣ) : ℝ)⁻¹ *
        ∑ x : J → (ZMod (∏ i, bulkResidueModuli r p i))ˣ,
          (2 : ℝ) ^ Fintype.card J * (‖F (e x).1‖ * ∏ i, ‖G i ((e x).2 i)‖) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      apply Finset.sum_le_sum
      intro x _
      have hgn : 0 ≤ ∏ i, ‖G i ((e x).2 i)‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
      have hp := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hpage x) (norm_nonneg (F (e x).1))) hgn
      simpa only [norm_mul, norm_prod, mul_assoc, mul_comm, mul_left_comm] using hp
    _ = (2 : ℝ) ^ Fintype.card J *
        (((Fintype.card (J → (ZMod r)ˣ) : ℝ)⁻¹ * ∑ a, ‖F a‖) *
          ((Fintype.card (∀ i, J → (ZMod (p i))ˣ) : ℝ)⁻¹ *
            ∑ a : ∀ i, J → (ZMod (p i))ˣ, ∏ i, ‖G i (a i)‖)) := by
      rw [← Finset.mul_sum, ← mul_assoc, mul_comm _ ((2 : ℝ) ^ Fintype.card J), mul_assoc]
      rw [uniform_equiv_product_average_real e (fun a => ‖F a‖) (fun a => ∏ i, ‖G i (a i)‖)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul hF hspec hspec0 hB) (by positivity)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternBulkData
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original pattern pair in selected bulk coordinates -/

namespace Ostmann
open scoped Classical

theorem movingPatternFiniteSamples_levels {B C : Type*} {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (n : ℕ) (pattern : Bool × MovingSampleIndex n → C)
    (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2) (side : Bool) :
    (movingPatternFiniteSamples e n pattern side).Levels ((Sum.elim tierB tierC) ∘ e) := by
  apply movingSampleCoordinates_levels
  intro i
  simpa only [Function.comp_apply, Equiv.apply_symm_apply, Sum.elim_inr] using htier (side, i)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrequencyModelModulus
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A modulus using only the frequencies of the two fixed histories -/

namespace Ostmann
open scoped Classical

theorem frequencyModelBase_roots (S : Finset ℤ) (n : ℕ) (t : FrequencyTree (S × S) n)
    (b : Bool) (j : Fin (2 ^ n - 1)) :
    (singleTreeNodeFrequencies S n (frequencyPairProjection S n b t) j.val).root.natAbs ∣
      frequencyModelBase S n t := by
  have hj : j.val < (singleFrequencySplitList S n (frequencyPairProjection S n b t)).length := by
    simpa only [singleFrequencySplitList_length] using j.isLt
  have hmem : singleTreeNodeFrequencies S n (frequencyPairProjection S n b t) j.val ∈
      singleFrequencySplitList S n (frequencyPairProjection S n b t) := by
    rw [singleTreeNodeFrequencies, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  have hd := history_node_dvd_frequencyProduct S n (frequencyPairProjection S n b t) _ hmem
  cases b
  · exact dvd_mul_of_dvd_left hd _
  · exact dvd_mul_of_dvd_right hd _

theorem buildMovingSlotData_frequencyProduct_abs {σ : Type*}
    (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (small bulk : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) :
    (buildMovingSlotData n (frequencyTreeMap Subtype.val n t) small bulk a).frequencyProduct.natAbs =
      historyFrequencyProduct S n t := by
  induction a with
  | leaf => rfl
  | @node n u l r ihL ihR =>
    simp only [buildMovingSlotData, frequencyTreeMap, MovingSlotData.frequencyProduct,
      Int.natAbs_mul, historyFrequencyProduct, ihL, ihR]

theorem frequencyModelModulus_precision (R n : ℕ) :
    (R : ℤ) ^ (n + 1) ∣ ((R ^ (n - 1 + 2) : ℕ) : ℤ) := by
  rw [Nat.cast_pow]
  exact pow_dvd_pow (R : ℤ) (by omega)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrozenBulkFrequencyNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The frequency norm with the original fixed nonbulk masks -/

namespace Ostmann
open scoped Classical BigOperators

section
variable {σ : Type*} (base : σ → ℕ) (tier : σ → ℕ) (S : Finset ℤ) (n m R : ℕ)
  [NeZero (R ^ (n - 1 + 2))] (t : FrequencyTree (S × S) n)
  (hS : ∀ s ∈ S, s ≠ 0) (hR : ∀ b (j : Fin (2 ^ n - 1)),
    (singleTreeNodeFrequencies S n (frequencyPairProjection S n b t) j.val).root.natAbs ∣ R)
  (slot : (TreeLeafIndex n × Fin m) ↪ σ)
  (small : Bool → TreeLeafTuple (List σ) n) (a : Bool → MovingSampleSlots σ n)
  (hslot : ∀ j, n ≤ tier (slot j))
  (hsmall : ∀ b i, i ∈ flattenMovingSlots n (small b) → i ∉ Set.range slot)
  (ha : ∀ b, (a b).Levels tier)
  (hbase : ∀ i ∉ Set.range slot, IsCoprime (base i : ℤ) (R : ℤ))
  (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
  (E : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℤ → ℤ → ℝ)
  (N : ℕ) (D : ℝ) (hD : 0 ≤ D) (hN : ∀ s ∈ S, s.natAbs ≤ N)
  (hdiv : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D)
  (hm : 0 < m)

include hslot hsmall ha hbase hS hR hD hN hdiv hm in
/-- The retained fixed support mask can only decrease the bulk norm. -/
theorem frozenBulkFrequencyFactor_mean_le
    (outside : List ℕ) (childBound : ℕ → ℕ) (input : PublishedProgressionInput)
    (Q : ℕ) (Y : ℝ) (hY : 0 ≤ Y) :
    let T := fun b => buildMovingSlotData n
      (frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t))
      (small b) (bulkSlotLeaves n m slot) (a b)
    (Fintype.card (TreeLeafIndex n × Fin m → (ZMod (R ^ (n - 1 + 2)))ˣ) : ℝ)⁻¹ *
        (∑ z : TreeLeafIndex n × Fin m → (ZMod (R ^ (n - 1 + 2)))ˣ,
          ‖frozenBulkFrequencyFactor base slot outside F E T childBound R
            (R ^ (n - 1 + 2)) input Q Y z‖) ≤
      2 * ((‖movingDataWeight (F false) (E false) (T false)‖ *
        ‖movingDataWeight (F true) (E true) (T true)‖) *
      ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod) := by
  intro T
  apply le_trans _ (frequencyModelBulkPage_mean_le base tier S n m R t hS hR slot small a
    hslot hsmall ha hbase F E N D hD hN hdiv hm input Q Y hY)
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_le_sum
  intro z _
  unfold frozenBulkFrequencyFactor
  split_ifs
  · rw [one_mul]
  · simpa only [zero_mul, norm_zero] using norm_nonneg
      (movingFrequencyCorePageAverage (Function.extend slot (fun j => (z j).val.val) base)
        F E T R (R ^ (n - 1 + 2)) input Q Y)

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_HarmonicPairIntegral
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem norm_harmonic_pair_integral_le (u v r s C : ℝ) (hu : 1 ≤ u) (hr : 1 ≤ r)
    (huv : u ≤ v) (hrs : r ≤ s) (hv : v ≤ u + 1) (hs : s ≤ r + 1)
    (hC : 0 ≤ C) (F : ℝ → ℝ → ℂ)
    (hF : ∀ x ∈ Set.Ioc u v, ∀ y ∈ Set.Ioc r s, ‖F x y‖ ≤ C) :
    ‖∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
      F x y / ((x : ℂ) * (y : ℂ))‖ ≤ C / (u * r) := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hpoint (x : ℝ) (hx : x ∈ Set.Ioc u v) (y : ℝ) (hy : y ∈ Set.Ioc r s) :
      ‖F x y / ((x : ℂ) * (y : ℂ))‖ ≤ C / (u * r) := by
    have hx0 := hu0.trans hx.1
    have hy0 := hr0.trans hy.1
    simp only [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hx0, abs_of_pos hy0]
    exact (div_le_div_of_nonneg_right (hF x hx y hy) (mul_nonneg hx0.le hy0.le)).trans
      (div_le_div_of_nonneg_left hC (mul_pos hu0 hr0)
        (mul_le_mul hx.1.le hy.1.le hr0.le hx0.le))
  have hin (x : ℝ) (hx : x ∈ Set.Ioc u v) :=
    norm_setIntegral_le_of_norm_le_const (μ := volume) measure_Ioc_lt_top (hpoint x hx)
  simp only [Real.volume_real_Ioc_of_le hrs] at hin
  have hout := norm_setIntegral_le_of_norm_le_const (μ := volume) measure_Ioc_lt_top hin
  rw [Real.volume_real_Ioc_of_le huv] at hout
  calc
    _ ≤ (C / (u * r) * (s - r)) * (v - u) := hout
    _ ≤ C / (u * r) * 1 * 1 := by gcongr <;> linarith
    _ = _ := by ring

/-- A finite signed average is integrated before its norm is bounded. This
retains cancellation in the arithmetic coefficient on each giant cell. -/
theorem finite_harmonic_pair_sum_norm {A : Type*} [Fintype A]
    (u v r s C : ℝ) (hu : 1 ≤ u) (hr : 1 ≤ r)
    (huv : u ≤ v) (hrs : r ≤ s) (hv : v ≤ u + 1) (hs : s ≤ r + 1)
    (hC : 0 ≤ C) (w : A → ℂ) (F : A → ℝ → ℝ → ℂ)
    (hmeas : ∀ a, Measurable (Function.uncurry (F a)))
    (K : A → ℝ) (hK : ∀ a, 0 ≤ K a)
    (hbound : ∀ a x, x ∈ Set.Ioc u v → ∀ y, y ∈ Set.Ioc r s → ‖F a x y‖ ≤ K a)
    (hmean : ∀ x ∈ Set.Ioc u v, ∀ y ∈ Set.Ioc r s, ‖∑ a, w a * F a x y‖ ≤ C) :
    ‖∑ a, w a * ∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
      F a x y / ((x : ℂ) * (y : ℂ))‖ ≤ C / (u * r) := by
  let box := Set.Ioc u v ×ˢ Set.Ioc r s
  let H := fun a (z : ℝ × ℝ) => box.indicator
    (fun z => w a * F a z.1 z.2 / ((z.1 : ℂ) * (z.2 : ℂ))) z
  have hH (a : A) : Measurable (H a) := by
    apply Measurable.indicator _ (measurableSet_Ioc.prod measurableSet_Ioc)
    exact (measurable_const.mul (hmeas a)).div
      ((Complex.continuous_ofReal.measurable.comp measurable_fst).mul
        (Complex.continuous_ofReal.measurable.comp measurable_snd))
  have hnorm (a : A) (z : ℝ × ℝ) : ‖H a z‖ ≤ ‖w a‖ * K a / (u * r) := by
    by_cases hz : z ∈ box
    · obtain ⟨hx, hy⟩ := hz
      have hx0 : 0 < z.1 := (lt_of_lt_of_le zero_lt_one hu).trans hx.1
      have hy0 : 0 < z.2 := (lt_of_lt_of_le zero_lt_one hr).trans hy.1
      simp only [H, Set.indicator_of_mem (show z ∈ box from ⟨hx, hy⟩), norm_div,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0, abs_of_pos hy0]
      exact (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hbound a z.1 hx z.2 hy) (norm_nonneg _))
        (mul_nonneg hx0.le hy0.le)).trans
        (div_le_div_of_nonneg_left (mul_nonneg (norm_nonneg _) (hK a)) (by positivity)
          (mul_le_mul hx.1.le hy.1.le (by linarith) hx0.le))
    · rw [show H a z = 0 from Set.indicator_of_notMem hz _]
      simp only [norm_zero]
      exact div_nonneg (mul_nonneg (norm_nonneg _) (hK a)) (by linarith [mul_pos (lt_of_lt_of_le zero_lt_one hu) (lt_of_lt_of_le zero_lt_one hr)])
  let μ := volume.restrict (Set.Ioc u v)
  let ν := volume.restrict (Set.Ioc r s)
  have hp (a : A) : Integrable (H a) (μ.prod ν) :=
    ⟨(hH a).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall (hnorm a))⟩
  have hi (a : A) (x : ℝ) : Integrable (fun y => H a (x, y)) ν :=
    ⟨((hH a).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall (fun y => hnorm a (x, y)))⟩
  have hswap := double_integral_finset_sum (Finset.univ : Finset A) μ ν
    (fun a x y => H a (x, y)) (fun a _ => hi a) (fun a _ => (hp a).integral_prod_left)
  have heq (a : A) : (∫ x, ∫ y, H a (x, y) ∂ν ∂μ) =
      w a * ∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
        F a x y / ((x : ℂ) * (y : ℂ)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    dsimp only
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro y hy
    simp only [H, box, Set.indicator_of_mem (show (x, y) ∈ box from ⟨hx, hy⟩)]
    ring
  have hinside : (∫ x, ∫ y, ∑ a, H a (x, y) ∂ν ∂μ) =
      ∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
        (∑ a, w a * F a x y) / ((x : ℂ) * (y : ℂ)) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    apply setIntegral_congr_fun measurableSet_Ioc
    intro y hy
    simp only [H, box, Set.indicator_of_mem (show (x, y) ∈ box from ⟨hx, hy⟩),
      Finset.sum_div]
  simp only [heq] at hswap
  rw [← hswap, hinside]
  exact norm_harmonic_pair_integral_le u v r s C hu hr huv hrs hv hs hC _ hmean

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingArithmeticSumRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original arithmetic error after summing all equality patterns -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem movingInternalArithmeticError_nonneg (n c d : ℕ) (F U α β V : ℝ)
    (hF : 1 ≤ F) (hU : 1 ≤ U) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hV : 0 ≤ V) :
    0 ≤ movingInternalArithmeticError n c d F U α β V := by
  have hbase : 1 ≤ 2 * (F * U ^ d) := by
    have hh := one_le_mul_of_one_le_of_one_le hF (one_le_pow₀ hU (n := d))
    linarith
  have hh := one_le_pow₀ (one_le_pow₀ hbase (n := n + 1)) (n := 2)
  have hlog : 0 ≤ Real.log (2 * ((2 * (F * U ^ d)) ^ (n + 1)) ^ 2) :=
    Real.log_nonneg (by linarith)
  unfold movingInternalArithmeticError
  positivity

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingDiagonalOuterWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining the inactive regular density under the bulk prime average -/

namespace Ostmann
open scoped Classical BigOperators

theorem inactiveRegularDensity_bounds {A σ J : Type*} [Fintype J]
    (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (reg : J → σ) (active : J → Bool) (x : σ → A) :
    0 ≤ inactiveRegularDensity prime reg active x ∧
      inactiveRegularDensity prime reg active x ≤ 1 := by
  have hlocal (j : J) : 0 ≤ (if active j then 1 else 1 - (prime (x (reg j)) : ℝ)⁻¹) ∧
      (if active j then 1 else 1 - (prime (x (reg j)) : ℝ)⁻¹) ≤ 1 := by
    have hp : (1 : ℝ) ≤ prime (x (reg j)) := by exact_mod_cast (hprime _).one_le
    cases active j
    · simp only [Bool.false_eq_true, ite_false, if_false]
      exact ⟨sub_nonneg.mpr ((inv_le_one₀ (by positivity)).mpr hp),
        sub_le_self _ (by positivity)⟩
    · simp
  exact ⟨Finset.prod_nonneg (fun j _ => (hlocal j).1),
    Finset.prod_le_one (fun j _ => (hlocal j).1) (fun j _ => (hlocal j).2)⟩

/-- Inactive factors use only the fixed nonbulk coordinates. -/
theorem inactiveRegularDensity_joinBulkNonbulk {A σ J K : Type*} [Fintype J]
    (prime : A → ℕ) (reg : J → σ) (active : J → Bool) (slot : K ↪ σ)
    (hfixed : ∀ j, active j = false → reg j ∉ Set.range slot)
    (x : σ → A) (z : K → A) :
    inactiveRegularDensity prime reg active (joinBulkNonbulk slot z (fun i => x i)) =
      inactiveRegularDensity prime reg active x := by
  apply Finset.prod_congr rfl
  intro j _
  cases ha : active j
  · have hj : reg j ∉ Set.range slot := hfixed j ha
    have he := joinBulkNonbulk_nonbulk slot z (fun i => x i) ⟨reg j, hj⟩
    simp only [Bool.false_eq_true, ite_false, if_false]
    rw [he]
  · simp only [ite_true, if_true]

theorem diagonalOuterMajorant_pos (B D : ℝ) (diagonal : Bool) :
    0 < diagonalOuterMajorant B D diagonal := by
  unfold diagonalOuterMajorant
  have hs : 0 ≤ giantOuterScalar diagonal := by
    cases diagonal <;> simp [giantOuterScalar, (Real.exp_pos _).le]
  have hh : 0 ≤ (if diagonal then 1 + Real.exp 2 else (2 : ℝ)) := by
    cases diagonal <;> positivity
  positivity

theorem movingDiagonalOuterWeight_norm {A σ J : Type*} [Fintype J]
    (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime) (reg : J → σ) (active : J → Bool)
    (φ : ℝ → ℝ) (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool)
    (u v : ℝ) (x : σ → A) :
    ‖movingDiagonalOuterWeight prime reg active φ Jleft Jright B D diagonal u v x‖ ≤ 1 := by
  have hc := diagonalOuterMajorant_pos B D diagonal
  have hd := inactiveRegularDensity_bounds prime hprime reg active x
  have ho := giantOuterWeight_norm φ Jleft Jright B D hB hD hφ hlip hout diagonal
    (Real.exp u) (Real.exp v)
  unfold movingDiagonalOuterWeight
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hd.1,
    Complex.norm_real, Real.norm_of_nonneg hc.le]
  apply (div_le_one hc).mpr
  calc
    _ ≤ ‖giantOuterWeight φ Jleft Jright diagonal (Real.exp u) (Real.exp v)‖ * 1 :=
      mul_le_mul_of_nonneg_left hd.2 (norm_nonneg _)
    _ ≤ diagonalOuterMajorant B D diagonal := by
      rw [mul_one]
      exact ho.trans (by unfold diagonalOuterMajorant; linarith)

theorem movingDiagonalOuterWeight_measurable {A σ J : Type*} [Fintype J]
    (prime : A → ℕ) (reg : J → σ) (active : J → Bool)
    (φ : ℝ → ℝ) (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (x : σ → A) :
    Measurable (fun z : ℝ × ℝ => movingDiagonalOuterWeight prime reg active φ
      Jleft Jright B D diagonal z.1 z.2 x) := by
  have hm := (measurable_giantOuterWeight φ Jleft Jright B D hB hD hφ hlip hout diagonal).comp
    ((Real.continuous_exp.measurable.comp measurable_fst).prodMk
      (Real.continuous_exp.measurable.comp measurable_snd))
  exact (hm.mul_const _).div_const _

theorem movingDiagonalOuterWeight_bulk {A σ J K : Type*} [Fintype J]
    (prime : A → ℕ) (reg : J → σ) (active : J → Bool) (slot : K ↪ σ)
    (hfixed : ∀ j, active j = false → reg j ∉ Set.range slot)
    (φ : ℝ → ℝ) (Jleft Jright B D : ℝ) (diagonal : Bool)
    (u v : ℝ) (x : σ → A) (z : K → A) :
    movingDiagonalOuterWeight prime reg active φ Jleft Jright B D diagonal u v
      (joinBulkNonbulk slot z (fun i => x i)) =
    movingDiagonalOuterWeight prime reg active φ Jleft Jright B D diagonal u v x := by
  unfold movingDiagonalOuterWeight
  rw [inactiveRegularDensity_joinBulkNonbulk prime reg active slot hfixed]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternCoefficientMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original pattern coefficients as a finite signed linear functional -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingOriginalPatternWeight_eq_coefficient_mul {A B C : Type*} [Fintype B] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (prime : A → ℕ) (n : ℕ) (pattern : Bool × MovingSampleIndex n → C)
    (G : (Fin (N + 1) → A) → ℂ) (x : Fin (N + 1) → A) :
    movingOriginalPatternWeight e μ ν prime n pattern G x =
      movingOriginalPatternWeight e μ ν prime n pattern (fun _ => 1) x * G x := by
  unfold movingOriginalPatternWeight movingPatternInjectionGuard
  split_ifs <;> ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingDiagonalIntegralScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the harmless constant normalization of the diagonal multiplier -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem movingDiagonalOuterWeight_denormalize {A σ J : Type*} [Fintype J]
    (prime : A → ℕ) (reg : J → σ) (active : J → Bool)
    (φ : ℝ → ℝ) (Jleft Jright B D : ℝ) (diagonal : Bool)
    (u v : ℝ) (x : σ → A) :
    (diagonalOuterMajorant B D diagonal : ℂ) *
      movingDiagonalOuterWeight prime reg active φ Jleft Jright B D diagonal u v x =
      giantOuterWeight φ Jleft Jright diagonal (Real.exp u) (Real.exp v) *
        (inactiveRegularDensity prime reg active x : ℂ) := by
  unfold movingDiagonalOuterWeight
  have hc : (diagonalOuterMajorant B D diagonal : ℂ) ≠ 0 := by
    exact_mod_cast (diagonalOuterMajorant_pos B D diagonal).ne'
  exact mul_div_cancel₀ _ hc

/-- The normalized multiplier costs only its fixed outer majorant after both
integrals and the original signed pattern average. -/
theorem movingPattern_diagonal_integral_norm {A B C J : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype J] {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (pattern : Bool × MovingSampleIndex n → C)
    (reg : J → Fin (N + 1)) (active : J → Bool)
    (φ : ℝ → ℝ) (Jleft Jright Bφ Dφ : ℝ) (diagonal : Bool)
    (raw : ℝ → ℝ → (Fin (N + 1) → A) → ℂ)
    (haar : (Fin (N + 1) → A) → ℂ) (u v a b center bound : ℝ)
    (hbound : ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern
      (fun x => ∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
        (movingDiagonalOuterWeight prime reg active φ Jleft Jright Bφ Dφ diagonal z y x *
          raw z y x) * (Real.exp (z - center) : ℂ) / (y : ℂ)) x * haar x‖ ≤ bound) :
    ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern
      (fun x => ∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
        ((giantOuterWeight φ Jleft Jright diagonal (Real.exp z) (Real.exp y) *
          (inactiveRegularDensity prime reg active x : ℂ)) * raw z y x) *
            (Real.exp (z - center) : ℂ) / (y : ℂ)) x * haar x‖ ≤
      diagonalOuterMajorant Bφ Dφ diagonal * bound := by
  let K := diagonalOuterMajorant Bφ Dφ diagonal
  have hK : 0 ≤ K := (diagonalOuterMajorant_pos Bφ Dφ diagonal).le
  have he (x) :
      (∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
        ((giantOuterWeight φ Jleft Jright diagonal (Real.exp z) (Real.exp y) *
          (inactiveRegularDensity prime reg active x : ℂ)) * raw z y x) *
            (Real.exp (z - center) : ℂ) / (y : ℂ)) =
      (K : ℂ) * (∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
        (movingDiagonalOuterWeight prime reg active φ Jleft Jright Bφ Dφ diagonal z y x *
          raw z y x) * (Real.exp (z - center) : ℂ) / (y : ℂ)) := by
    rw [← integral_const_mul]
    congr 1
    funext z
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [← movingDiagonalOuterWeight_denormalize prime reg active φ Jleft Jright Bφ Dφ diagonal z y x]
    change (((K : ℂ) * _) * _) * _ / _ = _
    ring
  let original := fun x => ∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
    ((giantOuterWeight φ Jleft Jright diagonal (Real.exp z) (Real.exp y) *
      (inactiveRegularDensity prime reg active x : ℂ)) * raw z y x) *
        (Real.exp (z - center) : ℂ) / (y : ℂ)
  let normalized := fun x => ∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
    (movingDiagonalOuterWeight prime reg active φ Jleft Jright Bφ Dφ diagonal z y x *
      raw z y x) * (Real.exp (z - center) : ℂ) / (y : ℂ)
  change ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern original x * haar x‖ ≤ _
  change ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern normalized x * haar x‖ ≤ bound at hbound
  have hsum : (∑ x, movingOriginalPatternWeight e μ ν prime n pattern original x * haar x) =
      (K : ℂ) * ∑ x, movingOriginalPatternWeight e μ ν prime n pattern normalized x * haar x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    conv_lhs => rw [movingOriginalPatternWeight_eq_coefficient_mul]
    conv_rhs => rw [movingOriginalPatternWeight_eq_coefficient_mul]
    change _ * (original x) * _ = _ * (_ * normalized x * _)
    have hi : original x = (K : ℂ) * normalized x := he x
    rw [hi]
    ring
  rw [hsum, norm_mul, Complex.norm_real, Real.norm_of_nonneg hK]
  exact mul_le_mul_of_nonneg_left hbound hK

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingKernelTransport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measure transport for the concrete bounded moving kernel -/

namespace Ostmann
open MeasureTheory
open scoped Classical SchwartzMap

theorem measurable_exp_pair_mul (K : ℝ → ℝ → ℂ)
    (hK : Measurable (Function.uncurry K)) (c : ℂ) :
    Measurable (Function.uncurry (fun x y => c * K (Real.exp x) (Real.exp y))) := by
  have he : Measurable (fun z : ℝ × ℝ => (Real.exp z.1, Real.exp z.2)) :=
    (Real.continuous_exp.comp continuous_fst).measurable.prodMk
      (Real.continuous_exp.comp continuous_snd).measurable
  exact measurable_const.mul (hK.comp he)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingLeafAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.movingSampleSlotsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The scalar leaf weights retain the actual frequency cutoff -/

namespace Ostmann
open scoped Classical

theorem movingDataWeight_unit_leaf_bound {σ : Type*}
    (F : {k : ℕ} → MovingSlotData σ k → ℤ → ℂ) (V : ℕ)
    (hF : ∀ s regular, ‖F (.leaf s regular) s‖ ≤ if s.natAbs ≤ V then 1 else 0)
    (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (small bulk : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) :
    ‖movingDataWeight F (fun _ _ _ _ => 1)
      (buildMovingSlotData n (frequencyTreeMap Subtype.val n t) small bulk a)‖ ≤
      frequencyLeafWeight (singleFrequencyLeaf S V) n t := by
  induction a with
  | leaf => exact hF _ _
  | @node n u l r ihL ihR =>
    simp only [buildMovingSlotData, frequencyTreeMap, movingDataWeight,
      Complex.ofReal_one, one_mul, norm_mul, norm_star, frequencyLeafWeight]
    exact mul_le_mul (ihL _ _ _) (ihR _ _ _) (norm_nonneg _)
      (frequencyLeafWeight_nonneg _ (fun _ => by unfold singleFrequencyLeaf; split_ifs <;> norm_num) _ _)

/-- Removing the explicit compensation multipliers leaves a scalar amplitude
of norm at most one whenever the actual leaf coefficients have that bound. -/
theorem movingDataWeight_unit_norm_le_one {σ : Type*}
    (F : {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (hF : ∀ s regular, ‖F (.leaf s regular) s‖ ≤ 1)
    {n : ℕ} (T : MovingSlotData σ n) :
    ‖movingDataWeight F (fun _ _ _ _ => 1) T‖ ≤ 1 := by
  induction T with
  | leaf s regular => exact hF s regular
  | node s CL CR U l r ihL ihR =>
    simp only [movingDataWeight, Complex.ofReal_one, one_mul, norm_mul, norm_star]
    exact (mul_le_mul ihL ihR (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)

theorem frequencyLeafWeight_pair_projection (S : Finset ℤ) (V n : ℕ)
    (t : FrequencyTree (S × S) n) :
    frequencyLeafWeight (singleFrequencyLeaf S V) n (frequencyPairProjection S n false t) *
      frequencyLeafWeight (singleFrequencyLeaf S V) n (frequencyPairProjection S n true t) =
      frequencyLeafWeight (pairedFrequencyLeaf S V) n t := by
  induction n with
  | zero =>
    change (if (t.1 : ℤ).natAbs ≤ V then (1 : ℝ) else 0) *
      (if (t.2 : ℤ).natAbs ≤ V then 1 else 0) = _
    unfold frequencyLeafWeight pairedFrequencyLeaf
    split_ifs <;> simp_all
  | succ n ih =>
    change
      (frequencyLeafWeight (singleFrequencyLeaf S V) n (frequencyPairProjection S n false t.2.1) *
        frequencyLeafWeight (singleFrequencyLeaf S V) n (frequencyPairProjection S n false t.2.2)) *
      (frequencyLeafWeight (singleFrequencyLeaf S V) n (frequencyPairProjection S n true t.2.1) *
        frequencyLeafWeight (singleFrequencyLeaf S V) n (frequencyPairProjection S n true t.2.2)) = _ * _
    rw [show ∀ a b c d : ℝ, (a * b) * (c * d) = (a * c) * (b * d) by intros; ring]
    rw [ih t.2.1, ih t.2.2]

theorem movingDataWeight_pair_unit_leaf_bound {σ : Type*}
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ) (V : ℕ)
    (hF : ∀ b s regular, ‖F b (.leaf s regular) s‖ ≤ if s.natAbs ≤ V then 1 else 0)
    (S : Finset ℤ) (n : ℕ) (t : FrequencyTree (S × S) n)
    (small : Bool → TreeLeafTuple (List σ) n) (bulk : TreeLeafTuple (List σ) n)
    (a : Bool → MovingSampleSlots σ n) :
    let T := fun b => buildMovingSlotData n
      (frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t)) (small b) bulk (a b)
    ‖movingDataWeight (F false) (fun _ _ _ _ => 1) (T false)‖ *
      ‖movingDataWeight (F true) (fun _ _ _ _ => 1) (T true)‖ ≤
      frequencyLeafWeight (pairedFrequencyLeaf S V) n t := by
  intro T
  rw [← frequencyLeafWeight_pair_projection]
  exact mul_le_mul (movingDataWeight_unit_leaf_bound (F false) V (hF false) S n _ _ bulk _)
    (movingDataWeight_unit_leaf_bound (F true) V (hF true) S n _ _ bulk _) (norm_nonneg _)
    (frequencyLeafWeight_nonneg _ (fun _ => by unfold singleFrequencyLeaf; split_ifs <;> norm_num) _ _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternBulkFrozen
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original pattern has fixed nonbulk data under bulk resampling -/

namespace Ostmann
open scoped Classical

theorem movingPatternBulkEmbedding_external_mem {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (slot : (TreeLeafIndex n × Fin m) ↪ B) (b : B) :
    e.symm (.inl b) ∈ Set.range (movingPatternBulkEmbedding e slot) ↔ b ∈ Set.range slot := by
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, Sum.inl.inj (e.symm.injective hj)⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, rfl⟩

theorem movingPatternFiniteSmall_absent {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (small : TreeLeafTuple (List B) n)
    (hsmall : ∀ i ∈ flattenMovingSlots n small, i ∉ Set.range slot) :
    ∀ i ∈ flattenMovingSlots n (movingPatternFiniteSmall e n small),
      i ∉ Set.range (movingPatternBulkEmbedding e slot) := by
  intro i hi
  rw [movingPatternFiniteSmall, flattenMovingSlots_map] at hi
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hi
  exact fun h => hsmall b hb ((movingPatternBulkEmbedding_external_mem e slot b).mp h)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MixedPairIntegral
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite signed averages under the original external integer density -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem finite_mixed_pair_sum_norm {A : Type*} [Fintype A]
    (u v r s center C : ℝ) (hu : 1 ≤ u) (hr : 1 ≤ r)
    (huv : u ≤ v) (hrs : r ≤ s) (hv : v ≤ u + 1) (hs : s ≤ r + 1)
    (hcenter : v ≤ center + 1) (hC : 0 ≤ C) (w : A → ℂ)
    (F : A → ℝ → ℝ → ℂ) (hmeas : ∀ a, Measurable (Function.uncurry (F a)))
    (K : A → ℝ) (hK : ∀ a, 0 ≤ K a)
    (hbound : ∀ a x, x ∈ Set.Ioc u v → ∀ y, y ∈ Set.Ioc r s → ‖F a x y‖ ≤ K a)
    (hmean : ∀ x ∈ Set.Ioc u v, ∀ y ∈ Set.Ioc r s, ‖∑ a, w a * F a x y‖ ≤ C) :
    ‖∑ a, w a * ∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
      F a x y * (Real.exp (x - center) : ℂ) / (y : ℂ)‖ ≤
      (2 * Real.exp 1 * C) / r := by
  let F' := fun a x y => ((x * Real.exp (x - center) : ℝ) : ℂ) * F a x y
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hv0 : 0 ≤ v := hu0.le.trans huv
  have he (x : ℝ) (hx : x ∈ Set.Ioc u v) :
      0 ≤ x * Real.exp (x - center) ∧ x * Real.exp (x - center) ≤ v * Real.exp 1 := by
    have hx0 : 0 ≤ x := hu0.le.trans hx.1.le
    refine ⟨mul_nonneg hx0 (Real.exp_nonneg _), ?_⟩
    exact mul_le_mul hx.2 (Real.exp_le_exp.mpr (by linarith [hx.2]))
      (Real.exp_nonneg _) hv0
  have hm (a : A) : Measurable (Function.uncurry (F' a)) := by
    have hscalar : Measurable (fun z : ℝ × ℝ => ((z.1 * Real.exp (z.1 - center) : ℝ) : ℂ)) := by
      fun_prop
    exact hscalar.mul (hmeas a)
  have hpoint (a : A) (x : ℝ) (hx : x ∈ Set.Ioc u v) (y : ℝ) (hy : y ∈ Set.Ioc r s) :
      ‖F' a x y‖ ≤ (v * Real.exp 1) * K a := by
    dsimp only [F']
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (he x hx).1]
    exact mul_le_mul (he x hx).2 (hbound a x hx y hy) (norm_nonneg _) (by positivity)
  have hmean' (x : ℝ) (hx : x ∈ Set.Ioc u v) (y : ℝ) (hy : y ∈ Set.Ioc r s) :
      ‖∑ a, w a * F' a x y‖ ≤ v * Real.exp 1 * C := by
    have hh : (∑ a, w a * F' a x y) =
        ((x * Real.exp (x - center) : ℝ) : ℂ) * ∑ a, w a * F a x y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      dsimp only [F']
      ring
    rw [hh, norm_mul, Complex.norm_real, Real.norm_of_nonneg (he x hx).1]
    exact mul_le_mul (he x hx).2 (hmean x hx y hy) (norm_nonneg _) (by positivity)
  have hh := finite_harmonic_pair_sum_norm u v r s (v * Real.exp 1 * C)
    hu hr huv hrs hv hs (by positivity) w F' hm
    (fun a => (v * Real.exp 1) * K a) (fun a => mul_nonneg (by positivity) (hK a))
    hpoint hmean'
  have heq (a : A) : (∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
      F a x y * (Real.exp (x - center) : ℂ) / (y : ℂ)) =
      ∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s, F' a x y / ((x : ℂ) * (y : ℂ)) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    apply setIntegral_congr_fun measurableSet_Ioc
    intro y hy
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (hu0.trans hx.1)
    have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (hr0.trans hy.1)
    dsimp only [F']
    push_cast
    field_simp
  simp_rw [heq]
  apply hh.trans
  have hratio : v / u ≤ 2 := (div_le_iff₀ hu0).mpr (by linarith)
  calc
    v * Real.exp 1 * C / (u * r) = (v / u) * (Real.exp 1 * C / r) := by ring
    _ ≤ 2 * (Real.exp 1 * C / r) :=
      mul_le_mul_of_nonneg_right hratio (div_nonneg (mul_nonneg (Real.exp_nonneg _) hC) hr0.le)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternMixedHarmonicIntegral
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing the signed original-pattern bound through both giant cells -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem movingPattern_mixed_harmonic_integral_bound {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C)
    (G : (Fin (N + 1) → A) → ℝ → ℝ → ℂ)
    (hG : ∀ x, Measurable (Function.uncurry (G x)))
    (u v r s center D : ℝ) (hu : 1 ≤ u) (hr : 1 ≤ r)
    (huv : u ≤ v) (hrs : r ≤ s) (hv : v ≤ u + 1) (hs : s ≤ r + 1) (hcenter : v ≤ center + 1) (hD : 0 ≤ D)
    (K : (Fin (N + 1) → A) → ℝ) (hK : ∀ x, 0 ≤ K x)
    (hbound : ∀ x a, a ∈ Set.Ioc u v → ∀ b, b ∈ Set.Ioc r s → ‖G x a b‖ ≤ K x)
    (hmean : ∀ a ∈ Set.Ioc u v, ∀ b ∈ Set.Ioc r s,
      ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern (fun x => G x a b) x *
        movingPatternHaarProduct e prime hprime n t small bulk pattern x‖ ≤ D) :
    ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern
        (fun x => ∫ a in Set.Ioc u v, ∫ b in Set.Ioc r s,
          G x a b * (Real.exp (a - center) : ℂ) / (b : ℂ)) x *
      movingPatternHaarProduct e prime hprime n t small bulk pattern x‖ ≤ (2 * Real.exp 1 * D) / r := by
  let w := movingOriginalPatternWeight e μ ν prime n pattern (fun _ => 1)
  let H := movingPatternHaarProduct e prime hprime n t small bulk pattern
  have hpoint (a : ℝ) (ha : a ∈ Set.Ioc u v) (b : ℝ) (hb : b ∈ Set.Ioc r s) :
      ‖∑ x, w x * (G x a b * H x)‖ ≤ D := by
    have he (x) : movingOriginalPatternWeight e μ ν prime n pattern (fun x => G x a b) x * H x =
        w x * (G x a b * H x) := by
      rw [movingOriginalPatternWeight_eq_coefficient_mul]
      exact mul_assoc _ _ _
    have hm := hmean a ha b hb
    change ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern (fun x => G x a b) x * H x‖ ≤ D at hm
    simpa only [he] using hm
  have h := finite_mixed_pair_sum_norm u v r s center D hu hr huv hrs hv hs hcenter hD w
    (fun x a b => G x a b * H x) (fun x => (hG x).mul_const (H x))
    (fun x => K x * ‖H x‖) (fun x => mul_nonneg (hK x) (norm_nonneg _))
    (by
      intro x a ha b hb
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hbound x a ha b hb) (norm_nonneg _)) hpoint
  have he (x) : movingOriginalPatternWeight e μ ν prime n pattern
        (fun x => ∫ a in Set.Ioc u v, ∫ b in Set.Ioc r s,
          G x a b * (Real.exp (a - center) : ℂ) / (b : ℂ)) x * H x =
      w x * ∫ a in Set.Ioc u v, ∫ b in Set.Ioc r s,
        (G x a b * H x) * (Real.exp (a - center) : ℂ) / (b : ℂ) := by
    rw [movingOriginalPatternWeight_eq_coefficient_mul]
    simp_rw [show ∀ a b : ℝ, (G x a b * H x) * (Real.exp (a - center) : ℂ) / (b : ℂ) =
      (G x a b * (Real.exp (a - center) : ℂ) / (b : ℂ)) * H x by intros; ring, integral_mul_const]
    exact mul_assoc _ _ _
  change ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern
    (fun x => ∫ a in Set.Ioc u v, ∫ b in Set.Ioc r s,
      G x a b * (Real.exp (a - center) : ℂ) / (b : ℂ)) x * H x‖ ≤ _
  simpa only [he] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HistoryRealEvaluation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real evaluation of the original cleared history formulas -/

namespace Ostmann.HistoryFormula
open scoped Classical BigOperators

theorem realEval_bind {σ τ : Type*} (F : HistoryFormula σ) (f : σ → HistoryFormula τ)
    (x : τ → ℝ) : (F.bind f).realEval x = F.realEval (fun i => (f i).realEval x) := by
  induction F with
  | prime i => simp only [bind, realEval_prime]
  | external z => simp only [bind, realEval_external]
  | product l r hl hr => simp only [bind, realEval_product, hl, hr]
  | solve l r v w s hs hl hr => simp only [bind, realEval_solve, hl, hr]

theorem realEval_listProduct {σ : Type*} (fs : List (HistoryFormula σ)) (x : σ → ℝ) :
    (listProduct fs).realEval x = (fs.map (fun F => F.realEval x)).prod := by
  induction fs with
  | nil => simp [listProduct]
  | cons f fs ih => simp only [listProduct, realEval_product, List.map_cons, List.prod_cons, ih]

end Ostmann.HistoryFormula

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RealNodeSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original real node inequalities with variable bulk values -/

namespace Ostmann
open scoped Classical

theorem MovingSlotReversal.giantFormula_realEval {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℕ) (hs : s.rootFrequency ≠ 0)
    (hu : MovingSlotReversal.naturalProduct value s.compensationSlots ≠ 0)
    (L R : HistoryFormula Bool) (x : Bool → ℝ) :
    (s.giantFormula value hs hu L R).realEval x =
      s.realValuePivot (fun i => (value i : ℝ)) (L.realEval x) (R.realEval x) := by
  simp only [giantFormula, HistoryFormula.realEval_solve, HistoryFormula.realEval_product,
    HistoryFormula.realEval_external, Int.cast_mul, Int.cast_natCast, realValuePivot,
    realSlotProduct_nat]
  ring

theorem movingNodeGuard_realEval (CL CR : ℕ) (s v w : ℤ) (hs : s ≠ 0)
    (childBound pivotBound : ℕ) (L R : HistoryFormula Bool) (x : Bool → ℝ) :
    (movingNodeGuard CL CR s v w hs childBound pivotBound L R).archimedeanAt x ↔
      1 ≤ ((v : ℝ) * (CR : ℝ) * R.realEval x - (w : ℝ) * (CL : ℝ) * L.realEval x) / s ∧
      ((v : ℝ) * (CR : ℝ) * R.realEval x - (w : ℝ) * (CL : ℝ) * L.realEval x) / s ≤ pivotBound ∧
      ((2 * pivotBound * childBound + 1 : ℕ) : ℝ) ≤ R.realEval x * CR := by
  simp only [movingNodeGuard, wordTransferGuard, WordTransferGuard.archimedeanAt,
    HistoryFormula.realEval_bind, HistoryPivotStep.formula, wordTransferStep, movingNodeWord,
    HistoryFormula.realEval_solve, HistoryFormula.realEval_listProduct, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, HistoryFormula.realEval_prime, Bool.false_eq_true, ite_false, if_false,
    ite_true, if_true, HistoryFormula.realEval_product, HistoryFormula.realEval_external, Int.cast_natCast, mul_one]
  ring_nf

/-- Exact agreement with all original archimedean formula-node tests. -/
theorem realValueNodeSupport_nat {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0))
    (L R : HistoryFormula Bool) (x : Bool → ℝ) :
    movingArchimedeanGate (T.formulaNodes value hvalue childBound pivotBound hf L R) x ↔
      realValueNodeSupport (fun i => (value i : ℝ)) childBound pivotBound T (L.realEval x) (R.realEval x) := by
  induction T generalizing L R with
  | leaf => simp [MovingSlotData.formulaNodes, movingArchimedeanGate, realValueNodeSupport]
  | node s CL CR u left right ihL ihR =>
    simp only [MovingSlotData.formulaNodes, movingArchimedeanGate, List.forall_mem_cons,
      List.forall_mem_append, realValueNodeSupport]
    rw [show (∀ f ∈ left.formulaNodes value hvalue childBound pivotBound hf.2.1
          ((MovingSlotData.step s CL CR u left right false).giantFormula value hf.1
            (MovingSlotReversal.naturalProduct_ne_zero value hvalue u) L R) L, f.guard.archimedeanAt x) ↔ _ from
      ihL hf.2.1 _ L,
      show (∀ f ∈ right.formulaNodes value hvalue childBound pivotBound hf.2.2
          ((MovingSlotData.step s CL CR u left right false).giantFormula value hf.1
            (MovingSlotReversal.naturalProduct_ne_zero value hvalue u) L R) R, f.guard.archimedeanAt x) ↔ _ from
      ihR hf.2.2 _ R]
    rw [movingNodeGuard_realEval]
    simp only [MovingSlotReversal.giantFormula_realEval, MovingSlotReversal.realCompositePivot,
      MovingSlotData.step, realSlotProduct_nat]
    tauto

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RealBulkKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full original kernel on real bulk coordinates -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap ComplexConjugate

/-- The real extension has precisely the old arithmetic gates and windows. -/
theorem realValueSupportFlag_nat {σ : Type*} (value : σ → ℕ) (hv : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) (X lo hi L R : ℝ) :
    realValueSupportFlag (fun i => (value i : ℝ)) childBound pivotBound T X lo hi L R =
      movingRealGateWeight value T
        (T.formulaNodes value hv childBound pivotBound hf (.prime false) (.prime true))
        X lo hi (topGiantReal L R) := by
  have hn := realValueNodeSupport_nat value hv childBound pivotBound T hf
    (.prime false) (.prime true) (topGiantReal L R)
  simp only [HistoryFormula.realEval_prime, topGiantReal, Bool.false_eq_true, ite_false, if_false, ite_true, if_true] at hn
  simp only [realValueSupportFlag, realValueFullSupport, movingRealGateWeight,
    movingArchimedeanFlag, movingRealWindowFlag, MovingSlotData.realValueLeafModuli_nat,
    topGiantReal, Bool.false_eq_true, ite_false, if_false, ite_true, if_true]
  rw [hn]
  split_ifs <;> simp_all

theorem realValueKernel_nat {σ : Type*} (value : σ → ℕ) (hv : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ) (L R : ℝ) :
    realValueKernel (fun i => (value i : ℝ)) childBound pivotBound T ψ X lo hi hlo hhi φ G L R =
      movingRealKernel value T
        (T.formulaNodes value hv childBound pivotBound hf (.prime false) (.prime true))
        ψ X lo hi hlo hhi φ G L R := by
  rw [realValueKernel, realValueSupportFlag_nat value hv childBound pivotBound T hf,
    realValueSmoothWeight_nat]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RealBulkKernelPair
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original paired kernel as a bounded measurable bulk integrand -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap ComplexConjugate

theorem realValueKernelPair_nat {σ : Type*} (value : σ → ℕ) (hv : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : Bool → MovingSlotData σ n)
    (hf : ∀ b, (T b).Frequencies (· ≠ 0)) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ) (L R : ℝ) :
    realValueKernelPair (fun i => (value i : ℝ)) childBound pivotBound T ψ X lo hi hlo hhi φ G L R =
      movingRealKernelPair value T
        (fun b => (T b).formulaNodes value hv childBound pivotBound (hf b) (.prime false) (.prime true))
        ψ X lo hi hlo hhi φ G L R := by
  rw [realValueKernelPair, realValueKernel_nat value hv childBound pivotBound (T false) (hf false),
    realValueKernel_nat value hv childBound pivotBound (T true) (hf true)]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternKernelNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit size of the actual sharp bulk kernel -/

namespace Ostmann
open scoped Classical SchwartzMap

/-- The bound used in prime replacement is explicit, rather than an
unspecified boundedness constant of the constructed integrand. -/
theorem realValueKernelPair_norm_le {σ : Type*}
    (value : σ → ℝ) (i : σ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n)
    (hcomp : ∀ b, (T b).CompensationAbsent i)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : ∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V))
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (L R : ℝ) :
    ‖realValueKernelPair value childBound pivotBound T ψ X lo hi hlo hhi φ G L R‖ ≤
      (movingFourierVariationBudget ψ V lo hi n *
        (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 := by
  have hb (b) := realValueKernel_norm value i childBound pivotBound (T b) (hcomp b)
    ψ X lo hi V hlo hhi (hV b) φ G B D hB hD hφ hlip hout L R
  have hpos := (norm_nonneg _).trans (hb false)
  rw [realValueKernelPair, norm_mul, Complex.norm_conj, pow_two]
  exact mul_le_mul (hb false) (hb true) (norm_nonneg _) hpos

theorem movingPattern_kernel_norm_le {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (value : Fin (N + 1) → ℝ) (childBound pivotBound : ℕ → ℕ)
    (j₀ : TreeLeafIndex n × Fin m) (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ V)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (L R : ℝ) :
    ‖realValueKernelPair value childBound pivotBound
      (movingPatternFinBulkData e n m t small slot perm pattern) ψ X lo hi hlo hhi φ G L R‖ ≤
      (movingFourierVariationBudget ψ V lo hi n *
        (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 :=
  realValueKernelPair_norm_le value (movingPatternBulkEmbedding e slot j₀) childBound pivotBound _
    (fun b => movingPatternFinBulkData_compensationAbsent e tierB tierC n m t small slot perm pattern hB htier b j₀)
    ψ X lo hi V hlo hhi
    (movingPatternFinBulkData_frequencies e t small slot perm pattern (fun s => |(s : ℝ)| ≤ V) hfreq)
    φ G Bφ Dφ hBφ hDφ hφ hlip hout L R

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternPrimeObservable
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal prime observable in the original nonbulk Fubini formula -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

section
variable {B C I : Type*} [Fintype I] {N n m : ℕ}
  (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
  (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
  (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
  (pattern : Bool × MovingSampleIndex n → C)
  (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
  (childBound pivotBound : ℕ → ℕ)
  (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
  (F : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℂ)
  (E : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℤ → ℤ → ℝ)
  (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
  (p : I → ℕ) [∀ i, Fact (p i).Prime] (g : ∀ i, ZMod (p i) → ℂ)
  (twist : ∀ i, Bool → (ZMod (p i))ˣ) (P : PublishedProgressionInput) (Q : ℕ) (y : ℝ)
  (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
  (φ : ℝ → ℝ) (G : ℕ → ℝ) (L U : ℝ)

theorem movingPatternPrimeObservable_join (base : Fin (N + 1) → primes)
    (z : TreeLeafIndex n × Fin m → primes) :
    movingPatternPrimeObservable e t small slot perm pattern primes hprimes
      childBound pivotBound hfreq F E outside R r p g twist P Q y ψ X lo hi hlo hhi φ G L U
      (joinBulkNonbulk (movingPatternBulkEmbedding e slot) z (fun i => base i)) =
    movingPatternPrimeBulkHaar e t small slot perm pattern (fun i => (base i : ℕ)) primes
      hprimes (fun i _ => hprimes _ (base i).property) childBound pivotBound hfreq F E outside
      R r p g twist P Q y ψ X lo hi hlo hhi φ G L U z := by
  have hv : (fun i => (joinBulkNonbulk (A := primes) (movingPatternBulkEmbedding e slot) z
      (fun j => base j) i : ℕ)) =
      primeBulkValues (fun i => (base i : ℕ)) (movingPatternBulkEmbedding e slot) z := by
    funext i
    by_cases hi : i ∈ Set.range (movingPatternBulkEmbedding e slot)
    · obtain ⟨j, rfl⟩ := hi
      rw [joinBulkNonbulk_bulk, primeBulkValues_at]
    · rw [joinBulkNonbulk_nonbulk (movingPatternBulkEmbedding e slot) z
        (fun j => base j) ⟨i, hi⟩, primeBulkValues_off _ _ _ i hi]
  let eval : {v : Fin (N + 1) → ℕ // ∀ i, v i ≠ 0} → ℂ := fun v =>
    let data := movingPatternFinBulkData e n m t small slot perm pattern
    let nodes := fun b => (data b).formulaNodes v.val v.property childBound pivotBound
      (movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hfreq b)
      (.prime false) (.prime true)
    movingRealKernelPair v.val data nodes ψ X lo hi hlo hhi φ G L U *
      (movingFrequencyPageAverage v.val outside F E data nodes R r P Q y *
        ∏ i, movingSpectatorHaarAverage v.val (p i) (g i) (twist i) data)
  let left : {v : Fin (N + 1) → ℕ // ∀ i, v i ≠ 0} :=
    ⟨fun i => (joinBulkNonbulk (A := primes) (movingPatternBulkEmbedding e slot) z
        (fun j => base j) i : ℕ),
      fun i => (hprimes _ ((joinBulkNonbulk (A := primes)
        (movingPatternBulkEmbedding e slot) z (fun j => base j)) i).property).ne_zero⟩
  let right : {v : Fin (N + 1) → ℕ // ∀ i, v i ≠ 0} :=
    ⟨primeBulkValues (fun i => (base i : ℕ)) (movingPatternBulkEmbedding e slot) z,
      fun i => (primeBulkValues_prime (fun i => (base i : ℕ))
        (movingPatternBulkEmbedding e slot) z hprimes
        (fun i _ => hprimes _ (base i).property) i).ne_zero⟩
  change eval left = eval right
  exact congrArg eval (Subtype.ext hv)

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_PrimePairHaarRegularity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem continuous_pageGiantWeight (P : PublishedProgressionInput) (Q q a : ℕ) :
    Continuous (pageGiantWeight P Q q a) := by
  unfold pageGiantWeight pageMultiplier
  fun_prop

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MixedPairHaarRegularity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Regularity of the retained mixed-prime mean -/

namespace Ostmann
open scoped Classical BigOperators

theorem continuous_correctedMixedPairAverage (P : PublishedProgressionInput) (Q q : ℕ)
    [NeZero q] (c : ℕ → ℕ → ℂ) :
    Continuous (correctedMixedPairAverage P Q q c) := by
  unfold correctedMixedPairAverage
  apply continuous_const.mul
  apply continuous_finsetSum
  intro z _
  exact continuous_const.mul (continuous_pageGiantWeight P Q q _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternMixedMeasurable
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurability of the original two-prime pattern integrand -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap

section
variable {B C I : Type*} [Fintype I] {N n m : ℕ}
  (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
  (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
  (perm : Equiv.Perm (TreeLeafIndex n × Fin m)) (pattern : Bool × MovingSampleIndex n → C)
  (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
  (childBound pivotBound : ℕ → ℕ)
  (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
  (F : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℂ)
  (E : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℤ → ℤ → ℝ)
  (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
  (p : I → ℕ) [∀ i, Fact (p i).Prime] (g : ∀ i, ZMod (p i) → ℂ)
  (twist : ∀ i, Bool → (ZMod (p i))ˣ) (input : PublishedProgressionInput) (Q : ℕ)
  (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
  (φ : ℝ → ℝ) (G : ℕ → ℝ)

theorem movingPatternPrimeObservable_measurable
    (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (x : Fin (N + 1) → primes) :
    Measurable (fun z : ℝ × ℝ =>
      movingPatternPrimeObservable e t small slot perm pattern primes hprimes
        childBound pivotBound hfreq F E outside R r p g twist input Q z.2
        ψ X lo hi hlo hhi φ G (Real.exp z.1) (Real.exp z.2) x) := by
  let value := fun i => (x i : ℕ)
  let T := movingPatternFinBulkData e n m t small slot perm pattern
  let hf := movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hfreq
  let nodes := fun b => (T b).formulaNodes value
    (fun i => (hprimes _ (x i).property).ne_zero) childBound pivotBound (hf b)
    (.prime false) (.prime true)
  have hk := measurable_exp_pair_mul (movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G)
    (measurable_movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G
      Bφ Dφ hBφ hDφ hφ hlip hout) (1 : ℂ)
  simp only [one_mul] at hk
  have ha := (continuous_correctedMixedPairAverage input Q r
    (fun a b => movingFrequencyPairFactor value outside F E T nodes R a b)).measurable.comp (show Measurable (Prod.snd : ℝ × ℝ → ℝ) from measurable_snd)
  change Measurable (fun z : ℝ × ℝ =>
    movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G (Real.exp z.1) (Real.exp z.2) *
      (movingFrequencyPageAverage value outside F E T nodes R r input Q z.2 *
        ∏ i, movingSpectatorHaarAverage value (p i) (g i) (twist i) T))
  exact hk.mul (ha.mul measurable_const)

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternFrequencyModulus
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual pattern denominator satisfies the frequency-model requirements -/

namespace Ostmann
open scoped Classical

theorem movingPattern_frequencyProduct_dvd {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (S : Finset ℤ) (t : FrequencyTree (S × S) n)
    (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m)) (pattern : Bool × MovingSampleIndex n → C)
    (b : Bool) :
    (movingPatternFinBulkData e n m
      (fun side => frequencyTreeMap Subtype.val n (frequencyPairProjection S n side t))
      small slot perm pattern b).frequencyProduct ∣ (frequencyModelBase S n t : ℤ) := by
  apply Int.natAbs_dvd.mp
  apply Int.natCast_dvd_natCast.mpr
  rw [movingPatternFinBulkData_build, buildMovingSlotData_frequencyProduct_abs]
  cases b
  · exact dvd_mul_right _ _
  · exact dvd_mul_left _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternSpectatorUnits
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The spectator unit conditions from the actual pattern coordinates -/

namespace Ostmann
open scoped Classical

theorem movingSlotValues_unit {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (n : ℕ) (small : TreeLeafTuple (List σ) n)
    (h : ∀ i ∈ flattenMovingSlots n small, (value i : ZMod q) ≠ 0) :
    ((treeLeafProduct n (movingSlotValues value n small) : ℕ) : ZMod q) ≠ 0 := by
  rw [← movingSlotValues_flatten, MovingSlotReversal.naturalProduct, Nat.cast_list_prod, List.map_map]
  apply List.prod_ne_zero
  intro hz
  obtain ⟨i, hi, he⟩ := List.mem_map.mp hz
  exact h i hi he

theorem MovingSampleSlots.values_units_of_coordinates {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) {n : ℕ} (samples : MovingSampleSlots σ n)
    (h : ∀ i, (value (movingSampleCoordinates σ n samples i) : ZMod q) ≠ 0) :
    (samples.values value).UnitsAt q := by
  induction samples with
  | leaf => trivial
  | @node n u l r ihL ihR =>
    refine ⟨?_, ihL (fun i => h (.inr (true, i))), ihR (fun i => h (.inr (false, i)))⟩
    rw [← movingCompensationValues_product]
    apply movingSlotValues_unit
    apply movingCompensationSlots_forall
    intro a j
    exact h (.inl (a, j))

theorem movingPatternFiniteSamples_units {B C : Type*} {N n q : ℕ} [Fact q.Prime]
    (e : Fin (N + 1) ≃ B ⊕ C) (value : Fin (N + 1) → ℕ)
    (pattern : Bool × MovingSampleIndex n → C)
    (h : ∀ c, (value (e.symm (.inr c)) : ZMod q) ≠ 0) (b : Bool) :
    ((movingPatternFiniteSamples e n pattern b).values value).UnitsAt q := by
  apply MovingSampleSlots.values_units_of_coordinates
  intro i
  simpa only [movingPatternFiniteSamples, movingPatternSamples, Equiv.apply_symm_apply,
    Function.comp_apply] using h (pattern (b, i))

theorem movingPatternFiniteSmall_unit {B C : Type*} {N n q : ℕ} [Fact q.Prime]
    (e : Fin (N + 1) ≃ B ⊕ C) (value : Fin (N + 1) → ℕ)
    (small : TreeLeafTuple (List B) n)
    (h : ∀ b ∈ flattenMovingSlots n small, (value (e.symm (.inl b)) : ZMod q) ≠ 0) :
    ((treeLeafProduct n (movingSlotValues value n (movingPatternFiniteSmall e n small)) : ℕ) : ZMod q) ≠ 0 := by
  apply movingSlotValues_unit
  intro i hi
  rw [movingPatternFiniteSmall, flattenMovingSlots_map] at hi
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hi
  exact h b hb

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternMixedNormalizedNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mixed arithmetic norm with distinct giant and bulk Page cutoffs -/

namespace Ostmann
open scoped Classical BigOperators

section
variable {σ I : Type*} [Fintype I] (base : σ → ℕ) (tier : σ → ℕ) (S : Finset ℤ) (n m R : ℕ)
  [NeZero (R ^ (n - 1 + 2))] (t : FrequencyTree (S × S) n)
  (hS : ∀ s ∈ S, s ≠ 0) (hR : ∀ b (j : Fin (2 ^ n - 1)),
    (singleTreeNodeFrequencies S n (frequencyPairProjection S n b t) j.val).root.natAbs ∣ R)
  (slot : (TreeLeafIndex n × Fin m) ↪ σ)
  (small : Bool → TreeLeafTuple (List σ) n) (a : Bool → MovingSampleSlots σ n)
  (hslot : ∀ j, n ≤ tier (slot j))
  (hsmall : ∀ b i, i ∈ flattenMovingSlots n (small b) → i ∉ Set.range slot)
  (ha : ∀ b, (a b).Levels tier)
  (hbase : ∀ i ∉ Set.range slot, IsCoprime (base i : ℤ) (R : ℤ))
  (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
  (E : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℤ → ℤ → ℝ)
  (N : ℕ) (D : ℝ) (hD : 0 ≤ D) (hN : ∀ s ∈ S, s.natAbs ≤ N)
  (hdiv : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D)
  (hm : 0 < m)

include hslot hsmall ha hbase hS hR hD hN hdiv hm in
/-- The nonnegative original arithmetic model retains the frequency saving,
the absolute spectator moments and the exact number of bulk Page factors. -/
theorem frozenArithmetic_same_assignment_mixed_norm
    (p : I → ℕ) [∀ i, Fact (p i).Prime]
    [NeZero (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i)]
    (hc : Pairwise (fun i j => (bulkResidueModuli (R ^ (n - 1 + 2)) p i).Coprime
      (bulkResidueModuli (R ^ (n - 1 + 2)) p j)))
    (hp : ∀ i, 3 ≤ p i)
    (hfreq : ∀ i b, movingGiantFrequencyUnits (p i) n
      (frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t)))
    (hsmallp : ∀ i b, ((treeLeafProduct n (movingSlotValues base n (small b)) : ℕ) : ZMod (p i)) ≠ 0)
    (hasamples : ∀ i b, ((a b).values base).UnitsAt (p i))
    (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (henergy : ∀ i, ∑ x : ZMod (p i), ‖g i x‖ ^ 2 ≤ (p i : ℝ))
    (twist : ∀ i, Bool → (ZMod (p i))ˣ)
    (outside : List ℕ) (childBound : ℕ → ℕ) (input : PublishedProgressionInput) (Qfreq Qbulk : ℕ)
    (Y : ℝ) (hY : 0 ≤ Y) (Ybulk : TreeLeafIndex n × Fin m → ℝ) (hYbulk : ∀ j, 0 ≤ Ybulk j) :
    let ts := fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t)
    let T := fun b => buildMovingSlotData n (ts b) (small b) (bulkSlotLeaves n m slot) (a b)
    let Freq := frozenBulkFrequencyFactor base slot outside F E T childBound R
      (R ^ (n - 1 + 2)) input Qfreq Y
    let Spec := fun i => frozenBulkSpectatorHaar base n m ts small a (twist i) (Equiv.refl _) (g i)
    (Fintype.card (TreeLeafIndex n × Fin m →
      (ZMod (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i))ˣ) : ℝ)⁻¹ *
      (∑ x : TreeLeafIndex n × Fin m →
          (ZMod (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i))ˣ,
        ‖(Freq (bulkResidueEquiv (R ^ (n - 1 + 2)) p hc x).1 *
          ∏ j, pageGiantWeight input Qbulk (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i)
            (x j).val.val (Ybulk j)) *
          ∏ i, Spec i ((bulkResidueEquiv (R ^ (n - 1 + 2)) p hc x).2 i)‖) ≤
      (2 : ℝ) ^ (2 ^ n * m) *
        ((2 * ((‖movingDataWeight (F false) (E false) (T false)‖ *
          ‖movingDataWeight (F true) (E true) (T true)‖) *
          ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod)) *
        (3 : ℝ) ^ (2 ^ n * Fintype.card I)) := by
  intro ts T Freq Spec
  let B := 2 * ((‖movingDataWeight (F false) (E false) (T false)‖ *
    ‖movingDataWeight (F true) (E true) (T true)‖) *
    ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod)
  have hprob : 0 ≤ ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod := by
    apply List.prod_nonneg
    intro c hc
    obtain ⟨f, _, rfl⟩ := List.mem_map.mp hc
    exact pairFrequencySupportBound_nonneg D f
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hFreq : (Fintype.card (TreeLeafIndex n × Fin m → (ZMod (R ^ (n - 1 + 2)))ˣ) : ℝ)⁻¹ *
      ∑ z, ‖Freq z‖ ≤ B :=
    frozenBulkFrequencyFactor_mean_le base tier S n m R t hS hR slot small a hslot hsmall ha
      hbase F E N D hD hN hdiv hm outside childBound input Qfreq Y hY
  have hSpec (i : I) : (Fintype.card (TreeLeafIndex n × Fin m → (ZMod (p i))ˣ) : ℝ)⁻¹ *
      ∑ z, ‖Spec i z‖ ≤ (3 : ℝ) ^ (2 ^ n) :=
    frozenBulkSpectatorHaar_absolute_mean_le (hp i) base n m hm ts small a
      (hfreq i) (hsmallp i) (hasamples i) (twist i) (Equiv.refl _) (g i) (hg i) (henergy i)
  have h := bulk_residue_absolute_mean_le (I := I) (J := TreeLeafIndex n × Fin m)
    (R ^ (n - 1 + 2)) p hc input Qbulk Ybulk hYbulk
    Freq Spec B hB (fun _ => (3 : ℝ) ^ (2 ^ n))
    (by
      simp only [finite_univ_canonical, Fintype.card_eq_nat_card] at hFreq ⊢
      exact hFreq)
    (by
      intro i
      have hi := hSpec i
      simp only [finite_univ_canonical, Fintype.card_eq_nat_card] at hi ⊢
      exact hi)
  simp only [Fintype.card_prod, card_treeLeafIndex, Fintype.card_fin, Finset.prod_const,
    Finset.card_univ, ← pow_mul, B] at h
  simp only [finite_univ_canonical, Fintype.card_eq_nat_card] at h ⊢
  exact h

end

theorem frozenMixedUnitArithmeticMean_le {σ I : Type*} [Fintype I]
    (base : σ → ℕ) (tier : σ → ℕ) (S : Finset ℤ) (n m R N V : ℕ)
    [NeZero (R ^ (n - 1 + 2))] (t : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0) (hN : ∀ s ∈ S, s.natAbs ≤ N)
    (hR : ∀ b (j : Fin (2 ^ n - 1)),
      (singleTreeNodeFrequencies S n (frequencyPairProjection S n b t) j.val).root.natAbs ∣ R)
    (slot : (TreeLeafIndex n × Fin m) ↪ σ)
    (small : Bool → TreeLeafTuple (List σ) n) (a : Bool → MovingSampleSlots σ n)
    (hslot : ∀ j, n ≤ tier (slot j))
    (hsmall : ∀ b i, i ∈ flattenMovingSlots n (small b) → i ∉ Set.range slot)
    (ha : ∀ b, (a b).Levels tier)
    (hbase : ∀ i ∉ Set.range slot, IsCoprime (base i : ℤ) (R : ℤ))
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (hF : ∀ b s regular, ‖F b (.leaf s regular) s‖ ≤ if s.natAbs ≤ V then 1 else 0)
    (D : ℝ) (hD : 0 ≤ D)
    (hdiv : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D) (hm : 0 < m)
    (p : I → ℕ) [∀ i, Fact (p i).Prime]
    [NeZero (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i)]
    (hc : Pairwise (fun i j => (bulkResidueModuli (R ^ (n - 1 + 2)) p i).Coprime
      (bulkResidueModuli (R ^ (n - 1 + 2)) p j))) (hp : ∀ i, 3 ≤ p i)
    (hfreq : ∀ i b, movingGiantFrequencyUnits (p i) n
      (frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t)))
    (hsmallp : ∀ i b, ((treeLeafProduct n (movingSlotValues base n (small b)) : ℕ) : ZMod (p i)) ≠ 0)
    (hasamples : ∀ i b, ((a b).values base).UnitsAt (p i))
    (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (henergy : ∀ i, ∑ x : ZMod (p i), ‖g i x‖ ^ 2 ≤ (p i : ℝ))
    (twist : ∀ i, Bool → (ZMod (p i))ˣ) (outside : List ℕ) (childBound : ℕ → ℕ)
    (input : PublishedProgressionInput) (Qfreq Qbulk : ℕ) (Y : ℝ) (hY : 0 ≤ Y)
    (Ybulk : TreeLeafIndex n × Fin m → ℝ) (hYbulk : ∀ j, 0 ≤ Ybulk j) :
    frozenMixedUnitArithmeticMean base n m R
      (fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t))
      small a slot F outside childBound input Qfreq Qbulk Y p hc g twist Ybulk ≤
      ((2 : ℝ) ^ (2 ^ n * m) * 2 * 3 ^ (2 ^ n * Fintype.card I)) *
        (frequencyLeafWeight (pairedFrequencyLeaf S V) n t *
          ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod) := by
  have h := frozenArithmetic_same_assignment_mixed_norm base tier S n m R t hS hR slot small a
    hslot hsmall ha hbase F (fun _ _ _ _ _ => 1) N D hD hN hdiv hm p hc hp hfreq
    hsmallp hasamples g hg henergy twist outside childBound input Qfreq Qbulk Y hY Ybulk hYbulk
  have hamp := movingDataWeight_pair_unit_leaf_bound F V hF S n t small (bulkSlotLeaves n m slot) a
  have hprob : 0 ≤ ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod := by
    apply List.prod_nonneg
    intro c hc
    obtain ⟨f, _, rfl⟩ := List.mem_map.mp hc
    exact pairFrequencySupportBound_nonneg D f
  have hbound := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hamp hprob) (by norm_num : (0 : ℝ) ≤ 2))
      (by positivity : (0 : ℝ) ≤ 3 ^ (2 ^ n * Fintype.card I)))
    (by positivity : (0 : ℝ) ≤ 2 ^ (2 ^ n * m))
  have h' : frozenMixedUnitArithmeticMean base n m R
      (fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t))
      small a slot F outside childBound input Qfreq Qbulk Y p hc g twist Ybulk ≤ _ := h
  exact h'.trans (hbound.trans_eq (by ring))

theorem movingPattern_same_assignment_mixed_norm {B C I : Type*} [Fintype I] {N₀ n m : ℕ}
    (e : Fin (N₀ + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (S : Finset ℤ) (t : FrequencyTree (S × S) n) (R N V : ℕ)
    [NeZero (R ^ (n - 1 + 2))]
    (hS : ∀ s ∈ S, s ≠ 0) (hN : ∀ s ∈ S, s.natAbs ≤ N)
    (hR : ∀ b (j : Fin (2 ^ n - 1)),
      (singleTreeNodeFrequencies S n (frequencyPairProjection S n b t) j.val).root.natAbs ∣ R)
    (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (pattern : Bool × MovingSampleIndex n → C)
    (hsmall : ∀ b i, i ∈ flattenMovingSlots n (small b) → i ∉ Set.range slot)
    (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (base : Fin (N₀ + 1) → ℕ)
    (hbase : ∀ i ∉ Set.range (movingPatternBulkEmbedding e slot), IsCoprime (base i : ℤ) (R : ℤ))
    (F : Bool → {k : ℕ} → MovingSlotData (Fin (N₀ + 1)) k → ℤ → ℂ)
    (hF : ∀ b s regular, ‖F b (.leaf s regular) s‖ ≤ if s.natAbs ≤ V then 1 else 0)
    (D : ℝ) (hD : 0 ≤ D)
    (hdiv : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D) (hm : 0 < m)
    (p : I → ℕ) [∀ i, Fact (p i).Prime]
    [NeZero (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i)]
    (hc : Pairwise (fun i j => (bulkResidueModuli (R ^ (n - 1 + 2)) p i).Coprime
      (bulkResidueModuli (R ^ (n - 1 + 2)) p j))) (hp : ∀ i, 3 ≤ p i)
    (hfreq : ∀ i b, movingGiantFrequencyUnits (p i) n
      (frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t)))
    (hsmallp : ∀ i b j, j ∈ flattenMovingSlots n (small b) →
      (base (e.symm (.inl j)) : ZMod (p i)) ≠ 0)
    (hasamples : ∀ i c, (base (e.symm (.inr c)) : ZMod (p i)) ≠ 0)
    (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (henergy : ∀ i, ∑ x : ZMod (p i), ‖g i x‖ ^ 2 ≤ (p i : ℝ))
    (twist : ∀ i, Bool → (ZMod (p i))ˣ) (outside : List ℕ) (childBound : ℕ → ℕ)
    (input : PublishedProgressionInput) (Qfreq Qbulk : ℕ) (Y : ℝ) (hY : 0 ≤ Y)
    (Ybulk : TreeLeafIndex n × Fin m → ℝ) (hYbulk : ∀ j, 0 ≤ Ybulk j) :
    let ts := fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t)
    let data := movingPatternFinBulkData e n m ts small slot (Equiv.refl _) pattern
    let freq := frozenBulkFrequencyFactor base (movingPatternBulkEmbedding e slot) outside
      F (fun _ _ _ _ _ => 1) data childBound R (R ^ (n - 1 + 2)) input Qfreq Y
    let spec := fun i => frozenBulkSpectatorHaar base n m ts
      (fun b => movingPatternFiniteSmall e n (small b)) (movingPatternFiniteSamples e n pattern)
      (twist i) (Equiv.refl _) (g i)
    let M := ∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i
    let A := fun z => freq (bulkResidueEquiv (R ^ (n - 1 + 2)) p hc z).1 *
      ∏ i, spec i ((bulkResidueEquiv (R ^ (n - 1 + 2)) p hc z).2 i)
    (Fintype.card (TreeLeafIndex n × Fin m → (ZMod M)ˣ) : ℝ)⁻¹ *
      (∑ z : TreeLeafIndex n × Fin m → (ZMod M)ˣ,
        ‖A z * ∏ j, pageGiantWeight input Qbulk M (z j).val.val (Ybulk j)‖) ≤
      ((2 : ℝ) ^ (2 ^ n * m) * 2 * 3 ^ (2 ^ n * Fintype.card I)) *
        (frequencyLeafWeight (pairedFrequencyLeaf S V) n t *
          ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod) := by
  intro ts data freq spec M A
  have hslot (j : TreeLeafIndex n × Fin m) :
      n ≤ ((Sum.elim tierB tierC) ∘ e) (movingPatternBulkEmbedding e slot j) := by
    change n ≤ Sum.elim tierB tierC (e (e.symm (.inl (slot j))))
    simpa only [Equiv.apply_symm_apply, Sum.elim_inl] using hB (slot j)
  have hd : data = fun b => buildMovingSlotData n (ts b) (movingPatternFiniteSmall e n (small b))
      (bulkSlotLeaves n m (movingPatternBulkEmbedding e slot)) (movingPatternFiniteSamples e n pattern b) := by
    funext b
    dsimp only [data]
    rw [movingPatternFinBulkData_build]
    cases b <;> rfl
  have h := frozenMixedUnitArithmeticMean_le base ((Sum.elim tierB tierC) ∘ e) S n m R N V t
    hS hN hR (movingPatternBulkEmbedding e slot) (fun b => movingPatternFiniteSmall e n (small b))
    (movingPatternFiniteSamples e n pattern) hslot
    (fun b => movingPatternFiniteSmall_absent e slot (small b) (hsmall b))
    (movingPatternFiniteSamples_levels e tierB tierC n pattern htier) hbase F hF D hD hdiv hm p hc hp hfreq
    (fun i b => movingPatternFiniteSmall_unit e base (small b) (hsmallp i b))
    (fun i => movingPatternFiniteSamples_units e base pattern (hasamples i))
    g hg henergy twist outside childBound input Qfreq Qbulk Y hY Ybulk hYbulk
  dsimp only [A, freq, spec, M]
  rw [hd]
  unfold frozenMixedUnitArithmeticMean at h
  dsimp only at h
  simp only [finite_univ_canonical, Fintype.card_eq_nat_card] at h ⊢
  apply le_trans (le_of_eq ?_) h
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  exact mul_right_comm _ _ _

theorem movingPattern_normalized_same_assignment_mixed_norm {B C I : Type*} [Fintype I] {N₀ n m : ℕ}
    (e : Fin (N₀ + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (S : Finset ℤ) (t : FrequencyTree (S × S) n) (R N V : ℕ)
    [NeZero (R ^ (n - 1 + 2))]
    (hS : ∀ s ∈ S, s ≠ 0) (hN : ∀ s ∈ S, s.natAbs ≤ N)
    (hR : ∀ b (j : Fin (2 ^ n - 1)),
      (singleTreeNodeFrequencies S n (frequencyPairProjection S n b t) j.val).root.natAbs ∣ R)
    (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (pattern : Bool × MovingSampleIndex n → C)
    (hsmall : ∀ b i, i ∈ flattenMovingSlots n (small b) → i ∉ Set.range slot)
    (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (base : Fin (N₀ + 1) → ℕ)
    (hbase : ∀ i ∉ Set.range (movingPatternBulkEmbedding e slot), IsCoprime (base i : ℤ) (R : ℤ))
    (F : Bool → {k : ℕ} → MovingSlotData (Fin (N₀ + 1)) k → ℤ → ℂ)
    (hF : ∀ b s regular, ‖F b (.leaf s regular) s‖ ≤ if s.natAbs ≤ V then 1 else 0)
    (D : ℝ) (hD : 0 ≤ D)
    (hdiv : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D) (hm : 0 < m)
    (p : I → ℕ) [∀ i, Fact (p i).Prime]
    [NeZero (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i)]
    (hc : Pairwise (fun i j => (bulkResidueModuli (R ^ (n - 1 + 2)) p i).Coprime
      (bulkResidueModuli (R ^ (n - 1 + 2)) p j))) (hp : ∀ i, 3 ≤ p i)
    (hfreq : ∀ i b, movingGiantFrequencyUnits (p i) n
      (frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t)))
    (hsmallp : ∀ i b j, j ∈ flattenMovingSlots n (small b) →
      (base (e.symm (.inl j)) : ZMod (p i)) ≠ 0)
    (hasamples : ∀ i c, (base (e.symm (.inr c)) : ZMod (p i)) ≠ 0)
    (sets : ∀ i, Finset (ZMod (p i)))
    (hsets : ∀ i, (sets i).Nonempty) (hsetsLt : ∀ i, (sets i).card < p i)
    (twist : ∀ i, Bool → (ZMod (p i))ˣ) (outside : List ℕ) (childBound : ℕ → ℕ)
    (input : PublishedProgressionInput) (Qfreq Qbulk : ℕ) (Y : ℝ) (hY : 0 ≤ Y)
    (Ybulk : TreeLeafIndex n × Fin m → ℝ) (hYbulk : ∀ j, 0 ≤ Ybulk j) :
    let ts := fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t)
    let data := movingPatternFinBulkData e n m ts small slot (Equiv.refl _) pattern
    let freq := frozenBulkFrequencyFactor base (movingPatternBulkEmbedding e slot) outside
      F (fun _ _ _ _ _ => 1) data childBound R (R ^ (n - 1 + 2)) input Qfreq Y
    let spec := fun i => frozenBulkSpectatorHaar base n m ts
      (fun b => movingPatternFiniteSmall e n (small b)) (movingPatternFiniteSamples e n pattern)
      (twist i) (Equiv.refl _) (normalizedResidueTransform (sets i))
    let M := ∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i
    let A := fun z => freq (bulkResidueEquiv (R ^ (n - 1 + 2)) p hc z).1 *
      ∏ i, spec i ((bulkResidueEquiv (R ^ (n - 1 + 2)) p hc z).2 i)
    (Fintype.card (TreeLeafIndex n × Fin m → (ZMod M)ˣ) : ℝ)⁻¹ *
      (∑ z : TreeLeafIndex n × Fin m → (ZMod M)ˣ,
        ‖A z * ∏ j, pageGiantWeight input Qbulk M (z j).val.val (Ybulk j)‖) ≤
      ((2 : ℝ) ^ (2 ^ n * m) * 2 * 3 ^ (2 ^ n * Fintype.card I)) *
        (frequencyLeafWeight (pairedFrequencyLeaf S V) n t *
          ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod) := by
  exact movingPattern_same_assignment_mixed_norm e tierB tierC S t R N V hS hN hR small slot pattern
    hsmall hB htier base hbase F hF D hD hdiv hm p hc hp hfreq hsmallp hasamples
    (fun i => normalizedResidueTransform (sets i))
    (fun i => normalizedResidueTransform_zero (sets i))
    (fun i => (normalizedResidueTransform_energy (sets i) (hsets i) (hsetsLt i)).le)
    twist outside childBound input Qfreq Qbulk Y hY Ybulk hYbulk

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSpectatorCost
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pointwise cost of the actual normalized spectator transforms -/

namespace Ostmann
open scoped Classical BigOperators

theorem normalizedResidueTransform_norm_le_sqrt {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) (x : ZMod p) :
    ‖normalizedResidueTransform S x‖ ≤ Real.sqrt (p : ℝ) := by
  have hx : ‖normalizedResidueTransform S x‖ ^ 2 ≤
      ∑ y : ZMod p, ‖normalizedResidueTransform S y‖ ^ 2 :=
    Finset.single_le_sum (f := fun y : ZMod p => ‖normalizedResidueTransform S y‖ ^ 2)
      (fun y _ => sq_nonneg _) (Finset.mem_univ x)
  rw [normalizedResidueTransform_energy S hS hSp] at hx
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg p : (0 : ℝ) ≤ p),
    Real.sqrt_nonneg (p : ℝ), norm_nonneg (normalizedResidueTransform S x)]

theorem normalizedResidueTransform_norm_le_prime {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) (x : ZMod p) :
    ‖normalizedResidueTransform S x‖ ≤ p := by
  apply (normalizedResidueTransform_norm_le_sqrt S hS hSp x).trans
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg p : (0 : ℝ) ≤ p), Real.sqrt_nonneg (p : ℝ)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternPrimeNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pointwise bound for the literal original prime observable -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

section
variable {B C Cell I : Type*} [Fintype Cell] [Fintype I] {N n m : ℕ}
  (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
  (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
  (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
  (pattern : Bool × MovingSampleIndex n → C)
  (hsmall : ∀ b, ∀ i ∈ flattenMovingSlots n (small b), i ∉ Set.range slot)
  (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
  (base : Fin (N + 1) → ℕ) (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
  (hbase : ∀ i ∉ Set.range (movingPatternBulkEmbedding e slot), (base i).Prime)
  (childBound pivotBound : ℕ → ℕ)
  (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
  (F : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℂ)
  (E : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℤ → ℤ → ℝ)
  (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
  (hR : ∀ b, (movingPatternFinBulkData e n m t small slot perm pattern b).frequencyProduct ∣ R)
  (hr : R ^ (n + 1) ∣ (r : ℤ))
  (p : I → ℕ) [∀ i, Fact (p i).Prime]
  (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
  (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
  (twist : ∀ i, Bool → (ZMod (p i))ˣ)
  (P : PublishedProgressionInput) (Q : ℕ) (y : ℝ)
  (j₀ : TreeLeafIndex n × Fin m) (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ)
  (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
  (hV : ∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ V)
  (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
  (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
  (hφout : ∀ x, 1 ≤ |x| → φ x = 0) (L U : ℝ)

include hB htier hV hBφ hDφ hφ hlip hφout j₀ in
/-- This uniform pointwise estimate allows the extra nonbulk-prime deletion
error to be returned to the initial external law. -/
theorem movingPatternPrimeBulkHaar_norm
    (hy : 0 ≤ y) (Kspec : I → ℝ) (hKspec : ∀ i, 0 ≤ Kspec i)
    (hgnorm : ∀ i z, ‖g i z‖ ≤ Kspec i)
    (x : (TreeLeafIndex n × Fin m) → primes) :
    let data := movingPatternFinBulkData e n m t small slot perm pattern
    let amp := 2 * (‖movingDataWeight (F false) (E false) (data false)‖ *
      ‖movingDataWeight (F true) (E true) (data true)‖)
    let W := (movingFourierVariationBudget ψ V lo hi n *
      (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
    ‖movingPatternPrimeBulkHaar e t small slot perm pattern base primes hprimes hbase
      childBound pivotBound hfreq F E outside R r p g twist P Q y ψ X lo hi hlo hhi φ G L U x‖ ≤
        (amp * ∏ i, Kspec i ^ (2 ^ (n + 1))) * W := by
  intro data amp W
  let value := primeBulkValues base (movingPatternBulkEmbedding e slot) x
  have hp := primeBulkValues_prime base (movingPatternBulkEmbedding e slot) x hprimes hbase
  have hv : ∀ i, value i ≠ 0 := fun i => (hp i).ne_zero
  have hf := movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hfreq
  let nodes := fun b => (data b).formulaNodes value hv childBound pivotBound (hf b)
    (.prime false) (.prime true)
  have hk : ‖movingRealKernelPair value data nodes ψ X lo hi hlo hhi φ G L U‖ ≤ W := by
    rw [← realValueKernelPair_nat value hv childBound pivotBound data hf]
    exact movingPattern_kernel_norm_le e tierB tierC t small slot perm pattern hB htier
      (fun i => (value i : ℝ)) childBound pivotBound j₀ ψ X lo hi V hlo hhi hV
      φ G Bφ Dφ hBφ hDφ hφ hlip hφout L U
  have hfr : ‖movingFrequencyPageAverage value outside F E data nodes R r P Q y‖ ≤ amp :=
    movingFrequencyPageAverage_norm_le value outside F E data nodes R r P Q y hy
  have hs : ‖∏ i, movingSpectatorHaarAverage value (p i) (g i) (twist i) data‖ ≤
      ∏ i, Kspec i ^ (2 ^ (n + 1)) := by
    rw [norm_prod]
    exact Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ =>
      movingSpectatorHaarAverage_norm_le value (p i) (g i) (twist i) data
        (Kspec i) (hKspec i) (hgnorm i))
  change ‖movingRealKernelPair value data nodes ψ X lo hi hlo hhi φ G L U *
    (movingFrequencyPageAverage value outside F E data nodes R r P Q y *
      ∏ i, movingSpectatorHaarAverage value (p i) (g i) (twist i) data)‖ ≤ _
  simp only [norm_mul]
  calc
    _ ≤ W * (amp * ∏ i, Kspec i ^ (2 ^ (n + 1))) :=
      mul_le_mul hk (mul_le_mul hfr hs (norm_nonneg _) (by dsimp only [amp]; positivity))
        (by positivity) (sq_nonneg _)
    _ = _ := mul_comm _ _

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternObservableCost
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual observable and its uniform pointwise arithmetic cost -/

namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

section
variable {B C I : Type*} [Fintype I] {N n m : ℕ}
  (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
  (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
  (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
  (pattern : Bool × MovingSampleIndex n → C)
  (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
  (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
  (childBound pivotBound : ℕ → ℕ)
  (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
  (F : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℂ)
  (E : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℤ → ℤ → ℝ)
  (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
  (p : I → ℕ) [∀ i, Fact (p i).Prime]
  (g : ∀ i, ZMod (p i) → ℂ)
  (twist : ∀ i, Bool → (ZMod (p i))ˣ)
  (P : PublishedProgressionInput) (Q : ℕ) (y : ℝ)
  (j₀ : TreeLeafIndex n × Fin m) (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ)
  (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
  (hV : ∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ V)
  (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
  (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
  (hφout : ∀ x, 1 ≤ |x| → φ x = 0) (L U : ℝ)

include hB htier hV hBφ hDφ hφ hlip hφout j₀ in
theorem movingPatternPrimeObservable_norm
    (hy : 0 ≤ y) (Kspec : I → ℝ) (hKspec : ∀ i, 0 ≤ Kspec i)
    (hgnorm : ∀ i z, ‖g i z‖ ≤ Kspec i)
    (x : Fin (N + 1) → primes) :
    let data := movingPatternFinBulkData e n m t small slot perm pattern
    let amp := 2 * (‖movingDataWeight (F false) (E false) (data false)‖ *
      ‖movingDataWeight (F true) (E true) (data true)‖)
    let W := (movingFourierVariationBudget ψ V lo hi n *
      (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
    ‖movingPatternPrimeObservable e t small slot perm pattern primes hprimes
      childBound pivotBound hfreq F E outside R r p g twist P Q y
      ψ X lo hi hlo hhi φ G L U x‖ ≤ (amp * ∏ i, Kspec i ^ (2 ^ (n + 1))) * W := by
  dsimp only
  let z := fun j => x (movingPatternBulkEmbedding e slot j)
  have heq : joinBulkNonbulk (movingPatternBulkEmbedding e slot) z (fun i => x i) = x := by
    funext i
    by_cases hi : i ∈ Set.range (movingPatternBulkEmbedding e slot)
    · obtain ⟨j, rfl⟩ := hi
      rw [joinBulkNonbulk_bulk]
    · exact joinBulkNonbulk_nonbulk (movingPatternBulkEmbedding e slot) z
        (fun i => x i) ⟨i, hi⟩
  have ho := movingPatternPrimeObservable_join e t small slot perm pattern primes hprimes
    childBound pivotBound hfreq F E outside R r p g twist P Q y
    ψ X lo hi hlo hhi φ G L U x z
  rw [heq] at ho
  rw [ho]
  exact movingPatternPrimeBulkHaar_norm e tierB tierC t small slot perm pattern hB htier
    (fun i => (x i : ℕ)) primes hprimes (fun i _ => hprimes _ (x i).property)
    childBound pivotBound hfreq F E outside R r p g twist P Q y j₀ ψ X lo hi V hlo hhi hV
    φ G Bφ Dφ hBφ hDφ hφ hlip hφout L U hy Kspec hKspec hgnorm z

end

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternMixedSameNormArithmetic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The norm estimate with the original internal and external priors -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.movingPattern_same_assignment_mixed_prime_arithmetic_rate
    (P : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A Wwin Bφ Dφ Cmass : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hCmass : 1 ≤ Cmass)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi),
      hi - lo ≤ Real.exp (Wwin * m) →
      ∀ (Bidx Cidx : Type) [Fintype Bidx] [Fintype Cidx] (Cell : Type) [Fintype Cell] (N : ℕ)
        (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (tierB : Bidx → ℕ) (tierC : Cidx → ℕ)
        (t : Bool → FrequencyTree ℤ n)
        (Sfreq : Finset ℤ) (ft : FrequencyTree (Sfreq × Sfreq) n) (Nfreq Vleaf : ℕ) (D : ℝ)
        (small : Bool → TreeLeafTuple (List Bidx) n)
        (slot : (TreeLeafIndex n × Fin m) ↪ Bidx)
        (pattern : Bool × MovingSampleIndex n → Cidx)
        (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
        (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (childBound pivotBound : ℕ → ℕ)
        (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
        (Fw : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℂ)
        (outside : List ℕ) [NeZero ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2))]
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (_hc : Pairwise (fun i j => (bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i).Coprime (bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p j)))
        [NeZero (∏ i, bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i)]
        (twist : ∀ i, Bool → (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (Qfreq : ℕ) (y X : ℝ) (_j₀ : TreeLeafIndex n × Fin m)
        (φ : ℝ → ℝ) (G : ℕ → ℝ) (XL U : ℝ)
        (u v : (TreeLeafIndex n × Fin m) → Cell → ℝ)
        (deleted : (Fin (N + 1) → primes) →
          (TreeLeafIndex n × Fin m) → Finset ℕ)
        (initial : (TreeLeafIndex n × Fin m) → Finset ℕ)
        (μ : ℕ → primes → ℝ) (ν : Bidx → primes → ℝ)
        (W : (Fin (N + 1) → primes) → ℂ) (Eprior αall βint Vint Uall : ℝ),
      let data := movingPatternFinBulkData e n m t small slot (Equiv.refl _) pattern
      let A₀ := ((2 : ℝ) ^ (2 ^ n * m) * 2 * 3 ^ (2 ^ n * m)) *
        (frequencyLeafWeight (pairedFrequencyLeaf Sfreq Vleaf) n ft *
          ((frequencySplitList Sfreq n ft).map (pairFrequencySupportBound D)).prod)
      let M := ∏ i, bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i
      let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
        (fun c => u j c.1) (fun c => v j c.1)
      let amp := 2 * (‖movingDataWeight (Fw false) ((fun _ _ _ _ _ => 1) false) (data false)‖ *
        ‖movingDataWeight (Fw true) ((fun _ _ _ _ _ => 1) true) (data true)‖)
      let law := fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)
      let raw := movingPatternPrimeObservable e t small slot (Equiv.refl _) pattern primes hprimes
        childBound pivotBound hfreq Fw (fun _ _ _ _ _ => 1) outside ((frequencyModelBase Sfreq n ft) : ℤ) ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p
        (fun i => normalizedResidueTransform (sets i)) twist P Qfreq
        y ψ X lo hi hlo hhi φ G XL U
      let obs := fun x => W x * raw x
      let cost := (amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) *
        (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n *
          (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
      (∀ b, ∀ i ∈ flattenMovingSlots n (small b), i ∉ Set.range slot) →
      (∀ i, n ≤ tierB i) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      (∀ b, MovingLeafLengthLE n (small b) r₀) →
      t = (fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n b ft)) →
      (∀ s ∈ Sfreq, s ≠ 0) → (∀ s ∈ Sfreq, s.natAbs ≤ Nfreq) →
      (∀ b s regular, ‖Fw b (.leaf s regular) s‖ ≤ if s.natAbs ≤ Vleaf then 1 else 0) →
      0 ≤ D → (∀ q : ℕ, q ≠ 0 → q ≤ Nfreq ^ 2 → (q.divisors.card : ℝ) ≤ D) →
      0 < m → (∀ i, 3 ≤ p i) → (∀ i b, movingGiantFrequencyUnits (p i) n (t b)) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 →
        ∀ i, i ∉ Set.range (movingPatternBulkEmbedding e slot) → IsCoprime ((x i : ℕ) : ℤ) ((frequencyModelBase Sfreq n ft) : ℤ)) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 → ∀ i b j,
        j ∈ flattenMovingSlots n (small b) → ((x (e.symm (.inl j)) : ℕ) : ZMod (p i)) ≠ 0) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 → ∀ i c,
        ((x (e.symm (.inr c)) : ℕ) : ZMod (p i)) ≠ 0) →
      (∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ Real.exp (A * m)) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      0 ≤ y →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      M ≤ bulkProgressionCutoff L →
      (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) →
      (Fintype.card Cell : ℝ) ≤ Real.exp (Real.exp ((14 / 10000 : ℝ) * L)) →
      (∀ j c, 1 ≤ u j c) → (∀ j c, Real.exp ((39 / 10000 : ℝ) * L) ≤ u j c) →
      (∀ j c, u j c ≤ v j c) → (∀ j c, v j c ≤ u j c + 1) →
      (∀ j c d, c ≠ d → v j c ≤ u j d ∨ v j d ≤ u j c) →
      (∀ j c, (M : ℝ) ≤ Real.exp (u j c)) →
      (∀ j, S j ⊆ primes) →
      (∀ x, productPrior law x ≠ 0 →
        ∀ j, ((deleted x j).card : ℝ) ≤ Real.exp (Cmass * L)) →
      (∀ j, Real.exp (-Cmass * L) ≤ ∑ q ∈ S j, (q : ℝ)⁻¹) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 →
        ∀ j i, i ∉ Set.range (movingPatternBulkEmbedding e slot) → (x i : ℕ) ∈ deleted x j) →
      (∀ q ∈ outside, q.Prime) →
      (∀ x, productPrior law x ≠ 0 → ∀ j q, q ∈ outside → q ∈ deleted x j) →
      ∀ _c₀ : Cell × (ZMod M)ˣ,
      (∀ j, initial j ⊆ S j) →
      (∀ x, productPrior law x ≠ 0 → ∀ j, S j \ deleted x j ⊆ initial j) →
      (∀ j, ν (slot j) = primeSubsetPrior primes (initial j)) →
      (∀ j q, 0 ≤ μ j q) → (∀ j q, 0 ≤ ν j q) →
      (∀ j, ∑ q, μ j q = 1) → (∀ j, ∑ q, ν j q = 1) →
      0 ≤ Eprior → 0 ≤ αall → 0 ≤ βint → 0 < Vint → 1 ≤ Uall →
      (∀ j (q : primes), (q : ℝ) * μ j q ≤ Eprior) →
      (∀ j q, μ j q ≤ αall) → (∀ j q, ν j q ≤ αall) →
      (∀ c q, μ (movingSampleTier (rep c).val.2) q ≤ βint) →
      (∀ c q, μ (movingSampleTier (rep c).val.2) q ≠ 0 → Real.exp Vint ≤ (q : ℝ)) →
      (∀ q : primes, (q : ℝ) ≤ Uall) →
      (∀ x, ‖W x‖ ≤ 1) →
      (∀ x z, W (joinBulkNonbulk (movingPatternBulkEmbedding e slot) z (fun i => x i)) = W x) →
      (∀ x, productPrior law x ≠ 0 → obs x ≠ 0 → ∀ i j,
        (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) →
          (x i : ℕ) ≠ (x j : ℕ)) →
      (∀ x, productPrior law x ≠ 0 → obs x ≠ 0 → ∀ b c,
        (x (e.symm (.inl b)) : ℕ) ≠ (x (e.symm (.inr c)) : ℕ)) →
      (∀ x, productPrior law x ≠ 0 → obs x ≠ 0 → ∀ c b, (data b).Frequencies
        (fun s => (s : ZMod (x (e.symm (.inr c)) : ℕ)) ≠ 0)) →
      ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern obs x *
        movingPatternHaarProduct e (fun q : primes => (q : ℕ)) (fun q => hprimes _ q.property)
          n t small (movingPatternBulkLeaves n m slot (Equiv.refl _)) pattern x‖ ≤
      ((2 : ℝ) ^ Fintype.card Cidx * Eprior ^ (4 * n * 2 ^ n - Fintype.card Cidx)) *
        (cost * movingInternalArithmeticError n (Fintype.card Cidx)
          (2 ^ n * (r₀ + m + 4 * n + 4)) (Real.exp (A * m)) Uall αall βint Vint +
        ((((((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) *
          Bφ ^ (2 ^ n - 1)) ^ 2) * A₀) * 2 ^ Fintype.card (TreeLeafIndex n × Fin m)) + Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
          2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)))) := by
  filter_upwards [P.movingPattern_original_mixed_prime_norm_arithmetic_rate ψ n r₀ k
    A Wwin Bφ Dφ 2 Cmass hA hWwin (by norm_num) hCmass hBφ hDφ] with L hrate
  dsimp only
  intro lo hi hlo hhi hwindow Bidx Cidx _ _ Cell _ N e tierB tierC t Sfreq ft Nfreq Vleaf D small slot pattern rep
    primes hprimes _ childBound pivotBound hfreq Fw outside _ p _ hc _ twist sets
    Qfreq y X j₀ φ G XL U u v deleted initial μ ν W Eprior αall βint Vint Uall
    hsmall hB htier hsmallLen ht hS hN hleaf hD hdiv hm hp hfreqp hbase
    hsmallp hsamplesp hV hsets hsetsp hy hpupper hMQ hφ hlip hφout
    hcard hu hulow huv hshort hsep hMcell hSS hdel hmass hdelbase hout hdelout
    c₀ hsub hretain hν hμ0 hν0 hμmass hνmass hEprior hαall hβint hVint hUall
    hμbound hμall hνall hμmax hμmin hvalues hW hWbulk hdisjoint hcross hfmod
  let m := spectatorBulkCount k L
  let R := frequencyModelBase Sfreq n ft
  have hR (b : Bool) : (movingPatternFinBulkData e n m t small slot (Equiv.refl _) pattern b).frequencyProduct ∣ (R : ℤ) := by
    simpa only [ht, R] using movingPattern_frequencyProduct_dvd e Sfreq ft small slot (Equiv.refl _) pattern b
  have hroots (b : Bool) (j : Fin (2 ^ n - 1)) :
      (singleTreeNodeFrequencies Sfreq n (frequencyPairProjection Sfreq n b ft) j.val).root.natAbs ∣ R :=
    frequencyModelBase_roots Sfreq n ft b j
  let data := movingPatternFinBulkData e n m t small slot (Equiv.refl _) pattern
  have hone (b : Bool) : ‖movingDataWeight (Fw b) (fun _ _ _ _ => 1) (data b)‖ ≤ 1 :=
    movingDataWeight_unit_norm_le_one (Fw b) (fun s regular =>
      (hleaf b s regular).trans (by split_ifs <;> norm_num)) (data b)
  have hamp : 2 * (‖movingDataWeight (Fw false) (fun _ _ _ _ => 1) (data false)‖ *
      ‖movingDataWeight (Fw true) (fun _ _ _ _ => 1) (data true)‖) ≤ Real.exp ((2 : ℝ) * m) := by
    have hpair := mul_le_mul (hone false) (hone true) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have he : (2 : ℝ) ≤ Real.exp (m : ℝ) := by linarith [Real.add_one_le_exp (m : ℝ)]
    calc
      _ ≤ 4 := by linarith
      _ ≤ (Real.exp (m : ℝ)) ^ 2 := by nlinarith [Real.exp_pos (m : ℝ)]
      _ = _ := by simpa only [Nat.cast_ofNat] using (Real.exp_nat_mul (m : ℝ) 2).symm
  let A₀ := ((2 : ℝ) ^ (2 ^ n * m) * 2 * 3 ^ (2 ^ n * m)) *
    (frequencyLeafWeight (pairedFrequencyLeaf Sfreq Vleaf) n ft *
      ((frequencySplitList Sfreq n ft).map (pairFrequencySupportBound D)).prod)
  have hA₀ : 0 ≤ A₀ := by
    have hleaf0 := frequencyLeafWeight_nonneg (pairedFrequencyLeaf Sfreq Vleaf)
      (fun _ => by unfold pairedFrequencyLeaf; split_ifs <;> norm_num) n ft
    have hprod : 0 ≤ ((frequencySplitList Sfreq n ft).map (pairFrequencySupportBound D)).prod := by
      apply List.prod_nonneg
      intro x hx
      obtain ⟨f, _, rfl⟩ := List.mem_map.mp hx
      exact pairFrequencySupportBound_nonneg D f
    exact mul_nonneg (by positivity) (mul_nonneg hleaf0 hprod)
  have hlocal (x : Fin (N + 1) → primes)
      (hx : productPrior (fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x ≠ 0)
      (z : (TreeLeafIndex n × Fin m) → ℝ) (hz : ∀ j, 0 ≤ z j) :=
    movingPattern_normalized_same_assignment_mixed_norm e tierB tierC Sfreq ft R Nfreq Vleaf
      hS hN hroots small slot pattern hsmall hB htier (fun i => (x i : ℕ)) (hbase x hx)
      Fw hleaf D hD hdiv hm p hc hp
      (by simpa only [ht] using hfreqp) (hsmallp x hx) (hsamplesp x hx)
      sets hsets hsetsp twist outside childBound P Qfreq (bulkProgressionCutoff L) y hy z hz
  have h := hrate lo hi hlo hhi hwindow Bidx Cidx Cell N e tierB tierC t small slot (Equiv.refl _) pattern rep
    primes hprimes childBound pivotBound hfreq Fw (fun _ _ _ _ _ => 1) outside (R : ℤ)
    (R ^ (n - 1 + 2)) p hc twist sets Qfreq y X A₀ j₀ φ G XL U u v deleted initial μ ν W
    Eprior αall βint Vint Uall hsmall hB htier hsmallLen hR (frequencyModelModulus_precision R n)
    hV hsets hsetsp hamp hy hpupper hMQ hφ hlip hφout hcard hu hulow huv hshort hsep hMcell
    hSS hdel hmass hdelbase hout hdelout hA₀
    (by
      intro x hx
      dsimp only
      intro z hz
      have hz' := hlocal x hx z hz
      simpa only [A₀, m, ht, finite_univ_canonical, Fintype.card_eq_nat_card, Nat.card_fin] using hz')
    c₀ hsub hretain hν hμ0 hν0 hμmass hνmass hEprior hαall hβint hVint hUall
    hμbound hμall hνall hμmax hμmin hvalues hW hWbulk hdisjoint hcross hfmod
  exact h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternMixedIntegratedRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual two-prime arithmetic bound integrated over its giant cells -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.movingPattern_same_assignment_mixed_prime_integral_rate
    (P : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A Wwin Bφ Dφ Cmass : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hCmass : 1 ≤ Cmass)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi),
      hi - lo ≤ Real.exp (Wwin * m) →
      ∀ (Bidx Cidx : Type) [Fintype Bidx] [Fintype Cidx] (Cell : Type) [Fintype Cell] (N : ℕ)
        (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (tierB : Bidx → ℕ) (tierC : Cidx → ℕ)
        (t : Bool → FrequencyTree ℤ n)
        (Sfreq : Finset ℤ) (ft : FrequencyTree (Sfreq × Sfreq) n) (Nfreq Vleaf : ℕ) (D : ℝ)
        (small : Bool → TreeLeafTuple (List Bidx) n)
        (slot : (TreeLeafIndex n × Fin m) ↪ Bidx)
        (pattern : Bool × MovingSampleIndex n → Cidx)
        (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
        (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (childBound pivotBound : ℕ → ℕ)
        (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
        (Fw : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℂ)
        (outside : List ℕ) [NeZero ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2))]
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (_hc : Pairwise (fun i j => (bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i).Coprime (bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p j)))
        [NeZero (∏ i, bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i)]
        (twist : ∀ i, Bool → (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (Qfreq : ℕ) (X : ℝ) (_j₀ : TreeLeafIndex n × Fin m)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (u v : (TreeLeafIndex n × Fin m) → Cell → ℝ)
        (deleted : (Fin (N + 1) → primes) →
          (TreeLeafIndex n × Fin m) → Finset ℕ)
        (initial : (TreeLeafIndex n × Fin m) → Finset ℕ)
        (μ : ℕ → primes → ℝ) (ν : Bidx → primes → ℝ)
        (W : ℝ → ℝ → (Fin (N + 1) → primes) → ℂ)
        (Eprior αall βint Vint Uall : ℝ) (uG vG rG sG center : ℝ),
      let data := movingPatternFinBulkData e n m t small slot (Equiv.refl _) pattern
      let A₀ := ((2 : ℝ) ^ (2 ^ n * m) * 2 * 3 ^ (2 ^ n * m)) *
        (frequencyLeafWeight (pairedFrequencyLeaf Sfreq Vleaf) n ft *
          ((frequencySplitList Sfreq n ft).map (pairFrequencySupportBound D)).prod)
      let M := ∏ i, bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i
      let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
        (fun c => u j c.1) (fun c => v j c.1)
      let amp := 2 * (‖movingDataWeight (Fw false) ((fun _ _ _ _ _ => 1) false) (data false)‖ *
        ‖movingDataWeight (Fw true) ((fun _ _ _ _ _ => 1) true) (data true)‖)
      let law := fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)
      let raw := fun xg y => movingPatternPrimeObservable e t small slot (Equiv.refl _) pattern primes hprimes
        childBound pivotBound hfreq Fw (fun _ _ _ _ _ => 1) outside ((frequencyModelBase Sfreq n ft) : ℤ) ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p
        (fun i => normalizedResidueTransform (sets i)) twist P Qfreq
        y ψ X lo hi hlo hhi φ G (Real.exp xg) (Real.exp y)
      let obs := fun xg y x => W xg y x * raw xg y x
      let cost := (amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) *
        (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n *
          (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
      1 ≤ uG → 1 ≤ rG → uG ≤ vG → rG ≤ sG → vG ≤ uG + 1 → sG ≤ rG + 1 → vG ≤ center + 1 →
      (∀ b, ∀ i ∈ flattenMovingSlots n (small b), i ∉ Set.range slot) →
      (∀ i, n ≤ tierB i) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      (∀ b, MovingLeafLengthLE n (small b) r₀) →
      t = (fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n b ft)) →
      (∀ s ∈ Sfreq, s ≠ 0) → (∀ s ∈ Sfreq, s.natAbs ≤ Nfreq) →
      (∀ b s regular, ‖Fw b (.leaf s regular) s‖ ≤ if s.natAbs ≤ Vleaf then 1 else 0) →
      0 ≤ D → (∀ q : ℕ, q ≠ 0 → q ≤ Nfreq ^ 2 → (q.divisors.card : ℝ) ≤ D) →
      0 < m → (∀ i, 3 ≤ p i) → (∀ i b, movingGiantFrequencyUnits (p i) n (t b)) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 →
        ∀ i, i ∉ Set.range (movingPatternBulkEmbedding e slot) → IsCoprime ((x i : ℕ) : ℤ) ((frequencyModelBase Sfreq n ft) : ℤ)) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 → ∀ i b j,
        j ∈ flattenMovingSlots n (small b) → ((x (e.symm (.inl j)) : ℕ) : ZMod (p i)) ≠ 0) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 → ∀ i c,
        ((x (e.symm (.inr c)) : ℕ) : ZMod (p i)) ≠ 0) →
      (∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ Real.exp (A * m)) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      M ≤ bulkProgressionCutoff L →
      (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) →
      (Fintype.card Cell : ℝ) ≤ Real.exp (Real.exp ((14 / 10000 : ℝ) * L)) →
      (∀ j c, 1 ≤ u j c) → (∀ j c, Real.exp ((39 / 10000 : ℝ) * L) ≤ u j c) →
      (∀ j c, u j c ≤ v j c) → (∀ j c, v j c ≤ u j c + 1) →
      (∀ j c d, c ≠ d → v j c ≤ u j d ∨ v j d ≤ u j c) →
      (∀ j c, (M : ℝ) ≤ Real.exp (u j c)) →
      (∀ j, S j ⊆ primes) →
      (∀ x, productPrior law x ≠ 0 →
        ∀ j, ((deleted x j).card : ℝ) ≤ Real.exp (Cmass * L)) →
      (∀ j, Real.exp (-Cmass * L) ≤ ∑ q ∈ S j, (q : ℝ)⁻¹) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 →
        ∀ j i, i ∉ Set.range (movingPatternBulkEmbedding e slot) → (x i : ℕ) ∈ deleted x j) →
      (∀ q ∈ outside, q.Prime) →
      (∀ x, productPrior law x ≠ 0 → ∀ j q, q ∈ outside → q ∈ deleted x j) →
      ∀ _c₀ : Cell × (ZMod M)ˣ,
      (∀ j, initial j ⊆ S j) →
      (∀ x, productPrior law x ≠ 0 → ∀ j, S j \ deleted x j ⊆ initial j) →
      (∀ j, ν (slot j) = primeSubsetPrior primes (initial j)) →
      (∀ j q, 0 ≤ μ j q) → (∀ j q, 0 ≤ ν j q) →
      (∀ j, ∑ q, μ j q = 1) → (∀ j, ∑ q, ν j q = 1) →
      0 ≤ Eprior → 0 ≤ αall → 0 ≤ βint → 0 < Vint → 1 ≤ Uall →
      (∀ j (q : primes), (q : ℝ) * μ j q ≤ Eprior) →
      (∀ j q, μ j q ≤ αall) → (∀ j q, ν j q ≤ αall) →
      (∀ c q, μ (movingSampleTier (rep c).val.2) q ≤ βint) →
      (∀ c q, μ (movingSampleTier (rep c).val.2) q ≠ 0 → Real.exp Vint ≤ (q : ℝ)) →
      (∀ q : primes, (q : ℝ) ≤ Uall) →
      (∀ x, Measurable (fun z : ℝ × ℝ => W z.1 z.2 x)) →
      (∀ xg y x, ‖W xg y x‖ ≤ 1) →
      (∀ xg y x z, W xg y (joinBulkNonbulk (movingPatternBulkEmbedding e slot) z (fun i => x i)) = W xg y x) →
      (∀ xg ∈ Set.Ioc uG vG, ∀ y ∈ Set.Ioc rG sG, ∀ x, productPrior law x ≠ 0 → obs xg y x ≠ 0 → ∀ i j,
        (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) →
          (x i : ℕ) ≠ (x j : ℕ)) →
      (∀ xg ∈ Set.Ioc uG vG, ∀ y ∈ Set.Ioc rG sG, ∀ x, productPrior law x ≠ 0 → obs xg y x ≠ 0 → ∀ b c,
        (x (e.symm (.inl b)) : ℕ) ≠ (x (e.symm (.inr c)) : ℕ)) →
      (∀ xg ∈ Set.Ioc uG vG, ∀ y ∈ Set.Ioc rG sG, ∀ x, productPrior law x ≠ 0 → obs xg y x ≠ 0 → ∀ c b, (data b).Frequencies
        (fun s => (s : ZMod (x (e.symm (.inr c)) : ℕ)) ≠ 0)) →
      ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern
          (fun x => ∫ xg in Set.Ioc uG vG, ∫ y in Set.Ioc rG sG,
            obs xg y x * (Real.exp (xg - center) : ℂ) / (y : ℂ)) x *
        movingPatternHaarProduct e (fun q : primes => (q : ℕ)) (fun q => hprimes _ q.property)
          n t small (movingPatternBulkLeaves n m slot (Equiv.refl _)) pattern x‖ ≤
      (2 * Real.exp 1 * (((2 : ℝ) ^ Fintype.card Cidx * Eprior ^ (4 * n * 2 ^ n - Fintype.card Cidx)) *
        (cost * movingInternalArithmeticError n (Fintype.card Cidx)
          (2 ^ n * (r₀ + m + 4 * n + 4)) (Real.exp (A * m)) Uall αall βint Vint +
        ((((((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) *
          Bφ ^ (2 ^ n - 1)) ^ 2) * A₀) * 2 ^ Fintype.card (TreeLeafIndex n × Fin m)) + Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
          2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)))))) / rG := by
  filter_upwards [P.movingPattern_same_assignment_mixed_prime_arithmetic_rate ψ n r₀ k
    A Wwin Bφ Dφ Cmass hA hWwin hCmass hBφ hDφ,
    eventually_ge_atTop (0 : ℝ)] with L hrate hL
  dsimp only
  intro lo hi hlo hhi hwindow Bidx Cidx _ _ Cell _ N e tierB tierC t Sfreq ft Nfreq Vleaf D small slot pattern rep
    primes hprimes _ childBound pivotBound hfreq Fw outside _ p _ hc _ twist sets
    Qfreq X j₀ φ G u v deleted initial μ ν W Eprior αall βint Vint Uall uG vG rG sG center
    huG hrG huvG hrsG hvG hsG hcenter
    hsmall hB htier hsmallLen ht hS hN hleaf hD hdiv hm hp hfreqp hbase
    hsmallp hsamplesp hV hsets hsetsp hpupper hMQ hφ hlip hφout
    hcard hu hulow huv hshort hsep hMcell hSS hdel hmass hdelbase hout hdelout
    c₀ hsub hretain hν hμ0 hν0 hμmass hνmass hEprior hαall hβint hVint hUall
    hμbound hμall hνall hμmax hμmin hvalues hWmeas hW hWbulk hdisjoint hcross hfmod
  let m := spectatorBulkCount k L
  let R := frequencyModelBase Sfreq n ft
  let data := movingPatternFinBulkData e n m t small slot (Equiv.refl _) pattern
  let raw := fun xg y => movingPatternPrimeObservable e t small slot (Equiv.refl _) pattern
    primes hprimes childBound pivotBound hfreq Fw (fun _ _ _ _ _ => 1) outside (R : ℤ)
    (R ^ (n - 1 + 2)) p (fun i => normalizedResidueTransform (sets i)) twist P Qfreq y ψ X lo hi hlo hhi φ G (Real.exp xg) (Real.exp y)
  let obs := fun xg y x => W xg y x * raw xg y x
  let amp := 2 * (‖movingDataWeight (Fw false) (fun _ _ _ _ => 1) (data false)‖ *
    ‖movingDataWeight (Fw true) (fun _ _ _ _ => 1) (data true)‖)
  let cost := (amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) *
    (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n *
      (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
  let A₀ := ((2 : ℝ) ^ (2 ^ n * m) * 2 * 3 ^ (2 ^ n * m)) *
    (frequencyLeafWeight (pairedFrequencyLeaf Sfreq Vleaf) n ft *
      ((frequencySplitList Sfreq n ft).map (pairFrequencySupportBound D)).prod)
  let bound := ((2 : ℝ) ^ Fintype.card Cidx * Eprior ^ (4 * n * 2 ^ n - Fintype.card Cidx)) *
        (cost * movingInternalArithmeticError n (Fintype.card Cidx)
          (2 ^ n * (r₀ + m + 4 * n + 4)) (Real.exp (A * m)) Uall αall βint Vint +
        ((((((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) *
          Bφ ^ (2 ^ n - 1)) ^ 2) * A₀) * 2 ^ Fintype.card (TreeLeafIndex n × Fin m)) + Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
          2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))))
  have hmean (xg : ℝ) (hxg : xg ∈ Set.Ioc uG vG) (y : ℝ) (hy : y ∈ Set.Ioc rG sG) :
      ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern
          (obs xg y) x * movingPatternHaarProduct e (fun q : primes => (q : ℕ))
          (fun q => hprimes _ q.property) n t small
          (movingPatternBulkLeaves n m slot (Equiv.refl _)) pattern x‖ ≤ bound := by
    exact hrate lo hi hlo hhi hwindow Bidx Cidx Cell N e tierB tierC t Sfreq ft Nfreq Vleaf D small slot pattern rep
      primes hprimes childBound pivotBound hfreq Fw outside p hc twist sets Qfreq y X j₀ φ G
      (Real.exp xg) (Real.exp y) u v deleted initial μ ν (W xg y) Eprior αall βint Vint Uall
      hsmall hB htier hsmallLen ht hS hN hleaf hD hdiv hm hp hfreqp hbase
      hsmallp hsamplesp hV hsets hsetsp (by linarith [hy.1])
      hpupper hMQ hφ hlip hφout hcard hu hulow huv hshort hsep hMcell hSS hdel hmass
      hdelbase hout hdelout c₀ hsub hretain hν hμ0 hν0 hμmass hνmass hEprior hαall hβint
      hVint hUall hμbound hμall hνall hμmax hμmin hvalues (hW xg y) (hWbulk xg y)
      (hdisjoint xg hxg y hy) (hcross xg hxg y hy) (hfmod xg hxg y hy)
  have hA₀ : 0 ≤ A₀ := by
    have hleaf0 := frequencyLeafWeight_nonneg (pairedFrequencyLeaf Sfreq Vleaf)
      (fun _ => by unfold pairedFrequencyLeaf; split_ifs <;> norm_num) n ft
    have hprod : 0 ≤ ((frequencySplitList Sfreq n ft).map (pairFrequencySupportBound D)).prod := by
      apply List.prod_nonneg
      intro z hz
      obtain ⟨f, _, rfl⟩ := List.mem_map.mp hz
      exact pairFrequencySupportBound_nonneg D f
    exact mul_nonneg (by positivity) (mul_nonneg hleaf0 hprod)
  have hcost : 0 ≤ cost := by dsimp only [cost, amp]; positivity
  have herr := movingInternalArithmeticError_nonneg n (Fintype.card Cidx)
    (2 ^ n * (r₀ + m + 4 * n + 4)) (Real.exp (A * m)) Uall αall βint Vint
    (Real.one_le_exp (mul_nonneg hA (Nat.cast_nonneg m))) hUall hαall hβint hVint.le
  have hbound : 0 ≤ bound := by dsimp only [bound]; positivity
  apply movingPattern_mixed_harmonic_integral_bound e (fun q : primes => (q : ℕ))
    (fun q => hprimes _ q.property) μ ν t small (movingPatternBulkLeaves n m slot (Equiv.refl _))
    pattern (fun x xg y => obs xg y x) _ uG vG rG sG center bound huG hrG huvG hrsG hvG hsG hcenter
    hbound (fun _ => cost) (fun _ => hcost) _ hmean
  · intro x
    exact (hWmeas x).mul (movingPatternPrimeObservable_measurable e t small slot (Equiv.refl _) pattern
      primes hprimes childBound pivotBound hfreq Fw (fun _ _ _ _ _ => 1) outside (R : ℤ)
      (R ^ (n - 1 + 2)) p (fun i => normalizedResidueTransform (sets i)) twist P Qfreq ψ X lo hi hlo hhi φ G Bφ Dφ hBφ hDφ hφ hlip hφout x)
  · intro x xg hxg y hy
    have hh := movingPatternPrimeObservable_norm e tierB tierC t small slot (Equiv.refl _) pattern
      hB htier primes hprimes childBound pivotBound hfreq Fw (fun _ _ _ _ _ => 1) outside (R : ℤ)
      (R ^ (n - 1 + 2)) p (fun i => normalizedResidueTransform (sets i)) twist P Qfreq y j₀ ψ X lo hi (Real.exp (A * m)) hlo hhi hV φ G
      Bφ Dφ hBφ hDφ hφ hlip hφout (Real.exp xg) (Real.exp y)
      (by linarith [hy.1]) (fun i => (p i : ℝ)) (fun _ => Nat.cast_nonneg _)
      (fun i z => normalizedResidueTransform_norm_le_prime (sets i) (hsets i) (hsetsp i) z) x
    change ‖W xg y x * raw xg y x‖ ≤ cost
    rw [norm_mul]
    exact (mul_le_mul (hW xg y x) hh (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternDiagonalIdealRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual two-prime arithmetic bound integrated over its giant cells -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.movingPattern_diagonal_ideal_integral_rate_oai
    (P : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A Wwin Bφ Dφ Cmass : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hCmass : 1 ≤ Cmass)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi),
      hi - lo ≤ Real.exp (Wwin * m) →
      ∀ (Bidx Cidx : Type) [Fintype Bidx] [Fintype Cidx] (Cell : Type) [Fintype Cell] (N : ℕ)
        (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (tierB : Bidx → ℕ) (tierC : Cidx → ℕ)
        (t : Bool → FrequencyTree ℤ n)
        (Sfreq : Finset ℤ) (ft : FrequencyTree (Sfreq × Sfreq) n) (Nfreq Vleaf : ℕ) (D : ℝ)
        (small : Bool → TreeLeafTuple (List Bidx) n)
        (slot : (TreeLeafIndex n × Fin m) ↪ Bidx)
        (pattern : Bool × MovingSampleIndex n → Cidx)
        (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
        (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (childBound pivotBound : ℕ → ℕ)
        (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
        (Fw : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℂ)
        (outside : List ℕ) [NeZero ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2))]
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (_hc : Pairwise (fun i j => (bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i).Coprime (bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p j)))
        [NeZero (∏ i, bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i)]
        (twist : ∀ i, Bool → (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (Qfreq : ℕ) (X : ℝ) (_j₀ : TreeLeafIndex n × Fin m)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (u v : (TreeLeafIndex n × Fin m) → Cell → ℝ)
        (deleted : (Fin (N + 1) → primes) →
          (TreeLeafIndex n × Fin m) → Finset ℕ)
        (initial : (TreeLeafIndex n × Fin m) → Finset ℕ)
        (μ : ℕ → primes → ℝ) (ν : Bidx → primes → ℝ)
        (Jidx : Type) [Fintype Jidx] (reg : Jidx → Fin (N + 1)) (active : Jidx → Bool)
        (Jleft Jright : ℝ) (diagonal : Bool)
        (Eprior αall βint Vint Uall : ℝ) (uG vG rG sG center : ℝ),
      let data := movingPatternFinBulkData e n m t small slot (Equiv.refl _) pattern
      let A₀ := ((2 : ℝ) ^ (2 ^ n * m) * 2 * 3 ^ (2 ^ n * m)) *
        (frequencyLeafWeight (pairedFrequencyLeaf Sfreq Vleaf) n ft *
          ((frequencySplitList Sfreq n ft).map (pairFrequencySupportBound D)).prod)
      let M := ∏ i, bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i
      let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
        (fun c => u j c.1) (fun c => v j c.1)
      let amp := 2 * (‖movingDataWeight (Fw false) ((fun _ _ _ _ _ => 1) false) (data false)‖ *
        ‖movingDataWeight (Fw true) ((fun _ _ _ _ _ => 1) true) (data true)‖)
      let law := fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)
      let raw := fun xg y => movingPatternPrimeObservable e t small slot (Equiv.refl _) pattern primes hprimes
        childBound pivotBound hfreq Fw (fun _ _ _ _ _ => 1) outside ((frequencyModelBase Sfreq n ft) : ℤ) ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p
        (fun i => normalizedResidueTransform (sets i)) twist P Qfreq
        y ψ X lo hi hlo hhi φ G (Real.exp xg) (Real.exp y)
      let W := movingDiagonalOuterWeight (fun q : primes => (q : ℕ)) reg active φ Jleft Jright Bφ Dφ diagonal
      let obs := fun xg y x => W xg y x * raw xg y x
      let cost := (amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) *
        (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n *
          (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
      1 ≤ uG → 1 ≤ rG → uG ≤ vG → rG ≤ sG → vG ≤ uG + 1 → sG ≤ rG + 1 → vG ≤ center + 1 →
      (∀ b, ∀ i ∈ flattenMovingSlots n (small b), i ∉ Set.range slot) →
      (∀ i, n ≤ tierB i) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      (∀ b, MovingLeafLengthLE n (small b) r₀) →
      t = (fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n b ft)) →
      (∀ s ∈ Sfreq, s ≠ 0) → (∀ s ∈ Sfreq, s.natAbs ≤ Nfreq) →
      (∀ b s regular, ‖Fw b (.leaf s regular) s‖ ≤ if s.natAbs ≤ Vleaf then 1 else 0) →
      0 ≤ D → (∀ q : ℕ, q ≠ 0 → q ≤ Nfreq ^ 2 → (q.divisors.card : ℝ) ≤ D) →
      0 < m → (∀ i, 3 ≤ p i) → (∀ i b, movingGiantFrequencyUnits (p i) n (t b)) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 →
        ∀ i, i ∉ Set.range (movingPatternBulkEmbedding e slot) → IsCoprime ((x i : ℕ) : ℤ) ((frequencyModelBase Sfreq n ft) : ℤ)) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 → ∀ i b j,
        j ∈ flattenMovingSlots n (small b) → ((x (e.symm (.inl j)) : ℕ) : ZMod (p i)) ≠ 0) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 → ∀ i c,
        ((x (e.symm (.inr c)) : ℕ) : ZMod (p i)) ≠ 0) →
      (∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ Real.exp (A * m)) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      M ≤ bulkProgressionCutoff L →
      (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) →
      (Fintype.card Cell : ℝ) ≤ Real.exp (Real.exp ((14 / 10000 : ℝ) * L)) →
      (∀ j c, 1 ≤ u j c) → (∀ j c, Real.exp ((39 / 10000 : ℝ) * L) ≤ u j c) →
      (∀ j c, u j c ≤ v j c) → (∀ j c, v j c ≤ u j c + 1) →
      (∀ j c d, c ≠ d → v j c ≤ u j d ∨ v j d ≤ u j c) →
      (∀ j c, (M : ℝ) ≤ Real.exp (u j c)) →
      (∀ j, S j ⊆ primes) →
      (∀ x, productPrior law x ≠ 0 →
        ∀ j, ((deleted x j).card : ℝ) ≤ Real.exp (Cmass * L)) →
      (∀ j, Real.exp (-Cmass * L) ≤ ∑ q ∈ S j, (q : ℝ)⁻¹) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 →
        ∀ j i, i ∉ Set.range (movingPatternBulkEmbedding e slot) → (x i : ℕ) ∈ deleted x j) →
      (∀ q ∈ outside, q.Prime) →
      (∀ x, productPrior law x ≠ 0 → ∀ j q, q ∈ outside → q ∈ deleted x j) →
      ∀ _c₀ : Cell × (ZMod M)ˣ,
      (∀ j, initial j ⊆ S j) →
      (∀ x, productPrior law x ≠ 0 → ∀ j, S j \ deleted x j ⊆ initial j) →
      (∀ j, ν (slot j) = primeSubsetPrior primes (initial j)) →
      (∀ j q, 0 ≤ μ j q) → (∀ j q, 0 ≤ ν j q) →
      (∀ j, ∑ q, μ j q = 1) → (∀ j, ∑ q, ν j q = 1) →
      0 ≤ Eprior → 0 ≤ αall → 0 ≤ βint → 0 < Vint → 1 ≤ Uall →
      (∀ j (q : primes), (q : ℝ) * μ j q ≤ Eprior) →
      (∀ j q, μ j q ≤ αall) → (∀ j q, ν j q ≤ αall) →
      (∀ c q, μ (movingSampleTier (rep c).val.2) q ≤ βint) →
      (∀ c q, μ (movingSampleTier (rep c).val.2) q ≠ 0 → Real.exp Vint ≤ (q : ℝ)) →
      (∀ q : primes, (q : ℝ) ≤ Uall) →
      (∀ j, active j = false → reg j ∉ Set.range (movingPatternBulkEmbedding e slot)) →
      (∀ xg ∈ Set.Ioc uG vG, ∀ y ∈ Set.Ioc rG sG, ∀ x, productPrior law x ≠ 0 → obs xg y x ≠ 0 → ∀ i j,
        (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) →
          (x i : ℕ) ≠ (x j : ℕ)) →
      (∀ xg ∈ Set.Ioc uG vG, ∀ y ∈ Set.Ioc rG sG, ∀ x, productPrior law x ≠ 0 → obs xg y x ≠ 0 → ∀ b c,
        (x (e.symm (.inl b)) : ℕ) ≠ (x (e.symm (.inr c)) : ℕ)) →
      (∀ xg ∈ Set.Ioc uG vG, ∀ y ∈ Set.Ioc rG sG, ∀ x, productPrior law x ≠ 0 → obs xg y x ≠ 0 → ∀ c b, (data b).Frequencies
        (fun s => (s : ZMod (x (e.symm (.inr c)) : ℕ)) ≠ 0)) →
      ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern
          (fun x => ∫ xg in Set.Ioc uG vG, ∫ y in Set.Ioc rG sG,
            ((giantOuterWeight φ Jleft Jright diagonal (Real.exp xg) (Real.exp y) *
              (inactiveRegularDensity (fun q : primes => (q : ℕ)) reg active x : ℂ)) * raw xg y x) *
              (Real.exp (xg - center) : ℂ) / (y : ℂ)) x *
        movingPatternHaarProduct e (fun q : primes => (q : ℕ)) (fun q => hprimes _ q.property)
          n t small (movingPatternBulkLeaves n m slot (Equiv.refl _)) pattern x‖ ≤
      diagonalOuterMajorant Bφ Dφ diagonal * ((2 * Real.exp 1 * (((2 : ℝ) ^ Fintype.card Cidx * Eprior ^ (4 * n * 2 ^ n - Fintype.card Cidx)) *
        (cost * movingInternalArithmeticError n (Fintype.card Cidx)
          (2 ^ n * (r₀ + m + 4 * n + 4)) (Real.exp (A * m)) Uall αall βint Vint +
        ((((((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) *
          Bφ ^ (2 ^ n - 1)) ^ 2) * A₀) * 2 ^ Fintype.card (TreeLeafIndex n × Fin m)) + Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
          2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)))))) / rG) := by
  filter_upwards [P.movingPattern_same_assignment_mixed_prime_integral_rate ψ n r₀ k
    A Wwin Bφ Dφ Cmass hA hWwin hCmass hBφ hDφ] with L hrate
  dsimp only
  intro lo hi hlo hhi hwindow Bidx Cidx _ _ Cell _ N e tierB tierC t Sfreq ft Nfreq Vleaf D small slot pattern rep
    primes hprimes _ childBound pivotBound hfreq Fw outside _ p _ hc _ twist sets
    Qfreq X j₀ φ G u v deleted initial μ ν Jidx _ reg active Jleft Jright diagonal Eprior αall βint Vint Uall uG vG rG sG center
    huG hrG huvG hrsG hvG hsG hcenter
    hsmall hB htier hsmallLen ht hS hN hleaf hD hdiv hm hp hfreqp hbase
    hsmallp hsamplesp hV hsets hsetsp hpupper hMQ hφ hlip hφout
    hcard hu hulow huv hshort hsep hMcell hSS hdel hmass hdelbase hout hdelout
    c₀ hsub hretain hν hμ0 hν0 hμmass hνmass hEprior hαall hβint hVint hUall
    hμbound hμall hνall hμmax hμmin hvalues hfixed hdisjoint hcross hfmod
  let m := spectatorBulkCount k L
  let R := frequencyModelBase Sfreq n ft
  let raw := fun xg y => movingPatternPrimeObservable e t small slot (Equiv.refl _) pattern
    primes hprimes childBound pivotBound hfreq Fw (fun _ _ _ _ _ => 1) outside (R : ℤ)
    (R ^ (n - 1 + 2)) p (fun i => normalizedResidueTransform (sets i)) twist P Qfreq y
    ψ X lo hi hlo hhi φ G (Real.exp xg) (Real.exp y)
  let W := movingDiagonalOuterWeight (fun q : primes => (q : ℕ)) reg active φ
    Jleft Jright Bφ Dφ diagonal
  have hh := hrate lo hi hlo hhi hwindow Bidx Cidx Cell N e tierB tierC t Sfreq ft Nfreq Vleaf D
    small slot pattern rep primes hprimes childBound pivotBound hfreq Fw outside p hc twist sets
    Qfreq X j₀ φ G u v deleted initial μ ν W Eprior αall βint Vint Uall uG vG rG sG center
    huG hrG huvG hrsG hvG hsG hcenter
    hsmall hB htier hsmallLen ht hS hN hleaf hD hdiv hm hp hfreqp hbase
    hsmallp hsamplesp hV hsets hsetsp hpupper hMQ hφ hlip hφout
    hcard hu hulow huv hshort hsep hMcell hSS hdel hmass hdelbase hout hdelout
    c₀ hsub hretain hν hμ0 hν0 hμmass hνmass hEprior hαall hβint hVint hUall
    hμbound hμall hνall hμmax hμmin hvalues
    (movingDiagonalOuterWeight_measurable (fun q : primes => (q : ℕ)) reg active φ
      Jleft Jright Bφ Dφ hBφ hDφ hφ hlip hφout diagonal)
    (fun xg y x => movingDiagonalOuterWeight_norm (fun q : primes => (q : ℕ))
      (fun q => hprimes _ q.property) reg active φ Jleft Jright Bφ Dφ hBφ hDφ hφ hlip hφout
      diagonal xg y x)
    (fun xg y x z => movingDiagonalOuterWeight_bulk (fun q : primes => (q : ℕ)) reg active
      (movingPatternBulkEmbedding e slot) hfixed φ Jleft Jright Bφ Dφ diagonal xg y x z)
    hdisjoint hcross hfmod
  exact movingPattern_diagonal_integral_norm e (fun q : primes => (q : ℕ)) μ ν pattern
    reg active φ Jleft Jright Bφ Dφ diagonal raw
    (movingPatternHaarProduct e (fun q : primes => (q : ℕ)) (fun q => hprimes _ q.property)
      n t small (movingPatternBulkLeaves n m slot (Equiv.refl _)) pattern)
    uG vG rG sG center _ hh

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.PublishedProgressionInput.movingPattern_diagonal_ideal_integral_rate_oai := @OAI.Ostmann.PublishedProgressionInput.movingPattern_diagonal_ideal_integral_rate_oai
