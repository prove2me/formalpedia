-- Prove2me | solution 1 for OAI.Ostmann.common_center_biased_populations_impossible
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:00:10.006298+00:00
-- url     : https://prove2.me/submissions/e4a94cf3-0e8e-41a2-a7d8-c8ef1f7e94d9

import Mathlib
import Definitions.Def_OAIQ095D008

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

theorem nat_residue_population_card_le (S : Finset ℕ) (q D : ℕ) (hq : 0 < q)
    (hdiam : ∀ a ∈ S, ∀ b ∈ S, Nat.dist a b ≤ D) :
    (S.card : ℝ) ≤ ((S.image (fun n : ℕ => (n : ZMod q))).card : ℝ) * ((D : ℝ) / q + 2) := by
  let R := S.image (fun n : ℕ => (n : ZMod q))
  have hf (r : ZMod q) : ((S.filter fun n : ℕ => (n : ZMod q) = r).card : ℝ) ≤ (D : ℝ) / q + 2 := by
    apply nat_progression_population_card_le _ q D hq
    · intro a ha b hb
      exact hdiam a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
    · intro a ha b hb
      exact (ZMod.natCast_eq_natCast_iff a b q).mp
        ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
  have heq := Finset.card_eq_sum_card_image (fun n : ℕ => (n : ZMod q)) S
  calc
    (S.card : ℝ) = ∑ r ∈ R, ((S.filter fun n : ℕ => (n : ZMod q) = r).card : ℝ) := by
      exact_mod_cast heq
    _ ≤ ∑ _r ∈ R, ((D : ℝ) / q + 2) := Finset.sum_le_sum fun r _ => hf r
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rfl

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
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_UnitResidueGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform square-root growth of the number of quadratic unit roots -/

namespace Ostmann

theorem exists_unit_residue_sqrt_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, m ≠ 0 →
      (2 : ℝ) ^ (m.primeFactors.card + 1) ≤ C * Real.sqrt m := by
  obtain ⟨D, hD, hbound⟩ := exists_divisors_power_bound 2
  refine ⟨2 * Real.sqrt D, by positivity, ?_⟩
  intro m hm
  have hω : (2 : ℝ) ^ m.primeFactors.card ≤ m.divisors.card := by
    exact_mod_cast two_pow_primeFactors_card_le_divisors_card m hm
  have htau : (m.divisors.card : ℝ) ^ 2 ≤ (D : ℝ) * m := by
    exact_mod_cast hbound m hm
  have hsq : ((2 : ℝ) ^ m.primeFactors.card) ^ 2 ≤ (D : ℝ) * m :=
    (pow_le_pow_left₀ (by positivity) hω 2).trans htau
  have hs := Real.le_sqrt_of_sq_le hsq
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ D)] at hs
  rw [pow_succ]
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DistinctTupleProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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

theorem distinct_tuple_sum {A R : Type*} [Fintype A] [DecidableEq A]
    [CommSemiring R] (k : ℕ) (y : A → R) :
    (∑ e : Fin k ↪ A, ∏ i, y (e i)) =
      (k.factorial : R) * ∑ Q ∈ (Finset.univ : Finset A).powersetCard k, ∏ a ∈ Q, y a := by
  have hmaps (e : Fin k ↪ A) (_ : e ∈ (Finset.univ : Finset (Fin k ↪ A))) :
      tupleImage e ∈ (Finset.univ : Finset A).powersetCard k := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    have hc : (Finset.univ.image e).card = (Finset.univ : Finset (Fin k)).card :=
      Finset.card_image_iff.mpr e.injective.injOn
    simpa only [tupleImage, Finset.card_univ, Fintype.card_fin] using hc
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Q hQ
  have hcard := (Finset.mem_powersetCard.mp hQ).2
  have hprod (e : Fin k ↪ A) (he : tupleImage e = Q) :
      (∏ i, y (e i)) = ∏ a ∈ Q, y a := by
    rw [← he, tupleImage, Finset.prod_image e.injective.injOn]
  calc
    _ = ∑ _e ∈ (Finset.univ : Finset (Fin k ↪ A)).filter (fun e => tupleImage e = Q),
        ∏ a ∈ Q, y a := by
      apply Finset.sum_congr rfl
      intro e he
      exact hprod e (Finset.mem_filter.mp he).2
    _ = _ := by
      rw [Finset.sum_const]
      have hf : ((Finset.univ : Finset (Fin k ↪ A)).filter (fun e => tupleImage e = Q)).card =
          k.factorial := by
        simpa only [Fintype.card_subtype] using card_tupleImage_fiber k Q hcard
      rw [hf]
      simp only [nsmul_eq_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RepeatRemovalAsymptotics
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The chosen prime population makes the relative deletion error small -/

namespace Ostmann

open Filter Asymptotics

theorem eventual_repeat_power_budget (C ε : ℝ) (hC : 1 ≤ C) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ (k : ℕ) (K : ℝ),
      (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ K →
      (16 * C * T * (k : ℝ) ^ 3) ^ k * C ^ 2 ≤ Real.exp (ε * K) := by
  let B := 128 * C
  let D := 2 * B + 8 + 2 * C
  have hC0 : 0 ≤ C := by linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hl := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 10 by norm_num)).bound zero_lt_one
  have hp := (tendsto_rpow_atTop
    (show (0 : ℝ) < 9999999 / 10000000 - 7 / 10 by norm_num)).eventually_ge_atTop
    (1000 * D / ε)
  filter_upwards [hl, hp, eventually_ge_atTop (1 : ℝ)] with T hlog hpow hT k K hk hK
  have hTpos : 0 < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hlog' : Real.log T ≤ T ^ (1 / 10 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlogT,
      abs_of_nonneg (Real.rpow_nonneg hTpos.le _), one_mul] using hlog
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hρ : T ^ (3 / 5 : ℝ) ≤ T := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT (show (3 / 5 : ℝ) ≤ 1 by norm_num)
  have hkT : (k : ℝ) ≤ 2 * T := hk.trans (by gcongr)
  have hbase : 16 * C * T * (k : ℝ) ^ 3 ≤ Real.exp (B + 4 * Real.log T) := by
    calc
      _ ≤ 16 * C * T * (2 * T) ^ 3 := by gcongr
      _ = B * T ^ 4 := by dsimp [B]; ring
      _ ≤ Real.exp B * T ^ 4 := by gcongr; linarith [Real.add_one_le_exp B]
      _ = Real.exp (B + 4 * Real.log T) := by
        rw [Real.exp_add]
        congr 1
        simpa only [Nat.cast_ofNat, Real.exp_log hTpos] using
          (Real.exp_nat_mul (Real.log T) 4).symm
  have hklog : (k : ℝ) * Real.log T ≤ 2 * T ^ (7 / 10 : ℝ) := by
    calc
      _ ≤ (2 * T ^ (3 / 5 : ℝ)) * T ^ (1 / 10 : ℝ) :=
        mul_le_mul hk hlog' hlogT (by positivity)
      _ = _ := by rw [mul_assoc, ← Real.rpow_add hTpos]; norm_num
  have hρ' : T ^ (3 / 5 : ℝ) ≤ T ^ (7 / 10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
  have h1 : (1 : ℝ) ≤ T ^ (7 / 10 : ℝ) := Real.one_le_rpow hT (by norm_num)
  have hexp : (k : ℝ) * (B + 4 * Real.log T) + 2 * C ≤ D * T ^ (7 / 10 : ℝ) := by
    have hk7 : (k : ℝ) ≤ 2 * T ^ (7 / 10 : ℝ) :=
      hk.trans (mul_le_mul_of_nonneg_left hρ' (by norm_num))
    have hkb := mul_le_mul_of_nonneg_left hk7 hB
    have hc := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * C by positivity)
    dsimp [D]
    nlinarith only [hkb, hc, hklog]
  have hbudget : D * T ^ (7 / 10 : ℝ) ≤ ε * K := by
    have hp' := (div_le_iff₀ hε).mp hpow
    have hh := mul_le_mul_of_nonneg_right hp' (Real.rpow_nonneg hTpos.le (7 / 10 : ℝ))
    have heq : T ^ (9999999 / 10000000 - 7 / 10 : ℝ) * T ^ (7 / 10 : ℝ) =
        T ^ (9999999 / 10000000 : ℝ) := by
      rw [← Real.rpow_add hTpos]
      norm_num
    have heq' : (T ^ (9999999 / 10000000 - 7 / 10 : ℝ) * ε) * T ^ (7 / 10 : ℝ) =
        ε * T ^ (9999999 / 10000000 : ℝ) := by rw [mul_right_comm, heq, mul_comm]
    rw [heq'] at hh
    have hK' := mul_le_mul_of_nonneg_left hK hε.le
    nlinarith only [hh, hK']
  calc
    _ ≤ (Real.exp (B + 4 * Real.log T)) ^ k * (Real.exp C) ^ 2 := by
      apply mul_le_mul (pow_le_pow_left₀ (by positivity) hbase k) _ (sq_nonneg C) (by positivity)
      exact pow_le_pow_left₀ hC0 (by linarith [Real.add_one_le_exp C]) 2
    _ = Real.exp ((k : ℝ) * (B + 4 * Real.log T) + 2 * C) := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      norm_num
    _ ≤ _ := Real.exp_le_exp.mpr (hexp.trans hbudget)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_PrimeSubsetProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Products of distinct primes index the amplified coefficient array -/

namespace Ostmann

open scoped BigOperators Classical

theorem primeSubset_product_injective (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    Set.InjOn (fun Q : Finset ℕ => ∏ p ∈ Q, p) {Q | Q ⊆ P} := by
  intro Q hQ R hR heq
  have h := congrArg Nat.primeFactors heq
  rwa [Nat.primeFactors_prod (fun p hp => hP p (hQ hp)),
    Nat.primeFactors_prod (fun p hp => hP p (hR hp))] at h

theorem primeSubsetProducts_card (P : Finset ℕ) (k : ℕ)
    (hP : ∀ p ∈ P, p.Prime) : (primeSubsetProducts P k).card = P.card.choose k := by
  rw [primeSubsetProducts, Finset.card_image_iff.mpr]
  · exact Finset.card_powersetCard k P
  · intro Q hQ R hR h
    exact primeSubset_product_injective P hP
      (Finset.mem_powersetCard.mp hQ).1 (Finset.mem_powersetCard.mp hR).1 h

theorem primeSubsetProducts_mem_range (P : Finset ℕ) (k Z : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, Odd p)
    (hZ : ∀ p ∈ P, p ≤ Z) : primeSubsetProducts P k ⊆ oddSquarefreeRange (Z ^ k) := by
  intro s hs
  obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨hQP, hcard⟩ := Finset.mem_powersetCard.mp hQ
  have hprime : ∀ p ∈ Q, p.Prime := fun p hp => hP p (hQP hp)
  have hsf := primeSubset_product_squarefree Q hprime
  refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hsf.ne_zero, ?_⟩, ?_, hsf⟩
  · simpa only [hcard] using Finset.prod_le_pow_card Q (fun p => p) Z (fun p hp => hZ p (hQP hp))
  · have ho : ∀ p ∈ Q, Odd p := fun p hp => hodd p (hQP hp)
    clear hprime hsf hcard hQP hQ hs
    induction Q using Finset.induction_on with
    | empty => simp
    | @insert p Q hp ih =>
      rw [Finset.prod_insert hp]
      exact (ho p (Finset.mem_insert_self _ _)).mul
        (ih (fun q hq => ho q (Finset.mem_insert_of_mem hq)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_Collision
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Elementary collision estimates

These are the finite probability and support-size inequalities used in §2
and in the final collision argument of §3. No analytic estimate is assumed.
-/

namespace Ostmann

open scoped BigOperators

/-- Cauchy--Schwarz bounds the collision probability of a unit mass on a
finite nonempty support by the reciprocal of the support's size. -/
theorem inverse_card_le_collision {α : Type*} (s : Finset α) (μ : α → ℝ)
    (hs : s.Nonempty) (hmass : ∑ x ∈ s, μ x = 1) :
    1 / (s.card : ℝ) ≤ ∑ x ∈ s, μ x ^ 2 := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  apply (div_le_iff₀ hc).mpr
  have h := sq_sum_le_card_mul_sum_sq (s := s) (f := μ)
  rw [hmass, one_pow] at h
  simpa only [mul_comm] using h

/-- Disjoint nonempty supports occupying at most `p` residues have combined
collision probability at least `4 / p`. -/
theorem four_div_le_inverse_add_inverse {a b p : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ p) :
    4 / p ≤ 1 / a + 1 / b := by
  have hp : 0 < p := lt_of_lt_of_le (add_pos ha hb) hab
  have habpos : 0 < a * b := mul_pos ha hb
  have hnum : 4 * (a * b) ≤ p * (a + b) := by
    nlinarith [sq_nonneg (a - b), mul_nonneg (le_of_lt (add_pos ha hb)) (sub_nonneg.mpr hab)]
  apply (div_le_iff₀ hp).mpr
  have hratio : 4 ≤ (p * (a + b)) / (a * b) := (le_div_iff₀ habpos).mpr hnum
  calc
    4 ≤ p * (a + b) / (a * b) := hratio
    _ = (1 / a + 1 / b) * p := by field_simp; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticKernelSeparation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Disjoint prime supports of the two endpoint kernel populations -/

namespace Ostmann

/-- A prime divisor of a kernel cannot divide the reduced denominator. -/
theorem kernel_prime_not_dvd_denominator (m : ℕ) (h x u t : ℤ)
    (hred : h.natAbs.Coprime m) (heq : u * t ^ 2 = (m : ℤ) * x - h)
    {p : ℕ} (hp : p.Prime) (hpu : p ∣ u.natAbs) : ¬p ∣ m := by
  intro hpm
  have hpu' : (p : ℤ) ∣ u := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hpu)
  have hpm' : (p : ℤ) ∣ (m : ℤ) := Int.natCast_dvd_natCast.mpr hpm
  have hph : (p : ℤ) ∣ h := by
    have hh := dvd_sub (dvd_mul_of_dvd_left hpm' x) (dvd_mul_of_dvd_left hpu' (t ^ 2))
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    linear_combination heq
  have hph' : p ∣ h.natAbs := Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hph)
  have hg := Nat.dvd_gcd hph' hpm
  rw [hred] at hg
  exact hp.not_dvd_one hg

/-- The sumset primality condition forces opposite-side kernels to have
disjoint prime factors. This is valid for signed kernels and endpoints. -/
theorem quadratic_kernels_coprime (m : ℕ) (h x y u v s t : ℤ)
    (hu0 : u ≠ 0)
    (hred : h.natAbs.Coprime m)
    (hx : u * s ^ 2 = (m : ℤ) * x - h)
    (hy : v * t ^ 2 = (m : ℤ) * y - h)
    (hprime : (x - y).natAbs.Prime)
    (hsmall : u.natAbs < (x - y).natAbs) :
    u.natAbs.Coprime v.natAbs := by
  apply Nat.coprime_of_dvd
  intro p hp hpu hpv
  have hpm := kernel_prime_not_dvd_denominator m h x u s hred hx hp hpu
  have hu : (p : ℤ) ∣ u := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hpu)
  have hv : (p : ℤ) ∣ v := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hpv)
  have hdiff : (p : ℤ) ∣ (m : ℤ) * (x - y) := by
    have hh := dvd_sub (dvd_mul_of_dvd_left hu (s ^ 2)) (dvd_mul_of_dvd_left hv (t ^ 2))
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    linear_combination -hx + hy
  have hn : p ∣ m * (x - y).natAbs := by
    have habs := Int.natAbs_dvd_natAbs.mpr hdiff
    simpa only [Int.natAbs_natCast, Int.natAbs_mul] using habs
  have hpn : p ∣ (x - y).natAbs := (hp.dvd_mul.mp hn).resolve_left hpm
  have heq : p = (x - y).natAbs :=
    (hprime.eq_one_or_self_of_dvd p hpn).resolve_left hp.ne_one
  have hup : 0 < u.natAbs := Int.natAbs_pos.mpr hu0
  exact (not_le_of_gt hsmall) (heq ▸ Nat.le_of_dvd hup hpu)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_KernelUnitResidues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unit residue constraints imposed by a reduced common center -/

namespace Ostmann

open scoped Classical

theorem kernel_root_coprime (m t : ℕ) (h x u : ℤ)
    (hred : h.natAbs.Coprime m) (heq : u * (t : ℤ) ^ 2 = (m : ℤ) * x - h) :
    t.Coprime m := by
  apply Nat.coprime_of_dvd
  intro p hp hpt hpm
  have hpt' : (p : ℤ) ∣ (t : ℤ) := Int.natCast_dvd_natCast.mpr hpt
  have hpm' : (p : ℤ) ∣ (m : ℤ) := Int.natCast_dvd_natCast.mpr hpm
  have hpterm : (p : ℤ) ∣ u * (t : ℤ) ^ 2 :=
    dvd_mul_of_dvd_right (dvd_pow hpt' (by omega)) u
  have hph : (p : ℤ) ∣ h := by
    have hd := dvd_sub (dvd_mul_of_dvd_left hpm' x) hpterm
    convert hd using 1
    all_goals try with_reducible_and_instances rfl
    linear_combination heq
  have hph' : p ∣ h.natAbs := Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hph)
  exact hp.not_dvd_one (hred ▸ Nat.dvd_gcd hph' hpm)

theorem kernel_coefficient_coprime (m : ℕ) (h x u t : ℤ)
    (hred : h.natAbs.Coprime m) (heq : u * t ^ 2 = (m : ℤ) * x - h) :
    u.natAbs.Coprime m := by
  apply Nat.coprime_of_dvd
  intro p hp hpu hpm
  exact kernel_prime_not_dvd_denominator m h x u t hred heq hp hpu hpm

theorem intCast_isUnit_of_natAbs_coprime (m : ℕ) (u : ℤ)
    (hc : u.natAbs.Coprime m) : IsUnit (u : ZMod m) := by
  have ha : IsUnit (u.natAbs : ZMod m) := (ZMod.unitOfCoprime u.natAbs hc).isUnit
  have habs : ((u.natAbs : ℤ) : ZMod m) = (u.natAbs : ZMod m) := by simp
  rcases le_total 0 u with hu | hu
  · have heq : (u.natAbs : ℤ) = u := by rw [Int.natCast_natAbs, abs_of_nonneg hu]
    rw [← heq, habs]
    exact ha
  · have heq : (u.natAbs : ℤ) = -u := by rw [Int.natCast_natAbs, abs_of_nonpos hu]
    have heq' : (u.natAbs : ZMod m) = -(u : ZMod m) := by
      rw [← habs, heq, Int.cast_neg]
    rw [heq'] at ha
    simpa using ha.neg

theorem kernel_square_residues (S : Finset ℤ) (root : ℤ → ℕ)
    (m : ℕ) (h u : ℤ) (hred : h.natAbs.Coprime m) (hS : S.Nonempty)
    (hroot : ∀ x ∈ S, u * (root x : ℤ) ^ 2 = (m : ℤ) * x - h) :
    ∃ a : (ZMod m)ˣ, ∀ x ∈ S,
      (root x).Coprime m ∧ (root x : ZMod m) ^ 2 = (a : ZMod m) := by
  obtain ⟨x0, hx0⟩ := hS
  have ht0 := kernel_root_coprime m (root x0) h x0 u hred (hroot x0 hx0)
  let a := (ZMod.unitOfCoprime (root x0) ht0) ^ 2
  refine ⟨a, fun x hx => ⟨kernel_root_coprime m (root x) h x u hred (hroot x hx), ?_⟩⟩
  have hu := intCast_isUnit_of_natAbs_coprime m u
    (kernel_coefficient_coprime m h x0 u (root x0) hred (hroot x0 hx0))
  have h1 := congrArg (fun z : ℤ => (z : ZMod m)) (hroot x hx)
  have h0 := congrArg (fun z : ℤ => (z : ZMod m)) (hroot x0 hx0)
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_sub,
    ZMod.natCast_self, zero_mul, zero_sub] at h1 h0
  have heq : (root x : ZMod m) ^ 2 = (root x0 : ZMod m) ^ 2 :=
    hu.mul_left_cancel (h1.trans h0.symm)
  simpa [a] using heq

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_RootResidueSeparation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scaled root populations have disjoint residues at split primes -/

namespace Ostmann

theorem kernel_roots_separated_mod_prime {p : ℕ} [Fact p.Prime]
    (m : ℕ) (h x y u v s t : ℤ) (c : ZMod p)
    (hpm : ¬p ∣ m)
    (hx : u * s ^ 2 = (m : ℤ) * x - h)
    (hy : v * t ^ 2 = (m : ℤ) * y - h)
    (hc : (u : ZMod p) * c ^ 2 = (v : ZMod p))
    (hprime : (x - y).natAbs.Prime) (hsmall : p < (x - y).natAbs) :
    (s : ZMod p) ≠ c * (t : ZMod p) := by
  intro hs
  have hm0 : (m : ZMod p) ≠ 0 := by
    intro hm
    exact hpm ((ZMod.natCast_eq_zero_iff m p).mp hm)
  have hx' : (u : ZMod p) * (s : ZMod p) ^ 2 =
      (m : ZMod p) * (x : ZMod p) - (h : ZMod p) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ZMod p)) hx
  have hy' : (v : ZMod p) * (t : ZMod p) ^ 2 =
      (m : ZMod p) * (y : ZMod p) - (h : ZMod p) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ZMod p)) hy
  have heq : (u : ZMod p) * (s : ZMod p) ^ 2 =
      (v : ZMod p) * (t : ZMod p) ^ 2 := by
    rw [hs, mul_pow, ← mul_assoc, hc]
  have hxy : (m : ZMod p) * ((x : ZMod p) - (y : ZMod p)) = 0 := by
    linear_combination -hx' + hy' + heq
  have hd0 : ((x - y : ℤ) : ZMod p) = 0 := by
    simpa only [Int.cast_sub] using (mul_eq_zero.mp hxy).resolve_left hm0
  have hd : (p : ℤ) ∣ x - y := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hd0
  have hdn : p ∣ (x - y).natAbs :=
    Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hd)
  have heq' : p = (x - y).natAbs :=
    (hprime.eq_one_or_self_of_dvd p hdn).resolve_left (Fact.out : p.Prime).ne_one
  omega

theorem kernel_root_images_disjoint {p : ℕ} [Fact p.Prime]
    (S T : Finset ℤ) (rootS rootT : ℤ → ℤ) (m : ℕ) (h u v : ℤ) (c : ZMod p)
    (hpm : ¬p ∣ m)
    (hS : ∀ x ∈ S, u * rootS x ^ 2 = (m : ℤ) * x - h)
    (hT : ∀ y ∈ T, v * rootT y ^ 2 = (m : ℤ) * y - h)
    (hc : (u : ZMod p) * c ^ 2 = (v : ZMod p))
    (hprime : ∀ x ∈ S, ∀ y ∈ T, (x - y).natAbs.Prime)
    (hsmall : ∀ x ∈ S, ∀ y ∈ T, p < (x - y).natAbs) :
    Disjoint (S.image (fun x => (rootS x : ZMod p)))
      (T.image (fun y => c * (rootT y : ZMod p))) := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hzS hzT
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hzS
  obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hzT
  exact kernel_roots_separated_mod_prime m h x y u v (rootS x) (rootT y) c hpm
    (hS x hx) (hT y hy) hc (hprime x hx y hy) (hsmall x hx y hy) hxy.symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_RootPopulationGeometry
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Diameter control for roots belonging to one signed quadratic kernel -/

namespace Ostmann

theorem square_sub_le_abs_square_difference (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a - b) ^ 2 ≤ |a ^ 2 - b ^ 2| := by
  by_cases hab : b ≤ a
  · have hs : 0 ≤ a ^ 2 - b ^ 2 := by nlinarith
    rw [abs_of_nonneg hs]
    nlinarith [mul_nonneg hb (sub_nonneg.mpr hab)]
  · have hab' : a ≤ b := le_of_not_ge hab
    have hs : a ^ 2 - b ^ 2 ≤ 0 := by nlinarith
    rw [abs_of_nonpos hs]
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hab')]

/-- Both signs of the squarefree kernel are allowed. Nonnegative root
parameters in an endpoint interval of diameter X have this diameter. -/
theorem kernel_root_diameter (u m h x y a b X : ℝ)
    (hu : u ≠ 0) (hm : 0 ≤ m) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : u * a ^ 2 = m * x - h) (hy : u * b ^ 2 = m * y - h)
    (hxy : |x - y| ≤ X) :
    |a - b| ≤ Real.sqrt (m * X / |u|) := by
  have hu0 : 0 < |u| := abs_pos.mpr hu
  have hdiff : u * (a ^ 2 - b ^ 2) = m * (x - y) := by nlinarith
  have habs := congrArg abs hdiff
  simp only [abs_mul, abs_of_nonneg hm] at habs
  have hp := square_sub_le_abs_square_difference a b ha hb
  have hsq : (a - b) ^ 2 ≤ m * X / |u| := by
    apply (le_div_iff₀ hu0).mpr
    have hmul := mul_le_mul_of_nonneg_left hp hu0.le
    have hsize := mul_le_mul_of_nonneg_left hxy hm
    nlinarith
  have hnonneg : 0 ≤ m * X / |u| := (sq_nonneg (a - b)).trans hsq
  have hroot := Real.sq_sqrt hnonneg
  have hroot0 := Real.sqrt_nonneg (m * X / |u|)
  nlinarith [sq_abs (a - b), abs_nonneg (a - b)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_RootPopulations
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete root populations attached to endpoint subsets -/

namespace Ostmann

open scoped Classical

theorem kernelRootPopulation_card (S : Finset ℤ) (root : ℤ → ℕ)
    (m : ℕ) (hm : 0 < m) (h u : ℤ)
    (hroot : ∀ x ∈ S, u * (root x : ℤ) ^ 2 = (m : ℤ) * x - h) :
    (kernelRootPopulation S root).card = S.card := by
  apply Finset.card_image_of_injOn
  intro x hx y hy heq
  have hx' := hroot x hx
  have hy' := hroot y hy
  rw [heq] at hx'
  have hmul : (m : ℤ) * x = (m : ℤ) * y := by omega
  exact mul_left_cancel₀ (by exact_mod_cast hm.ne' : (m : ℤ) ≠ 0) hmul

private theorem cast_nat_dist (a b : ℕ) :
    (Nat.dist a b : ℝ) = |(a : ℝ) - b| := by
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab, Nat.cast_sub hab, abs_of_nonpos]
    · ring
    · exact sub_nonpos.mpr (by exact_mod_cast hab)
  · rw [Nat.dist_eq_sub_of_le_right hba, Nat.cast_sub hba, abs_of_nonneg]
    exact sub_nonneg.mpr (by exact_mod_cast hba)

theorem kernelRootPopulation_diameter (S : Finset ℤ) (root : ℤ → ℕ)
    (m D : ℕ) (h u : ℤ) (hu : u ≠ 0) (X : ℝ)
    (hroot : ∀ x ∈ S, u * (root x : ℤ) ^ 2 = (m : ℤ) * x - h)
    (hspan : ∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ X)
    (hD : Real.sqrt ((m : ℝ) * X / |(u : ℝ)|) ≤ D) :
    ∀ a ∈ kernelRootPopulation S root, ∀ b ∈ kernelRootPopulation S root,
      Nat.dist a b ≤ D := by
  intro a ha b hb
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
  have hx' : (u : ℝ) * (root x : ℝ) ^ 2 = (m : ℝ) * (x : ℝ) - (h : ℝ) := by
    exact_mod_cast hroot x hx
  have hy' : (u : ℝ) * (root y : ℝ) ^ 2 = (m : ℝ) * (y : ℝ) - (h : ℝ) := by
    exact_mod_cast hroot y hy
  have hd := kernel_root_diameter (u : ℝ) (m : ℝ) (h : ℝ) (x : ℝ) (y : ℝ)
    (root x : ℝ) (root y : ℝ) X (by exact_mod_cast hu) (by positivity)
    (by positivity) (by positivity) hx' hy' (by exact_mod_cast hspan x hx y hy)
  have hd' : (Nat.dist (root x) (root y) : ℝ) ≤ D := by
    rw [cast_nat_dist]
    exact hd.trans hD
  exact_mod_cast hd'

theorem kernelRootPopulation_residues_disjoint {p : ℕ} [Fact p.Prime]
    (S T : Finset ℤ) (rootS rootT : ℤ → ℕ) (m : ℕ) (h u v : ℤ) (c : ZMod p)
    (hpm : ¬p ∣ m)
    (hS : ∀ x ∈ S, u * (rootS x : ℤ) ^ 2 = (m : ℤ) * x - h)
    (hT : ∀ y ∈ T, v * (rootT y : ℤ) ^ 2 = (m : ℤ) * y - h)
    (hc : (u : ZMod p) * c ^ 2 = (v : ZMod p))
    (hprime : ∀ x ∈ S, ∀ y ∈ T, (x - y).natAbs.Prime)
    (hsmall : ∀ x ∈ S, ∀ y ∈ T, p < (x - y).natAbs) :
    Disjoint ((kernelRootPopulation S rootS).image (fun a : ℕ => (a : ZMod p)))
      ((kernelRootPopulation T rootT).image (fun b : ℕ => c * (b : ZMod p))) := by
  have hsep := kernel_root_images_disjoint S T (fun x => (rootS x : ℤ))
    (fun y => (rootT y : ℤ)) m h u v c hpm hS hT hc hprime hsmall
  simpa only [kernelRootPopulation, Finset.image_image, Int.cast_natCast,
    Function.comp_def] using hsep

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_KernelResidueCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Few occupied residues for a fixed quadratic kernel -/

namespace Ostmann

open scoped Classical

theorem unit_square_residue_card_le (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) :
    ((Finset.univ : Finset (ZMod q)).filter
      (fun x => IsUnit x ∧ x ^ 2 = (a : ZMod q))).card ≤
        2 ^ (q.primeFactors.card + 1) := by
  let F := {x : ZMod q // IsUnit x ∧ x ^ 2 = (a : ZMod q)}
  let f : F → {x : (ZMod q)ˣ // x ^ 2 = a} := fun x =>
    ⟨x.property.1.unit, by
      apply Units.ext
      simpa only [Units.val_pow_eq_pow_val, IsUnit.unit_spec] using x.property.2⟩
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have hv := congrArg (fun z : {x : (ZMod q)ˣ // x ^ 2 = a} => (z.val : ZMod q)) h
    simpa only [f, IsUnit.unit_spec] using hv
  have hc := Fintype.card_le_of_injective f hinj
  have hb := unit_square_fiber_card_le q a
  rw [Nat.card_eq_fintype_card] at hb
  exact (show _ ≤ Fintype.card F from by simp [F, Fintype.card_subtype]).trans (hc.trans hb)

theorem kernel_root_residues_card_le (S : Finset ℤ) (root : ℤ → ℕ)
    (m : ℕ) [NeZero m] (h u : ℤ) (hred : h.natAbs.Coprime m)
    (hroot : ∀ x ∈ S, u * (root x : ℤ) ^ 2 = (m : ℤ) * x - h) :
    ((kernelRootPopulation S root).image (fun t : ℕ => (t : ZMod m))).card ≤
      2 ^ (m.primeFactors.card + 1) := by
  by_cases hS : S.Nonempty
  · obtain ⟨a, ha⟩ := kernel_square_residues S root m h u hred hS hroot
    apply (Finset.card_le_card (t := (Finset.univ : Finset (ZMod m)).filter
      (fun r => IsUnit r ∧ r ^ 2 = (a : ZMod m))) ?_).trans (unit_square_residue_card_le m a)
    intro r hr
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (ZMod.isUnit_iff_coprime _ _).mpr (ha x hx).1, (ha x hx).2⟩
  · simp [Finset.not_nonempty_iff_eq_empty.mp hS, kernelRootPopulation]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_PrimeDivisors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Prime-divisor budget in the collision argument

A distinct pair of integers at distance at most `X` contributes at most
`log X` to the sum of `log p` over primes at which it collides. This is the
elementary counting step behind the larger-sieve use in §§2–3.
-/

namespace Ostmann

open scoped BigOperators

/-- The off-diagonal prime-collision budget, in the ordered-pair convention. -/
theorem sum_log_congruent_primes_le_of_sub_le (P : Finset ℕ) {x y X : ℕ}
    (hxy : x < y) (hdiff : y - x ≤ X) (hprime : ∀ p ∈ P, p.Prime) :
    ∑ p ∈ P.filter (fun p => x ≡ y [MOD p]), Real.log (p : ℝ) ≤
      Real.log (X : ℝ) := by
  have hpos : 0 < y - x := Nat.sub_pos_of_lt hxy
  have hbudget := sum_log_prime_divisors_le (P.filter (fun p => x ≡ y [MOD p])) hpos
    (fun p hp => hprime p (Finset.mem_filter.mp hp).1)
    (fun p hp => (Finset.mem_filter.mp hp).2.dvd')
  exact hbudget.trans (Real.log_le_log (by exact_mod_cast hpos)
    (by exact_mod_cast hdiff))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_WeightedCollision
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weighted prime collisions

The elementary weighted pair count used in Lemma 2.5 (collision stability).
The diagonal is paid for by the largest atom; unequal pairs are paid for by
one logarithm of the interval length.
-/

namespace Ostmann

open scoped BigOperators

theorem primeCollisionWeight_self (P : Finset ℕ) (a : ℕ) :
    primeCollisionWeight P a a = ∑ p ∈ P, Real.log (p : ℝ) := by
  simp [primeCollisionWeight, Nat.ModEq.refl]

theorem primeCollisionWeight_symm (P : Finset ℕ) (a b : ℕ) :
    primeCollisionWeight P a b = primeCollisionWeight P b a := by
  unfold primeCollisionWeight
  congr 1
  ext p
  simp only [Finset.mem_filter]
  exact and_congr_right (fun _ => ⟨fun h => h.symm, fun h => h.symm⟩)

/-- The weighted pair count from an off-diagonal logarithmic budget. -/
theorem weighted_prime_collision_bound_of_budget (P S : Finset ℕ) (μ : ℕ → ℝ) (L m : ℝ)
    (hL : 0 ≤ L) (hP : ∀ p ∈ P, p.Prime) (hμ : ∀ a ∈ S, 0 ≤ μ a)
    (hmass : ∑ a ∈ S, μ a = 1) (hatom : ∀ a ∈ S, μ a ≤ m)
    (hbudget : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → primeCollisionWeight P a b ≤ L) :
    (∑ a ∈ S, ∑ b ∈ S, μ a * μ b * primeCollisionWeight P a b) ≤
      L + m * ∑ p ∈ P, Real.log (p : ℝ) := by
  classical
  let W : ℝ := ∑ p ∈ P, Real.log (p : ℝ)
  have hW : 0 ≤ W := Finset.sum_nonneg (fun p hp => Real.log_nonneg (by exact_mod_cast (hP p hp).one_le))
  have hpair : ∀ a ∈ S, ∀ b ∈ S,
      primeCollisionWeight P a b ≤ L + if a = b then W else 0 := by
    intro a ha b hb
    by_cases hab : a = b
    · subst b
      simp only [primeCollisionWeight_self, ite_true, if_true]
      dsimp [W] at *
      linarith
    · simpa [hab] using hbudget a ha b hb hab
  have hsquares : (∑ a ∈ S, μ a ^ 2) ≤ m := by
    calc
      (∑ a ∈ S, μ a ^ 2) ≤ ∑ a ∈ S, m * μ a := by
        apply Finset.sum_le_sum
        intro a ha
        nlinarith [hμ a ha, hatom a ha]
      _ = m := by rw [← Finset.mul_sum, hmass, mul_one]
  calc
    _ ≤ ∑ a ∈ S, ∑ b ∈ S, μ a * μ b * (L + if a = b then W else 0) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left (hpair a ha b hb) (mul_nonneg (hμ a ha) (hμ b hb))
    _ = L + W * ∑ a ∈ S, μ a ^ 2 := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      have hconstant : (∑ a ∈ S, ∑ b ∈ S, μ a * μ b * L) = L := by
        calc
          _ = ∑ a ∈ S, μ a * (∑ b ∈ S, μ b) * L := by
            apply Finset.sum_congr rfl
            intro a _
            rw [← Finset.sum_mul, ← Finset.mul_sum]
          _ = L := by
            rw [hmass]
            simp only [mul_one]
            rw [← Finset.sum_mul, hmass, one_mul]
      rw [hconstant]
      congr 1
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq]
      calc
        (∑ a ∈ S, if a ∈ S then μ a * μ a * W else 0) =
            ∑ a ∈ S, W * μ a ^ 2 := by
          apply Finset.sum_congr rfl
          intro a ha
          simp only [ha, ite_true, if_true]
          ring
        _ = W * ∑ a ∈ S, μ a ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ L + W * m := add_le_add_right (mul_le_mul_of_nonneg_left hsquares hW) L
    _ = _ := by dsimp [W]; ring

/-- The collision budget depends on the diameter, not the position of the
interval. This is needed for the translated square-root populations in §3. -/
theorem primeCollisionWeight_le_log_of_dist {P : Finset ℕ} {a b X : ℕ}
    (hab : a ≠ b) (hD : Nat.dist a b ≤ X) (hP : ∀ p ∈ P, p.Prime) :
    primeCollisionWeight P a b ≤ Real.log (X : ℝ) := by
  rcases lt_or_gt_of_ne hab with hab | hba
  · apply sum_log_congruent_primes_le_of_sub_le P hab _ hP
    rwa [Nat.dist_eq_sub_of_le hab.le] at hD
  · rw [primeCollisionWeight_symm]
    apply sum_log_congruent_primes_le_of_sub_le P hba _ hP
    rwa [Nat.dist_eq_sub_of_le_right hba.le] at hD

/-- Weighted larger-sieve pair bound for an arbitrary interval of diameter `X`. -/
theorem weighted_prime_collision_bound_of_diameter (P S : Finset ℕ) (μ : ℕ → ℝ)
    (X : ℕ) (m : ℝ) (hX : 1 ≤ X) (hP : ∀ p ∈ P, p.Prime)
    (hD : ∀ a ∈ S, ∀ b ∈ S, Nat.dist a b ≤ X) (hμ : ∀ a ∈ S, 0 ≤ μ a)
    (hmass : ∑ a ∈ S, μ a = 1) (hatom : ∀ a ∈ S, μ a ≤ m) :
    (∑ a ∈ S, ∑ b ∈ S, μ a * μ b * primeCollisionWeight P a b) ≤
      Real.log (X : ℝ) + m * ∑ p ∈ P, Real.log (p : ℝ) :=
  weighted_prime_collision_bound_of_budget P S μ (Real.log X) m
    (Real.log_nonneg (by exact_mod_cast hX)) hP hμ hmass hatom
    (fun a ha b hb hab => primeCollisionWeight_le_log_of_dist hab (hD a ha b hb) hP)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_Projection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Residue projection of finite probability measures

These identities connect the pair count in `WeightedCollision` with the
collision norm of a projected measure, as used in Lemma 2.5 of the paper.
-/

namespace Ostmann

open scoped BigOperators

theorem sum_fiberMass_mul {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : Finset β) (μ : α → ℝ) (f : α → β) (F : β → ℝ)
    (hf : ∀ a ∈ s, f a ∈ t) :
    ∑ y ∈ t, fiberMass s μ f y * F y = ∑ a ∈ s, μ a * F (f a) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to hf (fun a => μ a * F (f a))]
  apply Finset.sum_congr rfl
  intro y _
  unfold fiberMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [(Finset.mem_filter.mp ha).2]

theorem sum_fiberMass {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : Finset β) (μ : α → ℝ) (f : α → β)
    (hf : ∀ a ∈ s, f a ∈ t) :
    ∑ y ∈ t, fiberMass s μ f y = ∑ a ∈ s, μ a := by
  simpa only [mul_one] using sum_fiberMass_mul s t μ f (fun _ => 1) hf

theorem sum_fiberMass_sq {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : Finset β) (μ : α → ℝ) (f : α → β)
    (hf : ∀ a ∈ s, f a ∈ t) :
    ∑ y ∈ t, (fiberMass s μ f y) ^ 2 =
      ∑ a ∈ s, ∑ b ∈ s, if f a = f b then μ a * μ b else 0 := by
  classical
  simp only [pow_two]
  rw [sum_fiberMass_mul s t μ f (fiberMass s μ f) hf]
  apply Finset.sum_congr rfl
  intro a _
  simp only [fiberMass, Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
  apply Finset.sum_congr rfl
  intro b _
  simp only [eq_comm]

theorem residueMass_total (s : Finset ℕ) (μ : ℕ → ℝ) {p : ℕ}
    (hp : 0 < p) :
    ∑ r ∈ Finset.range p, residueMass s μ p r = ∑ a ∈ s, μ a :=
  sum_fiberMass s (Finset.range p) μ (fun a => a % p)
    (fun a _ => Finset.mem_range.mpr (Nat.mod_lt a hp))

theorem residueMass_sq (s : Finset ℕ) (μ : ℕ → ℝ) {p : ℕ}
    (hp : 0 < p) :
    ∑ r ∈ Finset.range p, (residueMass s μ p r) ^ 2 =
      ∑ a ∈ s, ∑ b ∈ s, if a ≡ b [MOD p] then μ a * μ b else 0 :=
  sum_fiberMass_sq s (Finset.range p) μ (fun a => a % p)
    (fun a _ => Finset.mem_range.mpr (Nat.mod_lt a hp))

/-- Reorder the weighted residue collisions as a sum over integer pairs. -/
theorem weighted_residueMass_sq (P s : Finset ℕ) (μ : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ P, Real.log (p : ℝ) *
      ∑ r ∈ Finset.range p, (residueMass s μ p r) ^ 2) =
    ∑ a ∈ s, ∑ b ∈ s, μ a * μ b * primeCollisionWeight P a b := by
  classical
  calc
    _ = ∑ p ∈ P, ∑ a ∈ s, ∑ b ∈ s,
        Real.log (p : ℝ) * (if a ≡ b [MOD p] then μ a * μ b else 0) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [residueMass_sq s μ (hP p hp).pos]
      simp only [Finset.mul_sum]
    _ = ∑ a ∈ s, ∑ b ∈ s, ∑ p ∈ P,
        Real.log (p : ℝ) * (if a ≡ b [MOD p] then μ a * μ b else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      simp only [primeCollisionWeight, Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> ring

/-- The projected bound for a translated interval uses only its diameter. -/
theorem residue_collision_bound_of_diameter (P s : Finset ℕ) (μ : ℕ → ℝ)
    (X : ℕ) (m : ℝ) (hX : 1 ≤ X) (hP : ∀ p ∈ P, p.Prime)
    (hD : ∀ a ∈ s, ∀ b ∈ s, Nat.dist a b ≤ X) (hμ : ∀ a ∈ s, 0 ≤ μ a)
    (hmass : ∑ a ∈ s, μ a = 1) (hatom : ∀ a ∈ s, μ a ≤ m) :
    (∑ p ∈ P, Real.log (p : ℝ) *
      ∑ r ∈ Finset.range p, (residueMass s μ p r) ^ 2) ≤
      Real.log (X : ℝ) + m * ∑ p ∈ P, Real.log (p : ℝ) := by
  rw [weighted_residueMass_sq P s μ hP]
  exact weighted_prime_collision_bound_of_diameter P s μ X m hX hP hD hμ hmass hatom

/-- Residue labels may be changed (in particular, negated) without changing
the collision norm, provided they identify exactly the congruent pairs. -/
theorem fiberMass_sq_eq_residueMass_sq (s t : Finset ℕ) (μ : ℕ → ℝ)
    (f : ℕ → ℕ) {p : ℕ} (hp : 0 < p)
    (hf : ∀ a ∈ s, f a ∈ t)
    (hcongr : ∀ a ∈ s, ∀ b ∈ s, f a = f b ↔ a ≡ b [MOD p]) :
    (∑ r ∈ t, (fiberMass s μ f r) ^ 2) =
      ∑ r ∈ Finset.range p, (residueMass s μ p r) ^ 2 := by
  rw [sum_fiberMass_sq s t μ f hf, residueMass_sq s μ hp]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  simp only [hcongr a ha b hb]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrimeSumInputs
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open scoped BigOperators

theorem prime_log_weight_le (Q : ℕ) :
    (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ)) ≤ Real.log 4 * Q := by
  rw [← Chebyshev.theta_eq_sum_primesLE_log]
  exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg Q)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FallingFactorialError
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The elementary collision loss for sampling distinct indices -/

namespace Ostmann

/-- A convenient collision bound with no restriction that k be smaller than J. -/
theorem pow_le_descFactorial_add (J : ℕ) (hJ : 1 ≤ J) (k : ℕ) :
    J ^ k ≤ J.descFactorial k + k ^ 2 * J ^ (k - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases hk : k = 0
    · subst k
      simp
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    by_cases hkJ : k ≤ J
    · have hmul := Nat.mul_le_mul_left J ih
      have hprev : J * J ^ (k - 1) = J ^ k := by
        rw [← pow_succ', Nat.sub_add_cancel hk1]
      have hdesc : J * J.descFactorial k =
          J.descFactorial (k + 1) + k * J.descFactorial k := by
        rw [Nat.descFactorial_succ, ← Nat.add_mul, Nat.sub_add_cancel hkJ]
      have hsmall := Nat.mul_le_mul_left k (Nat.descFactorial_le_pow J k)
      have herr : J * (k ^ 2 * J ^ (k - 1)) = k ^ 2 * J ^ k := by
        calc
          _ = k ^ 2 * (J * J ^ (k - 1)) := by ring
          _ = _ := by rw [hprev]
      rw [Nat.mul_add, hdesc, herr, ← pow_succ' J k] at hmul
      have hpoly : k ^ 2 + k ≤ (k + 1) ^ 2 := by nlinarith
      have hfinal := Nat.mul_le_mul_right (J ^ k) hpoly
      simp only [Nat.add_sub_cancel]
      nlinarith
    · have hJK : J ≤ (k + 1) ^ 2 := by
        have : J ≤ k := by omega
        nlinarith
      have h := Nat.mul_le_mul_right (J ^ k) hJK
      rw [pow_succ' J k]
      simpa only [Nat.add_sub_cancel] using h.trans (Nat.le_add_left _ _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_PrimeJacobiCharacter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prime-level Jacobi character is primitive -/

namespace Ostmann

theorem jacobiCharacterInt_prime (p : ℕ) [Fact p.Prime] :
    jacobiCharacterInt p = quadraticChar (ZMod p) := by
  apply MulChar.ext
  intro a
  have hcast : ((((a : ZMod p).val : ℤ) : ZMod p)) = (a : ZMod p) := by
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  calc
    jacobiCharacterInt p a = jacobiCharacterInt p ((((a : ZMod p).val : ℤ) : ZMod p)) :=
      congrArg (jacobiCharacterInt p) hcast.symm
    _ = jacobiSym ((a : ZMod p).val : ℤ) p := jacobiCharacterInt_intCast p _
    _ = legendreSym p ((a : ZMod p).val : ℤ) := (jacobiSym.legendreSym.to_jacobiSym p _).symm
    _ = quadraticChar (ZMod p) a := by rw [legendreSym, hcast]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_SquarefreeJacobiCharacter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The conductor of the Jacobi character at odd squarefree level -/

namespace Ostmann

private theorem jacobi_crt_negative (p M : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hM : 0 < M) (hcop : p.Coprime M) :
    ∃ n : ℕ, n.Coprime (p * M) ∧ n ≡ 1 [MOD M] ∧ jacobiSym (n : ℤ) (p * M) = -1 := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero M := ⟨hM.ne'⟩
  have hc : ringChar (ZMod p) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hp2
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' hc
  let n := Nat.chineseRemainder hcop (a : ZMod p).val 1
  have hnp : (n : ℕ) ≡ (a : ZMod p).val [MOD p] := n.property.1
  have hnM : (n : ℕ) ≡ 1 [MOD M] := n.property.2
  have hpa : ((n : ℕ) : ZMod p) = (a : ZMod p) := by
    have h := (ZMod.natCast_eq_natCast_iff (n : ℕ) (a : ZMod p).val p).mpr hnp
    simpa only [ZMod.natCast_zmod_val] using h
  have hMa : ((n : ℕ) : ZMod M) = 1 := by
    simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff (n : ℕ) 1 M).mpr hnM
  have hcp : (n : ℕ).Coprime p := by
    apply (ZMod.isUnit_iff_coprime (n : ℕ) p).mp
    rw [hpa]
    exact a.isUnit
  have hcM : (n : ℕ).Coprime M := by
    apply (ZMod.isUnit_iff_coprime (n : ℕ) M).mp
    rw [hMa]
    exact isUnit_one
  have hJp : jacobiSym (n : ℤ) p = -1 := by
    rw [← jacobiCharacterInt_intCast p, Int.cast_natCast, jacobiCharacterInt_prime, hpa, ha]
  have hJM : jacobiSym (n : ℤ) M = 1 := by
    have h := jacobiSym.mod_left' ((ZMod.intCast_eq_intCast_iff' (n : ℤ) 1 M).mp
      (by simpa only [Int.cast_natCast, Int.cast_one] using hMa))
    simpa only [jacobiSym.one_left] using h
  exact ⟨n, hcp.mul_right hcM, hnM, by rw [jacobiSym.mul_right, hJp, hJM, mul_one]⟩

/-- An odd prime factor missing from the conductor is contradicted by a
CRT unit whose Jacobi value is -1 and whose conductor residue is 1. -/
theorem jacobiCharacter_squarefree_primitive (N : ℕ) [NeZero N]
    (hN : Squarefree N) (hodd : Odd N) : (jacobiCharacter N).IsPrimitive := by
  let χ := jacobiCharacter N
  have hcN := χ.conductor_dvd_level
  have hcp (p : ℕ) (hp : p.Prime) (hpN : p ∣ N) : p ∣ χ.conductor := by
    by_contra hpc
    have hp2 : p ≠ 2 := by
      intro heq
      subst p
      exact hodd.not_two_dvd_nat hpN
    have hprod : p * (N / p) = N := Nat.mul_div_cancel' hpN
    have hM : 0 < N / p := by
      have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
      nlinarith
    have hcop : p.Coprime (N / p) := Nat.coprime_of_squarefree_mul (hprod.symm ▸ hN)
    obtain ⟨n, hn, hnM, hJn⟩ := jacobi_crt_negative p (N / p) hp hp2 hM hcop
    have hnc : n.Coprime N := hprod ▸ hn
    have hcd : χ.conductor ∣ N / p := by
      apply ((hp.coprime_iff_not_dvd.mpr hpc).symm).dvd_of_dvd_mul_left
      rwa [hprod]
    have hncon : (n : ZMod χ.conductor) = 1 := by
      have h := (ZMod.natCast_eq_natCast_iff n 1 χ.conductor).mpr (hnM.of_dvd hcd)
      simpa only [Nat.cast_one] using h
    have he := χ.primitiveCharacter_apply_of_isCoprime (Nat.isCoprime_iff_coprime.mpr hnc)
    have hv : χ.primitiveCharacter (n : ℤ) = 1 := by
      rw [Int.cast_natCast, hncon, map_one]
    have hv' : χ (n : ℤ) = -1 := by
      change jacobiCharacter N (n : ℤ) = -1
      rw [jacobiCharacter_intCast, ← hprod, hJn]
      norm_num
    rw [hv, hv'] at he
    norm_num at he
  have hNc : (∏ p ∈ N.primeFactors, p) ∣ χ.conductor := by
    apply (Nat.prod_primeFactors_dvd_iff χ.conductor_ne_zero).mpr
    intro p hp
    have hp' := Nat.mem_primeFactors.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hp'.1, hcp p hp'.1 hp'.2.1, χ.conductor_ne_zero⟩
  have hNc' : N ∣ χ.conductor := by
    simpa only [Nat.prod_primeFactors_of_squarefree hN] using hNc
  exact Nat.dvd_antisymm hcN hNc'

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticReciprocityCharacter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reciprocity formulas for the sign and two-part of a kernel -/

namespace Ostmann

theorem jacobi_odd_numerator_formula (N a : ℕ) (hN : Odd N) (ha : Odd a) :
    jacobiSym (N : ℤ) a = jacobiSym (a : ℤ) N * (ZMod.χ₄ a) ^ (N / 2) := by
  have h := jacobiSym.quadratic_reciprocity' hN ha
  rw [qrSign.symm ha hN, qrSign.neg_one_pow hN ha] at h
  rw [ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp ha), ← pow_mul]
  rw [Nat.mul_comm (a / 2) (N / 2)]
  exact h.trans (mul_comm _ _)

theorem jacobi_negative_odd_formula (N a : ℕ) (hN : Odd N) (ha : Odd a) :
    jacobiSym (-(N : ℤ)) a = jacobiSym (a : ℤ) N * (ZMod.χ₄ a) ^ (N / 2 + 1) := by
  rw [jacobiSym.neg _ ha, jacobi_odd_numerator_formula N a hN ha, pow_succ]
  ring

theorem jacobi_twice_odd_formula (N a : ℕ) (hN : Odd N) (ha : Odd a) :
    jacobiSym (2 * (N : ℤ)) a =
      jacobiSym (a : ℤ) N * (ZMod.χ₄ a) ^ (N / 2) * ZMod.χ₈ a := by
  rw [jacobiSym.mul_left, jacobiSym.at_two ha, jacobi_odd_numerator_formula N a hN ha]
  ring

theorem jacobi_negative_twice_odd_formula (N a : ℕ) (hN : Odd N) (ha : Odd a) :
    jacobiSym (-(2 * (N : ℤ))) a =
      jacobiSym (a : ℤ) N * (ZMod.χ₄ a) ^ (N / 2 + 1) * ZMod.χ₈ a := by
  rw [jacobiSym.neg _ ha, jacobi_twice_odd_formula N a hN ha, pow_succ]
  ring

theorem signedOddKernelCharacter_value (N : ℕ) [NeZero N] (negative : Bool)
    (hN : Odd N) (a : ℕ) (ha : a.Coprime (Nat.lcm N 4)) (haodd : Odd a) :
    signedOddKernelCharacter N negative (a : ZMod (Nat.lcm N 4)) =
      (jacobiSym (if negative then -(N : ℤ) else (N : ℤ)) a : ℝ) := by
  have hcop : IsCoprime (a : ℤ) (Nat.lcm N 4) := Nat.isCoprime_iff_coprime.mpr ha
  have hunit : IsUnit (a : ZMod 4) := (ZMod.isUnit_iff_coprime a 4).mpr
    (ha.of_dvd_right (Nat.dvd_lcm_right N 4))
  rw [← Int.cast_natCast (R := ZMod (Nat.lcm N 4))]
  rw [signedOddKernelCharacter, DirichletCharacter.mul, MulChar.mul_apply,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hcop,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hcop,
    jacobiCharacter_intCast]
  have hpow (k : ℕ) : (realFourCharacter ^ k) ((a : ℤ) : ZMod 4) = (ZMod.χ₄ a : ℝ) ^ k := by
    rw [Int.cast_natCast, ← hunit.unit_spec, MulChar.pow_apply_coe]
    rfl
  rw [hpow]
  cases negative
  · simp only [Bool.false_eq_true, ite_false, if_false, add_zero]
    exact_mod_cast (jacobi_odd_numerator_formula N a hN haodd).symm
  · simp only [ite_true, if_true]
    exact_mod_cast (jacobi_negative_odd_formula N a hN haodd).symm

theorem evenKernelTwist_value (k a : ℕ) (ha : a.Coprime 8) :
    evenKernelTwist k (a : ZMod 8) = (ZMod.χ₄ a : ℝ) ^ k * (ZMod.χ₈ a : ℝ) := by
  have hcop : IsCoprime (a : ℤ) 8 := Nat.isCoprime_iff_coprime.mpr ha
  have hunit : IsUnit (a : ZMod 4) := (ZMod.isUnit_iff_coprime a 4).mpr
    (ha.of_dvd_right (by decide : 4 ∣ 8))
  rw [evenKernelTwist, MulChar.mul_apply, ← Int.cast_natCast (R := ZMod 8),
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hcop, Int.cast_natCast,
    ← hunit.unit_spec, MulChar.pow_apply_coe, hunit.unit_spec]
  rfl

theorem signedEvenKernelCharacter_value (N : ℕ) [NeZero N] (negative : Bool)
    (hN : Odd N) (a : ℕ) (ha : a.Coprime (Nat.lcm N 8)) (haodd : Odd a) :
    signedEvenKernelCharacter N negative (a : ZMod (Nat.lcm N 8)) =
      (jacobiSym (if negative then -(2 * (N : ℤ)) else 2 * (N : ℤ)) a : ℝ) := by
  have hcop : IsCoprime (a : ℤ) (Nat.lcm N 8) := Nat.isCoprime_iff_coprime.mpr ha
  rw [← Int.cast_natCast (R := ZMod (Nat.lcm N 8)), signedEvenKernelCharacter,
    DirichletCharacter.mul, MulChar.mul_apply,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hcop,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hcop, jacobiCharacter_intCast,
    Int.cast_natCast, evenKernelTwist_value _ _ (ha.of_dvd_right (Nat.dvd_lcm_right N 8))]
  rw [← mul_assoc]
  cases negative
  · simp only [Bool.false_eq_true, ite_false, if_false, add_zero]
    exact_mod_cast (jacobi_twice_odd_formula N a hN haodd).symm
  · simp only [ite_true, if_true]
    exact_mod_cast (jacobi_negative_twice_odd_formula N a hN haodd).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticKernelConductor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conductor bounds for the signed kernel characters -/

namespace Ostmann

/-- A twist whose conductor is coprime to that of a character cannot remove
any of the latter's conductor. -/
theorem conductor_dvd_conductor_mul {n : ℕ} [NeZero n]
    (χ ψ : DirichletCharacter ℝ n) (hcop : χ.conductor.Coprime ψ.conductor) :
    χ.conductor ∣ (χ * ψ).conductor := by
  have h := DirichletCharacter.conductor_mul_dvd_lcm_conductor (χ * ψ) ψ⁻¹
  rw [mul_inv_cancel_right, DirichletCharacter.conductor_inv] at h
  exact hcop.dvd_of_dvd_mul_right (h.trans (Nat.lcm_dvd_mul _ _))

/-- Only the two-part can change when the odd squarefree Jacobi character is
multiplied by a character of level coprime to that odd part. -/
theorem odd_part_dvd_twisted_conductor (N t : ℕ) [NeZero N] [NeZero t]
    (hN : Squarefree N) (hodd : Odd N) (hcop : N.Coprime t)
    (ψ : DirichletCharacter ℝ t) :
    N ∣ (DirichletCharacter.mul (jacobiCharacter N) ψ).conductor := by
  let : NeZero (Nat.lcm N t) := ⟨Nat.lcm_ne_zero (NeZero.ne N) (NeZero.ne t)⟩
  let χ' := (jacobiCharacter N).changeLevel (Nat.dvd_lcm_left N t)
  let ψ' := ψ.changeLevel (Nat.dvd_lcm_right N t)
  have hχ : χ'.conductor = N := by
    rw [DirichletCharacter.conductor_changeLevel]
    exact jacobiCharacter_squarefree_primitive N hN hodd
  have hψ : ψ'.conductor ∣ t := by
    rw [DirichletCharacter.conductor_changeLevel]
    exact ψ.conductor_dvd_level
  have hc : χ'.conductor.Coprime ψ'.conductor := by
    rw [hχ]
    exact hcop.of_dvd_right hψ
  change N ∣ (χ' * ψ').conductor
  simpa only [hχ] using conductor_dvd_conductor_mul χ' ψ' hc

theorem signedOddKernelCharacter_conductor_bounds (N : ℕ) [NeZero N]
    (negative : Bool) (hN : Squarefree N) (hodd : Odd N) :
    N ∣ (signedOddKernelCharacter N negative).conductor ∧
    (signedOddKernelCharacter N negative).conductor ≤ 4 * N := by
  let : NeZero (Nat.lcm N 4) := ⟨Nat.lcm_ne_zero (NeZero.ne N) (by decide)⟩
  refine ⟨odd_part_dvd_twisted_conductor N 4 hN hodd ?_ _, ?_⟩
  · simpa using hodd.coprime_two_right.pow_right 2
  · exact (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne (Nat.lcm N 4)))
      (signedOddKernelCharacter N negative).conductor_dvd_level).trans
      ((Nat.lcm_le_mul (Nat.pos_of_ne_zero (NeZero.ne N)) (by decide : 0 < 4)).trans_eq (Nat.mul_comm N 4))

theorem signedEvenKernelCharacter_conductor_bounds (N : ℕ) [NeZero N]
    (negative : Bool) (hN : Squarefree N) (hodd : Odd N) :
    N ∣ (signedEvenKernelCharacter N negative).conductor ∧
    (signedEvenKernelCharacter N negative).conductor ≤ 8 * N := by
  let : NeZero (Nat.lcm N 8) := ⟨Nat.lcm_ne_zero (NeZero.ne N) (by decide)⟩
  refine ⟨odd_part_dvd_twisted_conductor N 8 hN hodd ?_ _, ?_⟩
  · simpa using hodd.coprime_two_right.pow_right 3
  · exact (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne (Nat.lcm N 8)))
      (signedEvenKernelCharacter N negative).conductor_dvd_level).trans
      ((Nat.lcm_le_mul (Nat.pos_of_ne_zero (NeZero.ne N)) (by decide : 0 < 8)).trans_eq (Nat.mul_comm N 8))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrimePowerRemainder
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform control of the prime-power remainder in the Euler identity -/

namespace Ostmann

open scoped BigOperators
open Complex LSeries

theorem primePowerRemainder_summable_one : LSeriesSummable primePowerRemainder (1 : ℂ) := by
  have h := ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div (0 : ZMod 1)
  rw [residue_one_eq_vonMangoldt] at h
  apply summable_norm_iff.mp
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  rw [LSeries.norm_term_eq]
  by_cases hn : n = 0
  · subst n
    simp
  · simp only [hn, ite_false, if_false, Complex.one_re, Real.rpow_one]
    by_cases hp : n.Prime
    · simp [primePowerRemainder, hp]
    · simp [primePowerRemainder, hp, Real.norm_eq_abs,
        abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))]

theorem primePowerRemainder_twist_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q)
    (s : ℝ) (hs : 1 ≤ s) (n : ℕ) :
    ‖LSeries.term (fun n => χ n * primePowerRemainder n) (s : ℂ) n‖ ≤
      ‖LSeries.term primePowerRemainder (1 : ℂ) n‖ := by
  apply (LSeries.norm_term_le (s : ℂ) ?_).trans
    (LSeries.norm_term_le_of_re_le_re primePowerRemainder (by exact hs) n)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)

/-- A single absolute constant bounds all higher-prime-power contributions,
uniformly in the modulus, character and real s >= 1. -/
theorem exists_primePowerRemainder_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (s : ℝ), 1 ≤ s →
      LSeriesSummable (fun n => χ n * primePowerRemainder n) (s : ℂ) ∧
        ‖LSeries (fun n => χ n * primePowerRemainder n) (s : ℂ)‖ ≤ C := by
  let C := ∑' n, ‖LSeries.term primePowerRemainder (1 : ℂ) n‖
  have hsum := primePowerRemainder_summable_one.norm
  refine ⟨C, tsum_nonneg (fun _ => norm_nonneg _), ?_⟩
  intro q χ s hs
  have hn := primePowerRemainder_twist_norm_le χ s hs
  have hsumn : Summable (fun n => ‖LSeries.term
      (fun n => χ n * primePowerRemainder n) (s : ℂ) n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hn hsum
  have ht : LSeriesSummable (fun n => χ n * primePowerRemainder n) (s : ℂ) :=
    summable_norm_iff.mp hsumn
  refine ⟨ht, ?_⟩
  exact (norm_tsum_le_tsum_norm hsumn).trans (hsumn.tsum_le_tsum hn hsum)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrimeLogDerivative
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prime logarithmic series and the actual L-function derivative -/

namespace Ostmann

open scoped BigOperators
open Complex LSeries

theorem twisted_vonMangoldt_decomposition {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) =
      primeLogCoefficients χ + (fun n : ℕ => χ n * primePowerRemainder n) := by
  funext n
  by_cases hp : n.Prime
  · simp [primeLogCoefficients, primePowerRemainder, hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
  · simp [primeLogCoefficients, primePowerRemainder, hp]

/-- Removing prime powers from the proved Euler identity costs only an
absolute bounded error, uniformly in the character and s > 1. -/
theorem exists_primeLogDerivative_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℝ), 1 < s →
      LSeriesSummable (primeLogCoefficients χ) (s : ℂ) ∧
      ‖LSeries (primeLogCoefficients χ) (s : ℂ) +
        deriv (DirichletCharacter.LFunction χ) (s : ℂ) /
          DirichletCharacter.LFunction χ (s : ℂ)‖ ≤ C := by
  obtain ⟨C, hC, hrem⟩ := exists_primePowerRemainder_bound
  refine ⟨C, hC, ?_⟩
  intro q hq χ s hs
  obtain ⟨hremSum, hremBound⟩ := hrem q χ s hs.le
  have ht := χ.LSeriesSummable_twist_vonMangoldt (show 1 < (s : ℂ).re from hs)
  have hdiff : (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) -
      (fun n : ℕ => χ n * primePowerRemainder n) = primeLogCoefficients χ := by
    rw [twisted_vonMangoldt_decomposition]
    exact add_sub_cancel_right _ _
  have hp : LSeriesSummable (primeLogCoefficients χ) (s : ℂ) := by
    rw [← hdiff]
    exact ht.sub hremSum
  have he := χ.LSeries_twist_vonMangoldt_eq (show 1 < (s : ℂ).re from hs)
  rw [← χ.deriv_LFunction_eq_deriv_LSeries hs, ← χ.LFunction_eq_LSeries hs] at he
  change LSeries (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ) = _ at he
  rw [twisted_vonMangoldt_decomposition, LSeries_add hp hremSum] at he
  have hid : LSeries (primeLogCoefficients χ) (s : ℂ) +
      deriv (DirichletCharacter.LFunction χ) (s : ℂ) /
        DirichletCharacter.LFunction χ (s : ℂ) =
      -LSeries (fun n : ℕ => χ n * primePowerRemainder n) (s : ℂ) := by
    linear_combination he
  refine ⟨hp, ?_⟩
  rw [hid, norm_neg]
  exact hremBound

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RealPrimeSeries
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The real prime series for a real Dirichlet character -/

namespace Ostmann

open scoped BigOperators
open Complex LSeries

theorem primeLogTerm_ofReal {q : ℕ} (χ : DirichletCharacter ℝ q) (s : ℝ) (n : ℕ) :
    LSeries.term (primeLogCoefficients (χ.ringHomComp Complex.ofRealHom)) (s : ℂ) n =
      (realPrimeTerm χ s n : ℂ) := by
  by_cases hn : n = 0
  · subst n
    simp [realPrimeTerm]
  · rw [LSeries.term_of_ne_zero hn]
    by_cases hp : n.Prime
    · simp only [primeLogCoefficients, hp, ite_true, if_true, realPrimeTerm,
        MulChar.ringHomComp_apply,
        Complex.ofReal_div, Complex.ofReal_mul]
      change (χ n : ℂ) * (Real.log n : ℂ) / (n : ℂ) ^ (s : ℂ) = _
      rw [← Complex.ofReal_natCast n, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
    · simp [primeLogCoefficients, realPrimeTerm, hp]

/-- The uniform prime-power error is retained for the actual real weighted
prime sum. This result requires no analytic input beyond proved Mathlib. -/
theorem exists_realPrimeSeries_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℝ q) (s : ℝ), 1 < s →
      Summable (realPrimeTerm χ s) ∧
      |(∑' n, realPrimeTerm χ s n) +
        (deriv (DirichletCharacter.LFunction (χ.ringHomComp Complex.ofRealHom)) (s : ℂ) /
          DirichletCharacter.LFunction (χ.ringHomComp Complex.ofRealHom) (s : ℂ)).re| ≤ C := by
  obtain ⟨C, hC, herror⟩ := exists_primeLogDerivative_error
  refine ⟨C, hC, ?_⟩
  intro q hq χ s hs
  obtain ⟨hseries, hbound⟩ := herror q (χ.ringHomComp Complex.ofRealHom) s hs
  have hcast : Summable (fun n => (realPrimeTerm χ s n : ℂ)) :=
    hseries.congr (primeLogTerm_ofReal χ s)
  have hsum : LSeries (primeLogCoefficients (χ.ringHomComp Complex.ofRealHom)) (s : ℂ) =
      (((∑' n, realPrimeTerm χ s n) : ℝ) : ℂ) := by
    calc
      _ = ∑' n, (realPrimeTerm χ s n : ℂ) := tsum_congr (primeLogTerm_ofReal χ s)
      _ = _ := (Complex.ofReal_tsum _).symm
  refine ⟨Complex.summable_ofReal.mp hcast, ?_⟩
  rw [hsum] at hbound
  have hb := (Complex.abs_re_le_norm _).trans hbound
  simpa only [Complex.add_re, Complex.ofReal_re] using hb

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RealZeroKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Comparing the real parts of zero contributions at two real points -/

namespace Ostmann

/-- The universal ratio bound used for zeros near the real axis. -/
theorem realZeroKernel_ratio {a b y : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    realZeroKernel a y ≤ (b / a) * realZeroKernel b y := by
  have hb : 0 < b := ha.trans_le hab
  have hda : 0 < a ^ 2 + y ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg y)
  have hdb : 0 < b ^ 2 + y ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hb) (sq_nonneg y)
  have hs : 0 ≤ (b ^ 2 - a ^ 2) * y ^ 2 := by
    apply mul_nonneg _ (sq_nonneg y)
    nlinarith
  unfold realZeroKernel
  rw [← mul_div_assoc, div_le_div_iff₀ hda hdb]
  apply (mul_le_mul_iff_left₀ ha).mp
  field_simp
  nlinarith

/-- At imaginary height at least one, bounded real parts give an absolute
constant independent of the zero-free region. -/
theorem realZeroKernel_high {a b y : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 2) (hy : 1 ≤ y ^ 2) :
    realZeroKernel a y ≤ 5 * realZeroKernel b y := by
  have hb0 : 0 < b := ha.trans_le hab
  have hda : 0 < a ^ 2 + y ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg y)
  have hdb : 0 < b ^ 2 + y ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hb0) (sq_nonneg y)
  have hd : b ^ 2 + y ^ 2 ≤ 5 * (a ^ 2 + y ^ 2) := by nlinarith [sq_nonneg a]
  have h1 := mul_le_mul_of_nonneg_right hab hdb.le
  have h2 := mul_le_mul_of_nonneg_left hd hb0.le
  unfold realZeroKernel
  rw [← mul_div_assoc, div_le_div_iff₀ hda hdb]
  nlinarith

theorem realZeroKernel_gap {a b y c δ : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hc : 0 < c) (hgap : b - a ≤ δ) (hregion : c * δ ≤ a) :
    realZeroKernel a y ≤ (1 + c⁻¹) * realZeroKernel b y := by
  have hδ : δ / a ≤ 1 / c := by
    apply (div_le_div_iff₀ ha hc).mpr
    nlinarith
  have hratio : b / a ≤ 1 + c⁻¹ := by
    have hg := div_le_div_of_nonneg_right (show b ≤ a + δ by linarith) ha.le
    rw [add_div, div_self ha.ne'] at hg
    exact hg.trans (by simpa only [one_div] using add_le_add (show (1 : ℝ) ≤ 1 from le_rfl) hδ)
  exact (realZeroKernel_ratio ha hab).trans
    (mul_le_mul_of_nonneg_right hratio (realZeroKernel_nonneg (ha.le.trans hab)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RealZeroSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the zero-free comparison with a finite exceptional set -/

namespace Ostmann

open scoped BigOperators Classical

theorem realZeroKernel_zero_free (ρ : ℂ) (s s₀ c δ C : ℝ)
    (hρ : 0 ≤ ρ.re ∧ ρ.re < 1) (hs : 1 < s) (hss : s ≤ s₀) (hs₀ : s₀ ≤ 2)
    (hc : 0 < c) (hC5 : 5 ≤ C) (hCc : 1 + c⁻¹ ≤ C)
    (hgap : s₀ - s ≤ δ) (hregion : ρ.im ^ 2 < 1 → c * δ ≤ s - ρ.re) :
    realZeroKernel (s - ρ.re) ρ.im ≤ C * realZeroKernel (s₀ - ρ.re) ρ.im := by
  have ha : 0 < s - ρ.re := by linarith [hρ.2]
  have hab : s - ρ.re ≤ s₀ - ρ.re := by linarith
  have hb : s₀ - ρ.re ≤ 2 := by linarith [hρ.1]
  have hn : 0 ≤ realZeroKernel (s₀ - ρ.re) ρ.im := realZeroKernel_nonneg (by linarith)
  by_cases hy : 1 ≤ ρ.im ^ 2
  · exact (realZeroKernel_high ha hab hb hy).trans (mul_le_mul_of_nonneg_right hC5 hn)
  · exact (realZeroKernel_gap ha hab hc (by linarith) (hregion (lt_of_not_ge hy))).trans
      (mul_le_mul_of_nonneg_right hCc hn)

/-- An arbitrary zero family may retain finitely many exceptions. The
comparison proves summability at s as well as the bound; summability at s
is not assumed. Multiplicities are represented by repeated indices. -/
theorem realZeroKernel_sum_bound {ι : Type*} (ρ : ι → ℂ) (E : Finset ι)
    (s s₀ c δ C : ℝ) (hρ : ∀ i, 0 ≤ (ρ i).re ∧ (ρ i).re < 1)
    (hs : 1 < s) (hss : s ≤ s₀) (hs₀ : s₀ ≤ 2) (hc : 0 < c)
    (hC5 : 5 ≤ C) (hCc : 1 + c⁻¹ ≤ C) (hgap : s₀ - s ≤ δ)
    (hregion : ∀ i ∉ E, (ρ i).im ^ 2 < 1 → c * δ ≤ s - (ρ i).re)
    (hsum : Summable (fun i => realZeroKernel (s₀ - (ρ i).re) (ρ i).im)) :
    Summable (fun i => realZeroKernel (s - (ρ i).re) (ρ i).im) ∧
      (∑' i, realZeroKernel (s - (ρ i).re) (ρ i).im) ≤
        C * (∑' i, realZeroKernel (s₀ - (ρ i).re) (ρ i).im) +
          ∑ i ∈ E, (s - (ρ i).re)⁻¹ := by
  let e : ι → ℝ := fun i => if i ∈ E then (s - (ρ i).re)⁻¹ else 0
  have he : Summable e := summable_of_ne_finset_zero (s := E) (by
    intro i hi
    simp only [e, ite_eq_right hi])
  have hE : ∑' i, e i = ∑ i ∈ E, (s - (ρ i).re)⁻¹ := by
    rw [tsum_eq_sum (s := E) (by intro i hi; simp only [e, ite_eq_right hi])]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [e, ite_eq_left hi]
  have hmaj := (hsum.mul_left C).add he
  have hp (i : ι) : realZeroKernel (s - (ρ i).re) (ρ i).im ≤
      C * realZeroKernel (s₀ - (ρ i).re) (ρ i).im + e i := by
    have ha : 0 < s - (ρ i).re := by linarith [(hρ i).2]
    have hn : 0 ≤ C * realZeroKernel (s₀ - (ρ i).re) (ρ i).im := by
      apply mul_nonneg (by linarith)
      apply realZeroKernel_nonneg
      linarith [(hρ i).2]
    by_cases hi : i ∈ E
    · have hb := realZeroKernel_le_inv (y := (ρ i).im) ha
      simp only [e, ite_eq_left hi]
      linarith
    · simpa only [e, ite_eq_right hi, add_zero] using
        realZeroKernel_zero_free (ρ i) s s₀ c δ C (hρ i) hs hss hs₀ hc hC5 hCc hgap (hregion i hi)
  have hsnew : Summable (fun i => realZeroKernel (s - (ρ i).re) (ρ i).im) :=
    Summable.of_nonneg_of_le (fun i => realZeroKernel_nonneg (by linarith [(hρ i).2])) hp hmaj
  refine ⟨hsnew, ?_⟩
  have hb := hsnew.tsum_le_tsum hp hmaj
  rwa [Summable.tsum_add (hsum.mul_left C) he, hsum.tsum_mul_left, hE] at hb

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_PrimitiveKernelCharacter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Primitive real characters representing the four signed kernel shapes -/

namespace Ostmann

theorem character_ne_one_of_conductor_dvd {n N : ℕ} [NeZero n]
    (χ : DirichletCharacter ℝ n) (hN : 1 < N) (hdiv : N ∣ χ.conductor) : χ ≠ 1 := by
  intro h
  rw [h, DirichletCharacter.conductor_one] at hdiv
  have := Nat.dvd_one.mp hdiv
  omega

theorem primitiveRealOfCharacter_value {n : ℕ} [NeZero n]
    (χ : DirichletCharacter ℝ n) (hχ : χ ≠ 1) (a : ℕ) (ha : a.Coprime n) :
    (primitiveRealOfCharacter χ hχ).character a = χ a := by
  change χ.primitiveCharacter (a : ZMod χ.conductor) = χ (a : ZMod n)
  rw [← Int.cast_natCast (R := ZMod χ.conductor),
    ← Int.cast_natCast (R := ZMod n)]
  exact χ.primitiveCharacter_apply_of_isCoprime (Nat.isCoprime_iff_coprime.mpr ha)

/-- An odd squarefree numerator, including either sign, has a primitive
representative whose conductor lies between N and 4N. -/
theorem exists_odd_kernel_primitive (N : ℕ) (hN : 1 < N) (hsf : Squarefree N)
    (hodd : Odd N) (negative : Bool) :
    ∃ χ : PrimitiveRealCharacter, N ∣ χ.modulus ∧ χ.modulus ≤ 4 * N ∧
      ∀ a : ℕ, Odd a → a.Coprime N →
        χ.character a = (jacobiSym (if negative then -(N : ℤ) else N) a : ℝ) := by
  let : NeZero N := ⟨by omega⟩
  let : NeZero (Nat.lcm N 4) := ⟨Nat.lcm_ne_zero (NeZero.ne N) (by decide)⟩
  let ψ := signedOddKernelCharacter N negative
  have hb := signedOddKernelCharacter_conductor_bounds N negative hsf hodd
  have hn : ψ ≠ 1 := character_ne_one_of_conductor_dvd ψ hN hb.1
  refine ⟨primitiveRealOfCharacter ψ hn, hb.1, hb.2, ?_⟩
  intro a ha haN
  have ha4 : a.Coprime 4 := by simpa using ha.coprime_two_right.pow_right 2
  have hac : a.Coprime (Nat.lcm N 4) :=
    (haN.mul_right ha4).of_dvd_right (Nat.lcm_dvd_mul N 4)
  rw [primitiveRealOfCharacter_value ψ hn a hac]
  exact signedOddKernelCharacter_value N negative hodd a hac ha

/-- The same construction for twice an odd squarefree numerator. -/
theorem exists_even_kernel_primitive (N : ℕ) (hN : 1 < N) (hsf : Squarefree N)
    (hodd : Odd N) (negative : Bool) :
    ∃ χ : PrimitiveRealCharacter, N ∣ χ.modulus ∧ χ.modulus ≤ 8 * N ∧
      ∀ a : ℕ, Odd a → a.Coprime N →
        χ.character a = (jacobiSym (if negative then -(2 * (N : ℤ)) else 2 * N) a : ℝ) := by
  let : NeZero N := ⟨by omega⟩
  let : NeZero (Nat.lcm N 8) := ⟨Nat.lcm_ne_zero (NeZero.ne N) (by decide)⟩
  let ψ := signedEvenKernelCharacter N negative
  have hb := signedEvenKernelCharacter_conductor_bounds N negative hsf hodd
  have hn : ψ ≠ 1 := character_ne_one_of_conductor_dvd ψ hN hb.1
  refine ⟨primitiveRealOfCharacter ψ hn, hb.1, hb.2, ?_⟩
  intro a ha haN
  have ha8 : a.Coprime 8 := by simpa using ha.coprime_two_right.pow_right 3
  have hac : a.Coprime (Nat.lcm N 8) :=
    (haN.mul_right ha8).of_dvd_right (Nat.lcm_dvd_mul N 8)
  rw [primitiveRealOfCharacter_value ψ hn a hac]
  exact signedEvenKernelCharacter_value N negative hodd a hac ha

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DistinctProductError
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A concrete error bound for deleting repeated indices -/

namespace Ostmann

open scoped BigOperators Classical

theorem distinct_product_error {A : Type*} [Fintype A] [DecidableEq A]
    (k : ℕ) (y : A → ℂ) (hy : ∀ a, ‖y a‖ ≤ 1) :
    ‖(∑ a, y a) ^ k - ∑ e : Fin k ↪ A, ∏ i, y (e i)‖ ≤
      ((Fintype.card A) ^ k - (Fintype.card A).descFactorial k : ℕ) := by
  let F : (Fin k → A) → ℂ := fun f => ∏ i, y (f i)
  have he : (∑ f : {f : Fin k → A // Function.Injective f}, F f) =
      ∑ e : Fin k ↪ A, ∏ i, y (e i) := by
    exact (Equiv.subtypeInjectiveEquivEmbedding (Fin k) A).sum_comp (fun e => ∏ i, y (e i))
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun f : Fin k → A => Function.Injective f) F
  rw [he] at hsplit
  have hdiff : (∑ a, y a) ^ k - ∑ e : Fin k ↪ A, ∏ i, y (e i) =
      ∑ f : {f : Fin k → A // ¬Function.Injective f}, F f := by
    rw [Fintype.sum_pow]
    change (∑ f, F f) - _ = _
    rw [← hsplit, add_sub_cancel_left]
  rw [hdiff]
  calc
    _ ≤ ∑ f : {f : Fin k → A // ¬Function.Injective f}, ‖F f‖ := norm_sum_le _ _
    _ ≤ ∑ _f : {f : Fin k → A // ¬Function.Injective f}, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro f _
      dsimp only [F]
      rw [Complex.norm_prod]
      exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => hy (f.1 i))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      congr 1
      rw [Fintype.card_subtype_compl]
      have hc := Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding (Fin k) A)
      rw [hc, Fintype.card_embedding_eq]
      simp

/-- For a nonempty finite population, the normalized deletion error is at
most k²/J. This suffices for kernels whose bias is bounded below. -/
theorem normalized_distinct_product_error {A : Type*} [Fintype A] [DecidableEq A]
    (k : ℕ) (hk : 1 ≤ k) (y : A → ℂ) (hy : ∀ a, ‖y a‖ ≤ 1)
    (hA : 0 < Fintype.card A) :
    ‖((∑ a, y a) / (Fintype.card A : ℂ)) ^ k -
      (∑ e : Fin k ↪ A, ∏ i, y (e i)) / (Fintype.card A : ℂ) ^ k‖ ≤
        (k : ℝ) ^ 2 / Fintype.card A := by
  let J := Fintype.card A
  have hJ : (0 : ℝ) < J := by exact_mod_cast hA
  have hpow : (0 : ℝ) < (J : ℝ) ^ k := pow_pos hJ k
  have hraw := distinct_product_error k y hy
  have hcount := pow_le_descFactorial_add J hA k
  have hcountR : ((J ^ k - J.descFactorial k : ℕ) : ℝ) ≤
      (k : ℝ) ^ 2 * (J : ℝ) ^ (k - 1) := by
    exact_mod_cast (show J ^ k - J.descFactorial k ≤ k ^ 2 * J ^ (k - 1) by omega)
  have hpoweq : (J : ℝ) ^ k = (J : ℝ) * (J : ℝ) ^ (k - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hk]
  rw [div_pow, ← sub_div, norm_div]
  have hnorm : ‖(Fintype.card A : ℂ) ^ k‖ = (J : ℝ) ^ k := by
    rw [norm_pow]
    simp [J]
  rw [hnorm]
  calc
    _ ≤ ((k : ℝ) ^ 2 * (J : ℝ) ^ (k - 1)) / (J : ℝ) ^ k :=
      div_le_div_of_nonneg_right (hraw.trans hcountR) hpow.le
    _ = _ := by
      rw [hpoweq]
      field_simp
      rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticAmplificationCoefficients
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The single finite coefficient array shared by all quadratic kernels -/

namespace Ostmann

open scoped BigOperators Classical

theorem primeSubsetCoefficient_norm_le (P : Finset ℕ) (k : ℕ) (c : ℂ) (e : ℕ → ℂ)
    (hP : ∀ p ∈ P, p.Prime) (he : ∀ p ∈ P, ‖e p‖ ≤ 1) (s : ℕ) :
    ‖primeSubsetCoefficient P k c e s‖ ≤ ‖c‖ := by
  unfold primeSubsetCoefficient
  split_ifs with hs
  · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hs
    have hQP := (Finset.mem_powersetCard.mp hQ).1
    rw [Nat.primeFactors_prod (fun p hp => hP p (hQP hp)), norm_mul]
    have hprod : ‖∏ p ∈ Q, e p‖ ≤ 1 := by
      rw [Complex.norm_prod]
      exact Finset.prod_le_one (fun p _ => norm_nonneg (e p)) (fun p hp => he p (hQP hp))
    simpa using mul_le_mul_of_nonneg_left hprod (norm_nonneg c)
  · simp

theorem primeSubsetCoefficient_energy_le (P : Finset ℕ) (k N : ℕ) (c : ℂ) (e : ℕ → ℂ)
    (hP : ∀ p ∈ P, p.Prime) (he : ∀ p ∈ P, ‖e p‖ ≤ 1) :
    quadraticSieveEnergy N (primeSubsetCoefficient P k c e) ≤
      (P.card.choose k : ℝ) * ‖c‖ ^ 2 := by
  let T := primeSubsetProducts P k
  let R := oddSquarefreeRange N
  let f := fun s => ‖primeSubsetCoefficient P k c e s‖ ^ 2
  have hrestrict : (∑ s ∈ R ∩ T, f s) = ∑ s ∈ R, f s := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro s hs hst
    have hn : s ∉ T := fun ht => hst (Finset.mem_inter.mpr ⟨hs, ht⟩)
    change s ∉ primeSubsetProducts P k at hn
    simp [f, primeSubsetCoefficient, hn]
  calc
    _ = ∑ s ∈ R ∩ T, f s := hrestrict.symm
    _ ≤ ∑ s ∈ T, f s :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun s _ _ => sq_nonneg _)
    _ ≤ (T.card : ℝ) * ‖c‖ ^ 2 := by
      simpa only [nsmul_eq_mul] using
        (Finset.sum_le_card_nsmul T f (‖c‖ ^ 2) (fun s _ =>
          pow_le_pow_left₀ (norm_nonneg _) (primeSubsetCoefficient_norm_le P k c e hP he s) 2))
    _ = _ := by rw [show T.card = P.card.choose k from primeSubsetProducts_card P k hP]

theorem amplification_numeric_budget (J k : ℕ) (hJ : 0 < J) :
    (J.choose k : ℝ) * ((k.factorial : ℝ) / (J : ℝ) ^ k) ^ 2 ≤
      (k.factorial : ℝ) / (J : ℝ) ^ k := by
  have hp : (0 : ℝ) < (J : ℝ) ^ k := pow_pos (by exact_mod_cast hJ) k
  have hF : (0 : ℝ) ≤ k.factorial := by positivity
  have hchoose : (k.factorial : ℝ) * (J.choose k : ℝ) ≤ (J : ℝ) ^ k := by
    exact_mod_cast (show k.factorial * J.choose k ≤ J ^ k by
      rw [← Nat.descFactorial_eq_factorial_mul_choose]
      exact Nat.descFactorial_le_pow J k)
  have hr : ((k.factorial : ℝ) * (J.choose k : ℝ)) / (J : ℝ) ^ k ≤ 1 :=
    (div_le_one hp).mpr hchoose
  calc
    _ = ((k.factorial : ℝ) / (J : ℝ) ^ k) *
      (((k.factorial : ℝ) * (J.choose k : ℝ)) / (J : ℝ) ^ k) := by ring
    _ ≤ ((k.factorial : ℝ) / (J : ℝ) ^ k) * 1 :=
      mul_le_mul_of_nonneg_left hr (div_nonneg hF hp.le)
    _ = _ := mul_one _

/-- This is the `k! / J^k` energy bound in the manuscript, for an actual
coefficient function supported on products of distinct primes. -/
theorem quadratic_amplification_energy (P : Finset ℕ) (k N : ℕ) (e : ℕ → ℂ)
    (hP : ∀ p ∈ P, p.Prime) (he : ∀ p ∈ P, ‖e p‖ ≤ 1) (hcard : 0 < P.card) :
    quadraticSieveEnergy N (primeSubsetCoefficient P k
      (((k.factorial : ℝ) / (P.card : ℝ) ^ k : ℝ) : ℂ) e) ≤
        (k.factorial : ℝ) / (P.card : ℝ) ^ k := by
  have hc : 0 ≤ (k.factorial : ℝ) / (P.card : ℝ) ^ k := by positivity
  have h := primeSubsetCoefficient_energy_le P k N
    (((k.factorial : ℝ) / (P.card : ℝ) ^ k : ℝ) : ℂ) e hP he
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc] at h
  exact h.trans (amplification_numeric_budget P.card k hcard)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSieveTranspose
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reciprocity supplies the transpose needed for quadratic kernels -/

namespace Ostmann

open scoped BigOperators Classical

theorem quadraticSieveEnergy_reciprocityTwist (N : ℕ) (b : ℕ → ℂ) :
    quadraticSieveEnergy N (reciprocityTwist b) = quadraticSieveEnergy N b := by
  apply Finset.sum_congr rfl
  intro s _
  unfold reciprocityTwist
  split_ifs <;> simp

theorem quadraticTransposeSum_one_mod_four (N : ℕ) (b : ℕ → ℂ) (u : ℕ)
    (hu : u % 4 = 1) : quadraticTransposeSum N b u = quadraticSieveSum N b u := by
  apply Finset.sum_congr rfl
  intro s hs
  have hsodd := (Finset.mem_filter.mp hs).2.1
  rw [jacobiSym.quadratic_reciprocity_one_mod_four hu hsodd]

theorem quadraticTransposeSum_three_mod_four (N : ℕ) (b : ℕ → ℂ) (u : ℕ)
    (hu : u % 4 = 3) :
    quadraticTransposeSum N b u = quadraticSieveSum N (reciprocityTwist b) u := by
  apply Finset.sum_congr rfl
  intro s hs
  have hsodd := (Finset.mem_filter.mp hs).2.1
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hsodd) with hs1 | hs3
  · rw [jacobiSym.quadratic_reciprocity_one_mod_four' (Nat.odd_iff.mpr (by omega)) hs1]
    simp [reciprocityTwist, hs1]
  · rw [jacobiSym.quadratic_reciprocity_three_mod_four hu hs3]
    simp [reciprocityTwist, hs3]

theorem quadratic_transpose_odd_bound (P : PublishedQuadraticLargeSieve)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℕ, 1 ≤ M → 1 ≤ N → ∀ b : ℕ → ℂ,
      (∑ u ∈ oddSquarefreeRange M, ‖quadraticTransposeSum N b u‖ ^ 2) ≤
        C * ((M : ℝ) * N) ^ ε * ((M : ℝ) + N) * quadraticSieveEnergy N b := by
  obtain ⟨C, hC, hb⟩ := P ε hε
  refine ⟨2 * C, by positivity, ?_⟩
  intro M N hM hN b
  have h1 := hb M N hM hN b
  have h3 := hb M N hM hN (reciprocityTwist b)
  rw [quadraticSieveEnergy_reciprocityTwist] at h3
  have ht : (∑ u ∈ oddSquarefreeRange M, ‖quadraticTransposeSum N b u‖ ^ 2) ≤
      (∑ u ∈ oddSquarefreeRange M, ‖quadraticSieveSum N b u‖ ^ 2) +
      ∑ u ∈ oddSquarefreeRange M, ‖quadraticSieveSum N (reciprocityTwist b) u‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro u hu
    have huodd := (Finset.mem_filter.mp hu).2.1
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp huodd) with hu1 | hu3
    · rw [quadraticTransposeSum_one_mod_four N b u hu1]
      linarith [sq_nonneg ‖quadraticSieveSum N (reciprocityTwist b) u‖]
    · rw [quadraticTransposeSum_three_mod_four N b u hu3]
      linarith [sq_nonneg ‖quadraticSieveSum N b u‖]
  apply ht.trans
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticAmplificationIdentity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying the shared coefficient test with the distinct-prime expansion -/

namespace Ostmann

open scoped BigOperators Classical

theorem jacobi_product_right (u : ℤ) (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p ≠ 0) :
    jacobiSym u (∏ p ∈ Q, p) = ∏ p ∈ Q, jacobiSym u p := by
  induction Q using Finset.induction_on with
  | empty => simp
  | @insert p Q hp ih =>
    have hpn := hQ p (Finset.mem_insert_self _ _)
    have hQn : ∀ q ∈ Q, q ≠ 0 := fun q hq => hQ q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hp, jacobiSym.mul_right' u hpn
      (Finset.prod_ne_zero_iff.mpr hQn), ih hQn, Finset.prod_insert hp]

theorem subset_product_sum_subtype (P : Finset ℕ) (k : ℕ) (y : ℕ → ℂ) :
    (∑ Q ∈ (Finset.univ : Finset P).powersetCard k, ∏ p ∈ Q, y p) =
      ∑ Q ∈ P.powersetCard k, ∏ p ∈ Q, y p := by
  let f : P ↪ ℕ := Function.Embedding.subtype _
  have hmap : (Finset.univ : Finset P).map f = P := by ext p; simp [f]
  have h := congrArg (fun R : Finset ℕ => ∑ Q ∈ R.powersetCard k, ∏ p ∈ Q, y p) hmap
  simp only [Finset.powersetCard_map, Finset.sum_map] at h
  change (∑ Q ∈ (Finset.univ : Finset P).powersetCard k, ∏ p ∈ Q.map f, y p) = _ at h
  simpa [f] using h

theorem quadratic_amplification_identity (P : Finset ℕ) (k Z : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, Odd p) (hZ : ∀ p ∈ P, p ≤ Z)
    (c : ℂ) (e : ℕ → ℂ) (u : ℤ) :
    quadraticTransposeSum (Z ^ k) (primeSubsetCoefficient P k c e) u =
      c * ∑ Q ∈ P.powersetCard k, ∏ p ∈ Q, e p * (jacobiSym u p : ℂ) := by
  let f : ℕ → ℂ := fun s => primeSubsetCoefficient P k c e s * (jacobiSym u s : ℂ)
  have hsub := primeSubsetProducts_mem_range P k Z hP hodd hZ
  have hs : (∑ s ∈ primeSubsetProducts P k, f s) =
      ∑ s ∈ oddSquarefreeRange (Z ^ k), f s := by
    apply Finset.sum_subset hsub
    intro s _ hs
    simp [f, primeSubsetCoefficient, hs]
  change (∑ s ∈ oddSquarefreeRange (Z ^ k), f s) = _
  rw [← hs]
  unfold primeSubsetProducts
  rw [Finset.sum_image, Finset.mul_sum]
  · apply Finset.sum_congr rfl
    intro Q hQ
    have hQP := (Finset.mem_powersetCard.mp hQ).1
    have hprime : ∀ p ∈ Q, p.Prime := fun p hp => hP p (hQP hp)
    have hmem : (∏ p ∈ Q, p) ∈ primeSubsetProducts P k :=
      Finset.mem_image.mpr ⟨Q, hQ, rfl⟩
    dsimp only [f]
    simp only [primeSubsetCoefficient, hmem, ite_true, if_true]
    rw [Nat.primeFactors_prod hprime,
      jacobi_product_right u Q (fun p hp => (hprime p hp).ne_zero), Int.cast_prod,
      Finset.prod_mul_distrib, mul_assoc]
  · intro Q hQ R hR heq
    exact primeSubset_product_injective P hP
      (Finset.mem_powersetCard.mp hQ).1 (Finset.mem_powersetCard.mp hR).1 heq

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PhysicalAmplification
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original physical-space amplified moment -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem orientedQuadraticValue_ternary (ε : ℕ → ℝ) (t : ℕ → ℤ) (n : ℤ) (p : ℕ)
    (hε : ε p = 1 ∨ ε p = -1) :
    orientedQuadraticValue ε t n p = 0 ∨ orientedQuadraticValue ε t n p = 1 ∨
      orientedQuadraticValue ε t n p = -1 := by
  rcases hε with h | h <;>
    rcases jacobiSym.trichotomy (n - t p) p with hχ | hχ | hχ <;>
    simp [orientedQuadraticValue, h, hχ]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PhysicalAmplificationBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original amplification dominates all fixed-bias and tail losses -/

namespace Ostmann

open Filter Asymptotics

theorem eventual_amplification_log_loss (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ k K : ℝ,
      0 ≤ k → k ≤ 2 * T ^ (3 / 5 : ℝ) →
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ K →
      C * (1 + k) + 6 * Real.log T ≤ ε * K := by
  let D := 3 * C + 6
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hl := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 3 / 5 by norm_num)).bound zero_lt_one
  have hp := (tendsto_rpow_atTop
    (show (0 : ℝ) < 9999999 / 10000000 - 3 / 5 by norm_num)).eventually_ge_atTop
    (1000 * D / ε)
  filter_upwards [hl, hp, eventually_ge_atTop (1 : ℝ)] with T hlog hpow hT k K hk hkU hK
  have hTpos : 0 < T := by linarith
  have hlog' : Real.log T ≤ T ^ (3 / 5 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hT),
      abs_of_nonneg (Real.rpow_nonneg hTpos.le _), one_mul] using hlog
  have h1 : (1 : ℝ) ≤ T ^ (3 / 5 : ℝ) := Real.one_le_rpow hT (by norm_num)
  have hb : C * (1 + k) + 6 * Real.log T ≤ D * T ^ (3 / 5 : ℝ) := by
    have hc := mul_le_mul_of_nonneg_left h1 hC
    have hkc := mul_le_mul_of_nonneg_left hkU hC
    dsimp [D]
    nlinarith only [hc, hkc, hlog']
  have hp' := (div_le_iff₀ hε).mp hpow
  have hh := mul_le_mul_of_nonneg_right hp' (Real.rpow_nonneg hTpos.le (3 / 5 : ℝ))
  have he : (T ^ (9999999 / 10000000 - 3 / 5 : ℝ) * ε) * T ^ (3 / 5 : ℝ) =
      ε * T ^ (9999999 / 10000000 : ℝ) := by
    rw [mul_right_comm, ← Real.rpow_add hTpos]
    norm_num
    ring
  rw [he] at hh
  have hK' := mul_le_mul_of_nonneg_left hK hε.le
  have hb' : D * T ^ (3 / 5 : ℝ) ≤ ε * K := by nlinarith only [hh, hK']
  exact hb.trans hb'

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticAmplificationBias
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed quadratic bias produces a large shared coefficient test -/

namespace Ostmann

open scoped BigOperators Classical

theorem norm_jacobi_complex_le (u : ℤ) (p : ℕ) : ‖(jacobiSym u p : ℂ)‖ ≤ 1 := by
  rcases jacobiSym.trichotomy u p with h | h | h <;> simp [h]

theorem quadraticAmplifiedCoefficients_identity (P : Finset ℕ) (k Z : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, Odd p) (hZ : ∀ p ∈ P, p ≤ Z)
    (e : ℕ → ℂ) (u : ℤ) :
    quadraticTransposeSum (Z ^ k) (quadraticAmplifiedCoefficients P k e) u =
      (∑ f : Fin k ↪ P, ∏ i, e (f i) * (jacobiSym u (f i) : ℂ)) / (P.card : ℂ) ^ k := by
  unfold quadraticAmplifiedCoefficients
  rw [quadratic_amplification_identity P k Z hP hodd hZ]
  have h := distinct_tuple_sum k (fun p : P => e p * (jacobiSym u p : ℂ))
  rw [subset_product_sum_subtype P k (fun p : ℕ => e p * (jacobiSym u p : ℂ))] at h
  rw [h]
  push_cast
  ring

theorem quadratic_amplification_error (P : Finset ℕ) (k Z : ℕ) (hk : 1 ≤ k)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, Odd p) (hZ : ∀ p ∈ P, p ≤ Z)
    (e : ℕ → ℂ) (he : ∀ p ∈ P, ‖e p‖ ≤ 1) (hcard : 0 < P.card) (u : ℤ) :
    ‖quadraticPrimeMean P e u ^ k -
      quadraticTransposeSum (Z ^ k) (quadraticAmplifiedCoefficients P k e) u‖ ≤
        (k : ℝ) ^ 2 / P.card := by
  rw [quadraticAmplifiedCoefficients_identity P k Z hP hodd hZ]
  have hy (p : P) : ‖e p * (jacobiSym u p : ℂ)‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul (he p p.property) (norm_jacobi_complex_le u p)
      (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)
  have h := normalized_distinct_product_error k hk
    (fun p : P => e p * (jacobiSym u p : ℂ)) hy (by simpa using hcard)
  rw [Finset.sum_coe_sort P (fun p : ℕ => e p * (jacobiSym u p : ℂ))] at h
  simpa only [quadraticPrimeMean, Fintype.card_coe] using h

theorem quadratic_amplification_lower (P : Finset ℕ) (k Z : ℕ) (hk : 1 ≤ k)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, Odd p) (hZ : ∀ p ∈ P, p ≤ Z)
    (e : ℕ → ℂ) (he : ∀ p ∈ P, ‖e p‖ ≤ 1) (hcard : 0 < P.card)
    (u : ℤ) (c : ℝ) (hc : 0 ≤ c) (hbias : c ≤ ‖quadraticPrimeMean P e u‖) :
    c ^ k - (k : ℝ) ^ 2 / P.card ≤
      ‖quadraticTransposeSum (Z ^ k) (quadraticAmplifiedCoefficients P k e) u‖ := by
  have herr := quadratic_amplification_error P k Z hk hP hodd hZ e he hcard u
  have hpow := pow_le_pow_left₀ hc hbias k
  have ht := norm_add_le
    (quadraticPrimeMean P e u ^ k - quadraticTransposeSum (Z ^ k) (quadraticAmplifiedCoefficients P k e) u)
    (quadraticTransposeSum (Z ^ k) (quadraticAmplifiedCoefficients P k e) u)
  rw [sub_add_cancel, norm_pow] at ht
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticKernelBias
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing from an affine value to its squarefree kernel -/

namespace Ostmann

open scoped BigOperators Classical

theorem jacobi_kernel_eq {u x : ℤ} {t p : ℕ} (hp : p.Prime) (hpt : ¬p ∣ t)
    (hx : u * (t : ℤ) ^ 2 = x) : jacobiSym x p = jacobiSym u p := by
  have hc : (t : ℤ).gcd p = 1 := by
    simpa using ((hp.coprime_iff_not_dvd.mpr hpt).symm : t.Coprime p)
  rw [← hx, jacobiSym.mul_left, jacobiSym.sq_one' hc, mul_one]

theorem quadratic_kernel_mean_error (P : Finset ℕ) (e : ℕ → ℂ)
    (hP : ∀ p ∈ P, p.Prime) (he : ∀ p ∈ P, ‖e p‖ ≤ 1)
    (u x : ℤ) (t : ℕ) (hx : u * (t : ℤ) ^ 2 = x) :
    ‖quadraticPrimeMean P e x - quadraticPrimeMean P e u‖ ≤
      2 * ((P.filter fun p => p ∣ t).card : ℝ) / P.card := by
  unfold quadraticPrimeMean
  rw [← sub_div, ← Finset.sum_sub_distrib, norm_div]
  have hsum : ‖∑ p ∈ P, (e p * (jacobiSym x p : ℂ) - e p * (jacobiSym u p : ℂ))‖ ≤
      2 * ((P.filter fun p => p ∣ t).card : ℝ) := by
    calc
      _ ≤ ∑ p ∈ P, ‖e p * (jacobiSym x p : ℂ) - e p * (jacobiSym u p : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ P, if p ∣ t then (2 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro p hp
        split_ifs with hpt
        · have hxnorm : ‖e p * (jacobiSym x p : ℂ)‖ ≤ 1 := by
            rw [norm_mul]
            exact (mul_le_mul (he p hp) (norm_jacobi_complex_le x p) (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)
          have hunorm : ‖e p * (jacobiSym u p : ℂ)‖ ≤ 1 := by
            rw [norm_mul]
            exact (mul_le_mul (he p hp) (norm_jacobi_complex_le u p) (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)
          exact (norm_sub_le _ _).trans (by linarith)
        · rw [jacobi_kernel_eq (hP p hp) hpt hx, sub_self, norm_zero]
      _ = _ := by rw [← Finset.sum_filter]; simp; ring
  have hden : ‖(P.card : ℂ)‖ = (P.card : ℝ) := by simp
  rw [hden]
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)

theorem prime_divisors_card_log_le (P : Finset ℕ) (t : ℕ) (ht : 0 < t)
    (hP : ∀ p ∈ P, p.Prime) (L : ℝ) (hL : ∀ p ∈ P, L ≤ Real.log (p : ℝ)) :
    ((P.filter fun p => p ∣ t).card : ℝ) * L ≤ Real.log (t : ℝ) := by
  calc
    _ = ∑ _p ∈ P.filter (fun p => p ∣ t), L := by simp
    _ ≤ ∑ p ∈ P.filter (fun p => p ∣ t), Real.log (p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact hL p (Finset.mem_filter.mp hp).1
    _ ≤ _ := sum_log_prime_divisors_le _ ht
      (fun p hp => hP p (Finset.mem_filter.mp hp).1)
      (fun _ hp => (Finset.mem_filter.mp hp).2)

theorem quadratic_kernel_bias_lower (P : Finset ℕ) (e : ℕ → ℂ)
    (hP : ∀ p ∈ P, p.Prime) (he : ∀ p ∈ P, ‖e p‖ ≤ 1)
    (u x : ℤ) (t : ℕ) (hx : u * (t : ℤ) ^ 2 = x)
    (c E : ℝ) (hbias : c + E ≤ ‖quadraticPrimeMean P e x‖)
    (hloss : 2 * ((P.filter fun p => p ∣ t).card : ℝ) / P.card ≤ E) :
    c ≤ ‖quadraticPrimeMean P e u‖ := by
  have herr := (quadratic_kernel_mean_error P e hP he u x t hx).trans hloss
  have ht := norm_add_le (quadraticPrimeMean P e x - quadraticPrimeMean P e u)
    (quadraticPrimeMean P e u)
  rw [sub_add_cancel] at ht
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_CommonCenterCharacter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Translating the original local biases to the common affine form -/

namespace Ostmann

open scoped BigOperators

theorem jacobi_commonCenter_identity (m p : ℕ) (h x t : ℤ) [Fact p.Prime]
    (hmp : m < p) (hm : 0 < m)
    (ht : (t : ZMod p) = (h : ZMod p) / (m : ZMod p)) :
    jacobiSym (x - t) p = jacobiSym (m : ℤ) p * jacobiSym ((m : ℤ) * x - h) p := by
  have hm0 : (m : ZMod p) ≠ 0 := by
    exact (ZMod.natCast_eq_zero_iff m p).not.mpr (Nat.not_dvd_of_pos_of_lt hm hmp)
  have htm : (m : ZMod p) * (t : ZMod p) = (h : ZMod p) := by
    rw [ht]
    field_simp
  have hmod : (((m : ℤ) * (x - t) : ℤ) : ZMod p) = (((m : ℤ) * x - h : ℤ) : ZMod p) := by
    push_cast
    linear_combination -htm
  have hχ := jacobiSym.mod_left' ((ZMod.intCast_eq_intCast_iff' _ _ p).mp hmod)
  rw [jacobiSym.mul_left] at hχ
  have hcop : (m : ℤ).gcd p = 1 := by
    simpa using ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt hm hmp) : p.Coprime m).symm
  have hsq := jacobiSym.sq_one hcop
  calc
    _ = jacobiSym (m : ℤ) p ^ 2 * jacobiSym (x - t) p := by rw [hsq, one_mul]
    _ = _ := by rw [← hχ]; ring

theorem commonCenterOrientation_norm (ε : ℕ → ℝ) (m p : ℕ)
    (hε : ε p = 1 ∨ ε p = -1) : ‖commonCenterOrientation ε m p‖ ≤ 1 := by
  unfold commonCenterOrientation
  rw [norm_mul]
  have he : ‖(ε p : ℂ)‖ = 1 := by rcases hε with h | h <;> simp [h]
  rw [he, one_mul]
  exact norm_jacobi_complex_le _ _

theorem commonCenter_oriented_value (ε : ℕ → ℝ) (t : ℕ → ℤ)
    (m p : ℕ) (h x : ℤ) [Fact p.Prime] (hmp : m < p) (hm : 0 < m)
    (ht : (t p : ZMod p) = (h : ZMod p) / (m : ZMod p)) :
    (orientedQuadraticValue ε t x p : ℂ) =
      commonCenterOrientation ε m p * (jacobiSym ((m : ℤ) * x - h) p : ℂ) := by
  unfold orientedQuadraticValue commonCenterOrientation
  push_cast
  rw [jacobi_commonCenter_identity m p h x (t p) hmp hm ht]
  push_cast
  ring

theorem quadraticPrimeMean_commonCenter (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (ε : ℕ → ℝ) (t : ℕ → ℤ) (m : ℕ) (h x : ℤ) (hm : 0 < m)
    (hmp : ∀ p ∈ P, m < p)
    (ht : ∀ (p : ℕ) (hp : p ∈ P),
      let _ : Fact p.Prime := ⟨hP p hp⟩
      (t p : ZMod p) = (h : ZMod p) / (m : ZMod p)) :
    quadraticPrimeMean P (commonCenterOrientation ε m) ((m : ℤ) * x - h) =
      (((∑ p ∈ P, orientedQuadraticValue ε t x p) / P.card : ℝ) : ℂ) := by
  unfold quadraticPrimeMean
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  let : Fact p.Prime := ⟨hP p hp⟩
  exact (commonCenter_oriented_value ε t m p h x (hmp p hp) hm (ht p hp)).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteBiasPopulation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed signed mean yields a positive population with large character bias -/

namespace Ostmann

open scoped BigOperators Classical

theorem finite_bias_population {ι : Type*} (S : Finset ι) (f : ι → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hf : ∀ i ∈ S, f i ≤ 1)
    (hsum : (S.card : ℝ) * c ≤ ∑ i ∈ S, f i) :
    (S.card : ℝ) * c / 2 ≤ ((S.filter fun i => c / 2 ≤ f i).card : ℝ) := by
  have hpoint (i : ι) (hi : i ∈ S) : f i ≤ c / 2 + if c / 2 ≤ f i then 1 else 0 := by
    split_ifs with h
    · linarith [hf i hi]
    · linarith
  have hh := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.sum_filter, mul_one] at hh
  linarith

theorem orientedPrimeMean_le_one (P : Finset ℕ) (ε : ℕ → ℝ) (t : ℕ → ℤ)
    (x : ℤ) (hε : ∀ p ∈ P, ε p = 1 ∨ ε p = -1) : orientedPrimeMean P ε t x ≤ 1 := by
  by_cases hP : P.Nonempty
  · have hcard : (0 : ℝ) < P.card := by exact_mod_cast Finset.card_pos.mpr hP
    apply (div_le_one hcard).mpr
    have hh : (∑ p ∈ P, orientedQuadraticValue ε t x p) ≤ ∑ _p ∈ P, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      rcases orientedQuadraticValue_ternary ε t x p (hε p hp) with h | h | h <;> rw [h] <;> norm_num
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using hh
  · simp only [orientedPrimeMean, Finset.not_nonempty_iff_eq_empty.mp hP,
      Finset.sum_empty, Finset.card_empty, Nat.cast_zero, div_zero, zero_le_one]

theorem orientedPrimeMean_sum_lower (P : Finset ℕ) (S : Finset ℤ)
    (ε : ℕ → ℝ) (t : ℕ → ℤ) (c : ℝ) (hP : 0 < P.card)
    (hmean : ∀ p ∈ P, (S.card : ℝ) * c ≤ ∑ x ∈ S, orientedQuadraticValue ε t x p) :
    (S.card : ℝ) * c ≤ ∑ x ∈ S, orientedPrimeMean P ε t x := by
  have hcard : (0 : ℝ) < P.card := by exact_mod_cast hP
  have hh := Finset.sum_le_sum hmean
  simp only [Finset.sum_const, nsmul_eq_mul] at hh
  simp only [orientedPrimeMean, ← Finset.sum_div]
  apply (le_div_iff₀ hcard).mpr
  rw [Finset.sum_comm]
  nlinarith only [hh]

theorem commonCenter_biased_population (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : Finset ℤ) (ε : ℕ → ℝ) (t : ℕ → ℤ) (m : ℕ) (h : ℤ) (c : ℝ)
    (hc : 0 ≤ c) (hm : 0 < m) (hcard : 0 < P.card)
    (hε : ∀ p ∈ P, ε p = 1 ∨ ε p = -1) (hmp : ∀ p ∈ P, m < p)
    (ht : ∀ (p : ℕ) (hp : p ∈ P), let _ : Fact p.Prime := ⟨hP p hp⟩
      (t p : ZMod p) = (h : ZMod p) / (m : ZMod p))
    (hmean : ∀ p ∈ P, (S.card : ℝ) * c ≤ ∑ x ∈ S, orientedQuadraticValue ε t x p) :
    ∃ U ⊆ S, (S.card : ℝ) * c / 2 ≤ (U.card : ℝ) ∧
      ∀ x ∈ U, c / 2 ≤ ‖quadraticPrimeMean P (commonCenterOrientation ε m) ((m : ℤ) * x - h)‖ := by
  let U := S.filter fun x => c / 2 ≤ orientedPrimeMean P ε t x
  refine ⟨U, Finset.filter_subset _ _, ?_, ?_⟩
  · exact finite_bias_population S _ c hc
      (fun x _ => orientedPrimeMean_le_one P ε t x hε)
      (orientedPrimeMean_sum_lower P S ε t c hcard hmean)
  · intro x hx
    have hh := (Finset.mem_filter.mp hx).2
    rw [quadraticPrimeMean_commonCenter P hP ε t m h x hm hmp ht, Complex.norm_real]
    exact hh.trans (le_abs_self _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_SignedSquarefreeRange
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A concrete four-piece cover of the signed squarefree integers -/

namespace Ostmann

open scoped BigOperators Classical

theorem signedSquarefreeRange_cover {M : ℕ} {u : ℤ}
    (hu : u ∈ signedSquarefreeRange M) :
    ∃ d ∈ quadraticSigns, ∃ v ∈ oddSquarefreeRange M, d * (v : ℤ) = u := by
  obtain ⟨huI, hu0, hsf⟩ := Finset.mem_filter.mp hu
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp huI
  have hn0 : 0 < u.natAbs := Int.natAbs_pos.mpr hu0
  have hnM : u.natAbs ≤ M := by
    have : (u.natAbs : ℤ) ≤ M := by rw [Int.natCast_natAbs]; exact abs_le.mpr ⟨hlo, hhi⟩
    exact_mod_cast this
  have hsign : (u.natAbs : ℤ) = u ∨ -(u.natAbs : ℤ) = u := by
    rw [Int.natCast_natAbs]
    rcases le_total 0 u with hp | hn
    · exact Or.inl (abs_of_nonneg hp)
    · exact Or.inr (by rw [abs_of_nonpos hn, neg_neg])
  by_cases ho : Odd u.natAbs
  · have hv : u.natAbs ∈ oddSquarefreeRange M :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn0, hnM⟩, ho, hsf⟩
    rcases hsign with hp | hn
    · exact ⟨1, by simp [quadraticSigns], u.natAbs, hv, by simpa using hp⟩
    · exact ⟨-1, by simp [quadraticSigns], u.natAbs, hv, by simpa using hn⟩
  · have he : 2 ∣ u.natAbs := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp ho)
    obtain ⟨v, hv⟩ := he
    have hsfv : Squarefree (2 * v) := hv ▸ hsf
    have hov : Odd v := Nat.coprime_two_left.mp (Nat.coprime_of_squarefree_mul hsfv)
    have hvM : v ∈ oddSquarefreeRange M := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hov, hsfv.of_mul_right⟩ <;>
        omega
    have hcast : (u.natAbs : ℤ) = 2 * v := by exact_mod_cast hv
    rcases hsign with hp | hn
    · exact ⟨2, by simp [quadraticSigns], v, hvM, by rw [← hcast, hp]⟩
    · exact ⟨-2, by simp [quadraticSigns], v, hvM, by rw [show (-2 : ℤ) * v = -(2 * v) by ring, ← hcast, hn]⟩

theorem sum_signedSquarefreeRange_le (M : ℕ) (f : ℤ → ℝ) (hf : ∀ u, 0 ≤ f u) :
    (∑ u ∈ signedSquarefreeRange M, f u) ≤
      ∑ d ∈ quadraticSigns, ∑ v ∈ oddSquarefreeRange M, f (d * v) := by
  let S := quadraticSigns.product (oddSquarefreeRange M)
  let g : ℤ × ℕ → ℤ := fun z => z.1 * z.2
  have hsub : signedSquarefreeRange M ⊆ S.image g := by
    intro u hu
    obtain ⟨d, hd, v, hv, h⟩ := signedSquarefreeRange_cover hu
    exact Finset.mem_image.mpr ⟨(d, v), Finset.mem_product.mpr ⟨hd, hv⟩, h⟩
  calc
    _ ≤ ∑ u ∈ S.image g, f u := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun u _ _ => hf u)
    _ ≤ ∑ z ∈ S, f (g z) := Finset.sum_image_le_of_nonneg (fun z _ => hf z)
    _ = _ := by simp [S, g, Finset.sum_product]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticKernelDecomposition
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual signed squarefree kernels of nonzero affine values -/

namespace Ostmann

open scoped BigOperators Classical

theorem exists_signed_squarefree_decomposition (x : ℤ) (hx : x ≠ 0) :
    ∃ (u : ℤ) (t : ℕ), u ≠ 0 ∧ 0 < t ∧ Squarefree u.natAbs ∧
      u * (t : ℤ) ^ 2 = x := by
  obtain ⟨a, t, ha, ht, heq, hsf⟩ := Nat.sq_mul_squarefree_of_pos (Int.natAbs_pos.mpr hx)
  have heqZ : (a : ℤ) * (t : ℤ) ^ 2 = |x| := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast (mul_comm a (t ^ 2)).trans heq
  rcases le_total 0 x with hp | hn
  · refine ⟨a, t, by exact_mod_cast ha.ne', ht, by simpa, ?_⟩
    simpa [abs_of_nonneg hp] using heqZ
  · refine ⟨-(a : ℤ), t, neg_ne_zero.mpr (by exact_mod_cast ha.ne'), ht, by simpa, ?_⟩
    rw [abs_of_nonpos hn] at heqZ
    linear_combination -heqZ

theorem signed_kernel_mem_range {M : ℕ} {u x : ℤ} {t : ℕ}
    (hu : u ≠ 0) (ht : 0 < t) (hsf : Squarefree u.natAbs)
    (heq : u * (t : ℤ) ^ 2 = x) (hbound : |x| ≤ M) :
    u ∈ signedSquarefreeRange M := by
  have htZ : (1 : ℤ) ≤ t := by exact_mod_cast ht
  have huabs : 0 ≤ |u| := abs_nonneg _
  have hle : |u| ≤ |x| := by
    rw [← heq, abs_mul, abs_pow, abs_of_nonneg (by omega : (0 : ℤ) ≤ t)]
    have ht2 : (1 : ℤ) ≤ (t : ℤ) ^ 2 := by nlinarith
    simpa using mul_le_mul_of_nonneg_left ht2 huabs
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr (abs_le.mp (hle.trans hbound)), hu, hsf⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AffineKernelBias
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual squarefree kernels retain the common-center character bias -/

namespace Ostmann

open scoped BigOperators Classical

theorem quadraticPrimeMean_zero (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (e : ℕ → ℂ) :
    quadraticPrimeMean P e 0 = 0 := by
  unfold quadraticPrimeMean
  have hz : (∑ p ∈ P, e p * (jacobiSym 0 p : ℂ)) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    rw [jacobiSym.zero_left (hP p hp).one_lt, Int.cast_zero, mul_zero]
  rw [hz, zero_div]

theorem exists_affine_kernel_assignment (S : Finset ℤ) (m : ℕ) (h : ℤ)
    (hnon : ∀ x ∈ S, (m : ℤ) * x - h ≠ 0) :
    ∃ (kernel : ℤ → ℤ) (root : ℤ → ℕ), ∀ x ∈ S,
      kernel x ≠ 0 ∧ 0 < root x ∧ Squarefree (kernel x).natAbs ∧
      kernel x * (root x : ℤ) ^ 2 = (m : ℤ) * x - h := by
  have hex (x : ℤ) : ∃ (u : ℤ) (t : ℕ), x ∈ S →
      u ≠ 0 ∧ 0 < t ∧ Squarefree u.natAbs ∧ u * (t : ℤ) ^ 2 = (m : ℤ) * x - h := by
    by_cases hx : x ∈ S
    · obtain ⟨u, t, hu⟩ := exists_signed_squarefree_decomposition ((m : ℤ) * x - h) (hnon x hx)
      exact ⟨u, t, fun _ => hu⟩
    · exact ⟨0, 0, fun hh => (hx hh).elim⟩
  choose kernel root hh using hex
  exact ⟨kernel, root, hh⟩

theorem kernel_root_log_bound (u x : ℤ) (t : ℕ) (Y : ℝ)
    (hu : u ≠ 0) (ht : 0 < t) (heq : u * (t : ℤ) ^ 2 = x)
    (hx : |(x : ℝ)| ≤ Real.exp Y) : Real.log (t : ℝ) ≤ Y := by
  have hu1 : (1 : ℝ) ≤ |(u : ℝ)| := by exact_mod_cast Int.one_le_abs hu
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have heqR : (u : ℝ) * (t : ℝ) ^ 2 = x := by exact_mod_cast heq
  have habs : |(u : ℝ)| * (t : ℝ) ^ 2 = |(x : ℝ)| := by
    rw [← heqR, abs_mul, abs_pow]
    simp only [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) t)]
  have htA : (t : ℝ) ≤ |(x : ℝ)| := by nlinarith [sq_nonneg ((t : ℝ) - 1)]
  exact (Real.log_le_iff_le_exp (by exact_mod_cast ht)).mpr (htA.trans hx)

theorem kernel_prime_divisor_loss (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (t : ℕ) (ht : 0 < t) (T Y c : ℝ) (hT : 0 < T) (hcard : 0 < P.card)
    (hlogp : ∀ p ∈ P, T ≤ Real.log (p : ℝ)) (hlogt : Real.log (t : ℝ) ≤ Y)
    (hsize : 2 * Y ≤ c * P.card * T) :
    2 * ((P.filter fun p => p ∣ t).card : ℝ) / P.card ≤ c := by
  have hc : (0 : ℝ) < P.card := by exact_mod_cast hcard
  have hh := (prime_divisors_card_log_le P t ht hP T hlogp).trans hlogt
  apply (div_le_iff₀ hc).mpr
  apply (mul_le_mul_iff_left₀ hT).mp
  nlinarith only [hh, hsize]

/-- A single actual kernel assignment is shared by all later tests. -/
theorem exists_biased_affine_kernels (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : Finset ℤ) (m : ℕ) (h : ℤ) (e : ℕ → ℂ) (c T Y : ℝ)
    (hc : 0 < c) (hT : 0 < T) (hcard : 0 < P.card) (he : ∀ p ∈ P, ‖e p‖ ≤ 1)
    (hlogp : ∀ p ∈ P, T ≤ Real.log (p : ℝ))
    (hsize : 2 * Y ≤ (c / 2) * P.card * T)
    (hbound : ∀ x ∈ S, |(((m : ℤ) * x - h : ℤ) : ℝ)| ≤ Real.exp Y)
    (hbias : ∀ x ∈ S, c ≤ ‖quadraticPrimeMean P e ((m : ℤ) * x - h)‖) :
    ∃ (kernel : ℤ → ℤ) (root : ℤ → ℕ), ∀ x ∈ S,
      kernel x ≠ 0 ∧ 0 < root x ∧ Squarefree (kernel x).natAbs ∧
      kernel x * (root x : ℤ) ^ 2 = (m : ℤ) * x - h ∧
      c / 2 ≤ ‖quadraticPrimeMean P e (kernel x)‖ := by
  have hnon (x : ℤ) (hx : x ∈ S) : (m : ℤ) * x - h ≠ 0 := by
    intro hz
    have hh := hbias x hx
    rw [hz, quadraticPrimeMean_zero P hP e, norm_zero] at hh
    linarith
  obtain ⟨kernel, root, hkr⟩ := exists_affine_kernel_assignment S m h hnon
  refine ⟨kernel, root, ?_⟩
  intro x hx
  obtain ⟨hu, ht, hsf, hEq⟩ := hkr x hx
  refine ⟨hu, ht, hsf, hEq, ?_⟩
  apply quadratic_kernel_bias_lower P e hP he (kernel x) ((m : ℤ) * x - h) (root x) hEq
    (c / 2) (c / 2)
  · have hh := hbias x hx
    linarith
  · exact kernel_prime_divisor_loss P hP (root x) ht T Y (c / 2) hT hcard hlogp
      (kernel_root_log_bound _ _ _ Y hu ht hEq (hbound x hx)) hsize

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_SignedQuadraticSieve
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The signed kernel form follows from Heath-Brown's published theorem -/

namespace Ostmann

open scoped BigOperators Classical

theorem quadraticSieveEnergy_numeratorTwist_le (N : ℕ) (d : ℤ) (b : ℕ → ℂ) :
    quadraticSieveEnergy N (quadraticNumeratorTwist d b) ≤ quadraticSieveEnergy N b := by
  apply Finset.sum_le_sum
  intro s _
  rcases jacobiSym.trichotomy d s with h | h | h <;>
    simp [quadraticNumeratorTwist, h]

theorem quadraticTransposeSum_mul (N : ℕ) (b : ℕ → ℂ) (d u : ℤ) :
    quadraticTransposeSum N b (d * u) =
      quadraticTransposeSum N (quadraticNumeratorTwist d b) u := by
  apply Finset.sum_congr rfl
  intro s _
  simp only [jacobiSym.mul_left, Int.cast_mul, quadraticNumeratorTwist, mul_assoc]

theorem quadratic_twist_sum_bound (M N : ℕ) (C ε : ℝ) (b : ℕ → ℂ) (d : ℤ)
    (hK : 0 ≤ C * ((M : ℝ) * N) ^ ε * ((M : ℝ) + N))
    (hb : ∀ b' : ℕ → ℂ,
      (∑ v ∈ oddSquarefreeRange M, ‖quadraticTransposeSum N b' v‖ ^ 2) ≤
        C * ((M : ℝ) * N) ^ ε * ((M : ℝ) + N) * quadraticSieveEnergy N b') :
    (∑ v ∈ oddSquarefreeRange M, ‖quadraticTransposeSum N b (d * v)‖ ^ 2) ≤
      C * ((M : ℝ) * N) ^ ε * ((M : ℝ) + N) * quadraticSieveEnergy N b := by
  calc
    _ = ∑ v ∈ oddSquarefreeRange M,
        ‖quadraticTransposeSum N (quadraticNumeratorTwist d b) v‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro v _
      rw [quadraticTransposeSum_mul]
    _ ≤ _ := (hb (quadraticNumeratorTwist d b)).trans
      (mul_le_mul_of_nonneg_left (quadraticSieveEnergy_numeratorTwist_le N d b) hK)

/-- Four numerator twists and two reciprocity classes suffice, including the
kernels `1` and `-1`. The constant here is exactly eight times the published one. -/
theorem quadratic_signed_bound (P : PublishedQuadraticLargeSieve)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℕ, 1 ≤ M → 1 ≤ N → ∀ b : ℕ → ℂ,
      (∑ u ∈ signedSquarefreeRange M, ‖quadraticTransposeSum N b u‖ ^ 2) ≤
        C * ((M : ℝ) * N) ^ ε * ((M : ℝ) + N) * quadraticSieveEnergy N b := by
  obtain ⟨C, hC, hbound⟩ := quadratic_transpose_odd_bound P ε hε
  refine ⟨4 * C, by positivity, ?_⟩
  intro M N hM hN b
  have hK : 0 ≤ C * ((M : ℝ) * N) ^ ε * ((M : ℝ) + N) := by positivity
  calc
    _ ≤ ∑ d ∈ quadraticSigns, ∑ v ∈ oddSquarefreeRange M,
        ‖quadraticTransposeSum N b (d * v)‖ ^ 2 :=
      by
        exact sum_signedSquarefreeRange_le M _ (fun _ => sq_nonneg _)
    _ ≤ ∑ _d ∈ quadraticSigns,
        C * ((M : ℝ) * N) ^ ε * ((M : ℝ) + N) * quadraticSieveEnergy N b := by
      apply Finset.sum_le_sum
      intro d _
      exact quadratic_twist_sum_bound M N C ε b d hK (hbound M N hM hN)
    _ = _ := by
      rw [Finset.sum_const, show quadraticSigns.card = 4 by norm_num [quadraticSigns]]
      simp only [nsmul_eq_mul, Nat.cast_ofNat]
      ring

/-- The genuine finite kernel-count consequence. Its sole analytic hypothesis
is the published large sieve, and the test array is shared by all kernels. -/
theorem quadratic_kernel_count (P : PublishedQuadraticLargeSieve)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M N : ℕ) (b : ℕ → ℂ) (U : Finset ℤ) (a : ℝ),
      1 ≤ M → 1 ≤ N → 0 < a → U ⊆ signedSquarefreeRange M →
      (∀ u ∈ U, a ≤ ‖quadraticTransposeSum N b u‖) →
      (U.card : ℝ) ≤ C * ((M : ℝ) * N) ^ ε * ((M : ℝ) + N) *
        quadraticSieveEnergy N b / a ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := quadratic_signed_bound P ε hε
  refine ⟨C, hC, ?_⟩
  intro M N b U a hM hN ha hU htest
  apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
  calc
    (U.card : ℝ) * a ^ 2 = ∑ _u ∈ U, a ^ 2 := by simp
    _ ≤ ∑ u ∈ U, ‖quadraticTransposeSum N b u‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro u hu
      exact pow_le_pow_left₀ ha.le (htest u hu) 2
    _ ≤ ∑ u ∈ signedSquarefreeRange M, ‖quadraticTransposeSum N b u‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hU (fun _ _ _ => sq_nonneg _)
    _ ≤ _ := hbound M N hM hN b

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticKernelCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative kernel counting from a shared character bias -/

namespace Ostmann

open scoped BigOperators Classical

/-- Heath-Brown's quadratic large sieve bounds the number of signed
squarefree kernels with a common amplified character bias. -/
theorem quadratic_biased_kernel_count (sieve : PublishedQuadraticLargeSieve)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ) (k Z M : ℕ) (e : ℕ → ℂ)
      (U : Finset ℤ) (c : ℝ),
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Odd p) → (∀ p ∈ P, p ≤ Z) →
      (∀ p ∈ P, ‖e p‖ ≤ 1) → 0 < P.card → 1 ≤ k → 1 ≤ Z → 1 ≤ M →
      0 ≤ c → 0 < c ^ k - (k : ℝ) ^ 2 / P.card →
      U ⊆ signedSquarefreeRange M →
      (∀ u ∈ U, c ≤ ‖quadraticPrimeMean P e u‖) →
      (U.card : ℝ) ≤ C * ((M : ℝ) * Z ^ k) ^ ε * ((M : ℝ) + Z ^ k) *
        ((k.factorial : ℝ) / (P.card : ℝ) ^ k) /
          (c ^ k - (k : ℝ) ^ 2 / P.card) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := quadratic_kernel_count sieve ε hε
  refine ⟨C, hC, ?_⟩
  intro P k Z M e U c hP hodd hZ he hcard hk hZ1 hM hc hpos hU hbias
  have htest (u : ℤ) (hu : u ∈ U) :=
    quadratic_amplification_lower P k Z hk hP hodd hZ e he hcard u c hc (hbias u hu)
  have hb := hbound M (Z ^ k) (quadraticAmplifiedCoefficients P k e) U
    (c ^ k - (k : ℝ) ^ 2 / P.card) hM (Nat.one_le_pow _ _ hZ1) hpos hU htest
  have henergy := quadratic_amplification_energy P k (Z ^ k) e hP he hcard
  change quadraticSieveEnergy (Z ^ k) (quadraticAmplifiedCoefficients P k e) ≤ _ at henergy
  apply hb.trans
  have hfactor : 0 ≤ C * ((M : ℝ) * (Z ^ k : ℕ)) ^ ε * ((M : ℝ) + (Z ^ k : ℕ)) := by
    positivity
  have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left henergy hfactor)
    (sq_nonneg (c ^ k - (k : ℝ) ^ 2 / P.card))
  simpa only [Nat.cast_pow] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_CommonCenterCoefficientBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original common-center set controls the amplification energy -/

namespace Ostmann

open Filter

theorem eventual_commonCenter_coefficient_budget (Cpop : ℝ) (hCpop : 500 ≤ Cpop) :
    ∀ᶠ T : ℝ in atTop, ∀ (r : ℕ) (J J₀ Z : ℝ),
      2 ≤ r → (r : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      0 < J → 0 < J₀ → 0 ≤ Z →
      Real.exp T ≤ Cpop * T * J → J * Real.exp (-T / (r - 1 : ℕ)) ≤ J₀ →
      Z ≤ Real.exp (T + 1) →
      Z ^ r * (r.factorial : ℝ) / J₀ ^ r ≤ Real.exp (3 * T) := by
  let C := Cpop * Real.exp 1
  have hC : 1 ≤ C := by
    have he : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp (by norm_num)
    have hh := mul_le_mul_of_nonneg_left he (show 0 ≤ Cpop by linarith)
    dsimp [C]
    linarith
  filter_upwards [eventual_repeat_power_budget C 1 hC zero_lt_one,
    eventually_ge_atTop (1 : ℝ)] with T hbudget hT r J J₀ Z hr hrU hJ hJ₀ hZ hpop hcenter hZU
  have hTpos : 0 < T := by linarith
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  have hprev : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ r by omega)]; norm_num
  have hprevpos : (0 : ℝ) < (r - 1 : ℕ) := by exact_mod_cast (show 0 < r - 1 by omega)
  have hK : T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ T := by
    have hp : T ^ (9999999 / 10000000 : ℝ) ≤ T := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT
        (show (9999999 / 10000000 : ℝ) ≤ 1 by norm_num)
    linarith [Real.rpow_nonneg hTpos.le (9999999 / 10000000 : ℝ)]
  have hrep := hbudget r T hrU hK
  have hbase : C * T * (r : ℝ) ≤ 16 * C * T * (r : ℝ) ^ 3 := by
    have hr3 : (r : ℝ) ≤ (r : ℝ) ^ 3 := by nlinarith [sq_nonneg ((r : ℝ) - 1)]
    calc
      _ ≤ C * T * (r : ℝ) ^ 3 := mul_le_mul_of_nonneg_left hr3 (by positivity)
      _ ≤ 16 * (C * T * (r : ℝ) ^ 3) := le_mul_of_one_le_left (by positivity) (by norm_num)
      _ = _ := by ring
  have hsmall : (C * T * (r : ℝ)) ^ r ≤ Real.exp T := by
    have hp := pow_le_pow_left₀ (by positivity) hbase r
    have hc2 : 1 ≤ C ^ 2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hc2 (pow_nonneg (show 0 ≤ 16 * C * T * (r : ℝ) ^ 3 by positivity) r)
    norm_num only [one_mul] at hrep
    nlinarith only [hp, hh, hrep]
  let u := T / (r - 1 : ℕ)
  have hZJ : Z ≤ (C * T * Real.exp u) * J₀ := by
    have he : Real.exp u * Real.exp (-u) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hcen : J * Real.exp (-u) ≤ J₀ := by simpa only [u, neg_div] using hcenter
    calc
      Z ≤ Real.exp (T + 1) := hZU
      _ = Real.exp 1 * Real.exp T := by rw [Real.exp_add]; ring
      _ ≤ Real.exp 1 * (Cpop * T * J) := mul_le_mul_of_nonneg_left hpop (Real.exp_nonneg _)
      _ = (Real.exp 1 * (Cpop * T * J)) * (Real.exp u * Real.exp (-u)) := by rw [he, mul_one]
      _ = (C * T * Real.exp u) * (J * Real.exp (-u)) := by dsimp [C]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcen (by positivity)
  have hfac : (r.factorial : ℝ) ≤ (r : ℝ) ^ r := by exact_mod_cast Nat.factorial_le_pow r
  have hu : (r : ℝ) * u ≤ 2 * T := by
    dsimp [u]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hprevpos).mpr
    rw [hprev]
    have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
    nlinarith
  calc
    Z ^ r * (r.factorial : ℝ) / J₀ ^ r ≤
        ((C * T * Real.exp u) * J₀) ^ r * (r : ℝ) ^ r / J₀ ^ r := by gcongr
    _ = (C * T * (r : ℝ)) ^ r * Real.exp ((r : ℝ) * u) := by
      rw [Real.exp_nat_mul, ← mul_pow]
      field_simp
      ring
    _ ≤ Real.exp T * Real.exp (2 * T) := by gcongr
    _ = Real.exp (3 * T) := by rw [← Real.exp_add]; congr 1; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_KernelAmplificationMargin
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed kernel bias survives distinct-tuple amplification -/

namespace Ostmann

open Filter

theorem eventual_kernel_amplification_margin (c : ℝ) (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop, ∀ (r : ℕ) (J : ℝ),
      (r : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) → Real.exp (3 * T / 5) ≤ J →
      Real.exp (-T / 10) ≤ c ^ r ∧
      0 < c ^ r - (r : ℝ) ^ 2 / J ∧
      (c ^ r - (r : ℝ) ^ 2 / J)⁻¹ ^ 2 ≤ Real.exp T := by
  have hpoly := ((isLittleO_pow_exp_pos_mul_atTop 2 (show (0 : ℝ) < 1 / 2 by norm_num)).const_mul_left 8).bound
    (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [eventual_amplification_log_loss |Real.log c| (1 / 10) (abs_nonneg _) (by norm_num),
    hpoly, eventually_ge_atTop (5 : ℝ)] with T hlog hp hT r J hr hJ
  have hT1 : 1 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hK : T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ T := by
    have hh : T ^ (9999999 / 10000000 : ℝ) ≤ T := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT1
        (show (9999999 / 10000000 : ℝ) ≤ 1 by norm_num)
    linarith [Real.rpow_nonneg hTpos.le (9999999 / 10000000 : ℝ)]
  have hl := hlog r T (Nat.cast_nonneg _) hr hK
  have hlower : -T / 10 ≤ (r : ℝ) * Real.log c := by
    have hh := mul_le_mul_of_nonneg_left (neg_abs_le (Real.log c)) (Nat.cast_nonneg (α := ℝ) r)
    nlinarith [Real.log_nonneg hT1, abs_nonneg (Real.log c)]
  have hcPow : Real.exp (-T / 10) ≤ c ^ r := by
    have hh := Real.exp_le_exp.mpr hlower
    rwa [Real.exp_nat_mul, Real.exp_log hc] at hh
  have hJpos : 0 < J := (Real.exp_pos _).trans_le hJ
  have hrT : (r : ℝ) ≤ 2 * T := hr.trans (by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT1
      (show (3 / 5 : ℝ) ≤ 1 by norm_num))
  have hp' : 8 * T ^ 2 ≤ Real.exp (T / 2) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 8 * T ^ 2),
      abs_of_pos (Real.exp_pos _), one_mul, one_div, inv_mul_eq_div] using hp
  have herror : 2 * (r : ℝ) ^ 2 / J ≤ Real.exp (-T / 10) := by
    apply (div_le_iff₀ hJpos).mpr
    calc
      _ ≤ 8 * T ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) r]
      _ ≤ Real.exp (T / 2) := hp'
      _ = Real.exp (-T / 10) * Real.exp (3 * T / 5) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hJ (Real.exp_nonneg _)
  have hgap : Real.exp (-T / 10) / 2 ≤ c ^ r - (r : ℝ) ^ 2 / J := by
    have he : 2 * ((r : ℝ) ^ 2 / J) ≤ Real.exp (-T / 10) := by simpa only [mul_div_assoc] using herror
    linarith
  have hgapPos : 0 < c ^ r - (r : ℝ) ^ 2 / J := (by positivity : 0 < Real.exp (-T / 10) / 2).trans_le hgap
  refine ⟨hcPow, hgapPos, ?_⟩
  have hinv : (c ^ r - (r : ℝ) ^ 2 / J)⁻¹ ≤ 2 * Real.exp (T / 10) := by
    have hi := one_div_le_one_div_of_le (by positivity : 0 < Real.exp (-T / 10) / 2) hgap
    have he : 1 / (Real.exp (-T / 10) / 2) = 2 * Real.exp (T / 10) := by
      rw [show -T / 10 = -(T / 10) by ring, Real.exp_neg]
      field_simp
    simpa only [one_div, he] using hi
  calc
    _ ≤ (2 * Real.exp (T / 10)) ^ 2 := pow_le_pow_left₀ (inv_nonneg.mpr hgapPos.le) hinv 2
    _ = 4 * Real.exp (T / 5) := by
      rw [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num, ← Real.exp_nat_mul]
      congr 2
      norm_num
      ring
    _ ≤ Real.exp (4 * T / 5) * Real.exp (T / 5) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      linarith [Real.add_one_le_exp (4 * T / 5)]
    _ = Real.exp T := by rw [← Real.exp_add]; congr 1; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_KernelCountFromCenter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The quadratic sieve counts the kernels of the actual common-center bias -/

namespace Ostmann

open Filter

theorem quadratic_count_scalar_budget (C F E S M g T : ℝ)
    (hC : 0 ≤ C) (hF : 0 ≤ F) (hE : 0 ≤ E) (hM : M ≤ S)
    (henergy : S * E ≤ Real.exp (3 * T)) (hgap : g⁻¹ ^ 2 ≤ Real.exp T) :
    C * F * (M + S) * E / g ^ 2 ≤ 2 * C * F * Real.exp (4 * T) := by
  calc
    _ ≤ C * F * (2 * S) * E / g ^ 2 := by gcongr; linarith
    _ = 2 * C * F * (S * E) * (g⁻¹ ^ 2) := by rw [div_eq_mul_inv, inv_pow]; ring
    _ ≤ 2 * C * F * Real.exp (3 * T) * Real.exp T := by gcongr
    _ = 2 * C * F * (Real.exp (3 * T) * Real.exp T) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

theorem eventual_kernel_count_prefactor (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ L : ℝ, T ^ (3 / 2 : ℝ) ≤ L →
      2 * C * Real.exp (4 * T) ≤ Real.exp (ε * L) := by
  let D := |Real.log (2 * C)| + 4
  have hD : 0 < D := by dsimp [D]; positivity
  have hp := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).eventually_ge_atTop (D / ε)
  filter_upwards [hp, eventually_ge_atTop (1 : ℝ)] with T hpow hT L hL
  have hTpos : 0 < T := by linarith
  have hd : D * T ≤ ε * T ^ (3 / 2 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right ((div_le_iff₀ hε).mp hpow) hTpos.le
    have he : T ^ (1 / 2 : ℝ) * T = T ^ (3 / 2 : ℝ) := by
      calc
        _ = T ^ (1 / 2 : ℝ) * T ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = T ^ (1 / 2 + 1 : ℝ) := (Real.rpow_add hTpos _ _).symm
        _ = _ := by norm_num
    rw [mul_right_comm, he] at hh
    nlinarith only [hh]
  have hl : Real.log (2 * C) + 4 * T ≤ ε * L := by
    have hh := mul_le_mul_of_nonneg_left hT (abs_nonneg (Real.log (2 * C)))
    have hll := mul_le_mul_of_nonneg_left hL hε.le
    dsimp [D] at hd
    nlinarith [le_abs_self (Real.log (2 * C))]
  calc
    _ = Real.exp (Real.log (2 * C) + 4 * T) := by rw [Real.exp_add, Real.exp_log (by positivity)]
    _ ≤ _ := Real.exp_le_exp.mpr hl

/-- A concrete version of the manuscript's X^(3 epsilon + o(1)) count.
The common-center loss and distinct-tuple error are both discharged. -/
theorem eventual_kernel_count_from_commonCenter (sieve : PublishedQuadraticLargeSieve)
    (Cpop : ℝ) (hCpop : 500 ≤ Cpop)
    (ε c : ℝ) (hε : 0 < ε) (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop, ∀ (L J : ℝ) (P : Finset ℕ) (r Z M : ℕ)
      (e : ℕ → ℂ) (U : Finset ℤ),
      T ^ (3 / 2 : ℝ) ≤ L → 2 ≤ r → (r : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      0 < J → Real.exp T ≤ Cpop * T * J →
      J * Real.exp (-T / (r - 1 : ℕ)) ≤ P.card →
      Real.exp (3 * T / 5) ≤ P.card → (Z : ℝ) ≤ Real.exp (T + 1) →
      1 ≤ Z → 1 ≤ M → M ≤ Z ^ r → ((Z : ℝ) ^ r) ≤ Real.exp (2 * L) →
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Odd p) → (∀ p ∈ P, p ≤ Z) →
      (∀ p ∈ P, ‖e p‖ ≤ 1) → U ⊆ signedSquarefreeRange M →
      (∀ u ∈ U, c ≤ ‖quadraticPrimeMean P e u‖) →
      (U.card : ℝ) ≤ Real.exp (3 * ε * L) := by
  obtain ⟨C, hC, hbound⟩ := quadratic_biased_kernel_count sieve (ε / 2) (by positivity)
  filter_upwards [eventual_commonCenter_coefficient_budget Cpop hCpop, eventual_kernel_amplification_margin c hc,
    eventual_kernel_count_prefactor C ε hC hε] with T hcoef hmargin hpref
  intro L J P r Z M e U hL hr hrU hJ hpop hcenter hsize hZupper hZ hM hMS hS
    hP hodd hPZ he hU hbias
  have hcard : (0 : ℝ) < P.card := (Real.exp_pos _).trans_le hsize
  have hcardN : 0 < P.card := by exact_mod_cast hcard
  obtain ⟨_, hgapPos, hgap⟩ := hmargin r P.card hrU hsize
  have henergy := hcoef r J P.card Z hr hrU hJ hcard (Nat.cast_nonneg _) hpop hcenter hZupper
  have hcount := hbound P r Z M e U c hP hodd hPZ he hcardN (by omega) hZ hM hc.le hgapPos hU hbias
  have hMSR : (M : ℝ) ≤ (Z : ℝ) ^ r := by exact_mod_cast hMS
  have heR : (Z : ℝ) ^ r * ((r.factorial : ℝ) / (P.card : ℝ) ^ r) ≤ Real.exp (3 * T) := by
    simpa only [mul_div_assoc] using henergy
  have hb := quadratic_count_scalar_budget C (((M : ℝ) * (Z : ℝ) ^ r) ^ (ε / 2))
    ((r.factorial : ℝ) / (P.card : ℝ) ^ r) ((Z : ℝ) ^ r) M
    (c ^ r - (r : ℝ) ^ 2 / P.card) T hC.le (by positivity) (by positivity) hMSR heR hgap
  have hh : (U.card : ℝ) ≤ 2 * C * (((M : ℝ) * (Z : ℝ) ^ r) ^ (ε / 2)) * Real.exp (4 * T) :=
    hcount.trans hb
  have hprod : (M : ℝ) * (Z : ℝ) ^ r ≤ Real.exp (4 * L) := by
    calc
      _ ≤ Real.exp (2 * L) * Real.exp (2 * L) := mul_le_mul (hMSR.trans hS) hS (by positivity) (by positivity)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hpower : ((M : ℝ) * (Z : ℝ) ^ r) ^ (ε / 2) ≤ Real.exp (2 * ε * L) := by
    calc
      _ ≤ (Real.exp (4 * L)) ^ (ε / 2) := Real.rpow_le_rpow (by positivity) hprod (by positivity)
      _ = _ := by rw [← Real.exp_mul]; congr 1; ring
  calc
    (U.card : ℝ) ≤ _ := hh
    _ = (2 * C * Real.exp (4 * T)) * (((M : ℝ) * (Z : ℝ) ^ r) ^ (ε / 2)) := by ring
    _ ≤ Real.exp (ε * L) * Real.exp (2 * ε * L) := mul_le_mul (hpref L hL) hpower (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AffineKernelCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual affine values have few distinct biased squarefree kernels -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem eventual_affine_kernel_count (sieve : PublishedQuadraticLargeSieve)
    (Cpop : ℝ) (hCpop : 500 ≤ Cpop)
    (ε c : ℝ) (hε : 0 < ε) (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop, ∀ (L J : ℝ) (P : Finset ℕ) (r Z M m : ℕ)
      (h : ℤ) (e : ℕ → ℂ) (S : Finset ℤ),
      T ^ (3 / 2 : ℝ) ≤ L → 2 ≤ r → (r : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      0 < J → Real.exp T ≤ Cpop * T * J →
      J * Real.exp (-T / (r - 1 : ℕ)) ≤ P.card →
      Real.exp (3 * T / 5) ≤ P.card → (Z : ℝ) ≤ Real.exp (T + 1) →
      1 ≤ Z → 1 ≤ M → M ≤ Z ^ r → ((Z : ℝ) ^ r) ≤ Real.exp (2 * L) →
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Odd p) → (∀ p ∈ P, p ≤ Z) →
      (∀ p ∈ P, ‖e p‖ ≤ 1) → (∀ p ∈ P, T ≤ Real.log (p : ℝ)) →
      4 * L ≤ (c / 2) * P.card * T →
      (∀ x ∈ S, |(m : ℤ) * x - h| ≤ M) →
      (∀ x ∈ S, c ≤ ‖quadraticPrimeMean P e ((m : ℤ) * x - h)‖) →
      ∃ (kernel : ℤ → ℤ) (root : ℤ → ℕ),
        ((S.image kernel).card : ℝ) ≤ Real.exp (3 * ε * L) ∧
        ∀ x ∈ S, kernel x ≠ 0 ∧ 0 < root x ∧ Squarefree (kernel x).natAbs ∧
          kernel x * (root x : ℤ) ^ 2 = (m : ℤ) * x - h ∧
          c / 2 ≤ ‖quadraticPrimeMean P e (kernel x)‖ := by
  filter_upwards [eventual_kernel_count_from_commonCenter sieve Cpop hCpop ε (c / 2) hε (by positivity),
    eventually_ge_atTop (1 : ℝ)] with T hcount hT
  intro L J P r Z M m h e S hL hr hrU hJ hpop hcenter hsize hZU hZ hM hMS hS
    hP hodd hPZ he hlogp hdiscard hbound hbias
  have hcard : 0 < P.card := by
    have hh := (Real.exp_pos (3 * T / 5)).trans_le hsize
    exact_mod_cast hh
  have hMexp : (M : ℝ) ≤ Real.exp (2 * L) := (by exact_mod_cast hMS : (M : ℝ) ≤ (Z : ℝ) ^ r).trans hS
  have hb (x : ℤ) (hx : x ∈ S) : |(((m : ℤ) * x - h : ℤ) : ℝ)| ≤ Real.exp (2 * L) := by
    have hh : |(((m : ℤ) * x - h : ℤ) : ℝ)| ≤ M := by exact_mod_cast hbound x hx
    exact hh.trans hMexp
  obtain ⟨kernel, root, hkr⟩ := exists_biased_affine_kernels P hP S m h e c T (2 * L)
    hc (by linarith) hcard he hlogp (by linarith) hb hbias
  refine ⟨kernel, root, ?_, hkr⟩
  apply hcount L J P r Z M e (S.image kernel) hL hr hrU hJ hpop hcenter hsize hZU
    hZ hM hMS hS hP hodd hPZ he
  · intro u hu
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hu, ht, hsf, heq, _⟩ := hkr x hx
    exact signed_kernel_mem_range hu ht hsf heq (hbound x hx)
  · intro u hu
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    exact (hkr x hx).2.2.2.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_KernelPairIdentification
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Disjoint prime supports identify a kernel pair from its product -/

namespace Ostmann

open scoped Classical

theorem cross_coprime_factor_unique {a b c d : ℕ} (ha : 0 < a)
    (had : a.Coprime d) (hcb : c.Coprime b) (hprod : a * b = c * d) :
    a = c ∧ b = d := by
  have hac : a ∣ c := had.dvd_of_dvd_mul_right (hprod ▸ dvd_mul_right a b)
  have hca : c ∣ a := hcb.dvd_of_dvd_mul_right (hprod.symm ▸ dvd_mul_right c d)
  have hacEq := Nat.dvd_antisymm hac hca
  refine ⟨hacEq, ?_⟩
  rw [← hacEq] at hprod
  exact Nat.eq_of_mul_eq_mul_left ha hprod

theorem signed_kernel_product_magnitudes {u v u' v' : ℤ} (hu : u ≠ 0)
    (huv' : u.natAbs.Coprime v'.natAbs) (hu'v : u'.natAbs.Coprime v.natAbs)
    (hprod : u * v = u' * v') : u.natAbs = u'.natAbs ∧ v.natAbs = v'.natAbs := by
  apply cross_coprime_factor_unique (Int.natAbs_pos.mpr hu) huv' hu'v
  simpa only [Int.natAbs_mul] using congrArg Int.natAbs hprod

/-- For any fixed signed product there are at most two pairs from two
nonzero kernel families with disjoint prime supports. -/
theorem kernel_product_fiber_card_le_two (A B : Finset ℤ) (d : ℤ)
    (hA : ∀ u ∈ A, u ≠ 0)
    (hAB : ∀ u ∈ A, ∀ v ∈ B, u.natAbs.Coprime v.natAbs) :
    Fintype.card {z : A × B // (z.1 : ℤ) * (z.2 : ℤ) = d} ≤ 2 := by
  let F := {z : A × B // (z.1 : ℤ) * (z.2 : ℤ) = d}
  let sign : F → Bool := fun z => decide (0 ≤ (z.1.1 : ℤ))
  have hinj : Function.Injective sign := by
    intro z w hsign
    have hu := hA z.1.1 z.1.1.property
    have hprod : (z.1.1 : ℤ) * (z.1.2 : ℤ) = (w.1.1 : ℤ) * (w.1.2 : ℤ) :=
      z.2.trans w.2.symm
    have habs := (signed_kernel_product_magnitudes hu
      (hAB z.1.1 z.1.1.property w.1.2 w.1.2.property)
      (hAB w.1.1 w.1.1.property z.1.2 z.1.2.property) hprod).1
    have heq : (z.1.1 : ℤ) = (w.1.1 : ℤ) := by
      by_cases hz : 0 ≤ (z.1.1 : ℤ) <;> by_cases hw : 0 ≤ (w.1.1 : ℤ)
      · exact (Int.natAbs_inj_of_nonneg_of_nonneg hz hw).mp habs
      · simp [sign, hz, hw] at hsign
      · simp [sign, hz, hw] at hsign
      · exact (Int.natAbs_inj_of_nonpos_of_nonpos (le_of_not_ge hz) (le_of_not_ge hw)).mp habs
    have heq' : (z.1.2 : ℤ) = (w.1.2 : ℤ) := by
      rw [← heq] at hprod
      exact mul_left_cancel₀ hu hprod
    apply Subtype.ext
    exact Prod.ext (Subtype.ext heq) (Subtype.ext heq')
  exact (Fintype.card_le_of_injective sign hinj).trans_eq Fintype.card_bool

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_KernelPopulationBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The congruence-refined population bound for a fixed signed kernel -/

namespace Ostmann

open scoped Classical

theorem kernel_population_residue_bound (S : Finset ℤ) (root : ℤ → ℕ)
    (m D : ℕ) (hm : 0 < m) (h u : ℤ) (hu : u ≠ 0) (hred : h.natAbs.Coprime m)
    (X : ℝ) (hroot : ∀ x ∈ S, u * (root x : ℤ) ^ 2 = (m : ℤ) * x - h)
    (hspan : ∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ X)
    (hD : Real.sqrt ((m : ℝ) * X / |(u : ℝ)|) ≤ D) :
    (S.card : ℝ) ≤ (2 : ℝ) ^ (m.primeFactors.card + 1) * ((D : ℝ) / m + 2) := by
  let : NeZero m := ⟨hm.ne'⟩
  have hcount := nat_residue_population_card_le (kernelRootPopulation S root) m D hm
    (kernelRootPopulation_diameter S root m D h u hu X hroot hspan hD)
  have hres : (((kernelRootPopulation S root).image (fun t : ℕ => (t : ZMod m))).card : ℝ) ≤
      (2 : ℝ) ^ (m.primeFactors.card + 1) := by
    exact_mod_cast kernel_root_residues_card_le S root m h u hred hroot
  rw [kernelRootPopulation_card S root m hm h u hroot] at hcount
  exact hcount.trans (mul_le_mul_of_nonneg_right hres (by positivity))

theorem kernel_population_real_bound (S : Finset ℤ) (root : ℤ → ℕ)
    (m : ℕ) (hm : 0 < m) (h u : ℤ) (hu : u ≠ 0) (hred : h.natAbs.Coprime m)
    (X : ℝ) (hroot : ∀ x ∈ S, u * (root x : ℤ) ^ 2 = (m : ℤ) * x - h)
    (hspan : ∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ X) :
    (S.card : ℝ) ≤ (2 : ℝ) ^ (m.primeFactors.card + 1) *
      (Real.sqrt ((m : ℝ) * X / |(u : ℝ)|) / m + 3) := by
  let R := Real.sqrt ((m : ℝ) * X / |(u : ℝ)|)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hb := kernel_population_residue_bound S root m ⌈R⌉₊ hm h u hu hred X hroot hspan
    (Nat.le_ceil R)
  have hceil : (⌈R⌉₊ : ℝ) ≤ R + 1 := (Nat.ceil_lt_add_one hR).le
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hdiv : (⌈R⌉₊ : ℝ) / m + 2 ≤ R / m + 3 := by
    have he := div_le_div_of_nonneg_right hceil (Nat.cast_nonneg m)
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hunit : (1 : ℝ) / m ≤ 1 := (div_le_one hm0).mpr hm1
    rw [add_div] at he
    linarith
  exact hb.trans (mul_le_mul_of_nonneg_left hdiv (by positivity))

private theorem sqrt_modulus_cancel (m X v : ℝ) (hm : 0 < m) :
    Real.sqrt m * (Real.sqrt (m * X / v) / m) = Real.sqrt (X / v) := by
  have heq : m * X / v = m * (X / v) := by ring
  rw [heq, Real.sqrt_mul hm.le]
  calc
    _ = (Real.sqrt m ^ 2 / m) * Real.sqrt (X / v) := by ring
    _ = _ := by rw [Real.sq_sqrt hm.le, div_self hm.ne', one_mul]

/-- The denominator loss is absorbed into an absolute constant. The remaining
sqrt(m) term is subpower for the common centers constructed in the application. -/
theorem exists_kernel_population_uniform_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℤ) (root : ℤ → ℕ) (m : ℕ) (h u : ℤ) (X : ℝ),
      0 < m → u ≠ 0 → h.natAbs.Coprime m →
      (∀ x ∈ S, u * (root x : ℤ) ^ 2 = (m : ℤ) * x - h) →
      (∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ X) →
      (S.card : ℝ) ≤ C * (Real.sqrt (X / |(u : ℝ)|) + Real.sqrt m) := by
  obtain ⟨C, hC, hgrowth⟩ := exists_unit_residue_sqrt_bound
  refine ⟨3 * C, by positivity, ?_⟩
  intro S root m h u X hm hu hred hroot hspan
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hb := kernel_population_real_bound S root m hm h u hu hred X hroot hspan
  have hg := hgrowth m hm.ne'
  have hn : 0 ≤ Real.sqrt ((m : ℝ) * X / |(u : ℝ)|) / m + 3 := by positivity
  apply hb.trans
  calc
    _ ≤ (C * Real.sqrt m) * (Real.sqrt ((m : ℝ) * X / |(u : ℝ)|) / m + 3) :=
      mul_le_mul_of_nonneg_right hg hn
    _ = C * (Real.sqrt (X / |(u : ℝ)|) + 3 * Real.sqrt m) := by
      rw [mul_add]
      have hs := sqrt_modulus_cancel (m : ℝ) X |(u : ℝ)| hmR
      calc
        _ = C * (Real.sqrt m * (Real.sqrt ((m : ℝ) * X / |(u : ℝ)|) / m)) +
            3 * C * Real.sqrt m := by ring
        _ = _ := by rw [hs]; ring
    _ ≤ _ := by nlinarith [Real.sqrt_nonneg (X / |(u : ℝ)|)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_KernelPairPopulationBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The population product estimate for a prescribed kernel product -/

namespace Ostmann

theorem root_population_product_bound (X m a b C : ℝ)
    (hX : 0 ≤ X) (hm : 0 ≤ m) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (C * (Real.sqrt (X / a) + Real.sqrt m)) *
      (C * (Real.sqrt (X / b) + Real.sqrt m)) ≤
      C ^ 2 * (X / Real.sqrt (a * b) + 2 * Real.sqrt (X * m) + m) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hroota : Real.sqrt (X / a) ≤ Real.sqrt X :=
    Real.sqrt_le_sqrt ((div_le_self hX ha).trans le_rfl)
  have hrootb : Real.sqrt (X / b) ≤ Real.sqrt X :=
    Real.sqrt_le_sqrt (div_le_self hX hb)
  have hab : Real.sqrt (X / a) * Real.sqrt (X / b) = X / Real.sqrt (a * b) := by
    rw [Real.sqrt_div hX, Real.sqrt_div hX, div_mul_div_comm,
      Real.mul_self_sqrt hX, ← Real.sqrt_mul ha0.le]
  have hm2 := Real.sq_sqrt hm
  have hac := mul_le_mul_of_nonneg_right hroota (Real.sqrt_nonneg m)
  have hbc := mul_le_mul_of_nonneg_right hrootb (Real.sqrt_nonneg m)
  have hinside : (Real.sqrt (X / a) + Real.sqrt m) *
      (Real.sqrt (X / b) + Real.sqrt m) ≤
        X / Real.sqrt (a * b) + 2 * Real.sqrt (X * m) + m := by
    rw [Real.sqrt_mul hX]
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hinside (sq_nonneg C)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_PairPopulationFibers
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact pair counting by the two population labels -/

namespace Ostmann

open scoped BigOperators Classical

theorem filteredPair_card {A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (f : A → C) (g : B → D) (R : C → D → Prop) :
    Fintype.card {z : A × B // R (f z.1) (g z.2)} =
      ∑ q : {z : C × D // R z.1 z.2},
        Fintype.card {x : A // f x = q.1.1} * Fintype.card {y : B // g y = q.1.2} := by
  rw [Fintype.card_congr (filteredPairFiberEquiv f g R), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro q _
  exact Fintype.card_prod _ _

theorem filteredPair_card_le {A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (f : A → C) (g : B → D) (R : C → D → Prop) (K H : ℝ)
    (hK : 0 ≤ K)
    (hlabels : (Fintype.card {z : C × D // R z.1 z.2} : ℝ) ≤ H)
    (hpop : ∀ q : {z : C × D // R z.1 z.2},
      (Fintype.card {x : A // f x = q.1.1} : ℝ) *
        Fintype.card {y : B // g y = q.1.2} ≤ K) :
    (Fintype.card {z : A × B // R (f z.1) (g z.2)} : ℝ) ≤ H * K := by
  rw [filteredPair_card f g R, Nat.cast_sum]
  calc
    _ ≤ ∑ _q : {z : C × D // R z.1 z.2}, K := by
      apply Finset.sum_le_sum
      intro q _
      simpa only [Nat.cast_mul] using hpop q
    _ = (Fintype.card {z : C × D // R z.1 z.2} : ℝ) * K := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hlabels hK

theorem finset_fiber_card {A B : Type*} [DecidableEq A] [DecidableEq B]
    (S : Finset A) (f : A → B) (b : B) :
    Fintype.card {x : S // f x = b} = (S.filter fun x => f x = b).card := by
  simpa only [Fintype.card_coe] using Fintype.card_congr (finsetFiberEquiv S f b)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_EndpointKernelPairCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Endpoint-pair counts for a fixed product of disjoint kernels -/

namespace Ostmann

open scoped Classical

theorem endpoint_kernel_product_count (S T : Finset ℤ) (f g : ℤ → ℤ) (d : ℤ)
    (hS : ∀ x ∈ S, f x ≠ 0)
    (hcross : ∀ x ∈ S, ∀ y ∈ T, (f x).natAbs.Coprime (g y).natAbs)
    (K : ℝ) (hK : 0 ≤ K)
    (hpop : ∀ u ∈ S.image f, ∀ v ∈ T.image g, u * v = d →
      ((S.filter fun x => f x = u).card : ℝ) * (T.filter fun y => g y = v).card ≤ K) :
    (Fintype.card {z : S × T // f z.1 * g z.2 = d} : ℝ) ≤ 2 * K := by
  let A := S.image f
  let B := T.image g
  let F : S → A := fun x => ⟨f x, Finset.mem_image.mpr ⟨x, x.property, rfl⟩⟩
  let G : T → B := fun y => ⟨g y, Finset.mem_image.mpr ⟨y, y.property, rfl⟩⟩
  have hA (u : ℤ) (hu : u ∈ A) : u ≠ 0 := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    exact hS x hx
  have hAB (u : ℤ) (hu : u ∈ A) (v : ℤ) (hv : v ∈ B) : u.natAbs.Coprime v.natAbs := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
    exact hcross x hx y hy
  have hlabels : (Fintype.card {z : A × B // (z.1 : ℤ) * (z.2 : ℤ) = d} : ℝ) ≤ 2 := by
    exact_mod_cast kernel_product_fiber_card_le_two A B d hA hAB
  have hpops (q : {z : A × B // (z.1 : ℤ) * (z.2 : ℤ) = d}) :
      (Fintype.card {x : S // F x = q.1.1} : ℝ) * Fintype.card {y : T // G y = q.1.2} ≤ K := by
    have eF : {x : S // F x = q.1.1} ≃ {x : S // f x = (q.1.1 : ℤ)} :=
      Equiv.subtypeEquivRight (fun _ => Subtype.ext_iff)
    have eG : {y : T // G y = q.1.2} ≃ {y : T // g y = (q.1.2 : ℤ)} :=
      Equiv.subtypeEquivRight (fun _ => Subtype.ext_iff)
    rw [Fintype.card_congr eF, Fintype.card_congr eG]
    have hF := finset_fiber_card S f (q.1.1 : ℤ)
    have hG := finset_fiber_card T g (q.1.2 : ℤ)
    simp only [Fintype.card_eq_nat_card] at hF hG ⊢
    rw [hF, hG]
    exact hpop q.1.1 q.1.1.property q.1.2 q.1.2.property q.2
  have hb := filteredPair_card_le F G (fun u v => (u : ℤ) * (v : ℤ) = d) K 2 hK
    (by simpa only [Fintype.card_eq_nat_card] using hlabels)
    (by simpa only [Fintype.card_eq_nat_card] using hpops)
  simpa only [Fintype.card_eq_nat_card] using hb

/-- The exceptional signed product accounts for few endpoint pairs. The bound
is uniform over the two finite endpoint sets and their affine square roots. -/
theorem exists_endpoint_kernel_product_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (S T : Finset ℤ) (f g : ℤ → ℤ)
      (r s : ℤ → ℕ) (m : ℕ) (h d : ℤ) (X : ℝ),
      0 < m → 0 ≤ X →
      (∀ x ∈ S, f x ≠ 0) → (∀ y ∈ T, g y ≠ 0) →
      h.natAbs.Coprime m →
      (∀ x ∈ S, f x * (r x : ℤ) ^ 2 = (m : ℤ) * x - h) →
      (∀ y ∈ T, g y * (s y : ℤ) ^ 2 = (m : ℤ) * y - h) →
      (∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ X) →
      (∀ x ∈ T, ∀ y ∈ T, |((x - y : ℤ) : ℝ)| ≤ X) →
      (∀ x ∈ S, ∀ y ∈ T, (f x).natAbs.Coprime (g y).natAbs) →
      (Fintype.card {z : S × T // f z.1 * g z.2 = d} : ℝ) ≤
        C * (X / Real.sqrt |(d : ℝ)| + 2 * Real.sqrt (X * m) + m) := by
  obtain ⟨C, hC, hpop⟩ := exists_kernel_population_uniform_bound
  refine ⟨2 * C ^ 2, by positivity, ?_⟩
  intro S T f g r s m h d X hm hX hf hg hred hr hs hspanS hspanT hcross
  let K := C ^ 2 * (X / Real.sqrt |(d : ℝ)| + 2 * Real.sqrt (X * m) + m)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hb := endpoint_kernel_product_count S T f g d hf hcross K hK (by
    intro u hu v hv huv
    obtain ⟨x, hx, hxu⟩ := Finset.mem_image.mp hu
    obtain ⟨y, hy, hyv⟩ := Finset.mem_image.mp hv
    have hu0 : u ≠ 0 := hxu ▸ hf x hx
    have hv0 : v ≠ 0 := hyv ▸ hg y hy
    have hau : (1 : ℝ) ≤ |(u : ℝ)| := by
      have hn : 1 ≤ u.natAbs := Int.natAbs_pos.mpr hu0
      have hh : (1 : ℝ) ≤ u.natAbs := by exact_mod_cast hn
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hh
    have hav : (1 : ℝ) ≤ |(v : ℝ)| := by
      have hn : 1 ≤ v.natAbs := Int.natAbs_pos.mpr hv0
      have hh : (1 : ℝ) ≤ v.natAbs := by exact_mod_cast hn
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hh
    have hS := hpop (S.filter fun x => f x = u) r m h u X hm hu0 hred
      (by intro x hx; obtain ⟨hx, he⟩ := Finset.mem_filter.mp hx; rw [← he]; exact hr x hx)
      (by intro x hx y hy; exact hspanS x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1)
    have hT := hpop (T.filter fun y => g y = v) s m h v X hm hv0 hred
      (by intro y hy; obtain ⟨hy, he⟩ := Finset.mem_filter.mp hy; rw [← he]; exact hs y hy)
      (by intro x hx y hy; exact hspanT x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1)
    have hprod : |(u : ℝ)| * |(v : ℝ)| = |(d : ℝ)| := by
      rw [← abs_mul, ← Int.cast_mul, huv]
    calc
      _ ≤ (C * (Real.sqrt (X / |(u : ℝ)|) + Real.sqrt m)) *
          (C * (Real.sqrt (X / |(v : ℝ)|) + Real.sqrt m)) :=
        mul_le_mul hS hT (Nat.cast_nonneg _) (by positivity)
      _ ≤ C ^ 2 * (X / Real.sqrt (|(u : ℝ)| * |(v : ℝ)|) +
          2 * Real.sqrt (X * m) + m) :=
        root_population_product_bound X m |(u : ℝ)| |(v : ℝ)| C hX (Nat.cast_nonneg _) hau hav
      _ = K := by rw [hprod])
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [K]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_KernelPairSelection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting populated kernels after removal of an exceptional product -/

namespace Ostmann

open scoped BigOperators Classical

/-- The finite-set count and the subtype count use exactly the same pairs. -/
theorem kernel_pair_filter_card (S T : Finset ℤ) (f g : ℤ → ℤ) (d : ℤ) :
    ((S.product T).filter fun z => f z.1 * g z.2 = d).card =
      Fintype.card {z : S × T // f z.1 * g z.2 = d} := by
  let e : {z : S × T // f z.1 * g z.2 = d} ≃
      {z : ℤ × ℤ // z ∈ (S.product T).filter fun z => f z.1 * g z.2 = d} :=
    { toFun := fun z => ⟨(z.1.1, z.1.2), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨z.1.1.property, z.1.2.property⟩, z.2⟩⟩
      invFun := fun z => ⟨(⟨z.1.1, (Finset.mem_product.mp (Finset.mem_filter.mp z.2).1).1⟩,
        ⟨z.1.2, (Finset.mem_product.mp (Finset.mem_filter.mp z.2).1).2⟩),
          (Finset.mem_filter.mp z.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa only [Fintype.card_coe] using (Fintype.card_congr e).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_FiniteKernelExclusion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing a finite family of exceptional signed kernel products -/

namespace Ostmann

open scoped BigOperators Classical

theorem kernel_pair_filter_mem_card (S T : Finset ℤ) (f g : ℤ → ℤ) (D : Finset ℤ) :
    ((S.product T).filter fun z => f z.1 * g z.2 ∈ D).card =
      ∑ d ∈ D, ((S.product T).filter fun z => f z.1 * g z.2 = d).card := by
  let U := (S.product T).filter fun z => f z.1 * g z.2 ∈ D
  have hm : (U : Set (ℤ × ℤ)).MapsTo (fun z => f z.1 * g z.2) D :=
    fun _ hz => (Finset.mem_filter.mp hz).2
  rw [Finset.card_eq_sum_card_fiberwise hm]
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  ext z
  simp only [U, Finset.mem_filter]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · exact fun h => ⟨⟨h.1, h.2 ▸ hd⟩, h.2⟩

theorem kernel_pair_finite_exclusion_bound (S T : Finset ℤ) (f g : ℤ → ℤ)
    (D : Finset ℤ) (E : ℝ)
    (hE : ∀ d ∈ D, (((S.product T).filter fun z => f z.1 * g z.2 = d).card : ℝ) ≤ E) :
    (((S.product T).filter fun z => f z.1 * g z.2 ∈ D).card : ℝ) ≤ D.card * E := by
  rw [kernel_pair_filter_mem_card, Nat.cast_sum]
  exact (Finset.sum_le_sum hE).trans_eq (by simp)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_KernelDiscardBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The refined large-kernel discard estimate -/

namespace Ostmann

open scoped BigOperators Classical

/-- This is the population estimate used to discard kernels larger than H.
The denominator m occurs only through sqrt(m), uniformly over all kernels. -/
theorem exists_large_kernel_discard_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℤ) (f : ℤ → ℤ) (root : ℤ → ℕ)
      (m : ℕ) (h : ℤ) (X H : ℝ), 0 < m → 0 ≤ X → 0 < H →
      h.natAbs.Coprime m →
      (∀ x ∈ S, f x * (root x : ℤ) ^ 2 = (m : ℤ) * x - h) →
      (∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ X) →
      ((S.filter fun x => H < |(f x : ℝ)|).card : ℝ) ≤
        (S.image f).card * (C * (Real.sqrt (X / H) + Real.sqrt m)) := by
  obtain ⟨C, hC, hpop⟩ := exists_kernel_population_uniform_bound
  refine ⟨C, hC, ?_⟩
  intro S f root m h X H hm hX hH hred hroot hspan
  let R := S.filter fun x => H < |(f x : ℝ)|
  have hRS : R ⊆ S := Finset.filter_subset _ _
  have hfiber (u : ℤ) (hu : u ∈ R.image f) :
      ((R.filter fun x => f x = u).card : ℝ) ≤ C * (Real.sqrt (X / H) + Real.sqrt m) := by
    obtain ⟨x, hx, hxu⟩ := Finset.mem_image.mp hu
    have hlarge : H < |(u : ℝ)| := by
      have hh := (Finset.mem_filter.mp hx).2
      rwa [hxu] at hh
    have hu0 : u ≠ 0 := by
      intro hu0
      simp only [hu0, Int.cast_zero, abs_zero] at hlarge
      linarith
    have hb := hpop (R.filter fun x => f x = u) root m h u X hm hu0 hred
      (by
        intro y hy
        obtain ⟨hy, heq⟩ := Finset.mem_filter.mp hy
        simpa only [heq] using hroot y (hRS hy))
      (by
        intro y hy z hz
        exact hspan y (hRS (Finset.mem_filter.mp hy).1) z (hRS (Finset.mem_filter.mp hz).1))
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    exact add_le_add (Real.sqrt_le_sqrt
      (div_le_div_of_nonneg_left hX hH hlarge.le)) le_rfl
  have hc : (R.card : ℝ) ≤ (R.image f).card *
      (C * (Real.sqrt (X / H) + Real.sqrt m)) := by
    rw [Finset.card_eq_sum_card_image f R, Nat.cast_sum]
    simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul (R.image f)
      (fun u => ((R.filter fun x => f x = u).card : ℝ)) _ hfiber
  apply hc.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (Finset.image_subset_image hRS)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_LargeKernelPopulationDecay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The high-kernel population is negligible at the original endpoint scale -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem eventual_large_kernel_population_decay (η ε a : ℝ)
    (hη : 0 < η) (hηU : η ≤ 1 / 1000) (_hε : 0 ≤ ε) (hεη : ε ≤ η / 100)
    (ha : 0 < a) :
    ∀ᶠ L : ℝ in atTop, ∀ (S : Finset ℤ) (f : ℤ → ℤ) (root : ℤ → ℕ)
      (m : ℕ) (h : ℤ),
      0 < m → (m : ℝ) ≤ Real.exp (η * L) → h.natAbs.Coprime m →
      ((S.image f).card : ℝ) ≤ Real.exp (3 * ε * L) →
      (∀ x ∈ S, f x * (root x : ℤ) ^ 2 = (m : ℤ) * x - h) →
      (∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ Real.exp L) →
      ((S.filter fun x => Real.exp (η * L) < |(f x : ℝ)|).card : ℝ) ≤
        a * Real.exp (L / 2) / L ^ 6 := by
  obtain ⟨C, hC, hbound⟩ := exists_large_kernel_discard_bound
  have hp := ((isLittleO_pow_exp_pos_mul_atTop 6 (show 0 < η / 4 by positivity)).const_mul_left
    (2 * C / a)).bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hp, eventually_ge_atTop (1 : ℝ)] with L hpoly hL S f root m h hm hmU hred hcount hroot hspan
  have hLpos : 0 < L := by linarith
  have hb := hbound S f root m h (Real.exp L) (Real.exp (η * L)) hm
    (Real.exp_nonneg _) (Real.exp_pos _) hred hroot hspan
  have hmain : Real.sqrt (Real.exp L / Real.exp (η * L)) = Real.exp ((1 - η) * L / 2) := by
    rw [← Real.exp_sub]
    have he : Real.exp (L - η * L) = (Real.exp ((1 - η) * L / 2)) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; norm_num; ring
    rw [he, Real.sqrt_sq (Real.exp_nonneg _)]
  have hmroot : Real.sqrt (m : ℝ) ≤ Real.exp (η * L / 2) := by
    have hh := Real.sqrt_le_sqrt hmU
    have he : Real.exp (η * L) = (Real.exp (η * L / 2)) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; norm_num; ring
    rwa [he, Real.sqrt_sq (Real.exp_nonneg _)] at hh
  have hfirst : Real.exp (3 * ε * L) * Real.exp ((1 - η) * L / 2) ≤
      Real.exp ((1 / 2 - η / 4) * L) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (show 0 ≤ η / 100 - ε by linarith) hLpos.le]
  have hsecond : Real.exp (3 * ε * L) * Real.exp (η * L / 2) ≤
      Real.exp ((1 / 2 - η / 4) * L) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh : 3 * ε + η / 2 ≤ 1 / 2 - η / 4 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hh hLpos.le]
  have hdecay : 2 * C * Real.exp ((1 / 2 - η / 4) * L) ≤ a * Real.exp (L / 2) / L ^ 6 := by
    have hp' : (2 * C / a) * L ^ 6 ≤ Real.exp (η / 4 * L) := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (2 * C / a) * L ^ 6),
        abs_of_pos (Real.exp_pos _), one_mul] using hpoly
    apply (le_div_iff₀ (pow_pos hLpos 6)).mpr
    have hp'' : 2 * C * L ^ 6 ≤ a * Real.exp (η / 4 * L) := by
      have hh : (2 * C * L ^ 6) / a ≤ Real.exp (η / 4 * L) := by
        simpa only [div_mul_eq_mul_div] using hp'
      nlinarith only [(div_le_iff₀ ha).mp hh]
    have hx := mul_le_mul_of_nonneg_right hp'' (Real.exp_nonneg ((1 / 2 - η / 4) * L))
    have he : Real.exp (η / 4 * L) * Real.exp ((1 / 2 - η / 4) * L) = Real.exp (L / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    calc
      _ = (2 * C * L ^ 6) * Real.exp ((1 / 2 - η / 4) * L) := by ring
      _ ≤ (a * Real.exp (η / 4 * L)) * Real.exp ((1 / 2 - η / 4) * L) := hx
      _ = _ := by rw [mul_assoc, he]
  calc
    _ ≤ (S.image f).card * (C * (Real.sqrt (Real.exp L / Real.exp (η * L)) + Real.sqrt m)) := hb
    _ ≤ Real.exp (3 * ε * L) * (C * (Real.exp ((1 - η) * L / 2) + Real.exp (η * L / 2))) := by
      rw [hmain]
      exact mul_le_mul hcount (mul_le_mul_of_nonneg_left (add_le_add le_rfl hmroot) hC.le)
        (by positivity) (by positivity)
    _ ≤ 2 * C * Real.exp ((1 / 2 - η / 4) * L) := by
      have hh₁ := mul_le_mul_of_nonneg_left hfirst hC.le
      have hh₂ := mul_le_mul_of_nonneg_left hsecond hC.le
      nlinarith only [hh₁, hh₂]
    _ ≤ _ := hdecay

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_PopulatedKernelSelection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining entire populated kernel fibers -/

namespace Ostmann

open scoped BigOperators Classical

/-- Fibers smaller than the cutoff remove at most the number of kernels times
that cutoff. The estimate concerns actual endpoint populations. -/
theorem small_kernel_fibers_card (S : Finset ℤ) (f : ℤ → ℤ) (Q : ℕ) :
    (S.filter fun x => (S.filter fun y => f y = f x).card < Q).card ≤
      (S.image f).card * Q := by
  let R := S.filter fun x => (S.filter fun y => f y = f x).card < Q
  have hsub : R ⊆ S := Finset.filter_subset _ _
  have hf (u : ℤ) (hu : u ∈ R.image f) :
      (R.filter fun x => f x = u).card ≤ Q := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    exact (Finset.card_le_card (Finset.filter_subset_filter _ hsub)).trans
      (Nat.le_of_lt (Finset.mem_filter.mp hx).2)
  calc
    R.card = ∑ u ∈ R.image f, (R.filter fun x => f x = u).card :=
      Finset.card_eq_sum_card_image f R
    _ ≤ ∑ _u ∈ R.image f, Q := Finset.sum_le_sum hf
    _ = (R.image f).card * Q := by simp
    _ ≤ (S.image f).card * Q := Nat.mul_le_mul_right Q
      (Finset.card_le_card (Finset.image_subset_image hsub))

theorem populatedKernelPoints_subset (S : Finset ℤ) (f : ℤ → ℤ) (A : ℤ → Prop)
    [DecidablePred A] (Q : ℕ) : populatedKernelPoints S f A Q ⊆ S :=
  Finset.filter_subset _ _

theorem populatedKernelPoints_fiber (S : Finset ℤ) (f : ℤ → ℤ) (A : ℤ → Prop)
    [DecidablePred A] (Q : ℕ) {u : ℤ} (hu : u ∈ (populatedKernelPoints S f A Q).image f) :
    A u ∧ Q ≤ (S.filter fun y => f y = u).card ∧
      ((populatedKernelPoints S f A Q).filter fun y => f y = u) =
        (S.filter fun y => f y = u) := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨hxS, ha, hq⟩ := Finset.mem_filter.mp hx
  refine ⟨ha, hq, ?_⟩
  ext y
  simp only [populatedKernelPoints, Finset.mem_filter]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · rintro ⟨hy, heq⟩
    exact ⟨⟨hy, by simpa only [heq] using ha, by simpa only [heq] using hq⟩, heq⟩

/-- A strict population surplus supplies an actual nonexceptional endpoint pair. -/
theorem exists_nonexceptional_endpoint_pair (S T : Finset ℤ) (f g : ℤ → ℤ)
    (E : ℤ → Prop) [DecidablePred E] (M : ℝ)
    (hbad : (((S.product T).filter fun z => E (f z.1 * g z.2)).card : ℝ) ≤ M)
    (hlarge : M < (S.card : ℝ) * T.card) :
    ∃ x ∈ S, ∃ y ∈ T, ¬ E (f x * g y) := by
  by_contra! hn
  have heq : (S.product T).filter (fun z => E (f z.1 * g z.2)) = S.product T := by
    apply Finset.filter_true_of_mem
    intro z hz
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hz
    exact hn z.1 hx z.2 hy
  rw [heq, Finset.product_eq_sprod, Finset.card_product, Nat.cast_mul] at hbad
  exact (not_lt_of_ge hbad) hlarge

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_HadamardPrimeBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Deriving signed prime-mass bounds from the published zero expansion -/

namespace Ostmann

open scoped BigOperators

theorem realCharacterZeroExpansion_anchor {χ : PrimitiveRealCharacter} {C : ℝ}
    (Z : RealCharacterZeroExpansion χ C) (s₀ L A : ℝ)
    (hs : 1 < s₀) (hs2 : s₀ ≤ 2) (hlog : Real.log χ.modulus ≤ L)
    (hderiv : χ.logDerivative s₀ ≤ L + A) (herror : A + C ≤ L / 2) :
    (∑' i, realZeroKernel (s₀ - (Z.zeros i).re) (Z.zeros i).im) ≤ 2 * L := by
  have hh := (abs_le.mp (Z.hadamard s₀ hs hs2)).2
  linarith

/-- The bounded Euler prime-power error has already been proved. Only the
Hadamard expansion remains an input to this implication. -/
theorem exists_signed_prime_lower_of_zero_sum :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (χ : PrimitiveRealCharacter) (C : ℝ)
      (Z : RealCharacterZeroExpansion χ C) (s B : ℝ), 1 < s → s ≤ 2 →
      (∑' i, realZeroKernel (s - (Z.zeros i).re) (Z.zeros i).im) ≤ B →
      -B - C - A ≤ ∑' n, realPrimeTerm χ.character s n := by
  obtain ⟨A, hA, heuler⟩ := exists_realPrimeSeries_error
  refine ⟨A, hA, ?_⟩
  intro χ C Z s B hs hs2 hzeros
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have he := (heuler χ.modulus χ.character s hs).2
  change |(∑' n, realPrimeTerm χ.character s n) + χ.logDerivative s| ≤ A at he
  have hh := (abs_le.mp (Z.hadamard s hs hs2)).1
  have hlog : 0 ≤ Real.log (χ.modulus : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast χ.positive
  have he' := (abs_le.mp he).1
  linarith

/-- Actual real exceptions in a finite zero family cost at most one Siegel
term when the region has at most one exceptional zero. -/
theorem exceptional_zero_sum_bound (hSiegel : PublishedSiegelBound)
    (ε : ℝ) (hε : 0 < ε) : ∃ K : ℝ, 0 < K ∧
    ∀ (χ : PrimitiveRealCharacter) (C : ℝ) (Z : RealCharacterZeroExpansion χ C)
      (E : Finset ℕ) (s : ℝ), E.card ≤ 1 → 1 < s →
      (∀ i ∈ E, (Z.zeros i).im = 0) →
      (∑ i ∈ E, (s - (Z.zeros i).re)⁻¹) ≤ K * (χ.modulus : ℝ) ^ ε := by
  obtain ⟨K, hK, hbound⟩ := hSiegel ε hε
  refine ⟨K, hK, ?_⟩
  intro χ C Z E s hE hs hreal
  have hf (i : ℕ) (hi : i ∈ E) : (s - (Z.zeros i).re)⁻¹ ≤ K * (χ.modulus : ℝ) ^ ε := by
    have hβ := (Z.in_strip i).2
    have he := hbound (Z.realZero i (hreal i hi))
    change (1 - (Z.zeros i).re)⁻¹ ≤ K * (χ.modulus : ℝ) ^ ε at he
    have hinv : (s - (Z.zeros i).re)⁻¹ ≤ (1 - (Z.zeros i).re)⁻¹ :=
      inv_anti₀ (by linarith) (by linarith)
    exact hinv.trans he
  calc
    _ ≤ (E.card : ℝ) * (K * (χ.modulus : ℝ) ^ ε) := by
      simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul E _ _ hf
    _ ≤ K * (χ.modulus : ℝ) ^ ε := by
      have hER : (E.card : ℝ) ≤ 1 := by exact_mod_cast hE
      have hnn : 0 ≤ K * (χ.modulus : ℝ) ^ ε := by positivity
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hER hnn

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PageSelection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single exceptional character for every modulus in a row

Only zeros in Page's common region are retained. Local exceptional zeros
outside that region will be bounded as an error, rather than identified
with a character belonging to a different modulus.
-/

namespace Ostmann

open Classical

theorem selectedPageZero_eq (P : PublishedProgressionInput) (Q : ℕ)
    (hQ : 2 ≤ Q) (e : PrimitiveRealZero) (hmod : e.modulus ≤ Q)
    (hnear : 1 - P.kappa / Real.log (4 * (Q : ℝ)) ≤ e.beta) :
    selectedPageZero P Q = some e := by
  have hex : ∃ f : PrimitiveRealZero, f.modulus ≤ Q ∧
      1 - P.kappa / Real.log (4 * (Q : ℝ)) ≤ f.beta := ⟨e, hmod, hnear⟩
  have heq := P.unique Q hQ hex.choose e hex.choose_spec.1 hmod hex.choose_spec.2 hnear
  unfold selectedPageZero
  rw [dite_eq_left hex, heq]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RetainedCharacterPrimeBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Signed prime mass for a retained primitive real character -/

namespace Ostmann

open scoped BigOperators Classical

/-- The only possible loss beyond the zero-free bound is a Siegel term for
the one retained Page character. The Euler and prime-power steps are proved. -/
theorem retained_character_prime_lower (P : PublishedProgressionInput)
    (H : PublishedRealZeroInput P) (hSiegel : PublishedSiegelBound)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A K : ℝ, 0 < A ∧ 0 < K ∧
      ∀ (χ : PrimitiveRealCharacter) (Q : ℕ) (R s : ℝ),
        2 ≤ Q → χ.modulus ≤ Q → 0 ≤ R →
        2 * (A + H.errorConstant) ≤ Real.log (4 * (Q : ℝ)) →
        1 < s → s ≤ 1 + 1 / Real.log (4 * (Q : ℝ)) →
        (∀ e : PrimitiveRealZero, selectedPageZero P Q = some e →
          samePrimitiveRealCharacter e χ → (e.modulus : ℝ) ≤ R) →
        -2 * zeroComparisonConstant P * Real.log (4 * (Q : ℝ)) -
            K * R ^ ε - H.errorConstant - A ≤ ∑' n, realPrimeTerm χ.character s n := by
  obtain ⟨Ad, hAd, hderiv⟩ := exists_dirichlet_logDerivative_bound
  obtain ⟨Ap, hAp, hprime⟩ := exists_signed_prime_lower_of_zero_sum
  obtain ⟨K, hK, hEbound⟩ := exceptional_zero_sum_bound hSiegel ε hε
  let A := Ad + Ap + 1
  refine ⟨A, K, by dsimp [A]; positivity, hK, ?_⟩
  intro χ Q R s hQ hχQ hR hsize hs hss hretain
  let L := Real.log (4 * (Q : ℝ))
  let s₀ := 1 + 1 / L
  let Z := H.expansion χ
  let Cz := zeroComparisonConstant P
  have hL1 : 1 ≤ L := by
    change 2 * (A + H.errorConstant) ≤ L at hsize
    dsimp [A] at hsize
    linarith [H.errorConstant_nonneg]
  have hL : 0 < L := by linarith
  have hs₀ : 1 < s₀ := by
    have hp : 0 < 1 / L := by positivity
    dsimp [s₀]
    linarith
  have hs₀2 : s₀ ≤ 2 := by
    have hdiv : 1 / L ≤ (1 : ℝ) := (div_le_one hL).mpr hL1
    dsimp [s₀]
    linarith
  have hss₀ : s ≤ s₀ := hss
  have hlog : Real.log (χ.modulus : ℝ) ≤ L := by
    apply Real.log_le_log (by exact_mod_cast χ.positive)
    have hmod : (χ.modulus : ℝ) ≤ Q := by exact_mod_cast hχQ
    linarith [show (0 : ℝ) ≤ Q from Nat.cast_nonneg Q]
  have hpole : 1 / (s₀ - 1) = L := by
    dsimp [s₀]
    field_simp
    ring
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have hd := hderiv χ.modulus χ.complexCharacter s₀ hs₀ hs₀2
  change ‖deriv χ.L (s₀ : ℂ) / χ.L (s₀ : ℂ)‖ ≤ _ at hd
  rw [hpole] at hd
  have hdl : χ.logDerivative s₀ ≤ L + Ad := (Complex.re_le_norm _).trans hd
  have hanchor : (∑' i, realZeroKernel (s₀ - (Z.zeros i).re) (Z.zeros i).im) ≤ 2 * L := by
    apply realCharacterZeroExpansion_anchor Z s₀ L Ad hs₀ hs₀2 hlog hdl
    change 2 * (A + H.errorConstant) ≤ L at hsize
    dsimp [A] at hsize
    linarith
  obtain ⟨E, hcard, hEin, hEout⟩ := H.region χ Q hQ hχQ
  have hexception : (∑ i ∈ E, (s - (Z.zeros i).re)⁻¹) ≤ K * R ^ ε := by
    by_cases hnon : E.Nonempty
    · obtain ⟨i, hi⟩ := hnon
      let e := Z.realZero i (hEin i hi).1
      have hsel : selectedPageZero P Q = some e :=
        selectedPageZero_eq P Q hQ e hχQ (hEin i hi).2
      have hechar : samePrimitiveRealCharacter e χ := ⟨rfl, fun _ => rfl⟩
      have hqR : (χ.modulus : ℝ) ≤ R := hretain e hsel hechar
      have he := hEbound χ H.errorConstant Z E s hcard hs (fun i hi => (hEin i hi).1)
      exact he.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hqR hε.le) hK.le)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hnon, Finset.sum_empty]
      positivity
  have hCz5 : 5 ≤ Cz := le_max_left _ _
  have hCzc : 1 + P.kappa⁻¹ ≤ Cz := le_max_right _ _
  have hCz : 0 ≤ Cz := by linarith
  have hcompare := (realZeroKernel_sum_bound Z.zeros E s s₀ P.kappa (1 / L) Cz
    (fun i => ⟨(Z.in_strip i).1.le, (Z.in_strip i).2⟩) hs hss₀ hs₀2 P.kappa_pos
    hCz5 hCzc (by dsimp [s₀]; linarith) (by
      intro i hi him
      have hz := hEout i hi him
      change (Z.zeros i).re ≤ 1 - P.kappa / L at hz
      have hh : P.kappa / L ≤ s - (Z.zeros i).re := by linarith
      simpa only [div_eq_mul_inv, one_mul] using hh)
    (Z.summable s₀ hs₀ hs₀2)).2
  have hzbound : (∑' i, realZeroKernel (s - (Z.zeros i).re) (Z.zeros i).im) ≤
      2 * Cz * L + K * R ^ ε := by
    have h := add_le_add (mul_le_mul_of_nonneg_left hanchor hCz) hexception
    nlinarith
  have hp := hprime χ H.errorConstant Z s (2 * Cz * L + K * R ^ ε) hs
    (hss₀.trans hs₀2) hzbound
  change -2 * Cz * L - K * R ^ ε - H.errorConstant - A ≤ _
  dsimp [A]
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_SignedKernelCharacter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A primitive character for each non-small signed squarefree kernel -/

namespace Ostmann

private theorem prime_character_zero (χ : PrimitiveRealCharacter) {p : ℕ}
    (hp : p.Prime) (hdiv : p ∣ χ.modulus) : χ.character p = 0 := by
  apply MulChar.map_nonunit
  intro hu
  have hc := (ZMod.isUnit_iff_coprime p χ.modulus).mp hu
  exact (hp.coprime_iff_not_dvd.mp hc) hdiv

private theorem prime_jacobi_zero (d : ℤ) {p : ℕ}
    (hp : p.Prime) (hdiv : p ∣ d.natAbs) : jacobiSym d p = 0 := by
  let : NeZero p := ⟨hp.ne_zero⟩
  apply jacobiSym.eq_zero_iff_not_coprime.mpr
  rw [Int.gcd_eq_natAbs]
  intro hc
  have hc' : d.natAbs.Coprime p := by simpa only [Int.natAbs_natCast] using hc
  exact (hp.coprime_iff_not_dvd.mp hc'.symm) hdiv

/-- Equality at coprime odd arguments extends to all odd primes because
both characters vanish at a prime factor of the odd kernel. -/
theorem kernel_prime_character_value (d : ℤ) (N : ℕ) (χ : PrimitiveRealCharacter)
    (hNq : N ∣ χ.modulus) (hNd : N ∣ d.natAbs)
    (hvalue : ∀ a : ℕ, Odd a → a.Coprime N → χ.character a = (jacobiSym d a : ℝ)) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → χ.character p = (jacobiSym d p : ℝ) := by
  intro p hp hp2
  by_cases hdiv : p ∣ N
  · rw [prime_character_zero χ hp (hdiv.trans hNq),
      prime_jacobi_zero d hp (hdiv.trans hNd), Int.cast_zero]
  · exact hvalue p (hp.odd_of_ne_two hp2) (hp.coprime_iff_not_dvd.mpr hdiv)

/-- The auxiliary N is the odd part of the kernel. Its divisibility and
conductor bounds also give a finite list of possible kernels for a fixed
exceptional conductor. No character-classification result is assumed. -/
theorem exists_signed_kernel_character (d : ℤ) (hsf : Squarefree d.natAbs)
    (hd : 2 < d.natAbs) :
    ∃ (χ : PrimitiveRealCharacter) (N : ℕ),
      1 < N ∧ N ∣ χ.modulus ∧ χ.modulus ≤ 8 * N ∧
      (d.natAbs = N ∨ d.natAbs = 2 * N) ∧
      χ.modulus ≤ 4 * d.natAbs ∧ d.natAbs ≤ 2 * χ.modulus ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 → χ.character p = (jacobiSym d p : ℝ) := by
  have hd0 : d ≠ 0 := by intro h; simp [h] at hd
  have hmem : d ∈ signedSquarefreeRange d.natAbs := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ?_, hd0, hsf⟩
    simpa only [Int.natCast_natAbs] using abs_le.mp (le_refl |d|)
  obtain ⟨c, hc, N, hNmem, heq⟩ := signedSquarefreeRange_cover hmem
  have hNsf : Squarefree N := (Finset.mem_filter.mp hNmem).2.2
  have hNodd : Odd N := (Finset.mem_filter.mp hNmem).2.1
  simp only [quadraticSigns, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · have hdN : d = (N : ℤ) := by simpa using heq.symm
    have habs : d.natAbs = N := by simp [hdN]
    have hN : 1 < N := by omega
    obtain ⟨χ, hq, hbound, hv⟩ := exists_odd_kernel_primitive N hN hNsf hNodd false
    have hNle : N ≤ χ.modulus := Nat.le_of_dvd χ.positive hq
    refine ⟨χ, N, hN, hq, by omega, Or.inl habs, by omega, by omega, ?_⟩
    apply kernel_prime_character_value d N χ hq (by simp [habs])
    simpa only [Bool.false_eq_true, ite_false, if_false, ← hdN] using hv
  · have hdN : d = -(N : ℤ) := by simpa using heq.symm
    have habs : d.natAbs = N := by simp [hdN]
    have hN : 1 < N := by omega
    obtain ⟨χ, hq, hbound, hv⟩ := exists_odd_kernel_primitive N hN hNsf hNodd true
    have hNle : N ≤ χ.modulus := Nat.le_of_dvd χ.positive hq
    refine ⟨χ, N, hN, hq, by omega, Or.inl habs, by omega, by omega, ?_⟩
    apply kernel_prime_character_value d N χ hq (by simp [habs])
    simpa only [ite_true, if_true, ← hdN] using hv
  · have hdN : d = 2 * (N : ℤ) := heq.symm
    have habs : d.natAbs = 2 * N := by simp [hdN, Int.natAbs_mul]
    have hN : 1 < N := by omega
    obtain ⟨χ, hq, hbound, hv⟩ := exists_even_kernel_primitive N hN hNsf hNodd false
    have hNle : N ≤ χ.modulus := Nat.le_of_dvd χ.positive hq
    refine ⟨χ, N, hN, hq, hbound, Or.inr habs, by omega, by omega, ?_⟩
    apply kernel_prime_character_value d N χ hq (by simp [habs])
    simpa only [Bool.false_eq_true, ite_false, if_false, ← hdN] using hv
  · have hdN : d = -(2 * (N : ℤ)) := by rw [← heq]; ring
    have habs : d.natAbs = 2 * N := by simp [hdN, Int.natAbs_mul]
    have hN : 1 < N := by omega
    obtain ⟨χ, hq, hbound, hv⟩ := exists_even_kernel_primitive N hN hNsf hNodd true
    have hNle : N ≤ χ.modulus := Nat.le_of_dvd χ.positive hq
    refine ⟨χ, N, hN, hq, hbound, Or.inr habs, by omega, by omega, ?_⟩
    apply kernel_prime_character_value d N χ hq (by simp [habs])
    simpa only [ite_true, if_true, ← hdN] using hv

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_ConductorKernelCandidates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finitely many kernel candidates for one exceptional conductor -/

namespace Ostmann

open scoped Classical

theorem conductorKernelCandidates_card (q : ℕ) :
    (conductorKernelCandidates q).card ≤ 32 := by
  calc
    _ ≤ ((Finset.Icc 1 8).product quadraticSigns).card := Finset.card_image_le
    _ = 32 := by norm_num [quadraticSigns]

/-- The divisibility and size facts proved for the constructed characters
place the signed kernel on the explicit list for its conductor. -/
theorem mem_conductorKernelCandidates (d : ℤ) (q N : ℕ)
    (hN : 0 < N) (hq : 0 < q) (hNq : N ∣ q) (hbound : q ≤ 8 * N)
    (hd : d.natAbs = N ∨ d.natAbs = 2 * N) :
    d ∈ conductorKernelCandidates q := by
  obtain ⟨k, hk⟩ := hNq
  have hkpos : 0 < k := by nlinarith
  have hk8 : k ≤ 8 := by nlinarith
  have hqN : q / k = N := by
    rw [hk, Nat.mul_div_cancel N hkpos]
  have hsign : (d.natAbs : ℤ) = d ∨ -(d.natAbs : ℤ) = d := by
    rw [Int.natCast_natAbs]
    rcases le_total 0 d with hp | hn
    · exact Or.inl (abs_of_nonneg hp)
    · exact Or.inr (by rw [abs_of_nonpos hn, neg_neg])
  have hmem (c : ℤ) (hc : c ∈ quadraticSigns) (hcd : c * (N : ℤ) = d) :
      d ∈ conductorKernelCandidates q := by
    apply Finset.mem_image.mpr
    refine ⟨(k, c), Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hkpos, hk8⟩, hc⟩, ?_⟩
    simpa only [hqN] using hcd
  rcases hd with hd | hd <;> rcases hsign with hs | hs
  · exact hmem 1 (by simp [quadraticSigns]) (by simpa [hd] using hs)
  · exact hmem (-1) (by simp [quadraticSigns]) (by simpa [hd] using hs)
  · exact hmem 2 (by simp [quadraticSigns]) (by simpa [hd] using hs)
  · exact hmem (-2) (by simp [quadraticSigns]) (by simpa [hd] using hs)

theorem largeConductorKernelCandidates_card (q : ℕ) :
    (largeConductorKernelCandidates q).card ≤ 32 :=
  (Finset.card_le_card (Finset.filter_subset _ _)).trans (conductorKernelCandidates_card q)

theorem mem_largeConductorKernelCandidates (d : ℤ) (q N : ℕ)
    (hN : 0 < N) (hq : 0 < q) (hNq : N ∣ q) (hbound : q ≤ 8 * N)
    (hd : d.natAbs = N ∨ d.natAbs = 2 * N) (hqd : q ≤ 4 * d.natAbs) :
    d ∈ largeConductorKernelCandidates q :=
  Finset.mem_filter.mpr ⟨mem_conductorKernelCandidates d q N hN hq hNq hbound hd, hqd⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_ExceptionalKernelFamilyBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The total population removed by one exceptional conductor -/

namespace Ostmann

private theorem kernel_sqrt_quotient_bound (X : ℝ) (q : ℕ) (d : ℤ)
    (hX : 0 ≤ X) (hq : 0 < q) (hd : q ≤ 4 * d.natAbs) :
    X / Real.sqrt |(d : ℝ)| ≤ 2 * (X / Real.sqrt (q : ℝ)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hdR : (q : ℝ) ≤ 4 * |(d : ℝ)| := by
    have hh : (q : ℝ) ≤ 4 * (d.natAbs : ℝ) := by exact_mod_cast hd
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hh
  have hdpos : 0 < |(d : ℝ)| := by nlinarith
  have hroot : Real.sqrt (q : ℝ) ≤ 2 * Real.sqrt |(d : ℝ)| := by
    have hh := Real.sqrt_le_sqrt hdR
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)] at hh
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at hh
    exact hh
  rw [show 2 * (X / Real.sqrt (q : ℝ)) = (2 * X) / Real.sqrt (q : ℝ) by ring]
  apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hdpos) (Real.sqrt_pos.mpr hqR)).mpr
  calc
    X * Real.sqrt (q : ℝ) ≤ X * (2 * Real.sqrt |(d : ℝ)|) :=
      mul_le_mul_of_nonneg_left hroot hX
    _ = (2 * X) * Real.sqrt |(d : ℝ)| := by ring

/-- At most 32 possible signed products are lost. The conductor lower bound
replaces each product size in the previously proved population estimate. -/
theorem exists_exceptional_kernel_family_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (S T : Finset ℤ) (f g : ℤ → ℤ)
      (r s : ℤ → ℕ) (m q : ℕ) (h : ℤ) (X : ℝ),
      0 < m → 0 < q → 0 ≤ X →
      (∀ x ∈ S, f x ≠ 0) → (∀ y ∈ T, g y ≠ 0) →
      h.natAbs.Coprime m →
      (∀ x ∈ S, f x * (r x : ℤ) ^ 2 = (m : ℤ) * x - h) →
      (∀ y ∈ T, g y * (s y : ℤ) ^ 2 = (m : ℤ) * y - h) →
      (∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ X) →
      (∀ x ∈ T, ∀ y ∈ T, |((x - y : ℤ) : ℝ)| ≤ X) →
      (∀ x ∈ S, ∀ y ∈ T, (f x).natAbs.Coprime (g y).natAbs) →
      (((S.product T).filter fun z => f z.1 * g z.2 ∈ largeConductorKernelCandidates q).card : ℝ) ≤
        C * (X / Real.sqrt (q : ℝ) + 2 * Real.sqrt (X * m) + m) := by
  obtain ⟨C, hC, hbound⟩ := exists_endpoint_kernel_product_bound
  refine ⟨64 * C, by positivity, ?_⟩
  intro S T f g r s m q h X hm hq hX hf hg hred hr hs hspanS hspanT hcross
  let B := X / Real.sqrt (q : ℝ) + 2 * Real.sqrt (X * m) + m
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hd (d : ℤ) (hd : d ∈ largeConductorKernelCandidates q) :
      (((S.product T).filter fun z => f z.1 * g z.2 = d).card : ℝ) ≤ 2 * C * B := by
    have hb := hbound S T f g r s m h d X hm hX hf hg hred hr hs hspanS hspanT hcross
    rw [← kernel_pair_filter_card] at hb
    have hquot := kernel_sqrt_quotient_bound X q d hX hq (Finset.mem_filter.mp hd).2
    have ht : X / Real.sqrt |(d : ℝ)| + 2 * Real.sqrt (X * m) + m ≤ 2 * B := by
      dsimp [B]
      linarith [Real.sqrt_nonneg (X * m), show (0 : ℝ) ≤ m from Nat.cast_nonneg m]
    exact hb.trans ((mul_le_mul_of_nonneg_left ht hC.le).trans_eq (by ring))
  have hb := kernel_pair_finite_exclusion_bound S T f g (largeConductorKernelCandidates q)
    (2 * C * B) hd
  have hcard : ((largeConductorKernelCandidates q).card : ℝ) ≤ 32 := by
    exact_mod_cast largeConductorKernelCandidates_card q
  calc
    _ ≤ (largeConductorKernelCandidates q).card * (2 * C * B) := hb
    _ ≤ 32 * (2 * C * B) := mul_le_mul_of_nonneg_right hcard (mul_nonneg (mul_nonneg (by norm_num) hC.le) hB)
    _ = _ := by dsimp [B]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_PageKernelExclusion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the kernel family of a large Page character -/

namespace Ostmann

open scoped Classical

/-- A kernel outside the explicit excluded family can only represent a
selected Page character whose conductor is at most the retained threshold. -/
theorem page_kernel_retention (P : PublishedProgressionInput) (Q : ℕ) (R : ℝ)
    (d : ℤ) (χ : PrimitiveRealCharacter) (N : ℕ) (hN : 0 < N)
    (hNq : N ∣ χ.modulus) (hqN : χ.modulus ≤ 8 * N)
    (hdN : d.natAbs = N ∨ d.natAbs = 2 * N) (hqd : χ.modulus ≤ 4 * d.natAbs)
    (hout : d ∉ pageKernelExclusion P Q R)
    (e : PrimitiveRealZero) (he : selectedPageZero P Q = some e)
    (hsame : samePrimitiveRealCharacter e χ) : (e.modulus : ℝ) ≤ R := by
  by_contra hnot
  have hlarge : R < (e.modulus : ℝ) := lt_of_not_ge hnot
  have hmem : d ∈ largeConductorKernelCandidates e.modulus := by
    rw [hsame.1]
    exact mem_largeConductorKernelCandidates d χ.modulus N hN χ.positive hNq hqN hdN hqd
  have heq : pageKernelExclusion P Q R = largeConductorKernelCandidates e.modulus := by
    simp only [pageKernelExclusion, he, ite_eq_left hlarge]
  exact hout (heq ▸ hmem)

/-- The empty case costs nothing; the only nonempty case is one of the
already-bounded conductor families above the threshold. -/
theorem page_kernel_exclusion_count (P : PublishedProgressionInput) (Q : ℕ) (R E : ℝ)
    (S T : Finset ℤ) (f g : ℤ → ℤ) (hE : 0 ≤ E)
    (hcount : ∀ q : ℕ, R < (q : ℝ) →
      (((S.product T).filter fun z => f z.1 * g z.2 ∈ largeConductorKernelCandidates q).card : ℝ) ≤ E) :
    (((S.product T).filter fun z => f z.1 * g z.2 ∈ pageKernelExclusion P Q R).card : ℝ) ≤ E := by
  cases he : selectedPageZero P Q with
  | none => simpa only [pageKernelExclusion, he, Finset.notMem_empty, Finset.filter_false,
      Finset.card_empty, Nat.cast_zero] using hE
  | some e =>
    by_cases hlarge : R < (e.modulus : ℝ)
    · simpa only [pageKernelExclusion, he, ite_eq_left hlarge] using hcount e.modulus hlarge
    · simpa only [pageKernelExclusion, he, ite_eq_right hlarge, Finset.notMem_empty,
        Finset.filter_false, Finset.card_empty, Nat.cast_zero] using hE

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_VonMangoldtPole
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded remainder at the pole of the von Mangoldt series -/

namespace Ostmann

open scoped BigOperators ComplexOrder
open Complex LSeries

theorem exists_vonMangoldt_pole_error :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 1 < s → s ≤ 2 →
      ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ) -
        (1 / (s - 1) : ℝ)‖ ≤ C := by
  let F := ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux (0 : ZMod 1)
  have hcont : ContinuousOn (fun s : ℝ => F (s : ℂ)) (Set.Icc 1 2) := by
    apply ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux (0 : ZMod 1) |>.comp
      Complex.continuous_ofReal.continuousOn
    intro s hs
    exact hs.1
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨|M| + 1, by positivity, ?_⟩
  intro s hs hs2
  have hunit : IsUnit (0 : ZMod 1) := by
    rw [Subsingleton.elim (0 : ZMod 1) 1]
    exact isUnit_one
  have heq := ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux hunit
    (show (s : ℂ) ∈ {z : ℂ | 1 < z.re} by exact hs)
  rw [residue_one_eq_vonMangoldt] at heq
  simp only [Nat.totient_one, Nat.cast_one, inv_one] at heq
  have he : LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ) -
      (1 / (s - 1) : ℝ) = F (s : ℂ) := by
    change F (s : ℂ) = _ at heq
    rw [heq]
    push_cast
    ring
  rw [he]
  have hb := hM s ⟨hs.le, hs2⟩
  linarith [le_abs_self M]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_UnsignedPrimeMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The total logarithmic prime mass near one, from the proved zeta pole -/

namespace Ostmann

open scoped BigOperators
open Complex LSeries

theorem unsignedPrimeTerm_nonneg (s : ℝ) (n : ℕ) : 0 ≤ unsignedPrimeTerm s n := by
  unfold unsignedPrimeTerm
  split_ifs with h
  · exact div_nonneg (Real.log_nonneg (by exact_mod_cast h.one_lt.le))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · exact le_refl _

theorem unsignedPrimeTerm_eq_principal (s : ℝ) :
    unsignedPrimeTerm s = realPrimeTerm (1 : DirichletCharacter ℝ 1) s := by
  funext n
  have hn : (n : ZMod 1) = 1 := Subsingleton.elim _ _
  simp only [unsignedPrimeTerm, realPrimeTerm, hn, map_one, one_mul]

private theorem principal_logDerivative_eq (s : ℝ) (hs : 1 < s) :
    deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)) (s : ℂ) /
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) (s : ℂ) =
      -LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ) := by
  let χ : DirichletCharacter ℂ 1 := 1
  have hs' : 1 < (s : ℂ).re := hs
  have he := χ.LSeries_twist_vonMangoldt_eq hs'
  rw [← χ.deriv_LFunction_eq_deriv_LSeries hs', ← χ.LFunction_eq_LSeries hs'] at he
  have hf : (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) =
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) := by
    funext n
    rw [Subsingleton.elim (n : ZMod 1) 1, map_one, one_mul]
  change LSeries (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ) = _ at he
  rw [hf] at he
  simpa only [neg_div, neg_neg] using congrArg Neg.neg he.symm

theorem exists_unsignedPrimeMass_error :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 1 < s → s ≤ 2 →
      Summable (unsignedPrimeTerm s) ∧
      |(∑' n, unsignedPrimeTerm s n) - 1 / (s - 1)| ≤ C := by
  obtain ⟨Cp, hCp, hprime⟩ := exists_realPrimeSeries_error
  obtain ⟨Cv, hCv, hvon⟩ := exists_vonMangoldt_pole_error
  refine ⟨Cp + Cv, by positivity, ?_⟩
  intro s hs hs2
  have hc : (1 : DirichletCharacter ℝ 1).ringHomComp Complex.ofRealHom =
      (1 : DirichletCharacter ℂ 1) := by
    apply MulChar.ext
    intro a
    rw [Subsingleton.elim a 1, Units.val_one, map_one, map_one]
  obtain ⟨hsum, hp⟩ := hprime 1 1 s hs
  rw [hc, principal_logDerivative_eq s hs, Complex.neg_re,
    ← unsignedPrimeTerm_eq_principal] at hp
  have hv := (Complex.abs_re_le_norm _).trans (hvon s hs hs2)
  simp only [Complex.sub_re, Complex.ofReal_re] at hv
  refine ⟨by rwa [unsignedPrimeTerm_eq_principal], ?_⟩
  have he : (∑' n, unsignedPrimeTerm s n) - 1 / (s - 1) =
      ((∑' n, unsignedPrimeTerm s n) -
        (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ)).re) +
      ((LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ)).re - 1 / (s - 1)) := by ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hp hv)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_PrimeDivisorMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A small weighted mass for the primes dividing one integer -/

namespace Ostmann

open scoped BigOperators Classical

theorem prime_log_weight_le_one (p : ℕ) (hp : p.Prime) (s : ℝ) (hs : 1 ≤ s) :
    Real.log p / (p : ℝ) ^ s ≤ 1 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpow := Real.self_le_rpow_of_one_le hp1 hs
  have hpows : 0 < (p : ℝ) ^ s := Real.rpow_pos_of_pos hp0 _
  apply (div_le_one hpows).mpr
  have hlog := Real.log_le_sub_one_of_pos hp0
  linarith

/-- Splitting at the integer Y costs at most Y from small primes and
log(D)/Y from the remaining divisors. Taking Y near sqrt(log D) suffices
for the split-prime application. -/
theorem prime_divisor_mass_bound (P : Finset ℕ) (D Y : ℕ) (s : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hD : 0 < D) (hY : 0 < Y) (hs : 1 ≤ s) :
    (∑ p ∈ P.filter (fun p => p ∣ D), Real.log p / (p : ℝ) ^ s) ≤
      Y + Real.log D / Y := by
  let A := P.filter fun p => p ∣ D
  let U := A.filter fun p => p ≤ Y
  let V := A.filter fun p => ¬ p ≤ Y
  have hsplit : (∑ p ∈ A, Real.log p / (p : ℝ) ^ s) =
      (∑ p ∈ U, Real.log p / (p : ℝ) ^ s) + ∑ p ∈ V, Real.log p / (p : ℝ) ^ s := by
    exact (Finset.sum_filter_add_sum_filter_not A (fun p => p ≤ Y) _).symm
  have hUsub : U ⊆ Finset.Icc 1 Y := by
    intro p hp
    obtain ⟨hpA, hpY⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_Icc.mpr ⟨(hP p (Finset.mem_filter.mp hpA).1).one_lt.le, hpY⟩
  have hUcard : U.card ≤ Y := by
    have hc := Finset.card_le_card hUsub
    simpa using hc
  have hUsum : (∑ p ∈ U, Real.log p / (p : ℝ) ^ s) ≤ Y := by
    calc
      _ ≤ ∑ p ∈ U, (1 : ℝ) := Finset.sum_le_sum (by
        intro p hp
        exact prime_log_weight_le_one p (hP p (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1) s hs)
      _ = U.card := by simp
      _ ≤ Y := by exact_mod_cast hUcard
  have hVterm (p : ℕ) (hp : p ∈ V) : Real.log p / (p : ℝ) ^ s ≤ Real.log p / Y := by
    obtain ⟨hpA, hpY⟩ := Finset.mem_filter.mp hp
    have hprime := hP p (Finset.mem_filter.mp hpA).1
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hprime.one_lt.le
    have hpow := Real.self_le_rpow_of_one_le hp1 hs
    have hYp0 : (Y : ℝ) ≤ p := by exact_mod_cast (le_of_lt (Nat.lt_of_not_ge hpY))
    have hYp : (Y : ℝ) ≤ (p : ℝ) ^ s := hYp0.trans hpow
    exact div_le_div_of_nonneg_left (Real.log_nonneg hp1) (by exact_mod_cast hY) hYp
  have hVlog : (∑ p ∈ V, Real.log p) ≤ Real.log D :=
    sum_log_prime_divisors_le V hD
      (by intro p hp; exact hP p (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1)
      (by intro p hp; exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2)
  have hVsum : (∑ p ∈ V, Real.log p / (p : ℝ) ^ s) ≤ Real.log D / Y := by
    calc
      _ ≤ ∑ p ∈ V, Real.log p / Y := Finset.sum_le_sum hVterm
      _ = (∑ p ∈ V, Real.log p) / Y := by rw [Finset.sum_div]
      _ ≤ Real.log D / Y := div_le_div_of_nonneg_right hVlog (Nat.cast_nonneg Y)
  change (∑ p ∈ A, Real.log p / (p : ℝ) ^ s) ≤ _
  rw [hsplit]
  exact add_le_add hUsum hVsum

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_JacobiPrimeSeries
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Jacobi prime series differs only at the prime two -/

namespace Ostmann

open scoped BigOperators Classical

private theorem two_weight_bound (a s : ℝ) (ha : |a| ≤ 1) (hs : 0 ≤ s) :
    |a * Real.log 2 / (2 : ℝ) ^ s| ≤ 1 := by
  have hp : 0 < (2 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) _
  have hp1 : 1 ≤ (2 : ℝ) ^ s := Real.one_le_rpow (by norm_num) hs
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  rw [abs_div, abs_mul, abs_of_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2)), abs_of_pos hp]
  apply (div_le_one hp).mpr
  nlinarith [abs_nonneg a]

theorem jacobiPrimeSeries_comparison (d : ℤ) (χ : PrimitiveRealCharacter) (s : ℝ)
    (hs : 0 ≤ s)
    (hvalue : ∀ p : ℕ, p.Prime → p ≠ 2 → χ.character p = (jacobiSym d p : ℝ))
    (hsum : Summable (realPrimeTerm χ.character s)) :
    Summable (jacobiPrimeTerm d s) ∧
      |(∑' n, jacobiPrimeTerm d s n) - ∑' n, realPrimeTerm χ.character s n| ≤ 2 := by
  let δ := jacobiPrimeTerm d s 2 - realPrimeTerm χ.character s 2
  let e : ℕ → ℝ := fun n => if n = 2 then δ else 0
  have he : Summable e := summable_of_ne_finset_zero (s := {2}) (by
    intro n hn
    have hne : n ≠ 2 := by simpa only [Finset.mem_singleton] using hn
    exact ite_eq_right hne)
  have heq : jacobiPrimeTerm d s = fun n => realPrimeTerm χ.character s n + e n := by
    funext n
    by_cases hn : n = 2
    · subst n
      simp only [e, ite_true, if_true, δ]
      ring
    · have hh : jacobiPrimeTerm d s n = realPrimeTerm χ.character s n := by
        by_cases hp : n.Prime
        · simp only [jacobiPrimeTerm, realPrimeTerm, ite_eq_left hp, hvalue n hp hn]
        · simp only [jacobiPrimeTerm, realPrimeTerm, ite_eq_right hp]
      simpa only [e, ite_eq_right hn, add_zero] using hh
  have ht : (∑' n, e n) = δ := by simp only [e, tsum_ite_eq]
  have hj : Summable (jacobiPrimeTerm d s) := heq ▸ hsum.add he
  refine ⟨hj, ?_⟩
  have hsumeq : (∑' n, jacobiPrimeTerm d s n) = (∑' n, realPrimeTerm χ.character s n) + δ := by
    rw [heq, hsum.tsum_add he, ht]
  rw [hsumeq, add_sub_cancel_left]
  have hJ : |(jacobiSym d 2 : ℝ)| ≤ 1 := by
    rcases jacobiSym.trichotomy d 2 with h | h | h <;> simp [h]
  have hχ : |χ.character (2 : ℕ)| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using χ.character.norm_le_one ((2 : ℕ) : ZMod χ.modulus)
  have hJw := two_weight_bound (jacobiSym d 2) s hJ hs
  have hχw := two_weight_bound (χ.character (2 : ℕ)) s hχ hs
  have hbound := abs_sub_le (jacobiPrimeTerm d s 2) 0 (realPrimeTerm χ.character s 2)
  simp only [sub_zero, zero_sub, abs_neg] at hbound
  dsimp only [δ]
  simp only [Nat.cast_ofNat] at hχw
  simp only [jacobiPrimeTerm, realPrimeTerm, Nat.prime_two, ite_true, if_true, Nat.cast_ofNat] at hbound ⊢
  exact hbound.trans (by linarith)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSplitMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Converting a signed quadratic sum to retained split-prime mass -/

namespace Ostmann

open scoped BigOperators Classical

theorem jacobi_ne_zero_of_prime_not_dvd (d : ℤ) {p : ℕ} (hp : p.Prime)
    (hpd : ¬p ∣ d.natAbs) : jacobiSym d p ≠ 0 := by
  apply jacobiSym.ne_zero
  rw [Int.gcd_eq_natAbs]
  exact (hp.coprime_iff_not_dvd.mpr hpd).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_UnsignedPrimeTail
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A sufficient tail estimate from the prime mass at a smaller exponent -/

namespace Ostmann

open scoped BigOperators Classical

theorem unsignedPrimeTail_nonneg (Q : ℕ) (s : ℝ) (n : ℕ) :
    0 ≤ unsignedPrimeTail Q s n := by
  unfold unsignedPrimeTail
  split_ifs
  · exact unsignedPrimeTerm_nonneg s n
  · exact le_refl _

theorem unsignedPrimeTail_pointwise (Q : ℕ) (s : ℝ) (hQ : 0 < Q) (hs : 1 < s) (n : ℕ) :
    unsignedPrimeTail Q s n ≤
      (Q : ℝ) ^ (-(s - 1) / 2) * unsignedPrimeTerm ((s + 1) / 2) n := by
  by_cases hnQ : Q < n
  · rw [unsignedPrimeTail, ite_eq_left hnQ]
    by_cases hp : n.Prime
    · rw [unsignedPrimeTerm, unsignedPrimeTerm, ite_eq_left hp, ite_eq_left hp]
      have hn : (0 : ℝ) < n := by exact_mod_cast hp.pos
      have hq : (0 : ℝ) < Q := by exact_mod_cast hQ
      have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
      have ha : 0 ≤ (s - 1) / 2 := by linarith
      have hpow : (Q : ℝ) ^ ((s - 1) / 2) ≤ (n : ℝ) ^ ((s - 1) / 2) :=
        Real.rpow_le_rpow hq.le (by exact_mod_cast hnQ.le) ha
      have heq : s = (s + 1) / 2 + (s - 1) / 2 := by ring
      calc
        Real.log n / (n : ℝ) ^ s =
            (Real.log n / (n : ℝ) ^ ((s + 1) / 2)) / (n : ℝ) ^ ((s - 1) / 2) := by
          conv_lhs => rw [heq, Real.rpow_add hn]
          exact div_mul_eq_div_div _ _ _
        _ ≤ (Real.log n / (n : ℝ) ^ ((s + 1) / 2)) / (Q : ℝ) ^ ((s - 1) / 2) :=
          div_le_div_of_nonneg_left (div_nonneg hlog (Real.rpow_nonneg hn.le _))
            (Real.rpow_pos_of_pos hq _) hpow
        _ = _ := by
          rw [show -(s - 1) / 2 = -((s - 1) / 2) by ring, Real.rpow_neg hq.le]
          ring
    · simp only [unsignedPrimeTerm, ite_eq_right hp, mul_zero, le_refl]
  · rw [unsignedPrimeTail, ite_eq_right hnQ]
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg Q) _) (unsignedPrimeTerm_nonneg _ n)

theorem exists_unsignedPrimeTail_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℕ) (s : ℝ), 0 < Q → 1 < s → s ≤ 2 →
      Summable (unsignedPrimeTail Q s) ∧
      (∑' n, unsignedPrimeTail Q s n) ≤
        (Q : ℝ) ^ (-(s - 1) / 2) * (2 / (s - 1) + C) := by
  obtain ⟨C, hC, hmass⟩ := exists_unsignedPrimeMass_error
  refine ⟨C, hC, ?_⟩
  intro Q s hQ hs hs2
  have hs0 : 1 < (s + 1) / 2 := by linarith
  have hs02 : (s + 1) / 2 ≤ 2 := by linarith
  obtain ⟨hm, hb⟩ := hmass ((s + 1) / 2) hs0 hs02
  have hmaj := hm.mul_left ((Q : ℝ) ^ (-(s - 1) / 2))
  have htail : Summable (unsignedPrimeTail Q s) :=
    Summable.of_nonneg_of_le (unsignedPrimeTail_nonneg Q s)
      (unsignedPrimeTail_pointwise Q s hQ hs) hmaj
  refine ⟨htail, ?_⟩
  have htotal : (∑' n, unsignedPrimeTerm ((s + 1) / 2) n) ≤ 2 / (s - 1) + C := by
    have hh := (abs_le.mp hb).2
    have hfrac : 1 / ((s + 1) / 2 - 1) = 2 / (s - 1) := by
      rw [show (s + 1) / 2 - 1 = (s - 1) / 2 by ring, div_div_eq_mul_div]
      norm_num
    rw [hfrac] at hh
    linarith
  have ht := htail.tsum_le_tsum (unsignedPrimeTail_pointwise Q s hQ hs) hmaj
  rw [hm.tsum_mul_left] at ht
  exact ht.trans (mul_le_mul_of_nonneg_left htotal (Real.rpow_nonneg (Nat.cast_nonneg Q) _))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InfiniteSplitMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing the prime-series bounds to a finite set of split primes -/

namespace Ostmann

open scoped BigOperators Classical

theorem retainedSplitTerm_support (d : ℤ) (D Q : ℕ) (s : ℝ) (n : ℕ)
    (hn : n ∉ Nat.primesLE Q) : retainedSplitTerm d D Q s n = 0 := by
  by_cases hp : n.Prime
  · have hnQ : ¬n ≤ Q := fun h => hn (Nat.mem_primesLE.mpr ⟨h, hp⟩)
    simp [retainedSplitTerm, hnQ]
  · simp [retainedSplitTerm, unsignedPrimeTerm, hp]

theorem retainedSplitTerm_summable (d : ℤ) (D Q : ℕ) (s : ℝ) :
    Summable (retainedSplitTerm d D Q s) :=
  summable_of_ne_finset_zero (s := Nat.primesLE Q) (retainedSplitTerm_support d D Q s)

theorem retainedSplitTerm_tsum (d : ℤ) (D Q : ℕ) (s : ℝ) :
    (∑' n, retainedSplitTerm d D Q s n) =
      ∑ p ∈ (Nat.primesLE Q).filter (fun p => ¬p ∣ D ∧ jacobiSym d p = 1),
        Real.log p / (p : ℝ) ^ s := by
  rw [tsum_eq_sum (s := Nat.primesLE Q) (retainedSplitTerm_support d D Q s), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [retainedSplitTerm, unsignedPrimeTerm, (Nat.mem_primesLE.mp hp).1,
    (Nat.mem_primesLE.mp hp).2, ite_true, if_true, true_and]

theorem divisorPrimeTerm_support (D : ℕ) (hD : 0 < D) (s : ℝ) (n : ℕ)
    (hn : n ∉ D.primeFactors) : divisorPrimeTerm D s n = 0 := by
  by_cases hp : n.Prime
  · have hd : ¬n ∣ D := fun h => hn (Nat.mem_primeFactors.mpr ⟨hp, h, hD.ne'⟩)
    simp [divisorPrimeTerm, hd]
  · simp [divisorPrimeTerm, unsignedPrimeTerm, hp]

theorem divisorPrimeTerm_summable (D : ℕ) (hD : 0 < D) (s : ℝ) :
    Summable (divisorPrimeTerm D s) :=
  summable_of_ne_finset_zero (s := D.primeFactors) (divisorPrimeTerm_support D hD s)

theorem divisorPrimeTerm_mass (D Y : ℕ) (s : ℝ) (hD : 0 < D) (hY : 0 < Y) (hs : 1 ≤ s) :
    (∑' n, divisorPrimeTerm D s n) ≤ Y + Real.log D / Y := by
  have hP : ∀ p ∈ D.primeFactors, p.Prime := fun p hp => (Nat.mem_primeFactors.mp hp).1
  have hf : D.primeFactors.filter (fun p => p ∣ D) = D.primeFactors :=
    Finset.filter_true_of_mem (fun p hp => (Nat.mem_primeFactors.mp hp).2.1)
  have hb := prime_divisor_mass_bound D.primeFactors D Y s hP hD hY hs
  rw [hf] at hb
  rw [tsum_eq_sum (s := D.primeFactors) (divisorPrimeTerm_support D hD s)]
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro p hp
  simp only [divisorPrimeTerm, unsignedPrimeTerm, (Nat.mem_primeFactors.mp hp).1,
    (Nat.mem_primeFactors.mp hp).2.1, ite_true, if_true]

/-- This is the pointwise split-prime identity, with explicit losses for
large primes and divisors of the excluded integer. -/
theorem split_prime_pointwise (d : ℤ) (D Q : ℕ) (s : ℝ) (hdD : d.natAbs ∣ D) (n : ℕ) :
    unsignedPrimeTerm s n + jacobiPrimeTerm d s n ≤
      2 * retainedSplitTerm d D Q s n + 2 * unsignedPrimeTail Q s n + 2 * divisorPrimeTerm D s n := by
  by_cases hp : n.Prime
  · let w := Real.log n / (n : ℝ) ^ s
    have hw : 0 ≤ w := by
      simpa only [w, unsignedPrimeTerm, ite_eq_left hp] using unsignedPrimeTerm_nonneg s n
    have hj : jacobiPrimeTerm d s n = w * (jacobiSym d n : ℝ) := by
      simp only [jacobiPrimeTerm, ite_eq_left hp, w]
      ring
    rw [hj]
    simp only [unsignedPrimeTerm, ite_eq_left hp, retainedSplitTerm, divisorPrimeTerm, unsignedPrimeTail]
    change w + w * (jacobiSym d n : ℝ) ≤
      2 * (if n ≤ Q ∧ ¬n ∣ D ∧ jacobiSym d n = 1 then w else 0) +
      2 * (if Q < n then w else 0) + 2 * (if n ∣ D then w else 0)
    rcases jacobiSym.trichotomy d n with hz | ho | hm
    · have hnD : n ∣ D := by
        by_contra hnot
        exact jacobi_ne_zero_of_prime_not_dvd d hp (fun h => hnot (h.trans hdD)) hz
      simp only [hz, Int.cast_zero, mul_zero, add_zero, hnD, ite_true, if_true]
      split_ifs <;> linarith
    · by_cases hnQ : n ≤ Q <;> by_cases hnD : n ∣ D <;>
        simp [ho, hnQ, hnD, show Q < n ↔ ¬n ≤ Q by omega] <;> linarith
    · simp only [hm, Int.cast_neg, Int.cast_one, mul_neg_one, add_neg_cancel]
      positivity
  · simp [unsignedPrimeTerm, jacobiPrimeTerm, retainedSplitTerm, unsignedPrimeTail,
      divisorPrimeTerm, hp]

/-- Infinite unsigned and signed series give a lower bound for the actual
finite retained set; all excluded-divisor weights are bounded explicitly. -/
theorem retained_split_mass_from_series (d : ℤ) (D Q Y : ℕ) (s L B T : ℝ)
    (hdD : d.natAbs ∣ D) (hD : 0 < D) (hY : 0 < Y) (hs : 1 ≤ s)
    (hu : Summable (unsignedPrimeTerm s)) (hj : Summable (jacobiPrimeTerm d s))
    (ht : Summable (unsignedPrimeTail Q s))
    (hL : L ≤ ∑' n, unsignedPrimeTerm s n)
    (hB : -B ≤ ∑' n, jacobiPrimeTerm d s n)
    (hT : (∑' n, unsignedPrimeTail Q s n) ≤ T) :
    (L - B) / 2 - T - (Y + Real.log D / Y) ≤
      ∑ p ∈ (Nat.primesLE Q).filter (fun p => ¬p ∣ D ∧ jacobiSym d p = 1),
        Real.log p / (p : ℝ) ^ s := by
  have hr := retainedSplitTerm_summable d D Q s
  have hd := divisorPrimeTerm_summable D hD s
  have hineq := (hu.add hj).tsum_le_tsum (split_prime_pointwise d D Q s hdD)
    (((hr.mul_left 2).add (ht.mul_left 2)).add (hd.mul_left 2))
  rw [hu.tsum_add hj, ((hr.mul_left 2).add (ht.mul_left 2)).tsum_add (hd.mul_left 2),
    (hr.mul_left 2).tsum_add (ht.mul_left 2), hr.tsum_mul_left, ht.tsum_mul_left, hd.tsum_mul_left,
    retainedSplitTerm_tsum] at hineq
  have hdiv := divisorPrimeTerm_mass D Y s hD hY hs
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_SplitMassNumerics
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit numerical margin in the split-prime estimate -/

namespace Ostmann

open scoped BigOperators

theorem exp_neg_twelve_fifths_le : Real.exp (-(12 / 5 : ℝ)) ≤ 1 / 11 := by
  have he : (11 : ℝ) ≤ Real.exp (12 / 5) := by
    apply le_trans _ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 12 / 5) 10)
    norm_num [Finset.sum_range_succ]
  rw [Real.exp_neg, inv_eq_one_div]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  linarith

/-- A cutoff whose logarithm is at least 0.48L suffices for the exponent
comparison tail. The later choices have logarithm asymptotic to 0.5L. -/
theorem split_prime_tail_factor_bound (Q : ℕ) (L : ℝ) (hQ : 0 < Q) (hL : 0 < L)
    (hlog : (12 / 25 : ℝ) * L ≤ Real.log (Q : ℝ)) :
    (Q : ℝ) ^ (-(10 / L) / 2) ≤ 1 / 11 := by
  have hneg : -(5 / L) ≤ (0 : ℝ) := neg_nonpos.mpr (div_nonneg (by norm_num) hL.le)
  have hm := mul_le_mul_of_nonpos_right hlog hneg
  have hid : ((12 / 25 : ℝ) * L) * -(5 / L) = -(12 / 5 : ℝ) := by
    field_simp
    ring
  rw [hid] at hm
  rw [Real.rpow_def_of_pos (by exact_mod_cast hQ)]
  have he : Real.log (Q : ℝ) * (-(10 / L) / 2) ≤ -(12 / 5 : ℝ) := by
    convert hm using 1
    all_goals try with_reducible_and_instances rfl
    ring
  exact (Real.exp_le_exp.mpr he).trans exp_neg_twelve_fifths_le

/-- The elementary margin leaves room for all constant and Siegel errors. -/
theorem split_mass_numeric_margin (L C B E t : ℝ) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hCsmall : C ≤ L / 10000) (hBsmall : B ≤ L / 10000)
    (hEsmall : E ≤ L / 10000) (ht : t ≤ 1 / 11) :
    (3 / 100 : ℝ) * L ≤ (L / 10 - C - B) / 2 - t * (L / 5 + C) - E := by
  have hfactor : 0 ≤ L / 5 + C := by positivity
  have hprod := mul_le_mul_of_nonneg_right ht hfactor
  nlinarith

/-- Specialization of the proved split mass, with no prime-sum hypothesis. -/
theorem split_prime_mass_of_small_errors (d : ℤ) (D Q Y : ℕ)
    (L C B : ℝ) (hL : 0 < L) (hQ : 0 < Q) (hC : 0 ≤ C)
    (hCsmall : C ≤ L / 10000) (hBsmall : B ≤ L / 10000)
    (hEsmall : (Y : ℝ) + Real.log D / Y ≤ L / 10000)
    (hlog : (12 / 25 : ℝ) * L ≤ Real.log (Q : ℝ))
    (hmass : (1 / ((1 + 10 / L) - 1) - C - B) / 2 -
      (Q : ℝ) ^ (-((1 + 10 / L) - 1) / 2) * (2 / ((1 + 10 / L) - 1) + C) -
      (Y + Real.log D / Y) ≤
      ∑ p ∈ (Nat.primesLE Q).filter (fun p => ¬p ∣ D ∧ jacobiSym d p = 1),
        Real.log p / (p : ℝ)) :
    (3 / 100 : ℝ) * L ≤
      ∑ p ∈ (Nat.primesLE Q).filter (fun p => ¬p ∣ D ∧ jacobiSym d p = 1),
        Real.log p / (p : ℝ) := by
  have hfrac : 1 / ((1 + 10 / L) - 1) = L / 10 := by
    field_simp
    ring
  have hfrac2 : 2 / ((1 + 10 / L) - 1) = L / 5 := by
    field_simp
    ring
  rw [hfrac, hfrac2, add_sub_cancel_left] at hmass
  exact (split_mass_numeric_margin L C B _ _ hL.le hC hCsmall hBsmall hEsmall
    (split_prime_tail_factor_bound Q L hQ hL hlog)).trans hmass

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_SmallKernelCharacters
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The three nonprincipal kernels of absolute value at most two -/

namespace Ostmann

private theorem negative_one_kernel_ne_one : signedOddKernelCharacter 1 true ≠ 1 := by
  intro he
  have hv := signedOddKernelCharacter_value 1 true (by decide) 3 (by decide) (by decide)
  have hJ : jacobiSym (-1) 3 = -1 := by
    rw [jacobiSym.at_neg_one (by decide)]
    norm_num [ZMod.χ₄_nat_eq_if_mod_four]
  have hu : IsUnit ((3 : ℕ) : ZMod (Nat.lcm 1 4)) := (ZMod.isUnit_iff_coprime 3 _).mpr (by decide)
  rw [he, MulChar.one_apply hu] at hv
  norm_num [hJ] at hv

private theorem even_one_kernel_ne_one (negative : Bool) :
    signedEvenKernelCharacter 1 negative ≠ 1 := by
  intro he
  have hv := signedEvenKernelCharacter_value 1 negative (by decide) 5 (by decide) (by decide)
  have hu : IsUnit ((5 : ℕ) : ZMod (Nat.lcm 1 8)) := (ZMod.isUnit_iff_coprime 5 _).mpr (by decide)
  rw [he, MulChar.one_apply hu] at hv
  have hp : jacobiSym 2 5 = -1 := by
    rw [jacobiSym.at_two (by decide)]
    norm_num [ZMod.χ₈_nat_eq_if_mod_eight]
  have hn : jacobiSym (-2) 5 = -1 := by
    rw [show (-2 : ℤ) = -(2 : ℤ) by rfl, jacobiSym.neg _ (by decide), hp]
    norm_num [ZMod.χ₄_nat_eq_if_mod_four]
  cases negative <;> norm_num [hp, hn] at hv

/-- The small characters are constructed from the same twists and checked at
3 or 5. Their conductors are bounded by the original levels 4 and 8. -/
theorem exists_negative_one_kernel_character :
    ∃ χ : PrimitiveRealCharacter, χ.modulus ≤ 4 ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 → χ.character p = (jacobiSym (-1) p : ℝ) := by
  let : NeZero (Nat.lcm 1 4) := ⟨by simp⟩
  let ψ := signedOddKernelCharacter 1 true
  let χ := primitiveRealOfCharacter ψ negative_one_kernel_ne_one
  have hbound : χ.modulus ≤ 4 := by
    change (signedOddKernelCharacter 1 true).conductor ≤ 4
    simpa using (signedOddKernelCharacter_conductor_bounds 1 true (by simp) (by decide)).2
  refine ⟨χ, hbound, ?_⟩
  intro p hp hp2
  have hpodd := hp.odd_of_ne_two hp2
  have hcop : p.Coprime (Nat.lcm 1 4) := by
    simpa using hpodd.coprime_two_right.pow_right 2
  dsimp only [χ]
  rw [primitiveRealOfCharacter_value ψ negative_one_kernel_ne_one p hcop]
  simpa using signedOddKernelCharacter_value 1 true (by decide) p hcop hpodd

theorem exists_even_one_kernel_character (negative : Bool) :
    ∃ χ : PrimitiveRealCharacter, χ.modulus ≤ 8 ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 →
        χ.character p = (jacobiSym (if negative then -2 else 2) p : ℝ) := by
  let : NeZero (Nat.lcm 1 8) := ⟨by simp⟩
  let ψ := signedEvenKernelCharacter 1 negative
  let χ := primitiveRealOfCharacter ψ (even_one_kernel_ne_one negative)
  have hbound : χ.modulus ≤ 8 := by
    change (signedEvenKernelCharacter 1 negative).conductor ≤ 8
    simpa using (signedEvenKernelCharacter_conductor_bounds 1 negative (by simp) (by decide)).2
  refine ⟨χ, hbound, ?_⟩
  intro p hp hp2
  have hpodd := hp.odd_of_ne_two hp2
  have hcop : p.Coprime (Nat.lcm 1 8) := by
    simpa using hpodd.coprime_two_right.pow_right 3
  dsimp only [χ]
  rw [primitiveRealOfCharacter_value ψ (even_one_kernel_ne_one negative) p hcop]
  simpa using signedEvenKernelCharacter_value 1 negative (by decide) p hcop hpodd

/-- Every nonprincipal nonzero squarefree kernel has the same conductor
and odd-prime properties, including the three small cases. -/
theorem exists_nonprincipal_kernel_character (d : ℤ)
    (hsf : Squarefree d.natAbs) (hzero : d ≠ 0) (hone : d ≠ 1) :
    ∃ (χ : PrimitiveRealCharacter) (N : ℕ),
      0 < N ∧ N ∣ χ.modulus ∧ χ.modulus ≤ 8 * N ∧
      (d.natAbs = N ∨ d.natAbs = 2 * N) ∧
      χ.modulus ≤ 4 * d.natAbs ∧ d.natAbs ≤ 2 * χ.modulus ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 → χ.character p = (jacobiSym d p : ℝ) := by
  by_cases hd : 2 < d.natAbs
  · obtain ⟨χ, N, hN, hNq, hqN, hdN, hqd, hdq, hv⟩ := exists_signed_kernel_character d hsf hd
    exact ⟨χ, N, by omega, hNq, hqN, hdN, hqd, hdq, hv⟩
  · have habs : |d| ≤ 2 := by
      have hh : (d.natAbs : ℤ) ≤ 2 := by exact_mod_cast (le_of_not_gt hd)
      simpa only [Int.natCast_natAbs] using hh
    have hlo := (abs_le.mp habs).1
    have hhi := (abs_le.mp habs).2
    interval_cases d
    · obtain ⟨χ, hq, hv⟩ := exists_even_one_kernel_character true
      have hp := χ.positive
      refine ⟨χ, 1, by decide, one_dvd _, by simpa using hq, ?_, ?_, ?_, ?_⟩
      · norm_num
      · simpa using hq
      · norm_num at ⊢
        omega
      · simpa using hv
    · obtain ⟨χ, hq, hv⟩ := exists_negative_one_kernel_character
      have hp := χ.positive
      refine ⟨χ, 1, by decide, one_dvd _, by omega, ?_, ?_, ?_, hv⟩
      · norm_num
      · simpa using hq
      · norm_num at ⊢
        omega
    · exact (hzero rfl).elim
    · exact (hone rfl).elim
    · obtain ⟨χ, hq, hv⟩ := exists_even_one_kernel_character false
      have hp := χ.positive
      refine ⟨χ, 1, by decide, one_dvd _, by simpa using hq, ?_, ?_, ?_, ?_⟩
      · norm_num
      · simpa using hq
      · norm_num at ⊢
        omega
      · simpa using hv

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_AllKernelSplitMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The retained split-prime estimate for every nonzero squarefree kernel -/

namespace Ostmann

open scoped BigOperators Classical

/-- This includes the principal kernel 1 and all three small nonprincipal
kernels. The constants and exclusion set are uniform over every kernel. -/
theorem all_kernel_split_prime_mass (P : PublishedProgressionInput)
    (H : PublishedRealZeroInput P) (hSiegel : PublishedSiegelBound)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A K C : ℝ, 0 < A ∧ 0 < K ∧ 0 < C ∧
      ∀ (d : ℤ) (Q₀ Q D Y : ℕ) (R s : ℝ),
        Squarefree d.natAbs → d ≠ 0 →
        2 ≤ Q₀ → 4 * d.natAbs ≤ Q₀ → 0 < Q → 0 < D → 0 < Y →
        d.natAbs ∣ D → 0 ≤ R →
        2 * (A + H.errorConstant) ≤ Real.log (4 * (Q₀ : ℝ)) →
        1 < s → s ≤ 2 → s ≤ 1 + 1 / Real.log (4 * (Q₀ : ℝ)) →
        d ∉ pageKernelExclusion P Q₀ R →
        splitPrimeMassLower P H A K C ε Q₀ Q D Y R s ≤
          ∑ p ∈ (Nat.primesLE Q).filter (fun p => ¬p ∣ D ∧ jacobiSym d p = 1),
            Real.log p / (p : ℝ) := by
  obtain ⟨A, K, hA, hK, hchar⟩ := retained_character_prime_lower P H hSiegel ε hε
  obtain ⟨Cu, hCu, hmass⟩ := exists_unsignedPrimeMass_error
  obtain ⟨Ct, hCt, htail⟩ := exists_unsignedPrimeTail_bound
  obtain ⟨Ce, hCe, hcharsum⟩ := exists_realPrimeSeries_error
  let C := Cu + Ct
  have hCuC : Cu ≤ C := by dsimp [C]; linarith
  have hCtC : Ct ≤ C := by dsimp [C]; linarith
  refine ⟨A, K, C, hA, hK, by dsimp [C]; positivity, ?_⟩
  intro d Q₀ Q D Y R s hsf hd hQ₀ hdQ₀ hQ hD hY hdD hR hsize hs hs2 hss hout
  obtain ⟨hu, hU⟩ := hmass s hs hs2
  obtain ⟨ht, hT⟩ := htail Q s hQ hs hs2
  let B := 2 * zeroComparisonConstant P * Real.log (4 * (Q₀ : ℝ)) +
    K * R ^ ε + H.errorConstant + A + 2
  have hJ : Summable (jacobiPrimeTerm d s) ∧ -B ≤ ∑' n, jacobiPrimeTerm d s n := by
    by_cases hone : d = 1
    · have heq : jacobiPrimeTerm d s = unsignedPrimeTerm s := by
        subst d
        funext n
        simp only [jacobiPrimeTerm, unsignedPrimeTerm, jacobiSym.one_left, Int.cast_one, one_mul]
      rw [heq]
      have hlog : 0 ≤ Real.log (4 * (Q₀ : ℝ)) := by
        apply Real.log_nonneg
        have hQr : (2 : ℝ) ≤ Q₀ := by exact_mod_cast hQ₀
        linarith
      have hCz : 0 ≤ zeroComparisonConstant P := by
        exact le_trans (by norm_num : (0 : ℝ) ≤ 5) (le_max_left _ _)
      have hHC := H.errorConstant_nonneg
      have hB : 0 ≤ B := by dsimp [B]; positivity
      exact ⟨hu, le_trans (neg_nonpos.mpr hB) (tsum_nonneg (unsignedPrimeTerm_nonneg s))⟩
    · obtain ⟨χ, N, hN, hNq, hqN, hdN, hqd, _, hv⟩ :=
        exists_nonprincipal_kernel_character d hsf hd hone
      have hret := page_kernel_retention P Q₀ R d χ N hN hNq hqN hdN hqd hout
      have hb := hchar χ Q₀ R s hQ₀ (hqd.trans hdQ₀) hR hsize hs hss hret
      let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
      have hc := jacobiPrimeSeries_comparison d χ s (by linarith) hv
        (hcharsum χ.modulus χ.character s hs).1
      refine ⟨hc.1, ?_⟩
      have hdiff := (abs_le.mp hc.2).1
      dsimp [B]
      linarith
  have hUl : 1 / (s - 1) - C ≤ ∑' n, unsignedPrimeTerm s n := by
    have hh := (abs_le.mp hU).1
    linarith
  have hTl : (∑' n, unsignedPrimeTail Q s n) ≤
      (Q : ℝ) ^ (-(s - 1) / 2) * (2 / (s - 1) + C) :=
    hT.trans (mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg Q) _))
  have hsplit := retained_split_mass_from_series d D Q Y s _ B _ hdD hD hY hs.le
    hu hJ.1 ht hUl hJ.2 hTl
  change splitPrimeMassLower P H A K C ε Q₀ Q D Y R s ≤ _
  apply hsplit.trans
  apply Finset.sum_le_sum
  intro p hp
  have hprime := Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hprime.one_lt.le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  exact div_le_div_of_nonneg_left (Real.log_nonneg hp1) hp0
    (Real.self_le_rpow_of_one_le hp1 hs.le)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_KernelAnalyticParameters
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete error absorption for the quadratic-kernel parameters -/

namespace Ostmann

/-- Choose the kernel-size exponent after the absolute zero-comparison
constant has been fixed. -/
theorem exists_kernel_size_exponent (Cz : ℝ) (hCz : 5 ≤ Cz) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 1000 ∧ 4 * Cz * η = 1 / 40000 := by
  have hp : 0 < Cz := by linarith
  refine ⟨1 / (160000 * Cz), by positivity, ?_, ?_⟩
  · apply (div_le_iff₀ (by positivity : 0 < 160000 * Cz)).mpr
    nlinarith
  · field_simp
    ring

theorem kernel_sqrt_error_absorption (K L : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hsize : (40000 * K) ^ 2 ≤ L) : K * Real.sqrt L ≤ L / 40000 := by
  have hroot : 40000 * K ≤ Real.sqrt L := (Real.le_sqrt (by positivity) hL).mpr hsize
  have hh := mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg L)
  rw [Real.mul_self_sqrt hL] at hh
  nlinarith

/-- The Page threshold is (log X)^100 and Siegel is used only at exponent
1/200, giving a square-root error in log X. -/
theorem page_threshold_siegel_power (L : ℝ) (hL : 0 ≤ L) :
    ((L ^ (100 : ℕ)) : ℝ) ^ (1 / 200 : ℝ) = Real.sqrt L := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL]
  norm_num
  rw [Real.sqrt_eq_rpow]

/-- The logarithmic conductor cost and square-root Siegel cost are both
absorbed by the chosen fixed coefficient of L. -/
theorem kernel_zero_error_absorption (Cz η K A H L logQ : ℝ)
    (hCz : 0 ≤ Cz) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hη : 4 * Cz * η ≤ 1 / 40000)
    (hQ : logQ ≤ 2 * η * L + Real.log 20)
    (hKsize : (40000 * K) ^ 2 ≤ L)
    (hconst : 40000 * (2 * Cz * Real.log 20 + H + A + 2) ≤ L) :
    2 * Cz * logQ + K * Real.sqrt L + H + A + 2 ≤ L / 10000 := by
  have hq := mul_le_mul_of_nonneg_left hQ (show 0 ≤ 2 * Cz by positivity)
  have heta := mul_le_mul_of_nonneg_right hη hL
  have hsqrt := kernel_sqrt_error_absorption K L hK hL hKsize
  nlinarith

/-- The elementary divisor bound is o(L) with a square-root cutoff. -/
theorem kernel_divisor_error_absorption (D Y : ℕ) (L : ℝ)
    (hL : 0 < L) (hlarge : (40000 : ℝ) ^ 2 ≤ L)
    (hYlo : Real.sqrt L ≤ Y) (hYhi : (Y : ℝ) ≤ Real.sqrt L + 1)
    (hlogD : Real.log D ≤ L) :
    (Y : ℝ) + Real.log D / Y ≤ L / 10000 := by
  have hr : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hY : (0 : ℝ) < Y := hr.trans_le hYlo
  have hroot : 40000 ≤ Real.sqrt L := (Real.le_sqrt (by norm_num) hL.le).mpr hlarge
  have hsquare : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL.le
  have hdiv : Real.log D / Y ≤ Real.sqrt L := by
    apply (div_le_iff₀ hY).mpr
    calc
      Real.log D ≤ L := hlogD
      _ = Real.sqrt L * Real.sqrt L := hsquare.symm
      _ ≤ Real.sqrt L * Y := mul_le_mul_of_nonneg_left hYlo hr.le
  have hprod := mul_le_mul_of_nonneg_right hroot hr.le
  rw [hsquare] at hprod
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_KernelPrimeCutoffs
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual integer cutoffs for the quadratic split-prime argument -/

namespace Ostmann

theorem kernelConductorCutoff_bounds (η L : ℝ) (hη : 0 ≤ η) (hL : 0 ≤ L) :
    2 ≤ kernelConductorCutoff η L ∧
      2 * η * L ≤ Real.log (4 * (kernelConductorCutoff η L : ℝ)) ∧
      Real.log (4 * (kernelConductorCutoff η L : ℝ)) ≤ 2 * η * L + Real.log 20 := by
  let t := 2 * η * L
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have he1 := Real.one_le_exp ht
  have hc : 4 * Real.exp t ≤ (kernelConductorCutoff η L : ℝ) := Nat.le_ceil _
  have hcl : (kernelConductorCutoff η L : ℝ) < 4 * Real.exp t + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hq : (2 : ℝ) ≤ kernelConductorCutoff η L := by linarith
  have hpos : 0 < 4 * (kernelConductorCutoff η L : ℝ) := by linarith
  refine ⟨by exact_mod_cast hq, ?_, ?_⟩
  · apply (Real.le_log_iff_exp_le hpos).mpr
    change Real.exp t ≤ _
    linarith
  · have he : 4 * (kernelConductorCutoff η L : ℝ) ≤ 20 * Real.exp t := by linarith
    have hl := Real.log_le_log hpos he
    rw [Real.log_mul (by norm_num : (20 : ℝ) ≠ 0) (Real.exp_ne_zero t), Real.log_exp] at hl
    simpa only [t, add_comm] using hl

theorem kernelConductorCutoff_covers (η L : ℝ) (d : ℤ)
    (hd : (d.natAbs : ℝ) ≤ Real.exp (2 * η * L)) :
    4 * d.natAbs ≤ kernelConductorCutoff η L := by
  have hc : 4 * Real.exp (2 * η * L) ≤ (kernelConductorCutoff η L : ℝ) := Nat.le_ceil _
  have hh : (4 : ℝ) * d.natAbs ≤ kernelConductorCutoff η L := by linarith
  exact_mod_cast hh

theorem kernelDivisorCutoff_bounds (L : ℝ) (hL : 0 < L) :
    0 < kernelDivisorCutoff L ∧ Real.sqrt L ≤ kernelDivisorCutoff L ∧
      (kernelDivisorCutoff L : ℝ) ≤ Real.sqrt L + 1 := by
  have hlo : Real.sqrt L ≤ (kernelDivisorCutoff L : ℝ) := Nat.le_ceil _
  have hhi : (kernelDivisorCutoff L : ℝ) < Real.sqrt L + 1 :=
    Nat.ceil_lt_add_one (Real.sqrt_nonneg L)
  have hp : (0 : ℝ) < kernelDivisorCutoff L := (Real.sqrt_pos.mpr hL).trans_le hlo
  exact ⟨by exact_mod_cast hp, hlo, hhi.le⟩

theorem kernelSplitCutoff_bounds (η L : ℝ) (hη : η ≤ 1 / 1000) (hL : 100 ≤ L) :
    0 < kernelSplitCutoff η L ∧
      (12 / 25 : ℝ) * L ≤ Real.log (kernelSplitCutoff η L : ℝ) := by
  let a := 1 / 2 - 5 * η
  have hL0 : 0 ≤ L := by linarith
  have ha : (99 / 200 : ℝ) ≤ a := by dsimp [a]; linarith
  have haL : (99 / 200 : ℝ) * L ≤ a * L := mul_le_mul_of_nonneg_right ha hL0
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have he2 : (2 : ℝ) ≤ Real.exp (a * L) := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mp
    linarith
  have hf : Real.exp (a * L) < (kernelSplitCutoff η L : ℝ) + 1 := Nat.lt_floor_add_one _
  have hhalf : Real.exp (a * L) / 2 ≤ (kernelSplitCutoff η L : ℝ) := by linarith
  have hp : (0 : ℝ) < kernelSplitCutoff η L :=
    (div_pos (Real.exp_pos _) (by norm_num)).trans_le hhalf
  refine ⟨by exact_mod_cast hp, ?_⟩
  have hl := Real.log_le_log (div_pos (Real.exp_pos (a * L)) (by norm_num)) hhalf
  rw [Real.log_div (Real.exp_ne_zero _) (by norm_num), Real.log_exp] at hl
  linarith

theorem kernelSplitCutoff_log_lower (η L : ℝ) (hη : η ≤ 1 / 1000) (hL : 100 ≤ L) :
    (1 / 2 - 5 * η) * L - 1 ≤ Real.log (kernelSplitCutoff η L : ℝ) := by
  let t := (1 / 2 - 5 * η) * L
  have hηL := mul_le_mul_of_nonneg_right hη (show 0 ≤ L by linarith)
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have he2 : (2 : ℝ) ≤ Real.exp t := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mp
    dsimp [t]
    linarith
  have hf : Real.exp t < (kernelSplitCutoff η L : ℝ) + 1 := Nat.lt_floor_add_one _
  have hhalf : Real.exp t / 2 ≤ (kernelSplitCutoff η L : ℝ) := by linarith
  have hl := Real.log_le_log (div_pos (Real.exp_pos t) (by norm_num)) hhalf
  rw [Real.log_div (Real.exp_ne_zero _) (by norm_num), Real.log_exp] at hl
  change t - 1 ≤ _
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_KernelPopulationRetention
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative retention of small, populated kernel fibers -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem eventual_small_kernel_fibers_decay (η ε a : ℝ)
    (hη : 0 < η) (hεη : ε ≤ η / 100) (ha : 0 < a) :
    ∀ᶠ L : ℝ in atTop, ∀ (S : Finset ℤ) (f : ℤ → ℤ),
      ((S.image f).card : ℝ) ≤ Real.exp (3 * ε * L) →
      ((S.filter fun x => (S.filter fun y => f y = f x).card <
        kernelSplitCutoff η L).card : ℝ) ≤ a * Real.exp (L / 2) / L ^ 6 := by
  have hp := ((isLittleO_pow_exp_pos_mul_atTop 6 hη).const_mul_left (1 / a)).bound
    (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hp, eventually_ge_atTop (1 : ℝ)] with L hpoly hL S f hcount
  have hLp : 0 < L := by linarith
  have hQ : (kernelSplitCutoff η L : ℝ) ≤ Real.exp ((1 / 2 - 5 * η) * L) :=
    Nat.floor_le (Real.exp_nonneg _)
  have he : Real.exp (3 * ε * L) * Real.exp ((1 / 2 - 5 * η) * L) ≤
      Real.exp ((1 / 2 - η) * L) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (show 0 ≤ η / 100 - ε by linarith) hLp.le]
  have hp' : L ^ 6 / a ≤ Real.exp (η * L) := by
    simpa only [Real.norm_eq_abs, one_div_mul_eq_div, abs_of_nonneg (by positivity : 0 ≤ L ^ 6 / a),
      abs_of_pos (Real.exp_pos _), one_mul] using hpoly
  have hdecay : Real.exp ((1 / 2 - η) * L) ≤ a * Real.exp (L / 2) / L ^ 6 := by
    apply (le_div_iff₀ (pow_pos hLp 6)).mpr
    have hh : L ^ 6 ≤ a * Real.exp (η * L)  := by
      simpa only [mul_comm] using (div_le_iff₀ ha).mp hp'
    have hmul := mul_le_mul_of_nonneg_left hh (Real.exp_nonneg ((1 / 2 - η) * L))
    have hexp : Real.exp ((1 / 2 - η) * L) * Real.exp (η * L) = Real.exp (L / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    calc
      _ ≤ Real.exp ((1 / 2 - η) * L) * (a * Real.exp (η * L)) := hmul
      _ = _ := by rw [mul_left_comm, hexp]
  calc
    _ ≤ (S.image f).card * (kernelSplitCutoff η L : ℝ) := by
      exact_mod_cast small_kernel_fibers_card S f (kernelSplitCutoff η L)
    _ ≤ Real.exp (3 * ε * L) * Real.exp ((1 / 2 - 5 * η) * L) :=
      mul_le_mul hcount hQ (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ ≤ _ := he.trans hdecay

/-- At least half the original population remains in entire fibers whose
kernels are small and whose individual sizes reach the split-prime cutoff. -/
theorem eventual_populated_kernel_retention (η ε a : ℝ)
    (hη : 0 < η) (hηU : η ≤ 1 / 1000) (hε : 0 ≤ ε) (hεη : ε ≤ η / 100)
    (ha : 0 < a) :
    ∀ᶠ L : ℝ in atTop, ∀ (S : Finset ℤ) (f : ℤ → ℤ) (root : ℤ → ℕ)
      (m : ℕ) (h : ℤ),
      0 < m → (m : ℝ) ≤ Real.exp (η * L) → h.natAbs.Coprime m →
      ((S.image f).card : ℝ) ≤ Real.exp (3 * ε * L) →
      (∀ x ∈ S, f x * (root x : ℤ) ^ 2 = (m : ℤ) * x - h) →
      (∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ Real.exp L) →
      a * Real.exp (L / 2) / L ^ 6 ≤ S.card →
      (a / 2) * Real.exp (L / 2) / L ^ 6 ≤
        (populatedKernelPoints S f (fun u => |(u : ℝ)| ≤ Real.exp (η * L))
          (kernelSplitCutoff η L)).card := by
  filter_upwards [eventual_large_kernel_population_decay η ε (a / 4) hη hηU hε hεη (by positivity),
    eventual_small_kernel_fibers_decay η ε (a / 4) hη hεη (by positivity)] with L hbig hsmall
  intro S f root m h hm hmU hred hcount hroot hspan hsize
  have hb := hbig S f root m h hm hmU hred hcount hroot hspan
  have hs := hsmall S f hcount
  let R := populatedKernelPoints S f (fun u => |(u : ℝ)| ≤ Real.exp (η * L))
    (kernelSplitCutoff η L)
  have hcover : S ⊆ R ∪ (S.filter fun x => Real.exp (η * L) < |(f x : ℝ)|) ∪
      (S.filter fun x => (S.filter fun y => f y = f x).card < kernelSplitCutoff η L) := by
    intro x hx
    by_cases ha : |(f x : ℝ)| ≤ Real.exp (η * L)
    · by_cases hq : kernelSplitCutoff η L ≤ (S.filter fun y => f y = f x).card
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, ha, hq⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, Nat.lt_of_not_ge hq⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, lt_of_not_ge ha⟩))
  have hc := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have hc' := Finset.card_union_le R (S.filter fun x => Real.exp (η * L) < |(f x : ℝ)|)
  have hsum : (S.card : ℝ) ≤ R.card +
      (S.filter fun x => Real.exp (η * L) < |(f x : ℝ)|).card +
      (S.filter fun x => (S.filter fun y => f y = f x).card < kernelSplitCutoff η L).card := by
    exact_mod_cast (by omega : S.card ≤ R.card +
      (S.filter fun x => Real.exp (η * L) < |(f x : ℝ)|).card +
      (S.filter fun x => (S.filter fun y => f y = f x).card < kernelSplitCutoff η L).card)
  change (a / 2) * Real.exp (L / 2) / L ^ 6 ≤ (R.card : ℝ)
  ring_nf at hb hs hsize ⊢
  linarith only [hsize, hsum, hb, hs]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_RootCollisions
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Collisions of uniform root populations

The root populations at the end of §3 occupy translated intervals. Their
collision upper bound depends on the diameter and their cardinality.
-/

namespace Ostmann

open scoped BigOperators

theorem sum_uniform_mass (s : Finset ℕ) (hs : s.Nonempty) :
    (∑ _a ∈ s, (1 / (s.card : ℝ))) = 1 := by
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  simp only [Finset.sum_const, nsmul_eq_mul]
  exact mul_one_div_cancel hc

theorem uniformResidueCollision_lower (s : Finset ℕ) (hs : s.Nonempty)
    {p : ℕ} (hp : 0 < p) : 1 / (p : ℝ) ≤ uniformResidueCollision s p := by
  have hmass := residueMass_total s (fun _ => 1 / (s.card : ℝ)) hp
  rw [sum_uniform_mass s hs] at hmass
  have hrange : (Finset.range p).Nonempty := ⟨0, Finset.mem_range.mpr hp⟩
  simpa only [Finset.card_range, uniformResidueCollision] using
    inverse_card_le_collision (Finset.range p)
      (residueMass s (fun _ => 1 / (s.card : ℝ)) p) hrange hmass

theorem uniformResidueCollision_upper (P s : Finset ℕ) (hs : s.Nonempty)
    (D : ℕ) (hD : 1 ≤ D) (hP : ∀ p ∈ P, p.Prime)
    (hdiam : ∀ a ∈ s, ∀ b ∈ s, Nat.dist a b ≤ D) :
    (∑ p ∈ P, Real.log (p : ℝ) * uniformResidueCollision s p) ≤
      Real.log (D : ℝ) + (1 / (s.card : ℝ)) * ∑ p ∈ P, Real.log (p : ℝ) := by
  exact residue_collision_bound_of_diameter P s (fun _ => 1 / (s.card : ℝ)) D
    (1 / (s.card : ℝ)) hD hP hdiam (fun _ _ => by positivity)
    (sum_uniform_mass s hs) (fun _ _ => le_rfl)

/-- Disjoint residue images, after an injective relabeling on each side,
force the stronger lower bound at a split prime. -/
theorem uniformResidueCollision_lower_of_disjoint_images (s t : Finset ℕ)
    (hs : s.Nonempty) (ht : t.Nonempty) {p : ℕ} (hp : 0 < p)
    (f g : ℕ → ℕ)
    (hf : ∀ a ∈ s, f a < p) (hg : ∀ b ∈ t, g b < p)
    (hfc : ∀ a ∈ s, ∀ b ∈ s, f a = f b ↔ a ≡ b [MOD p])
    (hgc : ∀ a ∈ t, ∀ b ∈ t, g a = g b ↔ a ≡ b [MOD p])
    (hdisjoint : Disjoint (s.image f) (t.image g)) :
    4 / (p : ℝ) ≤ uniformResidueCollision s p + uniformResidueCollision t p := by
  classical
  let S := s.image f
  let T := t.image g
  have hS : S.Nonempty := hs.image f
  have hT : T.Nonempty := ht.image g
  have hmaps : ∀ a ∈ s, f a ∈ S := fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hmapt : ∀ a ∈ t, g a ∈ T := fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hcard : S.card + T.card ≤ p := by
    rw [← Finset.card_union_of_disjoint hdisjoint, ← Finset.card_range p]
    apply Finset.card_le_card
    intro r hr
    rcases Finset.mem_union.mp hr with hr | hr
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
      exact Finset.mem_range.mpr (hf a ha)
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
      exact Finset.mem_range.mpr (hg a ha)
  have hmasss : (∑ r ∈ S, fiberMass s (fun _ => 1 / (s.card : ℝ)) f r) = 1 := by
    rw [sum_fiberMass s S _ f hmaps]
    exact sum_uniform_mass s hs
  have hmasst : (∑ r ∈ T, fiberMass t (fun _ => 1 / (t.card : ℝ)) g r) = 1 := by
    rw [sum_fiberMass t T _ g hmapt]
    exact sum_uniform_mass t ht
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hTpos : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  have hcard' : (S.card : ℝ) + T.card ≤ p := by exact_mod_cast hcard
  calc
    _ ≤ 1 / (S.card : ℝ) + 1 / (T.card : ℝ) :=
      four_div_le_inverse_add_inverse hSpos hTpos hcard'
    _ ≤ (∑ r ∈ S, (fiberMass s (fun _ => 1 / (s.card : ℝ)) f r) ^ 2) +
        (∑ r ∈ T, (fiberMass t (fun _ => 1 / (t.card : ℝ)) g r) ^ 2) :=
      add_le_add (inverse_card_le_collision S _ hS hmasss)
        (inverse_card_le_collision T _ hT hmasst)
    _ = _ := by
      rw [fiberMass_sq_eq_residueMass_sq s S _ f hp hmaps hfc,
        fiberMass_sq_eq_residueMass_sq t T _ g hp hmapt hgc]
      rfl

/-- Multiplying one population by a nonzero field element preserves its
collision probability. Thus disjoint scaled root residues give `4 / p`. -/
theorem uniformResidueCollision_lower_of_scaled_disjoint {p : ℕ} [Fact p.Prime]
    (s t : Finset ℕ) (hs : s.Nonempty) (ht : t.Nonempty) (c : ZMod p) (hc : c ≠ 0)
    (hdisjoint : Disjoint (s.image (fun a : ℕ => (a : ZMod p)))
      (t.image (fun b : ℕ => c * (b : ZMod p)))) :
    4 / (p : ℝ) ≤ uniformResidueCollision s p + uniformResidueCollision t p := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  let f : ℕ → ℕ := fun a => (a : ZMod p).val
  let g : ℕ → ℕ := fun b => (c * (b : ZMod p)).val
  apply uniformResidueCollision_lower_of_disjoint_images s t hs ht hp f g
  · intro a _
    exact ZMod.val_lt _
  · intro b _
    exact ZMod.val_lt _
  · intro a _ b _
    exact (ZMod.val_injective p).eq_iff.trans (ZMod.natCast_eq_natCast_iff a b p)
  · intro a _ b _
    constructor
    · intro hab
      exact (ZMod.natCast_eq_natCast_iff a b p).mp
        (mul_left_cancel₀ hc (ZMod.val_injective p hab))
    · intro hab
      apply congrArg ZMod.val
      rw [(ZMod.natCast_eq_natCast_iff a b p).mpr hab]
  · apply Finset.disjoint_left.mpr
    intro r hr hs'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp hs'
    apply Finset.disjoint_left.mp hdisjoint
      (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    exact Finset.mem_image.mpr ⟨b, hb, ZMod.val_injective p heq⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_SplitCollision
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The final split-prime collision contradiction

Finite quantitative form of the last step in Proposition 3.1. The inputs
about which primes split and the root populations are intermediate claims
of that proposition, not published inputs and not asserted here.
-/

namespace Ostmann

open scoped BigOperators

/-- Split primes double the universal lower bound for the combined collision
probability of the two root populations. -/
theorem split_collision_lower_bound (P R : Finset ℕ) (β₁ β₂ : ℕ → ℝ)
    (hRP : R ⊆ P) (hP : ∀ p ∈ P, p.Prime)
    (hbase : ∀ p ∈ P, 2 / (p : ℝ) ≤ β₁ p + β₂ p)
    (hsplit : ∀ p ∈ R, 4 / (p : ℝ) ≤ β₁ p + β₂ p) :
    2 * (∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) +
      2 * (∑ p ∈ R, Real.log (p : ℝ) / (p : ℝ)) ≤
      ∑ p ∈ P, Real.log (p : ℝ) * (β₁ p + β₂ p) := by
  classical
  have hindicator :
      (∑ p ∈ P, if p ∈ R then Real.log (p : ℝ) / (p : ℝ) else 0) =
      ∑ p ∈ R, Real.log (p : ℝ) / (p : ℝ) := by
    rw [← Finset.sum_filter]
    congr 1
    exact Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr hRP)
  calc
    _ = ∑ p ∈ P, Real.log (p : ℝ) *
        (2 / (p : ℝ) + if p ∈ R then 2 / (p : ℝ) else 0) := by
      simp_rw [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
      have hfirst : (∑ p ∈ P, Real.log (p : ℝ) * (2 / (p : ℝ))) =
          2 * ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
      have hsecond : (∑ p ∈ P,
          if p ∈ R then Real.log (p : ℝ) * (2 / (p : ℝ)) else 0) =
          2 * ∑ p ∈ R, Real.log (p : ℝ) / (p : ℝ) := by
        rw [← hindicator, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        split_ifs <;> ring
      rw [hfirst, hsecond]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_left _
        (Real.log_nonneg (by exact_mod_cast (hP p hp).one_le))
      by_cases hpr : p ∈ R
      · simp only [hpr, ite_true, if_true]
        calc
          2 / (p : ℝ) + 2 / (p : ℝ) = 4 / (p : ℝ) := by ring
          _ ≤ β₁ p + β₂ p := hsplit p hpr
      · simp only [hpr, ite_false, if_false, add_zero]
        exact hbase p hp

/-- Explicit constants for the collision contradiction in Proposition 3.1.
Once the asymptotic errors are at most `L/100`, the log scale is bounded by
`50 C`; hence these hypotheses cannot persist on unbounded scales. -/
theorem split_collision_scale_bound (P R : Finset ℕ) (β₁ β₂ : ℕ → ℝ)
    (L η C : ℝ) (hRP : R ⊆ P) (hP : ∀ p ∈ P, p.Prime)
    (hbase : ∀ p ∈ P, 2 / (p : ℝ) ≤ β₁ p + β₂ p)
    (hsplit : ∀ p ∈ R, 4 / (p : ℝ) ≤ β₁ p + β₂ p)
    (hL : 0 ≤ L) (hη : η ≤ 1 / 1000)
    (hmertens : (1 / 2 - 5 * η) * L - C ≤
      ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ))
    (hsplitmass : (3 / 100) * L ≤ ∑ p ∈ R, Real.log (p : ℝ) / (p : ℝ))
    (hupper : (∑ p ∈ P, Real.log (p : ℝ) * (β₁ p + β₂ p)) ≤ (101 / 100) * L) :
    L ≤ 50 * C := by
  have hlower := split_collision_lower_bound P R β₁ β₂ hRP hP hbase hsplit
  have hηL := mul_le_mul_of_nonneg_right hη hL
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_RootContradiction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Combining the root-population collision bounds

This proves the final finite contradiction in §3 from the populations and
split-prime mass constructed earlier there. Their construction, including
the common rational center, remains a separate part of the argument.
-/

namespace Ostmann

open scoped BigOperators

theorem root_population_scale_bound (P R s t : Finset ℕ)
    (hs : s.Nonempty) (ht : t.Nonempty) (Ds Dt : ℕ)
    (hDs : 1 ≤ Ds) (hDt : 1 ≤ Dt)
    (hdiamS : ∀ a ∈ s, ∀ b ∈ s, Nat.dist a b ≤ Ds)
    (hdiamT : ∀ a ∈ t, ∀ b ∈ t, Nat.dist a b ≤ Dt)
    (L η C : ℝ) (hRP : R ⊆ P) (hP : ∀ p ∈ P, p.Prime)
    (c : (p : ℕ) → ZMod p) (hc : ∀ p ∈ R, c p ≠ 0)
    (hdisjoint : ∀ p ∈ R,
      Disjoint (s.image (fun a : ℕ => (a : ZMod p)))
        (t.image (fun b : ℕ => c p * (b : ZMod p))))
    (hL : 0 ≤ L) (hη : η ≤ 1 / 1000)
    (hmertens : (1 / 2 - 5 * η) * L - C ≤
      ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ))
    (hsplitmass : (3 / 100) * L ≤ ∑ p ∈ R, Real.log (p : ℝ) / (p : ℝ))
    (hbudget : Real.log (Ds : ℝ) + Real.log (Dt : ℝ) +
      (1 / (s.card : ℝ) + 1 / (t.card : ℝ)) * ∑ p ∈ P, Real.log (p : ℝ) ≤
        (101 / 100) * L) :
    L ≤ 50 * C := by
  apply split_collision_scale_bound P R (uniformResidueCollision s)
    (uniformResidueCollision t) L η C hRP hP
  · intro p hp
    have hp' := (hP p hp).pos
    calc
      2 / (p : ℝ) = 1 / (p : ℝ) + 1 / (p : ℝ) := by ring
      _ ≤ uniformResidueCollision s p + uniformResidueCollision t p :=
        add_le_add (uniformResidueCollision_lower s hs hp')
          (uniformResidueCollision_lower t ht hp')
  · intro p hp
    let : Fact p.Prime := ⟨hP p (hRP hp)⟩
    exact uniformResidueCollision_lower_of_scaled_disjoint s t hs ht (c p)
      (hc p hp) (hdisjoint p hp)
  · exact hL
  · exact hη
  · exact hmertens
  · exact hsplitmass
  · have hS := uniformResidueCollision_upper P s hs Ds hDs hP hdiamS
    have hT := uniformResidueCollision_upper P t ht Dt hDt hP hdiamT
    calc
      _ = (∑ p ∈ P, Real.log (p : ℝ) * uniformResidueCollision s p) +
          (∑ p ∈ P, Real.log (p : ℝ) * uniformResidueCollision t p) := by
        simp only [mul_add, Finset.sum_add_distrib]
      _ ≤ (Real.log (Ds : ℝ) + (1 / (s.card : ℝ)) * ∑ p ∈ P, Real.log (p : ℝ)) +
          (Real.log (Dt : ℝ) + (1 / (t.card : ℝ)) * ∑ p ∈ P, Real.log (p : ℝ)) :=
        add_le_add hS hT
      _ ≤ (101 / 100) * L := by linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_KernelPopulationCollision
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The collision estimate for the constructed quadratic root populations -/

namespace Ostmann

open scoped BigOperators

theorem kernel_populations_scale_bound (P R : Finset ℕ) (S T : Finset ℤ)
    (hSnon : S.Nonempty) (hTnon : T.Nonempty)
    (rootS rootT : ℤ → ℕ) (m Ds Dt : ℕ) (hm : 0 < m)
    (hDs : 1 ≤ Ds) (hDt : 1 ≤ Dt) (h u v : ℤ) (hu : u ≠ 0) (hv : v ≠ 0)
    (hS : ∀ x ∈ S, u * (rootS x : ℤ) ^ 2 = (m : ℤ) * x - h)
    (hT : ∀ y ∈ T, v * (rootT y : ℤ) ^ 2 = (m : ℤ) * y - h)
    (X : ℝ) (hspanS : ∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ X)
    (hspanT : ∀ x ∈ T, ∀ y ∈ T, |((x - y : ℤ) : ℝ)| ≤ X)
    (hdiamS : Real.sqrt ((m : ℝ) * X / |(u : ℝ)|) ≤ Ds)
    (hdiamT : Real.sqrt ((m : ℝ) * X / |(v : ℝ)|) ≤ Dt)
    (hprimeDiff : ∀ x ∈ S, ∀ y ∈ T, (x - y).natAbs.Prime)
    (L η C : ℝ) (hRP : R ⊆ P) (hP : ∀ p ∈ P, p.Prime)
    (c : (p : ℕ) → ZMod p)
    (hc : ∀ p ∈ R, (u : ZMod p) * c p ^ 2 = (v : ZMod p))
    (hpm : ∀ p ∈ R, ¬p ∣ m) (hpv : ∀ p ∈ R, ¬p ∣ v.natAbs)
    (hsmall : ∀ p ∈ R, ∀ x ∈ S, ∀ y ∈ T, p < (x - y).natAbs)
    (hL : 0 ≤ L) (hη : η ≤ 1 / 1000)
    (hmertens : (1 / 2 - 5 * η) * L - C ≤
      ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ))
    (hsplitmass : (3 / 100) * L ≤ ∑ p ∈ R, Real.log (p : ℝ) / (p : ℝ))
    (hbudget : Real.log (Ds : ℝ) + Real.log (Dt : ℝ) +
      (1 / (S.card : ℝ) + 1 / (T.card : ℝ)) * ∑ p ∈ P, Real.log (p : ℝ) ≤
        (101 / 100) * L) : L ≤ 50 * C := by
  classical
  have hcardS := kernelRootPopulation_card S rootS m hm h u hS
  have hcardT := kernelRootPopulation_card T rootT m hm h v hT
  apply root_population_scale_bound P R
    (kernelRootPopulation S rootS) (kernelRootPopulation T rootT)
    (hSnon.image rootS) (hTnon.image rootT) Ds Dt hDs hDt
    (kernelRootPopulation_diameter S rootS m Ds h u hu X hS hspanS hdiamS)
    (kernelRootPopulation_diameter T rootT m Dt h v hv X hT hspanT hdiamT)
    L η C hRP hP c
  · intro p hp hc0
    have hv0 : (v : ZMod p) = 0 := by simpa [hc0] using (hc p hp).symm
    have hdiv := (ZMod.intCast_zmod_eq_zero_iff_dvd v p).mp hv0
    exact hpv p hp (Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hdiv))
  · intro p hp
    let : Fact p.Prime := ⟨hP p (hRP hp)⟩
    exact kernelRootPopulation_residues_disjoint S T rootS rootT m h u v (c p)
      (hpm p hp) hS hT (hc p hp) hprimeDiff (hsmall p hp)
  · exact hL
  · exact hη
  · exact hmertens
  · exact hsplitmass
  · simpa only [hcardS, hcardT] using hbudget

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSplitRoot
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the actual rescaling at a split prime -/

namespace Ostmann

theorem exists_quadratic_split_root (u v : ℤ) {p : ℕ} (hp : p.Prime)
    (hpu : ¬p ∣ u.natAbs) (hsplit : jacobiSym (u * v) p = 1) :
    ∃ c : ZMod p, (u : ZMod p) * c ^ 2 = (v : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  have hu : (u : ZMod p) ≠ 0 := by
    intro hz
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd u p).mp hz
    exact hpu (Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hd))
  obtain ⟨r, hr⟩ := ZMod.isSquare_of_jacobiSym_eq_one hsplit
  refine ⟨r / (u : ZMod p), ?_⟩
  have hr' : r ^ 2 = (u : ZMod p) * (v : ZMod p) := by
    simpa only [Int.cast_mul, pow_two] using hr.symm
  field_simp
  rw [hr']

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticKernelCollision
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The collision contradiction on the actual quadratic split primes -/

namespace Ostmann

open scoped BigOperators Classical

theorem quadratic_split_avoid (P : Finset ℕ) (m : ℕ) (u v : ℤ)
    {p : ℕ} (hp : p ∈ quadraticSplitPrimes P m u v) :
    ¬p ∣ m ∧ ¬p ∣ u.natAbs ∧ ¬p ∣ v.natAbs := by
  have hn := (Finset.mem_filter.mp hp).2.1
  constructor
  · intro hd
    apply hn
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd 2) _) _
  constructor
  · intro hd
    apply hn
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd (2 * m)) _
  · intro hd
    exact hn (dvd_mul_of_dvd_right hd _)

/-- No choice of a square root is assumed: Jacobi splitting constructs the
rescaling and hence the disjoint residue populations at every retained prime. -/
theorem quadratic_kernel_collision_bound (P : Finset ℕ) (S T : Finset ℤ)
    (hSnon : S.Nonempty) (hTnon : T.Nonempty)
    (rootS rootT : ℤ → ℕ) (m Ds Dt : ℕ) (hm : 0 < m)
    (hDs : 1 ≤ Ds) (hDt : 1 ≤ Dt) (h u v : ℤ) (hu : u ≠ 0) (hv : v ≠ 0)
    (hS : ∀ x ∈ S, u * (rootS x : ℤ) ^ 2 = (m : ℤ) * x - h)
    (hT : ∀ y ∈ T, v * (rootT y : ℤ) ^ 2 = (m : ℤ) * y - h)
    (X : ℝ) (hspanS : ∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ X)
    (hspanT : ∀ x ∈ T, ∀ y ∈ T, |((x - y : ℤ) : ℝ)| ≤ X)
    (hdiamS : Real.sqrt ((m : ℝ) * X / |(u : ℝ)|) ≤ Ds)
    (hdiamT : Real.sqrt ((m : ℝ) * X / |(v : ℝ)|) ≤ Dt)
    (hprimeDiff : ∀ x ∈ S, ∀ y ∈ T, (x - y).natAbs.Prime)
    (L η C : ℝ) (hP : ∀ p ∈ P, p.Prime)
    (hsmall : ∀ p ∈ P, ∀ x ∈ S, ∀ y ∈ T, p < (x - y).natAbs)
    (hL : 0 ≤ L) (hη : η ≤ 1 / 1000)
    (hmertens : (1 / 2 - 5 * η) * L - C ≤ ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ))
    (hsplitmass : (3 / 100) * L ≤
      ∑ p ∈ quadraticSplitPrimes P m u v, Real.log (p : ℝ) / (p : ℝ))
    (hbudget : Real.log (Ds : ℝ) + Real.log (Dt : ℝ) +
      (1 / (S.card : ℝ) + 1 / (T.card : ℝ)) * ∑ p ∈ P, Real.log (p : ℝ) ≤
        (101 / 100) * L) : L ≤ 50 * C := by
  let R := quadraticSplitPrimes P m u v
  have hRP : R ⊆ P := Finset.filter_subset _ _
  have hex (p : R) : ∃ c : ZMod (p : ℕ), (u : ZMod (p : ℕ)) * c ^ 2 = (v : ZMod (p : ℕ)) :=
    exists_quadratic_split_root u v (hP p (hRP p.property))
      (quadratic_split_avoid P m u v p.property).2.1
      (Finset.mem_filter.mp p.property).2.2
  choose c hc using hex
  let c' (p : ℕ) : ZMod p := if hp : p ∈ R then c ⟨p, hp⟩ else 0
  apply kernel_populations_scale_bound P R S T hSnon hTnon rootS rootT m Ds Dt hm hDs hDt
    h u v hu hv hS hT X hspanS hspanT hdiamS hdiamT hprimeDiff L η C hRP hP c'
  · intro p hp
    simpa only [c', dite_eq_left hp] using hc ⟨p, hp⟩
  · intro p hp
    exact (quadratic_split_avoid P m u v hp).1
  · intro p hp
    exact (quadratic_split_avoid P m u v hp).2.2
  · intro p hp
    exact hsmall p (hRP hp)
  · exact hL
  · exact hη
  · exact hmertens
  · exact hsplitmass
  · exact hbudget

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSplitSupply
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform split-prime supply outside the explicit exceptional family -/

namespace Ostmann

open scoped BigOperators Classical

/-- All analytic error conditions are discharged by fixed constants and
explicit integer cutoffs. Here L=log X, and the Page threshold is L^100. -/
theorem quadratic_split_supply (P : PublishedProgressionInput)
    (H : PublishedRealZeroInput P) (hSiegel : PublishedSiegelBound) :
    ∃ η L₀ : ℝ, 0 < η ∧ η ≤ 1 / 1000 ∧ 0 < L₀ ∧
      ∀ L : ℝ, L₀ ≤ L → ∀ (d : ℤ) (D : ℕ),
        Squarefree d.natAbs → d ≠ 0 →
        (d.natAbs : ℝ) ≤ Real.exp (2 * η * L) →
        0 < D → d.natAbs ∣ D → Real.log D ≤ L →
        d ∉ pageKernelExclusion P (kernelConductorCutoff η L) (L ^ (100 : ℕ)) →
        (3 / 100 : ℝ) * L ≤
          ∑ p ∈ (Nat.primesLE (kernelSplitCutoff η L)).filter
            (fun p => ¬p ∣ D ∧ jacobiSym d p = 1), Real.log p / (p : ℝ) := by
  obtain ⟨A, K, C, hA, hK, hC, hmass⟩ :=
    all_kernel_split_prime_mass P H hSiegel (1 / 200) (by norm_num)
  let Cz := zeroComparisonConstant P
  have hCz5 : 5 ≤ Cz := le_max_left _ _
  have hCz : 0 ≤ Cz := by linarith
  obtain ⟨η, hη, hηsmall, hηeq⟩ := exists_kernel_size_exponent Cz hCz5
  let B₀ := 2 * Cz * Real.log 20 + H.errorConstant + A + 2
  let L₀ := max 100 (max (10000 * C) (max ((40000 * K) ^ 2)
    (max (40000 * B₀) (max ((40000 : ℝ) ^ 2)
      (max ((A + H.errorConstant) / η) (20 * Real.log 20))))))
  have hL₀ : 0 < L₀ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 100) (le_max_left _ _)
  refine ⟨η, L₀, hη, hηsmall, hL₀, ?_⟩
  intro L hL d D hsf hd hdsize hD hdD hlogD hout
  have hb : 100 ≤ L ∧ 10000 * C ≤ L ∧ (40000 * K) ^ 2 ≤ L ∧
      40000 * B₀ ≤ L ∧ (40000 : ℝ) ^ 2 ≤ L ∧
      (A + H.errorConstant) / η ≤ L ∧ 20 * Real.log 20 ≤ L := by
    simpa only [L₀, max_le_iff] using hL
  obtain ⟨h100, hCs, hKs, hBs, hLs, hAs, hlogs⟩ := hb
  have hLpos : 0 < L := by linarith
  have hc := kernelConductorCutoff_bounds η L hη.le hLpos.le
  have hq := kernelSplitCutoff_bounds η L hηsmall h100
  have hy := kernelDivisorCutoff_bounds L hLpos
  have hcover := kernelConductorCutoff_covers η L d hdsize
  have hlogpos : 0 < Real.log (4 * (kernelConductorCutoff η L : ℝ)) :=
    lt_of_lt_of_le (by positivity : 0 < 2 * η * L) hc.2.1
  have hsize : 2 * (A + H.errorConstant) ≤
      Real.log (4 * (kernelConductorCutoff η L : ℝ)) := by
    have ha' := (div_le_iff₀ hη).mp hAs
    nlinarith [hc.2.1]
  have hlogupper : Real.log (4 * (kernelConductorCutoff η L : ℝ)) ≤ L / 10 := by
    have heta := mul_le_mul_of_nonneg_right hηsmall hLpos.le
    linarith [hc.2.2]
  have hss : 1 + 10 / L ≤ 1 + 1 / Real.log (4 * (kernelConductorCutoff η L : ℝ)) := by
    have hh : 10 / L ≤ 1 / Real.log (4 * (kernelConductorCutoff η L : ℝ)) :=
      (div_le_div_iff₀ hLpos hlogpos).mpr (by linarith)
    linarith
  have hs : 1 < 1 + 10 / L := by
    have hh : 0 < 10 / L := by positivity
    linarith
  have hs2 : 1 + 10 / L ≤ 2 := by
    have hh : 10 / L ≤ (1 : ℝ) := (div_le_one hLpos).mpr (by linarith)
    linarith
  have hbase := hmass d (kernelConductorCutoff η L) (kernelSplitCutoff η L) D
    (kernelDivisorCutoff L) (L ^ (100 : ℕ)) (1 + 10 / L)
    hsf hd hc.1 hcover hq.1 hD hy.1 hdD (by positivity) hsize hs hs2 hss hout
  have hCsmall : C ≤ L / 10000 := by linarith
  have hBsmall : 2 * Cz * Real.log (4 * (kernelConductorCutoff η L : ℝ)) +
      K * (L ^ (100 : ℕ)) ^ (1 / 200 : ℝ) + H.errorConstant + A + 2 ≤ L / 10000 := by
    rw [page_threshold_siegel_power L hLpos.le]
    apply kernel_zero_error_absorption Cz η K A H.errorConstant L _ hCz hK.le hLpos.le
      hηeq.le hc.2.2 hKs
    exact hBs
  have hEsmall : (kernelDivisorCutoff L : ℝ) + Real.log D / kernelDivisorCutoff L ≤ L / 10000 :=
    kernel_divisor_error_absorption D (kernelDivisorCutoff L) L hLpos hLs hy.2.1 hy.2.2 hlogD
  exact split_prime_mass_of_small_errors d D (kernelSplitCutoff η L) (kernelDivisorCutoff L)
    L C _ hLpos hq.1 hC.le hCsmall hBsmall hEsmall hq.2 hbase

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_RootPopulationBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A concrete diameter and collision budget for large root populations -/

namespace Ostmann

open scoped BigOperators

theorem naturalRootDiameter_bounds (m : ℕ) (L η : ℝ) (hm : 0 < m) (hL : 0 ≤ L)
    (hmupper : (m : ℝ) ≤ Real.exp (η * L)) :
    1 ≤ naturalRootDiameter m L ∧
      Real.sqrt ((m : ℝ) * Real.exp L) ≤ naturalRootDiameter m L ∧
      Real.log (naturalRootDiameter m L : ℝ) ≤ Real.log 2 + (1 + η) * L / 2 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have he1 := Real.one_le_exp hL
  have hx1 : (1 : ℝ) ≤ (m : ℝ) * Real.exp L := one_le_mul_of_one_le_of_one_le hm1 he1
  have hr1 : (1 : ℝ) ≤ Real.sqrt ((m : ℝ) * Real.exp L) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hx1
  have hroot : Real.sqrt ((m : ℝ) * Real.exp L) ≤ (naturalRootDiameter m L : ℝ) := Nat.le_ceil _
  have hn1 : (1 : ℝ) ≤ naturalRootDiameter m L := hr1.trans hroot
  refine ⟨by exact_mod_cast hn1, hroot, ?_⟩
  have hceil : (naturalRootDiameter m L : ℝ) ≤ 2 * Real.sqrt ((m : ℝ) * Real.exp L) := by
    have hh : (naturalRootDiameter m L : ℝ) < Real.sqrt ((m : ℝ) * Real.exp L) + 1 :=
      Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
    linarith
  have hl := Real.log_le_log (show (0 : ℝ) < naturalRootDiameter m L by linarith) hceil
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt (by linarith :
    0 < Real.sqrt ((m : ℝ) * Real.exp L))), Real.log_sqrt (by positivity),
    Real.log_mul hm0.ne' (Real.exp_ne_zero _), Real.log_exp] at hl
  have hlogm := (Real.log_le_iff_le_exp hm0).mpr hmupper
  linarith

theorem naturalRootDiameter_dominates (m : ℕ) (L : ℝ) (u : ℤ)
    (hm : 0 < m) (hu : u ≠ 0) :
    Real.sqrt ((m : ℝ) * Real.exp L / |(u : ℝ)|) ≤ naturalRootDiameter m L := by
  have hu1 : (1 : ℝ) ≤ |(u : ℝ)| := by
    have hh : (1 : ℝ) ≤ u.natAbs := by exact_mod_cast Int.natAbs_pos.mpr hu
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hh
  have hnon : 0 ≤ (m : ℝ) * Real.exp L := by positivity
  apply le_trans (Real.sqrt_le_sqrt (div_le_self hnon hu1))
  exact Nat.le_ceil _

/-- Cardinalities at least Q make the two sampling losses at most 2 log 4.
The diameter loss then leaves the manuscript's 1.01L budget. -/
theorem root_population_collision_budget (m Q a b : ℕ) (L η : ℝ)
    (hm : 0 < m) (hQ : 0 < Q) (hL : 1000 ≤ L) (hη : η ≤ 1 / 1000)
    (hmupper : (m : ℝ) ≤ Real.exp (η * L)) (ha : Q ≤ a) (hb : Q ≤ b) :
    2 * Real.log (naturalRootDiameter m L : ℝ) +
      (1 / (a : ℝ) + 1 / (b : ℝ)) * ∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) ≤
        (101 / 100 : ℝ) * L := by
  have hd := (naturalRootDiameter_bounds m L η hm (by linarith) hmupper).2.2
  have hQp : (0 : ℝ) < Q := by exact_mod_cast hQ
  have haR : (Q : ℝ) ≤ a := by exact_mod_cast ha
  have hbR : (Q : ℝ) ≤ b := by exact_mod_cast hb
  have hap : (0 : ℝ) < a := hQp.trans_le haR
  have hbp : (0 : ℝ) < b := hQp.trans_le hbR
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hsum := prime_log_weight_le Q
  have hfirst : (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ)) / a ≤ Real.log 4 := by
    apply (div_le_iff₀ hap).mpr
    exact hsum.trans (mul_le_mul_of_nonneg_left haR hlog4)
  have hsecond : (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ)) / b ≤ Real.log 4 := by
    apply (div_le_iff₀ hbp).mpr
    exact hsum.trans (mul_le_mul_of_nonneg_left hbR hlog4)
  have hsampling : (1 / (a : ℝ) + 1 / (b : ℝ)) *
      (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ)) ≤ 2 * Real.log 4 := by
    calc
      _ = (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ)) / a +
          (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ)) / b := by ring
      _ ≤ _ := by linarith
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlog4u := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
  have heta := mul_le_mul_of_nonneg_right hη (show 0 ≤ L by linarith)
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticPopulationContradiction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The large nonexceptional quadratic populations are impossible

The collision estimate uses the integer prime cutoff and the quadratic
split-prime estimate. Root equations, separation, and population sizes
supply its geometric hypotheses.
-/

namespace Ostmann

open scoped BigOperators Classical

theorem small_kernel_le_split_cutoff (η L : ℝ) (u : ℤ)
    (hη : η ≤ 1 / 1000) (hL : 0 ≤ L)
    (hu : (u.natAbs : ℝ) ≤ Real.exp (η * L)) :
    u.natAbs ≤ kernelSplitCutoff η L := by
  apply Nat.le_floor
  apply hu.trans
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right hη hL
  nlinarith

theorem small_kernel_product_bounds (η L : ℝ) (m : ℕ) (u v : ℤ)
    (hm : 0 < m) (hu : u ≠ 0) (hv : v ≠ 0)
    (hL : 1000 ≤ L) (hη : η ≤ 1 / 1000)
    (hmupper : (m : ℝ) ≤ Real.exp (η * L))
    (huupper : (u.natAbs : ℝ) ≤ Real.exp (η * L))
    (hvupper : (v.natAbs : ℝ) ≤ Real.exp (η * L)) :
    ((u * v).natAbs : ℝ) ≤ Real.exp (2 * η * L) ∧
      0 < 2 * m * u.natAbs * v.natAbs ∧
      (u * v).natAbs ∣ 2 * m * u.natAbs * v.natAbs ∧
      Real.log (2 * m * u.natAbs * v.natAbs : ℕ) ≤ L := by
  have hu0 : 0 < u.natAbs := Int.natAbs_pos.mpr hu
  have hv0 : 0 < v.natAbs := Int.natAbs_pos.mpr hv
  have hp : (u.natAbs : ℝ) * v.natAbs ≤ Real.exp (2 * η * L) := by
    calc
      _ ≤ Real.exp (η * L) * Real.exp (η * L) :=
        mul_le_mul huupper hvupper (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  refine ⟨by simpa only [Int.natAbs_mul, Nat.cast_mul] using hp, by positivity, ?_, ?_⟩
  · rw [Int.natAbs_mul]
    exact ⟨2 * m, by ring⟩
  · have hsize : (2 * m * u.natAbs * v.natAbs : ℕ) ≤ (2 : ℝ) * Real.exp (3 * η * L) := by
      push_cast
      calc
        _ = 2 * ((m : ℝ) * (u.natAbs * v.natAbs)) := by ring
        _ ≤ 2 * (Real.exp (η * L) * Real.exp (2 * η * L)) := by
          gcongr
        _ = _ := by rw [← Real.exp_add]; congr 2; ring
    have hpos : (0 : ℝ) < (2 * m * u.natAbs * v.natAbs : ℕ) := by positivity
    have hl := Real.log_le_log hpos hsize
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp] at hl
    have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have heta := mul_le_mul_of_nonneg_right hη (show 0 ≤ L by linarith)
    linarith

/-- For all sufficiently large scales, two separated prime-difference
populations cannot both exceed the split cutoff while carrying small,
nonexceptional squarefree kernels about one reduced rational center. -/
theorem no_large_nonexceptional_quadratic_populations (P : PublishedProgressionInput)
    (H : PublishedRealZeroInput P) (hSiegel : PublishedSiegelBound)
    (C : ℝ) (hM : MertensLowerBound C) :
    ∃ η L₁ : ℝ, 0 < η ∧ η ≤ 1 / 1000 ∧ 0 < L₁ ∧
      ∀ L : ℝ, L₁ ≤ L → ∀ (S T : Finset ℤ) (rootS rootT : ℤ → ℕ)
        (m : ℕ) (h u v : ℤ),
        0 < m → h.natAbs.Coprime m → u ≠ 0 → v ≠ 0 →
        Squarefree u.natAbs → Squarefree v.natAbs →
        (m : ℝ) ≤ Real.exp (η * L) →
        (u.natAbs : ℝ) ≤ Real.exp (η * L) →
        (v.natAbs : ℝ) ≤ Real.exp (η * L) →
        (∀ x ∈ S, u * (rootS x : ℤ) ^ 2 = (m : ℤ) * x - h) →
        (∀ y ∈ T, v * (rootT y : ℤ) ^ 2 = (m : ℤ) * y - h) →
        (∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ Real.exp L) →
        (∀ x ∈ T, ∀ y ∈ T, |((x - y : ℤ) : ℝ)| ≤ Real.exp L) →
        (∀ x ∈ S, ∀ y ∈ T, (x - y).natAbs.Prime ∧
          kernelSplitCutoff η L < (x - y).natAbs) →
        u * v ∉ pageKernelExclusion P (kernelConductorCutoff η L) (L ^ (100 : ℕ)) →
        kernelSplitCutoff η L ≤ S.card → kernelSplitCutoff η L ≤ T.card → False := by
  obtain ⟨η, L₀, hηpos, hη, hL₀, hsupply⟩ := quadratic_split_supply P H hSiegel
  let L₁ := max L₀ (max 1000 (50 * (C + 1) + 1))
  refine ⟨η, L₁, hηpos, hη, lt_of_lt_of_le hL₀ (le_max_left _ _), ?_⟩
  intro L hL S T rootS rootT m h u v hm hred hu hv husf hvsf hmupper huupper hvupper
    hS hT hspanS hspanT hcross hout hScard hTcard
  have hLbase : L₀ ≤ L := (le_max_left _ _).trans hL
  have h1000 : 1000 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hlarge : 50 * (C + 1) + 1 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hQ := (kernelSplitCutoff_bounds η L hη (by linarith)).1
  have hSnon : S.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hQ hScard)
  have hTnon : T.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hQ hTcard)
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (lt_of_lt_of_le hQ hScard)
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (lt_of_lt_of_le hQ hTcard)
  have hucut := small_kernel_le_split_cutoff η L u hη (by linarith) huupper
  have hcop : u.natAbs.Coprime v.natAbs := quadratic_kernels_coprime m h x y u v
    (rootS x) (rootT y) hu hred (hS x hx) (hT y hy) (hcross x hx y hy).1
    (hucut.trans_lt (hcross x hx y hy).2)
  have hsf : Squarefree (u * v).natAbs := by
    rw [Int.natAbs_mul]
    exact squarefree_mul_iff.mpr ⟨Nat.coprime_iff_isRelPrime.mp hcop, husf, hvsf⟩
  have hb := small_kernel_product_bounds η L m u v hm hu hv h1000 hη hmupper huupper hvupper
  have hmass := hsupply L hLbase (u * v) (2 * m * u.natAbs * v.natAbs)
    hsf (mul_ne_zero hu hv) hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 hout
  have hmertens : (1 / 2 - 5 * η) * L - (C + 1) ≤
      ∑ p ∈ Nat.primesLE (kernelSplitCutoff η L), Real.log (p : ℝ) / (p : ℝ) := by
    have hlo := kernelSplitCutoff_log_lower η L hη (by linarith)
    have hm' := hM (kernelSplitCutoff η L) hQ
    linarith
  have hd := naturalRootDiameter_bounds m L η hm (by linarith) hmupper
  have hbudget := root_population_collision_budget m (kernelSplitCutoff η L) S.card T.card
    L η hm hQ h1000 hη hmupper hScard hTcard
  have hcontr := quadratic_kernel_collision_bound (Nat.primesLE (kernelSplitCutoff η L))
    S T hSnon hTnon rootS rootT m (naturalRootDiameter m L) (naturalRootDiameter m L)
    hm hd.1 hd.1 h u v hu hv hS hT (Real.exp L) hspanS hspanT
    (naturalRootDiameter_dominates m L u hm hu)
    (naturalRootDiameter_dominates m L v hm hv)
    (fun x hx y hy => (hcross x hx y hy).1) L η (C + 1)
    (fun _ hp => Nat.prime_of_mem_primesLE hp)
    (fun p hp x hx y hy => (Nat.le_of_mem_primesLE hp).trans_lt (hcross x hx y hy).2)
    (by linarith) hη hmertens hmass (by simpa only [two_mul] using hbudget)
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_PageKernelPopulation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Population cost of deleting the large Page-kernel family -/

namespace Ostmann

/-- The threshold R replaces the actual exceptional conductor uniformly.
At R=(log X)^100 the leading cost is X/(log X)^50. -/
theorem exists_page_kernel_population_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : PublishedProgressionInput) (Q₀ : ℕ) (R : ℝ)
      (S T : Finset ℤ) (f g : ℤ → ℤ) (r s : ℤ → ℕ) (m : ℕ) (h : ℤ) (X : ℝ),
      0 < R → 0 < m → 0 ≤ X →
      (∀ x ∈ S, f x ≠ 0) → (∀ y ∈ T, g y ≠ 0) →
      h.natAbs.Coprime m →
      (∀ x ∈ S, f x * (r x : ℤ) ^ 2 = (m : ℤ) * x - h) →
      (∀ y ∈ T, g y * (s y : ℤ) ^ 2 = (m : ℤ) * y - h) →
      (∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ X) →
      (∀ x ∈ T, ∀ y ∈ T, |((x - y : ℤ) : ℝ)| ≤ X) →
      (∀ x ∈ S, ∀ y ∈ T, (f x).natAbs.Coprime (g y).natAbs) →
      (((S.product T).filter fun z => f z.1 * g z.2 ∈ pageKernelExclusion P Q₀ R).card : ℝ) ≤
        C * (X / Real.sqrt R + 2 * Real.sqrt (X * m) + m) := by
  obtain ⟨C, hC, hbound⟩ := exists_exceptional_kernel_family_bound
  refine ⟨C, hC, ?_⟩
  intro P Q₀ R S T f g r s m h X hR hm hX hf hg hred hr hs hspanS hspanT hcross
  apply page_kernel_exclusion_count P Q₀ R _ S T f g (by positivity)
  intro q hq
  have hqpos : 0 < q := by
    have hh : (0 : ℝ) < q := hR.trans hq
    exact_mod_cast hh
  have hb := hbound S T f g r s m q h X hm hqpos hX hf hg hred hr hs hspanS hspanT hcross
  have hquot : X / Real.sqrt (q : ℝ) ≤ X / Real.sqrt R :=
    div_le_div_of_nonneg_left hX (Real.sqrt_pos.mpr hR) (Real.sqrt_le_sqrt hq.le)
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_PagePopulationDecay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Decay of the exceptional Page-kernel population

At the manuscript's threshold `R = (log X)^100`, the already proved
population bound is smaller than `X / (log X)^40`, uniformly in the
small common-center denominator. No analytic estimate is added here.
-/

namespace Ostmann

open Filter Asymptotics

/-- One cutoff absorbs both square-root population errors uniformly for all
denominators bounded by `exp(η L)`, with `η ≤ 1/1000`. -/
theorem exists_page_population_error_cutoff :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L η : ℝ, L₀ ≤ L → η ≤ 1 / 1000 →
      ∀ m : ℕ, (m : ℝ) ≤ Real.exp (η * L) →
        Real.exp L / Real.sqrt (L ^ (100 : ℕ)) +
            2 * Real.sqrt (Real.exp L * m) + m ≤
          4 * (Real.exp L / L ^ (40 : ℕ)) := by
  have hpoly := (isLittleO_pow_exp_pos_mul_atTop 40
    (by norm_num : (0 : ℝ) < 1 / 4)).bound (by norm_num : (0 : ℝ) < 1)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hpoly
  refine ⟨max 1 M, le_max_left _ _, ?_⟩
  intro L η hL hη m hm
  have hL1 : 1 ≤ L := (le_max_left 1 M).trans hL
  have hL0 : 0 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hM' := hM L ((le_max_right 1 M).trans hL)
  have hpower : L ^ (40 : ℕ) ≤ Real.exp ((1 / 4 : ℝ) * L) := by
    apply (le_abs_self (L ^ (40 : ℕ))).trans
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul] using hM'
  have hmain : Real.exp ((3 / 4 : ℝ) * L) ≤ Real.exp L / L ^ (40 : ℕ) := by
    apply (le_div_iff₀ (pow_pos hLp 40)).mpr
    have h := mul_le_mul_of_nonneg_left hpower
      (Real.exp_pos ((3 / 4 : ℝ) * L)).le
    rw [← Real.exp_add] at h
    have hsum : (3 / 4 : ℝ) * L + (1 / 4 : ℝ) * L = L := by ring
    rwa [hsum] at h
  have hmhalf : (m : ℝ) ≤ Real.exp ((1 / 2 : ℝ) * L) := by
    apply hm.trans
    apply Real.exp_le_exp.mpr
    nlinarith
  have hmthree : (m : ℝ) ≤ Real.exp ((3 / 4 : ℝ) * L) := by
    apply hm.trans
    apply Real.exp_le_exp.mpr
    nlinarith
  have hsqrt : Real.sqrt (Real.exp L * m) ≤ Real.exp ((3 / 4 : ℝ) * L) := by
    have hmul := mul_le_mul_of_nonneg_left hmhalf (Real.exp_pos L).le
    have h := Real.sqrt_le_sqrt hmul
    have heq : Real.exp L * Real.exp ((1 / 2 : ℝ) * L) =
        (Real.exp ((3 / 4 : ℝ) * L)) ^ 2 := by
      rw [← Real.exp_add, ← Real.exp_nat_mul]
      congr 1
      ring
    rw [heq, Real.sqrt_sq (Real.exp_pos _).le] at h
    exact h
  have hsqrt100 : Real.sqrt (L ^ (100 : ℕ)) = L ^ (50 : ℕ) := by
    rw [show L ^ (100 : ℕ) = (L ^ (50 : ℕ)) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hleading : Real.exp L / Real.sqrt (L ^ (100 : ℕ)) ≤
      Real.exp L / L ^ (40 : ℕ) := by
    rw [hsqrt100]
    exact div_le_div_of_nonneg_left (Real.exp_pos L).le (pow_pos hLp 40)
      (pow_le_pow_right₀ hL1 (by omega : 40 ≤ 50))
  have hsqrt' := hsqrt.trans hmain
  have hm' := hmthree.trans hmain
  linarith

/-- The actual exceptional pair family at `R = L^100` has negligible
population on the endpoint-product scale `exp L / L^6`. The exponent forty
retains a fixed reserve for the subsequent common-center selections. -/
theorem exists_page_population_decay :
    ∃ C L₀ : ℝ, 0 < C ∧ 1 ≤ L₀ ∧
      ∀ (P : PublishedProgressionInput) (Q₀ : ℕ) (L η : ℝ),
      L₀ ≤ L → η ≤ 1 / 1000 →
      ∀ (S T : Finset ℤ) (f g : ℤ → ℤ) (r s : ℤ → ℕ) (m : ℕ) (h : ℤ),
      0 < m → (m : ℝ) ≤ Real.exp (η * L) →
      (∀ x ∈ S, f x ≠ 0) → (∀ y ∈ T, g y ≠ 0) →
      h.natAbs.Coprime m →
      (∀ x ∈ S, f x * (r x : ℤ) ^ 2 = (m : ℤ) * x - h) →
      (∀ y ∈ T, g y * (s y : ℤ) ^ 2 = (m : ℤ) * y - h) →
      (∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ Real.exp L) →
      (∀ x ∈ T, ∀ y ∈ T, |((x - y : ℤ) : ℝ)| ≤ Real.exp L) →
      (∀ x ∈ S, ∀ y ∈ T, (f x).natAbs.Coprime (g y).natAbs) →
      (((S.product T).filter fun z =>
        f z.1 * g z.2 ∈ pageKernelExclusion P Q₀ (L ^ (100 : ℕ))).card : ℝ) ≤
        C * (Real.exp L / L ^ (40 : ℕ)) := by
  obtain ⟨C, hC, hbound⟩ := exists_page_kernel_population_bound
  obtain ⟨L₀, hL₀, hcut⟩ := exists_page_population_error_cutoff
  refine ⟨4 * C, L₀, by positivity, hL₀, ?_⟩
  intro P Q₀ L η hL hη S T f g r s m h hm hmupper hf hg hred hr hs hspanS hspanT hcross
  have hLp : 0 < L := lt_of_lt_of_le (by linarith : (0 : ℝ) < L₀) hL
  have hb := hbound P Q₀ (L ^ (100 : ℕ)) S T f g r s m h (Real.exp L)
    (pow_pos hLp 100) hm (Real.exp_pos L).le hf hg hred hr hs hspanS hspanT hcross
  calc
    _ ≤ C * (Real.exp L / Real.sqrt (L ^ (100 : ℕ)) +
        2 * Real.sqrt (Real.exp L * m) + m) := hb
    _ ≤ C * (4 * (Real.exp L / L ^ (40 : ℕ))) :=
      mul_le_mul_of_nonneg_left (hcut L η hL hη m hmupper) hC.le
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PagePairCapacity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Endpoint products dominate the exceptional Page population -/

namespace Ostmann

open Filter

theorem eventual_page_pair_capacity (a C : ℝ) (ha : 0 < a) :
    ∀ᶠ L : ℝ in atTop,
      C * (Real.exp L / L ^ 40) < (a * Real.exp (L / 2) / L ^ 6) ^ 2 := by
  have hp : ∀ᶠ L : ℝ in atTop, C / a ^ 2 < L ^ 28 :=
    (tendsto_pow_atTop (by norm_num : (28 : ℕ) ≠ 0)).eventually_gt_atTop (C / a ^ 2)
  filter_upwards [hp, eventually_gt_atTop (0 : ℝ)] with L hpower hL
  have hmain : C < a ^ 2 * L ^ 28 := by
    have hh := (div_lt_iff₀ (pow_pos ha 2)).mp hpower
    simpa only [mul_comm] using hh
  have he : Real.exp L = (Real.exp (L / 2)) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; norm_num; ring
  have hfactor : 0 < Real.exp L / L ^ 40 := div_pos (Real.exp_pos L) (pow_pos hL 40)
  have hmul := mul_lt_mul_of_pos_right hmain hfactor
  have hid : a ^ 2 * L ^ 28 * (Real.exp L / L ^ 40) =
      (a * Real.exp (L / 2) / L ^ 6) ^ 2 := by
    rw [he]
    field_simp
  rwa [hid] at hmul

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_FewKernelContradiction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Few squarefree kernels cannot support two large prime-difference sets

The kernel-count hypotheses are geometric intermediate data. The contradiction
uses only the previously identified published analytic inputs.
-/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem few_kernel_populations_impossible (P : PublishedProgressionInput)
    (H : PublishedRealZeroInput P) (hSiegel : PublishedSiegelBound)
    (C : ℝ) (hM : MertensLowerBound C) (a : ℝ) (ha : 0 < a) :
    ∃ η L₀ : ℝ, 0 < η ∧ η ≤ 1 / 1000 ∧ 0 < L₀ ∧
      ∀ L : ℝ, L₀ ≤ L → ∀ (S T : Finset ℤ) (f g : ℤ → ℤ)
        (r s : ℤ → ℕ) (m : ℕ) (h : ℤ),
        0 < m → (m : ℝ) ≤ Real.exp (η * L) → h.natAbs.Coprime m →
        ((S.image f).card : ℝ) ≤ Real.exp (3 * (η / 100) * L) →
        ((T.image g).card : ℝ) ≤ Real.exp (3 * (η / 100) * L) →
        (∀ x ∈ S, f x ≠ 0 ∧ Squarefree (f x).natAbs ∧
          f x * (r x : ℤ) ^ 2 = (m : ℤ) * x - h) →
        (∀ y ∈ T, g y ≠ 0 ∧ Squarefree (g y).natAbs ∧
          g y * (s y : ℤ) ^ 2 = (m : ℤ) * y - h) →
        (∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ Real.exp L) →
        (∀ x ∈ T, ∀ y ∈ T, |((x - y : ℤ) : ℝ)| ≤ Real.exp L) →
        (∀ x ∈ S, ∀ y ∈ T, (x - y).natAbs.Prime ∧
          kernelSplitCutoff η L < (x - y).natAbs) →
        a * Real.exp (L / 2) / L ^ 6 ≤ S.card →
        a * Real.exp (L / 2) / L ^ 6 ≤ T.card → False := by
  obtain ⟨η, L₁, hη, hηU, hL₁, hno⟩ :=
    no_large_nonexceptional_quadratic_populations P H hSiegel C hM
  obtain ⟨E, L₂, hE, hL₂, hpage⟩ := exists_page_population_decay
  have hret := eventual_populated_kernel_retention η (η / 100) a hη hηU
    (by positivity) le_rfl ha
  have hcap := eventual_page_pair_capacity (a / 2) E (by positivity)
  obtain ⟨L₃, hL₃⟩ := eventually_atTop.mp (hret.and hcap)
  let L₀ := max L₁ (max L₂ (max L₃ 1000))
  refine ⟨η, L₀, hη, hηU, lt_of_lt_of_le hL₁ (le_max_left _ _), ?_⟩
  intro L hL S T f g r s m h hm hmU hred hcountS hcountT hf hg hspanS hspanT hcross hsizeS hsizeT
  have hLbase : L₁ ≤ L := (le_max_left _ _).trans hL
  have hLpage : L₂ ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLret : L₃ ≤ L := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
  have hL1000 : 1000 ≤ L := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
  have hLpos : 0 < L := by linarith
  let U := populatedKernelPoints S f (fun u => |(u : ℝ)| ≤ Real.exp (η * L))
    (kernelSplitCutoff η L)
  let V := populatedKernelPoints T g (fun v => |(v : ℝ)| ≤ Real.exp (η * L))
    (kernelSplitCutoff η L)
  have hUS : U ⊆ S := populatedKernelPoints_subset _ _ _ _
  have hVT : V ⊆ T := populatedKernelPoints_subset _ _ _ _
  have hsmallS (x : ℤ) (hx : x ∈ U) : ((f x).natAbs : ℝ) ≤ Real.exp (η * L) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using (Finset.mem_filter.mp hx).2.1
  have hsmallT (y : ℤ) (hy : y ∈ V) : ((g y).natAbs : ℝ) ≤ Real.exp (η * L) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using (Finset.mem_filter.mp hy).2.1
  have hcop (x : ℤ) (hx : x ∈ U) (y : ℤ) (hy : y ∈ V) :
      (f x).natAbs.Coprime (g y).natAbs := by
    apply quadratic_kernels_coprime m h x y (f x) (g y) (r x) (s y)
      (hf x (hUS hx)).1 hred (hf x (hUS hx)).2.2 (hg y (hVT hy)).2.2
      (hcross x (hUS hx) y (hVT hy)).1
    exact (small_kernel_le_split_cutoff η L (f x) hηU hLpos.le (hsmallS x hx)).trans_lt
      (hcross x (hUS hx) y (hVT hy)).2
  have hbad := hpage P (kernelConductorCutoff η L) L η hLpage hηU U V f g r s m h hm hmU
    (fun x hx => (hf x (hUS hx)).1) (fun y hy => (hg y (hVT hy)).1) hred
    (fun x hx => (hf x (hUS hx)).2.2) (fun y hy => (hg y (hVT hy)).2.2)
    (fun x hx y hy => hspanS x (hUS hx) y (hUS hy))
    (fun x hx y hy => hspanT x (hVT hx) y (hVT hy)) hcop
  have hretain := (hL₃ L hLret).1
  have hU : (a / 2) * Real.exp (L / 2) / L ^ 6 ≤ U.card :=
    hretain S f r m h hm hmU hred hcountS (fun x hx => (hf x hx).2.2) hspanS hsizeS
  have hV : (a / 2) * Real.exp (L / 2) / L ^ 6 ≤ V.card :=
    hretain T g s m h hm hmU hred hcountT (fun y hy => (hg y hy).2.2) hspanT hsizeT
  have hlarge : E * (Real.exp L / L ^ 40) < (U.card : ℝ) * V.card := by
    apply (hL₃ L hLret).2.trans_le
    rw [pow_two]
    exact mul_le_mul hU hV (by positivity) (by positivity)
  obtain ⟨x, hx, y, hy, hout⟩ := exists_nonexceptional_endpoint_pair U V f g
    (fun d => d ∈ pageKernelExclusion P (kernelConductorCutoff η L) (L ^ 100))
    (E * (Real.exp L / L ^ 40)) hbad hlarge
  have hqx := (populatedKernelPoints_fiber S f
    (fun u => |(u : ℝ)| ≤ Real.exp (η * L)) (kernelSplitCutoff η L)
    (Finset.mem_image_of_mem f hx)).2.1
  have hqy := (populatedKernelPoints_fiber T g
    (fun v => |(v : ℝ)| ≤ Real.exp (η * L)) (kernelSplitCutoff η L)
    (Finset.mem_image_of_mem g hy)).2.1
  apply hno L hLbase (S.filter fun z => f z = f x) (T.filter fun z => g z = g y)
    r s m h (f x) (g y) hm hred (hf x (hUS hx)).1 (hg y (hVT hy)).1
    (hf x (hUS hx)).2.1 (hg y (hVT hy)).2.1 hmU (hsmallS x hx) (hsmallT y hy)
    _ _ _ _ _ hout hqx hqy
  · intro z hz
    obtain ⟨hz, heq⟩ := Finset.mem_filter.mp hz
    simpa only [heq] using (hf z hz).2.2
  · intro z hz
    obtain ⟨hz, heq⟩ := Finset.mem_filter.mp hz
    simpa only [heq] using (hg z hz).2.2
  · intro z hz w hw
    exact hspanS z (Finset.mem_filter.mp hz).1 w (Finset.mem_filter.mp hw).1
  · intro z hz w hw
    exact hspanT z (Finset.mem_filter.mp hz).1 w (Finset.mem_filter.mp hw).1
  · intro z hz w hw
    exact hcross z (Finset.mem_filter.mp hz).1 w (Finset.mem_filter.mp hw).1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_BiasedAffineContradiction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The large-sieve count and the kernel-population contradiction meet

No squarefree-kernel assignment or kernel-count bound is assumed here: both
are constructed from the actual biased affine values.
-/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem biased_affine_populations_impossible (P₀ : PublishedProgressionInput)
    (H : PublishedRealZeroInput P₀) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (Cpop : ℝ) (hCpop : 500 ≤ Cpop) (C : ℝ) (hM : MertensLowerBound C)
    (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    ∃ η L₀ : ℝ, 0 < η ∧ η ≤ 1 / 1000 ∧ 0 < L₀ ∧
      ∀ᶠ T : ℝ in atTop, ∀ (L J : ℝ) (P : Finset ℕ) (k Z M m : ℕ)
        (h : ℤ) (eS eT : ℕ → ℂ) (S U : Finset ℤ),
        T ^ (3 / 2 : ℝ) ≤ L → L₀ ≤ L → 2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
        0 < J → Real.exp T ≤ Cpop * T * J →
        J * Real.exp (-T / (k - 1 : ℕ)) ≤ P.card →
        Real.exp (3 * T / 5) ≤ P.card → (Z : ℝ) ≤ Real.exp (T + 1) →
        1 ≤ Z → 1 ≤ M → M ≤ Z ^ k → ((Z : ℝ) ^ k) ≤ Real.exp (2 * L) →
        (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Odd p) → (∀ p ∈ P, p ≤ Z) →
        (∀ p ∈ P, ‖eS p‖ ≤ 1) → (∀ p ∈ P, ‖eT p‖ ≤ 1) →
        (∀ p ∈ P, T ≤ Real.log (p : ℝ)) → 4 * L ≤ (c / 2) * P.card * T →
        0 < m → (m : ℝ) ≤ Real.exp (η * L) → h.natAbs.Coprime m →
        (∀ x ∈ S, |(m : ℤ) * x - h| ≤ M) →
        (∀ x ∈ U, |(m : ℤ) * x - h| ≤ M) →
        (∀ x ∈ S, c ≤ ‖quadraticPrimeMean P eS ((m : ℤ) * x - h)‖) →
        (∀ x ∈ U, c ≤ ‖quadraticPrimeMean P eT ((m : ℤ) * x - h)‖) →
        (∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ Real.exp L) →
        (∀ x ∈ U, ∀ y ∈ U, |((x - y : ℤ) : ℝ)| ≤ Real.exp L) →
        (∀ x ∈ S, ∀ y ∈ U, (x - y).natAbs.Prime ∧
          kernelSplitCutoff η L < (x - y).natAbs) →
        a * Real.exp (L / 2) / L ^ 6 ≤ S.card →
        a * Real.exp (L / 2) / L ^ 6 ≤ U.card → False := by
  obtain ⟨η, L₀, hη, hηU, hL₀, hno⟩ := few_kernel_populations_impossible P₀ H hSiegel C hM a ha
  refine ⟨η, L₀, hη, hηU, hL₀, ?_⟩
  filter_upwards [eventual_affine_kernel_count sieve Cpop hCpop (η / 100) c (by positivity) hc] with T hcount
  intro L J P k Z M m h eS eT S U hTL hL hk hkU hJ hpop hcenter hsize hZU hZ hM1 hMZ hZL
    hP hodd hPZ heS heT hlogp hdiv hm hmU hred hboundS hboundU hbiasS hbiasU
    hspanS hspanU hcross hsizeS hsizeU
  obtain ⟨f, r, hfcard, hf⟩ := hcount L J P k Z M m h eS S hTL hk hkU hJ hpop hcenter
    hsize hZU hZ hM1 hMZ hZL hP hodd hPZ heS hlogp hdiv hboundS hbiasS
  obtain ⟨g, s, hgcard, hg⟩ := hcount L J P k Z M m h eT U hTL hk hkU hJ hpop hcenter
    hsize hZU hZ hM1 hMZ hZL hP hodd hPZ heT hlogp hdiv hboundU hbiasU
  exact hno L hL S U f g r s m h hm hmU hred hfcard hgcard
    (fun x hx => ⟨(hf x hx).1, (hf x hx).2.2.1, (hf x hx).2.2.2.1⟩)
    (fun x hx => ⟨(hg x hx).1, (hg x hx).2.2.1, (hg x hx).2.2.2.1⟩)
    hspanS hspanU hcross hsizeS hsizeU

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_CommonCenterPopulationContradiction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Two biased endpoint populations cannot share a rational center -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem eventual_center_divisor_budget (c : ℝ) (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop, ∀ L J : ℝ, L ≤ 2 * T ^ 2 →
      Real.exp (3 * T / 5) ≤ J → 4 * L ≤ (c / 4) * J * T := by
  have hp := ((isLittleO_pow_exp_pos_mul_atTop 1 (show (0 : ℝ) < 3 / 5 by norm_num)).const_mul_left
    (32 / c)).bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hp, eventually_ge_atTop (1 : ℝ)] with T hpoly hT L J hL hJ
  have heq : Real.exp ((3 / 5 : ℝ) * T) = Real.exp (3 * T / 5) := by congr 1; ring
  rw [heq] at hpoly
  have habs : |(32 / c) * T| ≤ Real.exp (3 * T / 5) := by
    simpa only [Real.norm_eq_abs, pow_one, abs_of_pos (Real.exp_pos _), one_mul,
      mul_div_assoc] using hpoly
  have hpoly' : 32 * T / c ≤ Real.exp (3 * T / 5) := by
    calc
      _ = (32 / c) * T := by ring
      _ ≤ |(32 / c) * T| := le_abs_self _
      _ ≤ _ := habs
  have hh : 32 * T ≤ c * J := by
    have hq := (div_le_iff₀ hc).mp (hpoly'.trans hJ)
    simpa only [mul_comm] using hq
  have hm := mul_le_mul_of_nonneg_right hh (show 0 ≤ T by linarith)
  nlinarith

theorem common_center_biased_populations_impossible_oai (P₀ : PublishedProgressionInput)
    (H : PublishedRealZeroInput P₀) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (Cpop : ℝ) (hCpop : 500 ≤ Cpop) (C : ℝ) (hM : MertensLowerBound C)
    (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    ∃ η L₀ : ℝ, 0 < η ∧ η ≤ 1 / 1000 ∧ 0 < L₀ ∧
      ∀ᶠ T : ℝ in atTop, ∀ (L J : ℝ) (P : Finset ℕ) (k Z M m : ℕ)
        (h : ℤ) (ε δ : ℕ → ℝ) (t : ℕ → ℤ) (S U : Finset ℤ),
        T ^ (3 / 2 : ℝ) ≤ L → L ≤ 2 * T ^ 2 → L₀ ≤ L →
        2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
        0 < J → Real.exp T ≤ Cpop * T * J →
        J * Real.exp (-T / (k - 1 : ℕ)) ≤ P.card →
        Real.exp (3 * T / 5) ≤ P.card → (Z : ℝ) ≤ Real.exp (T + 1) →
        1 ≤ Z → 1 ≤ M → M ≤ Z ^ k → ((Z : ℝ) ^ k) ≤ Real.exp (2 * L) →
        ∀ hP : ∀ p ∈ P, p.Prime,
        (∀ p ∈ P, Odd p) → (∀ p ∈ P, p ≤ Z) →
        (∀ p ∈ P, ε p = 1 ∨ ε p = -1) → (∀ p ∈ P, δ p = 1 ∨ δ p = -1) →
        (∀ p ∈ P, T ≤ Real.log (p : ℝ)) → (∀ p ∈ P, m < p) →
        (∀ (p : ℕ) (hp : p ∈ P), let _ : Fact p.Prime := ⟨hP p hp⟩
          (t p : ZMod p) = (h : ZMod p) / (m : ZMod p)) →
        0 < m → (m : ℝ) ≤ Real.exp (η * L) → h.natAbs.Coprime m →
        (∀ x ∈ S, |(m : ℤ) * x - h| ≤ M) → (∀ x ∈ U, |(m : ℤ) * x - h| ≤ M) →
        (∀ p ∈ P, (S.card : ℝ) * c ≤ ∑ x ∈ S, orientedQuadraticValue ε t x p) →
        (∀ p ∈ P, (U.card : ℝ) * c ≤ ∑ x ∈ U, orientedQuadraticValue δ t x p) →
        (∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ Real.exp L) →
        (∀ x ∈ U, ∀ y ∈ U, |((x - y : ℤ) : ℝ)| ≤ Real.exp L) →
        (∀ x ∈ S, ∀ y ∈ U, (x - y).natAbs.Prime ∧
          kernelSplitCutoff η L < (x - y).natAbs) →
        a * Real.exp (L / 2) / L ^ 6 ≤ S.card →
        a * Real.exp (L / 2) / L ^ 6 ≤ U.card → False := by
  obtain ⟨η, L₀, hη, hηU, hL₀, hno⟩ := biased_affine_populations_impossible P₀ H hSiegel
    sieve Cpop hCpop C hM (a * c / 2) (c / 2) (by positivity) (by positivity)
  refine ⟨η, L₀, hη, hηU, hL₀, ?_⟩
  filter_upwards [hno, eventual_center_divisor_budget c hc] with T hnoT hbudget
  intro L J P k Z M m h ε δ t S U hTL hLU hL hk hkU hJ hpop hcenter hsize hZU hZ hM1 hMZ hZL
    hP hodd hPZ hε hδ hlogp hmp ht hm hmU hred hboundS hboundU hmeanS hmeanU
    hspanS hspanU hcross hsizeS hsizeU
  have hcard : 0 < P.card := by exact_mod_cast (Real.exp_pos _).trans_le hsize
  obtain ⟨S', hSS, hScard, hSbias⟩ := commonCenter_biased_population P hP S ε t m h c hc.le
    hm hcard hε hmp ht hmeanS
  obtain ⟨U', hUU, hUcard, hUbias⟩ := commonCenter_biased_population P hP U δ t m h c hc.le
    hm hcard hδ hmp ht hmeanU
  have hSsize : (a * c / 2) * Real.exp (L / 2) / L ^ 6 ≤ S'.card := by
    have hh := mul_le_mul_of_nonneg_right hsizeS (show 0 ≤ c / 2 by positivity)
    calc
      _ = (a * Real.exp (L / 2) / L ^ 6) * (c / 2) := by ring
      _ ≤ (S.card : ℝ) * (c / 2) := hh
      _ = (S.card : ℝ) * c / 2 := by ring
      _ ≤ _ := hScard
  have hUsize : (a * c / 2) * Real.exp (L / 2) / L ^ 6 ≤ U'.card := by
    have hh := mul_le_mul_of_nonneg_right hsizeU (show 0 ≤ c / 2 by positivity)
    calc
      _ = (a * Real.exp (L / 2) / L ^ 6) * (c / 2) := by ring
      _ ≤ (U.card : ℝ) * (c / 2) := hh
      _ = (U.card : ℝ) * c / 2 := by ring
      _ ≤ _ := hUcard
  apply hnoT L J P k Z M m h (commonCenterOrientation ε m) (commonCenterOrientation δ m)
    S' U' hTL hL hk hkU hJ hpop hcenter hsize hZU hZ hM1 hMZ hZL hP hodd hPZ
    (fun p hp => commonCenterOrientation_norm ε m p (hε p hp))
    (fun p hp => commonCenterOrientation_norm δ m p (hδ p hp)) hlogp
    (by convert hbudget L P.card hLU hsize using 1; ring)
    hm hmU hred (fun x hx => hboundS x (hSS hx)) (fun x hx => hboundU x (hUU hx))
    hSbias hUbias (fun x hx y hy => hspanS x (hSS hx) y (hSS hy))
    (fun x hx y hy => hspanU x (hUU hx) y (hUU hy))
    (fun x hx y hy => hcross x (hSS hx) y (hUU hy)) hSsize hUsize

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.common_center_biased_populations_impossible_oai := @OAI.Ostmann.common_center_biased_populations_impossible_oai
