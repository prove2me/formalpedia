-- Prove2me | solution 1 for OAI.Ostmann.eventual_original_tuple_witness_lift
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:10:16.205892+00:00
-- url     : https://prove2.me/submissions/98529734-6357-4cdb-b75b-fa1607bd1911

import Mathlib
import Definitions.Def_OAIQ095D007

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SquareCongruence
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AdditiveFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_RealQuadraticPhase
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real quadratic phases and their linear correlations

These are the concrete exponential sums used in the inverse quadratic step.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem realAdditivePhase_add (x y : ℝ) :
    realAdditivePhase (x + y) = realAdditivePhase x * realAdditivePhase y := by
  unfold realAdditivePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem realAdditivePhase_nat_mul (n : ℕ) (x : ℝ) :
    realAdditivePhase ((n : ℝ) * x) = realAdditivePhase x ^ n := by
  unfold realAdditivePhase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem realAdditivePhase_sub (x y : ℝ) :
    realAdditivePhase (x - y) = realAdditivePhase x * conj (realAdditivePhase y) := by
  rw [sub_eq_add_neg, realAdditivePhase_add, conj_realAdditivePhase]

theorem realQuadraticPhase_correlation (α β : ℝ) (h j : ℕ) :
    realQuadraticPhase α β (j + h) * conj (realQuadraticPhase α β j) =
      realAdditivePhase (α * (h : ℝ) ^ 2 + β * h) *
        realAdditivePhase (2 * α * h) ^ j := by
  unfold realQuadraticPhase
  rw [← realAdditivePhase_sub, ← realAdditivePhase_nat_mul, ← realAdditivePhase_add]
  congr 1
  push_cast
  ring

theorem norm_quadratic_correlation_sum (α β : ℝ) (h N : ℕ) :
    ‖∑ j ∈ Finset.range N,
      realQuadraticPhase α β (j + h) * conj (realQuadraticPhase α β j)‖ =
      ‖∑ j ∈ Finset.range N, realAdditivePhase (2 * α * h) ^ j‖ := by
  simp_rw [realQuadraticPhase_correlation, ← Finset.mul_sum, Complex.norm_mul,
    norm_realAdditivePhase, one_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_WeightedPhaseExtraction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extracting an unweighted interval sum from a weighted phase -/

namespace Ostmann

open scoped BigOperators

/-- Finite Abel summation bounds a weighted sum by the largest prefix sum
and the endpoint-plus-variation of the actual weights. -/
theorem weighted_sum_le_variation (w f : ℕ → ℂ) (N : ℕ) (M : ℝ)
    (hprefix : ∀ n ≤ N, ‖∑ j ∈ Finset.range n, f j‖ ≤ M) :
    ‖∑ j ∈ Finset.range N, w j * f j‖ ≤ discreteVariation w N * M := by
  have hab := Finset.sum_range_by_parts w f N
  simp only [smul_eq_mul] at hab
  rw [hab]
  calc
    _ ≤ ‖w (N - 1) * ∑ j ∈ Finset.range N, f j‖ +
        ‖∑ j ∈ Finset.range (N - 1), (w (j + 1) - w j) * ∑ i ∈ Finset.range (j + 1), f i‖ :=
      norm_sub_le _ _
    _ ≤ ‖w (N - 1)‖ * M +
        ∑ j ∈ Finset.range (N - 1), ‖w (j + 1) - w j‖ * M := by
      apply add_le_add
      · rw [Complex.norm_mul]
        exact mul_le_mul_of_nonneg_left (hprefix N le_rfl) (norm_nonneg _)
      · apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro j hj
        rw [Complex.norm_mul]
        apply mul_le_mul_of_nonneg_left (hprefix (j + 1) (by
          have hh := Finset.mem_range.mp hj
          omega)) (norm_nonneg _)
    _ = _ := by rw [discreteVariation, ← Finset.sum_mul]; ring

/-- A large weighted sum therefore supplies a nonempty unweighted prefix.
For a translated interval the same statement applies after reindexing. -/
theorem exists_large_prefix_of_weighted_sum (w f : ℕ → ℂ) (N : ℕ) (R : ℝ)
    (hR : 0 < R)
    (hlarge : discreteVariation w N * R < ‖∑ j ∈ Finset.range N, w j * f j‖) :
    ∃ n : ℕ, 0 < n ∧ n ≤ N ∧ R < ‖∑ j ∈ Finset.range n, f j‖ := by
  by_contra hex
  have hprefix : ∀ n ≤ N, ‖∑ j ∈ Finset.range n, f j‖ ≤ R := by
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      simpa only [Finset.range_zero, Finset.sum_empty, norm_zero] using hR.le
    · apply le_of_not_gt
      intro hh
      exact hex ⟨n, Nat.pos_of_ne_zero hn0, hn, hh⟩
  have hb := weighted_sum_le_variation w f N R hprefix
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_PhaseDistance
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Distance to the nearest integer controls a linear phase sum -/

namespace Ostmann

open scoped BigOperators

theorem realAdditivePhase_sub_int (x : ℝ) (k : ℤ) :
    realAdditivePhase (x - k) = realAdditivePhase x := by
  rw [realAdditivePhase_sub, realAdditivePhase_intCast]
  simp

theorem norm_realAdditivePhase_sub_one (x : ℝ) :
    ‖realAdditivePhase x - 1‖ = 2 * |Real.sin (Real.pi * x)| := by
  unfold realAdditivePhase
  rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show (2 * Real.pi * x) / 2 = Real.pi * x by ring]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

theorem round_distance_le_phase_norm (x : ℝ) :
    4 * |x - (round x : ℤ)| ≤ ‖realAdditivePhase x - 1‖ := by
  rw [← realAdditivePhase_sub_int x (round x), norm_realAdditivePhase_sub_one]
  have hx := abs_sub_round x
  have hpi := Real.pi_pos
  have harg : |Real.pi * (x - (round x : ℤ))| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos hpi]
    nlinarith
  have hsin := Real.mul_abs_le_abs_sin harg
  rw [abs_mul, abs_of_pos hpi] at hsin
  have heq : 2 / Real.pi * (Real.pi * |x - (round x : ℤ)|) =
      2 * |x - (round x : ℤ)| := by field_simp
  rw [heq] at hsin
  linarith

/-- The multiplicative form remains valid at integral phases, so no division
by zero or exceptional phase needs to enter the packing argument. -/
theorem linear_phase_sum_distance_bound (x : ℝ) (N : ℕ) :
    ‖∑ j ∈ Finset.range N, realAdditivePhase x ^ j‖ ≤ N ∧
      2 * |x - (round x : ℤ)| *
        ‖∑ j ∈ Finset.range N, realAdditivePhase x ^ j‖ ≤ 1 := by
  have hz := norm_realAdditivePhase x
  constructor
  · calc
      _ ≤ ∑ j ∈ Finset.range N, ‖realAdditivePhase x ^ j‖ := norm_sum_le _ _
      _ = N := by simp [hz]
  · have hgeom := geom_sum_mul (realAdditivePhase x) N
    have heq : ‖∑ j ∈ Finset.range N, realAdditivePhase x ^ j‖ *
        ‖realAdditivePhase x - 1‖ = ‖realAdditivePhase x ^ N - 1‖ := by
      rw [← Complex.norm_mul, hgeom]
    have hb : ‖realAdditivePhase x ^ N - 1‖ ≤ 2 := by
      calc
        _ ≤ ‖realAdditivePhase x ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by norm_num [hz]
    have hm := mul_le_mul_of_nonneg_right (round_distance_le_phase_norm x)
      (norm_nonneg (∑ j ∈ Finset.range N, realAdditivePhase x ^ j))
    nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SeparatedPhasePacking
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite reciprocal-distance bound for separated centered phases -/

namespace Ostmann

open scoped BigOperators Classical

private theorem same_sign_abs_difference (x y : ℝ)
    (hs : decide (x < 0) = decide (y < 0)) :
    |(|x| - |y|)| = |x - y| := by
  by_cases hx : x < 0 <;> by_cases hy : y < 0
  · rw [abs_of_neg hx, abs_of_neg hy]
    have heq : -x - -y = -(x - y) := by ring
    rw [heq, abs_neg]
  · simp [hx, hy] at hs
  · simp [hx, hy] at hs
  · rw [abs_of_nonneg (le_of_not_gt hx), abs_of_nonneg (le_of_not_gt hy)]

theorem centeredPhaseBin_injective {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (r : ℕ) (hr : 0 < r)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 / (2 * (r : ℝ)) ≤ |f i - f j|) :
    Set.InjOn (fun i => centeredPhaseBin r (f i)) S := by
  intro i hi j hj heq
  by_contra hij
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hs := congrArg Prod.fst heq
  have hb := congrArg Prod.snd heq
  have hfi : (⌊2 * (r : ℝ) * |f i|⌋₊ : ℝ) ≤ 2 * (r : ℝ) * |f i| :=
    Nat.floor_le (by positivity)
  have hfj : (⌊2 * (r : ℝ) * |f j|⌋₊ : ℝ) ≤ 2 * (r : ℝ) * |f j| :=
    Nat.floor_le (by positivity)
  have hfi' := Nat.lt_floor_add_one (2 * (r : ℝ) * |f i|)
  have hfj' := Nat.lt_floor_add_one (2 * (r : ℝ) * |f j|)
  change ⌊2 * (r : ℝ) * |f i|⌋₊ = ⌊2 * (r : ℝ) * |f j|⌋₊ at hb
  rw [hb] at hfi hfi'
  have hclose : |(2 * (r : ℝ) * |f i|) - (2 * (r : ℝ) * |f j|)| < 1 := by
    apply abs_lt.mpr
    constructor <;> linarith
  rw [← mul_sub, abs_mul, abs_of_pos (show 0 < 2 * (r : ℝ) by positivity),
    same_sign_abs_difference (f i) (f j) hs] at hclose
  have hfar := (div_le_iff₀ (show 0 < 2 * (r : ℝ) by positivity)).mp (hsep i hi j hj hij)
  nlinarith

/-- Each signed distance bin contains at most one point. The zero bin costs
N; all other bins cost r/k. This is the finite harmonic estimate needed for
one rational-approximation block. -/
theorem separated_phase_weight_sum {ι : Type*} (S : Finset ι) (f w : ι → ℝ)
    (r : ℕ) (N : ℝ) (hr : 0 < r) (hN : 0 ≤ N)
    (hsize : ∀ i ∈ S, |f i| ≤ 1 / 2)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 / (2 * (r : ℝ)) ≤ |f i - f j|)
    (hw : ∀ i ∈ S, 0 ≤ w i)
    (hupper : ∀ i ∈ S, w i ≤ N)
    (hdist : ∀ i ∈ S, 2 * |f i| * w i ≤ 1) :
    ∑ i ∈ S, w i ≤
      2 * ∑ k ∈ Finset.range (r + 1), if k = 0 then N else (r : ℝ) / k := by
  let bin := fun i => centeredPhaseBin r (f i)
  let B := fun k : ℕ => if k = 0 then N else (r : ℝ) / k
  have hB : ∀ k, 0 ≤ B k := by
    intro k
    dsimp [B]
    split_ifs <;> positivity
  have hinj : Set.InjOn bin S := centeredPhaseBin_injective S f r hr hsep
  have hmem : ∀ i ∈ S, bin i ∈ (Finset.univ : Finset Bool).product (Finset.range (r + 1)) := by
    intro i hi
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_univ _, Finset.mem_range.mpr ?_⟩
    have hfloor : (⌊2 * (r : ℝ) * |f i|⌋₊ : ℝ) ≤ 2 * (r : ℝ) * |f i| :=
      Nat.floor_le (by positivity)
    have hb : (⌊2 * (r : ℝ) * |f i|⌋₊ : ℝ) ≤ r := by
      have hh := hsize i hi
      nlinarith [show (0 : ℝ) ≤ r from Nat.cast_nonneg r]
    have hk : ⌊2 * (r : ℝ) * |f i|⌋₊ ≤ r := by exact_mod_cast hb
    exact Nat.lt_succ_of_le hk
  have hpoint : ∀ i ∈ S, w i ≤ B (bin i).2 := by
    intro i hi
    let k := (bin i).2
    change w i ≤ if k = 0 then N else (r : ℝ) / k
    by_cases hk : k = 0
    · simpa only [hk, ite_true, if_true] using hupper i hi
    · rw [ite_eq_right hk]
      have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
      apply (le_div_iff₀ hkpos).mpr
      have hfloor : (k : ℝ) ≤ 2 * (r : ℝ) * |f i| := Nat.floor_le (by positivity)
      have hmul := mul_le_mul_of_nonneg_left hfloor (hw i hi)
      have hbound := mul_le_mul_of_nonneg_left (hdist i hi) (Nat.cast_nonneg r)
      nlinarith
  calc
    _ ≤ ∑ i ∈ S, B (bin i).2 := Finset.sum_le_sum hpoint
    _ = ∑ b ∈ S.image bin, B b.2 := (Finset.sum_image (f := fun b : Bool × ℕ => B b.2) hinj).symm
    _ ≤ ∑ b ∈ (Finset.univ : Finset Bool).product (Finset.range (r + 1)), B b.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro b hb
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
        exact hmem i hi
      · intro b _ _
        exact hB b.2
    _ = _ := by rw [Finset.product_eq_sprod, Finset.sum_product]; simp [B, two_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_RationalPhaseSeparation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separation of the phases in a short block near a reduced rational -/

namespace Ostmann

/-- Dirichlet approximation in exactly the form needed by quadratic
Weyl differencing; the numerator and denominator are reduced. -/
theorem exists_reduced_phase_approximation (θ : ℝ) (Q : ℕ) (hQ : 0 < Q) :
    ∃ (a : ℤ) (r : ℕ), 0 < r ∧ r ≤ Q ∧ a.natAbs.Coprime r ∧
      |θ - (a : ℝ) / r| ≤ 1 / (((Q : ℝ) + 1) * r) ∧
      |θ - (a : ℝ) / r| ≤ 1 / (r : ℝ) ^ 2 := by
  obtain ⟨q, hq, hqQ⟩ := Real.exists_rat_abs_sub_le_and_den_le θ hQ
  have hr : (0 : ℝ) < q.den := by exact_mod_cast q.pos
  have hQ' : (q.den : ℝ) ≤ Q := by exact_mod_cast hqQ
  have hcast : (q : ℝ) = (q.num : ℝ) / q.den := by exact Rat.cast_def q
  refine ⟨q.num, q.den, q.pos, hqQ, q.reduced, ?_, ?_⟩
  · simpa only [hcast] using hq
  · apply (show |θ - (q.num : ℝ) / q.den| ≤ 1 / (((Q : ℝ) + 1) * q.den) by
      simpa only [hcast] using hq).trans
    apply one_div_le_one_div_of_le (by positivity : 0 < (q.den : ℝ) ^ 2)
    nlinarith

/-- A nonzero short shift cannot be too close to any integer. This is the
separation claim used inside each block of length at most r/2. -/
theorem rational_phase_shift_separation (θ : ℝ) (a δ k : ℤ) (r : ℕ)
    (hr : 0 < r) (hcop : a.natAbs.Coprime r) (hδ : δ ≠ 0)
    (hshort : 2 * |(δ : ℝ)| ≤ r)
    (happrox : |θ - (a : ℝ) / r| ≤ 1 / (r : ℝ) ^ 2) :
    1 / (2 * (r : ℝ)) ≤ |(δ : ℝ) * θ - k| := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hn : δ * a - (r : ℤ) * k ≠ 0 := by
    intro heq
    have heq' : δ * a = (r : ℤ) * k := sub_eq_zero.mp heq
    have hd : r ∣ δ.natAbs * a.natAbs := by
      refine ⟨k.natAbs, ?_⟩
      simpa only [Int.natAbs_mul, Int.natAbs_natCast] using congrArg Int.natAbs heq'
    have hdδ : r ∣ δ.natAbs := hcop.symm.dvd_of_dvd_mul_right hd
    have hle : r ≤ δ.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hδ) hdδ
    have hleR : (r : ℝ) ≤ |(δ : ℝ)| := by
      have hh : (r : ℝ) ≤ δ.natAbs := by exact_mod_cast hle
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hh
    linarith
  have hnon : (1 : ℝ) ≤ |((δ * a - (r : ℤ) * k : ℤ) : ℝ)| := by
    have hh : (1 : ℝ) ≤ (δ * a - (r : ℤ) * k).natAbs := by
      exact_mod_cast Int.natAbs_pos.mpr hn
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hh
  have heq : ((δ * a - (r : ℤ) * k : ℤ) : ℝ) =
      (r : ℝ) * ((δ : ℝ) * θ - k) - (r : ℝ) * δ * (θ - (a : ℝ) / r) := by
    push_cast
    field_simp
    ring
  have habs : |(r : ℝ) * ((δ : ℝ) * θ - k) -
      (r : ℝ) * δ * (θ - (a : ℝ) / r)| ≤
      |(r : ℝ) * ((δ : ℝ) * θ - k)| +
        |(r : ℝ) * δ * (θ - (a : ℝ) / r)| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      abs_add_le ((r : ℝ) * ((δ : ℝ) * θ - k))
        (-((r : ℝ) * δ * (θ - (a : ℝ) / r)))
  rw [← heq] at habs
  simp only [abs_mul, abs_of_pos hrR] at habs
  have herr := mul_le_mul_of_nonneg_left happrox
    (show 0 ≤ (r : ℝ) * |(δ : ℝ)| by positivity)
  have hratio : (r : ℝ) * |(δ : ℝ)| * (1 / (r : ℝ) ^ 2) = |(δ : ℝ)| / r := by
    field_simp
  rw [hratio] at herr
  have hhalf : |(δ : ℝ)| / r ≤ 1 / 2 := (div_le_iff₀ hrR).mpr (by linarith)
  apply (div_le_iff₀ (show 0 < 2 * (r : ℝ) by positivity)).mpr
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_RationalPhaseBlock
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The harmonic bound for one short rational phase block -/

namespace Ostmann

open scoped BigOperators Classical

theorem phase_bin_sum_eq (r : ℕ) (N : ℝ) :
    (∑ k ∈ Finset.range (r + 1), if k = 0 then N else (r : ℝ) / k) =
      N + r * (harmonic r : ℝ) := by
  rw [Finset.sum_range_succ']
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, if_false, ite_true, if_true,
    Nat.cast_add, Nat.cast_one]
  rw [harmonic, Rat.cast_sum]
  simp only [Rat.cast_inv, Rat.cast_add, Rat.cast_one, Rat.cast_natCast, Nat.cast_add, Nat.cast_one]
  rw [Finset.mul_sum]
  simp only [div_eq_mul_inv]
  ring

/-- All points may be translated by an arbitrary integer block location.
Only the pairwise short-shift condition enters the estimate. -/
theorem rational_phase_block_bound (θ : ℝ) (a : ℤ) (r N : ℕ) (M : ℕ → ℕ) (S : Finset ℕ)
    (hr : 0 < r) (hcop : a.natAbs.Coprime r)
    (happrox : |θ - (a : ℝ) / r| ≤ 1 / (r : ℝ) ^ 2)
    (hshort : ∀ i ∈ S, ∀ j ∈ S, 2 * |(((i : ℤ) - j : ℤ) : ℝ)| ≤ (r : ℝ))
    (hlen : ∀ h ∈ S, M h ≤ N) :
    ∑ h ∈ S, ‖∑ j ∈ Finset.range (M h), realAdditivePhase (θ * h) ^ j‖ ≤
      2 * ((N : ℝ) + r * (1 + Real.log r)) := by
  let f := fun h : ℕ => θ * h - (round (θ * h) : ℤ)
  let w := fun h : ℕ => ‖∑ j ∈ Finset.range (M h), realAdditivePhase (θ * h) ^ j‖
  have hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 / (2 * (r : ℝ)) ≤ |f i - f j| := by
    intro i hi j hj hij
    have hd : (i : ℤ) - j ≠ 0 := by
      intro heq
      exact hij (by exact_mod_cast sub_eq_zero.mp heq)
    have hb := rational_phase_shift_separation θ a ((i : ℤ) - j)
      (round (θ * i) - round (θ * j)) r hr hcop hd (hshort i hi j hj) happrox
    convert hb using 1
    all_goals try with_reducible_and_instances rfl
    push_cast
    dsimp [f]
    congr 1
    ring
  have hweight := separated_phase_weight_sum S f w r N hr (Nat.cast_nonneg N)
    (fun h _ => abs_sub_round (θ * h)) hsep (fun _ _ => norm_nonneg _)
    (fun h hh => (linear_phase_sum_distance_bound (θ * h) (M h)).1.trans (by exact_mod_cast hlen h hh))
    (fun h _ => (linear_phase_sum_distance_bound (θ * h) (M h)).2)
  rw [phase_bin_sum_eq] at hweight
  apply hweight.trans
  have hh := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log r) (Nat.cast_nonneg r)
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_RationalPhaseGlobal
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the short-block bounds over all shifts -/

namespace Ostmann

open scoped BigOperators Classical

private theorem quotient_fiber_short (i j b r : ℕ) (hb : 0 < b)
    (hr : 2 * b ≤ r) (heq : i / b = j / b) :
    2 * |(((i : ℤ) - j : ℤ) : ℝ)| ≤ r := by
  have hi := Nat.mod_add_div i b
  have hj := Nat.mod_add_div j b
  rw [heq] at hi
  have hi' : ((i % b : ℕ) : ℝ) + (b : ℝ) * (j / b : ℕ) = i := by exact_mod_cast hi
  have hj' : ((j % b : ℕ) : ℝ) + (b : ℝ) * (j / b : ℕ) = j := by exact_mod_cast hj
  have hmi : ((i % b : ℕ) : ℝ) < b := by exact_mod_cast Nat.mod_lt i hb
  have hmj : ((j % b : ℕ) : ℝ) < b := by exact_mod_cast Nat.mod_lt j hb
  have hmi0 : (0 : ℝ) ≤ ((i % b : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmj0 : (0 : ℝ) ≤ ((j % b : ℕ) : ℝ) := Nat.cast_nonneg _
  have hr' : (2 : ℝ) * b ≤ r := by exact_mod_cast hr
  push_cast
  have hab : |(i : ℝ) - j| ≤ b := by
    apply abs_le.mpr
    constructor <;> linarith
  linarith

theorem rational_phase_global_bound (θ : ℝ) (a : ℤ) (r N H : ℕ) (M : ℕ → ℕ)
    (hr : 2 ≤ r) (hcop : a.natAbs.Coprime r)
    (happrox : |θ - (a : ℝ) / r| ≤ 1 / (r : ℝ) ^ 2)
    (hlen : ∀ h ∈ Finset.range H, M h ≤ N) :
    ∑ h ∈ Finset.range H, ‖∑ j ∈ Finset.range (M h), realAdditivePhase (θ * h) ^ j‖ ≤
      (4 * (H : ℝ) / r + 1) * (2 * ((N : ℝ) + r * (1 + Real.log r))) := by
  let b := r / 2
  let w := fun h : ℕ => ‖∑ j ∈ Finset.range (M h), realAdditivePhase (θ * h) ^ j‖
  let C := 2 * ((N : ℝ) + r * (1 + Real.log r))
  have hb : 0 < b := by dsimp [b]; omega
  have hb2 : 2 * b ≤ r := by dsimp [b]; omega
  have hb4 : r ≤ 4 * b := by dsimp [b]; omega
  have hrp : 0 < r := by omega
  have hmap : ∀ h ∈ Finset.range H, h / b ∈ Finset.range (H / b + 1) := by
    intro h hh
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt (Finset.mem_range.mp hh)))
  have hsum : (∑ h ∈ Finset.range H, w h) =
      ∑ k ∈ Finset.range (H / b + 1), ∑ h ∈ (Finset.range H).filter (fun h => h / b = k), w h := by
    exact (Finset.sum_fiberwise_of_maps_to hmap w).symm
  have hblock : ∀ k ∈ Finset.range (H / b + 1),
      (∑ h ∈ (Finset.range H).filter (fun h => h / b = k), w h) ≤ C := by
    intro k hk
    apply rational_phase_block_bound θ a r N M _ hrp hcop happrox
    · intro i hi j hj
      exact quotient_fiber_short i j b r hb hb2
        ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
    · intro h hh
      exact hlen h (Finset.mem_filter.mp hh).1
  have hbound : (∑ h ∈ Finset.range H, w h) ≤ (H / b + 1 : ℕ) * C := by
    rw [hsum]
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using Finset.sum_le_sum hblock
  have hrR : (0 : ℝ) < r := by exact_mod_cast hrp
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hdiv : ((H / b : ℕ) : ℝ) ≤ 4 * (H : ℝ) / r := by
    apply (Nat.cast_div_le : ((H / b : ℕ) : ℝ) ≤ (H : ℝ) / b).trans
    apply (div_le_div_iff₀ hbR hrR).mpr
    have hb4R : (r : ℝ) ≤ 4 * b := by exact_mod_cast hb4
    nlinarith [show (0 : ℝ) ≤ H from Nat.cast_nonneg H]
  have hC : 0 ≤ C := by
    have hlog : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg (by exact_mod_cast hrp)
    dsimp [C]
    positivity
  apply hbound.trans
  apply mul_le_mul_of_nonneg_right _ hC
  push_cast
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDifferencing
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One differencing step for the actual quadratic exponential sum -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

private theorem real_part_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, Complex.add_re, ih]

private theorem norm_add_sq_real (z w : ℂ) :
    ‖z + w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 + 2 * (w * conj z).re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem sum_norm_sq_triangle (f : ℕ → ℂ) (N : ℕ) :
    ‖∑ j ∈ Finset.range N, f j‖ ^ 2 =
      (∑ j ∈ Finset.range N, ‖f j‖ ^ 2) +
        2 * ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range k, (f k * conj (f j)).re := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, norm_add_sq_real, ih]
    have hc : (f N * conj (∑ j ∈ Finset.range N, f j)).re =
        ∑ j ∈ Finset.range N, (f N * conj (f j)).re := by
      rw [map_sum, Finset.mul_sum, real_part_sum]
    simp only [Finset.sum_range_succ, hc]
    ring

private theorem triangle_sum_by_gap (F : ℕ → ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, ∑ j ∈ Finset.range k, F k j) =
      ∑ h ∈ Finset.range N, ∑ j ∈ Finset.range (N - (h + 1)), F (j + (h + 1)) j := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_bij (fun (z : Σ _ : ℕ, ℕ) _ => ⟨z.1 - z.2 - 1, z.2⟩)
  · intro z hz
    obtain ⟨hk, hj⟩ := Finset.mem_sigma.mp hz
    apply Finset.mem_sigma.mpr
    simp only [Finset.mem_range] at hk hj ⊢
    constructor <;> omega
  · intro z hz w hw heq
    obtain ⟨hk, hj⟩ := Finset.mem_sigma.mp hz
    obtain ⟨hl, hi⟩ := Finset.mem_sigma.mp hw
    simp only [Finset.mem_range] at hk hj hl hi
    have h₁ := congrArg (fun z : Σ _ : ℕ, ℕ => z.1) heq
    have h₂ := congrArg (fun z : Σ _ : ℕ, ℕ => z.2) heq
    apply Sigma.ext
    · dsimp at h₁ h₂
      omega
    · exact heq_of_eq h₂
  · intro z hz
    obtain ⟨hh, hj⟩ := Finset.mem_sigma.mp hz
    simp only [Finset.mem_range] at hh hj
    refine ⟨⟨z.2 + (z.1 + 1), z.2⟩, Finset.mem_sigma.mpr ?_, ?_⟩
    · simp only [Finset.mem_range]
      constructor <;> omega
    · apply Sigma.ext
      · dsimp
        omega
      · rfl
  · intro z hz
    obtain ⟨hk, hj⟩ := Finset.mem_sigma.mp hz
    simp only [Finset.mem_range] at hk hj
    dsimp
    congr 1
    omega

/-- The linear coefficient disappears after taking absolute values of the
shift correlations. No rational-approximation estimate is assumed here. -/
theorem quadratic_differencing_bound (α β : ℝ) (N : ℕ) :
    ‖∑ j ∈ Finset.range N, realQuadraticPhase α β j‖ ^ 2 ≤
      (N : ℝ) + 2 * ∑ h ∈ Finset.range N,
        ‖∑ j ∈ Finset.range (N - (h + 1)), realAdditivePhase (2 * α * (h + 1)) ^ j‖ := by
  rw [sum_norm_sq_triangle, triangle_sum_by_gap]
  have hdiag : (∑ j ∈ Finset.range N, ‖realQuadraticPhase α β j‖ ^ 2) = (N : ℝ) := by
    simp [realQuadraticPhase]
  rw [hdiag]
  gcongr with h hh
  rw [← real_part_sum]
  apply le_trans (Complex.re_le_norm _)
  rw [norm_quadratic_correlation_sum]
  simp only [Nat.cast_add, Nat.cast_one]
  exact le_rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticWeylBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A concrete quadratic Weyl bound from one differencing step -/

namespace Ostmann

open scoped BigOperators

/-- The bound is uniform in the linear coefficient. It is derived from the
finite block-packing argument, with no external exponential-sum hypothesis. -/
theorem quadratic_weyl_bound (α β : ℝ) (a : ℤ) (r N : ℕ)
    (hr : 2 ≤ r) (hcop : a.natAbs.Coprime r)
    (happrox : |2 * α - (a : ℝ) / r| ≤ 1 / (r : ℝ) ^ 2) :
    ‖∑ j ∈ Finset.range N, realQuadraticPhase α β j‖ ^ 2 ≤
      64 * ((N : ℝ) / r + 1) * ((N : ℝ) + r * (1 + Real.log r)) := by
  by_cases hN : N = 0
  · subst N
    have hl : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ r by omega))
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    positivity
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  let w := fun h : ℕ => ‖∑ j ∈ Finset.range (N - h), realAdditivePhase (2 * α * h) ^ j‖
  have hs : (∑ h ∈ Finset.range N, w (h + 1)) ≤ ∑ h ∈ Finset.range (N + 1), w h := by
    rw [Finset.sum_range_succ']
    have hw0 : 0 ≤ w 0 := norm_nonneg _
    linarith
  have hd : ‖∑ j ∈ Finset.range N, realQuadraticPhase α β j‖ ^ 2 ≤
      (N : ℝ) + 2 * ∑ h ∈ Finset.range N, w (h + 1) := by
    simpa only [w, Nat.cast_add, Nat.cast_one] using quadratic_differencing_bound α β N
  have hg := rational_phase_global_bound (2 * α) a r N (N + 1) (fun h => N - h)
    hr hcop happrox (fun h _ => Nat.sub_le _ _)
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hlog : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ r by omega))
  let A := (N : ℝ) / r + 1
  let B := (N : ℝ) + r * (1 + Real.log r)
  have hA : 1 ≤ A := by
    have hh : 0 ≤ (N : ℝ) / r := by positivity
    dsimp [A]
    linarith
  have hB : (N : ℝ) ≤ B := by
    have hh : 0 ≤ (r : ℝ) * (1 + Real.log r) := by positivity
    dsimp [B]
    linarith
  have hB0 : 0 ≤ B := (Nat.cast_nonneg N).trans hB
  have hcoef : 4 * ((N + 1 : ℕ) : ℝ) / r + 1 ≤ 8 * A := by
    have hh : ((N : ℝ) + 1) / r ≤ 2 * ((N : ℝ) / r) := by
      calc
        _ ≤ (2 * (N : ℝ)) / r := div_le_div_of_nonneg_right (by linarith) hrR.le
        _ = _ := by ring
    dsimp [A]
    push_cast
    rw [mul_div_assoc]
    nlinarith
  have hg' : (∑ h ∈ Finset.range (N + 1), w h) ≤ 16 * A * B := by
    apply hg.trans
    have hm := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ 2 * B by positivity)
    simpa only [B] using hm.trans_eq (by ring)
  have hNB : (N : ℝ) ≤ A * B := by
    have hh := mul_le_mul_of_nonneg_right hA hB0
    nlinarith
  have hAB : 0 ≤ A * B := by positivity
  dsimp [A, B] at hg' hNB hAB ⊢
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticInverse
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An effective inverse conclusion for a large quadratic sum

All assumptions below are explicit numerical scale inequalities. The rational
approximation and exponential-sum bound are proved, not supplied as inputs.
-/

namespace Ostmann

open scoped BigOperators

private theorem weyl_numeric_contradiction (N Q r B ρ V : ℝ)
    (hN : 0 < N) (hr : 0 < r) (hB : 1 ≤ B) (hρ : 0 < ρ)
    (hrQ : r ≤ Q) (hsmallN : 512 * B ≤ ρ * N)
    (hsmallQ : 512 * Q * B ≤ ρ * N ^ 2)
    (hrlarge : 512 ≤ ρ * r)
    (hlower : ρ * N ^ 2 ≤ V)
    (hupper : V ≤ 64 * (N / r + 1) * (N + r * B)) : False := by
  let T := ρ * N ^ 2 / 512
  have hT : 0 < T := by dsimp [T]; positivity
  have hfirst : N ^ 2 / r ≤ T := by
    apply (div_le_iff₀ hr).mpr
    dsimp [T]
    nlinarith [mul_nonneg (sq_nonneg N) (sub_nonneg.mpr hrlarge)]
  have hsecond : N * B ≤ T := by
    dsimp [T]
    nlinarith [mul_le_mul_of_nonneg_left hsmallN hN.le]
  have hthird : N ≤ T := by
    have hh := mul_le_mul_of_nonneg_left hB hN.le
    linarith
  have hfourth : r * B ≤ T := by
    have hh := mul_le_mul_of_nonneg_right hrQ (show 0 ≤ B by linarith)
    dsimp [T]
    linarith
  have heq : 64 * (N / r + 1) * (N + r * B) =
      64 * (N ^ 2 / r + N * B + N + r * B) := by
    field_simp
    ring
  rw [heq] at hupper
  dsimp [T] at hfirst hsecond hthird hfourth hT
  nlinarith

/-- A large sum forces a denominator O(1/ρ), with approximation precision
1/(Q+1). The stated scale conditions are precisely those used to choose Q. -/
theorem quadratic_inverse_approximation (α β ρ B : ℝ) (N Q : ℕ)
    (hN : 0 < N) (hQ : 0 < Q) (hρ : 0 < ρ) (hB : 1 ≤ B)
    (hlog : 1 + Real.log (Q : ℝ) ≤ B)
    (hsmallN : 512 * B ≤ ρ * N)
    (hsmallQ : 512 * (Q : ℝ) * B ≤ ρ * (N : ℝ) ^ 2)
    (hlarge : ρ * (N : ℝ) ^ 2 ≤
      ‖∑ j ∈ Finset.range N, realQuadraticPhase α β j‖ ^ 2) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ 1024 / ρ ∧
      |(q : ℝ) * α - (round ((q : ℝ) * α) : ℤ)| ≤ 1 / ((Q : ℝ) + 1) := by
  obtain ⟨a, r, hr, hrQ, hcop, happ, happ'⟩ := exists_reduced_phase_approximation (2 * α) Q hQ
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hρ1 : ρ ≤ 1 := by
    have hnorm : ‖∑ j ∈ Finset.range N, realQuadraticPhase α β j‖ ≤ (N : ℝ) := by
      calc
        _ ≤ ∑ j ∈ Finset.range N, ‖realQuadraticPhase α β j‖ := norm_sum_le _ _
        _ = N := by simp [realQuadraticPhase]
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    nlinarith [sq_pos_of_pos hNpos]
  have hrsmall : (r : ℝ) ≤ 512 / ρ := by
    by_contra hh
    have hrlarge : 512 ≤ ρ * (r : ℝ) := by
      have hh' : 512 / ρ < (r : ℝ) := lt_of_not_ge hh
      nlinarith [(div_lt_iff₀ hρ).mp hh']
    have hr2 : 2 ≤ r := by
      by_contra hlt
      have hre : r = 1 := by omega
      have hR : (1 : ℝ) < r := by
        nlinarith
      exact (lt_irrefl (1 : ℝ)) (by simpa only [hre, Nat.cast_one] using hR)
    have hw := quadratic_weyl_bound α β a r N hr2 hcop happ'
    have hrQR : (r : ℝ) ≤ Q := by exact_mod_cast hrQ
    have hlogr : 1 + Real.log (r : ℝ) ≤ B := by
      have hh := Real.log_le_log hrR hrQR
      linarith
    have hw' : ‖∑ j ∈ Finset.range N, realQuadraticPhase α β j‖ ^ 2 ≤
        64 * ((N : ℝ) / r + 1) * ((N : ℝ) + r * B) := by
      apply hw.trans
      gcongr
    exact weyl_numeric_contradiction N Q r B ρ _ hNpos hrR hB hρ
      (by exact_mod_cast hrQ) hsmallN hsmallQ hrlarge hlarge hw'
  refine ⟨2 * r, by omega, ?_, ?_⟩
  · have hh := mul_le_mul_of_nonneg_left hrsmall (by norm_num : (0 : ℝ) ≤ 2)
    push_cast
    exact hh.trans_eq (by ring)
  · have hround := round_le (((2 * r : ℕ) : ℝ) * α) a
    apply hround.trans
    have hh := mul_le_mul_of_nonneg_left happ hrR.le
    have hid : (r : ℝ) * |2 * α - (a : ℝ) / r| = |((2 * r : ℕ) : ℝ) * α - a| := by
      calc
        _ = |(r : ℝ) * (2 * α - (a : ℝ) / r)| := by rw [abs_mul, abs_of_pos hrR]
        _ = _ := by
          congr 1
          push_cast
          field_simp
    rw [hid] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_EffectiveQuadraticInverse
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Choosing the actual approximation cutoff for the inverse quadratic step -/

namespace Ostmann

open scoped BigOperators

/-- A quadratic sum of relative squared size ρ has a small denominator,
with the expected N⁻² precision up to a logarithmic factor. -/
theorem effective_quadratic_inverse (α β ρ : ℝ) (N : ℕ)
    (hN : 0 < N) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hscale : 512 * (1 + 2 * Real.log (N : ℝ)) ≤ ρ * N)
    (hlarge : ρ * (N : ℝ) ^ 2 ≤
      ‖∑ j ∈ Finset.range N, realQuadraticPhase α β j‖ ^ 2) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ 1024 / ρ ∧
      |(q : ℝ) * α - (round ((q : ℝ) * α) : ℤ)| ≤
        1024 * (1 + 2 * Real.log (N : ℝ)) / (ρ * (N : ℝ) ^ 2) := by
  let B := 1 + 2 * Real.log (N : ℝ)
  let R := ρ * (N : ℝ) ^ 2 / (1024 * B)
  let Q : ℕ := ⌊R⌋₊
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hBp : 0 < B := by linarith
  have hN512 : (512 : ℝ) ≤ N := by
    have hm := mul_le_mul_of_nonneg_right hρ1 hNp.le
    dsimp [B] at hB
    linarith
  have hR1 : 1 ≤ R := by
    apply (le_div_iff₀ (show 0 < 1024 * B by positivity)).mpr
    have hm := mul_le_mul_of_nonneg_right hscale hNp.le
    have hb : 0 ≤ B * ((N : ℝ) - 2) :=
      mul_nonneg hBp.le (by linarith)
    dsimp [B] at hb ⊢
    nlinarith
  have hQ : 0 < Q := by
    have hh : 1 ≤ Q := Nat.le_floor (by simpa only [Nat.cast_one] using hR1)
    omega
  have hQle : (Q : ℝ) ≤ R := Nat.floor_le (by positivity)
  have hRle : R ≤ (N : ℝ) ^ 2 := by
    apply (div_le_iff₀ (show 0 < 1024 * B by positivity)).mpr
    have hm := mul_le_mul_of_nonneg_right hρ1 (sq_nonneg (N : ℝ))
    have hb := mul_le_mul_of_nonneg_right hB (sq_nonneg (N : ℝ))
    nlinarith
  have hQp : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hlogQ : 1 + Real.log (Q : ℝ) ≤ B := by
    have hh := Real.log_le_log hQp (hQle.trans hRle)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    dsimp [B]
    linarith
  have hQR : 512 * (Q : ℝ) * B ≤ ρ * (N : ℝ) ^ 2 := by
    have hh := (le_div_iff₀ (show 0 < 1024 * B by positivity)).mp hQle
    nlinarith
  obtain ⟨q, hq, hqsize, hqapprox⟩ := quadratic_inverse_approximation α β ρ B N Q
    hN hQ hρ hB hlogQ hscale hQR hlarge
  refine ⟨q, hq, hqsize, hqapprox.trans ?_⟩
  have hRupper : R ≤ (Q : ℝ) + 1 := (Nat.lt_floor_add_one R).le
  have hRp : 0 < R := by positivity
  calc
    1 / ((Q : ℝ) + 1) ≤ 1 / R := one_div_le_one_div_of_le hRp hRupper
    _ = _ := by dsimp [R, B]; field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_WeightedQuadraticInverse
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The inverse phase conclusion for the actual weighted quadratic sum -/

namespace Ostmann

open scoped BigOperators

/-- Finite variation removes the smooth weight. The resulting explicit losses
are harmless exponential factors when δ=exp(-K), as in the manuscript. -/
theorem weighted_quadratic_inverse (w : ℕ → ℂ) (α β δ : ℝ) (N : ℕ)
    (hN : 0 < N) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hscale : 512 * (1 + 2 * Real.log (N : ℝ)) ≤ δ ^ 3 * N)
    (hlarge : discreteVariation w N * (δ * N) <
      ‖∑ j ∈ Finset.range N, w j * realQuadraticPhase α β j‖) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ 1024 / δ ^ 2 ∧
      |(q : ℝ) * α - (round ((q : ℝ) * α) : ℤ)| ≤
        1024 * (1 + 2 * Real.log (N : ℝ)) / (δ ^ 4 * (N : ℝ) ^ 2) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨n, hn, hnN, hsum⟩ := exists_large_prefix_of_weighted_sum w
    (realQuadraticPhase α β) N (δ * N) (by positivity) hlarge
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hnNR : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hnorm : ‖∑ j ∈ Finset.range n, realQuadraticPhase α β j‖ ≤ (n : ℝ) := by
    calc
      _ ≤ ∑ j ∈ Finset.range n, ‖realQuadraticPhase α β j‖ := norm_sum_le _ _
      _ = n := by simp [realQuadraticPhase]
  have hδN : δ * N ≤ (n : ℝ) := (hsum.trans_le hnorm).le
  have hlog : Real.log (n : ℝ) ≤ Real.log (N : ℝ) := Real.log_le_log hnp hnNR
  have hnscale : 512 * (1 + 2 * Real.log (n : ℝ)) ≤ δ ^ 2 * n := by
    have hh := mul_le_mul_of_nonneg_left hδN (sq_nonneg δ)
    nlinarith
  have hlarge' : δ ^ 2 * (n : ℝ) ^ 2 ≤ ‖∑ j ∈ Finset.range n, realQuadraticPhase α β j‖ ^ 2 := by
    have hh : δ * (n : ℝ) ≤ ‖∑ j ∈ Finset.range n, realQuadraticPhase α β j‖ := by
      have ht := mul_le_mul_of_nonneg_left hnNR hδ.le
      linarith
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ δ * (n : ℝ)) hh 2
    nlinarith
  obtain ⟨q, hq, hqsize, hqapprox⟩ := effective_quadratic_inverse α β (δ ^ 2) n hn
    (sq_pos_of_pos hδ) (by nlinarith) hnscale hlarge'
  refine ⟨q, hq, hqsize, hqapprox.trans ?_⟩
  have hden : δ ^ 4 * (N : ℝ) ^ 2 ≤ δ ^ 2 * (n : ℝ) ^ 2 := by
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ δ * (N : ℝ)) hδN 2
    have hh := mul_le_mul_of_nonneg_left hs (sq_nonneg δ)
    nlinarith
  have hB : 0 ≤ 1024 * (1 + 2 * Real.log (N : ℝ)) := by
    have hl : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
    positivity
  calc
    _ ≤ 1024 * (1 + 2 * Real.log (N : ℝ)) / (δ ^ 2 * (n : ℝ) ^ 2) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left hB (by positivity) hden

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_RescaledWeightVariation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform variation of the rescaled smooth weight -/

namespace Ostmann

open scoped BigOperators

theorem rescaledPhaseWeight_variation (Φ : ℝ → ℂ) (ξ Y B D : ℝ) (N : ℕ)
    (hY : 0 < Y) (hD : 0 ≤ D)
    (hbound : ∀ x, ‖Φ x‖ ≤ B)
    (hlip : ∀ x y, ‖Φ x - Φ y‖ ≤ D * |x - y|) :
    discreteVariation (rescaledPhaseWeight Φ ξ Y) N ≤ B + D * N / Y := by
  have hstep : ∀ j : ℕ, ‖rescaledPhaseWeight Φ ξ Y (j + 1) -
      rescaledPhaseWeight Φ ξ Y j‖ ≤ D / Y := by
    intro j
    have h := hlip ((((j + 1 : ℕ) : ℝ) + ξ) / Y) (((j : ℝ) + ξ) / Y)
    have heq : ((((j + 1 : ℕ) : ℝ) + ξ) / Y - ((j : ℝ) + ξ) / Y) = 1 / Y := by
      push_cast
      ring
    rw [heq, abs_of_pos (one_div_pos.mpr hY)] at h
    simpa only [rescaledPhaseWeight, mul_one_div] using h
  have hsum : (∑ j ∈ Finset.range (N - 1), ‖rescaledPhaseWeight Φ ξ Y (j + 1) -
      rescaledPhaseWeight Φ ξ Y j‖) ≤ (N - 1 : ℕ) * (D / Y) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.range (N - 1)) (fun j _ => hstep j)
  have hcard : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
  have hsum' := hsum.trans (mul_le_mul_of_nonneg_right hcard (div_nonneg hD hY.le))
  have hend := hbound (((N - 1 : ℕ) + ξ) / Y)
  unfold discreteVariation
  change ‖Φ (((N - 1 : ℕ) + ξ) / Y)‖ + _ ≤ _
  calc
    _ ≤ B + (N : ℝ) * (D / Y) := add_le_add hend hsum'
    _ = _ := by ring

theorem rescaledPhaseWeight_variation_uniform (Φ : ℝ → ℂ) (ξ Y B D C : ℝ) (N : ℕ)
    (hY : 0 < Y) (hD : 0 ≤ D) (hN : (N : ℝ) ≤ C * Y)
    (hbound : ∀ x, ‖Φ x‖ ≤ B)
    (hlip : ∀ x y, ‖Φ x - Φ y‖ ≤ D * |x - y|) :
    discreteVariation (rescaledPhaseWeight Φ ξ Y) N ≤ B + D * C := by
  apply (rescaledPhaseWeight_variation Φ ξ Y B D N hY hD hbound hlip).trans
  have hn' := (div_le_iff₀ hY).mpr hN
  have hh := mul_le_mul_of_nonneg_left hn' hD
  rw [mul_div_assoc]
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SchwartzWeightVariation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete variation bounds for the quadratic Schwartz weight -/

namespace Ostmann

open scoped SchwartzMap

theorem schwartz_norm_sub_le (Φ : 𝓢(ℝ, ℂ)) (x y : ℝ) :
    ‖Φ x - Φ y‖ ≤ SchwartzMap.seminorm ℝ 0 1 Φ * |x - y| := by
  have hd (z : ℝ) : ‖fderiv ℝ Φ z‖ ≤ SchwartzMap.seminorm ℝ 0 1 Φ := by
    simpa only [norm_iteratedFDeriv_one] using Φ.norm_iteratedFDeriv_le_seminorm ℝ 1 z
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_fderiv_le
    (𝕜 := ℝ) (s := Set.univ) (fun _ _ => Φ.differentiableAt)
    (fun z _ => hd z) convex_univ (Set.mem_univ y) (Set.mem_univ x)

theorem schwartz_rescaled_variation (Φ : 𝓢(ℝ, ℂ)) (ξ Y C : ℝ) (N : ℕ)
    (hY : 0 < Y) (hN : (N : ℝ) ≤ C * Y) :
    discreteVariation (rescaledPhaseWeight Φ ξ Y) N ≤
      SchwartzMap.seminorm ℝ 0 0 Φ + SchwartzMap.seminorm ℝ 0 1 Φ * C := by
  have hD : 0 ≤ SchwartzMap.seminorm ℝ 0 1 Φ :=
    (norm_nonneg _).trans (Φ.norm_iteratedFDeriv_le_seminorm ℝ 1 0)
  exact rescaledPhaseWeight_variation_uniform Φ ξ Y _ _ C N hY hD hN
    (Φ.norm_le_seminorm ℝ) (schwartz_norm_sub_le Φ)

theorem quadratic_schwartz_rescaled_variation (Φ : 𝓢(ℝ, ℂ)) (ξ Y C : ℝ) (N : ℕ)
    (hY : 0 < Y) (hN : (N : ℝ) ≤ C * Y) :
    discreteVariation (fun j : ℕ => Φ ((((j : ℝ) + ξ) / Y) ^ 2)) N ≤
      SchwartzMap.seminorm ℝ 0 0 (quadraticSchwartzWeight Φ) +
        SchwartzMap.seminorm ℝ 0 1 (quadraticSchwartzWeight Φ) * C :=
  schwartz_rescaled_variation (quadraticSchwartzWeight Φ) ξ Y C N hY hN

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_KernelResidueCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SquarePullbackNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The small-kernel quadratic pullback norm -/

namespace Ostmann

open scoped BigOperators

/-- Vanishing at nonunits means only unit square fibers contribute.
The general unit-root bound loses at most an absolute factor two. -/
theorem square_pullback_energy_le (q : ℕ) [NeZero q]
    (g : ZMod q → ℂ) (hg : ∀ x, ¬IsUnit x → g x = 0) (a : ZMod q) :
    (∑ x : ZMod q, ‖g (a * x ^ 2)‖ ^ 2) ≤
      (2 : ℝ) ^ (q.primeFactors.card + 1) * ∑ y : ZMod q, ‖g y‖ ^ 2 := by
  classical
  by_cases hau : IsUnit a
  · let A := hau.unit
    have hfiber (y : ZMod q) (hy : IsUnit y) :
        ((Finset.univ : Finset (ZMod q)).filter (fun x => a * x ^ 2 = y)).card ≤
          2 ^ (q.primeFactors.card + 1) := by
      let Y := hy.unit
      have hsub : ((Finset.univ : Finset (ZMod q)).filter (fun x => a * x ^ 2 = y)) ⊆
          Finset.univ.filter (fun x => IsUnit x ∧ x ^ 2 = ((A⁻¹ * Y : (ZMod q)ˣ) : ZMod q)) := by
        intro x hx
        have he := (Finset.mem_filter.mp hx).2
        have hux : IsUnit (x * x) := by
          have hh : IsUnit (a * x ^ 2) := he ▸ hy
          simpa only [pow_two] using isUnit_of_mul_isUnit_right hh
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, isUnit_of_mul_isUnit_left hux, ?_⟩
        calc
          x ^ 2 = (A⁻¹ : (ZMod q)ˣ) * (a * x ^ 2) := by
            rw [← mul_assoc]
            have hA : (A⁻¹ : (ZMod q)ˣ) * a = (1 : ZMod q) := by
              rw [← hau.unit_spec]
              exact A.inv_mul
            rw [hA, one_mul]
          _ = ((A⁻¹ * Y : (ZMod q)ˣ) : ZMod q) := by rw [he]; simp [Y]
      exact (Finset.card_le_card hsub).trans (unit_square_residue_card_le q (A⁻¹ * Y))
    have hmaps (x : ZMod q) (_ : x ∈ (Finset.univ : Finset (ZMod q))) :
        a * x ^ 2 ∈ (Finset.univ : Finset (ZMod q)) := Finset.mem_univ _
    rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro y hy
    have he : (∑ x ∈ Finset.univ.filter (fun x : ZMod q => a * x ^ 2 = y),
        ‖g (a * x ^ 2)‖ ^ 2) =
        ((Finset.univ.filter (fun x : ZMod q => a * x ^ 2 = y)).card : ℝ) * ‖g y‖ ^ 2 := by
      calc
        _ = ∑ _x ∈ Finset.univ.filter (fun x : ZMod q => a * x ^ 2 = y), ‖g y‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [(Finset.mem_filter.mp hx).2]
        _ = _ := by simp
    rw [he]
    by_cases hyu : IsUnit y
    · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfiber y hyu) (sq_nonneg _)
    · simp [hg y hyu]
  · have hz (x : ZMod q) : g (a * x ^ 2) = 0 := by
      apply hg
      intro hh
      exact hau (isUnit_of_mul_isUnit_left hh)
    simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]
    positivity

theorem square_pullback_norm_le (q : ℕ) [NeZero q]
    (g : ZMod q → ℂ) (hg : ∀ x, ¬IsUnit x → g x = 0)
    (henergy : (∑ y : ZMod q, ‖g y‖ ^ 2) ≤ q) (a : ZMod q) :
    (∑ x : ZMod q, ‖g (a * x ^ 2)‖) ≤
      Real.sqrt ((2 : ℝ) ^ (q.primeFactors.card + 1)) * q := by
  have hsq := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ZMod q))
    (fun _ => (1 : ℝ)) (fun x => ‖g (a * x ^ 2)‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one] at hsq
  have hbound := (square_pullback_energy_le q g hg a).trans
    (mul_le_mul_of_nonneg_left henergy (by positivity))
  have hroot := Real.sq_sqrt (show 0 ≤ (2 : ℝ) ^ (q.primeFactors.card + 1) by positivity)
  have hsum : 0 ≤ ∑ x : ZMod q, ‖g (a * x ^ 2)‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have htotal := mul_le_mul_of_nonneg_left hbound (show (0 : ℝ) ≤ q by positivity)
  have hsquare : (∑ x : ZMod q, ‖g (a * x ^ 2)‖) ^ 2 ≤
      (Real.sqrt ((2 : ℝ) ^ (q.primeFactors.card + 1)) * q) ^ 2 := by
    rw [mul_pow, hroot]
    nlinarith
  exact (sq_le_sq₀ hsum (by positivity)).mp hsquare

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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

theorem densityFourier_energy_le {q : ℕ} [NeZero q] (f : ZMod q → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) : (∑ a : ZMod q, ‖densityFourier f a‖ ^ 2) ≤ q := by
  rw [densityFourier_energy]
  calc
    _ ≤ ∑ _x : ZMod q, (1 : ℝ) := Finset.sum_le_sum (fun x _ => by
      simpa using pow_le_pow_left₀ (norm_nonneg _) (hf x) 2)
    _ = _ := by simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityCRTProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the density product and its Fourier hypotheses -/

namespace Ostmann

open scoped BigOperators

/-- The hypotheses of the small-kernel bound hold for the original finite
product of centered density functions. -/
theorem densityCRTList_energy (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime)
    (hc : ps.Pairwise Nat.Coprime) (S : ∀ p : ℕ, Finset (ZMod p)) :
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
    (∑ a : ZMod ps.prod, ‖densityFourier (densityCRTList ps hp hc S).value a‖ ^ 2) ≤ ps.prod := by
  let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
  exact densityFourier_energy_le _ (densityCRTList ps hp hc S).norm_le_one

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_PrimeSetQuadratic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual quadratic density sums indexed by prime divisors -/

namespace Ostmann

open scoped BigOperators ComplexConjugate SchwartzMap

theorem primeSet_prod_le_of_subset (P U : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hU : U ⊆ P) : U.toList.prod ≤ P.toList.prod := by
  have he (Q : Finset ℕ) : Q.toList.prod = ∏ p ∈ Q, p := by
    simp
  rw [he, he]
  exact Finset.prod_le_prod_of_subset_of_one_le hU (fun _ _ => Nat.zero_le _)
    (fun p hp _ => (hP p hp).one_lt.le)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCompactCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite cutoffs for compactly supported quadratic transforms -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem quadraticDensityTerm_mem_cutoff {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (R v C : ℝ) (N s w : ℕ) (hR : 0 < R) (hv : 0 < v) (hN : 0 < N)
    (hs : N ≤ s) (hw : 0 < w) (hΦ : ∀ x : ℝ, C < x → Φ x = 0)
    (hne : quadraticDensityTerm g a θ Φ R v s w ≠ 0) :
    w ∈ quadraticCompactCutoff q R v C N := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsR : (N : ℝ) ≤ s := Nat.cast_le.mpr hs
  have hsupport : (s : ℝ) * v * (w : ℝ) ^ 2 / (R * q) ≤ C := by
    by_contra hh
    have hz := hΦ _ (lt_of_not_ge hh)
    exact hne (by simp only [quadraticDensityTerm, hz, mul_zero])
  have hb : (w : ℝ) ^ 2 ≤ C * R * q / ((N : ℝ) * v) := by
    apply (le_div_iff₀ (mul_pos hNR hv)).mpr
    have hh := (div_le_iff₀ (mul_pos hR hq)).mp hsupport
    have hm := mul_le_mul_of_nonneg_right hsR (show 0 ≤ v * (w : ℝ) ^ 2 by positivity)
    nlinarith only [hh, hm]
  exact Finset.mem_Ioc.mpr ⟨hw, Nat.le_floor (Real.le_sqrt_of_sq_le hb)⟩

/-- Compact support makes the positive quadratic series exactly finite,
with one common cutoff for every index in the dyadic segment. -/
theorem positiveQuadraticSum_eq_cutoff {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (R v C : ℝ) (N s : ℕ) (hR : 0 < R) (hv : 0 < v) (hN : 0 < N)
    (hs : N ≤ s) (hΦ : ∀ x : ℝ, C < x → Φ x = 0) :
    positiveQuadraticSum g a θ Φ R v s =
      quadraticDensitySum g (quadraticCompactCutoff q R v C N) a θ Φ R v s := by
  classical
  unfold positiveQuadraticSum quadraticDensitySum
  congr 1
  calc
    _ = ∑ w ∈ quadraticCompactCutoff q R v C N,
        if 0 < w then quadraticDensityTerm g a θ Φ R v s w else 0 := by
      apply tsum_eq_sum
      intro w hw
      by_cases hw0 : 0 < w
      · simp only [ite_eq_left hw0]
        by_contra hn
        exact hw (quadraticDensityTerm_mem_cutoff g a θ Φ R v C N s w hR hv hN hs hw0 hΦ hn)
      · simp only [ite_eq_right hw0]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w hw
      exact ite_eq_left (Finset.mem_Ioc.mp hw).1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_SmallPositiveQuadratic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The small-kernel bound for the original positive quadratic series -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem primeSet_modulus_primeFactors (U : Finset ℕ) (hU : ∀ p ∈ U, p.Prime) :
    U.toList.prod.primeFactors = U := by
  have he : U.toList.prod = ∏ p ∈ U, p := by simp
  rw [he, Nat.primeFactors_prod hU]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalQuadraticTerm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The modular and real phases in the manuscript's original summand -/

namespace Ostmann

open scoped SchwartzMap

theorem original_quadratic_real_phase (h₀ θ : ℝ) (q s v w : ℕ) :
    realAdditivePhase ((h₀ + θ) * v * (w : ℝ) ^ 2 / q) ^ s =
      realAdditivePhase ((h₀ + θ) * s * v * (w : ℝ) ^ 2 / q) := by
  rw [← realAdditivePhase_nat_mul]
  congr 1
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_SquarefreeFrequencyRectangle
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite rectangular expansion underlying the original coefficients -/

namespace Ostmann

open scoped BigOperators

theorem mem_squarefreeKernelSupport (L N s : ℕ) :
    s ∈ squarefreeKernelSupport L N ↔ 1 ≤ s ∧ s ≤ N ∧ Squarefree s ∧ s.Coprime L := by
  simp only [squarefreeKernelSupport, Finset.mem_filter, Finset.mem_Icc]
  tauto

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticResidueDecomposition
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact residue-class splitting before the inverse quadratic estimate -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem stdAddChar_nat_ratio {q : ℕ} [NeZero q] (n : ℕ) :
    ZMod.stdAddChar (n : ZMod q) = realAdditivePhase ((n : ℝ) / q) := by
  rw [← Int.cast_natCast, ZMod.stdAddChar_coe]
  unfold realAdditivePhase
  congr 1
  push_cast
  ring

theorem quadratic_phase_integer_part {q : ℕ} [NeZero q] (h₀ s v w : ℕ) (θ : ℝ) :
    realAdditivePhase (((h₀ : ℝ) + θ) * v * (w : ℝ) ^ 2 / q) ^ s =
      ZMod.stdAddChar (((h₀ * s * v : ℕ) : ZMod q) * (w : ZMod q) ^ 2) *
        realAdditivePhase (θ * s * v * (w : ℝ) ^ 2 / q) := by
  rw [original_quadratic_real_phase]
  have he : ((h₀ : ℝ) + θ) * s * v * (w : ℝ) ^ 2 / q =
      (h₀ : ℝ) * s * v * (w : ℝ) ^ 2 / q + θ * s * v * (w : ℝ) ^ 2 / q := by ring
  rw [he, realAdditivePhase_add]
  have hs := stdAddChar_nat_ratio (q := q) (h₀ * s * v * w ^ 2)
  push_cast at hs
  push_cast
  rw [hs]

theorem quadraticDensityTerm_residue_factor {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (h₀ s v w : ℕ) (θ R : ℝ) (Φ : 𝓢(ℝ, ℂ)) :
    quadraticDensityTerm g a ((h₀ : ℝ) + θ) Φ R v s w =
      quadraticResidueAmplitude g a h₀ s v (w : ZMod q) *
        quadraticResidueWave (q := q) θ Φ R s v w := by
  rw [quadraticDensityTerm, quadratic_phase_integer_part]
  simp only [quadraticResidueAmplitude, quadraticResidueWave]
  ring

theorem quadraticResidueAmplitude_norm {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (h₀ s v : ℕ) (r : ZMod q) :
    ‖quadraticResidueAmplitude g a h₀ s v r‖ = ‖g (a * r ^ 2 * (s : ZMod q))‖ := by
  simp only [quadraticResidueAmplitude, norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, mul_one]

theorem sum_by_zmod_residues {q : ℕ} [NeZero q] (W : Finset ℕ) (f : ℕ → ℂ) :
    (∑ w ∈ W, f w) = ∑ r : ZMod q, ∑ w ∈ W.filter (fun w : ℕ => (w : ZMod q) = r), f w := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  simp

theorem quadraticDensitySum_residue_decomposition {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (W : Finset ℕ) (a : ZMod q) (h₀ s v : ℕ)
    (θ R : ℝ) (Φ : 𝓢(ℝ, ℂ)) :
    quadraticDensitySum g W a ((h₀ : ℝ) + θ) Φ R v s =
      (Real.sqrt (R * q / ((s : ℝ) * v)) : ℂ)⁻¹ *
        ∑ r : ZMod q, quadraticResidueAmplitude g a h₀ s v r *
          ∑ w ∈ W.filter (fun w : ℕ => (w : ZMod q) = r), quadraticResidueWave (q := q) θ Φ R s v w := by
  rw [quadraticDensitySum, sum_by_zmod_residues (q := q)]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  have hwr := (Finset.mem_filter.mp hw).2
  rw [quadraticDensityTerm_residue_factor, hwr]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrincipalFourierGrid
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Principal Fourier terms in finite frequency families -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem smallSquarefreeKernels_spec (L N s : ℕ) (hs : s ∈ smallSquarefreeKernels L N) :
    1 ≤ s ∧ s ≤ N ∧ Squarefree s ∧ s.Coprime L ∧ s ≤ L ^ 4 := by
  obtain ⟨hs, hsmall⟩ := Finset.mem_filter.mp hs
  exact ⟨(mem_squarefreeKernelSupport L N s).mp hs |>.1,
    (mem_squarefreeKernelSupport L N s).mp hs |>.2.1,
    (mem_squarefreeKernelSupport L N s).mp hs |>.2.2.1,
    (mem_squarefreeKernelSupport L N s).mp hs |>.2.2.2, hsmall⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_CommonCenterLiftBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform lift bounds for ordered distinct prime tuples -/

namespace Ostmann

open scoped BigOperators

theorem primeTupleProduct_pos (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {r : ℕ} (e : Fin r ↪ P) : 0 < primeTupleProduct P e :=
  Finset.prod_pos (fun i _ => (hprime _ (e i).2).pos)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeTupleTranslation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the common translation for an actual tuple of primes -/

namespace Ostmann

open scoped BigOperators Classical

theorem primeTupleSet_subset (P : Finset ℕ) {k : ℕ} (e : Fin k ↪ P) :
    primeTupleSet P e ⊆ P := by
  intro p hp
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  exact (e i).property

theorem primeTupleProduct_eq_set (P : Finset ℕ) {k : ℕ} (e : Fin k ↪ P) :
    primeTupleProduct P e = (primeTupleSet P e).toList.prod := by
  simp only [primeTupleProduct, primeTupleSet, Finset.prod_toList]
  rw [Finset.prod_image]
  intro i _ j _ h
  exact e.injective (Subtype.ext h)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeProductTranslations
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # CRT translation tables indexed by the prime product alone -/

namespace Ostmann

open scoped BigOperators Classical

theorem primeTupleProduct_mem (P : Finset ℕ) {k : ℕ} (e : Fin k ↪ P) :
    primeTupleProduct P e ∈ primeSubsetProducts P k := by
  apply Finset.mem_image.mpr
  refine ⟨primeTupleSet P e, Finset.mem_powersetCard.mpr ⟨primeTupleSet_subset P e, ?_⟩, ?_⟩
  · have hc : (primeTupleSet P e).card = (Finset.univ : Finset (Fin k)).card := by
      apply Finset.card_image_iff.mpr
      intro i _ j _ he
      exact e.injective (Subtype.ext he)
    simpa only [Finset.card_univ, Fintype.card_fin] using hc
  · simpa only [Finset.prod_toList] using (primeTupleProduct_eq_set P e).symm

theorem primeTuple_member_primeFactors (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {k : ℕ} (e : Fin k ↪ P) (i : Fin k) : (e i).val ∈ (primeTupleProduct P e).primeFactors := by
  rw [primeTupleProduct_eq_set, Finset.prod_toList,
    Nat.primeFactors_prod (fun p hp => hP p (primeTupleSet_subset P e hp))]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_RationalApproximationLift
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Turning the phase approximation into the common-center integer lift -/

namespace Ostmann

theorem approximationLift_congruence (a M p : ℕ) (t b tp : ℤ)
    (hpM : p ∣ M) (ht : (p : ℤ) ∣ t - tp) :
    (p : ℤ) ∣ approximationLift a M t b - (a : ℤ) * tp := by
  have hpM' : (p : ℤ) ∣ (M : ℤ) := by exact_mod_cast hpM
  have h := dvd_sub (dvd_mul_of_dvd_right ht (a : ℤ)) (dvd_mul_of_dvd_right hpM' b)
  have heq : approximationLift a M t b - (a : ℤ) * tp =
      (a : ℤ) * (t - tp) - b * M := by
    unfold approximationLift
    ring
  rw [heq]
  exact h

theorem approximationLift_abs_bound (a M : ℕ) (hM : 0 < M) (t b : ℤ)
    (δ : ℝ) (happrox : |(a : ℝ) * ((t : ℝ) / M) - b| ≤ δ) :
    |(approximationLift a M t b : ℝ)| ≤ (M : ℝ) * δ := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have heq : (approximationLift a M t b : ℝ) =
      (M : ℝ) * ((a : ℝ) * ((t : ℝ) / M) - b) := by
    dsimp [approximationLift]
    push_cast
    field_simp
  rw [heq, abs_mul, abs_of_pos hM0]
  exact mul_le_mul_of_nonneg_left happrox hM0.le

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_WeightedQuadraticLift
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted quadratic witnesses supply the common-center lifts -/

namespace Ostmann

open scoped BigOperators

/-- Multiplying the inverse denominator by the actual quadratic coefficient
produces precisely the phase witness used by the common-center argument. -/
theorem weighted_quadratic_phase_witness (w : ℕ → ℂ) (β δ : ℝ)
    (N c Amax : ℕ) (θ : ℝ) (hN : 0 < N) (hc : 0 < c)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hscale : 512 * (1 + 2 * Real.log (N : ℝ)) ≤ δ ^ 3 * N)
    (hlarge : discreteVariation w N * (δ * N) <
      ‖∑ j ∈ Finset.range N, w j * realQuadraticPhase ((c : ℝ) * θ) β j‖)
    (hA : 1024 * (c : ℝ) / δ ^ 2 ≤ Amax) :
    ∃ a ∈ Finset.Icc 1 Amax, ∃ b : ℤ,
      |(a : ℝ) * θ - b| ≤
        1024 * (1 + 2 * Real.log (N : ℝ)) / (δ ^ 4 * (N : ℝ) ^ 2) := by
  obtain ⟨q, hq, hqbound, happrox⟩ := weighted_quadratic_inverse w ((c : ℝ) * θ) β δ N
    hN hδ hδ1 hscale hlarge
  let a := q * c
  have ha : 0 < a := Nat.mul_pos hq hc
  have habound : (a : ℝ) ≤ Amax := by
    have hh := mul_le_mul_of_nonneg_right hqbound (Nat.cast_nonneg c : (0 : ℝ) ≤ c)
    have heq : (1024 / δ ^ 2) * (c : ℝ) = 1024 * c / δ ^ 2 := by ring
    rw [heq] at hh
    exact (show (a : ℝ) ≤ 1024 * c / δ ^ 2 by exact_mod_cast hh).trans hA
  refine ⟨a, Finset.mem_Icc.mpr ⟨ha, by exact_mod_cast habound⟩,
    round ((q : ℝ) * ((c : ℝ) * θ)), ?_⟩
  convert happrox using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  dsimp [a]
  push_cast
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PositiveResidueProgression
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact finite progression of positive integers in a residue class -/

namespace Ostmann

open scoped BigOperators

theorem exists_positive_residue_representative {q : ℕ} [NeZero q] (r : ZMod q) :
    ∃ a : ℕ, 0 < a ∧ a ≤ q ∧ (a : ZMod q) = r := by
  by_cases hr : r.val = 0
  · refine ⟨q, NeZero.pos q, le_rfl, ?_⟩
    have hz : r = 0 := by simpa only [hr, Nat.cast_zero] using r.natCast_zmod_val.symm
    simp [hz]
  · exact ⟨r.val, Nat.pos_of_ne_zero hr, r.val_lt.le, r.natCast_zmod_val⟩

theorem positive_residue_progression (q a W : ℕ) (hq : 0 < q)
    (ha : 0 < a) (haq : a ≤ q) :
    ((Finset.Ioc 0 W).filter (fun w => w ≡ a [MOD q])) =
      (Finset.range ((W + q - a) / q)).image (fun j => a + q * j) := by
  classical
  have haqW : a ≤ W + q := by omega
  have hsub : W + q - a + a = W + q := Nat.sub_add_cancel haqW
  ext w
  constructor
  · intro hw
    obtain ⟨hw, hmod⟩ := Finset.mem_filter.mp hw
    obtain ⟨hw0, hwW⟩ := Finset.mem_Ioc.mp hw
    have haw : a ≤ w := by
      rcases lt_or_eq_of_le haq with haq' | heq
      · have hm : w % q = a := (show w % q = a % q from hmod).trans (Nat.mod_eq_of_lt haq')
        rw [← hm]
        exact Nat.mod_le w q
      · have hqw : q ∣ w := by
          apply Nat.dvd_of_mod_eq_zero
          simpa only [heq, Nat.mod_self] using (show w % q = a % q from hmod)
        exact heq ▸ Nat.le_of_dvd hw0 hqw
    obtain ⟨j, hj⟩ := hmod.symm.dvd'
    have hval : a + q * j = w := by omega
    refine Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr ?_, hval⟩
    apply Nat.lt_of_succ_le
    apply (Nat.le_div_iff_mul_le hq).mpr
    nlinarith
  · intro hw
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
    have hh := (Nat.le_div_iff_mul_le hq).mp (Nat.succ_le_of_lt (Finset.mem_range.mp hj))
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨by omega, ?_⟩, ?_⟩
    · nlinarith
    · simp [Nat.ModEq]

theorem sum_positive_residue_progression (q a W : ℕ) (hq : 0 < q)
    (ha : 0 < a) (haq : a ≤ q) (f : ℕ → ℂ) :
    (∑ w ∈ (Finset.Ioc 0 W).filter (fun w => w ≡ a [MOD q]), f w) =
      ∑ j ∈ Finset.range ((W + q - a) / q), f (a + q * j) := by
  classical
  rw [positive_residue_progression q a W hq ha haq, Finset.sum_image]
  intro j _ k _ he
  exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_left_cancel he)

theorem sum_positive_zmod_progression {q : ℕ} [NeZero q] (a W : ℕ)
    (ha : 0 < a) (haq : a ≤ q) (f : ℕ → ℂ) :
    (∑ w ∈ (Finset.Ioc 0 W).filter (fun w : ℕ => (w : ZMod q) = a), f w) =
      ∑ j ∈ Finset.range ((W + q - a) / q), f (a + q * j) := by
  simp_rw [ZMod.natCast_eq_natCast_iff]
  exact sum_positive_residue_progression q a W (NeZero.pos q) ha haq f

/-- The floor cutoff loses less than two progression steps, uniformly in the
residue. This keeps the inverse estimate at the original quadratic scale. -/
theorem positive_progression_length_bounds (q a : ℕ) (B Y : ℝ)
    (hq : 0 < q) (ha : 0 < a) (haq : a ≤ q) (hB : 3 ≤ B) (hY : 1 ≤ Y) :
    let W := ⌊B * q * Y⌋₊
    let N := (W + q - a) / q
    Y ≤ (N : ℝ) ∧ (N : ℝ) ≤ (B + 1) * Y := by
  dsimp only
  let W := ⌊B * q * Y⌋₊
  let N := (W + q - a) / q
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have haqR : (a : ℝ) ≤ q := by exact_mod_cast haq
  have hfloor : (W : ℝ) ≤ B * q * Y := Nat.floor_le (by positivity)
  have hfloor' : B * q * Y < (W : ℝ) + 1 := Nat.lt_floor_add_one _
  have hsub : W + q - a + a = W + q := Nat.sub_add_cancel (by omega)
  have hdiv : N * q ≤ W + q - a := Nat.div_mul_le_self _ _
  have hdiv' : W + q - a < (N + 1) * q := by
    exact (Nat.div_lt_iff_lt_mul hq).mp (Nat.lt_succ_self N)
  have hsubR : ((W + q - a : ℕ) : ℝ) + a = (W : ℝ) + q := by exact_mod_cast hsub
  have hdivR : (N : ℝ) * q ≤ ((W + q - a : ℕ) : ℝ) := by exact_mod_cast hdiv
  have hdivR' : ((W + q - a : ℕ) : ℝ) < ((N : ℝ) + 1) * q := by exact_mod_cast hdiv'
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  constructor
  · have hBY : 3 * Y ≤ B * Y := mul_le_mul_of_nonneg_right hB (by linarith)
    have hYq : 1 ≤ Y * q := by nlinarith
    have hBYq : 3 * Y * q ≤ B * q * Y := by nlinarith [mul_le_mul_of_nonneg_right hBY hqpos.le]
    nlinarith
  · have hYq : (q : ℝ) ≤ Y * q := le_mul_of_one_le_left hqpos.le hY
    nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticProgressionPhase
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual progression has quadratic coefficient s*v*q*theta -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem quadratic_progression_weight_argument (q s v a j : ℕ) (R : ℝ)
    (hq : 0 < q) (hs : 0 < s) (hv : 0 < v) (hR : 0 < R) :
    (s : ℝ) * v * ((a + q * j : ℕ) : ℝ) ^ 2 / (R * q) =
      (((j : ℝ) + (a : ℝ) / q) / Real.sqrt (R / ((s : ℝ) * v * q))) ^ 2 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  rw [div_pow, Real.sq_sqrt (by positivity)]
  push_cast
  field_simp
  ring

theorem quadratic_progression_phase (q s v a j : ℕ) (θ : ℝ) (hq : 0 < q) :
    realAdditivePhase (θ * s * v * ((a + q * j : ℕ) : ℝ) ^ 2 / q) =
      realAdditivePhase (θ * s * v * (a : ℝ) ^ 2 / q) *
        realQuadraticPhase (((s * v * q : ℕ) : ℝ) * θ) (2 * θ * s * v * a) j := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [realQuadraticPhase, ← realAdditivePhase_add]
  congr 1
  push_cast
  field_simp
  ring

theorem quadraticResidueWave_progression (q s v a j : ℕ) (θ R : ℝ)
    (Φ : 𝓢(ℝ, ℂ)) (hq : 0 < q) (hs : 0 < s) (hv : 0 < v) (hR : 0 < R) :
    quadraticResidueWave (q := q) θ Φ R s v (a + q * j) =
      realAdditivePhase (θ * s * v * (a : ℝ) ^ 2 / q) *
        (Φ ((((j : ℝ) + (a : ℝ) / q) / Real.sqrt (R / ((s : ℝ) * v * q))) ^ 2) *
          realQuadraticPhase (((s * v * q : ℕ) : ℝ) * θ) (2 * θ * s * v * a) j) := by
  rw [quadraticResidueWave, quadratic_progression_weight_argument q s v a j R hq hs hv hR,
    quadratic_progression_phase q s v a j θ hq]
  ring

theorem quadratic_progression_sum_norm (q s v a N : ℕ) (θ R : ℝ)
    (Φ : 𝓢(ℝ, ℂ)) (hq : 0 < q) (hs : 0 < s) (hv : 0 < v) (hR : 0 < R) :
    ‖∑ j ∈ Finset.range N, quadraticResidueWave (q := q) θ Φ R s v (a + q * j)‖ =
      ‖∑ j ∈ Finset.range N,
        Φ ((((j : ℝ) + (a : ℝ) / q) / Real.sqrt (R / ((s : ℝ) * v * q))) ^ 2) *
          realQuadraticPhase (((s * v * q : ℕ) : ℝ) * θ) (2 * θ * s * v * a) j‖ := by
  simp_rw [quadraticResidueWave_progression q s v a _ θ R Φ hq hs hv hR]
  rw [← Finset.mul_sum, norm_mul, norm_realAdditivePhase, one_mul]

theorem quadratic_progression_weight_variation (q s v a N : ℕ) (R C : ℝ)
    (Φ : 𝓢(ℝ, ℂ)) (hq : 0 < q) (hs : 0 < s) (hv : 0 < v) (hR : 0 < R)
    (hN : (N : ℝ) ≤ C * Real.sqrt (R / ((s : ℝ) * v * q))) :
    discreteVariation (fun j : ℕ =>
      Φ ((((j : ℝ) + (a : ℝ) / q) / Real.sqrt (R / ((s : ℝ) * v * q))) ^ 2)) N ≤
      SchwartzMap.seminorm ℝ 0 0 (quadraticSchwartzWeight Φ) +
        SchwartzMap.seminorm ℝ 0 1 (quadraticSchwartzWeight Φ) * C := by
  apply quadratic_schwartz_rescaled_variation
  · have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hsR : (0 : ℝ) < s := by exact_mod_cast hs
    have hvR : (0 : ℝ) < v := by exact_mod_cast hv
    exact Real.sqrt_pos.mpr (by positivity)
  · exact hN

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticResidueExtraction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A large original quadratic sum forces a large residue progression -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem quadraticResidueAmplitude_mass {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (hg : ∀ x, ¬IsUnit x → g x = 0)
    (henergy : (∑ x : ZMod q, ‖g x‖ ^ 2) ≤ q)
    (a : ZMod q) (h₀ s v : ℕ) :
    (∑ r : ZMod q, ‖quadraticResidueAmplitude g a h₀ s v r‖) ≤
      Real.sqrt ((2 : ℝ) ^ (q.primeFactors.card + 1)) * q := by
  simp only [quadraticResidueAmplitude_norm]
  have he (r : ZMod q) : a * r ^ 2 * (s : ZMod q) = (a * s) * r ^ 2 := by ring
  simp_rw [he]
  exact square_pullback_norm_le q g hg henergy (a * s)

theorem quadraticDensitySum_large_residue {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (hg : ∀ x, ¬IsUnit x → g x = 0)
    (henergy : (∑ x : ZMod q, ‖g x‖ ^ 2) ≤ q)
    (W : Finset ℕ) (a : ZMod q) (h₀ s v : ℕ) (θ R A : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hs : 0 < s) (hv : 0 < v) (hR : 0 < R) (hA : 0 ≤ A)
    (hlarge : (Real.sqrt ((2 : ℝ) ^ (q.primeFactors.card + 1)) * q) * A <
      Real.sqrt (R * q / ((s : ℝ) * v)) *
        ‖quadraticDensitySum g W a ((h₀ : ℝ) + θ) Φ R v s‖) :
    ∃ r : ZMod q, A < ‖∑ w ∈ W.filter (fun w : ℕ => (w : ZMod q) = r),
      quadraticResidueWave (q := q) θ Φ R s v w‖ := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hQ : 0 < Real.sqrt (R * q / ((s : ℝ) * v)) := Real.sqrt_pos.mpr (by positivity)
  rw [quadraticDensitySum_residue_decomposition, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hQ, ← mul_assoc, mul_inv_cancel₀ hQ.ne', one_mul] at hlarge
  by_contra! hn
  have hb : ‖∑ r : ZMod q, quadraticResidueAmplitude g a h₀ s v r *
      ∑ w ∈ W.filter (fun w : ℕ => (w : ZMod q) = r),
        quadraticResidueWave (q := q) θ Φ R s v w‖ ≤
      (Real.sqrt ((2 : ℝ) ^ (q.primeFactors.card + 1)) * q) * A := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ r : ZMod q, ‖quadraticResidueAmplitude g a h₀ s v r‖ * A := by
        apply Finset.sum_le_sum
        intro r _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hn r) (norm_nonneg _)
      _ ≤ _ := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (quadraticResidueAmplitude_mass g hg henergy a h₀ s v) hA
  exact (not_lt_of_ge hb) hlarge

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticProgressionExtraction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # From the original positive sum to its long weighted progression -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem quadratic_cutoff_scale (q s v : ℕ) (R B : ℝ)
    (hq : 0 < q) (hs : 0 < s) (hv : 0 < v) (hR : 0 < R) (hB : 0 ≤ B) :
    Real.sqrt (B ^ 2 * R * q / ((s : ℝ) * v)) =
      B * q * Real.sqrt (R / ((s : ℝ) * v * q)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  field_simp

theorem quadratic_normalizer_progression_scale (q s v : ℕ) (R : ℝ)
    (hq : 0 < q) (hs : 0 < s) (hv : 0 < v) (hR : 0 < R) :
    Real.sqrt (R * q / ((s : ℝ) * v)) =
      q * Real.sqrt (R / ((s : ℝ) * v * q)) := by
  simpa using quadratic_cutoff_scale q s v R 1 hq hs hv hR zero_le_one

/-- The estimate is extracted from the actual compactly supported positive
series. Its hypothesis is the explicit large-sum event in the manuscript. -/
theorem positiveQuadraticSum_large_progression {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (hg : ∀ x, ¬IsUnit x → g x = 0)
    (henergy : (∑ x : ZMod q, ‖g x‖ ^ 2) ≤ q)
    (a : ZMod q) (h₀ s v : ℕ) (θ R B A : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hs : 0 < s) (hv : 0 < v) (hR : 0 < R) (hB : 3 ≤ B)
    (hY : 1 ≤ Real.sqrt (R / ((s : ℝ) * v * q))) (hA : 0 ≤ A)
    (hΦ : ∀ x : ℝ, B ^ 2 < x → Φ x = 0)
    (hlarge : (Real.sqrt ((2 : ℝ) ^ (q.primeFactors.card + 1)) * q) * A <
      Real.sqrt (R * q / ((s : ℝ) * v)) *
        ‖positiveQuadraticSum g a ((h₀ : ℝ) + θ) Φ R v s‖) :
    ∃ r : ℕ, 0 < r ∧ r ≤ q ∧
      let N := (⌊B * q * Real.sqrt (R / ((s : ℝ) * v * q))⌋₊ + q - r) / q
      Real.sqrt (R / ((s : ℝ) * v * q)) ≤ (N : ℝ) ∧
      (N : ℝ) ≤ (B + 1) * Real.sqrt (R / ((s : ℝ) * v * q)) ∧
      A < ‖∑ j ∈ Finset.range N,
        Φ ((((j : ℝ) + (r : ℝ) / q) / Real.sqrt (R / ((s : ℝ) * v * q))) ^ 2) *
          realQuadraticPhase (((s * v * q : ℕ) : ℝ) * θ) (2 * θ * s * v * r) j‖ := by
  have hq := NeZero.pos q
  rw [positiveQuadraticSum_eq_cutoff g a _ Φ R v (B ^ 2) s s hR
    (by exact_mod_cast hv) hs le_rfl hΦ] at hlarge
  rw [quadraticCompactCutoff, quadratic_cutoff_scale q s v R B hq hs hv hR (by linarith)] at hlarge
  obtain ⟨r, hr⟩ := quadraticDensitySum_large_residue g hg henergy _ a h₀ s v θ R A Φ
    hs hv hR hA hlarge
  obtain ⟨r₀, hr₀, hrq, hrval⟩ := exists_positive_residue_representative r
  refine ⟨r₀, hr₀, hrq, ?_⟩
  dsimp only
  obtain ⟨hNlo, hNhi⟩ := positive_progression_length_bounds q r₀ B _ hq hr₀ hrq hB hY
  refine ⟨hNlo, hNhi, ?_⟩
  rw [← hrval, sum_positive_zmod_progression r₀ _ hr₀ hrq,
    quadratic_progression_sum_norm q s v r₀ _ θ R Φ hq hs hv hR] at hr
  exact hr

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_PositiveQuadraticInverse
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The rational approximation forced by the actual quadratic witness

The only hypotheses below are the density energy, compact support, the
explicit large-sum event, and numerical scale bounds. The inverse quadratic
estimate and the progression reduction are proved in the imported modules.
-/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem quadraticVariationBudget_one_le (Φ : 𝓢(ℝ, ℂ)) (B : ℝ) (hB : 3 ≤ B) :
    1 ≤ quadraticVariationBudget Φ B := by
  unfold quadraticVariationBudget
  have h₀ : 0 ≤ SchwartzMap.seminorm ℝ 0 0 (quadraticSchwartzWeight Φ) := by positivity
  have h₁ : 0 ≤ SchwartzMap.seminorm ℝ 0 1 (quadraticSchwartzWeight Φ) * (B + 1) := by positivity
  linarith

theorem quadratic_witness_large_progression {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (hg : ∀ x, ¬IsUnit x → g x = 0)
    (henergy : (∑ x : ZMod q, ‖g x‖ ^ 2) ≤ q)
    (a : ZMod q) (h₀ s v : ℕ) (θ R B K : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hs : 0 < s) (hv : 0 < v) (hR : 0 < R) (hB : 3 ≤ B)
    (hY : 1 ≤ Real.sqrt (R / ((s : ℝ) * v * q)))
    (hΦ : ∀ x : ℝ, B ^ 2 < x → Φ x = 0)
    (hlarge : Real.sqrt ((2 : ℝ) ^ q.primeFactors.card) * Real.exp (-K) <
      ‖positiveQuadraticSum g a ((h₀ : ℝ) + θ) Φ R v s‖) :
    ∃ r : ℕ, 0 < r ∧ r ≤ q ∧
      let Y := Real.sqrt (R / ((s : ℝ) * v * q))
      let N := (⌊B * q * Y⌋₊ + q - r) / q
      Y ≤ (N : ℝ) ∧ (N : ℝ) ≤ (B + 1) * Y ∧
      Y * Real.exp (-K) / 2 < ‖∑ j ∈ Finset.range N,
        Φ ((((j : ℝ) + (r : ℝ) / q) / Y) ^ 2) *
          realQuadraticPhase (((s * v * q : ℕ) : ℝ) * θ) (2 * θ * s * v * r) j‖ := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hYpos : 0 < Real.sqrt (R / ((s : ℝ) * v * q)) := by linarith
  apply positiveQuadraticSum_large_progression g hg henergy a h₀ s v θ R B
    (Real.sqrt (R / ((s : ℝ) * v * q)) * Real.exp (-K) / 2) Φ
    hs hv hR hB hY (by positivity) hΦ
  rw [quadratic_normalizer_progression_scale q s v R (NeZero.pos q) hs hv hR]
  have hpow : Real.sqrt ((2 : ℝ) ^ (q.primeFactors.card + 1)) ≤
      2 * Real.sqrt ((2 : ℝ) ^ q.primeFactors.card) := by
    rw [pow_succ, Real.sqrt_mul (by positivity)]
    have htwo : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    nlinarith [Real.sqrt_nonneg ((2 : ℝ) ^ q.primeFactors.card)]
  calc
    _ ≤ (q * Real.sqrt (R / ((s : ℝ) * v * q))) *
        (Real.sqrt ((2 : ℝ) ^ q.primeFactors.card) * Real.exp (-K)) := by
      have hh := mul_le_mul_of_nonneg_right hpow
        (show 0 ≤ (q : ℝ) * Real.sqrt (R / ((s : ℝ) * v * q)) * Real.exp (-K) / 2 by positivity)
      nlinarith
    _ < _ := mul_lt_mul_of_pos_left hlarge (mul_pos hqR hYpos)

theorem positiveQuadraticSum_phase_witness {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (hg : ∀ x, ¬IsUnit x → g x = 0)
    (henergy : (∑ x : ZMod q, ‖g x‖ ^ 2) ≤ q)
    (a : ZMod q) (h₀ s v Amax : ℕ) (θ R B K : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hs : 0 < s) (hv : 0 < v) (hR : 0 < R) (hB : 3 ≤ B) (hK : 0 ≤ K)
    (hY : 1 ≤ Real.sqrt (R / ((s : ℝ) * v * q)))
    (hΦ : ∀ x : ℝ, B ^ 2 < x → Φ x = 0)
    (hlarge : Real.sqrt ((2 : ℝ) ^ q.primeFactors.card) * Real.exp (-K) <
      ‖positiveQuadraticSum g a ((h₀ : ℝ) + θ) Φ R v s‖)
    (hscale : let Y := Real.sqrt (R / ((s : ℝ) * v * q))
      let δ := Real.exp (-K) / (4 * quadraticVariationBudget Φ B * (B + 1))
      512 * (1 + 2 * Real.log ((B + 1) * Y)) ≤ δ ^ 3 * Y)
    (hA : 1024 * ((s * v * q : ℕ) : ℝ) /
      (Real.exp (-K) / (4 * quadraticVariationBudget Φ B * (B + 1))) ^ 2 ≤ Amax) :
    ∃ c ∈ Finset.Icc 1 Amax, ∃ b : ℤ,
      |(c : ℝ) * θ - b| ≤
        1024 * (1 + 2 * Real.log ((B + 1) * Real.sqrt (R / ((s : ℝ) * v * q)))) /
          ((Real.exp (-K) / (4 * quadraticVariationBudget Φ B * (B + 1))) ^ 4 *
            (Real.sqrt (R / ((s : ℝ) * v * q))) ^ 2) := by
  let Y := Real.sqrt (R / ((s : ℝ) * v * q))
  let D := quadraticVariationBudget Φ B
  let δ := Real.exp (-K) / (4 * D * (B + 1))
  have hD : 1 ≤ D := quadraticVariationBudget_one_le Φ B hB
  have hDpos : 0 < D := by linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    have he : Real.exp (-K) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    dsimp [δ]
    apply (div_le_one (by positivity)).mpr
    nlinarith
  have hYpos : 0 < Y := by dsimp [Y]; linarith
  obtain ⟨r, hr, hrq, hNlo, hNhi, hsum⟩ := quadratic_witness_large_progression
    g hg henergy a h₀ s v θ R B K Φ hs hv hR hB hY hΦ hlarge
  let N := (⌊B * q * Y⌋₊ + q - r) / q
  let w := fun j : ℕ => Φ ((((j : ℝ) + (r : ℝ) / q) / Y) ^ 2)
  have hNpos : (0 : ℝ) < N := hYpos.trans_le hNlo
  have hN : 0 < N := by exact_mod_cast hNpos
  have hlog : Real.log (N : ℝ) ≤ Real.log ((B + 1) * Y) :=
    Real.log_le_log hNpos hNhi
  have hscaleN : 512 * (1 + 2 * Real.log (N : ℝ)) ≤ δ ^ 3 * N := by
    have hh := mul_le_mul_of_nonneg_left hNlo (show 0 ≤ δ ^ 3 by positivity)
    dsimp only at hscale
    change 512 * (1 + 2 * Real.log ((B + 1) * Y)) ≤ δ ^ 3 * Y at hscale
    linarith
  have hvar : discreteVariation w N ≤ D := by
    apply (quadratic_progression_weight_variation q s v r N R (B + 1) Φ
      (NeZero.pos q) hs hv hR hNhi).trans
    dsimp [D, quadraticVariationBudget]
    linarith
  have hweighted : discreteVariation w N * (δ * N) <
      ‖∑ j ∈ Finset.range N, w j *
        realQuadraticPhase (((s * v * q : ℕ) : ℝ) * θ) (2 * θ * s * v * r) j‖ := by
    have heq : D * (δ * ((B + 1) * Y)) = Y * Real.exp (-K) / 4 := by
      dsimp [δ]
      field_simp
    have hh := mul_le_mul_of_nonneg_left hNhi (show 0 ≤ D * δ by positivity)
    have hvv := mul_le_mul_of_nonneg_right hvar (show 0 ≤ δ * (N : ℝ) by positivity)
    change Y * Real.exp (-K) / 2 < _ at hsum
    calc
      _ ≤ D * (δ * ((B + 1) * Y)) := by nlinarith
      _ = Y * Real.exp (-K) / 4 := heq
      _ < Y * Real.exp (-K) / 2 := by nlinarith [mul_pos hYpos (Real.exp_pos (-K))]
      _ < _ := hsum
  obtain ⟨c, hc, b, hab⟩ := weighted_quadratic_phase_witness w (2 * θ * s * v * r) δ
    N (s * v * q) Amax θ hN (Nat.mul_pos (Nat.mul_pos hs hv) (NeZero.pos q))
    hδ hδ1 hscaleN hweighted hA
  refine ⟨c, hc, b, hab.trans ?_⟩
  have hnum : 0 ≤ 1024 * (1 + 2 * Real.log ((B + 1) * Y)) := by
    have hlog0 : 0 ≤ Real.log ((B + 1) * Y) := Real.log_nonneg (by nlinarith [hY])
    positivity
  calc
    _ ≤ 1024 * (1 + 2 * Real.log ((B + 1) * Y)) / (δ ^ 4 * (N : ℝ) ^ 2) := by
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left hnum (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hYpos.le hNlo 2) (by positivity))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticInverseBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The explicit inverse losses are subexponential at the chosen K scale -/

namespace Ostmann

open Filter Asymptotics

theorem eventual_kernel_scale_sublinear (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ K : ℝ,
      K ≤ T ^ (9999999 / 10000000 : ℝ) → K ≤ ε * T := by
  have hp := (tendsto_rpow_atTop (show (0 : ℝ) < 1 - 9999999 / 10000000 by norm_num)).eventually_ge_atTop
    (1 / ε)
  filter_upwards [hp, eventually_ge_atTop (1 : ℝ)] with T hpow hT K hK
  have hTpos : 0 < T := by linarith
  have hh := mul_le_mul_of_nonneg_right hpow
    (Real.rpow_nonneg hTpos.le (9999999 / 10000000 : ℝ))
  rw [← Real.rpow_add hTpos,
    show (1 - 9999999 / 10000000 : ℝ) + 9999999 / 10000000 = 1 by norm_num,
    Real.rpow_one] at hh
  have hh' := mul_le_mul_of_nonneg_left hh hε.le
  have he : ε * (1 / ε * T ^ (9999999 / 10000000 : ℝ)) =
      T ^ (9999999 / 10000000 : ℝ) := by field_simp
  rw [he] at hh'
  exact hK.trans hh'

theorem eventual_quadratic_inverse_cost (A m ε : ℝ) (hA : 0 ≤ A)
    (hm : 0 ≤ m) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ K : ℝ,
      K ≤ T ^ (9999999 / 10000000 : ℝ) →
      A * (1 + T) * Real.exp (m * K) ≤ Real.exp (ε * T) := by
  have hc : 0 < ε / (2 * (m + 1)) := by positivity
  have hp₀ := ((isLittleO_pow_exp_pos_mul_atTop 0 (show 0 < ε / 2 by positivity)).const_mul_left A)
  have hp₁ := ((isLittleO_pow_exp_pos_mul_atTop 1 (show 0 < ε / 2 by positivity)).const_mul_left A)
  have hp := (hp₀.add hp₁).bound zero_lt_one
  filter_upwards [eventual_kernel_scale_sublinear _ hc, hp,
    eventually_ge_atTop (0 : ℝ)] with T hKbound hpoly hT K hK
  have hpoly' : A * (1 + T) ≤ Real.exp (ε / 2 * T) := by
    simp only [pow_zero, pow_one, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ A + A * T),
      abs_of_pos (Real.exp_pos _), one_mul] at hpoly
    nlinarith only [hpoly]
  have hmk : m * K ≤ ε / 2 * T := by
    have hh := mul_le_mul_of_nonneg_left (hKbound K hK) hm
    have hc' : m * (ε / (2 * (m + 1))) ≤ ε / 2 := by
      have hratio : m / (m + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
      calc
        _ = (ε / 2) * (m / (m + 1)) := by field_simp
        _ ≤ (ε / 2) * 1 := mul_le_mul_of_nonneg_left hratio (by positivity)
        _ = _ := mul_one _
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_right hc' hT])
  calc
    _ ≤ Real.exp (ε / 2 * T) * Real.exp (ε / 2 * T) := by
      exact mul_le_mul hpoly' (Real.exp_le_exp.mpr hmk) (Real.exp_nonneg _) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem eventual_quadratic_inverse_factor (B J : ℝ) (hB : 3 ≤ B) (hJ : 1 ≤ J) :
    ∀ᶠ T : ℝ in atTop, ∀ K Y : ℝ,
      K ≤ T ^ (9999999 / 10000000 : ℝ) →
      Real.exp (4 * T) ≤ Y → Y ≤ Real.exp (7 * T) →
      1024 * J ^ 4 * (1 + 2 * Real.log ((B + 1) * Y)) * Real.exp (4 * K) ≤
        Real.exp (T / 100) := by
  let A := 1024 * J ^ 4 * (15 + 2 * Real.log (B + 1))
  have hlogB : 0 ≤ Real.log (B + 1) := Real.log_nonneg (by linarith)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  filter_upwards [eventual_quadratic_inverse_cost A 4 (1 / 100) hA (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with T hcost hT K Y hK hYlo hYhi
  have hYpos : 0 < Y := (Real.exp_pos _).trans_le hYlo
  have hlogY : Real.log Y ≤ 7 * T := (Real.log_le_iff_le_exp hYpos).mpr hYhi
  rw [Real.log_mul (by linarith : B + 1 ≠ 0) hYpos.ne']
  have hh : 1 + 2 * (Real.log (B + 1) + Real.log Y) ≤
      (15 + 2 * Real.log (B + 1)) * (1 + T) := by nlinarith
  calc
    _ ≤ (1024 * J ^ 4 * ((15 + 2 * Real.log (B + 1)) * (1 + T))) * Real.exp (4 * K) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by positivity)) (Real.exp_nonneg _)
    _ = A * (1 + T) * Real.exp (4 * K) := by dsimp [A]; ring
    _ ≤ _ := by simpa only [one_div_mul_eq_div] using hcost K hK

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticInverseRanges
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete denominator and error ranges for the inverse step -/

namespace Ostmann

theorem quadratic_inverse_ranges (T K B J Y R c : ℝ)
    (hT : 1 ≤ T) (hK : 0 ≤ K) (hB : 3 ≤ B) (hJ : 1 ≤ J)
    (hY : Real.exp (4 * T) ≤ Y) (hR : 0 < R) (hc : 0 < c)
    (hcupper : c ≤ Real.exp (3 * T / 25)) (hscale : Y ^ 2 = R / c)
    (hfactor : 1024 * J ^ 4 * (1 + 2 * Real.log ((B + 1) * Y)) * Real.exp (4 * K) ≤
      Real.exp (T / 100)) :
    let δ := Real.exp (-K) / J
    (512 * (1 + 2 * Real.log ((B + 1) * Y)) ≤ δ ^ 3 * Y) ∧
    (1024 * c / δ ^ 2 ≤ Real.exp (13 * T / 100)) ∧
    (1024 * (1 + 2 * Real.log ((B + 1) * Y)) / (δ ^ 4 * Y ^ 2) ≤
      Real.exp (13 * T / 100) / R) := by
  let E := J * Real.exp K
  let L := 1 + 2 * Real.log ((B + 1) * Y)
  have hE : 1 ≤ E := by
    dsimp [E]
    have he : 1 ≤ Real.exp K := Real.one_le_exp_iff.mpr hK
    nlinarith
  have hEpos : 0 < E := by linarith
  have hY1 : 1 ≤ Y := (Real.one_le_exp_iff.mpr (by linarith)).trans hY
  have hYpos : 0 < Y := by linarith
  have hL : 1 ≤ L := by
    have hh : 0 ≤ Real.log ((B + 1) * Y) := Real.log_nonneg (by nlinarith)
    dsimp [L]
    linarith
  have hδ : Real.exp (-K) / J = E⁻¹ := by
    dsimp [E]
    rw [Real.exp_neg, mul_inv_rev]
    ring
  have hf : 1024 * E ^ 4 * L ≤ Real.exp (T / 100) := by
    simpa only [E, L, mul_pow, ← Real.exp_nat_mul, Nat.cast_ofNat,
      mul_assoc, mul_left_comm, mul_comm] using hfactor
  have h23 : E ^ 2 ≤ E ^ 4 := pow_le_pow_right₀ hE (by omega)
  have h34 : E ^ 3 ≤ E ^ 4 := pow_le_pow_right₀ hE (by omega)
  have hsecond : 1024 * E ^ 2 ≤ Real.exp (T / 100) := by
    apply le_trans _ hf
    nlinarith [mul_le_mul_of_nonneg_left h23 (by norm_num : (0 : ℝ) ≤ 1024),
      mul_le_mul_of_nonneg_left hL (show 0 ≤ 1024 * E ^ 4 by positivity)]
  have hthird : 512 * L * E ^ 3 ≤ Real.exp (T / 100) := by
    apply le_trans _ hf
    have hh := mul_le_mul_of_nonneg_left h34 (show 0 ≤ 512 * L by positivity)
    nlinarith [mul_nonneg (show 0 ≤ L by linarith) (show 0 ≤ E ^ 4 by positivity)]
  have hcprod : c * Real.exp (T / 100) ≤ Real.exp (13 * T / 100) := by
    calc
      _ ≤ Real.exp (3 * T / 25) * Real.exp (T / 100) :=
        mul_le_mul_of_nonneg_right hcupper (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  dsimp only
  rw [hδ]
  refine ⟨?_, ?_, ?_⟩
  · change 512 * L ≤ E⁻¹ ^ 3 * Y
    rw [inv_pow, mul_comm (E ^ 3)⁻¹ Y, ← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos hEpos _)).mpr
    exact hthird.trans ((Real.exp_le_exp.mpr (by linarith)).trans hY)
  · rw [inv_pow, div_inv_eq_mul]
    calc
      1024 * c * E ^ 2 = c * (1024 * E ^ 2) := by ring
      _ ≤ c * Real.exp (T / 100) := mul_le_mul_of_nonneg_left hsecond hc.le
      _ ≤ _ := hcprod
  · have heq : 1024 * L / (E⁻¹ ^ 4 * Y ^ 2) = (1024 * E ^ 4 * L) * c / R := by
      rw [hscale]
      field_simp
    change 1024 * L / (E⁻¹ ^ 4 * Y ^ 2) ≤ _
    rw [heq]
    apply div_le_div_of_nonneg_right _ hR.le
    calc
      _ ≤ Real.exp (T / 100) * c := mul_le_mul_of_nonneg_right hf hc.le
      _ ≤ _ := by simpa only [mul_comm] using hcprod

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_PositiveQuadraticWitness
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A witness gives the denominator and accuracy at the manuscript scales -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem quadratic_progression_scale_range (T R c : ℝ) (hT : 0 ≤ T) (hc : 1 ≤ c)
    (hcupper : c ≤ Real.exp (3 * T / 25))
    (hRlo : Real.exp (10 * T) ≤ R) (hRhi : R ≤ Real.exp (14 * T)) :
    Real.exp (4 * T) ≤ Real.sqrt (R / c) ∧
      Real.sqrt (R / c) ≤ Real.exp (7 * T) := by
  have hcpos : 0 < c := by linarith
  have hRpos : 0 < R := (Real.exp_pos _).trans_le hRlo
  constructor
  · apply Real.le_sqrt_of_sq_le
    apply (le_div_iff₀ hcpos).mpr
    rw [← Real.exp_nat_mul]
    calc
      _ ≤ Real.exp (8 * T) * Real.exp (3 * T / 25) := by
        simp only [Nat.cast_ofNat]
        rw [show 2 * (4 * T) = 8 * T by ring]
        exact mul_le_mul_of_nonneg_left hcupper (Real.exp_nonneg (8 * T))
      _ = Real.exp (8 * T + 3 * T / 25) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (10 * T) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ R := hRlo
  · apply (Real.sqrt_le_iff).mpr
    refine ⟨(Real.exp_pos _).le, ?_⟩
    rw [← Real.exp_nat_mul]
    apply (div_le_iff₀ hcpos).mpr
    have hh := mul_le_mul_of_nonneg_left hc (Real.exp_nonneg (14 * T))
    norm_num only [Nat.cast_ofNat] at *
    have he : 2 * (7 * T) = 14 * T := by ring
    rw [he]
    nlinarith

/-- The original weighted series, with the original residue argument and
the original scale R, yields a rational approximation. All numerical
inequalities needed by the inverse theorem have been discharged. -/
theorem eventual_positiveQuadraticSum_phase_witness (B : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hB : 3 ≤ B) (hΦ : ∀ x : ℝ, B ^ 2 < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (q s v : ℕ) [NeZero q] (g : ZMod q → ℂ)
      (a : ZMod q) (h₀ : ℕ) (θ R K : ℝ),
      (∀ x, ¬IsUnit x → g x = 0) → (∑ x : ZMod q, ‖g x‖ ^ 2) ≤ q →
      0 < s → 0 < v → 0 ≤ K → K ≤ T ^ (9999999 / 10000000 : ℝ) →
      ((s * v * q : ℕ) : ℝ) ≤ Real.exp (3 * T / 25) →
      Real.exp (10 * T) ≤ R → R ≤ Real.exp (14 * T) →
      Real.sqrt ((2 : ℝ) ^ q.primeFactors.card) * Real.exp (-K) <
        ‖positiveQuadraticSum g a ((h₀ : ℝ) + θ) Φ R v s‖ →
      ∃ c ∈ Finset.Icc 1 ⌈Real.exp (13 * T / 100)⌉₊, ∃ b : ℤ,
        |(c : ℝ) * θ - b| ≤ Real.exp (13 * T / 100) / R := by
  let J := 4 * quadraticVariationBudget Φ B * (B + 1)
  have hJ : 1 ≤ J := by
    have hD := quadraticVariationBudget_one_le Φ B hB
    dsimp [J]
    nlinarith
  filter_upwards [eventual_quadratic_inverse_factor B J hB hJ,
    eventually_ge_atTop (1 : ℝ)] with T hfactor hT
  intro q s v _ g a h₀ θ R K hg henergy hs hv hK hKT hcupper hRlo hRhi hlarge
  let c : ℝ := ((s * v * q : ℕ) : ℝ)
  have hc : 1 ≤ c := by
    have hp : 0 < s * v * q := Nat.mul_pos (Nat.mul_pos hs hv) (NeZero.pos q)
    dsimp [c]
    exact_mod_cast (show 1 ≤ s * v * q from hp)
  have hR : 0 < R := (Real.exp_pos _).trans_le hRlo
  have hec : c = (s : ℝ) * v * q := by dsimp [c]; push_cast; rfl
  have hyrange := quadratic_progression_scale_range T R c (by linarith) hc hcupper hRlo hRhi
  have hysq : (Real.sqrt (R / c)) ^ 2 = R / c := Real.sq_sqrt (by positivity)
  have hnum := quadratic_inverse_ranges T K B J (Real.sqrt (R / c)) R c hT hK hB hJ
    hyrange.1 hR (by linarith) hcupper hysq (hfactor K _ hKT hyrange.1 hyrange.2)
  obtain ⟨hscale, hdenom, herr⟩ := hnum
  have hY : 1 ≤ Real.sqrt (R / ((s : ℝ) * v * q)) := by
    rw [← hec]
    exact (Real.one_le_exp_iff.mpr (by linarith)).trans hyrange.1
  obtain ⟨c₀, hc₀, b, hb⟩ := positiveQuadraticSum_phase_witness g hg henergy a h₀ s v
    ⌈Real.exp (13 * T / 100)⌉₊ θ R B K Φ hs hv hR hB hK hY hΦ hlarge
    (by simpa only [J, hec] using hscale)
    (hdenom.trans (Nat.le_ceil _))
  refine ⟨c₀, hc₀, b, hb.trans ?_⟩
  simpa only [J, hec] using herr

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_DivisorQuadraticWitness
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Inverse witnesses for the genuine divisor density Fourier transforms -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem sqrt_two_pow_card (n : ℕ) :
    Real.sqrt ((2 : ℝ) ^ n) = (Real.sqrt 2) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

theorem small_divisor_coefficient_bound (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (U V : Finset ℕ) (hU : U ⊆ Q) (hV : V ⊆ Q) (s : ℕ)
    (hs : s ≤ Q.toList.prod ^ 4) :
    s * V.toList.prod * U.toList.prod ≤ Q.toList.prod ^ 6 := by
  have hu := primeSet_prod_le_of_subset Q U hQ hU
  have hv := primeSet_prod_le_of_subset Q V hQ hV
  calc
    _ ≤ Q.toList.prod ^ 4 * Q.toList.prod * Q.toList.prod := Nat.mul_le_mul
      (Nat.mul_le_mul hs hv) hu
    _ = _ := by ring

theorem eventual_primeDivisorPositive_phase_witness (B : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hB : 3 ≤ B) (hΦ : ∀ x : ℝ, B ^ 2 < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (U V : Finset ℕ) (M h₀ s : ℕ) (θ R K : ℝ),
      U ⊆ Q → V ⊆ Q → 0 < s → s ≤ Q.toList.prod ^ 4 →
      (Q.toList.prod : ℝ) ≤ Real.exp (T / 50) →
      0 ≤ K → K ≤ T ^ (9999999 / 10000000 : ℝ) →
      Real.exp (10 * T) ≤ R → R ≤ Real.exp (14 * T) →
      (Real.sqrt 2) ^ U.card * Real.exp (-K) <
        ‖primeDivisorPositive Q hQ D (divisorQuadraticScalar (quadraticInverseResidue M) V)
          (fun _ => (h₀ : ℝ) + θ) Φ R V.toList.prod U s‖ →
      ∃ c ∈ Finset.Icc 1 ⌈Real.exp (13 * T / 100)⌉₊, ∃ b : ℤ,
        |(c : ℝ) * θ - b| ≤ Real.exp (13 * T / 100) / R := by
  filter_upwards [eventual_positiveQuadraticSum_phase_witness B Φ hB hΦ] with T hT
  intro Q hQ D U V M h₀ s θ R K hU hV hs hsL hL hK hKT hRlo hRhi hlarge
  have hu : ∀ p ∈ U, p.Prime := fun p hp => hQ p (hU hp)
  have hv : ∀ p ∈ V, p.Prime := fun p hp => hQ p (hV hp)
  let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime U hu)).ne'⟩
  have hVpos : 0 < V.toList.prod := prime_list_prod_pos _ (primeSet_list_prime V hv)
  have hc : ((s * V.toList.prod * U.toList.prod : ℕ) : ℝ) ≤ Real.exp (3 * T / 25) := by
    have hh : ((s * V.toList.prod * U.toList.prod : ℕ) : ℝ) ≤ (Q.toList.prod : ℝ) ^ 6 := by
      exact_mod_cast small_divisor_coefficient_bound Q hQ U V hU hV s hsL
    apply hh.trans
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg Q.toList.prod : (0 : ℝ) ≤ Q.toList.prod) hL 6
    rw [← Real.exp_nat_mul] at hp
    convert hp using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    norm_num
    ring
  simp only [primeDivisorPositive, dite_eq_left hU] at hlarge
  apply hT U.toList.prod s V.toList.prod
    (densityFourier (densityCRTList U.toList (primeSet_list_prime U hu)
      (primeSet_list_coprime U hu) D).value)
    (divisorQuadraticScalar (quadraticInverseResidue M) V U) h₀ θ R K
    (densityCRTList U.toList (primeSet_list_prime U hu) (primeSet_list_coprime U hu) D).fourier_nonunit
    (densityCRTList_energy _ _ _ _) hs hVpos hK hKT hc hRlo hRhi
  simpa only [primeSet_modulus_primeFactors U hu, sqrt_two_pow_card] using hlarge

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticWitnessLift
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An actual small-kernel witness supplies the simultaneous integer lift -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem eventual_quadratic_witness_lift (B : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hB : 3 ≤ B) (hΦ : ∀ x : ℝ, B ^ 2 < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (P : Finset ℕ) (_hP : ∀ p ∈ P, p.Prime)
      (k : ℕ) (e : Fin k ↪ P) (t : ℕ → ℤ) (tM : ℤ) (h₀ : ℕ) (X : ℝ),
      0 < X → (Q.toList.prod : ℝ) ≤ Real.exp (T / 50) →
      (Q.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
      Real.exp (10 * T) ≤ (primeTupleProduct P e : ℝ) / X →
      (primeTupleProduct P e : ℝ) / X ≤ Real.exp (14 * T) →
      (∀ i, ((e i).1 : ℤ) ∣ tM - t (e i).1) →
      (∃ U V : Finset ℕ, U ⊆ Q ∧ V ⊆ Q ∧ ∃ s : ℕ, 0 < s ∧ s ≤ Q.toList.prod ^ 4 ∧
        (Real.sqrt 2) ^ U.card * Real.exp (-(Q.card : ℝ)) <
          ‖primeDivisorPositive Q hQ D
            (divisorQuadraticScalar (quadraticInverseResidue (primeTupleProduct P e)) V)
            (fun _ => (h₀ : ℝ) + (tM : ℝ) / primeTupleProduct P e) Φ
            ((primeTupleProduct P e : ℝ) / X) V.toList.prod U s‖) →
      ∃ a ∈ Finset.Icc 1 ⌈Real.exp (13 * T / 100)⌉₊, ∃ n : ℤ,
        |(n : ℝ)| ≤ X * Real.exp (13 * T / 100) ∧
        ∀ i, ((e i).1 : ℤ) ∣ n - (a : ℤ) * t (e i).1 := by
  filter_upwards [eventual_primeDivisorPositive_phase_witness B Φ hB hΦ] with T hw
  intro Q hQ D P hP k e t tM h₀ X hX hL hK hRlo hRhi ht hW
  obtain ⟨U, V, hU, hV, s, hs, hsL, hwitness⟩ := hW
  obtain ⟨a, ha, b, hab⟩ := hw Q hQ D U V (primeTupleProduct P e) h₀ s
    ((tM : ℝ) / primeTupleProduct P e) ((primeTupleProduct P e : ℝ) / X) Q.card
    hU hV hs hsL hL (Nat.cast_nonneg _) hK hRlo hRhi hwitness
  let n := approximationLift a (primeTupleProduct P e) tM b
  have hM := primeTupleProduct_pos P hP e
  have hMR : (0 : ℝ) < primeTupleProduct P e := by exact_mod_cast hM
  refine ⟨a, ha, n, ?_, ?_⟩
  · apply (approximationLift_abs_bound a (primeTupleProduct P e) hM tM b _ hab).trans
    apply le_of_eq
    field_simp
  · intro i
    exact approximationLift_congruence a (primeTupleProduct P e) (e i).1 tM b (t (e i).1)
      (Finset.dvd_prod_of_mem (fun j : Fin k => (e j).1) (Finset.mem_univ i)) (ht i)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalTupleLifts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original Fourier witnesses give a positive family of integer tuple lifts -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap Classical

theorem int_mem_symmetric_Ico_of_abs_le (n : ℤ) (H : ℕ)
    (hn : |(n : ℝ)| ≤ H) : n ∈ Finset.Ico (-(H : ℤ)) (H + 1) := by
  have hh := abs_le.mp hn
  apply Finset.mem_Ico.mpr
  constructor
  · exact_mod_cast hh.1
  · have h : n ≤ (H : ℤ) := by exact_mod_cast hh.2
    omega

/-- Apply the inverse phase theorem to the literal small-kernel event. -/
theorem eventual_original_tuple_witness_lift_oai (B : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hB : 3 ≤ B) (hΦ : ∀ x : ℝ, B ^ 2 < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (P : Finset ℕ) (_hP : ∀ p ∈ P, p.Prime)
      (k N : ℕ) (t τ : ℕ → ℤ) (h₀ : ℕ → ℕ) (X : ℝ),
      0 < X → (Q.toList.prod : ℝ) ≤ Real.exp (T / 50) →
      (Q.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
      (∀ m ∈ primeSubsetProducts P k,
        Real.exp (10 * T) ≤ (m : ℝ) / X ∧ (m : ℝ) / X ≤ Real.exp (14 * T) ∧
        ∀ p ∈ m.primeFactors, (p : ℤ) ∣ τ m - t p) →
      ∀ e : Fin k ↪ P,
        principalSmallWitness Q hQ D (primeTupleProduct P e) N (h₀ (primeTupleProduct P e))
          ((τ (primeTupleProduct P e) : ℝ) / primeTupleProduct P e)
          ((primeTupleProduct P e : ℝ) / X) Φ →
        ∃ a ∈ Finset.Icc 1 ⌈Real.exp (13 * T / 100)⌉₊,
          ∃ n ∈ Finset.Ico (-(⌈X * Real.exp (13 * T / 100)⌉₊ : ℤ))
            (⌈X * Real.exp (13 * T / 100)⌉₊ + 1),
            ∀ i, ((e i).1 : ℤ) ∣ n - (a : ℤ) * t (e i).1 := by
  filter_upwards [eventual_quadratic_witness_lift B Φ hB hΦ] with T hw
  intro Q hQ D P hP k N t τ h₀ X hX hL hK hrange e he
  have heP := primeTupleProduct_mem P e
  obtain ⟨hRlo, hRhi, ht⟩ := hrange _ heP
  obtain ⟨s, hs, V, hV, U, hU, hval⟩ := he
  have hs' := smallSquarefreeKernels_spec Q.toList.prod N s hs
  obtain ⟨a, ha, n, hn, hd⟩ := hw Q hQ D P hP k e t (τ (primeTupleProduct P e))
    (h₀ (primeTupleProduct P e)) X hX hL hK hRlo hRhi
    (fun i => ht _ (primeTuple_member_primeFactors P hP e i))
    ⟨U, V, Finset.mem_powerset.mp hU, Finset.mem_powerset.mp hV,
      s, hs'.1, hs'.2.2.2.2, by simpa only [mul_comm] using hval⟩
  exact ⟨a, ha, n, int_mem_symmetric_Ico_of_abs_le n _ (hn.trans (Nat.le_ceil _)), hd⟩

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.eventual_original_tuple_witness_lift_oai := @OAI.Ostmann.eventual_original_tuple_witness_lift_oai
