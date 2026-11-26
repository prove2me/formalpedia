-- Prove2me | solution 1 for LinearDynamics.guarded_affine_binary_clock_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T18:59:28.647711+00:00
-- url     : https://prove2.me/submissions/99a12515-9666-413e-b877-82d7bf2490eb

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Fintype.Option
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option autoImplicit false

namespace PvsNP.AffineClockCertificate

open scoped BigOperators

/-- Big-endian interpretation of the remaining clock bits, given an accumulated prefix. -/
def clock : ℕ → List Bool → ℕ
  | acc, [] => acc
  | acc, b :: bs => clock (2 * acc + b.toNat) bs

/-- One binary-clock update of the verified matrix power. -/
def powerStep {M : Type*} [Monoid M] (base previous : M) (bit : Bool) : M :=
  previous * previous * (if bit then base else 1)

private theorem powerStep_pow {M : Type*} [Monoid M] (base : M) (acc : ℕ) (bit : Bool) :
    powerStep base (base ^ acc) bit = base ^ (2 * acc + bit.toNat) := by
  have oneBit : (if bit then base else 1) = base ^ bit.toNat := by
    cases bit <;> simp [Bool.toNat]
  rw [powerStep, oneBit, ← pow_add, ← pow_add, two_mul]

/-- Each clock bit consumes one supplied power row. The last supplied row
after those updates is reported separately as the verified answer. -/
def ValidLadder {M : Type*} [Monoid M] (base : M) :
    M → List Bool → List M → M → Prop
  | previous, [], rows, answer => rows = [] ∧ answer = previous
  | previous, b :: rest, rows, answer =>
    ∃ next tail, rows = next :: tail ∧ next = powerStep base previous b ∧
      ValidLadder base next rest tail answer

theorem validLadder_iff {M : Type*} [Monoid M] (base : M) (acc : ℕ)
    (bits : List Bool) (rows : List M) (answer : M)
    (valid : ValidLadder base (base ^ acc) bits rows answer) :
    rows.length = bits.length ∧ answer = base ^ clock acc bits := by
  induction bits generalizing acc rows with
  | nil => simp_all [ValidLadder, clock]
  | cons b rest ih =>
    obtain ⟨next, tail, row, value, later⟩ := valid
    rw [value, powerStep_pow] at later
    have claims := ih (2 * acc + b.toNat) tail later
    simp [row, claims.1, claims.2, clock]

theorem exists_validLadder {M : Type*} [Monoid M] (base : M)
    (acc : ℕ) (bits : List Bool) :
    ∃ rows, ValidLadder base (base ^ acc) bits rows (base ^ clock acc bits) := by
  induction bits generalizing acc with
  | nil => exact ⟨[], by simp [ValidLadder, clock]⟩
  | cons b rest ih =>
    let acc' := 2 * acc + b.toNat
    obtain ⟨rows, good⟩ := ih acc'
    exact ⟨base ^ acc' :: rows, base ^ acc', rows, rfl,
      (powerStep_pow base acc b).symm, good⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The extra coordinate stores the constant 1 used by affine translations. -/
def lift (x : ι → ZMod 2) : Option ι → ZMod 2
  | none => 1
  | some i => x i

/-- Matrix whose action on the lifted vector is the given affine step. -/
def liftMatrix (A : Matrix ι ι (ZMod 2)) (c : ι → ZMod 2) :
    Matrix (Option ι) (Option ι) (ZMod 2)
  | none, none => 1
  | none, some _ => 0
  | some i, none => c i
  | some i, some j => A i j

def affine (A : Matrix ι ι (ZMod 2)) (c x : ι → ZMod 2) : ι → ZMod 2 :=
  A.mulVec x + c

omit [DecidableEq ι] in
private theorem lift_step (A : Matrix ι ι (ZMod 2)) (c x : ι → ZMod 2) :
    (liftMatrix A c).mulVec (lift x) = lift (affine A c x) := by
  funext i
  cases i <;> simp [Matrix.mulVec, dotProduct, Fintype.sum_option, liftMatrix, lift,
    affine, add_comm]

theorem lift_iterate (A : Matrix ι ι (ZMod 2)) (c x : ι → ZMod 2) (t : ℕ) :
    ((liftMatrix A c) ^ t).mulVec (lift x) = lift ((affine A c)^[t] x) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Function.iterate_succ_apply', lift_step]

/-- A checked binary-clock ladder certifies one designated result bit of a
translated linear transition, including for clocks much longer than the ladder. -/
theorem ladder_certifies_bit (A : Matrix ι ι (ZMod 2)) (c x : ι → ZMod 2)
    (bits : List Bool) (rows : List (Matrix (Option ι) (Option ι) (ZMod 2)))
    (answer : Matrix (Option ι) (Option ι) (ZMod 2)) (out : ι)
    (valid : ValidLadder (liftMatrix A c) 1 bits rows answer) :
    rows.length = bits.length ∧
      answer.mulVec (lift x) (some out) = ((affine A c)^[clock 0 bits] x) out := by
  have initial : ValidLadder (liftMatrix A c) ((liftMatrix A c) ^ (0 : ℕ)) bits rows answer := by
    simpa using valid
  obtain ⟨length, value⟩ := validLadder_iff _ _ _ _ _ initial
  exact ⟨length, by rw [value, lift_iterate]; rfl⟩

end PvsNP.AffineClockCertificate

namespace PvsNP.GuardedAffineBlock

open scoped BigOperators
open Polynomial

section Linear

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A linear observation on an orbit vanishes everywhere once it vanishes
on the first `finrank K V` states. -/
theorem orbit_probe_zero_of_prefix (step : Module.End K V) (probe : V →ₗ[K] K)
    (start : V) (zeros : ∀ i < Module.finrank K V, probe ((step ^ i) start) = 0) :
    ∀ i : ℕ, probe ((step ^ i) start) = 0 := by
  let d := Module.finrank K V
  let p := step.charpoly
  have deg : p.natDegree = d := step.charpoly_natDegree
  have top : p.coeff d = 1 := deg ▸ step.charpoly_monic.coeff_natDegree
  have expanded : (∑ i ∈ Finset.range (d + 1), p.coeff i • step ^ i) = 0 := by
    have relation := step.aeval_self_charpoly
    change aeval step p = 0 at relation
    nth_rw 1 [p.as_sum_range] at relation
    simpa only [map_sum, aeval_monomial, deg, Algebra.smul_def] using relation
  have recurrence (offset : ℕ) :
      (∑ i ∈ Finset.range (d + 1), p.coeff i * probe ((step ^ (i + offset)) start)) = 0 := by
    have applied := congrArg (fun e : Module.End K V => probe (e ((step ^ offset) start)))
      expanded
    simpa only [LinearMap.sum_apply, LinearMap.zero_apply, map_sum, map_zero,
      LinearMap.smul_apply, map_smul, smul_eq_mul, pow_add, Module.End.mul_apply]
      using applied
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases small : t < d
    · exact zeros t small
    have bound : d ≤ t := Nat.le_of_not_gt small
    have ends : d + (t - d) = t := Nat.add_sub_of_le bound
    have triangular := recurrence (t - d)
    rw [Finset.sum_range_succ] at triangular
    have earlier :
        (∑ i ∈ Finset.range d, p.coeff i * probe ((step ^ (i + (t - d))) start)) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have prior : i + (t - d) < t := by
        have := Finset.mem_range.mp hi
        omega
      rw [ih _ prior, mul_zero]
    simpa only [earlier, zero_add, top, one_mul, ends] using triangular

end Linear

section Affine

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

def affineStep (A : Module.End K V) (b : V) (x : V) : V := A x + b

/-- Affine update on the first component, using the second as the constant
coordinate. -/
def liftUpdate (A : Module.End K V) (b : V) : Module.End K (V × K) where
  toFun x := (A x.1 + x.2 • b, x.2)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, add_smul, Prod.mk_add_mk]
    congr 1
    abel
  map_smul' k x := by
    simp [smul_add, mul_smul]

/-- The observation is zero exactly when the affine guard takes its expected
value, provided the second component is one. -/
def liftGuard (guard : V →ₗ[K] K) (bias expected : K) : (V × K) →ₗ[K] K where
  toFun x := guard x.1 + (bias - expected) * x.2
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, mul_add]
    abel
  map_smul' k x := by
    change guard (k • x.1) + (bias - expected) * (k * x.2) =
      k * (guard x.1 + (bias - expected) * x.2)
    rw [map_smul]
    change k * guard x.1 + (bias - expected) * (k * x.2) =
      k * (guard x.1 + (bias - expected) * x.2)
    ring

omit [FiniteDimensional K V] in
theorem liftUpdate_pow (A : Module.End K V) (b : V) (start : V) (t : ℕ) :
    ((liftUpdate A b) ^ t) (start, 1) = ((affineStep A b)^[t] start, 1) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [pow_succ', Module.End.mul_apply, ih, Function.iterate_succ_apply']
    change (A ((affineStep A b)^[t] start) + (1 : K) • b, 1) =
      (A ((affineStep A b)^[t] start) + b, 1)
    rw [one_smul]

omit [FiniteDimensional K V] in
private theorem liftGuard_eq_zero (guard : V →ₗ[K] K) (bias expected : K) (x : V) :
    liftGuard guard bias expected (x, 1) = 0 ↔ guard x + bias = expected := by
  change guard x + (bias - expected) * 1 = 0 ↔ _
  rw [mul_one, ← add_sub_assoc, sub_eq_zero]

theorem affine_guard_constant_of_prefix (A : Module.End K V) (b start : V)
    (guard : V →ₗ[K] K) (bias expected : K)
    (prefixOK : ∀ i < Module.finrank K V + 1,
      guard ((affineStep A b)^[i] start) + bias = expected) :
    ∀ i : ℕ, guard ((affineStep A b)^[i] start) + bias = expected := by
  have zeros : ∀ i < Module.finrank K (V × K),
      liftGuard guard bias expected (((liftUpdate A b) ^ i) (start, 1)) = 0 := by
    intro i before
    rw [Module.finrank_prod, Module.finrank_self] at before
    rw [liftUpdate_pow]
    exact (liftGuard_eq_zero _ _ _ _).mpr (prefixOK i before)
  intro i
  have zero := orbit_probe_zero_of_prefix (liftUpdate A b) (liftGuard guard bias expected)
    (start, 1) zeros i
  rw [liftUpdate_pow] at zero
  exact (liftGuard_eq_zero _ _ _ _).mp zero

/-- An alternate update may be arbitrary. A prefix check of size
`min duration (finrank K V + 1)` guarantees it is never taken in the block. -/
theorem guarded_block_eq_of_prefix [DecidableEq K] (A : Module.End K V) (b start : V)
    (guard : V →ₗ[K] K) (bias expected : K) (fallback : V → V) (duration : ℕ)
    (prefixOK : ∀ i < min duration (Module.finrank K V + 1),
      guard ((affineStep A b)^[i] start) + bias = expected) :
    let update := fun x => if guard x + bias = expected then affineStep A b x else fallback x
    ∀ t ≤ duration, update^[t] start = (affineStep A b)^[t] start := by
  have good : ∀ i < duration, guard ((affineStep A b)^[i] start) + bias = expected := by
    by_cases short : duration ≤ Module.finrank K V + 1
    · simpa only [min_eq_left short] using prefixOK
    · have long : Module.finrank K V + 1 ≤ duration := Nat.le_of_not_ge short
      have permanent := affine_guard_constant_of_prefix A b start guard bias expected
        (by simpa only [min_eq_right long] using prefixOK)
      exact fun i _ => permanent i
  dsimp only
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro before
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih (Nat.le_of_succ_le before), if_pos (good t before)]

end Affine

end PvsNP.GuardedAffineBlock

namespace PvsNP.GuardedAffineLadder

open PvsNP.AffineClockCertificate PvsNP.GuardedAffineBlock

abbrev State (ι : Type*) := ι → ZMod 2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An explicit branch of the transition program. The implication comes
from the program semantics for the listed guard, independently of each jump. -/
structure Branch (step : State ι → State ι) where
  matrix : Matrix ι ι (ZMod 2)
  translation : State ι
  guard : State ι →ₗ[ZMod 2] ZMod 2
  bias : ZMod 2
  expected : ZMod 2
  onMatch : ∀ x, guard x + bias = expected → step x = affine matrix translation x

structure Ladder (ι : Type*) where
  bits : List Bool
  rows : List (Matrix (Option ι) (Option ι) (ZMod 2))
  answer : Matrix (Option ι) (Option ι) (ZMod 2)

structure Checks {step : State ι → State ι} (branch : Branch step) (ladder : Ladder ι)
    (start finish : State ι) : Prop where
  initialGuards : ∀ i < min (clock 0 ladder.bits) (Fintype.card ι + 1),
    branch.guard ((affine branch.matrix branch.translation)^[i] start) + branch.bias =
      branch.expected
  power : ValidLadder (liftMatrix branch.matrix branch.translation) 1
    ladder.bits ladder.rows ladder.answer
  final : ∀ i, finish i = ladder.answer.mulVec (lift start) (some i)

/-- Checks for a single binary-clock block prove that the chosen guard
stays true and the recorded endpoint is the state of the actual program. -/
theorem Checks.exact {step : State ι → State ι} {branch : Branch step}
    {ladder : Ladder ι} {start finish : State ι} (checks : Checks branch ladder start finish) :
    ladder.rows.length = ladder.bits.length ∧
      finish = step^[clock 0 ladder.bits] start := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A : Module.End (ZMod 2) (State ι) := branch.matrix.mulVecLin
  have aff : affineStep A branch.translation = affine branch.matrix branch.translation := by
    funext x
    simp only [affineStep, A, Matrix.mulVecLin_apply, affine]
  have scope : ∀ i < min (clock 0 ladder.bits) (Module.finrank (ZMod 2) (State ι) + 1),
      branch.guard ((affineStep A branch.translation)^[i] start) + branch.bias =
        branch.expected := by
    simpa only [aff, Module.finrank_fintype_fun_eq_card] using checks.initialGuards
  have compressed := guarded_block_eq_of_prefix A branch.translation start branch.guard
    branch.bias branch.expected step (clock 0 ladder.bits) scope
  dsimp only at compressed
  rw [aff] at compressed
  have stepEq : (fun x => if branch.guard x + branch.bias = branch.expected then
      affine branch.matrix branch.translation x else step x) = step := by
    funext x
    split_ifs with good
    · exact (branch.onMatch x good).symm
    · rfl
  rw [stepEq] at compressed
  have initial : ValidLadder (liftMatrix branch.matrix branch.translation)
      ((liftMatrix branch.matrix branch.translation) ^ (0 : ℕ))
      ladder.bits ladder.rows ladder.answer := by
    simpa using checks.power
  obtain ⟨rowCount, finalPower⟩ := validLadder_iff _ _ _ _ _ initial
  refine ⟨rowCount, ?_⟩
  funext i
  rw [checks.final, finalPower, lift_iterate, compressed _ le_rfl]
  rfl

/-- The check for each branch uses the endpoint established by the prior
block. Zero-duration blocks are permitted and leave the state unchanged. -/
inductive Sequence (step : State ι → State ι) :
    State ι → List (Ladder ι) → State ι → Prop
  | empty (state : State ι) : Sequence step state [] state
  | block {branch : Branch step} {ladder : Ladder ι} {start middle finish : State ι}
      {later : List (Ladder ι)} (head : Checks branch ladder start middle)
      (tail : Sequence step middle later finish) : Sequence step start (ladder :: later) finish

theorem Sequence.exact {step : State ι → State ι} {start finish : State ι}
    {ladders : List (Ladder ι)} (path : Sequence step start ladders finish) :
    (∀ ladder ∈ ladders, ladder.rows.length = ladder.bits.length) ∧
      finish = step^[((ladders.map fun ladder => clock 0 ladder.bits).sum)] start := by
  induction path with
  | empty => simp
  | @block branch ladder start middle finish later head tail ih =>
    obtain ⟨rows, jump⟩ := head.exact
    obtain ⟨restRows, laterJumps⟩ := ih
    refine ⟨?_, ?_⟩
    · intro inspect member
      rcases List.mem_cons.mp member with same | rest
      · exact same ▸ rows
      · exact restRows inspect rest
    · simpa only [List.map_cons, List.sum_cons, Nat.add_comm (clock 0 ladder.bits),
        Function.iterate_add_apply, ← jump] using laterJumps

theorem clock_eq_foldl (initial : ℕ) (bits : List Bool) :
    clock initial bits = bits.foldl (fun current bit => 2 * current + bit.toNat) initial := by
  induction bits generalizing initial with
  | nil => rfl
  | cons bit rest ih => exact ih _

theorem scanned_ladder {M : Type*} [Monoid M] (base previous : M) (bits : List Bool) :
    ValidLadder base previous bits ((bits.scanl (powerStep base) previous).tail)
      (bits.foldl (powerStep base) previous) := by
  induction bits generalizing previous with
  | nil => simp [ValidLadder]
  | cons bit rest ih =>
    let next := powerStep base previous bit
    let nextRows := (rest.scanl (powerStep base) next).tail
    have head : rest.scanl (powerStep base) next = next :: nextRows := by
      cases rest <;> simp [nextRows]
    rw [List.scanl_cons, List.tail_cons, List.foldl_cons]
    exact ⟨next, nextRows, head, rfl, ih next⟩

end PvsNP.GuardedAffineLadder
open PvsNP.AffineClockCertificate PvsNP.GuardedAffineLadder

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι]
    (mat : Matrix ι ι (ZMod 2)) (translation start : ι → ZMod 2)
    (step : (ι → ZMod 2) → (ι → ZMod 2))
    (guard : (ι → ZMod 2) →ₗ[ZMod 2] ZMod 2) (bias expected : ZMod 2)
    (onBranch : ∀ x, guard x + bias = expected → step x = mat.mulVec x + translation)
    (bits : List Bool) (powers : List (Matrix (Option ι) (Option ι) (ZMod 2))) :
    let base : Matrix (Option ι) (Option ι) (ZMod 2) := fun i j =>
      match i, j with
      | none, none => 1
      | none, some _ => 0
      | some i, none => translation i
      | some i, some j => mat i j
    let liftedStart : Option ι → ZMod 2 := fun i =>
      match i with
      | none => 1
      | some i => start i
    let time := bits.foldl (fun current bit => 2 * current + bit.toNat) 0
    (∀ i < min time (Fintype.card ι + 1),
      guard ((fun x => mat.mulVec x + translation)^[i] start) + bias = expected) →
    powers = bits.scanl (fun previous bit => previous * previous * (if bit then base else 1)) 1 →
    powers.length = bits.length + 1 ∧
    ∀ i, (powers.getLast?.getD 1).mulVec liftedStart (some i) = (step^[time] start) i := by
  dsimp only
  intro guards checkedPowers
  let base := liftMatrix mat translation
  let answer := bits.foldl (powerStep base) 1
  let finish : State ι := fun i => answer.mulVec (lift start) (some i)
  let branch : Branch step := ⟨mat, translation, guard, bias, expected, onBranch⟩
  let claim : Ladder ι := ⟨bits, (bits.scanl (powerStep base) 1).tail, answer⟩
  change powers = bits.scanl (powerStep base) 1 at checkedPowers
  have valid : Checks branch claim start finish := by
    constructor
    · change ∀ i < min (clock 0 bits) (Fintype.card ι + 1),
        guard ((affine mat translation)^[i] start) + bias = expected
      rw [clock_eq_foldl]
      exact guards
    · exact scanned_ladder base 1 bits
    · intro i
      rfl
  rw [checkedPowers, List.length_scanl]
  refine ⟨rfl, fun i => ?_⟩
  rw [List.getLast?_scanl, Option.getD_some, ← clock_eq_foldl]
  exact congrFun valid.exact.2 i

#print axioms solution
