-- Prove2me | solution 1 for OAI.Erdos3.exists_scalarEndpoint_late_prime_common_side
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T03:27:54.359531+00:00
-- url     : https://prove2.me/submissions/beafb762-f0ae-4105-8dfe-c816d0c6b811

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1328

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonSideExponentialAbsorption
namespace OAI

section

namespace Erdos3

theorem commonSide_exp_absorption (n E : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ((n : ℝ) + 1) * Real.exp ((t + 2) ^ E) ≤
      Real.exp ((t + 2) ^ (E + n + 3)) := by
  have hbase : (1 : ℝ) ≤ t + 2 := by linarith
  have hpower : (1 : ℝ) ≤ (t + 2) ^ E := one_le_pow₀ hbase
  have hlinear : (n : ℝ) + 2 ≤ (t + 2) ^ (n + 1) := by
    calc
      (n : ℝ) + 2 ≤ (2 : ℝ) ^ (n + 1) := by
        have h := one_add_mul_le_pow (by norm_num : (-2 : ℝ) ≤ 1) (n + 1)
        norm_num only [Nat.cast_add, Nat.cast_one, mul_one, one_add_one_eq_two] at h
        linarith
      _ ≤ (t + 2) ^ (n + 1) := pow_le_pow_left₀ (by norm_num) (by linarith) _
  have hexponent : (n : ℝ) + (t + 2) ^ E ≤ (t + 2) ^ (E + n + 3) := by
    calc
      (n : ℝ) + (t + 2) ^ E ≤ ((n : ℝ) + 2) * (t + 2) ^ E := by
        nlinarith [mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hpower)]
      _ ≤ (t + 2) ^ (n + 1) * (t + 2) ^ E :=
        mul_le_mul_of_nonneg_right hlinear (by positivity)
      _ = (t + 2) ^ (E + n + 1) := by rw [← pow_add]; congr 1; omega
      _ ≤ (t + 2) ^ (E + n + 3) := pow_le_pow_right₀ hbase (by omega)
  calc
    ((n : ℝ) + 1) * Real.exp ((t + 2) ^ E) ≤
        Real.exp (n : ℝ) * Real.exp ((t + 2) ^ E) :=
      mul_le_mul_of_nonneg_right (Real.add_one_le_exp (n : ℝ)) (Real.exp_nonneg _)
    _ = Real.exp ((n : ℝ) + (t + 2) ^ E) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((t + 2) ^ (E + n + 3)) := Real.exp_le_exp.mpr hexponent

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScalarLatePrimeCutoffPowerBudget
namespace OAI

section

namespace Erdos3

theorem exists_scalarLatePrimeCutoff_power_budget (d r E C F A : ℕ) :
    ∃ G : ℕ, 2 ≤ G ∧ ∀ b : ℝ, 0 ≤ b →
      let p := (b + 2) ^ E
      let target := 8 * ((r * d : ℕ) + 1 : ℝ) * (p + 1)
      let t := (target + 2) ^ C
      (p + F) ^ F ≤ (b + 2) ^ G ∧ (t + 2) ^ A ≤ (b + 2) ^ G := by
  let Pscalar : Polynomial ℕ := ((Polynomial.X + 2) ^ E + Polynomial.C F) ^ F
  let Psample : Polynomial ℕ :=
    ((Polynomial.C (8 * (r * d + 1)) * ((Polynomial.X + 2) ^ E + 1) + 2) ^ C + 2) ^ A
  obtain ⟨G, hG, hbound⟩ := exists_natPolynomial_fixed_power_budget (Pscalar + Psample)
  refine ⟨G, hG, ?_⟩
  intro b hb p target t
  have hsum : (p + F) ^ F + (t + 2) ^ A ≤ (b + 2) ^ G := by
    simpa [Pscalar, Psample, p, target, t, Polynomial.eval₂_pow] using hbound b hb
  have hscalar : 0 ≤ (p + F) ^ F := by dsimp only [p]; positivity
  have hsample : 0 ≤ (t + 2) ^ A := by dsimp only [t, target, p]; positivity
  exact ⟨(le_add_of_nonneg_right hsample).trans hsum,
    (le_add_of_nonneg_left hscalar).trans hsum⟩

theorem exists_scalarLatePrimeCutoff_composite_power_budget (d r E C F A H : ℕ) :
    ∃ G : ℕ, 2 ≤ G ∧ ∀ p : ℝ, 2 ≤ p →
      let b := (p + 2) ^ H
      let scalarInput := (b + 2) ^ E
      let target := 8 * ((r * d : ℕ) + 1 : ℝ) * (scalarInput + 1)
      let t := (target + 2) ^ C
      (scalarInput + F) ^ F ≤ (p + 2) ^ G ∧ (t + 2) ^ A ≤ (p + 2) ^ G := by
  obtain ⟨G, hG, hbudget⟩ := exists_scalarLatePrimeCutoff_power_budget d r E C F A
  refine ⟨(H + 1) * G, by nlinarith, ?_⟩
  intro p hp b scalarInput target t
  have hbase : 1 ≤ p + 2 := by linarith
  have hb : 1 ≤ b := one_le_pow₀ hbase
  have hshift : b + 2 ≤ (p + 2) ^ (H + 1) := by
    rw [pow_succ']
    change b + 2 ≤ (p + 2) * b
    nlinarith
  have hcompose : (b + 2) ^ G ≤ (p + 2) ^ ((H + 1) * G) := by
    calc
      _ ≤ ((p + 2) ^ (H + 1)) ^ G := pow_le_pow_left₀ (by linarith) hshift G
      _ = _ := (pow_mul _ _ _).symm
  have h := hbudget b (by linarith)
  exact ⟨h.1.trans hcompose, h.2.trans hcompose⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.UnconditionedWidthExponentialBudget
namespace OAI

section

namespace Erdos3
open scoped BigOperators

theorem widthBudget_le_exp (x : ℝ) : x ≤ Real.exp x :=
  (by linarith : x ≤ x + 1).trans (Real.add_one_le_exp x)

theorem widthBudget_residue_bounds {n : ℕ} (P : Fin n → ℕ)
    [∀ i, NeZero (P i)] {t : ℝ} (ht : 0 ≤ t)
    (hP : ∀ i, (P i : ℝ) ≤ Real.exp t) :
    1 + unconditionedResidueSiteBound P ≤ Real.exp ((n : ℝ) + 1 + t) ∧
    (Fintype.card (∀ i, ZMod (P i)) : ℝ) ≤ Real.exp ((n : ℝ) * t) := by
  have hsum : unconditionedResidueSiteBound P ≤ (n : ℝ) * Real.exp t := by
    calc
      _ ≤ ∑ _i : Fin n, Real.exp t := Finset.sum_le_sum (fun i _ => hP i)
      _ = _ := by simp
  have hone : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr ht
  constructor
  · calc
      1 + unconditionedResidueSiteBound P ≤ ((n : ℝ) + 1) * Real.exp t := by nlinarith
      _ ≤ Real.exp ((n : ℝ) + 1) * Real.exp t :=
        mul_le_mul_of_nonneg_right (widthBudget_le_exp _) (Real.exp_pos _).le
      _ = _ := (Real.exp_add _ _).symm
  · calc
      (Fintype.card (∀ i, ZMod (P i)) : ℝ) = ∏ i, (P i : ℝ) := by
        simp [Fintype.card_pi]
      _ ≤ ∏ _i : Fin n, Real.exp t :=
        Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => hP i)
      _ = Real.exp ((n : ℝ) * t) := by simp [Real.exp_nat_mul]

theorem unconditionedSpatialTrimFraction_inv_exp_bound {p : ℝ} {d : ℕ}
    (hd : (d : ℝ) ≤ p) :
    (unconditionedSpatialTrimFraction d (Real.exp (-p)))⁻¹ ≤ Real.exp (2 * p + 33) := by
  have h32 : (32 : ℝ) ≤ Real.exp 32 := widthBudget_le_exp _
  have hdexp : (d : ℝ) + 1 ≤ Real.exp (p + 1) :=
    (by linarith : (d : ℝ) + 1 ≤ p + 1).trans (widthBudget_le_exp _)
  calc
    (unconditionedSpatialTrimFraction d (Real.exp (-p)))⁻¹ =
        32 * ((d : ℝ) + 1) * Real.exp p := by
      simp [unconditionedSpatialTrimFraction, Real.exp_neg]
    _ ≤ Real.exp 32 * Real.exp (p + 1) * Real.exp p := by gcongr
    _ = Real.exp (2 * p + 33) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem widthBudget_collision {n : ℕ} (P : Fin n → ℕ)
    [∀ i, NeZero (P i)] {t p : ℝ}
    (hcard : (Fintype.card (∀ i, ZMod (P i)) : ℝ) ≤ Real.exp ((n : ℝ) * t)) :
    unconditionedCollisionWidth P (Real.exp (-p)) ≤
      Real.exp (32 + 2 * (n : ℝ) * t + p) := by
  calc
    _ = 32 * (Fintype.card (∀ i, ZMod (P i)) : ℝ)^2 * Real.exp p := by
      simp [unconditionedCollisionWidth, div_eq_mul_inv, Real.exp_neg]
    _ ≤ Real.exp 32 * (Real.exp ((n : ℝ) * t))^2 * Real.exp p := by
      gcongr
      exact widthBudget_le_exp _
    _ = Real.exp (32 + 2 * (n : ℝ) * t + p) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      push_cast
      ring

theorem widthBudget_cutoff {n : ℕ} (c : ℕ)
    (hc : 8 * (probabilityProfileLipschitz : ℝ) ≤ c)
    {p : ℝ} (hp : 0 ≤ p) (d : ℕ) (hd : (d : ℝ) ≤ p)
    (P : Fin n → ℕ) [∀ i, NeZero (P i)]
    (hP : ∀ i, (P i : ℝ) ≤ Real.exp (p + n + 2)) :
    unconditionedSpatialWidthCutoff (unconditionedResidueSiteBound P)
      (unconditionedSpatialTrimFraction d (Real.exp (-p)))
      (unconditionedCollisionWidth P (Real.exp (-p))) ≤
      Real.exp ((c : ℝ) + 80 + n + (p + n + 2) + 2 * n * (p + n + 2) + 4 * p) := by
  let t : ℝ := p + n + 2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hcn : 0 ≤ (c : ℝ) := Nat.cast_nonneg _
  obtain ⟨hsite, hcard⟩ := widthBudget_residue_bounds P ht hP
  have hinv := unconditionedSpatialTrimFraction_inv_exp_bound hd
  have hcollision := widthBudget_collision P (p := p) hcard
  have hmax : max (8 * (probabilityProfileLipschitz : ℝ))
      (unconditionedCollisionWidth P (Real.exp (-p))) ≤
      Real.exp ((c : ℝ) + 32 + 2 * n * t + p) := by
    apply max_le
    · exact (hc.trans (widthBudget_le_exp _)).trans (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hn ht]))
    · exact hcollision.trans (Real.exp_le_exp.mpr (by linarith))
  have hsite0 : 0 ≤ 1 + unconditionedResidueSiteBound P := by
    have : 0 ≤ unconditionedResidueSiteBound P :=
      Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    linarith
  have hmax0 : 0 ≤ max (8 * (probabilityProfileLipschitz : ℝ))
      (unconditionedCollisionWidth P (Real.exp (-p))) :=
    (by positivity : (0 : ℝ) ≤ 8 * (probabilityProfileLipschitz : ℝ)).trans (le_max_left _ _)
  have hinv0 : 0 ≤ (unconditionedSpatialTrimFraction d (Real.exp (-p)))⁻¹ := by
    unfold unconditionedSpatialTrimFraction
    positivity
  unfold unconditionedSpatialWidthCutoff
  apply max_le
  · calc
      _ = 4 * (unconditionedSpatialTrimFraction d (Real.exp (-p)))⁻¹ := div_eq_mul_inv _ _
      _ ≤ Real.exp 4 * Real.exp (2 * p + 33) :=
        mul_le_mul (widthBudget_le_exp _) hinv hinv0 (Real.exp_pos _).le
      _ = Real.exp (4 + (2 * p + 33)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp only [t] at *; nlinarith [mul_nonneg hn ht])
  · calc
      _ = 8 * (1 + unconditionedResidueSiteBound P) *
          max (8 * (probabilityProfileLipschitz : ℝ))
            (unconditionedCollisionWidth P (Real.exp (-p))) *
          (unconditionedSpatialTrimFraction d (Real.exp (-p)))⁻¹ := div_eq_mul_inv _ _
      _ ≤ Real.exp 8 * Real.exp ((n : ℝ) + 1 + t) *
          Real.exp ((c : ℝ) + 32 + 2 * n * t + p) * Real.exp (2 * p + 33) := by
        apply mul_le_mul _ hinv hinv0 (by positivity)
        apply mul_le_mul _ hmax hmax0 (by positivity)
        exact mul_le_mul (widthBudget_le_exp _) hsite hsite0 (Real.exp_pos _).le
      _ = Real.exp (8 + ((n : ℝ) + 1 + t) +
          ((c : ℝ) + 32 + 2 * n * t + p) + (2 * p + 33)) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp only [t]; linarith)

theorem exists_unconditionedSpatialWidthCutoff_exp_budget (n₀ : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ (p : ℝ), 2 ≤ p → ∀ (d : ℕ), (d : ℝ) ≤ p →
    ∀ (P : Fin n₀ → ℕ) [∀ i, NeZero (P i)],
    (∀ i, (P i : ℝ) ≤ Real.exp (p + n₀ + 2)) →
    unconditionedSpatialWidthCutoff (unconditionedResidueSiteBound P)
      (unconditionedSpatialTrimFraction d (Real.exp (-p)))
      (unconditionedCollisionWidth P (Real.exp (-p))) ≤ Real.exp ((p + 2)^E) := by
  obtain ⟨c, hc⟩ := exists_nat_ge (8 * (probabilityProfileLipschitz : ℝ))
  let T : Polynomial ℕ := Polynomial.X + Polynomial.C n₀ + 2
  let Q : Polynomial ℕ := Polynomial.C c + 80 + Polynomial.C n₀ + T +
    2 * Polynomial.C n₀ * T + 4 * Polynomial.X
  obtain ⟨E, hE, hbudget⟩ := exists_natPolynomial_fixed_power_budget Q
  refine ⟨E, hE, ?_⟩
  intro p hp d hd P hne hP
  have hp0 : 0 ≤ p := by linarith
  apply (widthBudget_cutoff c hc hp0 d hd P hP).trans
  apply Real.exp_le_exp.mpr
  simpa [Q, T] using hbudget p hp0

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ComparableScalarPrimeParameters
namespace OAI

section

namespace Erdos3
open scoped Classical

theorem exists_distinct_primes_dyadic (n t : ℕ) (ht : 0 < t) :
    ∃ N : Fin n → ℕ, StrictMono N ∧
      ∀ i, (N i).Prime ∧ 2 ^ i.val * t < N i ∧ N i ≤ 2 ^ (i.val + 1) * t := by
  have hp (i : Fin n) : ∃ p : ℕ, p.Prime ∧
      2 ^ i.val * t < p ∧ p ≤ 2 ^ (i.val + 1) * t := by
    obtain ⟨p, hprime, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul
      (2 ^ i.val * t) (by positivity)
    refine ⟨p, hprime, hlo, ?_⟩
    simpa only [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hhi
  choose N hN using hp
  refine ⟨N, ?_, hN⟩
  intro i j hij
  have he : i.val + 1 ≤ j.val := by exact hij
  exact ((hN i).2.2.trans (Nat.mul_le_mul_right t
    (Nat.pow_le_pow_right (by norm_num : 0 < 2) he))).trans_lt (hN j).2.1

end Erdos3

end

section

namespace Erdos3
open scoped Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.UnconditionedLatePrimeBudget
namespace OAI

section

namespace Erdos3

theorem exists_unconditioned_prime_sides (n₀ : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    ∃ P : Fin n₀ → ℕ, (∀ i, (P i).Prime) ∧ Function.Injective P ∧
      (∀ i j, P i ≤ 2 ^ (n₀ + 1) * P j) ∧
      ∀ i, Real.exp p ≤ (P i : ℝ) ∧ (P i : ℝ) ≤ Real.exp (p + (n₀ : ℝ) + 2) := by
  let t := ⌈Real.exp p⌉₊
  have hceil : Real.exp p ≤ (t : ℝ) := Nat.le_ceil _
  have ht : 0 < t := by exact_mod_cast (Real.exp_pos p).trans_le hceil
  have he1 : (1 : ℝ) ≤ Real.exp p := Real.one_le_exp_iff.mpr hp
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have htR : (t : ℝ) ≤ Real.exp (p + 1) := by
    calc
      _ ≤ Real.exp p + 1 := (Nat.ceil_lt_add_one (Real.exp_nonneg p)).le
      _ ≤ Real.exp p * 2 := by linarith
      _ ≤ Real.exp p * Real.exp 1 := mul_le_mul_of_nonneg_left htwo (Real.exp_nonneg p)
      _ = Real.exp (p + 1) := (Real.exp_add p 1).symm
  have hpow : (2 : ℝ) ^ n₀ ≤ Real.exp (n₀ : ℝ) := by
    calc
      _ ≤ (Real.exp 1) ^ n₀ := pow_le_pow_left₀ (by norm_num) htwo n₀
      _ = _ := by rw [← Real.exp_nat_mul, mul_one]
  obtain ⟨P, hmono, hP⟩ := exists_distinct_primes_dyadic n₀ t ht
  have hlow (i : Fin n₀) : t < P i :=
    (Nat.le_mul_of_pos_left t (by positivity : 0 < 2 ^ i.val)).trans_lt (hP i).2.1
  have hhigh (i : Fin n₀) : P i ≤ 2 ^ n₀ * t :=
    (hP i).2.2.trans (Nat.mul_le_mul_right t
      (Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.succ_le_of_lt i.isLt)))
  refine ⟨P, fun i => (hP i).1, hmono.injective, ?_, ?_⟩
  · intro i j
    exact (hhigh i).trans (Nat.mul_le_mul
      (Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.le_succ n₀)) (hlow j).le)
  · intro i
    refine ⟨hceil.trans (Nat.cast_le.mpr (hlow i).le), ?_⟩
    calc
      (P i : ℝ) ≤ (2 : ℝ) ^ n₀ * (t : ℝ) := by exact_mod_cast hhigh i
      _ ≤ Real.exp (n₀ : ℝ) * Real.exp (p + 1) :=
        mul_le_mul hpow htR (Nat.cast_nonneg t) (Real.exp_nonneg _)
      _ = Real.exp ((n₀ : ℝ) + (p + 1)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (p + (n₀ : ℝ) + 2) := Real.exp_le_exp.mpr (by linarith)

theorem exists_unconditioned_prime_side_budget (n₀ : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ p : ℝ, 2 ≤ p →
      ∃ (P : Fin n₀ → ℕ) (hprime : ∀ i, (P i).Prime),
        Function.Injective P ∧ (∀ i j, P i ≤ 2 ^ (n₀ + 1) * P j) ∧
        (∀ i, Real.exp p ≤ (P i : ℝ) ∧ (P i : ℝ) ≤ Real.exp (p + (n₀ : ℝ) + 2)) ∧
        ∀ d : ℕ, (d : ℝ) ≤ p →
          let : ∀ i, NeZero (P i) := fun i => ⟨(hprime i).ne_zero⟩
          unconditionedSpatialWidthCutoff (unconditionedResidueSiteBound P)
            (unconditionedSpatialTrimFraction d (Real.exp (-p)))
            (unconditionedCollisionWidth P (Real.exp (-p))) ≤ Real.exp ((p + 2) ^ E) := by
  obtain ⟨E, hE, hbudget⟩ := exists_unconditionedSpatialWidthCutoff_exp_budget n₀
  refine ⟨E, hE, ?_⟩
  intro p hp
  obtain ⟨P, hprime, hinj, hcompare, hrange⟩ :=
    exists_unconditioned_prime_sides n₀ (by linarith : 0 ≤ p)
  refine ⟨P, hprime, hinj, hcompare, hrange, ?_⟩
  intro d hd
  let : ∀ i, NeZero (P i) := fun i => ⟨(hprime i).ne_zero⟩
  exact hbudget p hp d hd P (fun i => (hrange i).2)

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem unconditionedSpatialWidthCutoff_antitone_surplus
    {K : Type*} [Fintype K] [DecidableEq K] (P : K → ℕ) [∀ k, NeZero (P k)]
    (d : ℕ) {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ : σ₁ ≤ σ₂) :
    unconditionedSpatialWidthCutoff (unconditionedResidueSiteBound P)
      (unconditionedSpatialTrimFraction d σ₂) (unconditionedCollisionWidth P σ₂) ≤
    unconditionedSpatialWidthCutoff (unconditionedResidueSiteBound P)
      (unconditionedSpatialTrimFraction d σ₁) (unconditionedCollisionWidth P σ₁) := by
  have htrim : unconditionedSpatialTrimFraction d σ₁ ≤ unconditionedSpatialTrimFraction d σ₂ :=
    div_le_div_of_nonneg_right hσ (by positivity)
  have htrimpos : 0 < unconditionedSpatialTrimFraction d σ₁ := by
    unfold unconditionedSpatialTrimFraction
    positivity
  have hcollision : unconditionedCollisionWidth P σ₂ ≤ unconditionedCollisionWidth P σ₁ :=
    div_le_div_of_nonneg_left (by positivity) hσ₁ hσ
  have hsite : 0 ≤ unconditionedResidueSiteBound P :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  unfold unconditionedSpatialWidthCutoff
  apply max_le_max
  · exact div_le_div_of_nonneg_left (by norm_num) htrimpos htrim
  · apply (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (max_le_max_left _ hcollision) (by positivity))
      (htrimpos.le.trans htrim)).trans
    exact div_le_div_of_nonneg_left (by positivity) htrimpos htrim

theorem exists_unconditioned_late_prime_side_budget (n₀ : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ (p t : ℝ), 2 ≤ p → p ≤ t →
      ∃ (P : Fin n₀ → ℕ) (hprime : ∀ i, (P i).Prime),
        Function.Injective P ∧ (∀ i j, P i ≤ 2 ^ (n₀ + 1) * P j) ∧
        (∀ i, Real.exp t ≤ (P i : ℝ) ∧ (P i : ℝ) ≤ Real.exp (t + (n₀ : ℝ) + 2)) ∧
        (∀ i, Real.exp p ≤ (P i : ℝ)) ∧
        ∀ d : ℕ, (d : ℝ) ≤ p →
          let : ∀ i, NeZero (P i) := fun i => ⟨(hprime i).ne_zero⟩
          unconditionedSpatialWidthCutoff (unconditionedResidueSiteBound P)
            (unconditionedSpatialTrimFraction d (Real.exp (-p)))
            (unconditionedCollisionWidth P (Real.exp (-p))) ≤ Real.exp ((t + 2) ^ E) := by
  obtain ⟨E, hE, hbudget⟩ := exists_unconditioned_prime_side_budget n₀
  refine ⟨E, hE, ?_⟩
  intro p t hp hpt
  obtain ⟨P, hprime, hinj, hcompare, hrange, hwidth⟩ := hbudget t (hp.trans hpt)
  refine ⟨P, hprime, hinj, hcompare, hrange,
    fun i => (Real.exp_le_exp.mpr hpt).trans (hrange i).1, ?_⟩
  intro d hd
  let : ∀ i, NeZero (P i) := fun i => ⟨(hprime i).ne_zero⟩
  exact (unconditionedSpatialWidthCutoff_antitone_surplus P d (Real.exp_pos (-t))
    (Real.exp_le_exp.mpr (neg_le_neg hpt))).trans (hwidth d (hd.trans hpt))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.UnconditionedScalarScaleNiltestBase
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical NNReal TensorProduct
namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical NNReal TensorProduct
namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical NNReal TensorProduct

theorem unconditionedScalarPrimeRatio_exp_bound (n : ℕ) (t : ℝ) :
    Real.exp (t + (n : ℝ) + 2) ≤ (unconditionedScalarPrimeRatio n : ℝ) * Real.exp t := by
  have hratio : Real.exp ((n : ℝ) + 2) ≤ (unconditionedScalarPrimeRatio n : ℝ) := by
    have hceil := Nat.le_ceil (Real.exp ((n : ℝ) + 2))
    unfold unconditionedScalarPrimeRatio
    push_cast
    linarith
  calc
    _ = Real.exp ((n : ℝ) + 2) * Real.exp t := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hratio (Real.exp_nonneg t)

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CanonicalZeroLayerBudgetedInitialization
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem unconditionedCommonSide_pos {n : ℕ} (P : Fin n → ℕ) :
    0 < unconditionedCommonSide P := by
  unfold unconditionedCommonSide
  omega

theorem le_unconditionedCommonSide {n : ℕ} (P : Fin n → ℕ) (j : Fin n) :
    P j ≤ unconditionedCommonSide P := by
  have hsum : P j ≤ ∑ i, P i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  unfold unconditionedCommonSide
  omega

theorem unconditionedCommonSide_le {n : ℕ} (P : Fin n → ℕ)
    (hpos : ∀ i, 0 < P i) (hcompare : ∀ i j, P i ≤ 2 ^ (n + 1) * P j)
    (j : Fin n) :
    unconditionedCommonSide P ≤ (1 + n * 2 ^ (n + 1)) * P j := by
  have hsum : (∑ i, P i) ≤ n * (2 ^ (n + 1) * P j) := by
    calc
      _ ≤ ∑ _i : Fin n, 2 ^ (n + 1) * P j := Finset.sum_le_sum (fun i _ => hcompare i j)
      _ = _ := by simp
  calc
    unconditionedCommonSide P = 1 + ∑ i, P i := rfl
    _ ≤ P j + n * (2 ^ (n + 1) * P j) := Nat.add_le_add (hpos j) hsum
    _ = _ := by ring

theorem unconditionedCommonSide_density {n : ℕ} (P : Fin n → ℕ)
    (hpos : ∀ i, 0 < P i) (hcompare : ∀ i j, P i ≤ 2 ^ (n + 1) * P j) :
    1 / ((1 + n * 2 ^ (n + 1) : ℕ) : ℝ) ^ n ≤
      (∏ i, (P i : ℝ)) / (unconditionedCommonSide P : ℝ) ^ n := by
  have hside : 0 < (unconditionedCommonSide P : ℝ) :=
    Nat.cast_pos.mpr (unconditionedCommonSide_pos P)
  have hfactor : 0 < ((1 + n * 2 ^ (n + 1) : ℕ) : ℝ) := by positivity
  have hprod : (unconditionedCommonSide P : ℝ) ^ n ≤
      ((1 + n * 2 ^ (n + 1) : ℕ) : ℝ) ^ n * ∏ i, (P i : ℝ) := by
    calc
      _ = ∏ _i : Fin n, (unconditionedCommonSide P : ℝ) := by simp
      _ ≤ ∏ i : Fin n, ((1 + n * 2 ^ (n + 1) : ℕ) : ℝ) * (P i : ℝ) := by
        apply Finset.prod_le_prod (fun _ _ => hside.le)
        intro i _
        exact_mod_cast unconditionedCommonSide_le P hpos hcompare i
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  apply (div_le_div_iff₀ (pow_pos hfactor _) (pow_pos hside _)).mpr
  simpa only [one_mul, mul_one, mul_comm] using hprod

theorem unconditionedCommonSide_root_budget {n : ℕ} (P : Fin n → ℕ) :
    1 + (n : ℝ) * (unconditionedCommonSide P : ℝ) ≤
      ((n : ℝ) + 1) * (1 + unconditionedResidueSiteBound P) := by
  rw [unconditionedCommonSide_cast]
  have hB : 0 ≤ unconditionedResidueSiteBound P :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  nlinarith

theorem unconditionedSpatialWidthCutoff_common_side_le {n : ℕ} (P : Fin n → ℕ)
    {τ L : ℝ} (hτ : 0 < τ) :
    unconditionedSpatialWidthCutoff ((n : ℝ) * (unconditionedCommonSide P : ℝ)) τ L ≤
      ((n : ℝ) + 1) *
        unconditionedSpatialWidthCutoff (unconditionedResidueSiteBound P) τ L := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hfactor : 0 ≤ (n : ℝ) + 1 := by positivity
  have hmax : 0 ≤ max (8 * (probabilityProfileLipschitz : ℝ)) L :=
    (by positivity : 0 ≤ 8 * (probabilityProfileLipschitz : ℝ)).trans (le_max_left _ _)
  unfold unconditionedSpatialWidthCutoff
  apply max_le
  · calc
      4 / τ ≤ ((n : ℝ) + 1) * (4 / τ) := by
        nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 4) hτ.le,
          mul_nonneg hn (div_nonneg (by norm_num : (0 : ℝ) ≤ 4) hτ.le)]
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) hfactor
  · calc
      _ ≤ 8 * (((n : ℝ) + 1) * (1 + unconditionedResidueSiteBound P)) *
          max (8 * (probabilityProfileLipschitz : ℝ)) L / τ := by
        apply div_le_div_of_nonneg_right _ hτ.le
        apply mul_le_mul_of_nonneg_right _ hmax
        exact mul_le_mul_of_nonneg_left (unconditionedCommonSide_root_budget P) (by norm_num)
      _ = ((n : ℝ) + 1) * (8 * (1 + unconditionedResidueSiteBound P) *
          max (8 * (probabilityProfileLipschitz : ℝ)) L / τ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) hfactor

theorem exists_unconditioned_late_prime_common_side_budget (n : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ (p t : ℝ), 2 ≤ p → p ≤ t →
      ∃ (P : Fin n → ℕ) (hprime : ∀ i, (P i).Prime) (S : ℕ),
        Function.Injective P ∧ (∀ i j, P i ≤ 2 ^ (n + 1) * P j) ∧
        (∀ i, Real.exp t ≤ (P i : ℝ) ∧ (P i : ℝ) ≤ Real.exp (t + (n : ℝ) + 2)) ∧
        (∀ i, Real.exp p ≤ (P i : ℝ)) ∧
        S = 1 + ∑ i, P i ∧ 0 < S ∧ (∀ i, P i ≤ S) ∧
        (∀ i, S ≤ (1 + n * 2 ^ (n + 1)) * P i) ∧
        1 / ((1 + n * 2 ^ (n + 1) : ℕ) : ℝ) ^ n ≤
          (∏ i, (P i : ℝ)) / (S : ℝ) ^ n ∧
        ∀ d : ℕ, (d : ℝ) ≤ p →
          let : ∀ i, NeZero (P i) := fun i => ⟨(hprime i).ne_zero⟩
          unconditionedSpatialWidthCutoff ((n : ℝ) * (S : ℝ))
            (unconditionedSpatialTrimFraction d (Real.exp (-p)))
            (unconditionedCollisionWidth P (Real.exp (-p))) ≤ Real.exp ((t + 2) ^ E) := by
  obtain ⟨E, hE, hchoose⟩ := exists_unconditioned_late_prime_side_budget n
  refine ⟨E + n + 3, by omega, ?_⟩
  intro p t hp hpt
  obtain ⟨P, hprime, hinj, hcompare, hrange, hearly, hcutoff⟩ := hchoose p t hp hpt
  refine ⟨P, hprime, unconditionedCommonSide P, hinj, hcompare, hrange, hearly, rfl,
    unconditionedCommonSide_pos P, le_unconditionedCommonSide P,
    unconditionedCommonSide_le P (fun i => (hprime i).pos) hcompare,
    unconditionedCommonSide_density P (fun i => (hprime i).pos) hcompare, ?_⟩
  intro d hd
  let : ∀ i, NeZero (P i) := fun i => ⟨(hprime i).ne_zero⟩
  have hτ : 0 < unconditionedSpatialTrimFraction d (Real.exp (-p)) := by
    unfold unconditionedSpatialTrimFraction
    positivity
  exact (unconditionedSpatialWidthCutoff_common_side_le P hτ).trans
    ((mul_le_mul_of_nonneg_left (hcutoff d hd) (by positivity)).trans
      (commonSide_exp_absorption n E (by linarith : 0 ≤ t)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem unconditionedCommonSide_scalar_bound {n : ℕ} (P : Fin n → ℕ)
    {t : ℝ} (ht : 0 ≤ t)
    (hP : ∀ j, (P j : ℝ) ≤ (unconditionedScalarPrimeRatio n : ℝ) * Real.exp t) :
    (unconditionedCommonSide P : ℝ) ≤
      (unconditionedCommonSideScalarRatio n : ℝ) * Real.exp t := by
  have hsum : unconditionedResidueSiteBound P ≤
      (n : ℝ) * ((unconditionedScalarPrimeRatio n : ℝ) * Real.exp t) := by
    calc
      _ ≤ ∑ _j : Fin n, (unconditionedScalarPrimeRatio n : ℝ) * Real.exp t :=
        Finset.sum_le_sum (fun j _ => hP j)
      _ = _ := by simp
  rw [unconditionedCommonSide_cast]
  unfold unconditionedCommonSideScalarRatio
  push_cast
  nlinarith [Real.one_le_exp_iff.mpr ht]

theorem unconditionedCommonSide_scalar_bound_of_range {n : ℕ} (P : Fin n → ℕ)
    {t : ℝ} (ht : 0 ≤ t)
    (hP : ∀ j, (P j : ℝ) ≤ Real.exp (t + (n : ℝ) + 2)) :
    (unconditionedCommonSide P : ℝ) ≤
      (unconditionedCommonSideScalarRatio n : ℝ) * Real.exp t :=
  unconditionedCommonSide_scalar_bound P ht
    (fun j => (hP j).trans (unconditionedScalarPrimeRatio_exp_bound n t))

theorem unconditionedCommonSide_le_exp_extra_mul {n : ℕ} (P : Fin n → ℕ)
    (hpos : ∀ j, 0 < P j) (hcompare : ∀ i j, P i ≤ 2 ^ (n + 1) * P j)
    (j : Fin n) :
    (unconditionedCommonSide P : ℝ) ≤
      Real.exp (unconditionedCommonSideExtra n) * (P j : ℝ) := by
  rw [exp_unconditionedCommonSideExtra]
  exact_mod_cast unconditionedCommonSide_le P hpos hcompare j

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

namespace CanonicalEmptyLayerGeometry

end CanonicalEmptyLayerGeometry


end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ScalarEndpointScalePowerBudget
namespace OAI

section

namespace Erdos3

theorem exists_scalarEndpointScale_power_budget
    (n r E C H early : ℕ) (hE : 2 ≤ E) (hC : 2 ≤ C)
    (hH : max 1 early ≤ H) :
    ∃ L : ℕ, 2 ≤ L ∧ ∀ p : ℝ, 2 ≤ p →
      let b := (p + 2) ^ H
      let scalarInput := (b + 2) ^ E
      let target := 8 * ((r * n : ℕ) + 1 : ℝ) * (scalarInput + 1)
      let t := (target + 2) ^ C
      p ≤ t ∧ (p + 2) ^ early ≤ t ∧
        (r : ℝ) * Real.exp t ≤ Real.exp ((p + 2) ^ L) := by
  let tPoly : Polynomial ℕ :=
    (Polynomial.C (8 * (r * n + 1)) *
      ((((Polynomial.X + 2) ^ H + 2) ^ E) + 1) + 2) ^ C
  obtain ⟨L, hL, hbound⟩ :=
    exists_natPolynomial_fixed_power_budget (tPoly + Polynomial.C r)
  refine ⟨L, hL, ?_⟩
  intro p hp b scalarInput target t
  have hp0 : 0 ≤ p := by linarith
  have hb0 : 0 ≤ b := by dsimp only [b]; positivity
  have hscalar0 : 0 ≤ scalarInput := by dsimp only [scalarInput]; positivity
  have htarget0 : 0 ≤ target := by dsimp only [target]; positivity
  have hpB : p ≤ b := le_power_budget hp0 ((le_max_left 1 early).trans hH)
  have hBscalar : b ≤ scalarInput := le_power_budget hb0 (by omega)
  have hcoefficient : (1 : ℝ) ≤ 8 * ((r * n : ℕ) + 1 : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) (r * n)
    linarith
  have hscalarTarget : scalarInput ≤ target := by
    calc
      _ ≤ scalarInput + 1 := by linarith
      _ ≤ _ := le_mul_of_one_le_left (by linarith) hcoefficient
  have hTargetT : target ≤ t := le_power_budget htarget0 (by omega)
  have hBT : b ≤ t := hBscalar.trans (hscalarTarget.trans hTargetT)
  have hearlyB : (p + 2) ^ early ≤ b :=
    pow_le_pow_right₀ (by linarith) ((le_max_right 1 early).trans hH)
  refine ⟨hpB.trans hBT, hearlyB.trans hBT, ?_⟩
  have hmajor : t + (r : ℝ) ≤ (p + 2) ^ L := by
    simpa [tPoly, b, scalarInput, target, t, Polynomial.eval₂_pow] using hbound p hp0
  have hr : (r : ℝ) ≤ Real.exp (r : ℝ) := by
    linarith [Real.add_one_le_exp (r : ℝ)]
  calc
    _ ≤ Real.exp (r : ℝ) * Real.exp t :=
      mul_le_mul_of_nonneg_right hr (Real.exp_pos _).le
    _ = Real.exp (t + r) := by rw [← Real.exp_add, add_comm]
    _ ≤ _ := Real.exp_le_exp.mpr hmajor

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScalarEndpointLatePrimeCommonSide
namespace OAI

section

namespace Erdos3
open scoped Classical BigOperators

theorem exists_scalarEndpoint_late_prime_common_side_oai
    (n scalarE scalarC scalarF inputPower earlyExponent : ℕ)
    (hn : 2 ≤ n) (hE : 2 ≤ scalarE) (hC : 2 ≤ scalarC) (_hF : 2 ≤ scalarF)
    (hInput : max 1 earlyExponent ≤ inputPower) :
    ∃ latePower : ℕ, 2 ≤ latePower ∧ ∃ sizePower : ℕ, 2 ≤ sizePower ∧
    ∀ {p : ℝ}, 2 ≤ p →
      let b := (p + 2) ^ inputPower
      let scalarInput := (b + 2) ^ scalarE
      let ratio := unconditionedCommonSideScalarRatio n
      let t := (8 * ((ratio * n : ℕ) + 1 : ℝ) * (scalarInput + 1) + 2) ^ scalarC
      p ≤ t ∧ (p + 2) ^ earlyExponent ≤ t ∧
      (scalarInput + scalarF) ^ scalarF ≤ (p + 2) ^ sizePower ∧
      ∃ (P : Fin n → ℕ) (hprime : ∀ j, (P j).Prime) (S : ℕ),
        S = unconditionedCommonSide P ∧ 0 < S ∧
        Function.Injective P ∧ (∀ i j, P i ≤ 2 ^ (n + 1) * P j) ∧
        (∀ j, Real.exp p ≤ (P j : ℝ) ∧ P j ≤ S) ∧
        (∀ j, Real.exp t ≤ (P j : ℝ) ∧ (P j : ℝ) ≤ Real.exp (t + (n : ℝ) + 2)) ∧
        (∀ j, (S : ℝ) / (P j : ℝ) ≤ Real.exp (unconditionedCommonSideExtra n)) ∧
        Real.exp t ≤ (S : ℝ) ∧ (S : ℝ) ≤ (ratio : ℝ) * Real.exp t ∧
        (S : ℝ) ≤ Real.exp ((p + 2) ^ latePower) ∧
        ∀ nX : ℕ, (nX : ℝ) ≤ p →
          let : ∀ j, NeZero (P j) := fun j => ⟨(hprime j).ne_zero⟩
          unconditionedSpatialWidthCutoff ((n : ℝ) * (S : ℝ))
            (unconditionedSpatialTrimFraction nX (Real.exp (-p)))
            (unconditionedCollisionWidth P (Real.exp (-p))) ≤ Real.exp ((p + 2) ^ sizePower) := by
  let ratio := unconditionedCommonSideScalarRatio n
  obtain ⟨A, _, hChoose⟩ := exists_unconditioned_late_prime_common_side_budget n
  obtain ⟨latePower, hLate, hScale⟩ :=
    exists_scalarEndpointScale_power_budget n ratio scalarE scalarC inputPower earlyExponent hE hC hInput
  obtain ⟨sizePower, hSize, hCutoff⟩ :=
    exists_scalarLatePrimeCutoff_composite_power_budget n ratio scalarE scalarC scalarF A inputPower
  refine ⟨latePower, hLate, sizePower, hSize, ?_⟩
  intro p hp b scalarInput ratio' t
  have hScale' := hScale p hp
  change p ≤ t ∧ (p + 2) ^ earlyExponent ≤ t ∧
    (ratio' : ℝ) * Real.exp t ≤ Real.exp ((p + 2) ^ latePower) at hScale'
  have hCutoff' := hCutoff p hp
  change (scalarInput + scalarF) ^ scalarF ≤ (p + 2) ^ sizePower ∧
    (t + 2) ^ A ≤ (p + 2) ^ sizePower at hCutoff'
  refine ⟨hScale'.1, hScale'.2.1, hCutoff'.1, ?_⟩
  obtain ⟨P, hprime, S, hinj, hcompare, hrange, hearly, hS, hSpos, hleS,
    _, _, hWidth⟩ := hChoose p t hp hScale'.1
  have hSeq : S = unconditionedCommonSide P := hS
  have ht0 : 0 ≤ t := (by linarith : 0 ≤ p).trans hScale'.1
  have hSup : (S : ℝ) ≤ (ratio' : ℝ) * Real.exp t := by
    rw [hSeq]
    exact unconditionedCommonSide_scalar_bound_of_range P ht0 (fun j => (hrange j).2)
  have hSlo : Real.exp t ≤ (S : ℝ) :=
    (hrange (⟨0, by omega⟩ : Fin n)).1.trans
      (Nat.cast_le.mpr (hleS (⟨0, by omega⟩ : Fin n)))
  refine ⟨P, hprime, S, hSeq, hSpos, hinj, hcompare,
    (fun j => ⟨hearly j, hleS j⟩), hrange, ?_, hSlo, hSup,
    hSup.trans hScale'.2.2, ?_⟩
  · intro j
    apply (div_le_iff₀ (Nat.cast_pos.mpr (hprime j).pos)).mpr
    rw [hSeq]
    exact unconditionedCommonSide_le_exp_extra_mul P (fun j => (hprime j).pos) hcompare j
  · intro nX hnX
    let : ∀ j, NeZero (P j) := fun j => ⟨(hprime j).ne_zero⟩
    exact (hWidth nX hnX).trans (Real.exp_le_exp.mpr hCutoff'.2)

end Erdos3

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.exists_scalarEndpoint_late_prime_common_side_oai := @OAI.Erdos3.exists_scalarEndpoint_late_prime_common_side_oai
