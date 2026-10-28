-- Prove2me | solution 1 for OAI.Problem337.RandomProducts.eventually_common_geometric_random_fractional_residues
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:06:04.70772+00:00
-- url     : https://prove2.me/submissions/51339e39-2943-4474-82fa-0f4ba566ceaf

import Mathlib
import Definitions.Def_OAIQ8EF000

section
-- module Solutions.OAIQ8_EF.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_BilinearFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

lemma residue_character_orthogonality {q : ℕ} [NeZero q] (y z : ZMod q) :
    (∑ x : ZMod q, ZMod.stdAddChar (x * y) *
      (starRingEnd ℂ) (ZMod.stdAddChar (x * z))) =
      if y = z then (q : ℂ) else 0 := by
  simp_rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, ← mul_neg, ← mul_add]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q)]
  simp only [add_neg_eq_zero, ZMod.card]
  split_ifs <;> simp

/-- Parseval's identity for the positive-sign transform on all residue classes. -/
theorem residueFourier_parseval {q : ℕ} [NeZero q] (β : ZMod q → ℂ) :
    (∑ x : ZMod q, ‖residueFourier β x‖ ^ 2) =
      (q : ℝ) * ∑ y : ZMod q, ‖β y‖ ^ 2 := by
  have hc : (∑ x : ZMod q, residueFourier β x *
      (starRingEnd ℂ) (residueFourier β x)) =
      (q : ℂ) * ∑ y : ZMod q, β y * (starRingEnd ℂ) (β y) := by
    simp only [residueFourier, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_comm]
    calc
      _ = ∑ z : ZMod q, (β z * (starRingEnd ℂ) (β y)) *
          ∑ x : ZMod q, ZMod.stdAddChar (x * z) *
            (starRingEnd ℂ) (ZMod.stdAddChar (x * y)) := by
        apply Finset.sum_congr rfl
        intro z _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = (q : ℂ) * (β y * (starRingEnd ℂ) (β y)) := by
        simp_rw [residue_character_orthogonality]
        simp [mul_comm]
  simpa only [Complex.mul_conj, ← Complex.ofReal_sum, ← Complex.ofReal_mul,
    ← Complex.ofReal_natCast, Complex.ofReal_inj, Complex.normSq_eq_norm_sq] using hc

/-- A unit frequency preserves the Parseval identity, also for composite moduli. -/
theorem residueFourier_parseval_unit {q : ℕ} [NeZero q]
    (β : ZMod q → ℂ) (c : (ZMod q)ˣ) :
    (∑ x : ZMod q, ‖residueFourier β ((c : ZMod q) * x)‖ ^ 2) =
      (q : ℝ) * ∑ y : ZMod q, ‖β y‖ ^ 2 := by
  rw [show (∑ x : ZMod q, ‖residueFourier β ((c : ZMod q) * x)‖ ^ 2) =
      ∑ x : ZMod q, ‖residueFourier β x‖ ^ 2 from
    Equiv.sum_comp c.mulLeft (fun x => ‖residueFourier β x‖ ^ 2)]
  exact residueFourier_parseval β

/-- The bilinear additive-character bound used for random prime products.
No primality hypothesis on the modulus is needed; the frequency is a unit. -/
theorem residue_bilinear_bound {q : ℕ} [NeZero q]
    (α β : ZMod q → ℂ) (c : (ZMod q)ˣ) :
    ‖∑ x : ZMod q, ∑ y : ZMod q,
      α x * β y * ZMod.stdAddChar ((c : ZMod q) * x * y)‖ ≤
      Real.sqrt (q : ℝ) * Real.sqrt (∑ x : ZMod q, ‖α x‖ ^ 2) *
        Real.sqrt (∑ y : ZMod q, ‖β y‖ ^ 2) := by
  have hsum : (∑ x : ZMod q, ∑ y : ZMod q,
      α x * β y * ZMod.stdAddChar ((c : ZMod q) * x * y)) =
      ∑ x : ZMod q, α x * residueFourier β ((c : ZMod q) * x) := by
    simp only [residueFourier, Finset.mul_sum, mul_assoc]
  rw [hsum]
  calc
    _ ≤ ∑ x : ZMod q, ‖α x * residueFourier β ((c : ZMod q) * x)‖ :=
      norm_sum_le _ _
    _ = ∑ x : ZMod q, ‖α x‖ * ‖residueFourier β ((c : ZMod q) * x)‖ := by
      simp only [norm_mul]
    _ ≤ Real.sqrt (∑ x : ZMod q, ‖α x‖ ^ 2) *
        Real.sqrt (∑ x : ZMod q, ‖residueFourier β ((c : ZMod q) * x)‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by
      rw [residueFourier_parseval_unit, Real.sqrt_mul (by positivity)]
      ring

/-- A probability vector bounded by `A` has squared ℓ² norm at most `A`. -/
lemma probability_sum_sq_le {ι : Type*} [Fintype ι]
    (α : ι → ℝ) (A : ℝ) (hα : ∀ x, 0 ≤ α x)
    (hA : ∀ x, α x ≤ A) (hsum : ∑ x, α x = 1) :
    ∑ x, α x ^ 2 ≤ A := by
  calc
    _ ≤ ∑ x, α x * A := Finset.sum_le_sum fun x _ => by
      simpa only [pow_two] using mul_le_mul_of_nonneg_left (hA x) (hα x)
    _ = A := by rw [← Finset.sum_mul, hsum, one_mul]

/-- The version for probability vectors used after controlling atom sizes in
random products. -/
theorem residue_bilinear_probability_bound {q : ℕ} [NeZero q]
    (α β : ZMod q → ℝ) (A B : ℝ) (c : (ZMod q)ˣ)
    (hα : ∀ x, 0 ≤ α x) (hβ : ∀ y, 0 ≤ β y)
    (hA : ∀ x, α x ≤ A) (hB : ∀ y, β y ≤ B)
    (hsα : ∑ x, α x = 1) (hsβ : ∑ y, β y = 1) :
    ‖∑ x : ZMod q, ∑ y : ZMod q,
      (α x : ℂ) * (β y : ℂ) * ZMod.stdAddChar ((c : ZMod q) * x * y)‖ ≤
      Real.sqrt (q : ℝ) * Real.sqrt A * Real.sqrt B := by
  have h := residue_bilinear_bound (fun x => (α x : ℂ)) (fun y => (β y : ℂ)) c
  have hαnorm : (∑ x : ZMod q, ‖(α x : ℂ)‖ ^ 2) = ∑ x, α x ^ 2 := by
    apply Finset.sum_congr rfl
    intro x _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hα x)]
  have hβnorm : (∑ y : ZMod q, ‖(β y : ℂ)‖ ^ 2) = ∑ y, β y ^ 2 := by
    apply Finset.sum_congr rfl
    intro y _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hβ y)]
  rw [hαnorm, hβnorm] at h
  exact h.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (probability_sum_sq_le α A hα hA hsα)) (Real.sqrt_nonneg _))
    (Real.sqrt_le_sqrt (probability_sum_sq_le β B hβ hB hsβ))
    (Real.sqrt_nonneg _) (by positivity))

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CeilResidue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace Problem337

/-- The natural remainder specified by a ceiling step is the canonical
representative of the negative residue, including remainder zero. -/
theorem residue_eq_neg_zmod_val {u N z h : ℕ} (hh : h < u)
    (heq : u * z = N + h) : h = (-(N : ZMod u)).val := by
  have hzmod := congrArg (fun a : ℕ => (a : ZMod u)) heq
  simp only [Nat.cast_mul, Nat.cast_add, ZMod.natCast_self, zero_mul] at hzmod
  have hcast : (h : ZMod u) = -(N : ZMod u) := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [add_comm] using hzmod.symm
  rw [← hcast, ZMod.val_natCast_of_lt hh]

theorem natural_ceil_residue_eq_neg_zmod_val (u N : ℕ) (hu : 0 < u) :
    u * ⌈(N : ℝ) / u⌉₊ - N = (-(N : ZMod u)).val := by
  obtain ⟨_, heq, hlt⟩ := natural_ceil_residue_spec u N hu
  exact residue_eq_neg_zmod_val hlt heq

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_PrimeProductFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- Unique factorization bounds any fixed-product family of prime lists by permutations. -/
lemma prime_list_fiber_card_le (S : Finset (List ℕ)) (s N : ℕ)
    (hlen : ∀ l ∈ S, l.length = s)
    (hprime : ∀ l ∈ S, ∀ p ∈ l, Nat.Prime p)
    (hprod : ∀ l ∈ S, l.prod = N) : S.card ≤ s.factorial := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨l, hl⟩
  · simp
  have hsub : S ⊆ l.permutations.toFinset := by
    intro a ha
    apply List.mem_toFinset.mpr
    apply List.mem_permutations.mpr
    exact (Nat.primeFactorsList_unique (hprod a ha) (hprime a ha)).trans
      (Nat.primeFactorsList_unique (hprod l hl) (hprime l hl)).symm
  calc
    S.card ≤ l.permutations.toFinset.card := Finset.card_le_card hsub
    _ ≤ l.permutations.length := List.toFinset_card_le _
    _ = s.factorial := by rw [List.length_permutations, hlen l hl]

/-- A fixed product has at most `s!` ordered prime factorizations of length `s`. -/
lemma prime_tuple_fiber_card_le {s : ℕ} (S : Finset (Fin s → ℕ)) (N : ℕ)
    (hprime : ∀ a ∈ S, ∀ i, Nat.Prime (a i))
    (hprod : ∀ a ∈ S, (∏ i, a i) = N) : S.card ≤ s.factorial := by
  have h := prime_list_fiber_card_le (S.image List.ofFn) s N
  rw [Finset.card_image_of_injective S List.ofFn_injective] at h
  apply h
  · intro l hl
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hl
    exact List.length_ofFn
  · intro l hl p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact hprime a ha i
  · intro l hl
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hl
    rw [List.prod_ofFn]
    exact hprod a ha

/-- The counting version of the prime-product atom bound, allowing repeated prime samples. -/
theorem prime_product_fiber_card (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (s N : ℕ) :
    (Finset.univ.filter (fun a : Fin s → ↥P => (∏ i, (a i : ℕ)) = N)).card ≤
      s.factorial := by
  classical
  let S := Finset.univ.filter (fun a : Fin s → ↥P => (∏ i, (a i : ℕ)) = N)
  let f : (Fin s → ↥P) → (Fin s → ℕ) := fun a i => a i
  have hf : Function.Injective f := by
    intro a b hab
    funext i
    apply Subtype.ext
    exact congrFun hab i
  have h := prime_tuple_fiber_card_le (S.image f) N
  rw [Finset.card_image_of_injective S hf] at h
  apply h
  · intro a ha i
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    exact hP (b i) (b i).property
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    exact (Finset.mem_filter.mp hb).2

/-- Reducing products modulo a modulus larger than all products preserves the atom bound. -/
theorem prime_product_mod_fiber_card (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (s q : ℕ) (hsmall : ∀ a : Fin s → ↥P, (∏ i, (a i : ℕ)) < q) (r : ZMod q) :
    (Finset.univ.filter (fun a : Fin s → ↥P => ((∏ i, (a i : ℕ)) : ZMod q) = r)).card ≤
      s.factorial := by
  classical
  apply le_trans (Finset.card_le_card ?_) (prime_product_fiber_card P hP s r.val)
  intro a ha
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ a, ?_⟩
  have h := congrArg ZMod.val (Finset.mem_filter.mp ha).2
  rw [← Nat.cast_prod, ZMod.val_natCast, Nat.mod_eq_of_lt (hsmall a)] at h
  exact h

lemma primeProductModMass_nonneg (P : Finset ℕ) (s q : ℕ) (r : ZMod q) :
    0 ≤ primeProductModMass P s q r := by
  unfold primeProductModMass
  positivity

lemma primeProductModMass_le (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (s q : ℕ) (hsmall : ∀ a : Fin s → ↥P, (∏ i, (a i : ℕ)) < q) (r : ZMod q) :
    primeProductModMass P s q r ≤ (s.factorial : ℝ) / (P.card : ℝ)^s := by
  apply div_le_div_of_nonneg_right
  · exact_mod_cast prime_product_mod_fiber_card P hP s q hsmall r
  · positivity

lemma sum_primeProductModMass (P : Finset ℕ) (hP : P.Nonempty)
    (s q : ℕ) [NeZero q] : (∑ r : ZMod q, primeProductModMass P s q r) = 1 := by
  classical
  have hcounts : (∑ r : ZMod q,
      (Finset.univ.filter (fun a : Fin s → ↥P => ((∏ i, (a i : ℕ)) : ZMod q) = r)).card)
      = P.card^s := by
    simpa using Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Fin s → ↥P)) (Finset.univ : Finset (ZMod q))
      (fun a => ((∏ i, (a i : ℕ)) : ZMod q))
  unfold primeProductModMass
  rw [← Finset.sum_div]
  have hcountsR := congrArg (fun x : ℕ => (x : ℝ)) hcounts
  push_cast at hcountsR
  rw [hcountsR]
  have hp : (0 : ℝ) < P.card := by exact_mod_cast Finset.card_pos.mpr hP
  exact div_self (by positivity)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RandomProductFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- Regroup a finite sum by the fibers of a map, with explicit fiber cardinalities. -/
lemma sum_fiber_card_mul {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (g : κ → ℂ) :
    (∑ r : κ, ((Finset.univ.filter (fun a : ι => f a = r)).card : ℂ) * g r) =
      ∑ a : ι, g (f a) := by
  classical
  calc
    _ = ∑ r : κ, ∑ a ∈ Finset.univ.filter (fun a : ι => f a = r), g (f a) := by
      apply Finset.sum_congr rfl
      intro r _
      symm
      calc
        _ = ∑ a ∈ Finset.univ.filter (fun a : ι => f a = r), g r := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [(Finset.mem_filter.mp ha).2]
        _ = _ := by simp
    _ = _ := Finset.sum_fiberwise _ f (fun a => g (f a))

/-- The mass function of a prime product is the pushforward of uniform counting. -/
lemma primeProductModMass_average (P : Finset ℕ) (s q : ℕ) [NeZero q]
    (g : ZMod q → ℂ) :
    (∑ r : ZMod q, (primeProductModMass P s q r : ℂ) * g r) =
      (∑ a : Fin s → ↥P, g ((∏ i, (a i : ℕ)) : ZMod q)) / (P.card : ℂ)^s := by
  simp only [primeProductModMass, Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.ofReal_pow, div_mul_eq_mul_div]
  rw [← Finset.sum_div, sum_fiber_card_mul]

/-- Two independent prime products correspond to the product of their residue masses. -/
lemma primeProductModMass_double_average (P : Finset ℕ) (s q : ℕ) [NeZero q]
    (g : ZMod q → ZMod q → ℂ) :
    (∑ x : ZMod q, ∑ y : ZMod q,
      (primeProductModMass P s q x : ℂ) *
        (primeProductModMass P s q y : ℂ) * g x y) =
      (∑ a : Fin s → ↥P, ∑ b : Fin s → ↥P,
        g ((∏ i, (a i : ℕ)) : ZMod q) ((∏ i, (b i : ℕ)) : ZMod q)) /
          ((P.card : ℂ)^s)^2 := by
  simp_rw [mul_assoc, ← Finset.mul_sum]
  simp_rw [primeProductModMass_average]
  simp_rw [← Finset.sum_div]
  rw [div_div, pow_two]

/-- Exponential cancellation for two independent uniform prime products whenever
all attainable integer products are smaller than the modulus. Repetitions among
sampled primes are permitted. -/
theorem prime_product_bilinear_average_bound
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (hne : P.Nonempty)
    (s q : ℕ) [NeZero q]
    (hsmall : ∀ a : Fin s → ↥P, (∏ i, (a i : ℕ)) < q)
    (c : (ZMod q)ˣ) :
    ‖(∑ a : Fin s → ↥P, ∑ b : Fin s → ↥P,
      ZMod.stdAddChar ((c : ZMod q) * ((∏ i, (a i : ℕ)) : ZMod q) *
        ((∏ i, (b i : ℕ)) : ZMod q))) / ((P.card : ℂ)^s)^2‖ ≤
      Real.sqrt (q : ℝ) * ((s.factorial : ℝ) / (P.card : ℝ)^s) := by
  have h := residue_bilinear_probability_bound
    (primeProductModMass P s q) (primeProductModMass P s q)
    ((s.factorial : ℝ) / (P.card : ℝ)^s)
    ((s.factorial : ℝ) / (P.card : ℝ)^s) c
    (primeProductModMass_nonneg P s q) (primeProductModMass_nonneg P s q)
    (primeProductModMass_le P hP s q hsmall) (primeProductModMass_le P hP s q hsmall)
    (sum_primeProductModMass P hne s q) (sum_primeProductModMass P hne s q)
  rw [primeProductModMass_double_average] at h
  simpa only [mul_assoc, Real.mul_self_sqrt (by positivity :
      0 ≤ (s.factorial : ℝ) / (P.card : ℝ)^s)] using h

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_ReducedCharacter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace Problem337

/-- The standard additive character evaluated at a natural integer. -/
lemma stdAddChar_natCast {q : ℕ} [NeZero q] (z : ℕ) :
    ZMod.stdAddChar (z : ZMod q) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (q : ℂ)) := by
  simpa using ZMod.stdAddChar_coe (N := q) (z : ℤ)

lemma reduced_modulus_pos (a u : ℕ) (hu : 0 < u) :
    0 < u / a.gcd u :=
  Nat.div_pos (Nat.gcd_le_right a hu) (Nat.gcd_pos_of_pos_right a hu)

/-- Exact phase reduction to a primitive (unit-frequency) character. This also
covers `a = 0`, where the reduced modulus is `1`. -/
theorem stdAddChar_reduced (a u z : ℕ) (hu : 0 < u)
    [NeZero u] [NeZero (u / a.gcd u)] :
    ZMod.stdAddChar ((a * z : ℕ) : ZMod u) =
      ZMod.stdAddChar ((reducedFrequency a u hu : ZMod (u / a.gcd u)) *
        (z : ZMod (u / a.gcd u))) := by
  rw [reducedFrequency_coe, ← Nat.cast_mul]
  rw [stdAddChar_natCast, stdAddChar_natCast]
  congr 1
  have hgu : a.gcd u * (u / a.gcd u) = u :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right a u)
  have hga : a.gcd u * (a / a.gcd u) = a :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left a u)
  have hguC : (a.gcd u : ℂ) * ((u / a.gcd u : ℕ) : ℂ) = (u : ℂ) := by
    exact_mod_cast hgu
  have hgaC : (a.gcd u : ℂ) * ((a / a.gcd u : ℕ) : ℂ) = (a : ℂ) := by
    exact_mod_cast hga
  push_cast
  rw [← hguC, ← hgaC]
  have hg : (a.gcd u : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.gcd_pos_of_pos_right a hu).ne'
  have hq : ((u / a.gcd u : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (reduced_modulus_pos a u hu).ne'
  field_simp

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_ExposedCorrelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- The correlation bound after exposing all but two independent prime products.
The effective modulus is `u / gcd(a,u)`, and no coprimality of `a` and `u` is
assumed. -/
theorem exposed_prime_correlation_bound
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (hne : P.Nonempty)
    (s a u : ℕ) (hu : 0 < u) [NeZero u] [NeZero (u / a.gcd u)]
    (hsmall : ∀ w : Fin s → ↥P, (∏ i, (w i : ℕ)) < u / a.gcd u)
    (t : ZMod u) :
    ‖(∑ w₁ : Fin s → ↥P, ∑ w₂ : Fin s → ↥P,
      ZMod.stdAddChar
        (((a * (∏ i, (w₁ i : ℕ)) * (∏ i, (w₂ i : ℕ)) : ℕ) : ZMod u) - t)) /
        ((P.card : ℂ)^s)^2‖ ≤
      Real.sqrt ((u / a.gcd u : ℕ) : ℝ) *
        ((s.factorial : ℝ) / (P.card : ℝ)^s) := by
  have hshift :
      ‖(∑ w₁ : Fin s → ↥P, ∑ w₂ : Fin s → ↥P,
        ZMod.stdAddChar
          (((a * (∏ i, (w₁ i : ℕ)) * (∏ i, (w₂ i : ℕ)) : ℕ) : ZMod u) - t)) /
          ((P.card : ℂ)^s)^2‖ =
      ‖(∑ w₁ : Fin s → ↥P, ∑ w₂ : Fin s → ↥P,
        ZMod.stdAddChar
          ((a * (∏ i, (w₁ i : ℕ)) * (∏ i, (w₂ i : ℕ)) : ℕ) : ZMod u)) /
          ((P.card : ℂ)^s)^2‖ := by
    simp_rw [AddChar.map_sub_eq_div, ← Finset.sum_div]
    rw [div_right_comm, norm_div, AddChar.norm_apply, div_one]
  rw [hshift]
  have hp := prime_product_bilinear_average_bound P hP hne s
    (u / a.gcd u) hsmall (reducedFrequency a u hu)
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  apply Finset.sum_congr rfl
  intro w₁ _
  apply Finset.sum_congr rfl
  intro w₂ _
  rw [Nat.mul_assoc, stdAddChar_reduced a u _ hu, Nat.cast_mul, mul_assoc]
  simp only [Nat.cast_prod]

/-- Numerically, the square-root loss in the modulus changes an atom bound
`exp(-7 V / 10)` into the correlation bound `exp(-V / 5)`. -/
lemma sqrt_mul_atom_le_exp {q A V : ℝ}
    (hq : q ≤ Real.exp V) (hA : A ≤ Real.exp (-7 * V / 10)) (hA0 : 0 ≤ A) :
    Real.sqrt q * A ≤ Real.exp (-V / 5) := by
  have hsqrt : Real.sqrt q ≤ Real.exp (V / 2) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨(Real.exp_pos _).le, ?_⟩
    have heq : Real.exp (V / 2) ^ 2 = Real.exp V := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [heq]
    exact hq
  calc
    _ ≤ Real.exp (V / 2) * Real.exp (-7 * V / 10) :=
      mul_le_mul hsqrt hA hA0 (Real.exp_pos _).le
    _ = Real.exp (-V / 5) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The good-exposure estimate in the random-product argument. The product
size and atom decay hypotheses are separated from the algebraic cancellation. -/
theorem exposed_prime_correlation_le_exp
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (hne : P.Nonempty)
    (s a u : ℕ) (hu : 0 < u) [NeZero u] [NeZero (u / a.gcd u)]
    (hsmall : ∀ w : Fin s → ↥P, (∏ i, (w i : ℕ)) < u / a.gcd u)
    (t : ZMod u) (V : ℝ) (huV : (u : ℝ) ≤ Real.exp V)
    (hatom : (s.factorial : ℝ) / (P.card : ℝ)^s ≤ Real.exp (-7 * V / 10)) :
    ‖(∑ w₁ : Fin s → ↥P, ∑ w₂ : Fin s → ↥P,
      ZMod.stdAddChar
        (((a * (∏ i, (w₁ i : ℕ)) * (∏ i, (w₂ i : ℕ)) : ℕ) : ZMod u) - t)) /
        ((P.card : ℂ)^s)^2‖ ≤ Real.exp (-V / 5) := by
  apply (exposed_prime_correlation_bound P hP hne s a u hu hsmall t).trans
  apply sqrt_mul_atom_le_exp _ hatom (by positivity)
  have hqu : ((u / a.gcd u : ℕ) : ℝ) ≤ (u : ℝ) := by
    exact_mod_cast Nat.div_le_self u (a.gcd u)
  exact hqu.trans huV

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RandomProductParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace Problem337.RandomProducts

theorem freshLength_bounds {S V : ℝ} (hS : 1 < S)
    (hV : 100000 * Real.log S ≤ V) :
    (74 / 100 : ℝ) * V / (100 * Real.log S) ≤ freshLength S V ∧
    (freshLength S V : ℝ) ≤ (3 / 4 : ℝ) * V / (100 * Real.log S) := by
  have hlog : 0 < Real.log S := Real.log_pos hS
  have hVpos : 0 < V := by nlinarith
  have hx : 0 ≤ (3 / 4 : ℝ) * V / (100 * Real.log S) := by positivity
  constructor
  · have hfloor := Nat.sub_one_lt_floor ((3 / 4 : ℝ) * V / (100 * Real.log S))
    dsimp [freshLength]
    have hdiff : (74 / 100 : ℝ) * V / (100 * Real.log S) ≤
        (3 / 4 : ℝ) * V / (100 * Real.log S) - 1 := by
      apply (le_sub_iff_add_le).mpr
      apply (le_div_iff₀ (by positivity : 0 < 100 * Real.log S)).mpr
      field_simp
      nlinarith
    linarith
  · exact Nat.floor_le hx

theorem freshLength_eight_le_blockLength {S V : ℝ} (hS : 1 < S)
    (hV : 100000 * Real.log S ≤ V) (hVS : V ≤ S) :
    8 * freshLength S V ≤ blockLength S := by
  have hlog : 0 < Real.log S := Real.log_pos hS
  have hSpos : 0 < S := by linarith
  have hb : 2 ≤ S / Real.log S := by
    apply (le_div_iff₀ hlog).mpr
    nlinarith
  have hf := (freshLength_bounds hS hV).2
  have hfloor := Nat.sub_one_lt_floor (S / Real.log S)
  have hscale : (8 : ℝ) * freshLength S V ≤ (6 / 100 : ℝ) * (S / Real.log S) := by
    have := mul_le_mul_of_nonneg_left hf (by norm_num : (0 : ℝ) ≤ 8)
    have hdiv : V / Real.log S ≤ S / Real.log S := div_le_div_of_nonneg_right hVS hlog.le
    calc
      (8 : ℝ) * freshLength S V ≤ 8 * ((3 / 4 : ℝ) * V / (100 * Real.log S)) := this
      _ = (6 / 100 : ℝ) * (V / Real.log S) := by ring
      _ ≤ (6 / 100 : ℝ) * (S / Real.log S) := by gcongr
  have hreal : (8 : ℝ) * freshLength S V ≤ (blockLength S : ℝ) := by
    dsimp [blockLength]
    nlinarith
  exact_mod_cast hreal

/-- The factorial multiplicity bound implies the required small atom bound. -/
theorem fresh_factorial_atom_le_exp {S V : ℝ} (hS : 2 ≤ S)
    (hV : 100000 * Real.log S ≤ V) (hVS : V ≤ S) :
    ((freshLength S V).factorial : ℝ) / (S ^ 99) ^ freshLength S V ≤
      Real.exp (-(7 / 10 : ℝ) * V) := by
  have hSone : 1 < S := by linarith
  have hSpos : 0 < S := by linarith
  have hlog : 0 < Real.log S := Real.log_pos hSone
  have hVpos : 0 < V := by nlinarith
  have hloghalf : (1 / 2 : ℝ) ≤ Real.log S := by
    have htwo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at htwo
    exact htwo.trans (Real.log_le_log (by norm_num) hS)
  obtain ⟨hflower, hfupper⟩ := freshLength_bounds hSone hV
  have hlo := (div_le_iff₀ (by positivity : 0 < 100 * Real.log S)).mp hflower
  have hhi := (le_div_iff₀ (by positivity : 0 < 100 * Real.log S)).mp hfupper
  have hsnonneg : (0 : ℝ) ≤ freshLength S V := Nat.cast_nonneg _
  have hs : (freshLength S V : ℝ) ≤ S := by
    have := mul_le_mul_of_nonneg_left hloghalf hsnonneg
    nlinarith
  have hfact : ((freshLength S V).factorial : ℝ) ≤ S ^ freshLength S V := by
    calc
      ((freshLength S V).factorial : ℝ) ≤
          (freshLength S V : ℝ) ^ freshLength S V := by
        exact_mod_cast Nat.factorial_le_pow (freshLength S V)
      _ ≤ S ^ freshLength S V := pow_le_pow_left₀ hsnonneg hs _
  have hfactlog := Real.log_le_log (by positivity : (0 : ℝ) < (freshLength S V).factorial) hfact
  rw [Real.log_pow] at hfactlog
  apply (Real.log_le_iff_le_exp (by positivity :
    0 < ((freshLength S V).factorial : ℝ) / (S ^ 99) ^ freshLength S V)).mp
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  push_cast
  nlinarith

/-- Atom estimate with the actual cardinality of the prime sampling set. -/
theorem fresh_factorial_atom_of_card {S V : ℝ} (P : ℕ) (hS : 2 ≤ S)
    (hV : 100000 * Real.log S ≤ V) (hVS : V ≤ S)
    (hP : S ^ 99 ≤ (P : ℝ)) :
    ((freshLength S V).factorial : ℝ) / (P : ℝ) ^ freshLength S V ≤
      Real.exp (-(7 / 10 : ℝ) * V) := by
  calc
    ((freshLength S V).factorial : ℝ) / (P : ℝ) ^ freshLength S V ≤
        ((freshLength S V).factorial : ℝ) / (S ^ 99) ^ freshLength S V := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact pow_le_pow_left₀ (by positivity) hP _
    _ ≤ Real.exp (-(7 / 10 : ℝ) * V) := fresh_factorial_atom_le_exp hS hV hVS

theorem blockLength_le_self {S : ℝ} (hS : Real.exp 1 ≤ S) :
    (blockLength S : ℝ) ≤ S := by
  have hSpos : 0 < S := lt_of_lt_of_le (Real.exp_pos _) hS
  have hlog : 1 ≤ Real.log S := by
    have := Real.log_le_log (Real.exp_pos 1) hS
    simpa using this
  calc
    (blockLength S : ℝ) ≤ S / Real.log S := Nat.floor_le (by positivity)
    _ ≤ S := div_le_self hSpos.le hlog

/-- The Hamming-distance condition supplies two disjoint fresh blocks. -/
theorem fresh_coordinates_fit {S V : ℝ} (hS : 1 < S)
    (hV : 100000 * Real.log S ≤ V) (hVS : V ≤ S)
    (B : ℕ) (hB : blockLength S ≤ 4 * B) :
    2 * freshLength S V ≤ B := by
  have := freshLength_eight_le_blockLength hS hV hVS
  omega

theorem blockLength_large {S V : ℝ} (hS : 1 < S)
    (hV : 100000 * Real.log S ≤ V) (hVS : V ≤ S) :
    100000 ≤ blockLength S := by
  apply Nat.le_floor
  apply (le_div_iff₀ (Real.log_pos hS)).mpr
  norm_num
  linarith

end Problem337.RandomProducts

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_ConcreteGoodExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337.RandomProducts

/-- Allows the wider prime pool with upper endpoint `S^101`. -/
lemma fresh_wide_product_le_exp {S V : ℝ} (hS : 1 < S)
    (hV : 100000 * Real.log S ≤ V) :
    (S ^ 101) ^ freshLength S V ≤ Real.exp ((4 / 5 : ℝ) * V) := by
  have hlog : 0 < Real.log S := Real.log_pos hS
  have hSpos : 0 < S := by linarith
  have hVpos : 0 < V := by nlinarith
  have hf := (freshLength_bounds hS hV).2
  have hc := (le_div_iff₀ (by positivity : 0 < 100 * Real.log S)).mp hf
  apply (Real.log_le_iff_le_exp (by positivity :
    0 < (S ^ 101) ^ freshLength S V)).mp
  rw [Real.log_pow, Real.log_pow]
  push_cast
  nlinarith

lemma fresh_wide_samples_lt_modulus {S V : ℝ} (hS : 1 < S)
    (hV : 100000 * Real.log S ≤ V) (q : ℕ)
    (hq : Real.exp ((9 / 10 : ℝ) * V) ≤ (q : ℝ))
    (p : Fin (freshLength S V) → ℕ) (hp : ∀ i, (p i : ℝ) ≤ S ^ 101) :
    (∏ i, p i) < q := by
  have hlog : 0 < Real.log S := Real.log_pos hS
  have hVpos : 0 < V := by nlinarith
  have hprod : ((∏ i, p i : ℕ) : ℝ) ≤ (S ^ 101) ^ freshLength S V := by
    push_cast
    calc
      (∏ i, (p i : ℝ)) ≤ ∏ _i : Fin (freshLength S V), S ^ 101 :=
        Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun index _ => hp index)
      _ = _ := by simp
  have h : ((∏ i, p i : ℕ) : ℝ) < (q : ℝ) := calc
    _ ≤ (S ^ 101) ^ freshLength S V := hprod
    _ ≤ Real.exp ((4 / 5 : ℝ) * V) := fresh_wide_product_le_exp hS hV
    _ < Real.exp ((9 / 10 : ℝ) * V) := Real.exp_lt_exp.mpr (by nlinarith)
    _ ≤ (q : ℝ) := hq
  exact_mod_cast h

/-- Concrete good-exposure estimate, with atom decay proved rather than assumed. -/
theorem concrete_good_exposure_bound
    (S V : ℝ) (hS : 2 ≤ S) (hV : 100000 * Real.log S ≤ V) (hVS : V ≤ S)
    (P : Finset ℕ) (hPprime : ∀ p ∈ P, Nat.Prime p)
    (hPcard : S ^ 99 ≤ (P.card : ℝ))
    (hPupper : ∀ p ∈ P, (p : ℝ) ≤ S ^ 101)
    (a u : ℕ) (hu : 0 < u) [NeZero u]
    (huV : (u : ℝ) ≤ Real.exp V)
    (hq : Real.exp ((9 / 10 : ℝ) * V) ≤ ((u / a.gcd u : ℕ) : ℝ))
    (t : ZMod u) :
    ‖(∑ w₁ : Fin (freshLength S V) → ↥P,
      ∑ w₂ : Fin (freshLength S V) → ↥P,
      ZMod.stdAddChar
        (((a * (∏ i, (w₁ i : ℕ)) * (∏ i, (w₂ i : ℕ)) : ℕ) : ZMod u) - t)) /
        ((P.card : ℂ)^freshLength S V)^2‖ ≤ Real.exp (-V / 5) := by
  have hSpos : 0 < S := by linarith
  have hcardpos : 0 < (P.card : ℝ) := lt_of_lt_of_le (by positivity) hPcard
  have hne : P.Nonempty := Finset.card_pos.mp (by exact_mod_cast hcardpos)
  let : NeZero (u / a.gcd u) := ⟨(reduced_modulus_pos a u hu).ne'⟩
  have hsmall (w : Fin (freshLength S V) → ↥P) :
      (∏ i, (w i : ℕ)) < u / a.gcd u :=
    fresh_wide_samples_lt_modulus (by linarith) hV _ hq
      (fun i => (w i : ℕ)) (fun i => hPupper _ (w i).property)
  apply exposed_prime_correlation_le_exp P hPprime hne (freshLength S V) a u hu hsmall t V huV
  have heq : -(7 / 10 : ℝ) * V = -7 * V / 10 := by ring
  simpa only [heq] using fresh_factorial_atom_of_card P.card hS hV hVS hPcard

end Problem337.RandomProducts

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CyclicInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- A point to the right of an inner interval is separated from that interval
in both directions around the cyclic group. -/
theorem cyclic_sub_val_margin {q : ℕ} [NeZero q]
    (x y : ZMod q) (d : ℕ) (hy : d ≤ y.val)
    (hgap : y.val + d ≤ x.val) :
    d ≤ (x - y).val ∧ (x - y).val + d ≤ q := by
  have hxq := ZMod.val_lt x
  rw [ZMod.val_sub (by omega : y.val ≤ x.val)]
  omega

/-- Normalized version of the cyclic separation estimate. -/
theorem cyclic_sub_phase_margin {q : ℕ} [NeZero q]
    (x y : ZMod q) (d : ℕ) (hy : d ≤ y.val)
    (hgap : y.val + d ≤ x.val) :
    (d : ℝ) / q ≤ ((x - y).val : ℝ) / q ∧
    ((x - y).val : ℝ) / q ≤ 1 - (d : ℝ) / q := by
  obtain ⟨hlo, hhi⟩ := cyclic_sub_val_margin x y d hy hgap
  have hq : (0 : ℝ) < q := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q))
  constructor
  · apply div_le_div_of_nonneg_right _ hq.le
    exact_mod_cast hlo
  · apply (div_le_iff₀ hq).mpr
    have hh : ((x - y).val : ℝ) + d ≤ q := by exact_mod_cast hhi
    rw [sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hq)]
    linarith

/-- An inner initial interval with margin `d` lies away from every point
outside the initial target interval ending at `B+d`. -/
theorem cyclic_initial_interval_phase_margin {q : ℕ} [NeZero q]
    (x y : ZMod q) (d B : ℕ)
    (hx : B + d ≤ x.val) (hy : d ≤ y.val ∧ y.val ≤ B) :
    (d : ℝ) / q ≤ ((x - y).val : ℝ) / q ∧
    ((x - y).val : ℝ) / q ≤ 1 - (d : ℝ) / q :=
  cyclic_sub_phase_margin x y d hy.1 (by omega)

/-- A cyclic interval is the image of its ordinary representatives. -/
theorem cyclic_interval_eq_image {q : ℕ} [NeZero q] (a b : ℕ) (hb : b < q) :
    (Finset.univ.filter (fun x : ZMod q => a ≤ x.val ∧ x.val ≤ b)) =
      (Finset.Icc a b).image (fun n : ℕ => (n : ZMod q)) := by
  classical
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hx
    exact ⟨x.val, Finset.mem_Icc.mpr hx, ZMod.natCast_zmod_val x⟩
  · rintro ⟨n, hn, rfl⟩
    have hn' := Finset.mem_Icc.mp hn
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : n < q)] using hn'

/-- Exact cardinality of a cyclic interval which does not cross zero. -/
theorem cyclic_interval_card {q : ℕ} [NeZero q] (a b : ℕ) (hb : b < q) :
    (Finset.univ.filter (fun x : ZMod q => a ≤ x.val ∧ x.val ≤ b)).card =
      b + 1 - a := by
  classical
  rw [cyclic_interval_eq_image a b hb]
  have hinj : Set.InjOn (fun n : ℕ => (n : ZMod q)) (Finset.Icc a b) := by
    intro n hn m hm hnm
    have hn' := Finset.mem_Icc.mp hn
    have hm' := Finset.mem_Icc.mp hm
    have h := congrArg ZMod.val hnm
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : n < q),
      Nat.mod_eq_of_lt (by omega : m < q)] using h
  rw [Finset.card_image_iff.mpr hinj, Nat.card_Icc]

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CyclicSmoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.CyclicSmoothing

lemma window_le_one {G : Type*} [AddCommGroup G] [Fintype G]
    (K : G → ℝ) (J : Finset G) (hK : ∀ x, 0 ≤ K x) (hmass : ∑ x, K x = 1)
    (x : G) : window K J x ≤ 1 := by
  calc
    window K J x ≤ ∑ y, K (x - y) := Finset.sum_le_univ_sum_of_nonneg (fun _ => hK _)
    _ = ∑ y, K y := (Equiv.subLeft x).sum_comp K
    _ = 1 := hmass

lemma window_le_of_kernel_bound {G : Type*} [AddGroup G]
    (K : G → ℝ) (J : Finset G) (x : G) (η : ℝ)
    (h : ∀ y ∈ J, K (x - y) ≤ η) : window K J x ≤ (J.card : ℝ) * η := by
  calc
    window K J x ≤ ∑ _y ∈ J, η := Finset.sum_le_sum h
    _ = (J.card : ℝ) * η := by simp

/-- The counting conclusion of the smoothing argument. The spectral input is
only the sampled mean lower bound; the geometric input is the kernel tail
bound outside the outer window. Repeated sample values are allowed. -/
theorem count_window_lower {G Ω : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (K : G → ℝ) (inner outer : Finset G) (samples : Finset Ω) (x : Ω → G)
    (E η : ℝ) (hK : ∀ y, 0 ≤ K y) (hmass : ∑ y, K y = 1) (hη : 0 ≤ η)
    (htail : ∀ z, z ∉ outer → ∀ y ∈ inner, K (z - y) ≤ η)
    (hmean : (samples.card : ℝ) * ((inner.card : ℝ) / Fintype.card G - E) ≤
      ∑ ω ∈ samples, window K inner (x ω)) :
    (samples.card : ℝ) * ((inner.card : ℝ) / Fintype.card G - E -
      (inner.card : ℝ) * η) ≤ ((samples.filter (fun ω => x ω ∈ outer)).card : ℝ) := by
  classical
  have hbound (ω : Ω) : window K inner (x ω) ≤
      (if x ω ∈ outer then (1 : ℝ) else 0) + (inner.card : ℝ) * η := by
    split_ifs with h
    · have hu := window_le_one K inner hK hmass (x ω)
      have hp : 0 ≤ (inner.card : ℝ) * η := by positivity
      linarith
    · simpa using window_le_of_kernel_bound K inner (x ω) η (htail _ h)
  have hsum := Finset.sum_le_sum (fun ω (_ : ω ∈ samples) => hbound ω)
  have hind : (∑ ω ∈ samples, if x ω ∈ outer then (1 : ℝ) else 0) =
      ((samples.filter (fun ω => x ω ∈ outer)).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp
  rw [Finset.sum_add_distrib, hind] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  nlinarith

end Problem337.CyclicSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_FejerBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337.GeometricKernel

theorem kernel_nonneg (h : ℕ) (z : ℂ) : 0 ≤ kernel h z := by
  unfold kernel
  positivity

theorem cyclic_geometric_sum_eq {q : ℕ} [NeZero q] (h : ℕ) (x : ZMod q) :
    (∑ j ∈ Finset.range h, ZMod.stdAddChar ((j : ZMod q) * x)) =
      ∑ j ∈ Finset.range h, (ZMod.stdAddChar x) ^ j := by
  apply Finset.sum_congr rfl
  intro j hj
  simpa only [nsmul_eq_mul] using ZMod.stdAddChar.map_nsmul_eq_pow j x

end Problem337.GeometricKernel

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_FourierSecondMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators
open Complex ComplexConjugate

namespace Problem337

lemma re_finset_sum {α : Type*} (s : Finset α) (f : α → ℂ) :
    (∑ a ∈ s, f a).re = ∑ a ∈ s, (f a).re :=
  map_sum Complex.reAddGroupHom f s

/-- Expand a finite complex second moment into pairwise correlations. -/
theorem finite_complex_second_moment_identity {α β : Type*}
    (U : Finset α) (T : Finset β) (z : α → β → ℂ) :
    (∑ u ∈ U, ‖∑ t ∈ T, z u t‖ ^ 2) =
      ∑ t ∈ T, ∑ s ∈ T, (∑ u ∈ U, z u t * conj (z u s)).re := by
  have hpoint (u : α) : ‖∑ t ∈ T, z u t‖ ^ 2 =
      ∑ t ∈ T, ∑ s ∈ T, (z u t * conj (z u s)).re := by
    calc
      ‖∑ t ∈ T, z u t‖ ^ 2 =
          ((∑ t ∈ T, z u t) * conj (∑ t ∈ T, z u t)).re := by
            rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
      _ = _ := by
        simp only [map_sum, Finset.sum_mul, Finset.mul_sum, re_finset_sum]
        rw [Finset.sum_comm]
  simp_rw [hpoint, re_finset_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.sum_comm]

end Problem337

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CyclicKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
open ComplexConjugate

namespace Problem337.CyclicSmoothing

lemma conj_stdAddChar {q : ℕ} [NeZero q] (x : ZMod q) :
    conj (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq,
    AddChar.norm_apply]
  simp

lemma stdAddChar_pow {q : ℕ} [NeZero q] (r : ℕ) (x : ZMod q) :
    (ZMod.stdAddChar x) ^ r = ZMod.stdAddChar ((r : ZMod q) * x) := by
  simpa only [nsmul_eq_mul] using (ZMod.stdAddChar.map_nsmul_eq_pow r x).symm

lemma cyclic_power_correlation {q h : ℕ} [NeZero q]
    (hhq : h ≤ q) {r s : ℕ} (hr : r < h) (hs : s < h) :
    (∑ x : ZMod q, (ZMod.stdAddChar x)^r * conj ((ZMod.stdAddChar x)^s)) =
      if r = s then (q : ℂ) else 0 := by
  have hcast : (r : ZMod q) - (s : ZMod q) = 0 ↔ r = s := by
    rw [sub_eq_zero, ZMod.natCast_eq_natCast_iff']
    rw [Nat.mod_eq_of_lt (hr.trans_le hhq), Nat.mod_eq_of_lt (hs.trans_le hhq)]
  have hpoint (x : ZMod q) :
      (ZMod.stdAddChar x)^r * conj ((ZMod.stdAddChar x)^s) =
        ZMod.stdAddChar (x * ((r : ZMod q) - (s : ZMod q))) := by
    rw [stdAddChar_pow, stdAddChar_pow, conj_stdAddChar, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [hpoint]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q)]
  simp [hcast, ZMod.card]

/-- Exact mass of the cyclic Fejer kernel below the modulus. -/
theorem sum_cyclic_kernel {q h : ℕ} [NeZero q] (hh : 0 < h) (hhq : h ≤ q) :
    (∑ x : ZMod q, GeometricKernel.kernel h (ZMod.stdAddChar x)) = (q : ℝ) := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  simp only [GeometricKernel.kernel]
  rw [← Finset.sum_div]
  have hraw : (∑ x : ZMod q, ‖∑ r ∈ Finset.range h, (ZMod.stdAddChar x)^r‖ ^ 2) =
      (h : ℝ) * q := by
    rw [finite_complex_second_moment_identity]
    calc
      (∑ r ∈ Finset.range h, ∑ s ∈ Finset.range h,
          (∑ x : ZMod q, (ZMod.stdAddChar x)^r * conj ((ZMod.stdAddChar x)^s)).re) =
          ∑ r ∈ Finset.range h, ∑ s ∈ Finset.range h,
            (if r = s then (q : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro s hs
        rw [cyclic_power_correlation hhq (Finset.mem_range.mp hr) (Finset.mem_range.mp hs)]
        split_ifs <;> simp
      _ = ∑ _r ∈ Finset.range h, (q : ℝ) := by
        apply Finset.sum_congr rfl
        intro r hr
        simp [Finset.mem_range.mp hr]
      _ = (h : ℝ) * q := by simp
  rw [hraw]
  field_simp

lemma normalizedKernel_nonneg {q : ℕ} [NeZero q] (h : ℕ) (x : ZMod q) :
    0 ≤ normalizedKernel h x := by
  exact div_nonneg (GeometricKernel.kernel_nonneg _ _) (Nat.cast_nonneg q)

lemma sum_normalizedKernel {q h : ℕ} [NeZero q] (hh : 0 < h) (hhq : h ≤ q) :
    (∑ x : ZMod q, normalizedKernel h x) = 1 := by
  simp only [normalizedKernel]
  rw [← Finset.sum_div, sum_cyclic_kernel hh hhq]
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  exact div_self hq

end Problem337.CyclicSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_FejerBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace Problem337

/-- Rounding the inner cyclic interval leaves fixed proportional margins. -/
theorem cyclic_interval_floor_budget (δ : ℝ) (q : ℕ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hscale : 128 ≤ δ * q) :
    let d := ⌊δ * q / 8⌋₊
    1 ≤ d ∧ 7 * d < q ∧ (8 * d : ℕ) ≤ δ * q ∧
    δ / 16 ≤ (d : ℝ) / q ∧
    11 * δ / 16 ≤ ((6 * d + 1 : ℕ) : ℝ) / q ∧
    ((6 * d + 1 : ℕ) : ℝ) / q ≤ δ := by
  let d := ⌊δ * q / 8⌋₊
  change 1 ≤ d ∧ 7 * d < q ∧ (8 * d : ℕ) ≤ δ * q ∧
    δ / 16 ≤ (d : ℝ) / q ∧
    11 * δ / 16 ≤ ((6 * d + 1 : ℕ) : ℝ) / q ∧
    ((6 * d + 1 : ℕ) : ℝ) / q ≤ δ
  have hq : (0 : ℝ) < q := by
    by_contra h
    have hq0 : (q : ℝ) = 0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg q)
    rw [hq0] at hscale
    norm_num at hscale
  have hdhi : (d : ℝ) ≤ δ * q / 8 := Nat.floor_le (by positivity)
  have hdlo : δ * q / 8 < (d : ℝ) + 1 := Nat.lt_floor_add_one _
  have hδq : δ * q ≤ (q : ℝ) := by nlinarith [mul_le_mul_of_nonneg_right hδ1 hq.le]
  have hd1 : 1 ≤ d := by exact_mod_cast (show (1 : ℝ) ≤ d by linarith)
  have hdb : 7 * d < q := by exact_mod_cast (show 7 * (d : ℝ) < q by linarith)
  refine ⟨hd1, hdb, ?_, ?_, ?_, ?_⟩
  · push_cast
    linarith
  · apply (le_div_iff₀ hq).mpr
    linarith
  · apply (le_div_iff₀ hq).mpr
    push_cast
    linarith
  · apply (div_le_iff₀ hq).mpr
    push_cast
    linarith

/-- A low-degree kernel simultaneously has small leakage and Fourier error. -/
theorem fejer_degree_floor_budget (δ : ℝ)
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / 65536) :
    let h := ⌊1 / (64 * δ ^ 3)⌋₊
    1 ≤ h ∧ 1 / (128 * δ ^ 3) ≤ (h : ℝ) ∧
    (h : ℝ) ≤ 1 / (64 * δ ^ 3) ∧
    64 / ((h : ℝ) * δ) ≤ δ / 8 ∧
    2 * (h : ℝ) * δ * δ ^ 3 ≤ δ / 32 := by
  let h := ⌊1 / (64 * δ ^ 3)⌋₊
  change 1 ≤ h ∧ 1 / (128 * δ ^ 3) ≤ (h : ℝ) ∧
    (h : ℝ) ≤ 1 / (64 * δ ^ 3) ∧
    64 / ((h : ℝ) * δ) ≤ δ / 8 ∧
    2 * (h : ℝ) * δ * δ ^ 3 ≤ δ / 32
  have hcube : 0 < δ ^ 3 := by positivity
  have hcubehi : δ ^ 3 ≤ (1 / 8 : ℝ) ^ 3 := by
    gcongr
    norm_num at *
    linarith
  have harg2 : (2 : ℝ) ≤ 1 / (64 * δ ^ 3) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 64 * δ ^ 3)).mpr
    norm_num at hcubehi
    linarith
  have hhhi : (h : ℝ) ≤ 1 / (64 * δ ^ 3) := Nat.floor_le (by positivity)
  have hhlo : 1 / (64 * δ ^ 3) < (h : ℝ) + 1 := Nat.lt_floor_add_one _
  have hh1 : 1 ≤ h := by exact_mod_cast (show (1 : ℝ) ≤ h by linarith)
  have hhpos : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have half : 1 / (128 * δ ^ 3) = (1 / (64 * δ ^ 3)) / 2 := by ring
  have hhalf : 1 / (128 * δ ^ 3) ≤ (h : ℝ) := by rw [half]; linarith
  refine ⟨hh1, hhalf, hhhi, ?_, ?_⟩
  · calc
      64 / ((h : ℝ) * δ) ≤ 64 / ((1 / (128 * δ ^ 3)) * δ) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        exact mul_le_mul_of_nonneg_right hhalf hδ.le
      _ = 8192 * δ ^ 2 := by
        field_simp
        ring
      _ ≤ δ / 8 := by
        have hh := mul_le_mul_of_nonneg_right hsmall hδ.le
        nlinarith
  · calc
      2 * (h : ℝ) * δ * δ ^ 3 ≤ 2 * (1 / (64 * δ ^ 3)) * δ * δ ^ 3 := by
        gcongr
      _ = δ / 32 := by
        field_simp
        ring

/-- The chosen degree uses only the prescribed low frequencies. -/
theorem fejer_degree_frequency_bound (δ : ℝ)
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / 65536) :
    ⌊1 / (64 * δ ^ 3)⌋₊ ≤ ⌊1 / δ ^ 4⌋₊ := by
  apply Nat.floor_mono
  apply one_div_le_one_div_of_le (by positivity)
  have hh := mul_le_mul_of_nonneg_right (show δ ≤ 64 by linarith)
    (show 0 ≤ δ ^ 3 by positivity)
  nlinarith

/-- The three error budgets leave at least half the target interval mass. -/
theorem fejer_localization_budget (δ mass inner error leakage : ℝ)
    (hδ : 0 ≤ δ) (hinner : 11 * δ / 16 ≤ inner)
    (herror : error ≤ δ / 32) (hleakage : leakage ≤ δ / 8)
    (hmass : inner - error - leakage ≤ mass) : δ / 2 ≤ mass := by
  linarith

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_FejerSampleMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337.FejerSampleMean

/-- Translating the samples rotates every Fourier coefficient without changing
its norm. -/
theorem norm_sum_character_translate {q : ℕ} [NeZero q] {I : Type*}
    [Fintype I] (x : I → ZMod q) (a y : ZMod q) :
    ‖∑ t : I, ZMod.stdAddChar (a * (x t - y))‖ =
      ‖∑ t : I, ZMod.stdAddChar (a * x t)‖ := by
  simp_rw [mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
  rw [← Finset.sum_mul, norm_mul]
  simp

/-- Negating a frequency conjugates its coefficient. -/
theorem norm_sum_character_neg {q : ℕ} [NeZero q] {I : Type*}
    [Fintype I] (x : I → ZMod q) (a : ZMod q) :
    ‖∑ t : I, ZMod.stdAddChar ((-a) * x t)‖ =
      ‖∑ t : I, ZMod.stdAddChar (a * x t)‖ := by
  simp_rw [neg_mul, AddChar.map_neg_eq_conj]
  rw [← map_sum (starRingEnd ℂ) (fun t : I => ZMod.stdAddChar (a * x t)) Finset.univ]
  exact Complex.norm_conj _

/-- Off-diagonal correlations of the geometric packet are controlled by the
positive low frequencies, with no unmentioned negative-frequency assumption. -/
theorem packet_correlation_bound {q h : ℕ} [NeZero q] {I : Type*}
    [Fintype I] (x : I → ZMod q) (y : ZMod q) (E : ℝ)
    (hfourier : ∀ l : ℕ, 1 ≤ l → l < h →
      ‖∑ t : I, ZMod.stdAddChar ((l : ZMod q) * x t)‖ ≤ E)
    (j k : Fin h) (hjk : j ≠ k) :
    ‖∑ t : I, ZMod.stdAddChar ((j.val : ZMod q) * (x t - y)) *
      (starRingEnd ℂ) (ZMod.stdAddChar ((k.val : ZMod q) * (x t - y)))‖ ≤ E := by
  have heq (t : I) :
      ZMod.stdAddChar ((j.val : ZMod q) * (x t - y)) *
          (starRingEnd ℂ) (ZMod.stdAddChar ((k.val : ZMod q) * (x t - y))) =
        ZMod.stdAddChar (((j.val : ZMod q) - (k.val : ZMod q)) * (x t - y)) := by
    rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [heq]
  rw [norm_sum_character_translate]
  have hne : j.val ≠ k.val := by intro he; exact hjk (Fin.ext he)
  by_cases hkj : k.val ≤ j.val
  · have hc : ((j.val : ZMod q) - (k.val : ZMod q)) = ((j.val - k.val : ℕ) : ZMod q) :=
      (Nat.cast_sub hkj).symm
    rw [hc]
    exact hfourier (j.val - k.val) (by omega) (by omega)
  · have hc : ((j.val : ZMod q) - (k.val : ZMod q)) = -((k.val - j.val : ℕ) : ZMod q) := by
      rw [Nat.cast_sub (by omega : j.val ≤ k.val)]
      ring
    rw [hc, norm_sum_character_neg]
    exact hfourier (k.val - j.val) (by omega) (by omega)

/-- Lower counterpart of the finite second-moment bound, using the same
honest off-diagonal correlation hypotheses. -/
theorem second_moment_lower {α β : Type*}
    (U : Finset α) (T : Finset β) (z : α → β → ℂ) (E : ℝ)
    (hunit : ∀ u ∈ U, ∀ t ∈ T, ‖z u t‖ = 1)
    (hcorr : ∀ t ∈ T, ∀ s ∈ T, t ≠ s →
      ‖∑ u ∈ U, z u t * (starRingEnd ℂ) (z u s)‖ ≤ E) :
    (U.card : ℝ) * T.card - (T.card : ℝ) * (T.card - 1 : ℝ) * E ≤
      ∑ u ∈ U, ‖∑ t ∈ T, z u t‖ ^ 2 := by
  classical
  rw [finite_complex_second_moment_identity]
  have hentry (t : β) (ht : t ∈ T) (s : β) (hs : s ∈ T) :
      -E + (if t = s then (U.card : ℝ) + E else 0) ≤
        (∑ u ∈ U, z u t * (starRingEnd ℂ) (z u s)).re := by
    by_cases hts : t = s
    · subst s
      have hd : (∑ u ∈ U, z u t * (starRingEnd ℂ) (z u t)).re = U.card := by
        simp only [re_finset_sum, Complex.mul_conj, Complex.ofReal_re]
        calc
          (∑ u ∈ U, Complex.normSq (z u t)) = ∑ _u ∈ U, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [Complex.normSq_eq_norm_sq, hunit u hu t ht]
            norm_num
          _ = _ := by simp
      simp [hd]
    · have hc := hcorr t ht s hs hts
      have hn := Complex.re_le_norm (-(∑ u ∈ U, z u t * (starRingEnd ℂ) (z u s)))
      simp only [Complex.neg_re, norm_neg] at hn
      simp only [ite_eq_right hts, add_zero]
      linarith
  calc
    _ = ∑ t ∈ T, ∑ s ∈ T, (-E + if t = s then (U.card : ℝ) + E else 0) := by
      have hrow (t : β) (ht : t ∈ T) :
          (∑ s ∈ T, (-E + if t = s then (U.card : ℝ) + E else 0)) =
            -(T.card : ℝ) * E + (U.card : ℝ) + E := by
        simp [Finset.sum_add_distrib, ht]
        ring
      simp_rw [Finset.sum_congr rfl hrow]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := Finset.sum_le_sum (fun t ht => Finset.sum_le_sum (fun s hs => hentry t ht s hs))

/-- The lower sampled mean of the geometric packet, before identifying the
packet with the named kernel. -/
theorem raw_packet_mean_lower {q h : ℕ} [NeZero q] {I : Type*}
    [Fintype I] [Nonempty I] (hh : 0 < h)
    (x : I → ZMod q) (y : ZMod q) (ε : ℝ)
    (hfourier : ∀ l : ℕ, 1 ≤ l → l < h →
      ‖∑ t : I, ZMod.stdAddChar ((l : ZMod q) * x t)‖ ≤
        (Fintype.card I : ℝ) * ε) :
    1 - ((h : ℝ) - 1) * ε ≤
      (∑ t : I, ‖∑ j : Fin h,
        ZMod.stdAddChar ((j.val : ZMod q) * (x t - y))‖ ^ 2 / (h : ℝ)) /
        (Fintype.card I : ℝ) := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hI : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hraw := second_moment_lower Finset.univ Finset.univ
    (fun t : I => fun j : Fin h => ZMod.stdAddChar ((j.val : ZMod q) * (x t - y)))
    ((Fintype.card I : ℝ) * ε)
    (fun _ _ _ _ => by simp)
    (fun j _ k _ hjk => packet_correlation_bound x y _ hfourier j k hjk)
  simp only [Finset.card_univ, Fintype.card_fin] at hraw
  rw [← Finset.sum_div]
  apply (le_div_iff₀ hI).2
  apply (le_div_iff₀ hhR).2
  calc
    _ = (Fintype.card I : ℝ) * h -
        (h : ℝ) * ((h : ℝ) - 1) * ((Fintype.card I : ℝ) * ε) := by ring
    _ ≤ _ := hraw

theorem packet_eq_kernel {q h : ℕ} [NeZero q] (x : ZMod q) :
    ‖∑ j : Fin h, ZMod.stdAddChar ((j.val : ZMod q) * x)‖ ^ 2 / (h : ℝ) =
      GeometricKernel.kernel h (ZMod.stdAddChar x) := by
  unfold GeometricKernel.kernel
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => ZMod.stdAddChar ((j : ZMod q) * x)) h,
    GeometricKernel.cyclic_geometric_sum_eq]

/-- Low-frequency cancellation implies the expected lower mass at every
center of the named Fejér kernel. -/
theorem fejer_sample_mean_lower {q h : ℕ} [NeZero q] {I : Type*}
    [Fintype I] [Nonempty I] (hh : 0 < h)
    (x : I → ZMod q) (y : ZMod q) (ε : ℝ)
    (hfourier : ∀ l : ℕ, 1 ≤ l → l < h →
      ‖∑ t : I, ZMod.stdAddChar ((l : ZMod q) * x t)‖ ≤
        (Fintype.card I : ℝ) * ε) :
    1 - ((h : ℝ) - 1) * ε ≤
      (∑ t : I, GeometricKernel.kernel h (ZMod.stdAddChar (x t - y))) /
        (Fintype.card I : ℝ) := by
  simpa only [packet_eq_kernel] using raw_packet_mean_lower hh x y ε hfourier

end Problem337.FejerSampleMean

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_GeometricCharacterBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

/-- Geometric cancellation on the complex unit circle. -/
theorem norm_geometric_sum_le_two_div {z : ℂ} (hz : ‖z‖ = 1) (hne : z ≠ 1)
    (N : ℕ) : ‖∑ j ∈ Finset.range N, z ^ j‖ ≤ 2 / ‖z - 1‖ := by
  rw [geom_sum_eq hne, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [norm_pow, hz]

/-- The chord distance for a phase of period one. -/
theorem norm_exp_phase_sub_one (x : ℝ) :
    ‖Complex.exp (Complex.I * (2 * Real.pi * x : ℝ)) - 1‖ =
      2 * |Real.sin (Real.pi * x)| := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  have heq : 2 * Real.pi * x / 2 = Real.pi * x := by ring
  rw [heq, Real.norm_eq_abs, abs_mul]
  norm_num

/-- Geometric cancellation expressed directly in terms of the phase sine. -/
theorem norm_geometric_phase_sum_le {x : ℝ} (hx : Real.sin (Real.pi * x) ≠ 0)
    (N : ℕ) :
    ‖∑ j ∈ Finset.range N, (Complex.exp (Complex.I * (2 * Real.pi * x : ℝ))) ^ j‖ ≤
      1 / |Real.sin (Real.pi * x)| := by
  have habs : 0 < |Real.sin (Real.pi * x)| := abs_pos.2 hx
  have hne : Complex.exp (Complex.I * (2 * Real.pi * x : ℝ)) ≠ 1 := by
    intro h
    have hn := norm_exp_phase_sub_one x
    rw [h, sub_self, norm_zero] at hn
    linarith
  have hbound := norm_geometric_sum_le_two_div
    (Complex.norm_exp_I_mul_ofReal (2 * Real.pi * x)) hne N
  rw [norm_exp_phase_sub_one] at hbound
  convert hbound using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

/-- Uniform lower bound for the sine away from both ends of a period. -/
theorem sin_pi_mul_lower_on_middle {δ x : ℝ} (hδ : 0 < δ)
    (hleft : δ ≤ x) (hright : x ≤ 1 - δ) :
    2 * δ ≤ Real.sin (Real.pi * x) := by
  have hx0 : 0 ≤ x := le_trans hδ.le hleft
  have hx1 : 0 ≤ 1 - x := by linarith
  by_cases hx : x ≤ 1 / 2
  · have hs := Real.mul_le_sin (x := Real.pi * x)
      (mul_nonneg Real.pi_pos.le hx0) (by nlinarith [Real.pi_pos])
    have heq : 2 / Real.pi * (Real.pi * x) = 2 * x := by field_simp
    rw [heq] at hs
    linarith
  · have hs := Real.mul_le_sin (x := Real.pi * (1 - x))
      (mul_nonneg Real.pi_pos.le hx1)
      (by nlinarith [Real.pi_pos])
    have heq : 2 / Real.pi * (Real.pi * (1 - x)) = 2 * (1 - x) := by field_simp
    rw [heq, show Real.pi * (1 - x) = Real.pi - Real.pi * x by ring,
      Real.sin_pi_sub] at hs
    linarith

/-- A phase at distance at least `δ` from the ends gives a uniform kernel bound. -/
theorem norm_geometric_phase_sum_le_middle {δ x : ℝ} (hδ : 0 < δ)
    (hleft : δ ≤ x) (hright : x ≤ 1 - δ) (N : ℕ) :
    ‖∑ j ∈ Finset.range N, (Complex.exp (Complex.I * (2 * Real.pi * x : ℝ))) ^ j‖ ≤
      1 / (2 * δ) := by
  have hs := sin_pi_mul_lower_on_middle hδ hleft hright
  have hspos : 0 < Real.sin (Real.pi * x) := by linarith
  calc
    _ ≤ 1 / |Real.sin (Real.pi * x)| := norm_geometric_phase_sum_le hspos.ne' N
    _ = 1 / Real.sin (Real.pi * x) := by rw [abs_of_pos hspos]
    _ ≤ 1 / (2 * δ) := one_div_le_one_div_of_le (by positivity) hs

/-- Fejer leakage at phase distance at least `δ` from zero modulo one. -/
theorem geometric_phase_fejer_le_middle {δ x : ℝ} (hδ : 0 < δ)
    (hleft : δ ≤ x) (hright : x ≤ 1 - δ) {N : ℕ} (hN : 0 < N) :
    ‖∑ j ∈ Finset.range N, (Complex.exp (Complex.I * (2 * Real.pi * x : ℝ))) ^ j‖ ^ 2 /
      (N : ℝ) ≤ 1 / (4 * (N : ℝ) * δ ^ 2) := by
  have hs := norm_geometric_phase_sum_le_middle hδ hleft hright N
  have hs2 := pow_le_pow_left₀ (norm_nonneg _) hs 2
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    _ ≤ (1 / (2 * δ)) ^ 2 / (N : ℝ) := div_le_div_of_nonneg_right hs2 hNR.le
    _ = 1 / (4 * (N : ℝ) * δ ^ 2) := by field_simp; ring

/-- The standard cyclic character is the period-one phase at its normalized value. -/
theorem stdAddChar_eq_normalized_phase {p : ℕ} [NeZero p] (a : ZMod p) :
    ZMod.stdAddChar a =
      Complex.exp (Complex.I * (2 * Real.pi * ((a.val : ℝ) / (p : ℝ)) : ℝ)) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  congr 1
  push_cast
  ring

/-- Squared cyclic kernel leakage, normalized to have total mass one. -/
theorem stdAddChar_fejer_le_middle {p : ℕ} [NeZero p] (a : ZMod p)
    {δ : ℝ} (hδ : 0 < δ) (hleft : δ ≤ (a.val : ℝ) / p)
    (hright : (a.val : ℝ) / p ≤ 1 - δ) {N : ℕ} (hN : 0 < N) :
    ‖∑ j ∈ Finset.range N, ZMod.stdAddChar ((j : ZMod p) * a)‖ ^ 2 / (N : ℝ) ≤
      1 / (4 * (N : ℝ) * δ ^ 2) := by
  have hpow : ∀ j : ℕ, ZMod.stdAddChar ((j : ZMod p) * a) = (ZMod.stdAddChar a) ^ j := by
    intro j
    simpa only [nsmul_eq_mul] using ZMod.stdAddChar.map_nsmul_eq_pow j a
  simp_rw [hpow, stdAddChar_eq_normalized_phase]
  exact geometric_phase_fejer_le_middle hδ hleft hright hN

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CyclicDiscrepancy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.CyclicSmoothing

/-- The geometric and counting part of cyclic discrepancy. The sampled
spectral-mean input is separated from the exact kernel normalization. -/
theorem initial_interval_count_of_kernel_mean {q h d : ℕ} [NeZero q]
    {Ω : Type*} (samples : Finset Ω) (x : Ω → ZMod q) (ε : ℝ)
    (hh : 0 < h) (hhq : h ≤ q) (hd : 0 < d) (hdq : 7 * d < q)
    (hmean : ∀ y : ZMod q,
      (samples.card : ℝ) * (1 - ((h : ℝ) - 1) * ε) ≤
        ∑ ω ∈ samples, GeometricKernel.kernel h (ZMod.stdAddChar (x ω - y))) :
    (samples.card : ℝ) *
      (((6 * d + 1 : ℕ) : ℝ) / q -
        (((6 * d + 1 : ℕ) : ℝ) / q) * ((h : ℝ) - 1) * ε -
        (((6 * d + 1 : ℕ) : ℝ) / q) / (4 * (h : ℝ) * ((d : ℝ) / q)^2)) ≤
      ((samples.filter (fun ω => (x ω).val < 8 * d)).card : ℝ) := by
  classical
  let inner : Finset (ZMod q) := Finset.univ.filter (fun y => d ≤ y.val ∧ y.val ≤ 7 * d)
  let outer : Finset (ZMod q) := Finset.univ.filter (fun z => z.val < 8 * d)
  let A : ℝ := (inner.card : ℝ) / q
  let η : ℝ := (1 / (4 * (h : ℝ) * ((d : ℝ) / q)^2)) / q
  have hqR : (0 : ℝ) < q := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q))
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hβ : 0 < (d : ℝ) / q := div_pos hdR hqR
  have hcard : inner.card = 6 * d + 1 := by
    change (Finset.univ.filter (fun y : ZMod q => d ≤ y.val ∧ y.val ≤ 7 * d)).card = _
    rw [cyclic_interval_card d (7 * d) hdq]
    omega
  have htail : ∀ z : ZMod q, z ∉ outer → ∀ y ∈ inner,
      normalizedKernel h (z - y) ≤ η := by
    intro z hz y hy
    have hz' : 8 * d ≤ z.val := by simpa [outer] using hz
    have hy' : d ≤ y.val ∧ y.val ≤ 7 * d := by simpa [inner] using hy
    obtain ⟨hleft, hright⟩ := cyclic_initial_interval_phase_margin z y d (7 * d)
      (by omega) hy'
    have hb := stdAddChar_fejer_le_middle (z - y) hβ hleft hright hh
    rw [GeometricKernel.cyclic_geometric_sum_eq] at hb
    exact div_le_div_of_nonneg_right hb hqR.le
  have hsampled : (samples.card : ℝ) *
      ((inner.card : ℝ) / Fintype.card (ZMod q) - A * ((h : ℝ) - 1) * ε) ≤
      ∑ ω ∈ samples, window (normalizedKernel h) inner (x ω) := by
    have hsum := Finset.sum_le_sum (fun y (_ : y ∈ inner) => hmean y)
    have hdiv := div_le_div_of_nonneg_right hsum hqR.le
    simp only [Finset.sum_const, nsmul_eq_mul] at hdiv
    have hright : (∑ y ∈ inner, ∑ ω ∈ samples,
        GeometricKernel.kernel h (ZMod.stdAddChar (x ω - y))) / (q : ℝ) =
        ∑ ω ∈ samples, window (normalizedKernel h) inner (x ω) := by
      rw [Finset.sum_comm, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro ω hω
      simp only [window, normalizedKernel, Finset.sum_div]
    rw [hright] at hdiv
    convert hdiv using 1
    all_goals try with_reducible_and_instances rfl
    simp only [ZMod.card, A]
    ring
  have hcount := count_window_lower (normalizedKernel h) inner outer samples x
    (A * ((h : ℝ) - 1) * ε) η (normalizedKernel_nonneg h)
    (sum_normalizedKernel hh hhq) (by dsimp [η]; positivity) htail hsampled
  have hfilter : samples.filter (fun ω => x ω ∈ outer) =
      samples.filter (fun ω => (x ω).val < 8 * d) := by simp [outer]
  rw [hfilter] at hcount
  convert hcount using 1
  all_goals try with_reducible_and_instances rfl
  simp only [ZMod.card, A, η, hcard]
  ring

/-- With the explicit low-degree choice, the smoothing errors leave half of
the desired interval mass. This lemma isolates the sampled kernel mean. -/
theorem cyclic_small_interval_of_kernel_mean {q : ℕ} [NeZero q]
    {Ω : Type*} (samples : Finset Ω) (x : Ω → ZMod q) (δ : ℝ)
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / 65536) (hscale : 128 ≤ δ * q)
    (hdegree : ⌊1 / (64 * δ ^ 3)⌋₊ ≤ q)
    (hmean : ∀ y : ZMod q,
      (samples.card : ℝ) * (1 - ((⌊1 / (64 * δ ^ 3)⌋₊ : ℝ) - 1) * δ ^ 3) ≤
        ∑ ω ∈ samples, GeometricKernel.kernel ⌊1 / (64 * δ ^ 3)⌋₊
          (ZMod.stdAddChar (x ω - y))) :
    (δ / 2) * (samples.card : ℝ) ≤
      ((samples.filter (fun ω => ((x ω).val : ℝ) < δ * q)).card : ℝ) := by
  classical
  let h : ℕ := ⌊1 / (64 * δ ^ 3)⌋₊
  let d : ℕ := ⌊δ * q / 8⌋₊
  obtain ⟨hd1, hdq, hdouter, hdmargin, hinnerLo, hinnerHi⟩ :=
    cyclic_interval_floor_budget δ q hδ (by linarith) hscale
  obtain ⟨hh1, hhLo, hhHi, hleak, herror⟩ := fejer_degree_floor_budget δ hδ hsmall
  change 1 ≤ h at hh1
  change 1 ≤ d at hd1
  have hh : 0 < h := by omega
  have hd : 0 < d := by omega
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hhR1 : (1 : ℝ) ≤ h := by exact_mod_cast hh1
  have hqR : (0 : ℝ) < q := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q))
  let A : ℝ := ((6 * d + 1 : ℕ) : ℝ) / q
  let β : ℝ := (d : ℝ) / q
  have hβ : 0 < β := by dsimp [β]; positivity
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hAhi : A ≤ δ := hinnerHi
  have hAlo : 11 * δ / 16 ≤ A := hinnerLo
  have hβlo : δ / 16 ≤ β := hdmargin
  have hE : A * ((h : ℝ) - 1) * δ ^ 3 ≤ δ / 32 := by
    calc
      A * ((h : ℝ) - 1) * δ ^ 3 ≤ δ * (h : ℝ) * δ ^ 3 := by gcongr; linarith
      _ ≤ 2 * (h : ℝ) * δ * δ ^ 3 := by
        nlinarith [mul_nonneg (mul_nonneg hδ.le hhR.le) (show 0 ≤ δ ^ 3 by positivity)]
      _ ≤ δ / 32 := herror
  have hL : A / (4 * (h : ℝ) * β ^ 2) ≤ δ / 8 := by
    calc
      A / (4 * (h : ℝ) * β ^ 2) ≤ δ / (4 * (h : ℝ) * β ^ 2) := by
        exact div_le_div_of_nonneg_right hAhi (by positivity)
      _ ≤ δ / (4 * (h : ℝ) * (δ / 16) ^ 2) := by
        apply div_le_div_of_nonneg_left hδ.le (by positivity)
        gcongr
      _ = 64 / ((h : ℝ) * δ) := by field_simp; ring
      _ ≤ δ / 8 := hleak
  have hbudget : δ / 2 ≤ A - A * ((h : ℝ) - 1) * δ ^ 3 -
      A / (4 * (h : ℝ) * β ^ 2) :=
    fejer_localization_budget δ _ A _ _ hδ.le hAlo hE hL le_rfl
  have hcount := initial_interval_count_of_kernel_mean samples x (δ ^ 3)
    hh hdegree hd hdq hmean
  have hsubset : samples.filter (fun ω => (x ω).val < 8 * d) ⊆
      samples.filter (fun ω => ((x ω).val : ℝ) < δ * q) := by
    intro ω hω
    obtain ⟨hω, hval⟩ := Finset.mem_filter.mp hω
    refine Finset.mem_filter.mpr ⟨hω, ?_⟩
    have hv : ((x ω).val : ℝ) < (8 * d : ℕ) := by exact_mod_cast hval
    exact hv.trans_le hdouter
  calc
    (δ / 2) * (samples.card : ℝ) ≤ (samples.card : ℝ) *
        (A - A * ((h : ℝ) - 1) * δ ^ 3 - A / (4 * (h : ℝ) * β ^ 2)) := by
      simpa only [mul_comm (δ / 2)] using
        mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg samples.card)
    _ ≤ ((samples.filter (fun ω => (x ω).val < 8 * d)).card : ℝ) := hcount
    _ ≤ ((samples.filter (fun ω => ((x ω).val : ℝ) < δ * q)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset

/-- Genuine finite cyclic low-frequency discrepancy, with no sampled-kernel
hypothesis remaining. Repeated samples are allowed. -/
theorem cyclic_small_interval_of_fourier {q : ℕ} [NeZero q]
    {Ω : Type*} [Fintype Ω] (x : Ω → ZMod q) (δ : ℝ)
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / 65536) (hscale : 128 ≤ δ * q)
    (hdegree : ⌊1 / (64 * δ ^ 3)⌋₊ ≤ q)
    (hfourier : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊1 / δ ^ 4⌋₊ →
      ‖∑ ω : Ω, ZMod.stdAddChar ((l : ZMod q) * x ω)‖ ≤
        (Fintype.card Ω : ℝ) * δ ^ 3) :
    (δ / 2) * (Fintype.card Ω : ℝ) ≤
      ((Finset.univ.filter (fun ω => ((x ω).val : ℝ) < δ * q)).card : ℝ) := by
  classical
  cases isEmpty_or_nonempty Ω with
  | inl h =>
    let := h
    simp
  | inr h =>
    let := h
    have hN : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
    have hh : 0 < ⌊1 / (64 * δ ^ 3)⌋₊ := by
      have hb := (fejer_degree_floor_budget δ hδ hsmall).1
      omega
    have hfreq := fejer_degree_frequency_bound δ hδ hsmall
    apply cyclic_small_interval_of_kernel_mean Finset.univ x δ hδ hsmall hscale hdegree
    intro y
    have hm := FejerSampleMean.fejer_sample_mean_lower hh x y (δ ^ 3)
      (fun l hl hlh => hfourier l hl (by omega))
    have hm' := (le_div_iff₀ hN).mp hm
    simpa only [Finset.card_univ, mul_comm] using hm'

end Problem337.CyclicSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_FourierFrequencyGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- Nontrivial cancellation at all prescribed low frequencies forces the
modulus itself to lie beyond that range. -/
theorem modulus_gt_low_frequency_range {q : ℕ} [NeZero q]
    {ι : Type*} (I : Finset ι) (hI : I.Nonempty) (x : ι → ZMod q)
    (H : ℕ) (ε : ℝ) (hε : ε < 1)
    (hfourier : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ H →
      ‖(∑ i ∈ I, ZMod.stdAddChar ((ℓ : ZMod q) * x i)) / (I.card : ℂ)‖ ≤ ε) :
    H < q := by
  by_contra h
  have hqH : q ≤ H := by omega
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have h := hfourier q hq1 hqH
  have hcard : I.card ≠ 0 := ne_of_gt (Finset.card_pos.mpr hI)
  have hcardC : (I.card : ℂ) ≠ 0 := by exact_mod_cast hcard
  simp only [ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one,
    Finset.sum_const, nsmul_eq_mul, mul_one, div_self hcardC, norm_one] at h
  linarith

/-- The frequency range needed for localization also guarantees that the
cyclic interval contains many integer representatives. -/
theorem low_frequency_gap_scale (δ : ℝ) (q : ℕ)
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / 65536)
    (hgap : ⌊1 / δ ^ 4⌋₊ < q) : 128 ≤ δ * q := by
  have hq : 1 / δ ^ 4 < (q : ℝ) := (Nat.floor_lt (by positivity)).mp hgap
  have hδ8 : δ ≤ (1 / 8 : ℝ) := by linarith
  have hcube : δ ^ 3 ≤ (1 / 8 : ℝ) ^ 3 := by gcongr
  have hbound : (128 : ℝ) ≤ δ * (1 / δ ^ 4) := by
    have heq : δ * (1 / δ ^ 4) = 1 / δ ^ 3 := by
      field_simp
    rw [heq]
    apply (le_div_iff₀ (by positivity : 0 < δ ^ 3)).mpr
    norm_num at hcube
    linarith
  exact hbound.trans (mul_le_mul_of_nonneg_left hq.le hδ.le)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CyclicDiscrepancyAutomatic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.CyclicSmoothing

/-- Low-frequency cancellation itself supplies both numerical modulus
conditions needed for the cyclic localization argument. -/
theorem cyclic_small_interval_of_fourier_automatic {q : ℕ} [NeZero q]
    {Ω : Type*} [Fintype Ω] (x : Ω → ZMod q) (δ : ℝ)
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / 65536)
    (hfourier : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊1 / δ ^ 4⌋₊ →
      ‖∑ ω : Ω, ZMod.stdAddChar ((l : ZMod q) * x ω)‖ ≤
        (Fintype.card Ω : ℝ) * δ ^ 3) :
    (δ / 2) * (Fintype.card Ω : ℝ) ≤
      ((Finset.univ.filter (fun ω => ((x ω).val : ℝ) < δ * q)).card : ℝ) := by
  classical
  cases isEmpty_or_nonempty Ω with
  | inl h =>
    let := h
    simp
  | inr h =>
    let := h
    have hN : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
    have hε : δ ^ 3 < 1 := by
      have hδ1 : δ < 1 := by linarith
      exact pow_lt_one₀ hδ.le hδ1 (by decide)
    have hgap : ⌊1 / δ ^ 4⌋₊ < q :=
      modulus_gt_low_frequency_range Finset.univ Finset.univ_nonempty x _ _ hε
        (fun l hl hH => by
          simp only [Finset.card_univ, norm_div, Complex.norm_natCast]
          exact (div_le_iff₀ hN).mpr (by simpa [mul_comm] using hfourier l hl hH))
    have hscale := low_frequency_gap_scale δ q hδ hsmall hgap
    have hdegree : ⌊1 / (64 * δ ^ 3)⌋₊ ≤ q :=
      (fejer_degree_frequency_bound δ hδ hsmall).trans (Nat.le_of_lt hgap)
    exact cyclic_small_interval_of_fourier x δ hδ hsmall hscale hdegree hfourier

end Problem337.CyclicSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_LeastResidueBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- The integer remainder in the ceiling descent is exactly the canonical
representative of the negative residue, including remainder zero. -/
theorem least_remainder_eq_neg_cast_val {u A z : ℕ} [NeZero u]
    (hlo : A ≤ u * z) (hhi : u * z < A + u) :
    u * z - A = (-(A : ZMod u)).val := by
  have hr : u * z - A < u := by omega
  have hc : ((u * z - A : ℕ) : ZMod u) = -(A : ZMod u) := by
    rw [Nat.cast_sub hlo, Nat.cast_mul]
    simp
  have hv := congrArg ZMod.val hc
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hr] using hv

/-- Natural rational ceiling supplies the exact least-residue integer. -/
theorem ceiling_remainder_eq_neg_cast_val {u A : ℕ} [NeZero u] :
    u * ⌈(A : ℚ) / (u : ℚ)⌉₊ - A = (-(A : ZMod u)).val := by
  have hu : (0 : ℚ) < u := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne u)
  let z : ℕ := ⌈(A : ℚ) / (u : ℚ)⌉₊
  have hloQ : (A : ℚ) ≤ (u : ℚ) * z := by
    have h := (div_le_iff₀ hu).mp (Nat.le_ceil ((A : ℚ) / (u : ℚ)))
    simpa only [mul_comm] using h
  have hhiQ : (u : ℚ) * z < (A : ℚ) + u := by
    have h := mul_lt_mul_of_pos_right
      (Nat.ceil_lt_add_one (by positivity : (0 : ℚ) ≤ (A : ℚ) / (u : ℚ))) hu
    dsimp [z]
    rw [add_mul, div_mul_cancel₀ _ hu.ne', one_mul] at h
    simpa only [mul_comm] using h
  exact least_remainder_eq_neg_cast_val (by exact_mod_cast hloQ) (by exact_mod_cast hhiQ)

/-- Standard additive characters at natural residues are the usual
exponential phases without choosing a representative. -/
theorem stdAddChar_nat_phase {u : ℕ} [NeZero u] (A : ℕ) :
    ZMod.stdAddChar (A : ZMod u) =
      Complex.exp (2 * Real.pi * Complex.I * (A : ℂ) / (u : ℂ)) := by
  simpa only [Int.cast_natCast] using (ZMod.stdAddChar_coe (N := u) (A : ℤ))

/-- In particular, the positive Fourier coefficient for natural products is
exactly the exponential sum in the residue estimates. -/
theorem stdAddChar_nat_product_phase {u : ℕ} [NeZero u] (l A : ℕ) :
    ZMod.stdAddChar ((l : ZMod u) * (A : ZMod u)) =
      Complex.exp (2 * Real.pi * Complex.I * (l * A : ℕ) / (u : ℂ)) := by
  rw [← Nat.cast_mul, stdAddChar_nat_phase]

/-- Passing from positive exponential phases to the negative least-residue
phases preserves every Fourier coefficient norm. -/
theorem norm_neg_residue_fourier_eq {u : ℕ} [NeZero u]
    {I : Type*} [Fintype I] (A : I → ℕ) (l : ℕ) :
    ‖∑ t : I, ZMod.stdAddChar ((l : ZMod u) * (-(A t : ZMod u)))‖ =
      ‖∑ t : I, Complex.exp
        (2 * Real.pi * Complex.I * (l * A t : ℕ) / (u : ℂ))‖ := by
  simp_rw [mul_neg, AddChar.map_neg_eq_conj]
  rw [← map_sum (starRingEnd ℂ)
    (fun t : I => ZMod.stdAddChar ((l : ZMod u) * (A t : ZMod u))) Finset.univ]
  rw [Complex.norm_conj]
  simp_rw [stdAddChar_nat_product_phase]

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CyclicCeilingCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- Cancellation forces its own modulus-size conditions, so the direct
ceiling-remainder count has no separate scale or degree hypothesis. -/
theorem ceiling_remainder_count_of_character_expect_automatic {u : ℕ} [NeZero u]
    {Ω : Type*} [Fintype Ω] (A : Ω → ℕ) (δ : ℝ)
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / 65536)
    (hfourier : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊1 / δ ^ 4⌋₊ →
      ‖𝔼 ω : Ω, ZMod.stdAddChar ((l : ZMod u) * (A ω : ZMod u))‖ ≤ δ ^ 3) :
    (δ / 2) * (Fintype.card Ω : ℝ) ≤
      ((Finset.univ.filter (fun ω =>
        ((u * ⌈(A ω : ℚ) / (u : ℚ)⌉₊ - A ω : ℕ) : ℝ) < δ * u)).card : ℝ) := by
  classical
  cases isEmpty_or_nonempty Ω with
  | inl h =>
    let := h
    simp
  | inr h =>
    let := h
    have hN : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
    have hc := CyclicSmoothing.cyclic_small_interval_of_fourier_automatic
      (fun ω => -(A ω : ZMod u)) δ hδ hsmall
      (fun l hl hld => by
        rw [norm_neg_residue_fourier_eq]
        have hf := hfourier l hl hld
        simp only [Fintype.expect_eq_sum_div_card, stdAddChar_nat_product_phase,
          norm_div, Complex.norm_natCast] at hf
        simpa only [mul_comm] using (div_le_iff₀ hN).mp hf)
    simpa only [ceiling_remainder_eq_neg_cast_val] using hc

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_FiniteExposureAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- Uniform averaging over labelled samples factors over any partition of the labels. -/
theorem expect_pi_partition {ι A M : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]
    [AddCommMonoid M] [Module ℚ≥0 M] (p : ι → Prop) [DecidablePred p]
    (F : (ι → A) → M) :
    (𝔼 f : ι → A, F f) =
      𝔼 a : {i // p i} → A, 𝔼 b : {i // ¬p i} → A,
        F (fun i => if h : p i then a ⟨i,h⟩ else b ⟨i,h⟩) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd p (fun _ => A)
  calc
    (𝔼 f : ι → A, F f) = 𝔼 ab, F (e.symm ab) :=
      Fintype.expect_equiv e F (fun ab => F (e.symm ab)) (fun f => by simp)
    _ = _ := by
      simpa [e, Equiv.piEquivPiSubtypeProd] using
        Finset.expect_product Finset.univ Finset.univ (fun ab => F (e.symm ab))

/-- Average over a finite probability space of an indicator is its relative cardinality. -/
lemma expect_finset_indicator {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (B : Finset Ω) :
    (𝔼 x : Ω, if x ∈ B then (1 : ℝ) else 0) =
      (B.card : ℝ) / Fintype.card Ω := by
  classical
  rw [Fintype.expect_eq_sum_div_card]
  congr 1
  simp

/-- Exposing some variables costs only the proportion of exceptional exposures.
The inner finite type can itself be a product of independent fresh sample blocks. -/
theorem conditional_average_norm_bound {Ω A : Type*} [Fintype Ω] [Fintype A]
    [Nonempty Ω] [Nonempty A] (F : Ω → A → ℂ) (B : Finset Ω) (δ : ℝ)
    (hδ : 0 ≤ δ) (hunit : ∀ ω a, ‖F ω a‖ ≤ 1)
    (hgood : ∀ ω, ω ∉ B → ‖𝔼 a : A, F ω a‖ ≤ δ) :
    ‖𝔼 ω : Ω, 𝔼 a : A, F ω a‖ ≤ (B.card : ℝ) / Fintype.card Ω + δ := by
  classical
  have hbound (ω : Ω) : ‖𝔼 a : A, F ω a‖ ≤ 1 := by
    calc
      _ ≤ 𝔼 a : A, ‖F ω a‖ := RCLike.norm_expect_le (K := ℂ)
      _ ≤ 𝔼 _a : A, (1 : ℝ) := Finset.expect_le_expect (fun a _ => hunit ω a)
      _ = 1 := Fintype.expect_const 1
  calc
    _ ≤ 𝔼 ω : Ω, ‖𝔼 a : A, F ω a‖ := RCLike.norm_expect_le (K := ℂ)
    _ ≤ 𝔼 ω : Ω, ((if ω ∈ B then (1 : ℝ) else 0) + δ) := by
      apply Finset.expect_le_expect
      intro ω hω
      by_cases hb : ω ∈ B
      · simp only [ite_eq_left hb]
        linarith [hbound ω]
      · simpa only [ite_eq_right hb, zero_add] using hgood ω hb
    _ = _ := by
      rw [Finset.expect_add_distrib, expect_finset_indicator, Fintype.expect_const]

/-- A finite reindexing into exposed and fresh coordinates gives exact Fubini averaging. -/
theorem expect_equiv_prod {Ω E A M : Type*} [Fintype Ω] [Fintype E] [Fintype A]
    [AddCommMonoid M] [Module ℚ≥0 M] (e : Ω ≃ E × A) (F : Ω → M) :
    (𝔼 ω : Ω, F ω) = 𝔼 x : E, 𝔼 a : A, F (e.symm (x,a)) := by
  calc
    (𝔼 ω : Ω, F ω) = 𝔼 xa, F (e.symm xa) :=
      Fintype.expect_equiv e F (fun xa => F (e.symm xa)) (fun ω => by simp)
    _ = _ := by
      simpa using Finset.expect_product Finset.univ Finset.univ (fun xa => F (e.symm xa))

/-- The conditional estimate transported back to the original labelled sample space. -/
theorem exposure_average_norm_bound {Ω E A : Type*}
    [Fintype Ω] [Fintype E] [Fintype A] [Nonempty E] [Nonempty A]
    (e : Ω ≃ E × A) (F : Ω → ℂ) (B : Finset E) (δ : ℝ)
    (hδ : 0 ≤ δ) (hunit : ∀ ω, ‖F ω‖ ≤ 1)
    (hgood : ∀ x, x ∉ B → ‖𝔼 a : A, F (e.symm (x,a))‖ ≤ δ) :
    ‖𝔼 ω : Ω, F ω‖ ≤ (B.card : ℝ) / Fintype.card E + δ := by
  rw [expect_equiv_prod e F]
  exact conditional_average_norm_bound (fun x a => F (e.symm (x,a))) B δ hδ
    (fun x a => hunit _) hgood

/-- Uniform samples on coordinates not inspected by the function can be discarded. -/
theorem expect_restrict_coordinates {ι A M : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype A] [Nonempty A]
    [AddCommMonoid M] [Module ℚ≥0 M] (p : ι → Prop) [DecidablePred p]
    (F : ({i // p i} → A) → M) :
    (𝔼 f : ι → A, F (fun i => f i)) = 𝔼 a : {i // p i} → A, F a := by
  rw [expect_pi_partition p]
  simp only [dite_eq_left, Subtype.property, Fintype.expect_const]

/-- Sampling any injectively selected labels gives the same uniform product law. -/
theorem expect_injective_coordinates {ι κ A M : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype A] [Nonempty A] [AddCommMonoid M] [Module ℚ≥0 M]
    (e : κ ↪ ι) (F : (κ → A) → M) :
    (𝔼 f : ι → A, F (fun k => f (e k))) = 𝔼 a : κ → A, F a := by
  classical
  let : Fintype (Set.range e) := Subtype.fintype (fun i => i ∈ Set.range e)
  let E := Equiv.ofInjective e e.injective
  have h := expect_restrict_coordinates (fun i => i ∈ Set.range e)
    (fun a => F (fun k => a (E k)))
  calc
    (𝔼 f : ι → A, F (fun k => f (e k))) =
        𝔼 a : (Set.range e) → A, F (fun k => a (E k)) := h
    _ = 𝔼 a : κ → A, F a := by
      apply Fintype.expect_equiv (Equiv.arrowCongr E.symm (Equiv.refl A))
      intro a
      rfl

/-- The normalized count of a coordinate event is unaffected by unused independent labels. -/
theorem injective_coordinate_event_fraction {ι κ A : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype A] [Nonempty A] (e : κ ↪ ι) (R : (κ → A) → Prop) [DecidablePred R] :
    ((Finset.univ.filter (fun f : ι → A => R (fun k => f (e k)))).card : ℝ) /
        Fintype.card (ι → A) =
      ((Finset.univ.filter R).card : ℝ) / Fintype.card (κ → A) := by
  simpa only [Fintype.expect_eq_sum_div_card, Finset.sum_boole] using
    expect_injective_coordinates e (fun a => if R a then (1 : ℝ) else 0)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_FiniteGoodExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.RandomProducts

/-- Reindex independent coordinates in a uniform finite product average. -/
lemma expect_product_reindex {A B X : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Fintype X] (e : A ≃ B) (g : X → ℕ) (F : ℕ → ℂ) :
    (𝔼 w : A → X, F (∏ i, g (w i))) =
      𝔼 w : B → X, F (∏ i, g (w i)) := by
  classical
  apply Fintype.expect_equiv (e.arrowCongr (Equiv.refl X))
  intro w
  congr 1
  simpa [Equiv.arrowCongr_apply, Function.comp_def] using
    (e.symm.prod_comp (fun i => g (w i))).symm

/-- Conversion of two uniform finite function averages to the explicit
normalization used in the bilinear exponential-sum estimate. -/
lemma double_expect_fin_eq_sum (P : Finset ℕ) (s : ℕ)
    (F : (Fin s → ↥P) → (Fin s → ↥P) → ℂ) :
    (𝔼 a : Fin s → ↥P, 𝔼 b : Fin s → ↥P, F a b) =
      (∑ a : Fin s → ↥P, ∑ b : Fin s → ↥P, F a b) /
        ((P.card : ℂ)^s)^2 := by
  classical
  simp_rw [Fintype.expect_eq_sum_div_card]
  rw [← Finset.sum_div, div_div]
  simp [pow_two]

/-- Reindex two independent coordinate families simultaneously. -/
lemma double_expect_product_reindex {A B C D X : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype X]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    (eA : A ≃ C) (eB : B ≃ D) (g : X → ℕ) (F : ℕ → ℕ → ℂ) :
    (𝔼 a : A → X, 𝔼 b : B → X, F (∏ i, g (a i)) (∏ i, g (b i))) =
      𝔼 a : C → X, 𝔼 b : D → X, F (∏ i, g (a i)) (∏ i, g (b i)) := by
  classical
  calc
    _ = 𝔼 a : C → X, 𝔼 b : B → X, F (∏ i, g (a i)) (∏ i, g (b i)) :=
      expect_product_reindex eA g (fun x => 𝔼 b : B → X, F x (∏ i, g (b i)))
    _ = _ := by
      apply Finset.expect_congr rfl
      intro a ha
      exact expect_product_reindex eB g (fun y => F (∏ i, g (a i)) y)

/-- The actual good-exposure bound with arbitrary finite coordinate types,
in the nested uniform-expectation form used after conditioning. -/
theorem concrete_good_exposure_expect {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (S V : ℝ) (hA : Fintype.card A = freshLength S V)
    (hB : Fintype.card B = freshLength S V)
    (hS : 2 ≤ S) (hV : 100000 * Real.log S ≤ V) (hVS : V ≤ S)
    (P : Finset ℕ) (hPprime : ∀ p ∈ P, Nat.Prime p)
    (hPcard : S ^ 99 ≤ (P.card : ℝ))
    (hPupper : ∀ p ∈ P, (p : ℝ) ≤ S ^ 101)
    (c u : ℕ) (hu : 0 < u) [NeZero u]
    (huV : (u : ℝ) ≤ Real.exp V)
    (hq : Real.exp ((9 / 10 : ℝ) * V) ≤ ((u / c.gcd u : ℕ) : ℝ))
    (t : ZMod u) :
    ‖𝔼 a : A → ↥P, 𝔼 b : B → ↥P,
      ZMod.stdAddChar
        (((c * (∏ i, (a i : ℕ)) * (∏ i, (b i : ℕ)) : ℕ) : ZMod u) - t)‖ ≤
      Real.exp (-V / 5) := by
  classical
  let F : ℕ → ℕ → ℂ := fun x y =>
    ZMod.stdAddChar (((c * x * y : ℕ) : ZMod u) - t)
  change ‖𝔼 a : A → ↥P, 𝔼 b : B → ↥P,
    F (∏ i, (a i : ℕ)) (∏ i, (b i : ℕ))‖ ≤ _
  rw [double_expect_product_reindex
    (Fintype.equivFinOfCardEq hA) (Fintype.equivFinOfCardEq hB)
    (fun p : ↥P => (p : ℕ)) F]
  rw [double_expect_fin_eq_sum]
  exact concrete_good_exposure_bound S V hS hV hVS P hPprime hPcard hPupper
    c u hu huV hq t

end Problem337.RandomProducts

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_SimultaneousSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- A finite Markov inequality with a union over frequencies. No independence
between the frequencies, or between the points, is required. -/
theorem card_exists_large_score_mul_le {α β : Type*}
    (U : Finset α) (L : Finset β) (g : α → β → ℝ) (a : ℝ)
    (hg : ∀ u ∈ U, ∀ l ∈ L, 0 ≤ g u l) :
    ((U.filter (fun u => ∃ l ∈ L, a < g u l)).card : ℝ) * a ≤
      ∑ l ∈ L, ∑ u ∈ U, g u l := by
  classical
  let bad := U.filter (fun u => ∃ l ∈ L, a < g u l)
  calc
    (bad.card : ℝ) * a = ∑ _u ∈ bad, a := by simp
    _ ≤ ∑ u ∈ bad, ∑ l ∈ L, g u l := by
      apply Finset.sum_le_sum
      intro u hu
      obtain ⟨huU, l, hl, hlarge⟩ := Finset.mem_filter.mp hu
      exact hlarge.le.trans (Finset.single_le_sum (hg u huU) hl)
    _ ≤ ∑ u ∈ U, ∑ l ∈ L, g u l := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro u hu _
      exact Finset.sum_nonneg (hg u hu)
    _ = ∑ l ∈ L, ∑ u ∈ U, g u l := Finset.sum_comm

/-- Squared complex Fourier scores are a common instance of the preceding
finite Markov/union estimate. -/
theorem card_exists_large_norm_sq_mul_le {α β : Type*}
    (U : Finset α) (L : Finset β) (f : α → β → ℂ) (a : ℝ) (ha : 0 ≤ a) :
    ((U.filter (fun u => ∃ l ∈ L, a < ‖f u l‖)).card : ℝ) * a ^ 2 ≤
      ∑ l ∈ L, ∑ u ∈ U, ‖f u l‖ ^ 2 := by
  classical
  have hfilter : U.filter (fun u => ∃ l ∈ L, a < ‖f u l‖) =
      U.filter (fun u => ∃ l ∈ L, a ^ 2 < ‖f u l‖ ^ 2) := by
    apply Finset.filter_congr
    intro u _
    apply exists_congr
    intro l
    exact and_congr_right (fun _ => by
      constructor
      · intro h
        nlinarith [norm_nonneg (f u l)]
      · intro h
        nlinarith [norm_nonneg (f u l)])
  rw [hfilter]
  apply card_exists_large_score_mul_le
  intros
  positivity

/-- The uniform second-moment version of the frequency-union bound. -/
theorem card_exists_large_norm_le_of_moments {α β : Type*}
    (U : Finset α) (L : Finset β) (f : α → β → ℂ) (a E : ℝ)
    (ha : 0 < a) (hE : ∀ l ∈ L, (∑ u ∈ U, ‖f u l‖ ^ 2) ≤ E) :
    ((U.filter (fun u => ∃ l ∈ L, a < ‖f u l‖)).card : ℝ) ≤
      (L.card : ℝ) * E / a ^ 2 := by
  classical
  apply (le_div_iff₀ (sq_pos_of_pos ha)).2
  calc
    ((U.filter (fun u => ∃ l ∈ L, a < ‖f u l‖)).card : ℝ) * a ^ 2 ≤
        ∑ l ∈ L, ∑ u ∈ U, ‖f u l‖ ^ 2 :=
      card_exists_large_norm_sq_mul_le U L f a ha.le
    _ ≤ ∑ _l ∈ L, E := Finset.sum_le_sum hE
    _ = (L.card : ℝ) * E := by simp

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_FourierFailureBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.FourierFailureBounds

/-- Frequency union and second-moment Markov bound with the exact scales used
    in the random-product construction. -/
theorem failure_fraction_le_exp {Ω L : Type*} [Fintype Ω] [Nonempty Ω]
    [DecidableEq Ω] (freq : Finset L) (phase : Ω → L → ℂ) (m w : ℝ)
    (hfreq : (freq.card : ℝ) ≤ Real.exp (4 * m / 10000))
    (hmoment : ∀ l ∈ freq, (∑ ω, ‖phase ω l‖ ^ 2) ≤
      (Fintype.card Ω : ℝ) * Real.exp (-w / 100)) :
    ((Finset.univ.filter (fun ω => ∃ l ∈ freq,
      Real.exp (-3 * m / 10000) < ‖phase ω l‖)).card : ℝ) /
      Fintype.card Ω ≤ Real.exp (m / 1000 - w / 100) := by
  classical
  have hΩ : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hΩ).2
  have hmarkov := card_exists_large_norm_le_of_moments Finset.univ freq phase
    (Real.exp (-3 * m / 10000))
    ((Fintype.card Ω : ℝ) * Real.exp (-w / 100)) (Real.exp_pos _) hmoment
  calc
    ((Finset.univ.filter (fun ω => ∃ l ∈ freq,
        Real.exp (-3 * m / 10000) < ‖phase ω l‖)).card : ℝ) ≤
        (freq.card : ℝ) * ((Fintype.card Ω : ℝ) * Real.exp (-w / 100)) /
          Real.exp (-3 * m / 10000) ^ 2 := hmarkov
    _ ≤ Real.exp (4 * m / 10000) *
        ((Fintype.card Ω : ℝ) * Real.exp (-w / 100)) /
          Real.exp (-3 * m / 10000) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right hfreq (by positivity)
    _ = Real.exp (m / 1000 - w / 100) * Fintype.card Ω := by
      have he : Real.exp (4 * m / 10000) * Real.exp (-w / 100) /
          Real.exp (-3 * m / 10000) ^ 2 = Real.exp (m / 1000 - w / 100) := by
        rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_sub]
        congr 1
        ring
      calc
        _ = (Real.exp (4 * m / 10000) * Real.exp (-w / 100) /
          Real.exp (-3 * m / 10000) ^ 2) * Fintype.card Ω := by ring
        _ = _ := by rw [he]

/-- Throughout a middle level, the logarithmic range is at least
    `(1-10⁻⁴)m`, giving the uniform single-block failure budget `exp(-m/200)`. -/
theorem middle_failure_fraction_le {Ω L : Type*} [Fintype Ω] [Nonempty Ω]
    [DecidableEq Ω] (freq : Finset L) (phase : Ω → L → ℂ) (m w : ℝ)
    (hm : 0 ≤ m) (hw : (9999 / 10000 : ℝ) * m ≤ w)
    (hfreq : (freq.card : ℝ) ≤ Real.exp (4 * m / 10000))
    (hmoment : ∀ l ∈ freq, (∑ ω, ‖phase ω l‖ ^ 2) ≤
      (Fintype.card Ω : ℝ) * Real.exp (-w / 100)) :
    ((Finset.univ.filter (fun ω => ∃ l ∈ freq,
      Real.exp (-3 * m / 10000) < ‖phase ω l‖)).card : ℝ) /
      Fintype.card Ω ≤ Real.exp (-m / 200) := by
  apply (failure_fraction_le_exp freq phase m w hfreq hmoment).trans
  apply Real.exp_le_exp.mpr
  linarith

/-- At a terminal integer the same Fourier bound gives the power-law failure
    probability amplified by the one-thousand-block selection lemma. -/
theorem terminal_failure_fraction_le {Ω L : Type*} [Fintype Ω] [Nonempty Ω]
    [DecidableEq Ω] (freq : Finset L) (phase : Ω → L → ℂ) (u : ℝ)
    (hu : 1 ≤ u)
    (hfreq : (freq.card : ℝ) ≤ Real.exp (4 * Real.log u / 10000))
    (hmoment : ∀ l ∈ freq, (∑ ω, ‖phase ω l‖ ^ 2) ≤
      (Fintype.card Ω : ℝ) * Real.exp (-Real.log u / 100)) :
    ((Finset.univ.filter (fun ω => ∃ l ∈ freq,
      Real.exp (-3 * Real.log u / 10000) < ‖phase ω l‖)).card : ℝ) /
      Fintype.card Ω ≤ u ^ (-(1 / 200 : ℝ)) := by
  apply (failure_fraction_le_exp freq phase (Real.log u) (Real.log u) hfreq hmoment).trans
  have hupos : 0 < u := by linarith
  rw [Real.rpow_def_of_pos hupos]
  apply Real.exp_le_exp.mpr
  have hlog := Real.log_nonneg hu
  linarith

end Problem337.FourierFailureBounds

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_IndependentBlockSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.IndependentBlockSelection

/-- Number of block choices in which every block belongs to one bad set. -/
theorem card_all_bad_vectors {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (B : Finset Ω) (R : ℕ) :
    (Finset.univ.filter (fun f : Fin R → Ω => ∀ i, f i ∈ B)).card = B.card ^ R := by
  classical
  calc
    (Finset.univ.filter (fun f : Fin R → Ω => ∀ i, f i ∈ B)).card =
        Fintype.card {f : Fin R → Ω // ∀ i, f i ∈ B} := by
      rw [Fintype.card_subtype]
    _ = Fintype.card (Fin R → B) :=
      Fintype.card_congr Equiv.subtypePiEquivPi
    _ = B.card ^ R := by simp

/-- Summability gives a uniform bound for every finite set beyond one cutoff. -/
theorem finite_tail_sum_lt_of_summable (f : ℕ → ℝ) (hf : Summable f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ s : Finset ℕ, (∀ u ∈ s, N ≤ u) → (∑ u ∈ s, f u) < ε := by
  obtain ⟨t, ht⟩ := hf.vanishing (Iio_mem_nhds hε)
  refine ⟨t.sup id + 1, ?_⟩
  intro s hs
  apply ht s
  apply Finset.disjoint_left.mpr
  intro u hus hut
  have hu : u ≤ t.sup id := Finset.le_sup (f := id) hut
  have hv := hs u hus
  omega

/-- The terminal error `u⁻⁵` is uniformly summable over arbitrary finite ranges. -/
theorem finite_inverse_fifth_tail_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ s : Finset ℕ, (∀ u ∈ s, N ≤ u) →
      (∑ u ∈ s, (1 : ℝ) / (u : ℝ) ^ 5) < ε := by
  apply finite_tail_sum_lt_of_summable _ _ hε
  exact Real.summable_one_div_nat_pow.mpr (by norm_num)

/-- Joint selection avoiding a global exceptional event and all local failures. -/
theorem exists_blocks_avoiding_global_bad_of_card_sum_lt
    {Ω U : Type*} [Fintype Ω] (s : Finset U) (B : U → Finset Ω)
    (R : ℕ) (E : Finset (Fin R → Ω))
    (hsmall : E.card + (∑ u ∈ s, (B u).card ^ R) < Fintype.card Ω ^ R) :
    ∃ f : Fin R → Ω, f ∉ E ∧ ∀ u ∈ s, ∃ i : Fin R, f i ∉ B u := by
  classical
  let bad : U → Finset (Fin R → Ω) := fun u =>
    Finset.univ.filter (fun f => ∀ i, f i ∈ B u)
  have hcard : (E ∪ s.biUnion bad).card <
      (Finset.univ : Finset (Fin R → Ω)).card := by
    calc
      (E ∪ s.biUnion bad).card ≤ E.card + (s.biUnion bad).card :=
        Finset.card_union_le _ _
      _ ≤ E.card + ∑ u ∈ s, (bad u).card :=
        Nat.add_le_add_left Finset.card_biUnion_le _
      _ = E.card + ∑ u ∈ s, (B u).card ^ R := by
        congr 1
        apply Finset.sum_congr rfl
        intro u hu
        exact card_all_bad_vectors (B u) R
      _ < Fintype.card Ω ^ R := hsmall
      _ = (Finset.univ : Finset (Fin R → Ω)).card := by simp
  obtain ⟨f, _, hf⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨f, fun h => hf (Finset.mem_union_left _ h), ?_⟩
  intro u hu
  by_contra h
  push Not at h
  apply hf
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_filter.mpr ⟨Finset.mem_univ f, h⟩⟩

/-- Probability budgets add even when the global event is not independent
    of any of the individual terminal events. -/
theorem exists_blocks_avoiding_global_bad_of_probability_sum_lt
    {Ω U : Type*} [Fintype Ω] [Nonempty Ω] (s : Finset U)
    (B : U → Finset Ω) (R : ℕ) (E : Finset (Fin R → Ω)) (p : U → ℝ)
    (hbad : ∀ u ∈ s, ((B u).card : ℝ) / Fintype.card Ω ≤ p u)
    (hsmall : (E.card : ℝ) / (Fintype.card Ω : ℝ) ^ R +
      (∑ u ∈ s, p u ^ R) < 1) :
    ∃ f : Fin R → Ω, f ∉ E ∧ ∀ u ∈ s, ∃ i : Fin R, f i ∉ B u := by
  apply exists_blocks_avoiding_global_bad_of_card_sum_lt s B R E
  have hΩ : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hpow : (0 : ℝ) < (Fintype.card Ω : ℝ) ^ R := pow_pos hΩ R
  have hsum : ((E.card : ℝ) + ∑ u ∈ s, ((B u).card : ℝ) ^ R) /
      (Fintype.card Ω : ℝ) ^ R < 1 := by
    calc
      ((E.card : ℝ) + ∑ u ∈ s, ((B u).card : ℝ) ^ R) /
          (Fintype.card Ω : ℝ) ^ R =
          (E.card : ℝ) / (Fintype.card Ω : ℝ) ^ R +
          ∑ u ∈ s, (((B u).card : ℝ) / Fintype.card Ω) ^ R := by
        simp only [add_div, div_pow, Finset.sum_div]
      _ ≤ (E.card : ℝ) / (Fintype.card Ω : ℝ) ^ R + ∑ u ∈ s, p u ^ R := by
        apply add_le_add (le_refl _)
        apply Finset.sum_le_sum
        intro u hu
        exact pow_le_pow_left₀ (by positivity) (hbad u hu) R
      _ < 1 := hsmall
  have hreal := (div_lt_one hpow).mp hsum
  exact_mod_cast hreal

/-- Final simultaneous-selection form: a global budget below one leaves room
    for every sufficiently far-out finite collection of terminal integers. -/
theorem exists_terminal_blocks_with_global_bad (δ : ℝ) (hδ : δ < 1) :
    ∃ N : ℕ, ∀ (Ω : Type) [Fintype Ω] [Nonempty Ω]
      (s : Finset ℕ) (B : ℕ → Finset Ω) (R : ℕ)
      (E : Finset (Fin R → Ω)) (p : ℕ → ℝ),
      (∀ u ∈ s, N ≤ u) →
      ((E.card : ℝ) / (Fintype.card Ω : ℝ) ^ R ≤ δ) →
      (∀ u ∈ s, ((B u).card : ℝ) / Fintype.card Ω ≤ p u) →
      (∀ u ∈ s, p u ^ R ≤ (1 : ℝ) / (u : ℝ) ^ 5) →
      ∃ f : Fin R → Ω, f ∉ E ∧ ∀ u ∈ s, ∃ i : Fin R, f i ∉ B u := by
  obtain ⟨N, hN⟩ := finite_inverse_fifth_tail_lt (sub_pos.mpr hδ)
  refine ⟨N, ?_⟩
  intro Ω _ _ s B R E p hs hE hbad herr
  apply exists_blocks_avoiding_global_bad_of_probability_sum_lt s B R E p hbad
  have htail := (Finset.sum_le_sum herr).trans_lt (hN s hs)
  linarith

/-- One thousand blocks turn `u^(-.005)`
    into the summable error `u^(-5)`. -/
theorem thousand_blocks_rpow (u : ℕ) :
    ((u : ℝ) ^ (-(1 / 200 : ℝ))) ^ 1000 = (1 : ℝ) / (u : ℝ) ^ 5 := by
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg u)]
  norm_num

/-- Explicit 1000-block form of simultaneous terminal selection. -/
theorem exists_thousand_terminal_blocks_with_global_bad (δ : ℝ) (hδ : δ < 1) :
    ∃ N : ℕ, ∀ (Ω : Type) [Fintype Ω] [Nonempty Ω]
      (s : Finset ℕ) (B : ℕ → Finset Ω) (E : Finset (Fin 1000 → Ω)),
      (∀ u ∈ s, N ≤ u) →
      ((E.card : ℝ) / (Fintype.card Ω : ℝ) ^ 1000 ≤ δ) →
      (∀ u ∈ s, ((B u).card : ℝ) / Fintype.card Ω ≤
        (u : ℝ) ^ (-(1 / 200 : ℝ))) →
      ∃ f : Fin 1000 → Ω, f ∉ E ∧ ∀ u ∈ s, ∃ i : Fin 1000, f i ∉ B u := by
  obtain ⟨N, hN⟩ := exists_terminal_blocks_with_global_bad δ hδ
  refine ⟨N, ?_⟩
  intro Ω _ _ s B E hs hE hbad
  exact hN Ω s B 1000 E (fun u => (u : ℝ) ^ (-(1 / 200 : ℝ)))
    hs hE hbad (fun u _ => (thousand_blocks_rpow u).le)

/-- Restricting the first block has exactly its single-block failure fraction. -/
theorem card_bad_first_block {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (B : Finset Ω) (R : ℕ) :
    (Finset.univ.filter (fun f : Fin (R + 1) → Ω => f 0 ∈ B)).card =
      B.card * Fintype.card Ω ^ R := by
  classical
  let e : {f : Fin (R + 1) → Ω // f 0 ∈ B} ≃ B × (Fin R → Ω) :=
    { toFun := fun f => (⟨f.1 0, f.2⟩, Fin.tail f.1)
      invFun := fun p => ⟨Fin.cons p.1.1 p.2, p.1.2⟩
      left_inv := by
        intro f
        apply Subtype.ext
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      right_inv := by
        intro p
        rcases p with ⟨b, f⟩
        rfl }
  calc
    (Finset.univ.filter (fun f : Fin (R + 1) → Ω => f 0 ∈ B)).card =
        Fintype.card {f : Fin (R + 1) → Ω // f 0 ∈ B} := by
      rw [Fintype.card_subtype]
    _ = Fintype.card (B × (Fin R → Ω)) := Fintype.card_congr e
    _ = B.card * Fintype.card Ω ^ R := by simp

/-- Normalized first-block bad count, for combining a middle-level event
    on block zero with terminal success on at least one of all blocks. -/
theorem bad_first_block_fraction {Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    (B : Finset Ω) (R : ℕ) :
    ((Finset.univ.filter (fun f : Fin (R + 1) → Ω => f 0 ∈ B)).card : ℝ) /
        (Fintype.card Ω : ℝ) ^ (R + 1) = (B.card : ℝ) / Fintype.card Ω := by
  rw [card_bad_first_block]
  have hΩ : (Fintype.card Ω : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := Ω))
  push_cast
  rw [pow_succ]
  field_simp

/-- A realization with a good middle-level block and a successful block for
    every terminal integer, matching the final simultaneous selection step. -/
theorem exists_middle_and_terminal_blocks (δ : ℝ) (hδ : δ < 1) :
    ∃ N : ℕ, ∀ (Ω : Type) [Fintype Ω] [Nonempty Ω]
      (s : Finset ℕ) (B : ℕ → Finset Ω) (middleBad : Finset Ω),
      (∀ u ∈ s, N ≤ u) →
      ((middleBad.card : ℝ) / Fintype.card Ω ≤ δ) →
      (∀ u ∈ s, ((B u).card : ℝ) / Fintype.card Ω ≤
        (u : ℝ) ^ (-(1 / 200 : ℝ))) →
      ∃ f : Fin 1000 → Ω, f 0 ∉ middleBad ∧
        ∀ u ∈ s, ∃ i : Fin 1000, f i ∉ B u := by
  classical
  obtain ⟨N, hN⟩ := exists_thousand_terminal_blocks_with_global_bad δ hδ
  refine ⟨N, ?_⟩
  intro Ω _ _ s B middleBad hs hmiddle hbad
  let E : Finset (Fin 1000 → Ω) :=
    Finset.univ.filter (fun f => f 0 ∈ middleBad)
  have hE : (E.card : ℝ) / (Fintype.card Ω : ℝ) ^ 1000 ≤ δ := by
    exact (bad_first_block_fraction middleBad 999).trans_le hmiddle
  obtain ⟨f, hf, hterminal⟩ := hN Ω s B E hs hE hbad
  refine ⟨f, ?_, hterminal⟩
  simpa only [E, Finset.mem_filter, Finset.mem_univ, true_and] using hf

end Problem337.IndependentBlockSelection

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RandomSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.RandomSelection

/-- A simultaneous variable-threshold Markov bound on the fraction of bad samples. -/
theorem bad_threshold_fraction_le {Ω J : Type*} [Fintype Ω] [Nonempty Ω]
    [DecidableEq Ω] (tests : Finset J) (score : Ω → J → ℝ)
    (threshold ε : J → ℝ)
    (hnonneg : ∀ ω, ∀ j ∈ tests, 0 ≤ score ω j)
    (hpos : ∀ j ∈ tests, 0 < threshold j)
    (hmean : ∀ j ∈ tests, (∑ ω, score ω j) ≤
      (Fintype.card Ω : ℝ) * ε j * threshold j) :
    ((Finset.univ.filter (fun ω => ∃ j ∈ tests, threshold j < score ω j)).card : ℝ) /
      Fintype.card Ω ≤ ∑ j ∈ tests, ε j := by
  classical
  have hΩ : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hfilter :
      Finset.univ.filter (fun ω => ∃ j ∈ tests, threshold j < score ω j) =
      Finset.univ.filter (fun ω => ∃ j ∈ tests, 1 < score ω j / threshold j) := by
    apply Finset.filter_congr
    intro ω _
    apply exists_congr
    intro j
    apply and_congr_right
    intro hj
    rw [lt_div_iff₀ (hpos j hj), one_mul]
  rw [hfilter]
  apply (div_le_iff₀ hΩ).2
  have hmarkov := card_exists_large_score_mul_le Finset.univ tests
    (fun ω j => score ω j / threshold j) 1
    (fun ω _ j hj => div_nonneg (hnonneg ω j hj) (hpos j hj).le)
  simp only [mul_one] at hmarkov
  calc
    ((Finset.univ.filter (fun ω => ∃ j ∈ tests, 1 < score ω j / threshold j)).card : ℝ) ≤
        ∑ j ∈ tests, ∑ ω, score ω j / threshold j := hmarkov
    _ = ∑ j ∈ tests, (∑ ω, score ω j) / threshold j := by
      simp_rw [Finset.sum_div]
    _ ≤ ∑ j ∈ tests, (Fintype.card Ω : ℝ) * ε j := by
      apply Finset.sum_le_sum
      intro j hj
      exact (div_le_iff₀ (hpos j hj)).2 (hmean j hj)
    _ = (∑ j ∈ tests, ε j) * Fintype.card Ω := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- A finite realization simultaneously meeting all middle-level mean thresholds
    and enjoying a successful block for every terminal integer. -/
theorem exists_middle_thresholds_and_terminal_blocks (δ : ℝ) (hδ : δ < 1) :
    ∃ N : ℕ, ∀ (Ω J : Type) [Fintype Ω] [Nonempty Ω]
      (tests : Finset J) (score : Ω → J → ℝ) (threshold ε : J → ℝ)
      (s : Finset ℕ) (B : ℕ → Finset Ω),
      (∀ ω, ∀ j ∈ tests, 0 ≤ score ω j) →
      (∀ j ∈ tests, 0 < threshold j) →
      (∀ j ∈ tests, (∑ ω, score ω j) ≤
        (Fintype.card Ω : ℝ) * ε j * threshold j) →
      (∑ j ∈ tests, ε j) ≤ δ →
      (∀ u ∈ s, N ≤ u) →
      (∀ u ∈ s, ((B u).card : ℝ) / Fintype.card Ω ≤
        (u : ℝ) ^ (-(1 / 200 : ℝ))) →
      ∃ f : Fin 1000 → Ω, (∀ j ∈ tests, score (f 0) j ≤ threshold j) ∧
        ∀ u ∈ s, ∃ i : Fin 1000, f i ∉ B u := by
  classical
  obtain ⟨N, hN⟩ := IndependentBlockSelection.exists_middle_and_terminal_blocks δ hδ
  refine ⟨N, ?_⟩
  intro Ω J _ _ tests score threshold ε s B hnonneg hpos hmean hε hs hbad
  let middleBad := Finset.univ.filter (fun ω => ∃ j ∈ tests, threshold j < score ω j)
  have hmiddle : (middleBad.card : ℝ) / Fintype.card Ω ≤ δ :=
    (bad_threshold_fraction_le tests score threshold ε hnonneg hpos hmean).trans hε
  obtain ⟨f, hf, hterminal⟩ := hN Ω s B middleBad hs hmiddle hbad
  refine ⟨f, ?_, hterminal⟩
  intro j hj
  by_contra h
  apply hf
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hj, lt_of_not_ge h⟩

end Problem337.RandomSelection

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_LevelFailureMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.LevelFailureMean

/-- Fubini for counts of failing integers at a level. -/
theorem sum_failure_counts {Ω U : Type*} [Fintype Ω] [DecidableEq Ω]
    (level : Finset U) (bad : Ω → U → Prop) [DecidableRel bad] :
    (∑ ω, ((level.filter (bad ω)).card : ℝ)) =
      ∑ u ∈ level, ((Finset.univ.filter (fun ω => bad ω u)).card : ℝ) := by
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  exact Finset.sum_comm

/-- Pointwise failure probabilities bound the expected number of failing
    integers on a level, without any independence between integers. -/
theorem level_failure_mean_le {Ω U : Type*} [Fintype Ω] [Nonempty Ω]
    [DecidableEq Ω] (level : Finset U) (bad : Ω → U → Prop) [DecidableRel bad]
    (X e : ℝ) (he : 0 ≤ e) (hlevel : (level.card : ℝ) ≤ X)
    (hbad : ∀ u ∈ level,
      ((Finset.univ.filter (fun ω => bad ω u)).card : ℝ) / Fintype.card Ω ≤ e) :
    (∑ ω, ((level.filter (bad ω)).card : ℝ)) ≤
      (Fintype.card Ω : ℝ) * e * X := by
  have hΩ : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  rw [sum_failure_counts]
  calc
    (∑ u ∈ level, ((Finset.univ.filter (fun ω => bad ω u)).card : ℝ)) ≤
        ∑ _u ∈ level, e * (Fintype.card Ω : ℝ) := by
      apply Finset.sum_le_sum
      intro u hu
      exact (div_le_iff₀ hΩ).mp (hbad u hu)
    _ = (level.card : ℝ) * (e * Fintype.card Ω) := by simp
    _ ≤ X * (e * Fintype.card Ω) :=
      mul_le_mul_of_nonneg_right hlevel (by positivity)
    _ = (Fintype.card Ω : ℝ) * e * X := by ring

/-- The two middle-level exponential budgets differ by exactly `exp(-m/250)`. -/
theorem middle_level_failure_mean_le {Ω U : Type*} [Fintype Ω] [Nonempty Ω]
    [DecidableEq Ω] (level : Finset U) (bad : Ω → U → Prop) [DecidableRel bad]
    (X m : ℝ) (hlevel : (level.card : ℝ) ≤ X)
    (hbad : ∀ u ∈ level,
      ((Finset.univ.filter (fun ω => bad ω u)).card : ℝ) / Fintype.card Ω ≤
        Real.exp (-m / 200)) :
    (∑ ω, ((level.filter (bad ω)).card : ℝ)) ≤ (Fintype.card Ω : ℝ) *
      Real.exp (-m / 250) * (X * Real.exp (-m / 1000)) := by
  have h := level_failure_mean_le level bad X (Real.exp (-m / 200))
    (Real.exp_pos _).le hlevel hbad
  have he : Real.exp (-m / 200) = Real.exp (-m / 250) * Real.exp (-m / 1000) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

/-- A deliberately coarse explicit onset suffices to absorb the number of levels. -/
theorem middle_level_budget_le_half (m : ℝ) (hm : 500000 ≤ m) :
    m * Real.exp (-m / 250) ≤ 1 / 2 := by
  have hm0 : 0 ≤ m := by linarith
  have hlin := Real.add_one_le_exp (m / 500)
  have hsq : (m / 500 + 1) ^ 2 ≤ Real.exp (m / 500) ^ 2 := by
    exact (sq_le_sq₀ (by positivity) (Real.exp_pos _).le).mpr hlin
  have heq : Real.exp (m / 500) ^ 2 = Real.exp (m / 250) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [heq] at hsq
  have hlarge : 2 * m ≤ Real.exp (m / 250) := by
    nlinarith
  rw [show -m / 250 = -(m / 250) by ring, Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).2
  linarith

/-- Concrete finite form of the simultaneous-selection step: one block has
    few failures at every middle level, while the collection of 1000 blocks
    succeeds at every sufficiently large terminal integer. -/
theorem exists_good_levels_and_terminal_blocks :
    ∃ N : ℕ, ∀ (Ω J : Type) [Fintype Ω] [Nonempty Ω]
      (tests : Finset J) (level : J → Finset ℕ) (X : J → ℝ) (m : ℝ)
      (middleBad terminalBad : Ω → ℕ → Prop)
      [DecidableRel middleBad] [DecidableRel terminalBad] (terminal : Finset ℕ),
      500000 ≤ m → (tests.card : ℝ) ≤ m →
      (∀ j ∈ tests, 0 < X j) →
      (∀ j ∈ tests, ((level j).card : ℝ) ≤ X j) →
      (∀ j ∈ tests, ∀ u ∈ level j,
        ((Finset.univ.filter (fun ω => middleBad ω u)).card : ℝ) /
          Fintype.card Ω ≤ Real.exp (-m / 200)) →
      (∀ u ∈ terminal, N ≤ u) →
      (∀ u ∈ terminal,
        ((Finset.univ.filter (fun ω => terminalBad ω u)).card : ℝ) /
          Fintype.card Ω ≤ (u : ℝ) ^ (-(1 / 200 : ℝ))) →
      ∃ f : Fin 1000 → Ω,
        (∀ j ∈ tests,
          (((level j).filter (middleBad (f 0))).card : ℝ) ≤
            X j * Real.exp (-m / 1000)) ∧
        ∀ u ∈ terminal, ∃ i : Fin 1000, ¬ terminalBad (f i) u := by
  classical
  obtain ⟨N, hN⟩ := RandomSelection.exists_middle_thresholds_and_terminal_blocks
    (1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨N, ?_⟩
  intro Ω J _ _ tests level X m middleBad terminalBad _ _ terminal
    hm htests hX hlevel hmiddle hterminal hbad
  let score : Ω → J → ℝ := fun ω j => ((level j).filter (middleBad ω)).card
  let threshold : J → ℝ := fun j => X j * Real.exp (-m / 1000)
  let ε : J → ℝ := fun _ => Real.exp (-m / 250)
  let B : ℕ → Finset Ω := fun u => Finset.univ.filter (fun ω => terminalBad ω u)
  have hnonneg : ∀ ω, ∀ j ∈ tests, 0 ≤ score ω j := by
    intros
    exact Nat.cast_nonneg _
  have hpos : ∀ j ∈ tests, 0 < threshold j := by
    intro j hj
    exact mul_pos (hX j hj) (Real.exp_pos _)
  have hmean : ∀ j ∈ tests, (∑ ω, score ω j) ≤
      (Fintype.card Ω : ℝ) * ε j * threshold j := by
    intro j hj
    exact middle_level_failure_mean_le (level j) middleBad (X j) m
      (hlevel j hj) (hmiddle j hj)
  have herror : (∑ j ∈ tests, ε j) ≤ (1 / 2 : ℝ) := by
    dsimp [ε]
    simp only [Finset.sum_const, nsmul_eq_mul]
    exact (mul_le_mul_of_nonneg_right htests (Real.exp_pos _).le).trans
      (middle_level_budget_le_half m hm)
  obtain ⟨f, hf, ht⟩ := hN Ω J tests score threshold ε terminal B
    hnonneg hpos hmean herror hterminal hbad
  refine ⟨f, hf, ?_⟩
  intro u hu
  obtain ⟨i, hi⟩ := ht u hu
  exact ⟨i, by simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using hi⟩

end Problem337.LevelFailureMean

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_FourierCommonRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.FourierCommonRealization

/-- The random-product second moment hypotheses imply one common collection
    of 1000 sample blocks, simultaneously good at all middle and terminal scales.
    This is stated directly in normalized Fourier averages. -/
theorem exists_common_fourier_realization :
    ∃ N : ℕ, ∀ (Ω J : Type) [Fintype Ω] [Nonempty Ω]
      (tests : Finset J) (level : J → Finset ℕ) (X : J → ℝ) (m : ℝ)
      (freq : Finset ℕ) (terminalFreq : ℕ → Finset ℕ)
      (phase : Ω → ℕ → ℕ → ℂ) (w : ℕ → ℝ) (terminal : Finset ℕ),
      500000 ≤ m → (tests.card : ℝ) ≤ m →
      (∀ j ∈ tests, 0 < X j) →
      (∀ j ∈ tests, ((level j).card : ℝ) ≤ X j) →
      ((freq.card : ℝ) ≤ Real.exp (4 * m / 10000)) →
      (∀ j ∈ tests, ∀ u ∈ level j, (9999 / 10000 : ℝ) * m ≤ w u) →
      (∀ j ∈ tests, ∀ u ∈ level j, ∀ l ∈ freq,
        (∑ ω, ‖phase ω u l‖ ^ 2) / Fintype.card Ω ≤ Real.exp (-w u / 100)) →
      (∀ u ∈ terminal, N ≤ u) →
      (∀ u ∈ terminal, ((terminalFreq u).card : ℝ) ≤
        Real.exp (4 * Real.log (u : ℝ) / 10000)) →
      (∀ u ∈ terminal, ∀ l ∈ terminalFreq u,
        (∑ ω, ‖phase ω u l‖ ^ 2) / Fintype.card Ω ≤
          Real.exp (-Real.log (u : ℝ) / 100)) →
      ∃ f : Fin 1000 → Ω,
        (∀ j ∈ tests,
          (((level j).filter (fun u => ∃ l ∈ freq,
            Real.exp (-3 * m / 10000) < ‖phase (f 0) u l‖)).card : ℝ) ≤
              X j * Real.exp (-m / 1000)) ∧
        ∀ u ∈ terminal, ∃ i : Fin 1000, ∀ l ∈ terminalFreq u,
          ‖phase (f i) u l‖ ≤ Real.exp (-3 * Real.log (u : ℝ) / 10000) := by
  classical
  obtain ⟨N, hN⟩ := LevelFailureMean.exists_good_levels_and_terminal_blocks
  refine ⟨max N 1, ?_⟩
  intro Ω J _ _ tests level X m freq terminalFreq phase w terminal
    hm htests hX hlevels hfreq hw hmoment hterminal htfreq htmoment
  have hΩ : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  let middleBad : Ω → ℕ → Prop := fun ω u =>
    ∃ l ∈ freq, Real.exp (-3 * m / 10000) < ‖phase ω u l‖
  let terminalBad : Ω → ℕ → Prop := fun ω u =>
    ∃ l ∈ terminalFreq u,
      Real.exp (-3 * Real.log (u : ℝ) / 10000) < ‖phase ω u l‖
  have hmiddle : ∀ j ∈ tests, ∀ u ∈ level j,
      ((Finset.univ.filter (fun ω => middleBad ω u)).card : ℝ) /
        Fintype.card Ω ≤ Real.exp (-m / 200) := by
    intro j hj u hu
    apply FourierFailureBounds.middle_failure_fraction_le
      freq (fun ω l => phase ω u l) m (w u) (by linarith) (hw j hj u hu) hfreq
    intro l hl
    have h := (div_le_iff₀ hΩ).mp (hmoment j hj u hu l hl)
    simpa only [mul_comm] using h
  have htcut : ∀ u ∈ terminal, N ≤ u := by
    intro u hu
    exact (le_max_left N 1).trans (hterminal u hu)
  have hbad : ∀ u ∈ terminal,
      ((Finset.univ.filter (fun ω => terminalBad ω u)).card : ℝ) /
        Fintype.card Ω ≤ (u : ℝ) ^ (-(1 / 200 : ℝ)) := by
    intro u hu
    have hu1 : 1 ≤ u := (le_max_right N 1).trans (hterminal u hu)
    apply FourierFailureBounds.terminal_failure_fraction_le
      (terminalFreq u) (fun ω l => phase ω u l) (u : ℝ)
      (by exact_mod_cast hu1) (htfreq u hu)
    intro l hl
    have h := (div_le_iff₀ hΩ).mp (htmoment u hu l hl)
    simpa only [mul_comm] using h
  obtain ⟨f, hf, ht⟩ := hN Ω J tests level X m middleBad terminalBad terminal
    hm htests hX hlevels hmiddle htcut hbad
  refine ⟨f, hf, ?_⟩
  intro u hu
  obtain ⟨i, hi⟩ := ht u hu
  refine ⟨i, ?_⟩
  intro l hl
  exact le_of_not_gt (fun h => hi ⟨l, hl, h⟩)

end Problem337.FourierCommonRealization

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_ResidueLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open Filter

namespace Problem337.ResidueLevels

theorem before_depth_iff {A m η : ℝ} (hm : 0 < m) (hη : 0 < η) (j : ℕ) :
    j < depth A m η ↔ m < A - η * m * j := by
  rw [depth, Nat.lt_ceil, lt_div_iff₀ (mul_pos hη hm)]
  constructor <;> intro h <;> nlinarith

theorem depth_upper {A m η : ℝ} (hm : 0 < m) (hη : 0 < η)
    (hA : m ≤ A) :
    (depth A m η : ℝ) < A / (η * m) + 1 := by
  have hp : 0 < η * m := mul_pos hη hm
  have hx : 0 ≤ (A - m) / (η * m) := div_nonneg (sub_nonneg.mpr hA) hp.le
  have hu := Nat.ceil_lt_add_one hx
  change (depth A m η : ℝ) < (A - m) / (η * m) + 1 at hu
  have hle : (A - m) / (η * m) ≤ A / (η * m) :=
    div_le_div_of_nonneg_right (by linarith) hp.le
  linarith

theorem depth_log_bound {S D m η : ℝ} (_hS : 0 < S) (hlog : 1 ≤ Real.log S)
    (hD : 1 ≤ D) (hm : 0 < m) (hη : 0 < η) (hηone : η ≤ 1)
    (hmlo : S / (2 * Real.log S) ≤ m) (hmhi : m ≤ D * S) :
    (depth (D * S) m η : ℝ) ≤ (3 * D / η) * Real.log S := by
  have hp : 0 < η * m := mul_pos hη hm
  have hlogpos : 0 < Real.log S := by linarith
  have hmlo' : S ≤ m * (2 * Real.log S) :=
    (div_le_iff₀ (by positivity : 0 < 2 * Real.log S)).1 hmlo
  have hratio : D * S / (η * m) ≤ (2 * D / η) * Real.log S := by
    apply (div_le_iff₀ hp).2
    have hmul := mul_le_mul_of_nonneg_left hmlo' (show 0 ≤ D by linarith)
    have heq : (2 * D / η) * Real.log S * (η * m) = D * (m * (2 * Real.log S)) := by
      field_simp
    rw [heq]
    exact hmul
  have hDone : 1 ≤ D / η := (le_div_iff₀ hη).2 (by linarith)
  have hbudget : 1 ≤ (D / η) * Real.log S := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hDone) (sub_nonneg.mpr hlog)]
  have hu := depth_upper hm hη hmhi
  have heq : (3 * D / η) * Real.log S =
      (2 * D / η) * Real.log S + (D / η) * Real.log S := by ring
  rw [heq]
  linarith

theorem tendsto_div_log : Tendsto (fun S : ℝ => S / Real.log S) atTop atTop := by
  have ht : Tendsto (fun S : ℝ => Real.log S / S) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  apply tendsto_atTop.2
  intro b
  let c : ℝ := max b 1
  have hc : 0 < c := by dsimp [c]; positivity
  filter_upwards [ht.eventually (gt_mem_nhds (one_div_pos.mpr hc)),
    eventually_gt_atTop (1 : ℝ)] with S hratio hS
  have hSp : 0 < S := by linarith
  have hlogp : 0 < Real.log S := Real.log_pos hS
  have hprod := (div_lt_div_iff₀ hSp hc).1 hratio
  have hlt : c < S / Real.log S := (lt_div_iff₀ hlogp).2 (by nlinarith)
  exact (le_max_left b 1).trans hlt.le

theorem scale_bounds {S : ℝ} (hS : 0 < S) (hlog : 0 < Real.log S)
    (hratio : 2 ≤ S / Real.log S) :
    S / (2 * Real.log S) ≤ (scale S : ℝ) ∧
      (scale S : ℝ) ≤ S / Real.log S := by
  have hx : 0 ≤ S / Real.log S := div_nonneg hS.le hlog.le
  have hfloor := Nat.lt_floor_add_one (S / Real.log S)
  have hle := Nat.floor_le hx
  change S / Real.log S < (scale S : ℝ) + 1 at hfloor
  change (scale S : ℝ) ≤ S / Real.log S at hle
  have heq : S / (2 * Real.log S) = (S / Real.log S) / 2 := by ring
  refine ⟨?_, hle⟩
  rw [heq]
  linarith

theorem eventually_scale_bounds : ∀ᶠ S : ℝ in atTop,
    1 ≤ Real.log S ∧ 2 ≤ scale S ∧
    S / (2 * Real.log S) ≤ (scale S : ℝ) ∧
    (scale S : ℝ) ≤ S / Real.log S := by
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_div_log.eventually (eventually_ge_atTop (2 : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with S hlog hratio hS
  refine ⟨hlog, Nat.le_floor hratio, ?_⟩
  exact scale_bounds (by linarith) (by linarith) hratio

theorem tendsto_scale : Tendsto (fun S : ℝ => (scale S : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ (tendsto_div_log.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  filter_upwards [eventually_scale_bounds] with S hS
  have heq : (S / Real.log S) / 2 = S / (2 * Real.log S) := by ring
  simpa only [heq] using hS.2.2.1

theorem eventually_depth_log_bound {D η : ℝ} (hD : 1 ≤ D) (hη : 0 < η)
    (hηone : η ≤ 1) : ∀ᶠ S : ℝ in atTop,
    (depth (D * S) (scale S) η : ℝ) ≤ (3 * D / η) * Real.log S := by
  filter_upwards [eventually_scale_bounds, eventually_gt_atTop (1 : ℝ)] with S hS hSp
  have hm : (0 : ℝ) < scale S := by exact_mod_cast (show 0 < scale S by omega)
  have hlog : 0 < Real.log S := by linarith [hS.1]
  have hratio : S / Real.log S ≤ S := by
    apply (div_le_iff₀ hlog).2
    nlinarith [hS.1]
  have hDS : S ≤ D * S := by nlinarith
  exact depth_log_bound (by linarith) hS.1 hD hm hη hηone hS.2.2.1
    (hS.2.2.2.trans (hratio.trans hDS))

end Problem337.ResidueLevels

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_GeometricRandomRanges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Filter

namespace Problem337.GeometricRandomRanges

/-- The floor prime-product scale eventually dominates any fixed multiple of
`log S`. This simultaneously handles the number of levels and the random
product theorem's lower logarithmic cutoff. -/
theorem eventually_log_mul_le_scale (K : ℝ) :
    ∀ᶠ S : ℝ in atTop, K * Real.log S ≤ (ResidueLevels.scale S : ℝ) := by
  let C : ℝ := max K 1
  have hC : 0 < C := by dsimp [C]; positivity
  have ht : Tendsto (fun S : ℝ => Real.log S ^ 2 / S) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have heps : 0 < 1 / (2 * C) := by positivity
  filter_upwards [ht.eventually (gt_mem_nhds heps),
    ResidueLevels.eventually_scale_bounds, eventually_gt_atTop (1 : ℝ)] with S hsmall hm hS
  have hSpos : 0 < S := by linarith
  have hlog : 0 < Real.log S := Real.log_pos hS
  have hcross : 2 * C * Real.log S ^ 2 < S := by
    have h := (div_lt_div_iff₀ hSpos (by positivity : 0 < 2 * C)).mp hsmall
    nlinarith
  have hfloor := (div_le_iff₀ (by positivity : 0 < 2 * Real.log S)).mp hm.2.2.1
  have hCle : C * Real.log S ≤ (ResidueLevels.scale S : ℝ) := by
    nlinarith
  exact (mul_le_mul_of_nonneg_right (le_max_left K 1) hlog.le).trans hCle

theorem mem_middleTests {D S : ℝ} {j : ℕ} (hj : j ∈ middleTests D S) :
    j < ResidueLevels.depth (D * S) (ResidueLevels.scale S) (1 / 10000) ∧
      cutoff D S j ≤ Real.exp S := by
  simpa only [middleTests, Finset.mem_filter, Finset.mem_range] using hj

theorem mem_middleLevel {D S : ℝ} {j u : ℕ} (hu : u ∈ middleLevel D S j) :
    0 < u ∧ cutoff D S (j + 1) < (u : ℝ) ∧ (u : ℝ) ≤ cutoff D S j := by
  obtain ⟨huI, hlo⟩ := Finset.mem_filter.mp hu
  obtain ⟨hupos, huhi⟩ := Finset.mem_Icc.mp huI
  refine ⟨hupos, hlo, ?_⟩
  exact (Nat.cast_le.mpr huhi).trans
    (Nat.floor_le (ResidueLevels.level_pos _ _ _ _).le)

theorem middleLevel_card_le (D S : ℝ) (j : ℕ) :
    ((middleLevel D S j).card : ℝ) ≤ cutoff D S j := by
  have hcard : (middleLevel D S j).card ≤ ⌊cutoff D S j⌋₊ := by
    apply le_trans (Finset.card_filter_le _ _)
    simp
  exact (Nat.cast_le.mpr hcard).trans
    (Nat.floor_le (ResidueLevels.level_pos _ _ _ _).le)

/-- The exact logarithmic window, including the slight overlap of the middle
level with numerators below `exp m`. -/
theorem middle_log_bounds {D S : ℝ}
    (hm : 0 < (ResidueLevels.scale S : ℝ)) {j u : ℕ}
    (hj : j ∈ middleTests D S) (hu : u ∈ middleLevel D S j) :
    (9999 / 10000 : ℝ) * (ResidueLevels.scale S : ℝ) < Real.log (u : ℝ) ∧
      Real.log (u : ℝ) ≤ S := by
  obtain ⟨hjdepth, hjtop⟩ := mem_middleTests hj
  obtain ⟨hupos, hulow, huhi⟩ := mem_middleLevel hu
  have hur : (0 : ℝ) < u := by exact_mod_cast hupos
  have hbefore := (ResidueLevels.before_depth_iff hm
    (by norm_num : (0 : ℝ) < 1 / 10000) j).mp hjdepth
  have hloglower : D * S - (1 / 10000 : ℝ) * ResidueLevels.scale S * (j + 1 : ℕ) <
      Real.log (u : ℝ) := by
    exact (Real.lt_log_iff_exp_lt hur).mpr hulow
  have hnext : (9999 / 10000 : ℝ) * (ResidueLevels.scale S : ℝ) <
      D * S - (1 / 10000 : ℝ) * ResidueLevels.scale S * (j + 1 : ℕ) := by
    push_cast
    nlinarith
  refine ⟨hnext.trans hloglower, ?_⟩
  exact (Real.log_le_iff_le_exp hur).mpr (huhi.trans hjtop)

theorem mem_terminalRange {S : ℝ} {u : ℕ} (hu : u ∈ terminalRange S) :
    0 < u ∧ S ^ 100000 < (u : ℝ) ∧
      (u : ℝ) ≤ Real.exp (ResidueLevels.scale S) := by
  obtain ⟨huI, hlo⟩ := Finset.mem_filter.mp hu
  obtain ⟨hupos, huhi⟩ := Finset.mem_Icc.mp huI
  exact ⟨hupos, hlo, (Nat.cast_le.mpr huhi).trans
    (Nat.floor_le (Real.exp_pos _).le)⟩

/-- The terminal range has exactly the log window required by random products. -/
theorem terminal_log_bounds {S : ℝ} (hS : 0 < S) {u : ℕ}
    (hu : u ∈ terminalRange S) :
    100000 * Real.log S < Real.log (u : ℝ) ∧
      Real.log (u : ℝ) ≤ (ResidueLevels.scale S : ℝ) := by
  obtain ⟨hupos, hlo, hhi⟩ := mem_terminalRange hu
  have hur : (0 : ℝ) < u := by exact_mod_cast hupos
  constructor
  · have hlog := Real.log_lt_log (pow_pos hS 100000) hlo
    simpa only [Real.log_pow, Nat.cast_ofNat] using hlog
  · exact (Real.log_le_iff_le_exp hur).mpr hhi

/-- A single onset works for all middle levels and terminal numerators.
In particular the abstract random-selection range premises are satisfied
by the explicit geometric cutoffs, not assumed separately. -/
theorem eventually_selectionRanges (D : ℝ) (hD : 1 ≤ D) (N : ℕ) :
    ∀ᶠ S : ℝ in atTop, SelectionRanges D S N := by
  filter_upwards [ResidueLevels.eventually_scale_bounds,
    ResidueLevels.eventually_depth_log_bound hD (by norm_num : (0 : ℝ) < 1 / 10000)
      (by norm_num : (1 / 10000 : ℝ) ≤ 1),
    eventually_log_mul_le_scale (3 * D / (1 / 10000)),
    eventually_log_mul_le_scale 200000,
    ResidueLevels.tendsto_scale.eventually (eventually_ge_atTop (500000 : ℝ)),
    eventually_ge_atTop (8 : ℝ), eventually_ge_atTop (N : ℝ)]
    with S hscale hdepth hcount hlogscale hlarge hS8 hN
  have hS : 1 < S := by linarith
  have hm : 0 < (ResidueLevels.scale S : ℝ) := by linarith
  have hlog : 0 ≤ Real.log S := (Real.log_pos hS).le
  refine ⟨hS8, hlarge, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hcard : (middleTests D S).card ≤
        ResidueLevels.depth (D * S) (ResidueLevels.scale S) (1 / 10000) := by
      apply le_trans (Finset.card_filter_le _ _)
      simp
    exact (Nat.cast_le.mpr hcard).trans (hdepth.trans hcount)
  · intro j hj
    exact ResidueLevels.level_pos _ _ _ _
  · intro j hj
    exact middleLevel_card_le D S j
  · intro j hj u hu
    obtain ⟨hlo, hhi⟩ := middle_log_bounds hm hj hu
    exact ⟨by nlinarith, hhi, hlo.le⟩
  · intro u hu
    obtain ⟨_, hlo, _⟩ := mem_terminalRange hu
    have hpow : S ≤ S ^ 100000 := le_self_pow₀ hS.le (by norm_num)
    have hNu : (N : ℝ) ≤ u := hN.trans (hpow.trans hlo.le)
    exact_mod_cast hNu
  · intro u hu
    obtain ⟨hlo, hhi⟩ := terminal_log_bounds (by linarith : 0 < S) hu
    exact ⟨hlo.le, hhi⟩

end Problem337.GeometricRandomRanges

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RandomCorrelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337.RandomProducts

/-- Transfer an exposed product factorization to a pair-correlation estimate.
The bad-exposure counting and the fresh-product cancellation are separate,
explicit inputs, so this lemma does not assume probabilistic independence. -/
theorem correlation_of_exposed_products
    {Ω E A B : Type*} [Fintype Ω] [Fintype E] [Fintype A] [Fintype B]
    [Nonempty E] [Nonempty A] [Nonempty B]
    (e : Ω ≃ E × (A × B)) (pI pJ : Ω → ℕ)
    (U V : E → ℕ) (f : A → ℕ) (g : B → ℕ)
    (hI : ∀ c a b, pI (e.symm (c, (a, b))) = U c * f a * g b)
    (hJ : ∀ c a b, pJ (e.symm (c, (a, b))) = V c)
    (u l : ℕ) [NeZero u] (bad : Finset E) (ε δ : ℝ) (hδ : 0 ≤ δ)
    (hbad : (bad.card : ℝ) / Fintype.card E ≤ ε)
    (hgood : ∀ c, c ∉ bad →
      ‖𝔼 a : A, 𝔼 b : B,
        ZMod.stdAddChar (((l * U c * f a * g b : ℕ) : ZMod u) -
          ((l * V c : ℕ) : ZMod u))‖ ≤ δ) :
    ‖𝔼 ω : Ω, ZMod.stdAddChar (((l * pI ω : ℕ) : ZMod u) -
      ((l * pJ ω : ℕ) : ZMod u))‖ ≤ ε + δ := by
  have h := exposure_average_norm_bound e
    (fun ω : Ω => ZMod.stdAddChar (((l * pI ω : ℕ) : ZMod u) -
      ((l * pJ ω : ℕ) : ZMod u))) bad δ hδ
    (fun ω => (AddChar.norm_apply _ _).le) ?_
  · exact h.trans (by linarith)
  · intro c hc
    rw [show (𝔼 ab : A × B,
        ZMod.stdAddChar (((l * pI (e.symm (c, ab)) : ℕ) : ZMod u) -
          ((l * pJ (e.symm (c, ab)) : ℕ) : ZMod u))) =
        𝔼 a : A, 𝔼 b : B,
          ZMod.stdAddChar (((l * pI (e.symm (c, (a,b))) : ℕ) : ZMod u) -
            ((l * pJ (e.symm (c, (a,b))) : ℕ) : ZMod u)) by
      exact Finset.expect_product Finset.univ Finset.univ _]
    simp_rw [hI, hJ, ← Nat.mul_assoc]
    exact hgood c hc

end Problem337.RandomProducts

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RandomExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.RandomExposure

/-- Two disjoint equally sized groups can be selected from a sufficiently large finite set. -/
theorem exists_two_disjoint_subsets {α : Type*} [DecidableEq α]
    (D : Finset α) (s : ℕ) (hsize : 2 * s ≤ D.card) :
    ∃ A B : Finset α, A ⊆ D ∧ B ⊆ D ∧ Disjoint A B ∧ A.card = s ∧ B.card = s := by
  obtain ⟨A, hAD, hA⟩ := Finset.exists_subset_card_eq (show s ≤ D.card by omega)
  have hremain : s ≤ (D \ A).card := by
    rw [Finset.card_sdiff_of_subset hAD, hA]
    omega
  obtain ⟨B, hB, hBs⟩ := Finset.exists_subset_card_eq hremain
  refine ⟨A, B, hAD, hB.trans Finset.sdiff_subset, ?_, hA, hBs⟩
  apply Finset.disjoint_left.mpr
  intro i hiA hiB
  exact (Finset.mem_sdiff.mp (hB hiB)).2 hiA

/-- Select the two fresh groups for a pair of Boolean words with enough differing positions. -/
theorem exists_differing_blocks {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I J : ι → Bool) (s : ℕ)
    (hsize : 2 * s ≤ (Finset.univ.filter fun i => I i ≠ J i).card) :
    ∃ A B : Finset ι, Disjoint A B ∧ A.card = s ∧ B.card = s ∧
      (∀ i ∈ A, I i ≠ J i) ∧ (∀ i ∈ B, I i ≠ J i) := by
  obtain ⟨A, B, hA, hB, hAB, hAs, hBs⟩ :=
    exists_two_disjoint_subsets (Finset.univ.filter fun i => I i ≠ J i) s hsize
  refine ⟨A, B, hAB, hAs, hBs, ?_, ?_⟩
  · intro i hi
    exact (Finset.mem_filter.mp (hA hi)).2
  · intro i hi
    exact (Finset.mem_filter.mp (hB hi)).2

theorem product_selectedLabels {ι M : Type*} [DecidableEq ι] [CommMonoid M]
    (I : ι → Bool) (A : Finset ι) (p : ι × Bool → M) :
    (∏ i ∈ A, p (i, I i)) = ∏ z : selectedLabels I A, p z := by
  rw [Finset.prod_coe_sort]
  symm
  apply Finset.prod_image
  intro i _ j _ h
  exact congrArg Prod.fst h

/-- Factor the first word's product into exposed and two free coordinate groups. -/
theorem selected_product_factorization {ι M : Type*} [Fintype ι] [DecidableEq ι]
    [CommMonoid M] (I : ι → Bool) (A B : Finset ι) (hAB : Disjoint A B)
    (p : ι × Bool → M) :
    (∏ i, p (i, I i)) =
      (∏ i ∈ Finset.univ \ (A ∪ B), p (i, I i)) *
      (∏ i ∈ A, p (i, I i)) * (∏ i ∈ B, p (i, I i)) := by
  have h := Finset.prod_sdiff (f := fun i => p (i, I i)) (Finset.subset_univ (A ∪ B))
  rw [Finset.prod_union hAB] at h
  simpa only [mul_assoc] using h.symm

theorem outsideSelectedLabel_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I : ι → Bool) (A B : Finset ι) : Function.Injective (outsideSelectedLabel I A B) := by
  intro i j h
  apply Subtype.ext
  exact congrArg (fun z : ExposedLabel I A B => z.val.1) h

/-- Explicit form of the exposed factor, useful for bounding the bad gcd event. -/
theorem exposed_first_factor_formula {ι β M : Type*} [Fintype ι] [DecidableEq ι]
    [CommMonoid M] (v : β → M) (I : ι → Bool) (A B : Finset ι) (hAB : Disjoint A B)
    (a : selectedLabels I A → β) (b : selectedLabels I B → β) (c : ExposedLabel I A B → β) :
    (∏ i ∈ Finset.univ \ (A ∪ B),
      v ((splitSample _ _ (selectedLabels_disjoint I hAB)).symm (a, b, c) (i, I i))) =
      exposedFirstProduct v I A B c := by
  rw [← Finset.prod_coe_sort]
  unfold exposedFirstProduct
  apply Finset.prod_congr rfl
  intro i _
  exact congrArg v (splitSample_symm_exposed _ _ _ a b c (outsideSelectedLabel I A B i))

theorem exposed_other_factor_formula {ι β M : Type*} [Fintype ι] [DecidableEq ι]
    [CommMonoid M] (v : β → M) (I J : ι → Bool) (A B : Finset ι) (hAB : Disjoint A B)
    (hA : ∀ i ∈ A, I i ≠ J i) (hB : ∀ i ∈ B, I i ≠ J i)
    (a : selectedLabels I A → β) (b : selectedLabels I B → β) (c : ExposedLabel I A B → β) :
    (∏ i, v ((splitSample _ _ (selectedLabels_disjoint I hAB)).symm (a, b, c) (i, J i))) =
      exposedOtherProduct v I J A B hA hB c := by
  apply Finset.prod_congr rfl
  intro i _
  exact congrArg v (splitSample_symm_exposed _ _ _ a b c
    ⟨(i, J i), other_word_exposed I J A hA i, other_word_exposed I J B hB i⟩)

end Problem337.RandomExposure

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_HitCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337.RandomProducts

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
theorem card_hitCylinder (P H : Finset α) {t : ℕ} (T : Finset (Fin t)) :
    (hitCylinder P H T).card = H.card ^ T.card * P.card ^ (t - T.card) := by
  classical
  rw [hitCylinder, Fintype.card_piFinset]
  simp_rw [apply_ite Finset.card]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hc : (Finset.univ.filter (fun i : Fin t => i ∉ T)).card = t - T.card := by
    simpa only [Finset.card_compl, Fintype.card_fin] using congrArg Finset.card
      (show (Finset.univ.filter (fun i : Fin t => i ∉ T)) = Tᶜ by ext; simp)
  rw [hc]

/-- Elementary union bound over sets of `k` hit positions. -/
theorem card_hitWords_le (P H : Finset α) (t k : ℕ) :
    (hitWords P H t k).card ≤ t.choose k * H.card ^ k * P.card ^ (t - k) := by
  classical
  have hcover : hitWords P H t k ⊆
      (Finset.univ.powersetCard k).biUnion (hitCylinder P H) := by
    intro f hf
    obtain ⟨hfP, hfk⟩ := Finset.mem_filter.mp hf
    obtain ⟨T, hT, hTk⟩ := Finset.exists_subset_card_eq hfk
    apply Finset.mem_biUnion.mpr
    refine ⟨T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hTk⟩, ?_⟩
    apply Fintype.mem_piFinset.mpr
    intro i
    by_cases hi : i ∈ T
    · simp only [ite_eq_left hi]
      exact (Finset.mem_filter.mp (hT hi)).2
    · simp only [ite_eq_right hi]
      exact Fintype.mem_piFinset.mp hfP i
  calc
    (hitWords P H t k).card ≤
        ((Finset.univ.powersetCard k).biUnion (hitCylinder P H)).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ T ∈ Finset.univ.powersetCard k, (hitCylinder P H T).card :=
      Finset.card_biUnion_le
    _ = ∑ _T ∈ Finset.univ.powersetCard k, H.card ^ k * P.card ^ (t - k) := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [card_hitCylinder, (Finset.mem_powersetCard.mp hT).2]
    _ = t.choose k * H.card ^ k * P.card ^ (t - k) := by
      simp only [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
      ring

/-- Normalized finite counting bound for independent uniform samples. -/
theorem hit_probability_le (P H : Finset α) (t k : ℕ) (hP : P.Nonempty) :
    ((hitWords P H t k).card : ℝ) / (P.card : ℝ) ^ t ≤
      ((t : ℝ) * (H.card : ℝ) / (P.card : ℝ)) ^ k := by
  have hPpos : 0 < (P.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hP
  by_cases hk : k ≤ t
  · have hcard : (hitWords P H t k).card ≤ t ^ k * H.card ^ k * P.card ^ (t - k) :=
      (card_hitWords_le P H t k).trans
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.choose_le_pow t k)))
    have hcardR : ((hitWords P H t k).card : ℝ) ≤
        (t : ℝ) ^ k * (H.card : ℝ) ^ k * (P.card : ℝ) ^ (t - k) := by
      exact_mod_cast hcard
    calc
      ((hitWords P H t k).card : ℝ) / (P.card : ℝ) ^ t ≤
          ((t : ℝ) ^ k * (H.card : ℝ) ^ k * (P.card : ℝ) ^ (t - k)) /
            (P.card : ℝ) ^ t := div_le_div_of_nonneg_right hcardR (by positivity)
      _ = ((t : ℝ) * (H.card : ℝ) / (P.card : ℝ)) ^ k := by
        have hp : (P.card : ℝ) ^ t = (P.card : ℝ) ^ (t - k) * (P.card : ℝ) ^ k := by
          rw [← pow_add, Nat.sub_add_cancel hk]
        rw [hp, div_pow, mul_pow]
        field_simp
  · have hgt : t < k := Nat.lt_of_not_ge hk
    have hzero : (hitWords P H t k).card = 0 := by
      have h := card_hitWords_le P H t k
      simpa [Nat.choose_eq_zero_of_lt hgt] using h
    rw [hzero]
    simp only [Nat.cast_zero, zero_div]
    positivity

/-- The numerical parameter choice for the exceptional gcd event in the random-products argument.
The threshold hypothesis is the denominator-cleared form of
`k ≥ 0.08 * V / (101 * log S)`. -/
theorem hit_probability_le_exp (P H : Finset α) (t k : ℕ) (S V : ℝ)
    (hP : P.Nonempty) (hS : 1 < S) (hV : 0 ≤ V)
    (ht : (t : ℝ) ≤ S) (hH : (H.card : ℝ) ≤ S)
    (hsize : S ^ 99 ≤ (P.card : ℝ))
    (hk : 8 * V ≤ 10100 * (k : ℝ) * Real.log S) :
    ((hitWords P H t k).card : ℝ) / (P.card : ℝ) ^ t ≤ Real.exp (-V / 20) := by
  have hSpos : 0 < S := by linarith
  have hprod : (t : ℝ) * (H.card : ℝ) ≤ S ^ 2 := by
    simpa only [pow_two] using mul_le_mul ht hH (Nat.cast_nonneg H.card) hSpos.le
  have hbase : (t : ℝ) * (H.card : ℝ) / (P.card : ℝ) ≤ 1 / S ^ 97 := by
    calc
      (t : ℝ) * (H.card : ℝ) / (P.card : ℝ) ≤ S ^ 2 / S ^ 99 :=
        div_le_div₀ (by positivity) hprod (by positivity) hsize
      _ = 1 / S ^ 97 := by
        rw [show (99 : ℕ) = 2 + 97 from rfl, pow_add]
        field_simp
  calc
    ((hitWords P H t k).card : ℝ) / (P.card : ℝ) ^ t ≤
        ((t : ℝ) * (H.card : ℝ) / (P.card : ℝ)) ^ k := hit_probability_le P H t k hP
    _ ≤ (1 / S ^ 97) ^ k := pow_le_pow_left₀ (by positivity) hbase k
    _ = Real.exp (-((97 * k : ℕ) : ℝ) * Real.log S) := by
      rw [one_div_pow, ← pow_mul, neg_mul, Real.exp_neg, Real.exp_nat_mul,
        Real.exp_log hSpos]
      simp only [one_div]
    _ ≤ Real.exp (-V / 20) := by
      apply Real.exp_le_exp.mpr
      push_cast
      nlinarith

end Problem337.RandomProducts

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_PrimeGcdHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337
/-- Only prime sample values which divide the modulus contribute to the gcd.
The index set, unlike a set of prime values, retains repeated samples. -/
theorem prime_gcd_eq_hit_gcd {ι : Type*} (s : Finset ι) (p : ι → ℕ) (u : ℕ)
    (hp : ∀ i ∈ s, Nat.Prime (p i)) :
    Nat.gcd (∏ i ∈ s, p i) u =
      Nat.gcd (∏ i ∈ s with p i ∣ u, p i) u := by
  classical
  have hcop : Nat.Coprime (∏ i ∈ s with ¬ p i ∣ u, p i) u := by
    apply Nat.Coprime.prod_left
    intro i hi
    obtain ⟨his, hnot⟩ := Finset.mem_filter.mp hi
    exact (hp i his).coprime_iff_not_dvd.mpr hnot
  rw [← Finset.prod_filter_mul_prod_filter_not s (fun i => p i ∣ u) p]
  exact hcop.gcd_mul_right_cancel _

theorem prime_gcd_dvd_hit_product {ι : Type*} (s : Finset ι) (p : ι → ℕ) (u : ℕ)
    (hp : ∀ i ∈ s, Nat.Prime (p i)) :
    Nat.gcd (∏ i ∈ s, p i) u ∣ ∏ i ∈ s with p i ∣ u, p i := by
  classical
  rw [prime_gcd_eq_hit_gcd s p u hp]
  exact Nat.gcd_dvd_left _ _

theorem prime_gcd_le_hit_product {ι : Type*} (s : Finset ι) (p : ι → ℕ) (u : ℕ)
    (hp : ∀ i ∈ s, Nat.Prime (p i)) :
    Nat.gcd (∏ i ∈ s, p i) u ≤ ∏ i ∈ s with p i ∣ u, p i := by
  classical
  apply Nat.le_of_dvd _ (prime_gcd_dvd_hit_product s p u hp)
  exact Finset.prod_pos (fun i hi => (hp i (Finset.mem_filter.mp hi).1).pos)

/-- Real-valued sample bounds are convenient when the sampling interval is
specified by a real asymptotic parameter. -/
theorem prime_gcd_le_real_pow_hit_count {ι : Type*} (s : Finset ι) (p : ι → ℕ)
    (u : ℕ) (B : ℝ) (hp : ∀ i ∈ s, Nat.Prime (p i))
    (hB : ∀ i ∈ s, (p i : ℝ) ≤ B) :
    (Nat.gcd (∏ i ∈ s, p i) u : ℝ) ≤
      B ^ (s.filter (fun i => p i ∣ u)).card := by
  classical
  calc
    (Nat.gcd (∏ i ∈ s, p i) u : ℝ) ≤ (∏ i ∈ s with p i ∣ u, p i : ℕ) := by
      exact_mod_cast prime_gcd_le_hit_product s p u hp
    _ = ∏ i ∈ s with p i ∣ u, (p i : ℝ) := by push_cast; rfl
    _ ≤ ∏ _i ∈ s with p _i ∣ u, B := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        exact hB i (Finset.mem_filter.mp hi).1
    _ = B ^ (s.filter (fun i => p i ∣ u)).card := by simp

/-- A large gcd forces many hits, counted with their sample multiplicities. -/
theorem hit_count_large_of_gcd_large {ι : Type*} (s : Finset ι) (p : ι → ℕ)
    (u : ℕ) {B x : ℝ} (hp : ∀ i ∈ s, Nat.Prime (p i))
    (hB : ∀ i ∈ s, (p i : ℝ) ≤ B) (hB1 : 1 < B) (hx : 0 < x)
    (hlarge : x < (Nat.gcd (∏ i ∈ s, p i) u : ℝ)) :
    Real.log x / Real.log B < ((s.filter (fun i => p i ∣ u)).card : ℝ) := by
  classical
  have hlt := hlarge.trans_le (prime_gcd_le_real_pow_hit_count s p u B hp hB)
  have hlog := Real.log_lt_log hx hlt
  rw [Real.log_pow] at hlog
  exact (div_lt_iff₀ (Real.log_pos hB1)).2 hlog

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_PrimeHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337

/-- A set of distinct prime divisors, all at least `L`, has size bounded
    by the logarithm of the modulus. This bounds the population of hit values. -/
theorem prime_divisor_population_pow_le (P : Finset ℕ) (u L : ℕ)
    (hu : 0 < u) (hp : ∀ p ∈ P, p.Prime) (hL : ∀ p ∈ P, L ≤ p) :
    L ^ (P.filter (fun p => p ∣ u)).card ≤ u := by
  have hsub : P.filter (fun p => p ∣ u) ⊆ u.primeFactors := by
    intro p h
    obtain ⟨hpP, hpu⟩ := Finset.mem_filter.mp h
    exact Nat.mem_primeFactors.mpr ⟨hp p hpP, hpu, hu.ne'⟩
  have hdvd : (∏ p ∈ P.filter (fun p => p ∣ u), p) ∣ u :=
    (Finset.prod_dvd_prod_of_subset _ _ id hsub).trans (Nat.prod_primeFactors_dvd u)
  calc
    L ^ (P.filter (fun p => p ∣ u)).card ≤
        ∏ p ∈ P.filter (fun p => p ∣ u), p := by
      apply Finset.pow_card_le_prod
      intro p h
      exact hL p (Finset.mem_filter.mp h).1
    _ ≤ u := Nat.le_of_dvd hu hdvd

/-- Real logarithmic version of the prime hit population estimate. -/
theorem prime_divisor_population_log_le (P : Finset ℕ) (u L : ℕ)
    (hu : 0 < u) (hL1 : 1 < L)
    (hp : ∀ p ∈ P, p.Prime) (hL : ∀ p ∈ P, L ≤ p) :
    ((P.filter (fun p => p ∣ u)).card : ℝ) ≤
      Real.log (u : ℝ) / Real.log (L : ℝ) := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hpow := prime_divisor_population_pow_le P u L hu hp hL
  have hreal : (L : ℝ) ^ (P.filter (fun p => p ∣ u)).card ≤ u := by
    exact_mod_cast hpow
  have hlog := Real.log_le_log (pow_pos hLpos _) hreal
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos (by exact_mod_cast hL1))).mpr hlog

end Problem337

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RandomGcdBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337.RandomProducts

/-- A concrete large-gcd probability estimate for uniform samples from a prime set.
This retains all sample multiplicities, and uses only finite counting. -/
theorem large_gcd_probability_le_exp (P : Finset ℕ) (t u : ℕ) (S V : ℝ)
    (hP : P.Nonempty) (hS : 1 < S) (hV : 0 ≤ V)
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (hmax : ∀ p ∈ P, (p : ℝ) ≤ S ^ 101)
    (ht : (t : ℝ) ≤ S) (hhits : ((P.filter (fun p => p ∣ u)).card : ℝ) ≤ S)
    (hsize : S ^ 99 ≤ (P.card : ℝ)) :
    (((sampleWords P t).filter (fun f =>
      Real.exp ((2 / 25 : ℝ) * V) < (Nat.gcd (∏ i, f i) u : ℝ))).card : ℝ) /
        (P.card : ℝ) ^ t ≤ Real.exp (-V / 20) := by
  classical
  let k : ℕ := ⌈((2 / 25 : ℝ) * V) / (101 * Real.log S)⌉₊
  let H := P.filter (fun p => p ∣ u)
  have hlog : 0 < Real.log S := Real.log_pos hS
  have hk : ((2 / 25 : ℝ) * V) / (101 * Real.log S) ≤ (k : ℝ) := Nat.le_ceil _
  have hknum : 8 * V ≤ 10100 * (k : ℝ) * Real.log S := by
    have h := (div_le_iff₀ (by positivity : 0 < 101 * Real.log S)).mp hk
    nlinarith
  have hsub : (sampleWords P t).filter (fun f =>
      Real.exp ((2 / 25 : ℝ) * V) < (Nat.gcd (∏ i, f i) u : ℝ)) ⊆
      hitWords P H t k := by
    intro f hf
    obtain ⟨hfP, hlarge⟩ := Finset.mem_filter.mp hf
    have hfp : ∀ i, f i ∈ P := Fintype.mem_piFinset.mp hfP
    have hB : 1 < S ^ 101 := one_lt_pow₀ hS (by decide)
    have hcount := hit_count_large_of_gcd_large Finset.univ f u
      (fun i _ => hprime (f i) (hfp i)) (fun i _ => hmax (f i) (hfp i))
      hB (Real.exp_pos _) hlarge
    have hratio : ((2 / 25 : ℝ) * V) / (101 * Real.log S) <
        ((Finset.univ.filter (fun i => f i ∣ u)).card : ℝ) := by
      simpa only [Real.log_exp, Real.log_pow, Nat.cast_ofNat] using hcount
    have hkcount : k ≤ (Finset.univ.filter (fun i => f i ∣ u)).card :=
      Nat.ceil_le.mpr hratio.le
    apply Finset.mem_filter.mpr
    refine ⟨hfP, ?_⟩
    have heq : (Finset.univ.filter (fun i => f i ∈ H)) =
        (Finset.univ.filter (fun i => f i ∣ u)) := by
      ext i
      simp only [H, Finset.mem_filter, Finset.mem_univ, true_and, hfp i]
    rw [heq]
    exact hkcount
  calc
    _ ≤ ((hitWords P H t k).card : ℝ) / (P.card : ℝ) ^ t := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ Real.exp (-V / 20) := hit_probability_le_exp P H t k S V hP hS hV ht hhits hsize hknum

/-- The same estimate permits a small fixed frequency factor in the gcd. -/
theorem large_frequency_gcd_probability_le_exp (P : Finset ℕ) (t u l : ℕ) (S V : ℝ)
    (hP : P.Nonempty) (hS : 1 < S) (hV : 0 ≤ V)
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (hmax : ∀ p ∈ P, (p : ℝ) ≤ S ^ 101)
    (ht : (t : ℝ) ≤ S) (hhits : ((P.filter (fun p => p ∣ u)).card : ℝ) ≤ S)
    (hsize : S ^ 99 ≤ (P.card : ℝ)) (hl : 0 < l)
    (hlbound : (l : ℝ) ≤ Real.exp (V / 200)) :
    (((sampleWords P t).filter (fun f =>
      Real.exp (V / 10) < (Nat.gcd (l * ∏ i, f i) u : ℝ))).card : ℝ) /
        (P.card : ℝ) ^ t ≤ Real.exp (-V / 20) := by
  classical
  have hsub : (sampleWords P t).filter (fun f =>
      Real.exp (V / 10) < (Nat.gcd (l * ∏ i, f i) u : ℝ)) ⊆
      (sampleWords P t).filter (fun f =>
      Real.exp ((2 / 25 : ℝ) * V) < (Nat.gcd (∏ i, f i) u : ℝ)) := by
    intro f hf
    obtain ⟨hfP, hlarge⟩ := Finset.mem_filter.mp hf
    refine Finset.mem_filter.mpr ⟨hfP, ?_⟩
    have hfp : ∀ i, f i ∈ P := Fintype.mem_piFinset.mp hfP
    have hprod : 0 < ∏ i, f i := Finset.prod_pos (fun i _ => (hprime (f i) (hfp i)).pos)
    have hg : 0 < Nat.gcd (∏ i, f i) u := Nat.gcd_pos_of_pos_left u hprod
    have hdiv : Nat.gcd (l * ∏ i, f i) u ∣ l * Nat.gcd (∏ i, f i) u :=
      (Nat.gcd_mul_left_dvd_mul_gcd u l (∏ i, f i)).trans
        (Nat.mul_dvd_mul (Nat.gcd_dvd_left l u) dvd_rfl)
    have hnat := Nat.le_of_dvd (Nat.mul_pos hl hg) hdiv
    have hreal : (Nat.gcd (l * ∏ i, f i) u : ℝ) ≤
        (l : ℝ) * (Nat.gcd (∏ i, f i) u : ℝ) := by exact_mod_cast hnat
    by_contra hnot
    have hsmall := le_of_not_gt hnot
    have hcontr : (Nat.gcd (l * ∏ i, f i) u : ℝ) ≤ Real.exp (V / 10) := by
      calc
        _ ≤ (l : ℝ) * (Nat.gcd (∏ i, f i) u : ℝ) := hreal
        _ ≤ Real.exp (V / 200) * Real.exp ((2 / 25 : ℝ) * V) :=
          mul_le_mul hlbound hsmall (Nat.cast_nonneg _) (Real.exp_pos _).le
        _ = Real.exp (V / 200 + (2 / 25 : ℝ) * V) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (V / 10) := Real.exp_le_exp.mpr (by linarith)
    exact hlarge.not_ge hcontr
  calc
    _ ≤ (((sampleWords P t).filter (fun f =>
        Real.exp ((2 / 25 : ℝ) * V) < (Nat.gcd (∏ i, f i) u : ℝ))).card : ℝ) /
          (P.card : ℝ) ^ t := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ Real.exp (-V / 20) :=
      large_gcd_probability_le_exp P t u S V hP hS hV hprime hmax ht hhits hsize

/-- Reduced moduli below `exp (0.9 V)` form an exponentially small set of samples.
This is the random-gcd estimate used before applying bilinear Fourier cancellation. -/
theorem small_reduced_modulus_probability_le (P : Finset ℕ) (t u l : ℕ) (S V : ℝ)
    (hP : P.Nonempty) (hS : 1 < S) (hV : 0 ≤ V) (huexp : (u : ℝ) = Real.exp V)
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (hmax : ∀ p ∈ P, (p : ℝ) ≤ S ^ 101)
    (ht : (t : ℝ) ≤ S) (hhits : ((P.filter (fun p => p ∣ u)).card : ℝ) ≤ S)
    (hsize : S ^ 99 ≤ (P.card : ℝ)) (hl : 0 < l)
    (hlbound : (l : ℝ) ≤ Real.exp (V / 200)) :
    (((sampleWords P t).filter (fun f =>
      ((u / Nat.gcd (l * ∏ i, f i) u : ℕ) : ℝ) < Real.exp (9 * V / 10))).card : ℝ) /
        (P.card : ℝ) ^ t ≤ Real.exp (-V / 20) := by
  classical
  have huR : 0 < (u : ℝ) := by rw [huexp]; exact Real.exp_pos _
  have hu : 0 < u := by exact_mod_cast huR
  have hsub : (sampleWords P t).filter (fun f =>
      ((u / Nat.gcd (l * ∏ i, f i) u : ℕ) : ℝ) < Real.exp (9 * V / 10)) ⊆
      (sampleWords P t).filter (fun f =>
      Real.exp (V / 10) < (Nat.gcd (l * ∏ i, f i) u : ℝ)) := by
    intro f hf
    obtain ⟨hfP, hsmall⟩ := Finset.mem_filter.mp hf
    refine Finset.mem_filter.mpr ⟨hfP, ?_⟩
    have hg : 0 < Nat.gcd (l * ∏ i, f i) u := Nat.gcd_pos_of_pos_right _ hu
    have hgR : 0 < (Nat.gcd (l * ∏ i, f i) u : ℝ) := by exact_mod_cast hg
    rw [Nat.cast_div_charZero (Nat.gcd_dvd_right _ _), huexp] at hsmall
    have hmul := (div_lt_iff₀ hgR).mp hsmall
    by_contra hnot
    have hle := mul_le_mul_of_nonneg_left (le_of_not_gt hnot) (Real.exp_pos (9 * V / 10)).le
    have heq : Real.exp (9 * V / 10) * Real.exp (V / 10) = Real.exp V := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq] at hle
    exact hmul.not_ge hle
  calc
    _ ≤ (((sampleWords P t).filter (fun f =>
        Real.exp (V / 10) < (Nat.gcd (l * ∏ i, f i) u : ℝ))).card : ℝ) /
          (P.card : ℝ) ^ t := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ Real.exp (-V / 20) := large_frequency_gcd_probability_le_exp
      P t u l S V hP hS hV hprime hmax ht hhits hsize hl hlbound

/-- The random-gcd bound with exactly the prime sampling scale used in the manuscript.
No asymptotic number-theory result is hidden: existence and cardinality of the prime set
are explicit hypotheses, while the entire exceptional-event estimate is proved. -/
theorem random_gcd_exception_bound_wide (P : Finset ℕ) (t u l : ℕ) (S V : ℝ)
    (hP : P.Nonempty) (hS : 2 ≤ S) (hV : 0 ≤ V) (hVS : V ≤ S)
    (huexp : (u : ℝ) = Real.exp V) (hprime : ∀ p ∈ P, Nat.Prime p)
    (hinterval : ∀ p ∈ P, S ^ 100 ≤ (p : ℝ) ∧ (p : ℝ) ≤ S ^ 101)
    (ht : (t : ℝ) ≤ S) (hsize : S ^ 99 ≤ (P.card : ℝ)) (hl : 0 < l)
    (hlbound : (l : ℝ) ≤ Real.exp (V / 200)) :
    (((sampleWords P t).filter (fun f =>
      ((u / Nat.gcd (l * ∏ i, f i) u : ℕ) : ℝ) < Real.exp (9 * V / 10))).card : ℝ) /
        (P.card : ℝ) ^ t ≤ Real.exp (-V / 20) := by
  have hS1 : 1 < S := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hmax : ∀ p ∈ P, (p : ℝ) ≤ S ^ 101 := fun p hp => (hinterval p hp).2
  have hmin : ∀ p ∈ P, 3 ≤ p := by
    intro p hp
    have hpow : (4 : ℝ) ≤ S ^ 100 := by
      calc
        4 = (2 : ℝ) ^ 2 := by norm_num
        _ ≤ S ^ 2 := pow_le_pow_left₀ (by norm_num) hS 2
        _ ≤ S ^ 100 := pow_le_pow_right₀ hS1.le (by norm_num)
    have hpR : (3 : ℝ) ≤ (p : ℝ) := by linarith [(hinterval p hp).1]
    exact_mod_cast hpR
  have huR : 0 < (u : ℝ) := by rw [huexp]; exact Real.exp_pos _
  have hu : 0 < u := by exact_mod_cast huR
  have hlog3 : 1 ≤ Real.log 3 := by
    have h := Real.log_le_log (Real.exp_pos 1) Real.exp_one_lt_three.le
    simpa only [Real.log_exp] using h
  have hpop := prime_divisor_population_log_le P u 3 hu (by norm_num) hprime hmin
  have hhits : ((P.filter (fun p => p ∣ u)).card : ℝ) ≤ S := by
    rw [huexp, Real.log_exp] at hpop
    exact hpop.trans ((div_le_self hV hlog3).trans hVS)
  exact small_reduced_modulus_probability_le P t u l S V hP hS1 hV huexp
    hprime hmax ht hhits hsize hl hlbound

end Problem337.RandomProducts

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_SampleWordTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337.RandomProducts

/-- The finite-set word model agrees exactly with independent samples in the alphabet subtype. -/
theorem typed_sample_event_card {α : Type*} [DecidableEq α]
    (P : Finset α) (t : ℕ) (R : (Fin t → α) → Prop) [DecidablePred R] :
    Fintype.card {f : Fin t → P // R (fun i => (f i : α))} =
      ((sampleWords P t).filter R).card := by
  classical
  let E : {f : Fin t → P // R (fun i => (f i : α))} ≃
      {f : Fin t → α // f ∈ (sampleWords P t).filter R} := {
    toFun := fun f => ⟨fun i => (f.1 i : α), Finset.mem_filter.mpr
      ⟨Fintype.mem_piFinset.mpr (fun i => (f.1 i).property), f.2⟩⟩
    invFun := fun f => ⟨fun i => ⟨f.1 i,
      Fintype.mem_piFinset.mp (Finset.mem_filter.mp f.2).1 i⟩,
      (Finset.mem_filter.mp f.2).2⟩
    left_inv := by
      intro f
      apply Subtype.ext
      funext i
      apply Subtype.ext
      rfl
    right_inv := by
      intro f
      apply Subtype.ext
      rfl }
  simpa only [Fintype.card_coe] using Fintype.card_congr E

/-- Reindexing a finite sample index type preserves all product-dependent event counts. -/
theorem typed_product_event_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finset ℕ) (R : ℕ → Prop) [DecidablePred R] :
    Fintype.card {f : ι → P // R (∏ i, (f i : ℕ))} =
      ((sampleWords P (Fintype.card ι)).filter (fun f => R (∏ i, f i))).card := by
  classical
  let e := Fintype.equivFin ι
  let E : (ι → P) ≃ (Fin (Fintype.card ι) → P) := Equiv.piCongrLeft' (fun _ => P) e
  have hprod : ∀ f : ι → P, (∏ j, ((E f) j : ℕ)) = ∏ i, (f i : ℕ) := by
    intro f
    change (∏ j, (f (e.symm j) : ℕ)) = ∏ i, (f i : ℕ)
    exact e.symm.prod_comp (fun i => (f i : ℕ))
  have hcard : Fintype.card {f : ι → P // R (∏ i, (f i : ℕ))} =
      Fintype.card {f : Fin (Fintype.card ι) → P // R (∏ i, (f i : ℕ))} := by
    apply Fintype.card_congr
    exact E.subtypeEquiv (fun f => by rw [hprod])
  exact hcard.trans (typed_sample_event_card P (Fintype.card ι) (fun f => R (∏ i, f i)))

/-- Normalized version, suitable for an exposed block of independent typed samples. -/
theorem typed_product_event_probability {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finset ℕ) (R : ℕ → Prop) [DecidablePred R] :
    (Fintype.card {f : ι → P // R (∏ i, (f i : ℕ))} : ℝ) /
        (Fintype.card (ι → P) : ℝ) =
      (((sampleWords P (Fintype.card ι)).filter (fun f => R (∏ i, f i))).card : ℝ) /
        (P.card : ℝ) ^ (Fintype.card ι) := by
  rw [typed_product_event_card]
  simp only [Fintype.card_fun, Fintype.card_coe, Nat.cast_pow]

end Problem337.RandomProducts

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RandomGcdMarginal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337.RandomProducts

/-- Typed-sample form of the concrete reduced-modulus exceptional-event bound. -/
theorem random_gcd_typed_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finset ℕ) (u l : ℕ) (S V : ℝ)
    (hP : P.Nonempty) (hS : 2 ≤ S) (hV : 0 ≤ V) (hVS : V ≤ S)
    (huexp : (u : ℝ) = Real.exp V) (hprime : ∀ p ∈ P, Nat.Prime p)
    (hinterval : ∀ p ∈ P, S ^ 100 ≤ (p : ℝ) ∧ (p : ℝ) ≤ S ^ 101)
    (ht : (Fintype.card ι : ℝ) ≤ S) (hsize : S ^ 99 ≤ (P.card : ℝ))
    (hl : 0 < l) (hlbound : (l : ℝ) ≤ Real.exp (V / 200)) :
    (Fintype.card {f : ι → P //
      ((u / Nat.gcd (l * ∏ i, (f i : ℕ)) u : ℕ) : ℝ) < Real.exp (9 * V / 10)} : ℝ) /
        (Fintype.card (ι → P) : ℝ) ≤ Real.exp (-V / 20) := by
  rw [typed_product_event_probability P
    (fun n => ((u / Nat.gcd (l * n) u : ℕ) : ℝ) < Real.exp (9 * V / 10))]
  exact random_gcd_exception_bound_wide P (Fintype.card ι) u l S V
    hP hS hV hVS huexp hprime hinterval ht hsize hl hlbound

end Problem337.RandomProducts

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_HammingException
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- The Hamming-distance generating polynomial of a Boolean cube. -/
theorem sum_pow_hammingDist {m : ℕ} (x : Fin m → Bool) (t : ℝ) :
    (∑ y : Fin m → Bool, t ^ hammingDist x y) = (1 + t) ^ m := by
  have hweight (y : Fin m → Bool) :
      t ^ hammingDist x y = ∏ i : Fin m, if x i ≠ y i then t else 1 := by
    rw [hammingDist, ← Finset.prod_filter]
    simp
  simp_rw [hweight]
  rw [← Fintype.prod_sum (fun i (b : Bool) => if x i ≠ b then t else 1)]
  have hcoordinate (i : Fin m) :
      (∑ b : Bool, if x i ≠ b then t else 1) = 1 + t := by
    cases x i <;> simp [add_comm]
  simp_rw [hcoordinate]
  simp

/-- The exact exponential moment for uniformly counted pairs of Boolean strings. -/
theorem sum_pairs_pow_hammingDist (m : ℕ) (t : ℝ) :
    (∑ xy : (Fin m → Bool) × (Fin m → Bool), t ^ hammingDist xy.1 xy.2) =
      (2 * (1 + t)) ^ m := by
  rw [Fintype.sum_prod_type (fun xy : (Fin m → Bool) × (Fin m → Bool) => t ^ hammingDist xy.1 xy.2)]
  simp_rw [sum_pow_hammingDist]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [mul_pow]


/-- A numerical Chernoff estimate with the constants used in the manuscript. -/
theorem hamming_chernoff_factor (m : ℕ) :
    (2 : ℝ) ^ ((m : ℝ) / 4) * (3 / 4 : ℝ) ^ m ≤
      Real.exp (-(m : ℝ) / 16) := by
  have hpow : (3 / 4 : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log (3 / 4)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), hpow, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hlog2 : Real.log 2 ≤ (3 / 4 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hlog34 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 4)
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith

/-- Fewer than one quarter differing coordinates is an exponentially small
fraction of all ordered pairs of Boolean strings. -/
theorem hamming_exception_count (m : ℕ) :
    ((Finset.univ.filter (fun xy : (Fin m → Bool) × (Fin m → Bool) =>
      (hammingDist xy.1 xy.2 : ℝ) < (m : ℝ) / 4)).card : ℝ) ≤
      (4 : ℝ) ^ m * Real.exp (-(m : ℝ) / 16) := by
  classical
  let E := Finset.univ.filter (fun xy : (Fin m → Bool) × (Fin m → Bool) =>
    (hammingDist xy.1 xy.2 : ℝ) < (m : ℝ) / 4)
  let C : ℝ := (2 : ℝ) ^ ((m : ℝ) / 4)
  have hweight (xy : (Fin m → Bool) × (Fin m → Bool)) (hxy : xy ∈ E) :
      (1 : ℝ) ≤ C * (1 / 2 : ℝ) ^ hammingDist xy.1 xy.2 := by
    have hd := (Finset.mem_filter.mp hxy).2
    have hp : (2 : ℝ) ^ hammingDist xy.1 xy.2 ≤ C := by
      exact (Real.rpow_natCast 2 _).symm ▸
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hd.le
    rw [one_div_pow, mul_one_div]
    exact (le_div_iff₀ (by positivity)).2 (by simpa using hp)
  have hcount : (E.card : ℝ) ≤ C * (3 : ℝ) ^ m := by
    calc
      (E.card : ℝ) = ∑ xy ∈ E, (1 : ℝ) := by simp
      _ ≤ ∑ xy ∈ E, C * (1 / 2 : ℝ) ^ hammingDist xy.1 xy.2 :=
        Finset.sum_le_sum hweight
      _ ≤ ∑ xy : (Fin m → Bool) × (Fin m → Bool),
          C * (1 / 2 : ℝ) ^ hammingDist xy.1 xy.2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E)
        intro xy hxy hnot
        positivity
      _ = C * (3 : ℝ) ^ m := by
        rw [← Finset.mul_sum, sum_pairs_pow_hammingDist]
        norm_num
  have hmain : C * (3 : ℝ) ^ m ≤ (4 : ℝ) ^ m * Real.exp (-(m : ℝ) / 16) := by
    calc
      C * (3 : ℝ) ^ m = (4 : ℝ) ^ m * (C * (3 / 4 : ℝ) ^ m) := by
        rw [← mul_assoc, mul_comm ((4 : ℝ) ^ m) C, mul_assoc, ← mul_pow]
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left (hamming_chernoff_factor m) (by positivity)
  exact hcount.trans hmain

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_SecondMomentAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

theorem norm_sum_sq_eq_sum_pair {I : Type*} [Fintype I] (z : I → ℂ) :
    ‖∑ i, z i‖ ^ 2 = ∑ ij : I × I, (z ij.1 * star (z ij.2)).re := by
  rw [Fintype.sum_prod_type]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.re_sum, Complex.im_sum,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
    mul_neg, sub_neg_eq_add]
  simp_rw [Finset.sum_add_distrib]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]

/-- The numerical absorption at the end of the random-products argument. -/
theorem random_second_moment_absorption (m V : ℝ) (hlarge : 50 ≤ min m V) :
    Real.exp (-m / 16) + Real.exp (-V / 20) + Real.exp (-V / 5) ≤
      Real.exp (-min m V / 100) := by
  let w := min m V
  have hwm : w ≤ m := min_le_left _ _
  have hwV : w ≤ V := min_le_right _ _
  have hw : 50 ≤ w := hlarge
  have h1 : Real.exp (-m / 16) ≤ Real.exp (-w / 20) := by
    apply Real.exp_le_exp.mpr
    dsimp [w] at *
    nlinarith
  have h2 : Real.exp (-V / 20) ≤ Real.exp (-w / 20) := by
    apply Real.exp_le_exp.mpr
    linarith
  have h3 : Real.exp (-V / 5) ≤ Real.exp (-w / 20) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hlog3 : Real.log 3 ≤ (2 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at h ⊢
    exact h
  have habsorb : 3 * Real.exp (-w / 20) ≤ Real.exp (-w / 100) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 3), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  exact (by linarith : Real.exp (-m / 16) + Real.exp (-V / 20) +
    Real.exp (-V / 5) ≤ 3 * Real.exp (-w / 20)).trans habsorb

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_UniformSecondMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

theorem norm_expect_sq_eq_expect_pairs {I : Type*} [Fintype I] (z : I → ℂ) :
    ‖𝔼 i, z i‖ ^ 2 = 𝔼 ij : I × I, (z ij.1 * star (z ij.2)).re := by
  simp only [Fintype.expect_eq_sum_div_card, norm_div, norm_natCast]
  rw [div_pow, norm_sum_sq_eq_sum_pair]
  simp only [Fintype.card_prod, Nat.cast_mul, pow_two]

theorem uniform_second_moment_identity {Ω I : Type*} [Fintype Ω] [Fintype I]
    (z : Ω → I → ℂ) :
    (𝔼 ω, ‖𝔼 i, z ω i‖ ^ 2) =
      𝔼 ij : I × I, (𝔼 ω, z ω ij.1 * star (z ω ij.2)).re := by
  simp_rw [norm_expect_sq_eq_expect_pairs]
  rw [Finset.expect_comm]
  congr 1
  funext ij
  exact (map_expect (Complex.reCLM.toLinearMap.restrictScalars ℚ≥0) (fun ω => z ω ij.1 * star (z ω ij.2)) Finset.univ).symm

/-- Uniform finite-average version of the Hamming second-moment reduction. -/
theorem uniform_boolean_second_moment_bound {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (m : ℕ) (z : Ω → (Fin m → Bool) → ℂ)
    (hz : ∀ ω i, ‖z ω i‖ ≤ 1) (δ : ℝ) (hδ : 0 ≤ δ)
    (hgood : ∀ i j, (m : ℝ) / 4 ≤ (hammingDist i j : ℝ) →
      ‖𝔼 ω, z ω i * star (z ω j)‖ ≤ δ) :
    (𝔼 ω, ‖𝔼 i, z ω i‖ ^ 2) ≤ Real.exp (-(m : ℝ) / 16) + δ := by
  classical
  let E := Finset.univ.filter (fun ij : (Fin m → Bool) × (Fin m → Bool) =>
    (hammingDist ij.1 ij.2 : ℝ) < (m : ℝ) / 4)
  have hall (i j : Fin m → Bool) : ‖𝔼 ω, z ω i * star (z ω j)‖ ≤ 1 := by
    calc
      _ ≤ 𝔼 ω, ‖z ω i * star (z ω j)‖ := RCLike.norm_expect_le (K := ℂ)
      _ ≤ 𝔼 _ω : Ω, (1 : ℝ) := by
        apply Finset.expect_le_expect
        intro ω hω
        rw [norm_mul, norm_star]
        nlinarith [hz ω i, hz ω j, norm_nonneg (z ω i), norm_nonneg (z ω j)]
      _ = 1 := Fintype.expect_const 1
  have hexc : (E.card : ℝ) ≤ (4 : ℝ) ^ m * Real.exp (-(m : ℝ) / 16) :=
    hamming_exception_count m
  have hcard : (Fintype.card ((Fin m → Bool) × (Fin m → Bool)) : ℝ) = (4 : ℝ) ^ m := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [← mul_pow]
    norm_num
  rw [uniform_second_moment_identity]
  calc
    (𝔼 ij : (Fin m → Bool) × (Fin m → Bool),
        (𝔼 ω, z ω ij.1 * star (z ω ij.2)).re) ≤
        𝔼 ij : (Fin m → Bool) × (Fin m → Bool),
          ((if ij ∈ E then 1 else 0) + δ : ℝ) := by
      apply Finset.expect_le_expect
      intro ij hij
      by_cases hb : ij ∈ E
      · simp only [ite_eq_left hb]
        exact (Complex.re_le_norm _).trans ((hall _ _).trans (by linarith))
      · simp only [ite_eq_right hb, zero_add]
        apply (Complex.re_le_norm _).trans (hgood _ _ ?_)
        simpa only [E, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hb
    _ = (E.card : ℝ) / (4 : ℝ) ^ m + δ := by
      rw [Finset.expect_add_distrib, expect_finset_indicator, Fintype.expect_const, hcard]
    _ ≤ Real.exp (-(m : ℝ) / 16) + δ := by
      have hdiv : (E.card : ℝ) / (4 : ℝ) ^ m ≤ Real.exp (-(m : ℝ) / 16) :=
        (div_le_iff₀ (by positivity)).2 (by simpa only [mul_comm] using hexc)
      linarith

/-- Uniform-mean final random estimate, directly matching the second moment
of the sampled Boolean-product exponential average. -/
theorem uniform_boolean_random_second_moment_bound {Ω : Type*}
    [Fintype Ω] [Nonempty Ω] (m : ℕ) (V : ℝ)
    (z : Ω → (Fin m → Bool) → ℂ) (hz : ∀ ω i, ‖z ω i‖ ≤ 1)
    (hlarge : 50 ≤ min (m : ℝ) V)
    (hgood : ∀ i j, (m : ℝ) / 4 ≤ (hammingDist i j : ℝ) →
      ‖𝔼 ω, z ω i * star (z ω j)‖ ≤ Real.exp (-V / 20) + Real.exp (-V / 5)) :
    (𝔼 ω, ‖𝔼 i, z ω i‖ ^ 2) ≤ Real.exp (-min (m : ℝ) V / 100) := by
  have h := uniform_boolean_second_moment_bound m z hz
    (Real.exp (-V / 20) + Real.exp (-V / 5)) (by positivity) hgood
  exact h.trans (by simpa only [add_assoc] using
    random_second_moment_absorption (m : ℝ) V hlarge)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RandomSecondMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337.RandomProducts

theorem sampledPhase_correlation {m : ℕ} {P : Finset ℕ} (u l : ℕ) [NeZero u]
    (p : (Fin m × Bool) → P) (I J : Fin m → Bool) :
    sampledPhase u l p I * star (sampledPhase u l p J) =
      ZMod.stdAddChar (((l * sampledProduct p I : ℕ) : ZMod u) -
        ((l * sampledProduct p J : ℕ) : ZMod u)) := by
  unfold sampledPhase
  rw [Complex.star_def, ← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
  simp only [sub_eq_add_neg]

open RandomExposure

theorem sampledProduct_split_first {m : ℕ} {P : Finset ℕ}
    (I : Fin m → Bool) (A B : Finset (Fin m)) (hAB : Disjoint A B)
    (a : selectedLabels I A → P) (b : selectedLabels I B → P)
    (c : ExposedLabel I A B → P) :
    sampledProduct ((splitSampleExposedFirst (selectedLabels I A) (selectedLabels I B)
      (selectedLabels_disjoint I hAB)).symm (c, (a,b))) I =
      exposedFirstProduct (fun p : P => (p : ℕ)) I A B c *
        (∏ z, (a z : ℕ)) * (∏ z, (b z : ℕ)) := by
  unfold sampledProduct
  rw [splitSampleExposedFirst_symm]
  rw [selected_product_factorization I A B hAB
    (fun z => (((splitSample (selectedLabels I A) (selectedLabels I B)
      (selectedLabels_disjoint I hAB)).symm (a,b,c)) z : ℕ))]
  rw [exposed_first_factor_formula (fun p : P => (p : ℕ)) I A B hAB a b c]
  congr 1
  · congr 1
    rw [product_selectedLabels I A (fun z => (((splitSample (selectedLabels I A)
      (selectedLabels I B) (selectedLabels_disjoint I hAB)).symm (a,b,c)) z : ℕ))]
    apply Finset.prod_congr rfl
    intro z hz
    simp
  · rw [product_selectedLabels I B (fun z => (((splitSample (selectedLabels I A)
      (selectedLabels I B) (selectedLabels_disjoint I hAB)).symm (a,b,c)) z : ℕ))]
    apply Finset.prod_congr rfl
    intro z hz
    simp

theorem sampledProduct_split_other {m : ℕ} {P : Finset ℕ}
    (I J : Fin m → Bool) (A B : Finset (Fin m)) (hAB : Disjoint A B)
    (hA : ∀ i ∈ A, I i ≠ J i) (hB : ∀ i ∈ B, I i ≠ J i)
    (a : selectedLabels I A → P) (b : selectedLabels I B → P)
    (c : ExposedLabel I A B → P) :
    sampledProduct ((splitSampleExposedFirst (selectedLabels I A) (selectedLabels I B)
      (selectedLabels_disjoint I hAB)).symm (c, (a,b))) J =
      exposedOtherProduct (fun p : P => (p : ℕ)) I J A B hA hB c := by
  unfold sampledProduct
  rw [splitSampleExposedFirst_symm]
  exact exposed_other_factor_formula _ I J A B hAB hA hB a b c

/-- The exact sample-splitting interface for one pair of Boolean words. -/
theorem sampled_pair_bound_of_good_bad {m : ℕ} {P : Finset ℕ}
    (hne : P.Nonempty) (I J : Fin m → Bool) (A B : Finset (Fin m))
    (hAB : Disjoint A B) (hA : ∀ i ∈ A, I i ≠ J i) (hB : ∀ i ∈ B, I i ≠ J i)
    (u l : ℕ) [NeZero u] (bad : Finset (ExposedLabel I A B → P))
    (ε δ : ℝ) (hδ : 0 ≤ δ)
    (hbad : (bad.card : ℝ) / Fintype.card (ExposedLabel I A B → P) ≤ ε)
    (hgood : ∀ c, c ∉ bad →
      ‖𝔼 a : selectedLabels I A → P, 𝔼 b : selectedLabels I B → P,
        ZMod.stdAddChar
          (((l * exposedFirstProduct (fun p : P => (p : ℕ)) I A B c *
            (∏ z, (a z : ℕ)) * (∏ z, (b z : ℕ)) : ℕ) : ZMod u) -
            ((l * exposedOtherProduct (fun p : P => (p : ℕ)) I J A B hA hB c : ℕ) : ZMod u))‖ ≤ δ) :
    ‖𝔼 p : (Fin m × Bool) → P,
      ZMod.stdAddChar (((l * sampledProduct p I : ℕ) : ZMod u) -
        ((l * sampledProduct p J : ℕ) : ZMod u))‖ ≤ ε + δ := by
  let : Nonempty P := hne.to_subtype
  apply correlation_of_exposed_products
    (splitSampleExposedFirst (selectedLabels I A) (selectedLabels I B)
      (selectedLabels_disjoint I hAB))
    (fun p => sampledProduct p I) (fun p => sampledProduct p J)
    (exposedFirstProduct (fun p : P => (p : ℕ)) I A B)
    (exposedOtherProduct (fun p : P => (p : ℕ)) I J A B hA hB)
    (fun a => ∏ z, (a z : ℕ)) (fun b => ∏ z, (b z : ℕ))
    (fun c a b => sampledProduct_split_first I A B hAB a b c)
    (fun c a b => sampledProduct_split_other I J A B hAB hA hB a b c)
    u l bad ε δ hδ hbad hgood

/-- The actual labelled-prime-product random quantity, reduced to separated-pair
correlations. The remaining hypothesis is precisely the output of exposure. -/
theorem sampled_product_second_moment_of_correlations {P : Finset ℕ}
    (hne : P.Nonempty) (m u l : ℕ) [NeZero u] (V : ℝ)
    (hlarge : 50 ≤ min (m : ℝ) V)
    (hpair : ∀ I J : Fin m → Bool,
      (m : ℝ) / 4 ≤ (hammingDist I J : ℝ) →
      ‖𝔼 p : (Fin m × Bool) → P,
        ZMod.stdAddChar (((l * sampledProduct p I : ℕ) : ZMod u) -
          ((l * sampledProduct p J : ℕ) : ZMod u))‖ ≤
        Real.exp (-V / 20) + Real.exp (-V / 5)) :
    (𝔼 p : (Fin m × Bool) → P, ‖𝔼 I : Fin m → Bool, sampledPhase u l p I‖ ^ 2) ≤
      Real.exp (-min (m : ℝ) V / 100) := by
  let : Nonempty P := hne.to_subtype
  apply uniform_boolean_random_second_moment_bound m V (sampledPhase u l)
    (fun p I => (norm_sampledPhase u l p I).le) hlarge
  intro I J hIJ
  simpa only [sampledPhase_correlation] using hpair I J hIJ

/-- The actual Hamming condition supplies the two fresh blocks used by exposure. -/
theorem sampled_pair_fresh_blocks {S V : ℝ} (hS : 1 < S)
    (hV : 100000 * Real.log S ≤ V) (hVS : V ≤ S)
    (I J : Fin (blockLength S) → Bool)
    (hIJ : (blockLength S : ℝ) / 4 ≤ (hammingDist I J : ℝ)) :
    ∃ A B : Finset (Fin (blockLength S)), Disjoint A B ∧
      A.card = freshLength S V ∧ B.card = freshLength S V ∧
      (∀ i ∈ A, I i ≠ J i) ∧ (∀ i ∈ B, I i ≠ J i) := by
  apply exists_differing_blocks
  apply fresh_coordinates_fit hS hV hVS
  have hreal : (blockLength S : ℝ) ≤ 4 * (hammingDist I J : ℝ) := by linarith
  exact_mod_cast hreal

/-- The exposed factor uses at most the full first word's number of coordinates. -/
theorem exposed_coordinate_card_le {S : ℝ} (hS : Real.exp 1 ≤ S)
    (A B : Finset (Fin (blockLength S))) :
    (Fintype.card ↥(Finset.univ \ (A ∪ B)) : ℝ) ≤ S := by
  have hcard : (Finset.univ \ (A ∪ B)).card ≤ blockLength S := by
    simpa using Finset.card_le_card (Finset.sdiff_subset :
      (Finset.univ \ (A ∪ B)) ⊆ Finset.univ)
  have hreal : ((Finset.univ \ (A ∪ B)).card : ℝ) ≤ blockLength S := by
    exact_mod_cast hcard
  simpa only [Fintype.card_coe] using hreal.trans (blockLength_le_self hS)

/-- The parameter range guarantees the fixed numeric threshold for error absorption. -/
theorem random_min_large {S V : ℝ} (hS : 2 ≤ S)
    (hV : 100000 * Real.log S ≤ V) (hVS : V ≤ S) :
    50 ≤ min (blockLength S : ℝ) V := by
  apply le_min
  · have h := blockLength_large (by linarith : 1 < S) hV hVS
    have : (100000 : ℝ) ≤ blockLength S := by exact_mod_cast h
    linarith
  · have htwo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at htwo
    have hlog := htwo.trans (Real.log_le_log (by norm_num) hS)
    nlinarith

/-- The actual exposed first-word factor has an exponentially small bad-gcd event.
Unused exposed labels are eliminated by the exact uniform-coordinate marginal law. -/
theorem exposed_bad_gcd_fraction (S V : ℝ) (hS : 3 ≤ S)
    (hV : 100000 * Real.log S ≤ V) (hVS : V ≤ S)
    (P : Finset ℕ) (hP : P.Nonempty) (hprime : ∀ p ∈ P, Nat.Prime p)
    (hinterval : ∀ p ∈ P, S ^ 100 ≤ (p : ℝ) ∧ (p : ℝ) ≤ S ^ 101)
    (hsize : S ^ 99 ≤ (P.card : ℝ)) (u l : ℕ)
    (huexp : (u : ℝ) = Real.exp V) (hl : 0 < l)
    (hlbound : (l : ℝ) ≤ Real.exp (V / 200))
    (I : Fin (blockLength S) → Bool) (A B : Finset (Fin (blockLength S))) :
    ((Finset.univ.filter (fun c : ExposedLabel I A B → P =>
      ((u / Nat.gcd (l * exposedFirstProduct (fun p : P => (p : ℕ)) I A B c) u : ℕ) : ℝ)
        < Real.exp (9 * V / 10))).card : ℝ) /
      Fintype.card (ExposedLabel I A B → P) ≤ Real.exp (-V / 20) := by
  classical
  let : Nonempty P := hP.to_subtype
  let e : ↥(Finset.univ \ (A ∪ B)) ↪ ExposedLabel I A B :=
    ⟨outsideSelectedLabel I A B, outsideSelectedLabel_injective I A B⟩
  let R : (↥(Finset.univ \ (A ∪ B)) → P) → Prop := fun a =>
    ((u / Nat.gcd (l * ∏ i, (a i : ℕ)) u : ℕ) : ℝ) < Real.exp (9 * V / 10)
  change ((Finset.univ.filter (fun c : ExposedLabel I A B → P =>
    R (fun k => c (e k)))).card : ℝ) / _ ≤ _
  rw [injective_coordinate_event_fraction e R]
  have hV0 : 0 ≤ V := by
    have := Real.log_pos (show 1 < S by linarith)
    nlinarith
  have hSexp : Real.exp 1 ≤ S := Real.exp_one_lt_three.le.trans hS
  have h := random_gcd_typed_bound (ι := ↥(Finset.univ \ (A ∪ B)))
    P u l S V hP (by linarith) hV0 hVS huexp hprime hinterval
    (exposed_coordinate_card_le hSexp A B) hsize hl hlbound
  simpa only [Fintype.card_subtype, R] using h

/-- The complete random-product second-moment estimate for labelled independent
prime samples, including Hamming exceptions, bad gcds, and bilinear cancellation. -/
theorem sampled_product_second_moment_bound
    (S V : ℝ) (hS : 3 ≤ S) (hV : 100000 * Real.log S ≤ V) (hVS : V ≤ S)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, Nat.Prime p)
    (hinterval : ∀ p ∈ P, S ^ 100 ≤ (p : ℝ) ∧ (p : ℝ) ≤ S ^ 101)
    (hsize : S ^ 99 ≤ (P.card : ℝ)) (u l : ℕ) [NeZero u]
    (huexp : (u : ℝ) = Real.exp V) (hl : 0 < l)
    (hlbound : (l : ℝ) ≤ Real.exp (V / 200)) :
    (𝔼 p : (Fin (blockLength S) × Bool) → P,
      ‖𝔼 I : Fin (blockLength S) → Bool, sampledPhase u l p I‖ ^ 2) ≤
        Real.exp (-min (blockLength S : ℝ) V / 100) := by
  classical
  have hS2 : 2 ≤ S := by linarith
  have hSpos : 0 < S := by linarith
  have hcardpos : 0 < (P.card : ℝ) := lt_of_lt_of_le (by positivity) hsize
  have hP : P.Nonempty := Finset.card_pos.mp (by exact_mod_cast hcardpos)
  have hu : 0 < u := Nat.pos_of_ne_zero (NeZero.ne u)
  apply sampled_product_second_moment_of_correlations hP _ u l V
    (random_min_large hS2 hV hVS)
  intro I J hIJ
  obtain ⟨A, B, hAB, hAs, hBs, hA, hB⟩ :=
    sampled_pair_fresh_blocks (by linarith : 1 < S) hV hVS I J hIJ
  let bad : Finset (ExposedLabel I A B → P) := Finset.univ.filter fun c =>
    ((u / Nat.gcd (l * exposedFirstProduct (fun p : P => (p : ℕ)) I A B c) u : ℕ) : ℝ)
      < Real.exp (9 * V / 10)
  apply sampled_pair_bound_of_good_bad hP I J A B hAB hA hB u l bad
    (Real.exp (-V / 20)) (Real.exp (-V / 5)) (Real.exp_pos _).le
  · exact exposed_bad_gcd_fraction S V hS hV hVS P hP hprime hinterval hsize
      u l huexp hl hlbound I A B
  · intro c hc
    have hq : Real.exp ((9 / 10 : ℝ) * V) ≤
        ((u / Nat.gcd (l * exposedFirstProduct (fun p : P => (p : ℕ)) I A B c) u : ℕ) : ℝ) := by
      have hn : ¬ ((u / Nat.gcd
          (l * exposedFirstProduct (fun p : P => (p : ℕ)) I A B c) u : ℕ) : ℝ) <
          Real.exp (9 * V / 10) := by simpa only [bad, Finset.mem_filter,
            Finset.mem_univ, true_and] using hc
      simpa only [show (9 / 10 : ℝ) * V = 9 * V / 10 by ring] using le_of_not_gt hn
    have hAc : Fintype.card (selectedLabels I A) = freshLength S V := by
      simpa only [Fintype.card_coe, selectedLabels_card] using hAs
    have hBc : Fintype.card (selectedLabels I B) = freshLength S V := by
      simpa only [Fintype.card_coe, selectedLabels_card] using hBs
    exact concrete_good_exposure_expect S V hAc hBc hS2 hV hVS P hprime hsize
      (fun p hp => (hinterval p hp).2)
      (l * exposedFirstProduct (fun p : P => (p : ℕ)) I A B c) u hu
      huexp.le hq ((l * exposedOtherProduct (fun p : P => (p : ℕ)) I J A B hA hB c : ℕ) : ZMod u)

/-- Logarithmic form with `V = log u` and the smaller common frequency range. -/
theorem sampled_product_second_moment_log_bound
    (S : ℝ) (hS : 3 ≤ S) (P : Finset ℕ)
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (hinterval : ∀ p ∈ P, S ^ 100 ≤ (p : ℝ) ∧ (p : ℝ) ≤ S ^ 101)
    (hsize : S ^ 99 ≤ (P.card : ℝ)) (u l : ℕ) [NeZero u]
    (hV : 100000 * Real.log S ≤ Real.log (u : ℝ))
    (hVS : Real.log (u : ℝ) ≤ S) (hl : 0 < l)
    (hlbound : (l : ℝ) ≤ Real.exp (min (blockLength S : ℝ) (Real.log (u : ℝ)) / 200)) :
    (𝔼 p : (Fin (blockLength S) × Bool) → P,
      ‖𝔼 I : Fin (blockLength S) → Bool, sampledPhase u l p I‖ ^ 2) ≤
        Real.exp (-min (blockLength S : ℝ) (Real.log (u : ℝ)) / 100) := by
  apply sampled_product_second_moment_bound S (Real.log (u : ℝ)) hS hV hVS
    P hprime hinterval hsize u l
  · exact (Real.exp_log (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne u))).symm
  · exact hl
  · exact hlbound.trans (Real.exp_le_exp.mpr
      (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)))

end Problem337.RandomProducts

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RandomCommonRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.RandomProducts

/-- The complete random moment theorem in the total normalized-average interface. -/
theorem sampledMean_second_moment_bound
    (S : ℝ) (hS : 3 ≤ S) (P : Finset ℕ)
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (hinterval : ∀ p ∈ P, S ^ 100 ≤ (p : ℝ) ∧ (p : ℝ) ≤ S ^ 101)
    (hsize : S ^ 99 ≤ (P.card : ℝ)) (u l : ℕ) (hu : 0 < u)
    (hV : 100000 * Real.log S ≤ Real.log (u : ℝ))
    (hVS : Real.log (u : ℝ) ≤ S) (hl : 0 < l)
    (hlbound : (l : ℝ) ≤ Real.exp (min (blockLength S : ℝ) (Real.log (u : ℝ)) / 200)) :
    (∑ p : (Fin (blockLength S) × Bool) → P, ‖sampledMean p u l‖ ^ 2) /
      Fintype.card ((Fin (blockLength S) × Bool) → P) ≤
        Real.exp (-min (blockLength S : ℝ) (Real.log (u : ℝ)) / 100) := by
  let : NeZero u := ⟨Nat.ne_of_gt hu⟩
  simpa only [sampledMean_eq, Fintype.expect_eq_sum_div_card] using
    sampled_product_second_moment_log_bound S hS P hprime hinterval hsize u l
      hV hVS hl hlbound

/-- Concrete labelled-prime-product realization. All remaining hypotheses are
finite index bounds and explicit numeric ranges, not moment assumptions. -/
theorem exists_common_sampled_realization :
    ∃ N : ℕ, ∀ (S : ℝ) (P : Finset ℕ) (J : Type)
      (tests : Finset J) (level : J → Finset ℕ) (X : J → ℝ)
      (freq : Finset ℕ) (terminalFreq : ℕ → Finset ℕ) (terminal : Finset ℕ),
      3 ≤ S →
      (∀ p ∈ P, Nat.Prime p) →
      (∀ p ∈ P, S ^ 100 ≤ (p : ℝ) ∧ (p : ℝ) ≤ S ^ 101) →
      S ^ 99 ≤ (P.card : ℝ) →
      500000 ≤ (blockLength S : ℝ) →
      (tests.card : ℝ) ≤ (blockLength S : ℝ) →
      (∀ j ∈ tests, 0 < X j) →
      (∀ j ∈ tests, ((level j).card : ℝ) ≤ X j) →
      (freq.card : ℝ) ≤ Real.exp (4 * (blockLength S : ℝ) / 10000) →
      (∀ j ∈ tests, ∀ u ∈ level j, 0 < u ∧
        100000 * Real.log S ≤ Real.log (u : ℝ) ∧ Real.log (u : ℝ) ≤ S ∧
        (9999 / 10000 : ℝ) * (blockLength S : ℝ) ≤ Real.log (u : ℝ)) →
      (∀ j ∈ tests, ∀ u ∈ level j, ∀ l ∈ freq, 0 < l ∧
        (l : ℝ) ≤ Real.exp (min (blockLength S : ℝ) (Real.log (u : ℝ)) / 200)) →
      (∀ u ∈ terminal, max N 1 ≤ u ∧
        100000 * Real.log S ≤ Real.log (u : ℝ) ∧
        Real.log (u : ℝ) ≤ min (blockLength S : ℝ) S) →
      (∀ u ∈ terminal, ((terminalFreq u).card : ℝ) ≤
        Real.exp (4 * Real.log (u : ℝ) / 10000)) →
      (∀ u ∈ terminal, ∀ l ∈ terminalFreq u, 0 < l ∧
        (l : ℝ) ≤ Real.exp (Real.log (u : ℝ) / 200)) →
      ∃ f : Fin 1000 → ((Fin (blockLength S) × Bool) → P),
        (∀ j ∈ tests,
          (((level j).filter (fun u => ∃ l ∈ freq,
            Real.exp (-3 * (blockLength S : ℝ) / 10000) <
              ‖sampledMean (f 0) u l‖)).card : ℝ) ≤
                X j * Real.exp (-(blockLength S : ℝ) / 1000)) ∧
        ∀ u ∈ terminal, ∃ i : Fin 1000, ∀ l ∈ terminalFreq u,
          ‖sampledMean (f i) u l‖ ≤ Real.exp (-3 * Real.log (u : ℝ) / 10000) := by
  classical
  obtain ⟨N, hN⟩ := FourierCommonRealization.exists_common_fourier_realization
  refine ⟨N, ?_⟩
  intro S P J tests level X freq terminalFreq terminal hS hp hi hs hm ht hX hlevel
    hf hmid hmf hterminal htf htl
  have hcard : 0 < (P.card : ℝ) := lt_of_lt_of_le (by positivity) hs
  have hP : P.Nonempty := Finset.card_pos.mp (by exact_mod_cast hcard)
  let : Nonempty P := hP.to_subtype
  apply hN ((Fin (blockLength S) × Bool) → P) J tests level X
    (blockLength S : ℝ) freq terminalFreq sampledMean
    (fun u => min (blockLength S : ℝ) (Real.log (u : ℝ))) terminal
    hm ht hX hlevel hf
  · intro j hj u hu
    apply le_min
    · have : (0 : ℝ) ≤ blockLength S := Nat.cast_nonneg _
      nlinarith
    · exact (hmid j hj u hu).2.2.2
  · intro j hj u hu l hl
    exact sampledMean_second_moment_bound S hS P hp hi hs u l
      (hmid j hj u hu).1 (hmid j hj u hu).2.1 (hmid j hj u hu).2.2.1
      (hmf j hj u hu l hl).1 (hmf j hj u hu l hl).2
  · intro u hu
    exact (le_max_left N 1).trans (hterminal u hu).1
  · exact htf
  · intro u hu l hl
    have hmin : min (blockLength S : ℝ) (Real.log (u : ℝ)) = Real.log (u : ℝ) :=
      min_eq_right ((hterminal u hu).2.2.trans (min_le_left _ _))
    have hu0 : 0 < u := by have := (le_max_right N 1).trans (hterminal u hu).1; omega
    have hbound := (htl u hu l hl).2
    rw [← hmin] at hbound
    have h := sampledMean_second_moment_bound S hS P hp hi hs u l hu0
      (hterminal u hu).2.1 ((hterminal u hu).2.2.trans (min_le_right _ _))
      (htl u hu l hl).1 hbound
    simpa only [hmin] using h

end Problem337.RandomProducts

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RandomResidueRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.RandomProducts

/-- The exact, normalized random Fourier bound gives the half-mass
small-remainder bound. Indexed repeated products are retained. -/
theorem sampled_remainder_count_of_fourier {m : ℕ} {P : Finset ℕ}
    (p : (Fin m × Bool) → P) (u : ℕ) (hu : 0 < u) (w : ℝ)
    (hw : 10000 * Real.log 65536 ≤ w)
    (hfourier : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊Real.exp (4 * w / 10000)⌋₊ →
      ‖sampledMean p u l‖ ≤ Real.exp (-3 * w / 10000)) :
    (Real.exp (-w / 10000) / 2) * (2 : ℝ) ^ m ≤
      ((Finset.univ.filter (fun I : Fin m → Bool =>
        (sampledRemainder p u I : ℝ) < Real.exp (-w / 10000) * u)).card : ℝ) := by
  classical
  let : NeZero u := ⟨Nat.ne_of_gt hu⟩
  have hsmall : Real.exp (-w / 10000) ≤ 1 / 65536 := by
    calc
      Real.exp (-w / 10000) ≤ Real.exp (-Real.log 65536) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hcube : Real.exp (-w / 10000) ^ 3 = Real.exp (-3 * w / 10000) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hfourth : 1 / Real.exp (-w / 10000) ^ 4 = Real.exp (4 * w / 10000) := by
    rw [← Real.exp_nat_mul, one_div, ← Real.exp_neg]
    congr 1
    norm_num
    ring
  have h := ceiling_remainder_count_of_character_expect_automatic
    (sampledProduct p) (Real.exp (-w / 10000)) (Real.exp_pos _) hsmall
    (fun l hl hlH => by
      rw [hfourth] at hlH
      rw [hcube]
      simpa only [sampledMean_eq, sampledPhase, Nat.cast_mul] using hfourier l hl hlH)
  convert h using 1 <;> simp [sampledRemainder]
  congr 1

/-- Every Fourier-good terminal modulus has an actual Boolean product with
remainder smaller than the required power of that modulus. -/
theorem exists_sampled_terminal_remainder {m : ℕ} {P : Finset ℕ}
    (p : (Fin m × Bool) → P) (u : ℕ) (hu : 0 < u)
    (hw : 10000 * Real.log 65536 ≤ Real.log (u : ℝ))
    (hfourier : ∀ l : ℕ, 1 ≤ l →
      l ≤ ⌊Real.exp (4 * Real.log (u : ℝ) / 10000)⌋₊ →
      ‖sampledMean p u l‖ ≤ Real.exp (-3 * Real.log (u : ℝ) / 10000)) :
    ∃ I : Fin m → Bool,
      (sampledRemainder p u I : ℝ) < (u : ℝ) ^ (9999 / 10000 : ℝ) := by
  classical
  have h := sampled_remainder_count_of_fourier p u hu (Real.log (u : ℝ)) hw hfourier
  have hc : 0 < (Finset.univ.filter (fun I : Fin m → Bool =>
      (sampledRemainder p u I : ℝ) <
        Real.exp (-Real.log (u : ℝ) / 10000) * u)).card := by
    have hpos : (0 : ℝ) < (Real.exp (-Real.log (u : ℝ) / 10000) / 2) * (2 : ℝ) ^ m := by positivity
    exact_mod_cast hpos.trans_le h
  obtain ⟨I, hI⟩ := Finset.card_pos.mp hc
  refine ⟨I, ?_⟩
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hpower : Real.exp (-Real.log (u : ℝ) / 10000) * u =
      (u : ℝ) ^ (9999 / 10000 : ℝ) := by
    conv_lhs => rhs; rw [← Real.exp_log huR]
    rw [← Real.exp_add, Real.rpow_def_of_pos huR]
    congr 1
    ring
  simpa only [hpower] using (Finset.mem_filter.mp hI).2


/-- Rational and real ceiling remainder formulas agree exactly. -/
theorem sampledRemainder_eq_real_ceil {m : ℕ} {P : Finset ℕ}
    (p : (Fin m × Bool) → P) (u : ℕ) (hu : 0 < u) (I : Fin m → Bool) :
    sampledRemainder p u I =
      u * ⌈(sampledProduct p I : ℝ) / u⌉₊ - sampledProduct p I := by
  let : NeZero u := ⟨Nat.ne_of_gt hu⟩
  unfold sampledRemainder
  rw [ceiling_remainder_eq_neg_cast_val,
    natural_ceil_residue_eq_neg_zmod_val u (sampledProduct p I) hu]

/-- A sampled rational-ceiling remainder has exactly the same normalized
fractional-part interpretation as the real-ceiling construction. -/
theorem sampledRemainder_lt_iff_fract {m : ℕ} {P : Finset ℕ}
    (p : (Fin m × Bool) → P) (u : ℕ) (hu : 0 < u)
    (I : Fin m → Bool) (δ : ℝ) :
    (sampledRemainder p u I : ℝ) < δ * u ↔
      Int.fract (-(sampledProduct p I : ℝ) / u) < δ := by
  have hrem := sampledRemainder_eq_real_ceil p u hu I
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  rw [← natural_ceil_residue_div_eq_fract_neg u (sampledProduct p I) hu, ← hrem]
  exact (div_lt_iff₀ huR).symm

/-- A common choice of actual prime samples supplies the middle-level
small-remainder counts and covers every prescribed terminal numerator.
All hypotheses are explicit finite size/range conditions. -/
theorem exists_common_sampled_residue_realization_strict :
    ∃ N : ℕ, ∀ (S : ℝ) (P : Finset ℕ) (J : Type)
      (tests : Finset J) (level : J → Finset ℕ) (X : J → ℝ)
      (terminal : Finset ℕ),
      3 ≤ S →
      (∀ p ∈ P, Nat.Prime p) →
      (∀ p ∈ P, S ^ 100 ≤ (p : ℝ) ∧ (p : ℝ) ≤ S ^ 101) →
      S ^ 99 ≤ (P.card : ℝ) →
      500000 ≤ (blockLength S : ℝ) →
      10000 * Real.log 65536 ≤ (blockLength S : ℝ) →
      (tests.card : ℝ) ≤ (blockLength S : ℝ) →
      (∀ j ∈ tests, 0 < X j) →
      (∀ j ∈ tests, ((level j).card : ℝ) ≤ X j) →
      (∀ j ∈ tests, ∀ u ∈ level j, 0 < u ∧ (u : ℝ) ≤ X j ∧
        100000 * Real.log S ≤ Real.log (u : ℝ) ∧ Real.log (u : ℝ) ≤ S ∧
        (9999 / 10000 : ℝ) * (blockLength S : ℝ) ≤ Real.log (u : ℝ)) →
      (∀ u ∈ terminal, max N 1 ≤ u ∧
        100000 * Real.log S ≤ Real.log (u : ℝ) ∧
        Real.log (u : ℝ) ≤ min (blockLength S : ℝ) S ∧
        10000 * Real.log 65536 ≤ Real.log (u : ℝ)) →
      ∃ (f : Fin 1000 → ((Fin (blockLength S) × Bool) → P))
        (exceptional : J → Finset ℕ),
        (∀ j ∈ tests, exceptional j ⊆ level j ∧
          ((exceptional j).card : ℝ) ≤ X j * Real.exp (-(blockLength S : ℝ) / 1000) ∧
          ∀ u ∈ level j, u ∉ exceptional j →
            (Real.exp (-(blockLength S : ℝ) / 10000) / 2) *
                (2 : ℝ) ^ blockLength S ≤
              ((Finset.univ.filter (fun I : Fin (blockLength S) → Bool =>
                (sampledRemainder (f 0) u I : ℝ) <
                  Real.exp (-(blockLength S : ℝ) / 10000) * u)).card : ℝ)) ∧
        ∀ u ∈ terminal, ∃ i : Fin 1000, ∃ I : Fin (blockLength S) → Bool,
          (sampledRemainder (f i) u I : ℝ) < (u : ℝ) ^ (9999 / 10000 : ℝ) := by
  classical
  obtain ⟨N, hN⟩ := exists_common_sampled_realization
  refine ⟨N, ?_⟩
  intro S P J tests level X terminal hS hp hi hs hm hsmallm ht hX hlevel hmid hterminal
  have hfreqcard (w : ℝ) : ((residueFrequencies w).card : ℝ) ≤
      Real.exp (4 * w / 10000) := by
    simpa [residueFrequencies] using Nat.floor_le (Real.exp_pos (4 * w / 10000)).le
  have hfreqmem {w : ℝ} {l : ℕ} (hl : l ∈ residueFrequencies w) :
      0 < l ∧ (l : ℝ) ≤ Real.exp (4 * w / 10000) := by
    obtain ⟨hl1, hlH⟩ := Finset.mem_Icc.mp hl
    exact ⟨hl1, (Nat.cast_le.mpr hlH).trans (Nat.floor_le (Real.exp_pos _).le)⟩
  have hmiddlefreq : ∀ j ∈ tests, ∀ u ∈ level j,
      ∀ l ∈ residueFrequencies (blockLength S : ℝ), 0 < l ∧
        (l : ℝ) ≤ Real.exp (min (blockLength S : ℝ) (Real.log (u : ℝ)) / 200) := by
    intro j hj u hu l hl
    obtain ⟨hl0, hlbound⟩ := hfreqmem hl
    refine ⟨hl0, hlbound.trans (Real.exp_le_exp.mpr ?_)⟩
    have hmin : (9999 / 10000 : ℝ) * (blockLength S : ℝ) ≤
        min (blockLength S : ℝ) (Real.log (u : ℝ)) :=
      le_min (by have := Nat.cast_nonneg (blockLength S) (α := ℝ); nlinarith) (hmid j hj u hu).2.2.2.2
    linarith
  have hterminalfreq : ∀ u ∈ terminal,
      ∀ l ∈ residueFrequencies (Real.log (u : ℝ)), 0 < l ∧
        (l : ℝ) ≤ Real.exp (Real.log (u : ℝ) / 200) := by
    intro u hu l hl
    obtain ⟨hl0, hlbound⟩ := hfreqmem hl
    refine ⟨hl0, hlbound.trans (Real.exp_le_exp.mpr ?_)⟩
    have hu1 : 1 ≤ u := (le_max_right N 1).trans (hterminal u hu).1
    have hlog : 0 ≤ Real.log (u : ℝ) := Real.log_nonneg (by exact_mod_cast hu1)
    linarith
  obtain ⟨f, hmiddle, hterm⟩ := hN S P J tests level X
    (residueFrequencies (blockLength S : ℝ))
    (fun u => residueFrequencies (Real.log (u : ℝ))) terminal
    hS hp hi hs hm ht hX hlevel (hfreqcard _)
    (fun j hj u hu => ⟨(hmid j hj u hu).1, (hmid j hj u hu).2.2⟩)
    hmiddlefreq
    (fun u hu => ⟨(hterminal u hu).1, (hterminal u hu).2.1,
      (hterminal u hu).2.2.1⟩)
    (fun u _ => hfreqcard _) hterminalfreq
  let exceptional : J → Finset ℕ := fun j => (level j).filter (fun u =>
    ∃ l ∈ residueFrequencies (blockLength S : ℝ),
      Real.exp (-3 * (blockLength S : ℝ) / 10000) < ‖sampledMean (f 0) u l‖)
  refine ⟨f, exceptional, ?_, ?_⟩
  · intro j hj
    refine ⟨Finset.filter_subset _ _, hmiddle j hj, ?_⟩
    intro u hu hnot
    have hgood : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊Real.exp (4 * (blockLength S : ℝ) / 10000)⌋₊ →
        ‖sampledMean (f 0) u l‖ ≤ Real.exp (-3 * (blockLength S : ℝ) / 10000) := by
      intro l hl hlH
      by_contra hbad
      apply hnot
      exact Finset.mem_filter.mpr ⟨hu, l, Finset.mem_Icc.mpr ⟨hl, hlH⟩, lt_of_not_ge hbad⟩
    have hcount := sampled_remainder_count_of_fourier (f 0) u (hmid j hj u hu).1
      (blockLength S : ℝ) hsmallm hgood
    exact hcount
  · intro u hu
    obtain ⟨i, hi⟩ := hterm u hu
    have hu0 : 0 < u := by have := (le_max_right N 1).trans (hterminal u hu).1; omega
    obtain ⟨I, hI⟩ := exists_sampled_terminal_remainder (f i) u hu0
      (hterminal u hu).2.2.2 (fun l hl hlH => hi l (Finset.mem_Icc.mpr ⟨hl, hlH⟩))
    exact ⟨i, I, hI⟩

end Problem337.RandomProducts

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_GeometricRandomResidues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Filter
open scoped BigOperators

namespace Problem337.RandomProducts
open GeometricRandomRanges

/-- The middle-level small-residue and every-terminal-numerator guarantees
hold for one common family of actual labelled prime samples. The onset is
uniform in the prime pool and no Fourier hypothesis remains. -/
theorem eventually_common_geometric_random_fractional_residues_oai (D : ℝ) (hD : 1 ≤ D) :
    ∀ᶠ S : ℝ in atTop, ∀ P : Finset ℕ,
      (∀ p ∈ P, Nat.Prime p) →
      (∀ p ∈ P, S ^ 100 ≤ (p : ℝ) ∧ (p : ℝ) ≤ S ^ 101) →
      S ^ 99 ≤ (P.card : ℝ) →
      ∃ (f : Fin 1000 → ((Fin (blockLength S) × Bool) → P))
        (exceptional : ℕ → Finset ℕ),
        (∀ j ∈ middleTests D S, exceptional j ⊆ middleLevel D S j ∧
          ((exceptional j).card : ℝ) ≤
            cutoff D S j * Real.exp (-(blockLength S : ℝ) / 1000) ∧
          ∀ u ∈ middleLevel D S j, u ∉ exceptional j →
            (Real.exp (-(blockLength S : ℝ) / 10000) / 2) *
                (2 : ℝ) ^ blockLength S ≤
              ((Finset.univ.filter (fun I : Fin (blockLength S) → Bool =>
                Int.fract (-(sampledProduct (f 0) I : ℝ) / u) <
                  Real.exp (-(blockLength S : ℝ) / 10000))).card : ℝ)) ∧
        ∀ u ∈ terminalRange S, ∃ i : Fin 1000, ∃ I : Fin (blockLength S) → Bool,
          (sampledRemainder (f i) u I : ℝ) < (u : ℝ) ^ (9999 / 10000 : ℝ) := by
  classical
  obtain ⟨N, hN⟩ := exists_common_sampled_residue_realization_strict
  filter_upwards [eventually_selectionRanges D hD (max N 1),
    ResidueLevels.eventually_scale_bounds,
    ResidueLevels.tendsto_scale.eventually
      (eventually_ge_atTop (10000 * Real.log 65536)),
    Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop (Real.log 65536 / 10))]
    with S hr hscale hsmallm hlogsmall
  intro P hp hi hs
  have hSpos : 0 < S := by linarith [hr.parameter_large]
  have hlogpos : 0 < Real.log S := by linarith [hscale.1]
  have hmS : (blockLength S : ℝ) ≤ S := by
    have hratio : S / Real.log S ≤ S := by
      apply (div_le_iff₀ hlogpos).mpr
      nlinarith [hscale.1]
    exact hscale.2.2.2.trans hratio
  have hsmallV : 10000 * Real.log 65536 ≤ 100000 * Real.log S := by
    linarith
  obtain ⟨f, exceptional, hmiddle, hterminal⟩ :=
    hN S P ℕ (middleTests D S) (middleLevel D S) (cutoff D S) (terminalRange S)
      (by linarith [hr.parameter_large]) hp hi hs hr.scale_large hsmallm
      hr.tests_card hr.cutoff_positive hr.level_card
      (fun j hj u hu => ⟨(mem_middleLevel hu).1, (mem_middleLevel hu).2.2,
        hr.middle_window j hj u hu⟩)
      (fun u hu => ⟨hr.terminal_threshold u hu, (hr.terminal_window u hu).1,
        le_min (hr.terminal_window u hu).2 ((hr.terminal_window u hu).2.trans hmS),
        hsmallV.trans (hr.terminal_window u hu).1⟩)
  refine ⟨f, exceptional, ?_, hterminal⟩
  intro j hj
  obtain ⟨hsub, hcard, hcount⟩ := hmiddle j hj
  refine ⟨hsub, hcard, ?_⟩
  intro u hu hnot
  simpa only [sampledRemainder_lt_iff_fract (f 0) u (mem_middleLevel hu).1] using
    hcount u hu hnot

end Problem337.RandomProducts

end

end OAI
end

theorem solution : type_of% @OAI.Problem337.RandomProducts.eventually_common_geometric_random_fractional_residues_oai := @OAI.Problem337.RandomProducts.eventually_common_geometric_random_fractional_residues_oai
