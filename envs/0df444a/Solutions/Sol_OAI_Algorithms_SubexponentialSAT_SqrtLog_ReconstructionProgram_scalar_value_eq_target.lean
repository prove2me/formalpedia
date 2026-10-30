-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.scalar_value_eq_target
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:08:21.051388+00:00
-- url     : https://prove2.me/submissions/a2df1002-e180-423e-aaee-53a8012c5f63

import Mathlib
import Definitions.Def_OAIQ081S070
import Definitions.Def_OAIQ081S081

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_JetCRT
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Reconstruction from formal polynomial jets over a commutative ring

These results use unit differences of nodes, not a field assumption. Jets are
formal Taylor polynomials modulo `X ^ D`; no factorial divisions occur.
-/

noncomputable section

namespace SubexponentialSAT.JetCRT

open Polynomial
open scoped BigOperators

variable {A : Type*} [CommRing A]

theorem nodePower_monic (a : A) (D : ℕ) : (nodePower a D).Monic :=
  (monic_X_sub_C a).pow D

theorem nodePower_coprime {a b : A} (D E : ℕ) (h : IsUnit (a - b)) :
    IsCoprime (nodePower a D) (nodePower b E) :=
  (isCoprime_X_sub_C_of_isUnit_sub h).pow

theorem jet_eq_iff_dvd_sub (a : A) (D : ℕ) (f g : A[X]) :
    jet a D f = jet a D g ↔ nodePower a D ∣ f - g := by
  change (f.comp (X + C a)) %ₘ (X ^ D) = (g.comp (X + C a)) %ₘ (X ^ D) ↔ _
  rw [← sub_eq_zero, ← sub_modByMonic, ← sub_comp,
    modByMonic_eq_zero_iff_dvd (monic_X.pow D),
    dvd_comp_X_add_C_iff]
  simp only [nodePower, pow_comp, X_comp]

variable {ι : Type*} [Fintype ι]

theorem modulus_monic (θ : ι → A) (D : ℕ) : (modulus θ D).Monic :=
  monic_prod_of_monic _ _ (fun i _ => nodePower_monic (θ i) D)

theorem modulus_natDegree [Nontrivial A] (θ : ι → A) (D : ℕ) :
    (modulus θ D).natDegree = Fintype.card ι * D := by
  rw [modulus, natDegree_prod_of_monic _ _ (fun i _ => nodePower_monic (θ i) D)]
  simp only [nodePower, (monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]
  simp

theorem modulus_degree [Nontrivial A] (θ : ι → A) (D : ℕ) :
    (modulus θ D).degree = (Fintype.card ι * D : ℕ) := by
  rw [degree_eq_natDegree (modulus_monic θ D).ne_zero, modulus_natDegree]

theorem modulus_dvd_iff (θ : ι → A) (D : ℕ)
    (hθ : Pairwise fun i j => IsUnit (θ i - θ j)) (f : A[X]) :
    modulus θ D ∣ f ↔ ∀ i, nodePower (θ i) D ∣ f := by
  classical
  constructor
  · intro h i
    have hi : nodePower (θ i) D ∣ ∏ j, nodePower (θ j) D :=
      Finset.dvd_prod_of_mem (fun j => nodePower (θ j) D) (Finset.mem_univ i)
    exact hi.trans h
  · intro h
    apply Fintype.prod_dvd_of_coprime
    · intro i j hij
      exact nodePower_coprime D D (hθ hij)
    · exact h

/-- Divisibility at all nodes determines a polynomial below the total degree. -/
theorem eq_of_dvd_sub_of_degree_lt (θ : ι → A) (D : ℕ)
    (hθ : Pairwise fun i j => IsUnit (θ i - θ j))
    (f g : A[X])
    (hf : f.degree < (Fintype.card ι * D : ℕ))
    (hg : g.degree < (Fintype.card ι * D : ℕ))
    (hlocal : ∀ i, nodePower (θ i) D ∣ f - g) : f = g := by
  nontriviality A
  apply sub_eq_zero.mp
  by_contra hfg
  have hdiv := (modulus_dvd_iff θ D hθ (f - g)).2 hlocal
  have hdeg : (f - g).degree < (modulus θ D).degree := by
    rw [modulus_degree]
    exact (degree_sub_le f g).trans_lt (max_lt hf hg)
  exact (modulus_monic θ D).not_dvd_of_degree_lt hfg hdeg hdiv

/-- Actual truncated formal Taylor polynomials determine the global polynomial. -/
theorem eq_of_jets_of_degree_lt (θ : ι → A) (D : ℕ)
    (hθ : Pairwise fun i j => IsUnit (θ i - θ j))
    (f g : A[X])
    (hf : f.degree < (Fintype.card ι * D : ℕ))
    (hg : g.degree < (Fintype.card ι * D : ℕ))
    (hjets : ∀ i, jet (θ i) D f = jet (θ i) D g) : f = g := by
  exact eq_of_dvd_sub_of_degree_lt θ D hθ f g hf hg
    (fun i => (jet_eq_iff_dvd_sub (θ i) D f g).1 (hjets i))

/-- The natural-degree form is convenient for bounds on the global count polynomial. -/
theorem eq_of_jets_of_natDegree_lt (θ : ι → A) (D : ℕ)
    (hθ : Pairwise fun i j => IsUnit (θ i - θ j))
    (f g : A[X])
    (hf : f.natDegree < Fintype.card ι * D)
    (hg : g.natDegree < Fintype.card ι * D)
    (hjets : ∀ i, jet (θ i) D f = jet (θ i) D g) : f = g := by
  exact eq_of_jets_of_degree_lt θ D hθ f g
    (degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hf))
    (degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hg)) hjets

/-- Shifting a local polynomial back to the global coordinate and then taking
its jet recovers exactly its truncation. -/
theorem jet_unshift (a : A) (D : ℕ) (f : A[X]) :
    jet a D (f.comp (X - C a)) = f %ₘ (X ^ D) := by
  simp only [jet, comp_assoc, sub_comp, X_comp, C_comp, add_sub_cancel_right, comp_X]

section ExplicitFormula

variable [DecidableEq ι]

theorem nodePower_dvd_cofactor (θ : ι → A) (D : ℕ) {i j : ι} (hij : i ≠ j) :
    nodePower (θ i) D ∣ cofactor θ D j :=
  Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)

end ExplicitFormula

end SubexponentialSAT.JetCRT

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_LiftRing
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# The finite free ring used for prime-power counting

This file constructs the quotient by a monic polynomial, proves that a
positive-degree quotient retains the base ring, and constructs coefficient
reduction maps between these polynomial quotient rings.
-/

namespace SubexponentialSAT.LiftRing

noncomputable section

open Polynomial

section General

variable {R S : Type*} [CommRing R] [CommRing S]

theorem reduction_surjective (φ : R →+* S) (hφ : Function.Surjective φ) (F : R[X]) :
    Function.Surjective (reduction φ F) := by
  intro x
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨r, rfl⟩ := Polynomial.map_surjective φ hφ q
  exact ⟨mk F r, rfl⟩

end General

theorem baseReduction_surjective (p μ : ℕ) [NeZero p] (hμ : 0 < μ) :
    Function.Surjective (baseReduction p μ hμ) := by
  intro a
  refine ⟨(a.val : Base p μ), ?_⟩
  simp only [map_natCast, ZMod.natCast_zmod_val]

theorem residue_surjective (p μ : ℕ) [NeZero p] (hμ : 0 < μ)
    (F : (Base p μ)[X]) :
    Function.Surjective (residue p μ hμ F) :=
  reduction_surjective _ (baseReduction_surjective p μ hμ) F

end

end SubexponentialSAT.LiftRing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_NilpotentDefect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Divisibility of the marked defect

After the input coordinates have been substituted, the coefficient of U in
each incidence argument is divisible by p. Polynomial operations preserve
the stronger invariant that the coefficient of U^j is divisible by p^j.
This proves the high-U vanishing needed by canonical truncation.
-/

namespace SubexponentialSAT.NilpotentDefect

noncomputable section

open scoped BigOperators

section Units

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A unit lifts along a surjection whose kernel consists of nilpotents.
The proof corrects any lifted inverse by the finite geometric-series unit. -/
theorem isUnit_of_nilpotent_kernel (ρ : R →+* S)
    (hρ : Function.Surjective ρ)
    (hker : ∀ x, ρ x = 0 → IsNilpotent x)
    {a : R} (ha : IsUnit (ρ a)) : IsUnit a := by
  obtain ⟨b, hb⟩ := ha.exists_right_inv
  obtain ⟨c, hc⟩ := hρ b
  have hz : ρ (a * c - 1) = 0 := by
    rw [map_sub, map_mul, map_one, hc, hb, sub_self]
  have hu := (hker (a * c - 1) hz).isUnit_add_one
  have hu' : IsUnit (a * c) := by
    simpa only [sub_add_cancel] using hu
  exact isUnit_of_mul_isUnit_left hu'

theorem isUnit_of_principal_nilpotent_kernel (ρ : R →+* S)
    (hρ : Function.Surjective ρ)
    (p : R) (μ : ℕ) (hnil : p ^ μ = 0)
    (hker : ∀ x, ρ x = 0 → p ∣ x)
    {a : R} (ha : IsUnit (ρ a)) : IsUnit a := by
  apply isUnit_of_nilpotent_kernel ρ hρ _ ha
  intro x hx
  obtain ⟨d, hd⟩ := hker x hx
  refine ⟨μ, ?_⟩
  rw [hd, mul_pow, hnil, zero_mul]

theorem isUnit_of_residue_ne_zero {K : Type*} [Field K]
    (ρ : R →+* K) (hρ : Function.Surjective ρ)
    (p : R) (μ : ℕ) (hnil : p ^ μ = 0)
    (hker : ∀ x, ρ x = 0 → p ∣ x)
    {a : R} (ha : ρ a ≠ 0) : IsUnit a :=
  isUnit_of_principal_nilpotent_kernel ρ hρ p μ hnil hker ha.isUnit

end Units

end

end SubexponentialSAT.NilpotentDefect

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_TruncatedInverse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Explicit finite geometric inversion and local CRT factors

The inverses in this file are finite polynomial expressions. Scalar inverses are
input data with multiplication certificates; no Bézout coefficients are chosen.
-/

noncomputable section

namespace SubexponentialSAT.TruncatedInverse

open Polynomial
open scoped BigOperators

variable {A : Type*} [CommRing A]

theorem trunc_degree_lt (D : ℕ) (f : A[X]) :
    (Truncation.trunc D f).degree < (D : ℕ) := by
  apply (degree_lt_iff_coeff_zero _ _).2
  intro n hn
  simp [Truncation.coeff_trunc, Nat.not_lt.mpr hn]

theorem X_pow_dvd_sub_trunc (D : ℕ) (f : A[X]) :
    (X : A[X]) ^ D ∣ f - Truncation.trunc D f := by
  rw [X_pow_dvd_iff]
  intro n hn
  simp [Truncation.coeff_trunc, hn]

/-- Coefficient truncation and monic remainder are the same operation. -/
theorem trunc_eq_modByMonic (D : ℕ) (f : A[X]) :
    Truncation.trunc D f = f %ₘ (X ^ D) := by
  nontriviality A
  have hself : Truncation.trunc D f %ₘ (X ^ D) = Truncation.trunc D f := by
    apply (modByMonic_eq_self_iff (monic_X.pow D)).2
    rw [degree_X_pow]
    exact trunc_degree_lt D f
  exact ((modByMonic_eq_of_dvd_sub (monic_X.pow D)
    (X_pow_dvd_sub_trunc D f)).trans hself).symm

theorem rawInverse_correct (B : A[X]) (a : A) (D : ℕ)
    (ha : a * B.coeff 0 = 1) :
    (X : A[X]) ^ D ∣ B * rawInverse B a D - 1 := by
  let z : A[X] := 1 - C a * B
  have hz : (X : A[X]) ∣ z := by
    apply X_dvd_iff.mpr
    simp [z, coeff_sub, ha]
  have heq : B * rawInverse B a D - 1 = -(z ^ D) := by
    calc
      B * rawInverse B a D - 1 =
          (1 - z) * (∑ j ∈ Finset.range D, z ^ j) - 1 := by
        dsimp [rawInverse, z]
        ring
      _ = -(z ^ D) := by rw [mul_neg_geom_sum]; ring
  rw [heq]
  exact dvd_neg.mpr (pow_dvd_pow_of_dvd hz D)

/-- Only the supplied constant inverse is used. This works in positive
characteristic and in rings with zero divisors. -/
theorem inverse_correct (B : A[X]) (a : A) (D : ℕ)
    (ha : a * B.coeff 0 = 1) :
    (X : A[X]) ^ D ∣ B * inverse B a D - 1 := by
  have hraw := rawInverse_correct B a D ha
  have htail := dvd_mul_of_dvd_right (X_pow_dvd_sub_trunc D (rawInverse B a D)) B
  convert dvd_sub hraw htail using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [inverse]
  ring

theorem correctedJet_correct (B J : A[X]) (a : A) (D : ℕ)
    (ha : a * B.coeff 0 = 1) :
    (X : A[X]) ^ D ∣ B * correctedJet B J a D - J := by
  have hinv := dvd_mul_of_dvd_right (inverse_correct B a D ha) J
  have htail := dvd_mul_of_dvd_right (X_pow_dvd_sub_trunc D (J * inverse B a D)) B
  convert dvd_sub hinv htail using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [correctedJet]
  ring

theorem local_dvd_iff (a : A) (D : ℕ) (f : A[X]) :
    (X : A[X]) ^ D ∣ f.comp (X + C a) ↔ JetCRT.nodePower a D ∣ f := by
  rw [dvd_comp_X_add_C_iff]
  simp only [JetCRT.nodePower, pow_comp, X_comp]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem diagonal_correct (θ : ι → A) (D : ℕ) (a : ι → A) (J : ι → A[X])
    (ha : ∀ i, a i * (localFactor θ D i).coeff 0 = 1) (i : ι) :
    JetCRT.nodePower (θ i) D ∣
      JetCRT.cofactor θ D i * (correction θ D a J i).comp (X - C (θ i)) -
        (J i).comp (X - C (θ i)) := by
  apply (local_dvd_iff (θ i) D _).1
  simpa only [sub_comp, mul_comp, comp_assoc, X_comp, C_comp,
    add_sub_cancel_right, comp_X, correction, localFactor] using
      correctedJet_correct (localFactor θ D i) (J i) (a i) D (ha i)

theorem reconstruct_local_dvd (θ : ι → A) (D : ℕ) (a : ι → A) (J : ι → A[X])
    (ha : ∀ i, a i * (localFactor θ D i).coeff 0 = 1) (i : ι) :
    JetCRT.nodePower (θ i) D ∣ reconstruct θ D a J - (J i).comp (X - C (θ i)) := by
  unfold reconstruct
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), add_sub_assoc]
  apply dvd_add
  · apply Finset.dvd_sum
    intro j hj
    exact dvd_mul_of_dvd_left
      (JetCRT.nodePower_dvd_cofactor θ D (Finset.mem_erase.mp hj).1.symm) _
  · exact diagonal_correct θ D a J ha i

theorem reconstruct_jets (θ : ι → A) (D : ℕ) (a : ι → A) (J : ι → A[X])
    (ha : ∀ i, a i * (localFactor θ D i).coeff 0 = 1) (i : ι) :
    JetCRT.jet (θ i) D (reconstruct θ D a J) = Truncation.trunc D (J i) := by
  calc
    JetCRT.jet (θ i) D (reconstruct θ D a J) =
        JetCRT.jet (θ i) D ((J i).comp (X - C (θ i))) :=
      (JetCRT.jet_eq_iff_dvd_sub _ _ _ _).2 (reconstruct_local_dvd θ D a J ha i)
    _ = J i %ₘ (X ^ D) := JetCRT.jet_unshift _ _ _
    _ = Truncation.trunc D (J i) := (trunc_eq_modByMonic D _).symm

theorem trunc_natDegree_lt (D : ℕ) (hD : 0 < D) (f : A[X]) :
    (Truncation.trunc D f).natDegree < D := by
  by_cases h : Truncation.trunc D f = 0
  · simpa [h] using hD
  · exact (natDegree_lt_iff_degree_lt h).2 (trunc_degree_lt D f)

theorem cofactor_natDegree [Nontrivial A] (θ : ι → A) (D : ℕ) (i : ι) :
    (JetCRT.cofactor θ D i).natDegree = (Fintype.card ι - 1) * D := by
  rw [JetCRT.cofactor, natDegree_prod_of_monic _ _
    (fun j _ => JetCRT.nodePower_monic (θ j) D)]
  simp only [JetCRT.nodePower, (monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]
  simp

theorem reconstruct_natDegree_lt [Nontrivial A] [Nonempty ι]
    (θ : ι → A) (D : ℕ) (hD : 0 < D) (a : ι → A) (J : ι → A[X]) :
    (reconstruct θ D a J).natDegree < Fintype.card ι * D := by
  have ht (i : ι) :
      (JetCRT.cofactor θ D i * (correction θ D a J i).comp (X - C (θ i))).natDegree ≤
        (Fintype.card ι - 1) * D + (D - 1) := by
    apply natDegree_mul_le.trans
    apply Nat.add_le_add
    · exact (cofactor_natDegree θ D i).le
    · have hc : (correction θ D a J i).natDegree < D :=
        trunc_natDegree_lt D hD _
      have hs := natDegree_comp_le (p := correction θ D a J i) (q := X - C (θ i))
      rw [natDegree_X_sub_C, mul_one] at hs
      exact hs.trans (by omega)
  have hb : (reconstruct θ D a J).natDegree ≤
      (Fintype.card ι - 1) * D + (D - 1) := by
    apply natDegree_sum_le_of_forall_le
    intro i _
    exact ht i
  apply hb.trans_lt
  calc
    (Fintype.card ι - 1) * D + (D - 1) < (Fintype.card ι - 1) * D + D :=
      Nat.add_lt_add_left (Nat.sub_lt hD (by decide)) _
    _ = ((Fintype.card ι - 1) + 1) * D := by ring
    _ = Fintype.card ι * D := by rw [Nat.sub_add_cancel Fintype.card_pos]

/-- Correct local data reconstruct the original polynomial by the proved
degree bound and CRT injectivity, using the explicit geometric formula. -/
theorem reconstruct_eq [Nontrivial A] [Nonempty ι]
    (θ : ι → A) (D : ℕ) (hD : 0 < D)
    (hθ : Pairwise fun i j => IsUnit (θ i - θ j)) (a : ι → A) (J : ι → A[X])
    (ha : ∀ i, a i * (localFactor θ D i).coeff 0 = 1)
    (H : A[X]) (hH : H.natDegree < Fintype.card ι * D)
    (hJ : ∀ i, Truncation.trunc D (J i) = JetCRT.jet (θ i) D H) :
    reconstruct θ D a J = H := by
  exact JetCRT.eq_of_jets_of_natDegree_lt θ D hθ _ H
    (reconstruct_natDegree_lt θ D hD a J) hH
    (fun i => (reconstruct_jets θ D a J ha i).trans (hJ i))

end SubexponentialSAT.TruncatedInverse

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Unramified ring attached to a supplied irreducible ternary polynomial

`Data.coefficients` is execution data. An irreducible-search correctness proof
can supply `Data.irreducible`; no separate choice of a minimum polynomial is
made in this model. All polynomial lifts use coefficient representatives.
-/

noncomputable section
namespace SubexponentialSAT.SqrtLog.RingModel

open Polynomial

namespace Data

variable {d : ℕ} (a : Data d) (t : ℕ)

theorem rho_surjective (ht : 0 < t) : Function.Surjective (a.rho t ht) :=
  (a.reducedEquiv t ht).surjective.comp (LiftRing.residue_surjective 3 t ht (a.F t))

theorem isUnit_of_rho_ne_zero (ht : 0 < t) {x : a.O t}
    (hx : a.rho t ht x ≠ 0) : IsUnit x :=
  NilpotentDefect.isUnit_of_residue_ne_zero
    (a.rho t ht) (a.rho_surjective t ht) (3 : a.O t) t
    (a.prime_power_zero t) (fun z hz => (a.rho_eq_zero_iff t ht z).mp hz) hx

end Data

end SubexponentialSAT.SqrtLog.RingModel

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpCRTAtZero
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Direct evaluation of the explicit Hermite reconstruction at zero. The
algorithm needs only local corrections and scalar Horner evaluations; no
global shifted polynomial or final polynomial division is required. -/

namespace SubexponentialSAT.SubexpCRTAtZero

open Polynomial
open scoped BigOperators

noncomputable section

variable {A I : Type*} [CommRing A] [Fintype I] [DecidableEq I]

theorem value_eq_eval (θ : I → A) (D : ℕ) (a : I → A) (J : I → A[X]) :
    value θ D a J = (TruncatedInverse.reconstruct θ D a J).eval 0 := by
  simp [value, TruncatedInverse.reconstruct, eval_finsetSum, eval_mul, eval_comp]

theorem value_eq_target [Nontrivial A] [Nonempty I]
    (θ : I → A) (D : ℕ) (hD : 0 < D)
    (hθ : Pairwise fun i j => IsUnit (θ i - θ j)) (a : I → A) (J : I → A[X])
    (ha : ∀ i, a i * (TruncatedInverse.localFactor θ D i).coeff 0 = 1)
    (H : A[X]) (hH : H.natDegree < Fintype.card I * D)
    (hJ : ∀ i, Truncation.trunc D (J i) = JetCRT.jet (θ i) D H) :
    value θ D a J = H.eval 0 := by
  rw [value_eq_eval, TruncatedInverse.reconstruct_eq θ D hD hθ a J ha H hH hJ]

end

end SubexponentialSAT.SubexpCRTAtZero

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramResult
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact semantic readback for the scalar returned by the native CRT loop,
in the ring defined by the actual searched polynomial. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram

open SubexponentialSAT Polynomial

variable {d : ℕ} (model : RingModel.Data d) (t : ℕ) (ht : 0 < t)

/-- Distinct residue nodes certify the unit differences required by Hermite
uniqueness, also in the presence of nilpotents in the coefficient ring. -/
theorem model_unit_differences {Q : ℕ} (theta : Fin Q → model.O t)
    (h : Function.Injective (fun i => model.rho t ht (theta i))) :
    Pairwise (fun i j => IsUnit (theta i - theta j)) := by
  intro i j hij
  apply model.isUnit_of_rho_ne_zero t ht
  rw [map_sub, sub_ne_zero]
  exact fun he => hij (h he)

theorem scalar_value_eq_target_oai {Q : ℕ} [NeZero Q]
    (theta : Fin Q → model.O t) (J : ℕ) (hJ : 0 < J)
    (hnodes : Function.Injective (fun i => model.rho t ht (theta i)))
    (inverse : Fin Q → model.O t) (jets : Fin Q → (model.O t)[X])
    (hinverse : ∀ i, inverse i * (TruncatedInverse.localFactor theta J i).coeff 0 = 1)
    (target : (model.O t)[X]) (hdegree : target.natDegree < Q * J)
    (hjets : ∀ i, Truncation.trunc J (jets i) = JetCRT.jet (theta i) J target) :
    SubexpCRTAtZero.value theta J inverse jets = target.eval 0 := by
  let _ : Nontrivial (model.O t) := (model.rho t ht).domain_nontrivial
  exact SubexpCRTAtZero.value_eq_target theta J hJ
    (model_unit_differences model t ht theta hnodes) inverse jets hinverse target
    (by simpa using hdegree) hjets

end SubexponentialSAT.SqrtLog.ReconstructionProgram

end

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.scalar_value_eq_target_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.scalar_value_eq_target_oai
