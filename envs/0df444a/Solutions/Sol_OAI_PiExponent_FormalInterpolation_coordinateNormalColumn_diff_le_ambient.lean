-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_diff_le_ambient
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T01:00:09.832884+00:00
-- url     : https://prove2.me/submissions/e14820b5-5f27-46fa-907d-440cfb1f9b1b

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

namespace A3S50JL

variable {m : Nat} (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]

abbrev R (m : Nat) := MvPolynomial (Fin (m + 1)) Complex

/-- chain rule for a derivation on the function field -/
theorem deriv_formula (D : Derivation Complex (logarithmicPrimeField P) (logarithmicPrimeField P))
    (p : R m) :
    D (algebraMap (R m) (logarithmicPrimeField P) p) =
      ∑ i, algebraMap (R m) (logarithmicPrimeField P) (MvPolynomial.pderiv i p) *
        D (algebraMap (R m) (logarithmicPrimeField P) (MvPolynomial.X i)) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [show algebraMap (R m) (logarithmicPrimeField P) (MvPolynomial.C a) =
      algebraMap Complex _ a from (IsScalarTower.algebraMap_apply Complex (R m) _ a).symm]
    simp
  | add p q hp hq => simp [hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    rw [map_mul, D.leibniz, hp]
    simp_rw [MvPolynomial.pderiv_mul, map_add, map_mul, add_mul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    · rw [smul_eq_mul, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
    · rw [Finset.sum_eq_single j]
      · rw [MvPolynomial.pderiv_X_self, map_one, mul_one, smul_eq_mul]
      · intro i _ hij
        rw [MvPolynomial.pderiv_X, Pi.single_apply, if_neg (Ne.symm hij), map_zero, mul_zero,
          zero_mul]
      · intro h; exact absurd (Finset.mem_univ j) h

/-- derivations are determined by their values on the coordinates -/
theorem deriv_ext (D : Derivation Complex (logarithmicPrimeField P) (logarithmicPrimeField P))
    (h : ∀ i, D (algebraMap (R m) (logarithmicPrimeField P) (MvPolynomial.X i)) = 0) : D = 0 := by
  have hR : ∀ p : R m, D (algebraMap (R m) (logarithmicPrimeField P) p) = 0 := by
    intro p; rw [deriv_formula]; simp [h]
  have hA : ∀ a : R m ⧸ P, D (algebraMap (R m ⧸ P) (logarithmicPrimeField P) a) = 0 := by
    intro a
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    have : algebraMap (R m ⧸ P) (logarithmicPrimeField P) (Ideal.Quotient.mk P p) =
        algebraMap (R m) (logarithmicPrimeField P) p := by
      rw [IsScalarTower.algebraMap_apply (R m) (R m ⧸ P) (logarithmicPrimeField P)]; rfl
    rw [this, hR]
  ext z
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R m ⧸ P) z
  have hb0 : algebraMap (R m ⧸ P) (logarithmicPrimeField P) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have key := D.leibniz (algebraMap (R m ⧸ P) (logarithmicPrimeField P) b)
    (algebraMap _ (logarithmicPrimeField P) a / algebraMap (R m ⧸ P) (logarithmicPrimeField P) b)
  rw [mul_div_cancel₀ _ hb0, hA, hA, smul_zero, add_zero, smul_eq_mul] at key
  simpa [hb0] using key.symm

/-- the Jacobian map `a ↦ ∑ aᵢ • cᵢ` -/
noncomputable abbrev T : (Fin (m + 1) → logarithmicPrimeField P) →ₗ[logarithmicPrimeField P]
    (P → logarithmicPrimeField P) :=
  Fintype.linearCombination (logarithmicPrimeField P) (coordinateNormalColumnAtPrime P)

theorem coords_mem_ker (D : Derivation Complex (logarithmicPrimeField P) (logarithmicPrimeField P)) :
    (fun i => D (algebraMap (R m) (logarithmicPrimeField P) (MvPolynomial.X i))) ∈
      LinearMap.ker (T P) := by
  rw [LinearMap.mem_ker, Fintype.linearCombination_apply]
  funext F
  have hF : algebraMap (R m) (logarithmicPrimeField P) (F : R m) = 0 := by
    rw [IsScalarTower.algebraMap_apply (R m) (R m ⧸ P) (logarithmicPrimeField P)]
    show algebraMap (R m ⧸ P) (logarithmicPrimeField P) (Ideal.Quotient.mk P (F : R m)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr F.2, map_zero]
  have := deriv_formula P D F
  rw [hF, D.map_zero] at this
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  rw [this]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [coordinateNormalColumnAtPrime, mul_comm]

noncomputable def Phi : Derivation Complex (logarithmicPrimeField P) (logarithmicPrimeField P)
    →ₗ[logarithmicPrimeField P] LinearMap.ker (T P) where
  toFun D := ⟨_, coords_mem_ker P D⟩
  map_add' D E := by ext; simp
  map_smul' c D := by ext; simp

theorem Phi_injective : Function.Injective (Phi P) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro D hD
  apply deriv_ext P D
  intro i
  have := congrFun (Subtype.ext_iff.mp hD) i
  simpa [Phi] using this

theorem le_main :
    Module.finrank (logarithmicPrimeField P)
      (Submodule.span (logarithmicPrimeField P)
        (Set.range (coordinateNormalColumnAtPrime P))) +
      Module.finrank (logarithmicPrimeField P)
        (Ω[logarithmicPrimeField P⁄Complex]) ≤ m + 1 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (T P)
  rw [Fintype.range_linearCombination] at hrn
  have hm : Module.finrank (logarithmicPrimeField P) (Fin (m + 1) → logarithmicPrimeField P) =
    m + 1 := Module.finrank_fin_fun _
  suffices Module.finrank (logarithmicPrimeField P) (Ω[logarithmicPrimeField P⁄Complex]) ≤
      Module.finrank (logarithmicPrimeField P) (LinearMap.ker (T P)) by omega
  by_cases hfin : Module.Finite (logarithmicPrimeField P) (Ω[logarithmicPrimeField P⁄Complex])
  · rw [← Subspace.dual_finrank_eq,
      (KaehlerDifferential.linearMapEquivDerivation Complex (logarithmicPrimeField P)).finrank_eq]
    exact LinearMap.finrank_le_finrank_of_injective (Phi_injective P)
  · rw [Module.finrank_of_not_finite hfin]; exact Nat.zero_le _

end A3S50JL

theorem solution
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    Module.finrank (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
      (Submodule.span (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
        (Set.range (OAI.PiExponent.FormalInterpolation.coordinateNormalColumnAtPrime P))) +
      Module.finrank (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
        (Ω[OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P⁄Complex]) ≤ m + 1 :=
  A3S50JL.le_main P
