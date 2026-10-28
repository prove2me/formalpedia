-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.ambient_le_coordinateNormalColumn_diff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T06:55:25.642987+00:00
-- url     : https://prove2.me/submissions/944b2f3b-6848-4fbe-9085-a5f22c2372d6

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib
set_option linter.unusedSectionVars false
open scoped BigOperators
open scoped KaehlerDifferential
open OAI.PiExponent.FormalInterpolation

namespace A3S51AL

variable {m : Nat} (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]

abbrev R (m : Nat) := MvPolynomial (Fin (m + 1)) Complex

/-- derivation on R from a vector a -/
noncomputable def D0 (a : Fin (m + 1) → logarithmicPrimeField P) :
    Derivation Complex (R m) (logarithmicPrimeField P) :=
  ∑ i, a i • (Algebra.linearMap (R m) (logarithmicPrimeField P)).compDer (MvPolynomial.pderiv i)

lemma D0_apply (a : Fin (m + 1) → logarithmicPrimeField P) (p : R m) :
    D0 P a p = ∑ i, a i * algebraMap (R m) (logarithmicPrimeField P) (MvPolynomial.pderiv i p) := by
  rw [D0, ← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply, smul_eq_mul]
  rfl

lemma D0_X (a : Fin (m + 1) → logarithmicPrimeField P) (j : Fin (m + 1)) :
    D0 P a (MvPolynomial.X j) = a j := by
  rw [D0_apply]
  simp [MvPolynomial.pderiv_X, Pi.single_apply]


abbrev A (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) := R m ⧸ P

lemma smul_mk (p : R m) (k : logarithmicPrimeField P) :
    (Ideal.Quotient.mk P p) • k = p • k := by
  rw [← smul_one_smul (A P) p k]
  congr 1
  exact Algebra.algebraMap_eq_smul_one (A := A P) p

noncomputable def L1 (a : Fin (m + 1) → logarithmicPrimeField P) (ha : ∀ F ∈ P, D0 P a F = 0) :
    A P →ₗ[Complex] logarithmicPrimeField P :=
  ((P.restrictScalars Complex).liftQ (D0 P a).toLinearMap (fun F hF => ha F hF)).comp
    (Submodule.Quotient.restrictScalarsEquiv Complex P).symm.toLinearMap

lemma L1_mk (a : Fin (m + 1) → logarithmicPrimeField P) (ha : ∀ F ∈ P, D0 P a F = 0) (p : R m) :
    L1 P a ha (Ideal.Quotient.mk P p) = D0 P a p := rfl

noncomputable def D1 (a : Fin (m + 1) → logarithmicPrimeField P) (ha : ∀ F ∈ P, D0 P a F = 0) :
    Derivation Complex (A P) (logarithmicPrimeField P) where
  toLinearMap := L1 P a ha
  map_one_eq_zero' := by
    change L1 P a ha (Ideal.Quotient.mk P 1) = 0
    rw [L1_mk, Derivation.map_one_eq_zero]
  leibniz' := by
    intro x y
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective y
    change L1 P a ha (Ideal.Quotient.mk P (p * q)) = _
    simp only [L1_mk, Derivation.leibniz, smul_mk]


instance : Algebra.FormallyEtale (A P) (logarithmicPrimeField P) :=
  Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (A P))

noncomputable def phi (a : Fin (m + 1) → logarithmicPrimeField P) (ha : ∀ F ∈ P, D0 P a F = 0) :
    Ω[logarithmicPrimeField P⁄Complex] →ₗ[logarithmicPrimeField P] logarithmicPrimeField P :=
  (LinearMap.liftBaseChange (logarithmicPrimeField P) (D1 P a ha).liftKaehlerDifferential).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale Complex (A P)
      (logarithmicPrimeField P)).symm.toLinearMap

lemma phi_X (a : Fin (m + 1) → logarithmicPrimeField P) (ha : ∀ F ∈ P, D0 P a F = 0)
    (j : Fin (m + 1)) :
    phi P a ha (KaehlerDifferential.D Complex (logarithmicPrimeField P)
      (algebraMap (R m) (logarithmicPrimeField P) (MvPolynomial.X j))) = a j := by
  rw [IsScalarTower.algebraMap_apply (R m) (A P) (logarithmicPrimeField P)]
  simp only [phi, LinearMap.comp_apply, LinearEquiv.coe_coe,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    LinearMap.liftBaseChange_tmul, Derivation.liftKaehlerDifferential_comp_D, one_smul]
  exact D0_X P a j

instance : Module.Finite (logarithmicPrimeField P) (Ω[logarithmicPrimeField P⁄Complex]) :=
  Module.Finite.equiv (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale Complex (A P)
      (logarithmicPrimeField P))

theorem main :
    m + 1 ≤
      Module.finrank (logarithmicPrimeField P)
        (Submodule.span (logarithmicPrimeField P)
          (Set.range (coordinateNormalColumnAtPrime P))) +
      Module.finrank (logarithmicPrimeField P)
        (Ω[logarithmicPrimeField P⁄Complex]) := by
  classical
  set K := logarithmicPrimeField P
  let c := coordinateNormalColumnAtPrime P
  let T := Fintype.linearCombination K c
  let E : Module.Dual K (Ω[K⁄Complex]) →ₗ[K] (Fin (m + 1) → K) :=
    LinearMap.pi fun j => Module.Dual.eval K _ (KaehlerDifferential.D Complex K
      (algebraMap (R m) K (MvPolynomial.X j)))
  have hker : LinearMap.ker T ≤ LinearMap.range E := by
    intro a ha
    have ha' : ∀ F ∈ P, D0 P a F = 0 := by
      intro F hF
      have := congrFun (LinearMap.mem_ker.mp ha) ⟨F, hF⟩
      rw [Fintype.linearCombination_apply, Finset.sum_apply] at this
      rw [D0_apply]
      simpa [Pi.smul_apply, smul_eq_mul, c, coordinateNormalColumnAtPrime] using this
    refine ⟨phi P a ha', funext fun j => ?_⟩
    exact phi_X P a ha' j
  have h1 := LinearMap.finrank_range_add_finrank_ker T
  rw [Fintype.range_linearCombination, Module.finrank_fin_fun] at h1
  have h2 := Submodule.finrank_mono hker
  have h3 := LinearMap.finrank_range_le E
  rw [Subspace.dual_finrank_eq] at h3
  have h4 : m + 1 ≤ Module.finrank K ↥(Submodule.span K (Set.range c)) +
      Module.finrank K (Ω[K⁄Complex]) := by omega
  exact h4

end A3S51AL

theorem solution
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    m + 1 ≤
      Module.finrank (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
        (Submodule.span (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
          (Set.range (OAI.PiExponent.FormalInterpolation.coordinateNormalColumnAtPrime P))) +
      Module.finrank (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
        (Ω[OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P⁄Complex]) :=
  A3S51AL.main P
