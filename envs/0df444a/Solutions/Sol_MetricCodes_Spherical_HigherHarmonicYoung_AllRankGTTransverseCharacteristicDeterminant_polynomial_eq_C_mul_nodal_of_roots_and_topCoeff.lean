-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCharacteristicDeterminant.polynomial_eq_C_mul_nodal_of_roots_and_topCoeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:47.506255+00:00
-- url     : https://prove2.me/submissions/d16c16fa-d67e-48d0-9339-6d257d4959dc

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCharacteristicDeterminant
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCharacteristicDeterminant
theorem _root_.solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → ℝ) (hinj : Function.Injective nodes)
    (P : Polynomial ℝ) (c : ℝ)
    (hdeg : P.degree < Fintype.card ι + 1)
    (hcoeff : P.coeff (Fintype.card ι) = c)
    (hroot : ∀ i : ι, P.eval (nodes i) = 0) :
    P = Polynomial.C c * Lagrange.nodal Finset.univ nodes := by
  classical
  let Q : Polynomial ℝ :=
    P - Polynomial.C c * Lagrange.nodal Finset.univ nodes
  have hqdeg : Q.degree < Fintype.card ι := by
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro k hk
    unfold Q
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    by_cases heq : k = Fintype.card ι
    · subst k
      rw [hcoeff]
      have hmonic := (Lagrange.nodal_monic
        (s := Finset.univ) (v := nodes)).leadingCoeff
      rw [Polynomial.leadingCoeff, Lagrange.natDegree_nodal] at hmonic
      simp only [Finset.card_univ] at hmonic
      rw [hmonic]
      ring
    · have hstrict : Fintype.card ι < k := lt_of_le_of_ne hk (Ne.symm heq)
      have hpzero : P.coeff k = 0 := by
        apply Polynomial.coeff_eq_zero_of_degree_lt
        exact hdeg.trans_le (by exact_mod_cast hstrict)
      have hnzero :
          (Lagrange.nodal (Finset.univ : Finset ι) nodes).coeff k = 0 := by
        apply Polynomial.coeff_eq_zero_of_degree_lt
        rw [Lagrange.degree_nodal]
        exact_mod_cast hstrict
      rw [hpzero, hnzero, mul_zero, sub_zero]
  have hqzero : Q = 0 :=
    Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero
      (Finset.univ : Finset ι) hinj.injOn hqdeg (by
        intro i _
        simp [Q, hroot i, Lagrange.eval_nodal_at_node
          (Finset.mem_univ i)])
  exact sub_eq_zero.mp hqzero
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCharacteristicDeterminant
