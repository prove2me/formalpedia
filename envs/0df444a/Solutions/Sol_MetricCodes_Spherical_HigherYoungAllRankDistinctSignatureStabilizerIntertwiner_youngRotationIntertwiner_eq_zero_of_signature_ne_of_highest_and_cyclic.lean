-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner.youngRotationIntertwiner_eq_zero_of_signature_ne_of_highest_and_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/91f075fa-a306-4e18-8d8c-f4b1a8046b04

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankDistinctSignatureStabilizerIntertwiner_youngComplexPair_mem_fullYoungComplexPolynomialSpan
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankDistinctSignatureStabilizerIntertwiner_rotationIntertwiner_ambientCartan_dominantHighest_of_signatures
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankDistinctSignatureStabilizerIntertwiner_rotationIntertwiner_positiveRoot_dominantHighest_of_signatures

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
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.CrossGram
open MetricCodes.Spherical.HigherHarmonicYoung.IsotropicAmbientHighestLine
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAmbientRootRotationDecomposition
open MetricCodes.Spherical.HigherYoungAllRankActualHighestKernelRigidity
open MetricCodes.Spherical.HigherYoungAllRankStabilizerHighestCyclicity
open MetricCodes.Spherical.HigherYoungArbitraryRankDominantHighestLinePreservation
open MetricCodes.Spherical.HigherYoungArbitraryRankOrthogonalRootHighestKernel
open MetricCodes.Spherical.HigherYoungCyclicHighestSchur
open MetricCodes.Spherical.HigherYoungMixedGapLieGram
open MetricCodes.Spherical.HigherYoungTwoRowLieIrreducibility
namespace MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner
theorem _root_.solution
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (mu nu : Fin (r + 1) → ℕ) (hmu : Antitone mu)
    (hne : mu ≠ nu)
    (A : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      HarmonicYoungSpace (n := n) nu)
    (hcomm : ∀ a b : Fin n,
      A.comp (youngAmbientRotation mu a b) =
        (youngAmbientRotation nu a b).comp A)
    (hhighest : ∀ z ∈ fullYoungComplexPolynomialSpan (n := n) nu,
      (∀ α : OrthogonalPositiveRoot r n,
        orthogonalPositiveRootDerivation hn α z = 0) →
      z ∈ ambientIsotropicHighestSubmodule hn nu)
    (hcyclic : dominantHighestRotationWordSpan hn mu hmu = ⊤) :
    A = 0 := by
  classical
  let p := dominantHighestRealVector hn mu hmu
  let q := dominantHighestImaginaryVector hn mu hmu
  let f := youngIntertwinerHighestPolynomial hn mu nu hmu A
  have hfspan : f ∈ fullYoungComplexPolynomialSpan nu :=
    youngComplexPair_mem_fullYoungComplexPolynomialSpan nu (A p) (A q)
  have hfhighest : f ∈ ambientIsotropicHighestSubmodule hn nu :=
    hhighest f hfspan
      (rotationIntertwiner_positiveRoot_dominantHighest_of_signatures
        hn mu nu hmu A hcomm)
  obtain ⟨i, hi⟩ : ∃ i, mu i ≠ nu i :=
    not_forall.mp (fun h => hne (funext h))
  have hsource :=
    rotationIntertwiner_ambientCartan_dominantHighest_of_signatures
      hn mu nu hmu A hcomm i
  have htarget :=
    ((mem_ambientIsotropicHighestSubmodule hn nu f).mp hfhighest).2.2.1 i
  have hscalar :
      (((2 * mu i : ℕ) : ℂ) - ((2 * nu i : ℕ) : ℂ)) • f = 0 := by
    rw [sub_smul, ← hsource, ← htarget, sub_self]
  have hneNat : 2 * mu i ≠ 2 * nu i := by omega
  have hneComplex :
      (((2 * mu i : ℕ) : ℂ) - ((2 * nu i : ℕ) : ℂ)) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast hneNat
  have hfzero : f = 0 := (smul_eq_zero.mp hscalar).resolve_left hneComplex
  have hpair : A p = 0 ∧ A q = 0 :=
    (youngComplexPair_eq_zero_iff nu (A p) (A q)).mp hfzero
  have hword (v : HarmonicYoungSpace (n := n) mu)
      (hv : A v = 0) :
      operatorWordSpan (youngRotationFamily mu) v ≤ LinearMap.ker A := by
    rw [operatorWordSpan, Submodule.span_le]
    rintro _ ⟨word, rfl⟩
    induction word generalizing v with
    | nil => exact hv
    | cons ab rest ih =>
        apply ih (youngRotationFamily mu ab v)
        have hrot := LinearMap.congr_fun (hcomm ab.1 ab.2) v
        change A (youngRotationFamily mu ab v) =
          youngRotationFamily nu ab (A v) at hrot
        rw [hrot, hv, map_zero]
  have hker : LinearMap.ker A = ⊤ := by
    apply top_unique
    rw [← hcyclic]
    exact sup_le (hword p hpair.1) (hword q hpair.2)
  exact LinearMap.ker_eq_top.mp hker
end MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner
