-- Prove2me | solution 1 for GlobalTheory.LocalLattice.mem_of_forall_mem_localize_of_not_isField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:49:07.759607+00:00
-- url     : https://prove2.me/submissions/7a95d559-9ab6-48c7-ade9-050f921a4b24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.LocalLattice
set_option linter.unusedSectionVars false
variable {O : Type*} (K : Type*) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K]
  [IsFractionRing O K]
  {V : Type*} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
variable {K}
namespace GlobalTheory.LocalLattice
theorem _root_.solution (hO : ¬ IsField O) {L : Submodule O V} {x : V}
    (h : ∀ v : HeightOneSpectrum O, x ∈ localize K v L) : x ∈ L := by
  obtain ⟨m, hm0, hm⟩ := Ring.not_isField_iff_exists_prime.1 hO
  refine mem_of_forall_mem_localize ?_ h
  exact Submodule.span_le_restrictScalars
    ((⟨m, hm, hm0⟩ : HeightOneSpectrum O).valuationSubringAtPrime K) K _ (h ⟨m, hm, hm0⟩)
end GlobalTheory.LocalLattice
