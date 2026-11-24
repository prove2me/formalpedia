-- Prove2me | solution 1 for GlobalTheory.LocalLattice.mem_localRing_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:49:06.894255+00:00
-- url     : https://prove2.me/submissions/d6036223-cb9d-43d5-a32c-2b00f2ff81df

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
theorem _root_.solution (v : HeightOneSpectrum O) (x : K) :
    x ∈ v.valuationSubringAtPrime K ↔ ∃ s ∉ v.asIdeal, s • x ∈ (1 : Submodule O K) := by
  rw [← mem_localize_iff (K := K), localize_def, Submodule.one_eq_span,
    Submodule.span_span_of_tower, Submodule.mem_span_singleton]
  constructor
  · intro hx; exact ⟨⟨x, hx⟩, mul_one x⟩
  · rintro ⟨a, rfl⟩
    have : a • (1 : K) = a := mul_one (a : K)
    rw [this]; exact a.2
end GlobalTheory.LocalLattice
