-- Prove2me | solution 1 for GlobalTheory.LocalLattice.mem_iff_forall_mem_localize_ringOfIntegers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:10:20.214374+00:00
-- url     : https://prove2.me/submissions/a3eadec9-2491-4499-ad67-3a006ba09cd2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Theorems.Thm_GlobalTheory_LocalLattice_mem_of_forall_mem_localize_of_not_isField

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
open NumberField
namespace GlobalTheory.LocalLattice
theorem _root_.solution {K V : Type*} [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ L ↔ ∀ v : HeightOneSpectrum (𝓞 K), x ∈ localize K v L :=
  ⟨fun hx v => mem_localize_of_mem v hx,
    mem_of_forall_mem_localize_of_not_isField (RingOfIntegers.not_isField K)⟩
end GlobalTheory.LocalLattice
