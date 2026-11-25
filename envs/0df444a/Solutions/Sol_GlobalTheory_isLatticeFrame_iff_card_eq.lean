-- Prove2me | solution 1 for GlobalTheory.isLatticeFrame_iff_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:34:27.353826+00:00
-- url     : https://prove2.me/submissions/9de964ab-d813-4425-b159-498afc9c3b73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice
import Theorems.Thm_GlobalTheory_IsSaturatedSubmodule_eq_of_le_of_finrank_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped ComplexOrder ComplexConjugate
open GlobalTheory
variable {K : Type*} [Field K] [NumberField K] {V V' : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
namespace GlobalTheory
theorem _root_.solution {A : Submodule (𝓞 K) V} (hA : A.FG) {ι : Type*} [Fintype ι]
    {e : ι → V} : IsLatticeFrame A e ↔
      (∀ i, e i ∈ A) ∧ LinearIndependent K e ∧ Fintype.card ι = finrank (𝓞 K) A := by
  refine ⟨fun he => ⟨he.mem, he.linearIndependent, he.card_eq⟩, fun ⟨h1, h2, h3⟩ => ?_⟩
  haveI := finiteDimensional_span_of_fg hA
  have : Submodule.span K (Set.range e) = Submodule.span K (A : Set V) :=
    Submodule.eq_of_le_of_finrank_eq (Submodule.span_mono (Set.range_subset_iff.2 h1)) (by
      rw [finrank_span_eq_card h2, h3, finrank_lattice_eq_finrank_span])
  exact ⟨h1, h2, fun x hx => this ▸ Submodule.subset_span hx⟩
end GlobalTheory
