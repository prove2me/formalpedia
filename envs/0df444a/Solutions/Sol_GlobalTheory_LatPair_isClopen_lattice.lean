-- Prove2me | solution 1 for GlobalTheory.LatPair.isClopen_lattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:44.84565+00:00
-- url     : https://prove2.me/submissions/81ec5ada-ef99-4201-8ec3-f66bcb70fa49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Theorems.Thm_GlobalTheory_SplitWeil_isCompact_int
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_int
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair
open SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable [Fintype n] [Fintype n']
namespace GlobalTheory.LatPair
theorem _root_.solution (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] : IsClopen (L : Set (n → k)) := by
  classical
  haveI := t2Space k
  obtain ⟨g, rfl⟩ := exists_smul_lat (stdLat k n) L
  have h : ((g • stdLat k n : Submodule 𝒪[k] (n → k)) : Set (n → k)) =
      ⋂ i, (fun x => ((g⁻¹ : GL n k).val *ᵥ x) i) ⁻¹' (𝒪[k] : Set k) := by
    ext x
    simp only [SetLike.mem_coe, mem_smul_iff, mem_stdLat, Set.mem_iInter, Set.mem_preimage]
    rfl
  rw [h]
  refine isClopen_iInter_of_finite fun i => IsClopen.preimage ⟨(isCompact_int k).isClosed, isOpen_int k⟩ ?_
  exact (continuous_apply i).comp (continuous_const.matrix_mulVec continuous_id)
end GlobalTheory.LatPair
