-- Prove2me | solution 1 for GlobalTheory.LastSteps.isClopen_isCompact_qLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:42.550997+00:00
-- url     : https://prove2.me/submissions/895d24c6-3e87-477a-995d-7827c1bdc2cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat
import Theorems.Thm_GlobalTheory_LatPair_isClopen_lattice
import Theorems.Thm_GlobalTheory_SplitWeil_Model_isCompact_int
import Theorems.Thm_GlobalTheory_SplitWeil_isCompact_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData
noncomputable section
open GlobalTheory GlobalTheory.LastSteps
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' n'' : Type}
variable [Fintype n]
namespace GlobalTheory.LastSteps
theorem _root_.solution (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] :
    IsClopen {y : n → k | q.inv • y ∈ L} ∧ IsCompact {y : n → k | q.inv • y ∈ L} := by
  classical
  refine ⟨(isClopen_lattice L).preimage (f := fun y : n → k => q.inv • y) (by fun_prop), ?_⟩
  obtain ⟨g, rfl⟩ := exists_smul_lat (stdLat k n) L
  have hK : IsCompact (Set.univ.pi fun _ : n => (𝒪[k] : Set k)) := isCompact_univ_pi fun _ => isCompact_int k
  convert hK.image (f := fun z : n → k => ((q.1 : 𝒪[k]) : k) • (g.val *ᵥ z))
    ((continuous_const.matrix_mulVec continuous_id).const_smul ((q.1 : 𝒪[k]) : k)) using 1
  ext y
  simp only [Set.mem_setOf_eq, mem_smul_iff, mem_stdLat, Set.mem_image, Set.mem_pi, Set.mem_univ, true_imp_iff,
    SetLike.mem_coe]
  constructor
  · intro h
    refine ⟨_, h, ?_⟩
    change q.1 • g • g⁻¹ • q.inv • y = y
    rw [smul_inv_smul, q.smul_inv_smul]
  · rintro ⟨z, hz, rfl⟩
    change ∀ i, (g⁻¹ • q.inv • q.1 • g • z) i ∈ _
    rwa [q.inv_smul_smul, inv_smul_smul]
end GlobalTheory.LastSteps
