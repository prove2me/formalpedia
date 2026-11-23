-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ProdSub.inl_inr_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:43:12.453825+00:00
-- url     : https://prove2.me/submissions/e158a2ff-ea3d-4554-a5cb-4d98aedbbb41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsIrreducibleOfFixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ProdSub
namespace GlobalTheory.CompanionTheory.ProdSub
theorem _root_.solution {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (G × H) V) (g : G) (h : H) (x : V) :
    ρ (g, 1) (ρ (1, h) x) = ρ (1, h) (ρ (g, 1) x) := by
  have hc : ((g, 1) * (1, h) : G × H) = (1, h) * (g, 1) := Prod.ext (by simp) (by simp)
  rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply]
end GlobalTheory.CompanionTheory.ProdSub
