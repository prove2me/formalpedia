-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ProdSub.mem_fixed_iff_forall
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:43:10.581812+00:00
-- url     : https://prove2.me/submissions/1b4bcf35-89fe-4894-993d-633bf0176395

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
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.ProdSub
theorem _root_.solution {π : Representation ℂ G V} {K : Subgroup G} {x : V} :
    x ∈ fixed π K ↔ ∀ k ∈ K, π k x = x := by
  show (∀ h : K, π h x = ((1 : K →* ℂˣ) h : ℂ) • x) ↔ _
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  exact ⟨fun h k hk => h ⟨k, hk⟩, fun h k => h k k.2⟩
end GlobalTheory.CompanionTheory.ProdSub
