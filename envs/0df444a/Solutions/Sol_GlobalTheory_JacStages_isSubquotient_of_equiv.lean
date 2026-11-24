-- Prove2me | solution 1 for GlobalTheory.JacStages.isSubquotient_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:57.761355+00:00
-- url     : https://prove2.me/submissions/cf87b546-75c3-4bbb-894a-0345e31e2d89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSubquotientOfEquiv
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_of_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.JacStages
variable {G G' V W : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.JacStages
theorem _root_.solution {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (φ : σ.Equiv ρ) :
    IsSubquotient σ ρ :=
  .of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective
end GlobalTheory.JacStages
