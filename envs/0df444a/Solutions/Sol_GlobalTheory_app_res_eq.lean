-- Prove2me | solution 1 for GlobalTheory.app_res_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:23:17.330657+00:00
-- url     : https://prove2.me/submissions/5846ec29-16c0-4592-bedd-3973d9fb6b4e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GlueOfDenseOpenImmersion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {T Z : Scheme.{0}} (j : T ⟶ Z) {V W : Z.Opens} (i : V ⟶ W)
    (i' : j ⁻¹ᵁ V ⟶ j ⁻¹ᵁ W) (a : Γ(Z, W)) :
    j.app V (Z.presheaf.map i.op a) = T.presheaf.map i'.op (j.app W a) := by
  obtain rfl : i' = (Opens.map j.base).map i := Subsingleton.elim _ _
  have := congrArg (fun f => f.hom a) (j.naturality i.op)
  simpa using this
end GlobalTheory
