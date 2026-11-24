-- Prove2me | solution 1 for GlobalTheory.Cusp.Shear.prodHomeo_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:48.074872+00:00
-- url     : https://prove2.me/submissions/5a147e75-5d3a-4fc5-9093-26a23c2ef39d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdHomeoSymmApplySnd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cusp GlobalTheory.Cusp.Shear
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {N N' : Subgroup G}
  {V : Type} [AddCommGroup V] [TopologicalSpace V] {s : V → G} {π : N → V}
namespace GlobalTheory.Cusp.Shear
theorem _root_.solution (hle : N' ≤ N) (hs : ∀ v, s v ∈ N) (hsc : Continuous s) (hπc : Continuous π)
    (hπmul : ∀ a b : N, π (a * b) = π a + π b) (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v)
    (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N') (z : N' × V) :
    (prodHomeo hle hs hsc hπc hπmul hπs hker z : G) = z.1 * s z.2 := rfl
end GlobalTheory.Cusp.Shear
