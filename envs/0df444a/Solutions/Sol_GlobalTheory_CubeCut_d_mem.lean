-- Prove2me | solution 1 for GlobalTheory.CubeCut.d_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:02:52.05085+00:00
-- url     : https://prove2.me/submissions/f900356b-77f6-4b04-adb5-98539aec96dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CubeCutRegularSequence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory GlobalTheory
open GlobalTheory
open GlobalTheory.CubeCut
variable {K : Type} [CommRing K] {I : Type} [LinearOrder I]
namespace GlobalTheory.CubeCut
theorem _root_.solution {A : Cube.{0} I K} {J : ∀ s, Submodule K (A.obj s)}
    (hJ : ∀ {s t : Finset I} (h : s ⊆ t) (x : A.obj s), x ∈ J s → Cube.res A h x ∈ J t)
    {p : ℕ} {x : Cube.Term A p} (hx : ∀ s, x s ∈ J s.1) (t) : Cube.d A p x t ∈ J t.1 := by
  rw [Cube.d_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  have h1 : Cube.res A (Finset.erase_subset i.1 t.1) (x (Cube.eraseIdx t i)) ∈ J t.1 :=
    hJ (Finset.erase_subset i.1 t.1) _ (hx (Cube.eraseIdx t i))
  exact Submodule.smul_of_tower_mem _ _ h1
end GlobalTheory.CubeCut
