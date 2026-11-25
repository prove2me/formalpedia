-- Prove2me | solution 1 for GlobalTheory.hom_eq_iff_forall_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:55:18.58483+00:00
-- url     : https://prove2.me/submissions/02ede40c-9dd3-4345-93e6-00ed7019e3f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Theorems.Thm_GlobalTheory_hom_eq_iff_forall_field
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineX
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineY
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originW
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originZ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineX
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineY
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originW
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originZ



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
universe u
noncomputable section
open GlobalTheory
variable {T Y S : Scheme.{u}}
namespace GlobalTheory
theorem _root_.solution [IsReduced T] (s : Y ⟶ S) [IsSeparated s] {f g : T ⟶ Y}
    (h : f ≫ s = g ≫ s) :
    f = g ↔ ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ T), x ≫ f = x ≫ g := by
  refine ⟨fun e _ _ _ _ => e ▸ rfl, fun H => (hom_eq_iff_forall_field s h).mpr fun k _ x => ?_⟩
  let ι : Spec (.of (AlgebraicClosure k)) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  have : Surjective ι := ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
  refine ext_of_isDominant_of_isSeparated s (by simp only [Category.assoc, h]) ι ?_
  simpa only [Category.assoc] using H _ (ι ≫ x)
end GlobalTheory
