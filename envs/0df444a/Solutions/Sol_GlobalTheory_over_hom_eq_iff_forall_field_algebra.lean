-- Prove2me | solution 1 for GlobalTheory.over_hom_eq_iff_forall_field_algebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:18:26.928513+00:00
-- url     : https://prove2.me/submissions/99e4a250-f2ea-4b5d-a608-5b658bd68648

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Theorems.Thm_GlobalTheory_over_hom_eq_iff_forall_isAlgClosed_algebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
universe u
noncomputable section
open GlobalTheory
variable {T Y S : Scheme.{u}}
variable {R : Type u} [CommRing R]
namespace GlobalTheory
theorem _root_.solution {T Y : Over (Spec (.of R))} [IsReduced T.left]
    [IsSeparated Y.hom] {f g : T ⟶ Y} :
    f = g ↔ ∀ (k : Type u) [Field k] [Algebra R k]
      (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k))) ⟶ T), x ≫ f = x ≫ g :=
  ⟨fun e _ _ _ _ => e ▸ rfl,
    fun H => over_hom_eq_iff_forall_isAlgClosed_algebra.mpr fun k _ _ _ x => H k x⟩
end GlobalTheory
