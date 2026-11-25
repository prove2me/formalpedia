-- Prove2me | solution 1 for GlobalTheory.over_hom_eq_iff_forall_isAlgClosed_algebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:07:20.902999+00:00
-- url     : https://prove2.me/submissions/2edca62a-5174-4c5e-bfc2-d2ba6b37431f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Theorems.Thm_GlobalTheory_hom_eq_iff_forall_isAlgClosed
import Theorems.Thm_GlobalTheory_AddLaw_Proportional_symm


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
    f = g ↔ ∀ (k : Type u) [Field k] [IsAlgClosed k] [Algebra R k]
      (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k))) ⟶ T), x ≫ f = x ≫ g := by
  refine ⟨fun e _ _ _ _ _ => e ▸ rfl, fun H => Over.OverMorphism.ext ?_⟩
  refine (hom_eq_iff_forall_isAlgClosed Y.hom ((Over.w f).trans (Over.w g).symm)).mpr
    fun k _ _ x => ?_
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (x ≫ T.hom)
  letI : Algebra R k := φ.hom.toAlgebra
  exact congrArg (·.left) (H k (Over.homMk x hφ.symm))
end GlobalTheory
