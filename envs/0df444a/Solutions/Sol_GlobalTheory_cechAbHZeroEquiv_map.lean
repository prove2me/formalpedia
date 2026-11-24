-- Prove2me | solution 1 for GlobalTheory.cechAbHZeroEquiv_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:22:28.629053+00:00
-- url     : https://prove2.me/submissions/29170001-f35e-40e2-8de6-a07aaca8c748

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoCechComplexMapPresheafCubeRes
import Theorems.Thm_GlobalTheory_cechAbHMap_toCechAbH
import Theorems.Thm_GlobalTheory_cechAbHZeroEquiv_symm_apply
import Theorems.Thm_GlobalTheory_Cube_SemiHom_homology_cechClass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Cube.SemiHom.homology_cechClass


attribute [local simp] GlobalTheory.cechAbHZeroEquiv_symm_apply

set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace Opposite
universe w v u
noncomputable section
open GlobalTheory
variable {T : TopCat.{w}} {ι : Type} {P Q : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{w}}
  {V : Opens T} {U : ι → Opens T}
variable [LinearOrder ι]
namespace GlobalTheory
theorem _root_.solution (hP : Presheaf.IsSheaf (Opens.grothendieckTopology T) P)
    (hQ : Presheaf.IsSheaf (Opens.grothendieckTopology T) Q) (hc : V ≤ ⨆ i, U i) (φ : P ⟶ Q)
    (x : cechAbH P V U 0) :
    cechAbHZeroEquiv hQ hc ((cechAbHMap V U φ 0).hom x) =
      φ.app (op V) (cechAbHZeroEquiv hP hc x) := by
  obtain ⟨y, rfl⟩ := (cechAbHZeroEquiv hP hc).symm.surjective x
  rw [LinearEquiv.apply_symm_apply, cechAbHZeroEquiv_symm_apply, cechAbHMap_toCechAbH,
    ← cechAbHZeroEquiv_symm_apply hQ hc, LinearEquiv.apply_symm_apply]
end GlobalTheory
