-- Prove2me | solution 1 for GlobalTheory.cohOn.map_smul_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:37:14.818546+00:00
-- url     : https://prove2.me/submissions/30ea1abb-5e5a-435f-a948-2f3a68feaf30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ToAbSheafPreservesFiniteLimits
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Theorems.Thm_GlobalTheory_smul_hom_def


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
universe t v u
noncomputable section
open GlobalTheory
variable {X : Scheme.{u}}
open GlobalTheory.cohOn
variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
variable {F G H : X.Modules} {U V W : X.Opens} {n : ℕ}
variable (U n)
namespace GlobalTheory.cohOn
theorem _root_.solution (r : Γ(X, ⊤)) (φ : F ⟶ G) : map R (r • φ) U n = r • map R φ U n := by
  rw [smul_hom_def, map_comp]; rfl
end GlobalTheory.cohOn
