-- Prove2me | solution 1 for GlobalTheory.AffineQuotient.SpecMap_pullOver
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:11.728996+00:00
-- url     : https://prove2.me/submissions/7292f387-a8f7-4a20-97b8-55603c1c121a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoequifiberedDiagramMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.AffineQuotient
open Scheme.AffineZariskiSite
variable {W X Y : Scheme.{0}}
variable (f : X ⟶ Y) (g : W ⟶ Y) (a : W ⟶ X) (ha : a ≫ f = g) (p : W ⟶ X) (hp : p ≫ f = g)
variable [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
set_option backward.isDefEq.respectTransparency false
omit [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
namespace GlobalTheory.AffineQuotient
theorem _root_.solution {U : Y.Opens} (hf : IsAffineOpen (f ⁻¹ᵁ U)) (hg : IsAffineOpen (g ⁻¹ᵁ U)) :
    Spec.map (pullOver f g a ha U) ≫ hf.fromSpec = hg.fromSpec ≫ a :=
  IsAffineOpen.SpecMap_appLE_fromSpec ..
end GlobalTheory.AffineQuotient
