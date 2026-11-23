-- Prove2me | solution 1 for GlobalTheory.AffineQuotient.isPullback_pullOver
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:45.05286+00:00
-- url     : https://prove2.me/submissions/f808b231-3fcf-47c6-9e81-c410544adfaa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoequifiberedDiagramMap
import Theorems.Thm_GlobalTheory_AffineQuotient_SpecMap_pullOver

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
theorem _root_.solution {U : Y.Opens} (hf : IsAffineOpen (f ⁻¹ᵁ U))
    (hg : IsAffineOpen (g ⁻¹ᵁ U)) :
    IsPullback (Spec.map (pullOver f g a ha U)) hg.fromSpec hf.fromSpec a := by
  refine IsOpenImmersion.isPullback _ _ _ _ (SpecMap_pullOver f g a ha hf hg).symm ?_
  subst ha
  rw [IsAffineOpen.opensRange_fromSpec, IsAffineOpen.opensRange_fromSpec]
  rfl
end GlobalTheory.AffineQuotient
