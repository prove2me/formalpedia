-- Prove2me | solution 1 for GlobalTheory.ZMTFin.exists_basicOpen_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:41:12.024421+00:00
-- url     : https://prove2.me/submissions/f87f99d3-e5e8-42b5-b956-434d5939f758

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFinsetAwayMapSubalgebraBijectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteCoequifiberedSubalgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelSpecMapIsIsoOverBasicOpenStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormalizationBasicOpenCoverStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AwayMapBijectiveOfRangeEqSubalgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteCompOpenImmersionOfQuasiFinite
import Theorems.Thm_P2M_GlobalTheory_T_normalization_basicOpen_cover__db3065aef85b


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite
open GlobalTheory GlobalTheory.ZMTFin
namespace GlobalTheory.ZMTFin
theorem _root_.solution (U X : Scheme.{0}) (f : U ⟶ X) (h₁ : IsSeparated f)
    (h₂ : LocallyOfFiniteType f) (h₃ : QuasiCompact f) (h₄ : LocallyQuasiFinite f)
    (V : X.AffineZariskiSite) :
    ∃ G : Finset (f.normalizationDiagram.obj (Opposite.op V.1)),
      (∀ b ∈ G, letI := (f.normalizationDiagramMap.app (Opposite.op V.1)).hom.toAlgebra
        Algebra.FiniteType Γ(X, V.1) (Localization.Away b)) ∧
      ∀ x : U, f x ∈ V.1 → ∃ b ∈ G, f.toNormalization x ∈
        f.normalizationOpenCover.f V '' (PrimeSpectrum.basicOpen b :
          Set (PrimeSpectrum (f.normalizationDiagram.obj (Opposite.op V.1)))) :=
  GlobalTheory.T.normalization_basicOpen_cover' U X f V
end GlobalTheory.ZMTFin
