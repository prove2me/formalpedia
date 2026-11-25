-- Prove2me | solution 1 for GlobalTheory.Spread.exists_fg_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:36:42.747798+00:00
-- url     : https://prove2.me/submissions/529f75e3-ca27-43d5-968b-456802fd8db5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Spread
variable {k : Type} [CommRing k] {B Z : Scheme.{0}} (pB : B ⟶ Sp k)
variable (A : Type) [CommRing A] [Algebra k A]
variable {A} (pZ : Z ⟶ Sp k)
namespace GlobalTheory.Spread
theorem _root_.solution [QuasiCompact pB] [QuasiSeparated pB] [LocallyOfFinitePresentation pZ]
    (φ : pullback pB (spMap (algebraMap k A)) ⟶ Z) (hφ : φ ≫ pZ = pullback.fst _ _ ≫ pB) :
    ∃ (R : Subalgebra k A) (ψ : pullback pB (spMap (algebraMap k R)) ⟶ Z),
      R.FG ∧ ψ ≫ pZ = pullback.fst _ _ ≫ pB ∧ bcMap pB R.val ≫ ψ = φ := by
  classical
  obtain ⟨s, ψ, h₁, h₂⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (bcDiagram pB A) (bcStr pB A) pZ (bcCone pB A) (isLimitBcCone pB A) φ (by
      ext s
      change bcMap pB _ ≫ pullback.fst pB _ ≫ pB = φ ≫ pZ
      rw [bcMap_fst_assoc, hφ])
  exact ⟨Algebra.adjoin k (s.unop : Set A), ψ, Subalgebra.fg_adjoin_finset _, h₂, h₁⟩
end GlobalTheory.Spread
