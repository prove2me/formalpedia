-- Prove2me | solution 1 for GlobalTheory.PowLie.isLieComb_iff_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:45.89282+00:00
-- url     : https://prove2.me/submissions/a0ac7c64-657e-47a4-a53f-ce4d9e274a4c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieCombIffProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.PowLie
variable {R : Type} [CommRing R]
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
namespace GlobalTheory.PowLie
namespace _root_.GlobalTheory.PowLie
theorem _root_.solution {G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)} [GrpObj G] [IsCommMonObj G]
    {n : ℕ} (c : Fin n → R) (v : Fin n → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G)) (w : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieComb c v w ↔ w = ∏ i, _root_.GlobalTheory.PowLie.sc (c i) ≫ v i := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieComb
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [List.prod_ofFn]
    refine Finset.prod_congr rfl fun i _ => ?_
    ext
    simp [_root_.GlobalTheory.PowLie.sc, hu i]
  · intro hw
    refine ⟨fun i => _root_.GlobalTheory.PowLie.sc (c i) ≫ v i, fun i => by
      simp [_root_.GlobalTheory.PowLie.sc], ?_⟩
    rw [List.prod_ofFn]
    exact hw
end _root_.GlobalTheory.PowLie
end GlobalTheory.PowLie
