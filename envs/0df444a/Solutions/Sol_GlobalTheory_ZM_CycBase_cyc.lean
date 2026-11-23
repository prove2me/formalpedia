-- Prove2me | solution 1 for GlobalTheory.ZM.CycBase.cyc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:41.425004+00:00
-- url     : https://prove2.me/submissions/e1938fa6-3c21-4e86-9d5b-7033f0431b37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsCyclotomicBaseRingInvertingPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
namespace GlobalTheory.ZM.CycBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
private lemma zeta_isPrimitiveRoot' {k : ℕ} (hk : k ≠ 0) : IsPrimitiveRoot (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta k) k := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta; exact Complex.isPrimitiveRoot_exp k hk
end GlobalTheory.ZM.CycBase
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.CycBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct
namespace GlobalTheory.ZM.CycBase
namespace _root_.GlobalTheory.ZM.CycBase
theorem _root_.solution {k : ℕ} [NeZero k] :
    IsCyclotomicExtension {k} ℚ (_root_.GlobalTheory.ZM.CycBase.CF k) := by
  have hζ := zeta_isPrimitiveRoot' (NeZero.ne k)
  haveI := hζ.adjoin_isCyclotomicExtension ℚ
  have h2 : (_root_.GlobalTheory.ZM.CycBase.CF k).toSubalgebra = Algebra.adjoin ℚ {_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta k} :=
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      ((hζ.isIntegral (NeZero.pos k)).tower_top.isAlgebraic)
  exact IsCyclotomicExtension.equiv _ _ _ (Subalgebra.equivOfEq _ _ h2).symm
end _root_.GlobalTheory.ZM.CycBase
end GlobalTheory.ZM.CycBase
