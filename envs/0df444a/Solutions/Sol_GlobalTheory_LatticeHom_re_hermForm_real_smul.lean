-- Prove2me | solution 1 for GlobalTheory.LatticeHom.re_hermForm_real_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:35:34.089804+00:00
-- url     : https://prove2.me/submissions/0aaac0a9-b451-444d-a12a-a42dccca2f3c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SectionsPowThetaFunctions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HermFormSwapOfIsHermitian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LatticeHom
namespace GlobalTheory.LatticeHom
theorem _root_.solution {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (t : ℝ) (z : Fin g → ℂ) :
    (hermForm Hm (t • z) (t • z)).re = t ^ 2 * (hermForm Hm z z).re := by
  unfold hermForm
  have hst : star (t • z) = t • star z := by rw [star_smul, star_trivial]
  rw [hst, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_smul, Complex.smul_re]
  ring
end GlobalTheory.LatticeHom
