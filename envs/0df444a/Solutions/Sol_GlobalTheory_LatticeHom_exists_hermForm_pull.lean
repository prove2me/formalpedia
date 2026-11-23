-- Prove2me | solution 1 for GlobalTheory.LatticeHom.exists_hermForm_pull
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:28:50.027823+00:00
-- url     : https://prove2.me/submissions/aae78bfa-bf1e-4bc5-8fe2-a4dc754ba370

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
theorem _root_.solution {g g' : ℕ} {Hm : Matrix (Fin g') (Fin g') ℂ} (h : Hm.IsHermitian)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) :
    ∃ K : Matrix (Fin g) (Fin g) ℂ, K.IsHermitian ∧ ∀ z w, hermForm K z w = hermForm Hm (F z) (F w) := by
  set M := LinearMap.toMatrix' F
  have hF : ∀ z, F z = M *ᵥ z := fun z => by rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  refine ⟨Mᵀ * Hm * Mᵀᴴ, isHermitian_mul_mul_conjTranspose _ h, fun z w => ?_⟩
  unfold hermForm
  rw [hF, hF, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec z Mᵀ, vecMul_transpose, ← star_vecMul,
    vecMul_transpose]
end GlobalTheory.LatticeHom
