-- Prove2me | solution 1 for GlobalTheory.FormalChartOf.tmul_eps_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:47:16.222835+00:00
-- url     : https://prove2.me/submissions/0e3dc78b-ef4b-42d1-b697-24edaf3a6fab

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsFormalChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.FormalChartOf
variable {R₀ : Type} [CommRing R₀]
namespace GlobalTheory.FormalChartOf
theorem _root_.solution [IsLocalRing R₀] {M : Type} [AddCommGroup M] [Module R₀ M]
    (w : M) (h : w ⊗ₜ[R₀] epsK R₀ = 0) : w = 0 := by
  let s : (dualProj R₀).ker →ₗ[R₀] R₀ := (TrivSqZeroExt.sndHom R₀ R₀).comp (dualProj R₀).ker.subtype
  have hs : s (epsK R₀) = 1 := rfl
  have := congrArg (fun v => TensorProduct.rid R₀ M (LinearMap.lTensor M s v)) h
  simpa [hs] using this
end GlobalTheory.FormalChartOf
