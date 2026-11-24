-- Prove2me | solution 1 for GlobalTheory.DenseBasis.comp_linComb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:19:23.402773+00:00
-- url     : https://prove2.me/submissions/34887024-0439-4444-b9e1-dff2e9f71d8c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteEtaleLatticeTorsionHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueSectionOfDense

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.DenseBasis
variable {Z S : Scheme.{0}}
namespace GlobalTheory.DenseBasis
theorem _root_.solution {A T T' : Over S} [GrpObj A] (f : T' ⟶ T) {n : ℕ} (y : Fin n → (T ⟶ A))
    (a : Fin n → ℕ) : f ≫ Out.linComb y a = Out.linComb (fun i => f ≫ y i) a := by
  unfold Out.linComb
  let φ : (T ⟶ A) →* (T' ⟶ A) :=
    { toFun := fun g => f ≫ g, map_one' := MonObj.comp_one f, map_mul' := MonObj.comp_mul f }
  have hφ := map_list_prod φ (List.ofFn fun i => y i ^ a i)
  simpa [φ, List.map_ofFn, Function.comp_def, MonObj.comp_pow] using hφ
end GlobalTheory.DenseBasis
