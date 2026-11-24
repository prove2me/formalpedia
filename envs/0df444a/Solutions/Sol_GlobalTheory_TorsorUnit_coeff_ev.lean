-- Prove2me | solution 1 for GlobalTheory.TorsorUnit.coeff_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:33:01.754723+00:00
-- url     : https://prove2.me/submissions/e591365a-d283-4c27-b4b9-fabd4107756f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Theorems.Thm_GlobalTheory_TorsorUnit_ev_single
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorsorUnit
variable {X : Type} [AddCommGroup X] {A C R R' : Type} [CommRing A] [CommRing C] [CommRing R]
  [CommRing R']
namespace GlobalTheory.TorsorUnit
theorem _root_.solution (δ : C →+* R) (ψ : Multiplicative X →* Rˣ) (f : AddMonoidAlgebra C X) (x : X) :
    (ev ((cst X R).comp δ) (univ X R * (Units.map (cst X R).toMonoidHom).comp ψ) f).coeff x =
      δ (f.coeff x) * (ψ (Multiplicative.ofAdd x)).val := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hf, hg, add_mul]
  | single y c =>
    rw [ev_single]
    change (AddMonoidAlgebra.single 0 (δ c) * (AddMonoidAlgebra.single y 1 *
      AddMonoidAlgebra.single 0 (ψ (Multiplicative.ofAdd y)).val)).coeff x = _
    simp only [AddMonoidAlgebra.single_mul_single, zero_add, add_zero, _root_.one_mul,
      AddMonoidAlgebra.coeff_single]
    by_cases h : y = x
    · subst h; simp
    · simp [Finsupp.single_eq_of_ne' h]
end GlobalTheory.TorsorUnit
