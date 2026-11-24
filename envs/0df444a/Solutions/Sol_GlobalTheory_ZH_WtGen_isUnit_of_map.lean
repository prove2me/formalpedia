-- Prove2me | solution 1 for GlobalTheory.ZH.WtGen.isUnit_of_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:17:56.39358+00:00
-- url     : https://prove2.me/submissions/8cd4562e-2dc7-42a8-b542-e26bfebe7f51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueIsRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsPartPartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GroupAlgebraSingleOneMemOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPowEqTorus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PureSectionRatiosGenerateFunctions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.WtGen
open GlobalTheory.ZH.WtPart
variable {A R X : Type} [CommRing A] [CommRing R] [AddCommGroup X]
  {f : A →+* R} {m : Multiplicative X →* R}
  (hb : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f m (fun _ _ => Commute.all _ _)))
include hb
namespace GlobalTheory.ZH.WtGen
theorem _root_.solution {c : A} (h : IsUnit (f c)) : IsUnit c := by
  obtain ⟨t, ht⟩ := h.exists_right_inv
  obtain ⟨b, rfl⟩ := hb.2 t
  have e : AddMonoidAlgebra.single (0 : X) c * b = 1 := by
    apply hb.1
    rw [map_mul, map_one, AddMonoidAlgebra.liftNCRingHom_single, ofAdd_zero, map_one, _root_.mul_one, ht]
  have e' := congrArg (AddMonoidAlgebra.liftNCRingHom (RingHom.id A) (1 : Multiplicative X →* A)
    (fun _ _ => Commute.all _ _)) e
  rw [map_mul, map_one, AddMonoidAlgebra.liftNCRingHom_single, ofAdd_zero, map_one, _root_.mul_one] at e'
  exact IsUnit.of_mul_eq_one _ e'
end GlobalTheory.ZH.WtGen
