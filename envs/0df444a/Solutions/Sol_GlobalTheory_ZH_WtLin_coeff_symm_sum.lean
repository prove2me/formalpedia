-- Prove2me | solution 1 for GlobalTheory.ZH.WtLin.coeff_symm_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:38.782958+00:00
-- url     : https://prove2.me/submissions/b76e442a-966b-4cc2-aa98-bd1ffe8c9ed2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CoeffSymmSum

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
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.WtLin
namespace GlobalTheory.ZH.WtLin
theorem _root_.solution {A B X : Type} [CommRing A] [CommRing B] [AddCommGroup X] (f : A →+* B)
    (g : Multiplicative X →* B) (hc : ∀ x y, Commute (f x) (g y))
    (hb : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f g hc)) {J : Type} [Fintype J]
    (c : J → A) (s : J → B) (χ : X) :
    ((Equiv.ofBijective _ hb).symm (∑ i, f (c i) * s i)).coeff χ =
      ∑ i, c i * ((Equiv.ofBijective _ hb).symm (s i)).coeff χ := by
  let e := RingEquiv.ofBijective _ hb
  have h1 : ∀ x, e.symm (f x) = AddMonoidAlgebra.single 0 x := fun x => by
    rw [RingEquiv.symm_apply_eq]
    change _ = AddMonoidAlgebra.liftNCRingHom f g hc _
    simp [AddMonoidAlgebra.liftNCRingHom]
  change (e.symm _).coeff χ = ∑ i, c i * (e.symm (s i)).coeff χ
  simp [map_sum, map_mul, h1]
end GlobalTheory.ZH.WtLin
