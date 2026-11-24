-- Prove2me | solution 1 for GlobalTheory.KS.ProdLift.der_eq_of_isPushout
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:27:14.108717+00:00
-- url     : https://prove2.me/submissions/23779bf5-bd91-4c71-865c-7f03cbbaae00

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueLocalDerivationAlongFibreFieldOfAffiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDerOfIsPushout

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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.ProdLift
namespace GlobalTheory.KS.ProdLift
theorem _root_.solution {R S T P : CommRingCat.{0}} {i : R ⟶ S} {j : R ⟶ T} {u : S ⟶ P}
    {v : T ⟶ P} (po : IsPushout i j u v) {B : Type} [CommRing B] (a : P →+* B) (d d' : P → B)
    (hadd : ∀ x y, d (x + y) = d x + d y)
    (hmul : ∀ x y, d (x * y) = a x * d y + a y * d x)
    (hadd' : ∀ x y, d' (x + y) = d' x + d' y)
    (hmul' : ∀ x y, d' (x * y) = a x * d' y + a y * d' x)
    (hu : ∀ x, d (u.hom x) = d' (u.hom x)) (hv : ∀ x, d (v.hom x) = d' (v.hom x)) : d = d' := by
  have hext : u ≫ CommRingCat.ofHom (derHom a d hadd hmul) = u ≫ CommRingCat.ofHom (derHom a d' hadd' hmul') ∧
      v ≫ CommRingCat.ofHom (derHom a d hadd hmul) = v ≫ CommRingCat.ofHom (derHom a d' hadd' hmul') := by
    constructor
    · ext x
      · simp [derHom]
      · simp [derHom, hu]
    · ext x
      · simp [derHom]
      · simp [derHom, hv]
  have hφ := po.hom_ext hext.1 hext.2
  funext x
  have := congrArg (fun g => (g.hom x).snd) hφ
  simpa [derHom] using this
end GlobalTheory.KS.ProdLift
