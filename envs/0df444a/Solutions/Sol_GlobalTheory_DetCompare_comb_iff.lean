-- Prove2me | solution 1 for GlobalTheory.DetCompare.comb_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:07:59.489251+00:00
-- url     : https://prove2.me/submissions/ae11fe65-eaa9-4096-91e0-d2ecf8da421d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_LieCharpolyRootPairs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsTangentModuleUniversalGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetCondIffHasMultiplicities

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DetCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LieCharpolyRootPairs GlobalTheory.TanMod GlobalTheory.EigenSplit
variable {S : Scheme.{0}} {k : Type} [Field k]
variable {G : Over S} [GrpObj G] {O : Type} [CommRing O]
variable [IsCommMonObj G]
namespace GlobalTheory.DetCompare
theorem _root_.solution {t : Sp k ⟶ S} {n : ℕ} (v : Fin n → Lie G t) (c : Fin n → k) (w : epsPt t ⟶ G) :
    (∃ u : Fin n → (epsPt t ⟶ G),
      (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (v i).1.left) ∧ w = (List.ofFn u).prod) ↔
      w = (comb v c).1 := by
  have key : (comb v c).1 = (List.ofFn fun i => (smulLie (c i) (v i)).1).prod := by
    rw [List.prod_ofFn]
    exact SubmonoidClass.coe_finset_prod (fun i => smulLie (c i) (v i)) Finset.univ
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain rfl : u = fun i => (smulLie (c i) (v i)).1 := funext fun i => Over.OverMorphism.ext (hu i)
    exact key.symm
  · rintro rfl
    exact ⟨fun i => (smulLie (c i) (v i)).1, fun _ => rfl, key⟩
end GlobalTheory.DetCompare
