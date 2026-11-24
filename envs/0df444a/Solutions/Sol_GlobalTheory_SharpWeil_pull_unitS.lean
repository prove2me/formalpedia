-- Prove2me | solution 1 for GlobalTheory.SharpWeil.pull_unitS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:46:59.354645+00:00
-- url     : https://prove2.me/submissions/0e58a6c3-61a2-4803-8b03-df0961d766c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CommutatorPairingE8SharpLevelPoints

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
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.SharpWeil
namespace GlobalTheory.SharpWeil
theorem _root_.solution {o K : Type} [CommRing o] [CommRing K] {S : Scheme.{0}} (s : S ⟶ Sp o) (p : Sp K ⟶ S)
    (β : o →+* K) (u : oˣ) (z : Kˣ) (hp : p ≫ s = spMap β) (hz : (z : K) = β u) :
    Units.map p.appTop.hom.toMonoidHom (unitS s u) = unitOn z := by
  apply Units.ext
  have hc := congrArg (fun f : Sp K ⟶ Sp o => f.appTop.hom (unitOn u).val) hp
  simp only [unitS, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp, RingHom.comp_apply] at hc ⊢
  rw [hc]
  unfold unitOn spMap Sp
  have hn := congrArg (fun φ => φ.hom (u : o)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hn
  simp only [Units.coe_map, hz]
  exact hn.symm
end GlobalTheory.SharpWeil
