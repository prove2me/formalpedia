-- Prove2me | solution 1 for GlobalTheory.CechDR.pullHyp1_ptCmp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:23:08.88586+00:00
-- url     : https://prove2.me/submissions/a53a31a8-8630-41ad-bac4-982c460eee6a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamCoefMapOneFormsRestrictAlongFunctor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsNilDPOfCube
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_StructureHomApply
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Theorems.Thm_GlobalTheory_CechDR_connForm_pull
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective
import Theorems.Thm_GlobalTheory_Cris_Form_ev_sq
import Theorems.Thm_GlobalTheory_Cris_ev_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry KaehlerDifferential Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.CechDR
open CatCoh Cris
universe v u v' u'
variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
attribute [local instance] opModule isCentralScalar_kaehler isScalarTower_kaehler
variable {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X}
variable {C : Type u} [Category.{v} C] {F : C ⥤ CommAlgCat.{0} R}
  (x : ∀ T : C, Sp (F.obj T) ⟶ X) (hx : ∀ T, x T ≫ s = spMap (algebraMap R (F.obj T)))
  (hc : ∀ ⦃T T' : C⦄ (a : T ⟶ T'), spMap (mp F a : F.obj T →+* F.obj T') ≫ x T = x T')
namespace GlobalTheory.CechDR
theorem _root_.solution {C' : Type u'} [Category.{v'} C'] {F' : C' ⥤ CommAlgCat.{0} R'}
    (x' : ∀ T : C', Sp (F'.obj T) ⟶ X') (hx' : ∀ T, x' T ≫ s' = spMap (algebraMap R' (F'.obj T)))
    (hc' : ∀ ⦃T T' : C'⦄ (a : T ⟶ T'), spMap (mp F' a : F'.obj T →+* F'.obj T') ≫ x' T = x' T')
    (h : IsMor (dp0 R) s (dp0 R') s' σ φ) (m : CoefMap σ F F')
    (e : ∀ T, spMap (m.α T) ≫ x (m.G.obj T) = x' T ≫ φ) (c : FirstDeRham s) :
    pullHyp1 m (ptCmp x hx hc c) = ptCmp x' hx' hc' (h.pull1 c) := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  let g : Tot0 F' := fun T ↦ ev f (semiTriv h (semiHom_coef m T) (hx _) (hx' T) (e T))
  refine Hyp1.mk_eq_mk.2 ⟨-g, (map_neg _ g).trans (Tot1.ext (fun T T' a ↦ ?_) fun T ↦ ?_)⟩
  · have k := ev_sq f (semiTriv h (semiHom_coef m T) (hx _) (hx' T) (e T))
      (h.functor.map ((ptFunctor x' hx' hc').map a).hom) ((ptFunctor x hx hc).map (m.G.map a)).hom
      (semiTriv h (semiHom_coef m T') (hx _) (hx' T') (e T')) fun b ↦ (m.naturality a b).symm
    have key : ∀ a b c d : F'.obj T', a + b = c + d → -(d - a) = c - b :=
      fun a b c d h1 ↦ by linear_combination h1
    exact key _ _ _ _ k
  · have k := connForm_pull h (semiHom_coef m T) (hx _) (hx' T) (e T) f
    have key : ∀ a b c : Ω[F'.obj T⁄R'], a = b + c → -c = b - a :=
      fun a b c h1 ↦ by rw [h1]; abel
    exact key _ _ _ k
end GlobalTheory.CechDR
