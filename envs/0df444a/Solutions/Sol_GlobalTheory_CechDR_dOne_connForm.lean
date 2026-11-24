-- Prove2me | solution 1 for GlobalTheory.CechDR.dOne_connForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:09:20.424361+00:00
-- url     : https://prove2.me/submissions/bff9858e-4707-42c8-ba0b-274c7f53691d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OneFormMapEqKaehlerDifferentialMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsNilDPOfCube
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_Cris_Form_ev_sq
import Theorems.Thm_GlobalTheory_Cris_ev_sq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.CechDR
open CatCoh Cris
variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
attribute [local instance] opModule isCentralScalar_kaehler isScalarTower_kaehler
variable {R B}
variable {X : Scheme.{0}} {s : X ⟶ Sp R}
namespace GlobalTheory.CechDR
theorem _root_.solution (f : Z1 (O (dp0 R) s)) (x : Sp B ⟶ X) (hx : x ≫ s = spMap (algebraMap R B)) :
    dOne R B (connForm f x hx) = 0 := by
  let i := (diagExt R B).secHom hx (diagExt R B).i fun _ ↦ rfl
  let k := (diagExt R B).secHom hx (diagSec R B) (fst_derSec _)
  let a1 := Bi.hom hx Bi.j1 (fun _ ↦ rfl) fun c _ ↦ by ext1 <;> simp [Bi.sq, Bi.j1]
  let a12 := Bi.hom hx Bi.j12 (fun _ ↦ rfl) fun c _ ↦ by ext1 <;> simp [Bi.sq, Bi.j12]
  let ad := Bi.hom hx Bi.jd (fun _ ↦ rfl) fun c hc ↦ by ext1 <;> simp [Bi.sq, Bi.jd, hc]
  have e0 := ev_sq f i a1 i a12 fun c ↦ rfl
  have e1 := ev_sq f k a1 i ad fun c ↦ by
    change Bi.j1 (diagSec R B c) = Bi.jd (TrivSqZeroExt.inl c)
    ext1 <;> simp [Bi.j1, Bi.jd]
  have e2 := ev_sq f k a12 k ad fun c ↦ by
    change Bi.j12 (diagSec R B c) = Bi.jd (diagSec R B c)
    ext1 <;> simp [Bi.j12, Bi.jd]
  have l0 := congrArg (fun y : Bi R B ↦ y.2.2.2) e0
  have l1 := congrArg (fun y : Bi R B ↦ y.2.2.2) e1
  have l2 := congrArg (fun y : Bi R B ↦ y.2.2.2) e2
  change 0 + _ = 0 + _ at l0
  change 0 + _ = dOne R B (TrivSqZeroExt.snd (R := B) (ev f i)) + _ at l1
  change 0 + _ = dOne R B (TrivSqZeroExt.snd (R := B) (ev f k)) + _ at l2
  change dOne R B (TrivSqZeroExt.snd (R := B) (ev f i) - TrivSqZeroExt.snd (R := B) (ev f k)) = 0
  rw [map_sub]
  have key : ∀ a b c d e : Om R B 2, 0 + a = 0 + b → 0 + a = d + c → 0 + b = e + c → d - e = 0 :=
    fun a b c d e h1 h2 h3 ↦ by linear_combination (norm := abel1) h1 - h2 + h3
  exact key _ _ _ _ _ l0 l1 l2
end GlobalTheory.CechDR
