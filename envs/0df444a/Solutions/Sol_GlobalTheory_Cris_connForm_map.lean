-- Prove2me | solution 1 for GlobalTheory.Cris.connForm_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:20:44.321144+00:00
-- url     : https://prove2.me/submissions/2fa81834-4177-41ce-9a1b-e55705de5960

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_Pullback1MemHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CrystallineConnectionFormCoboundaryZero
import Theorems.Thm_GlobalTheory_Cris_fst_diagMap
import Theorems.Thm_GlobalTheory_Cris_snd_diagMap
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
open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.Cris
open CatCoh
variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}}
open KaehlerDifferential
variable (R) (B B' : Type) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
attribute [local instance] opModule
attribute [local instance] isCentralScalar_kaehler isScalarTower_kaehler
variable {R B B'} {s : X ⟶ Sp R}
namespace GlobalTheory.Cris
theorem _root_.solution [Algebra B B'] [IsScalarTower R B B'] (f : Z1 (O (dp0 R) s)) (x : Sp B ⟶ X)
    (hx : x ≫ s = spMap (algebraMap R B)) (x' : Sp B' ⟶ X) (hx' : x' ≫ s = spMap (algebraMap R B'))
    (e : spMap (algebraMap B B') ≫ x = x') :
    connForm f x' hx' - KaehlerDifferential.map R R B B' (connForm f x hx) =
      D R B' (ev f (Thick.trivHom (hx := hx) (T := Thick.triv B' x' hx')
        (IsScalarTower.toAlgHom R B B') e)) := by
  let a := Thick.trivHom (hx := hx) (T := Thick.triv B' x' hx') (IsScalarTower.toAlgHom R B B') e
  let Φ := (diagExt R B).thickHom (diagExt R B') (diagMap R B B') (IsScalarTower.toAlgHom R B B')
    (fun c ↦ (fst_diagMap R c).symm) hx hx' e
  have k1 := ev_sq f a ((diagExt R B').secHom hx' (diagExt R B').i fun _ ↦ rfl)
    ((diagExt R B).secHom hx (diagExt R B).i fun _ ↦ rfl) Φ fun c ↦
      TrivSqZeroExt.ext (fst_diagMap R (TrivSqZeroExt.inl c)).symm
        ((snd_diagMap R (TrivSqZeroExt.inl c)).trans (map_zero _)).symm
  have k2 := ev_sq f a ((diagExt R B').secHom hx' (diagSec R B') (fst_derSec _))
    ((diagExt R B).secHom hx (diagSec R B) (fst_derSec _)) Φ fun c ↦
      by
      change diagSec R B' (algebraMap B B' c) = diagMap R B B' (diagSec R B c)
      ext
      · rw [fst_diagMap, fst_derSec, fst_derSec]
      · rw [snd_diagMap, snd_derSec, snd_derSec, KaehlerDifferential.map_D]
  have l1 := congrArg (TrivSqZeroExt.snd (R := B')) k1
  have l2 := congrArg (TrivSqZeroExt.snd (R := B')) k2
  change 0 + _ = (diagMap R B B' _).snd + _ at l1
  change (diagSec R B' (ev f a)).snd + _ = (diagMap R B B' _).snd + _ at l2
  rw [snd_diagMap] at l1 l2
  rw [snd_derSec] at l2
  simp only [connForm, TrivSqZeroExt.snd_sub, map_sub]
  have key : ∀ a b c d e f : Ω[B'⁄R], 0 + a = c + e → f + b = d + e → a - b - (c - d) = f :=
    fun a b c d e f h1 h2 ↦ by linear_combination (norm := abel1) h1 - h2
  exact key _ _ _ _ _ _ l1 l2
end GlobalTheory.Cris
