-- Prove2me | solution 1 for GlobalTheory.CechDR.connForm_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:03:27.090461+00:00
-- url     : https://prove2.me/submissions/6573973b-9e46-4eff-b909-afc494887abe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamCoefMapOneFormsRestrictAlongFunctor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsNilDPOfCube
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_StructureHomApply
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
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
open CategoryTheory AlgebraicGeometry KaehlerDifferential Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.CechDR
open CatCoh Cris
universe v u v' u'
variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
attribute [local instance] opModule isCentralScalar_kaehler isScalarTower_kaehler
variable {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X}
variable {B B' : Type} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R' B'] {α : B →+* B'}
  (h : IsMor (dp0 R) s (dp0 R') s' σ φ) (ha : SemiHom σ α)
  {x : Sp B ⟶ X} (hx : x ≫ s = spMap (algebraMap R B))
  {x' : Sp B' ⟶ X'} (hx' : x' ≫ s' = spMap (algebraMap R' B')) (e : spMap α ≫ x = x' ≫ φ)
namespace GlobalTheory.CechDR
theorem _root_.solution (f : Z1 (O (dp0 R) s)) :
    connForm (h.coef.pullbackOneCocycle f) x' hx' =
      ha.m1 (connForm f x hx) + D R' B' (ev f (semiTriv h ha hx hx' e)) := by
  have k1 := ev_sq f (semiTriv h ha hx hx' e)
    (h.functor.map ((diagExt R' B').secHom hx' (diagExt R' B').i fun _ ↦ rfl))
    ((diagExt R B).secHom hx (diagExt R B).i fun _ ↦ rfl) (semiDiagHom h ha hx hx' e) fun c ↦
      TrivSqZeroExt.ext (fst_semiDiag ha (TrivSqZeroExt.inl c)).symm
        ((snd_semiDiag ha (TrivSqZeroExt.inl c)).trans (map_zero _)).symm
  have k2 := ev_sq f (semiTriv h ha hx hx' e)
    (h.functor.map ((diagExt R' B').secHom hx' (diagSec R' B') (fst_derSec _)))
    ((diagExt R B).secHom hx (diagSec R B) (fst_derSec _)) (semiDiagHom h ha hx hx' e) fun c ↦ by
      change diagSec R' B' (α c) = semiDiag ha (diagSec R B c)
      ext
      · rw [fst_semiDiag, fst_derSec, fst_derSec]
      · rw [snd_semiDiag, snd_derSec, snd_derSec, SemiHom.m1_D]
  have l1 := congrArg (TrivSqZeroExt.snd (R := B')) k1
  have l2 := congrArg (TrivSqZeroExt.snd (R := B')) k2
  change 0 + _ = (semiDiag ha _).snd + _ at l1
  change (diagSec R' B' (ev f (semiTriv h ha hx hx' e))).snd + _ = (semiDiag ha _).snd + _ at l2
  rw [snd_semiDiag] at l1 l2
  have l3 : (diagSec R' B' (ev f (semiTriv h ha hx hx' e))).snd = D R' B' (ev f (semiTriv h ha hx hx' e)) :=
    snd_derSec _ _
  rw [l3] at l2
  simp only [connForm, TrivSqZeroExt.snd_sub, map_sub]
  have key : ∀ a b c d e f : Ω[B'⁄R'], 0 + a = c + e → f + b = d + e → a - b = c - d + f :=
    fun a b c d e f h1 h2 ↦ by linear_combination (norm := abel1) h1 - h2
  exact key _ _ _ _ _ _ l1 l2
end GlobalTheory.CechDR
