-- Prove2me | solution 1 for GlobalTheory.Cris.cl_tdt_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:37:44.704533+00:00
-- url     : https://prove2.me/submissions/224e11bf-c02a-412b-8faa-f98054ca2dd3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_Pullback1MemHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CrystallineConnectionFormCoboundaryZero

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
open Polynomial
namespace GlobalTheory.Cris
theorem _root_.solution [Nontrivial R] (h2 : (2 : R) = 0) : Form.cl _ (tdt R) ≠ 0 := by
  intro h
  obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 h
  have hx : 𝟙 _ ≫ lineStr R = spMap (algebraMap R R[X]) := Category.id_comp _
  let E := SqExt.ofModule R R[X] R[X]
  let j : R[X] →ₐ[R] E.C := derSec derivative'
  have hπ : ∀ b, E.π (j b) = b := fst_derSec _
  have c0 : coordLift (Thick.triv R[X] _ hx) = Polynomial.X := by
    refine (π_coordLift (Thick.triv R[X] _ hx)).trans ?_
    change (Spec.preimage (𝟙 (Sp R[X]))).hom Polynomial.X = Polynomial.X
    rw [Spec.preimage_id]; rfl
  have c1 : (coordLift (E.thick _ hx)).fst = Polynomial.X := by
    refine (π_coordLift (E.thick _ hx)).trans ?_
    change (Spec.preimage (𝟙 (Sp R[X]))).hom Polynomial.X = Polynomial.X
    rw [Spec.preimage_id]; rfl
  have e1 := congrFun (congrFun (congrFun hg _) _) (E.secHom hx E.i E.π_i)
  have e2 := congrFun (congrFun (congrFun hg _) _) (E.secHom hx j hπ)
  change (_ - TrivSqZeroExt.inl _ : E.C) = TrivSqZeroExt.inl (coordLift (Thick.triv R[X] _ hx)) *
    (_ - TrivSqZeroExt.inl (coordLift (Thick.triv R[X] _ hx))) + (divided₂ E.sq).dpow 2 _ at e1
  change (_ - j _ : E.C) = j (coordLift (Thick.triv R[X] _ hx)) *
    (_ - j (coordLift (Thick.triv R[X] _ hx))) + (divided₂ E.sq).dpow 2 _ at e2
  rw [squareZeroDividedPowers_dpow E.sq le_rfl, c0] at e1 e2
  have key : ∀ (G c : TrivSqZeroExt R[X] R[X]) (p : R[X]), c.fst = Polynomial.X →
      G - TrivSqZeroExt.inl p = TrivSqZeroExt.inl Polynomial.X * (c - TrivSqZeroExt.inl Polynomial.X) + 0 →
      G - derSec (R := R) derivative' p = derSec (R := R) derivative' Polynomial.X *
        (c - derSec (R := R) derivative' Polynomial.X) + 0 → derivative p = Polynomial.X := by
    intro G c p c1 e1 e2
    have f1 := congrArg TrivSqZeroExt.snd e1
    have f2 := congrArg TrivSqZeroExt.snd e2
    simp [c1] at f1 f2
    linear_combination f1 - f2
  have f3 := key _ _ _ c1 e1 e2
  have := congrArg (coeff · 1) f3
  simp only [coeff_derivative, coeff_X_one] at this
  rw [show ((1 : ℕ) : R) + 1 = 2 by norm_num, h2, mul_zero] at this
  exact zero_ne_one this
end GlobalTheory.Cris
