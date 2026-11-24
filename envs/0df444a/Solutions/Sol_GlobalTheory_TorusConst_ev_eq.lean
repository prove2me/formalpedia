-- Prove2me | solution 1 for GlobalTheory.TorusConst.ev_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:13:28.728572+00:00
-- url     : https://prove2.me/submissions/9f20aa8c-de74-4fd5-954a-f791fb851ce4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusToAbelianVarietyConst
import Theorems.Thm_GlobalTheory_TorusConst_spm_val
import Theorems.Thm_GlobalTheory_TorusConst_Glue_symm
import Theorems.Thm_GlobalTheory_TorusConst_val_unit_eq
import Theorems.Thm_GlobalTheory_TorusConst_ev_comp_inc
import Theorems.Thm_GlobalTheory_TorusConst_ev_comp_cst
import Theorems.Thm_GlobalTheory_TorusConst_ev_tU
import Theorems.Thm_GlobalTheory_TorusConst_comp_ev
import Theorems.Thm_GlobalTheory_TorusConst_exists_extension_line
import Theorems.Thm_GlobalTheory_TorusToProper_spm_comp


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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.TorusConst
open Polynomial TorusToProper
variable {K : Type} [Field K] {B : Over (Spec (CommRingCat.of K))}
open LaurentPolynomial
variable {L : Type} [Field L] [Algebra K L]
namespace GlobalTheory.TorusConst
theorem _root_.solution [GrpObj B] [IsProper B.hom] (u : sp K L[T;T⁻¹] ⟶ B) (x y : Lˣ) :
    spm (ev (AlgHom.id K L) x) ≫ u = spm (ev (AlgHom.id K L) y) ≫ u := by
  obtain ⟨b, hb⟩ := exists_extension_line u
  obtain ⟨b', hb'⟩ := exists_extension_line (spm (ev (cst K L) (tU L)⁻¹) ≫ u)
  have h1 : ∀ (u : sp K L[T;T⁻¹] ⟶ B) (b : sp K L[X] ⟶ B), spm (inc K L) ≫ b = u →
      ∀ (A : Type) [CommRing A] [Algebra K A] (c : L →ₐ[K] A) (x : Aˣ),
        val b c (x : A) = spm (ev c x) ≫ u := by
    intro u b hb A _ _ c x
    rw [← hb, ← Category.assoc, spm_comp, ev_comp_inc, val]
  have hg : Glue b b' := by
    intro A _ _ c x hx
    have e1 := h1 _ _ hb A c (Units.mk0 x hx)
    have e2 := h1 _ _ hb' A c (Units.mk0 x hx)⁻¹
    rw [← Category.assoc, spm_comp, comp_ev, ev_comp_cst, map_inv] at e2
    have e3 : Units.map (ev c (Units.mk0 x hx)⁻¹ : L[T;T⁻¹] →* A) (tU L) = (Units.mk0 x hx)⁻¹ :=
      Units.ext (ev_tU _ _)
    rw [e3, inv_inv] at e2
    simpa using e1.trans e2.symm
  have key := val_unit_eq hg (cst K L) (tU L) (ev (AlgHom.id K L) 1)
    (fun a => ⟨cst K L a, AlgHom.congr_fun (ev_comp_cst (AlgHom.id K L) 1) a⟩) (ev_tU _ _)
  have h2 : ∀ x : Lˣ, spm (ev (AlgHom.id K L) x) ≫ u = val b (AlgHom.id K L) 1 := by
    intro x
    have := congrArg (spm (ev (AlgHom.id K L) x) ≫ ·) key
    simp only [spm_val, ev_comp_cst, ev_tU, map_one] at this
    rw [← this, h1 _ _ hb]
  rw [h2, h2]
end GlobalTheory.TorusConst
