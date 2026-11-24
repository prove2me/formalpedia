-- Prove2me | solution 1 for GlobalTheory.CechDR.AffLoc.fv_eq_sub_of_glued
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:35:11.90309+00:00
-- url     : https://prove2.me/submissions/fc0989a0-0b68-43be-9894-f3ddfe9e04b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecPullA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecFunctionsEqOfRestrictionsOnPairsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CochainValueOnThickeningHomEqSubOfGlued
import Theorems.Thm_GlobalTheory_CechDR_AffLoc_pt_comp
import Theorems.Thm_GlobalTheory_CechDR_AffLoc_fv_of_comp
import Theorems.Thm_GlobalTheory_CechDR_AffLoc_ringHom_eq_of_spMap_eq
import Theorems.Thm_GlobalTheory_CechDR_AffLoc_spMap_toSec
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_T_spec_functions_eq_of_restrictions_on_pairs
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
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR
open GlobalTheory GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc
namespace GlobalTheory.CechDR.AffLoc
theorem _root_.solution : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}
    (f : Z1 ((IsTriv s).ι ⋙ O (dp0 R) s)) (g : C0 (OAff s)),
    (∀ ⦃U V : AffOp X⦄ (a : U ⟶ V), g V - Sec.res s (leOfHom a.unop) (g U) = fv f ((affF s).map a)) →
    ∀ {T T' : TT s} (φ : T ⟶ T') (G : T.obj.B) (G' : T'.obj.B),
    (∀ p : Pair (pt T), toSec R T.obj.B p.1.1 G = hSec f g T p) →
    (∀ p : Pair (pt T'), toSec R T'.obj.B p.1.1 G' = hSec f g T' p) →
    fv f φ = G' - φ.hom.φ G := by
  intro R _ X s f g _ T T' φ G G' hG hG'
  refine GlobalTheory.T.spec_functions_eq_of_restrictions_on_pairs T.obj.B T'.obj.B (pt T) (spMap (φ.hom.φ : T.obj.B →+* T'.obj.B)) _ _ ?_
  intro V' p hV'
  have hp' : V'.1 ≤ pt T' ⁻¹ᵁ p.1.2.1 := by
    rw [pt_comp φ]
    exact fun y hy ↦ p.2 (hV' hy)
  let p' : Pair (pt T') := ⟨(V', p.1.2), hp'⟩
  let q : Pair (spMap (φ.hom.φ : T.obj.B →+* T'.obj.B)) := ⟨(V', p.1.1), hV'⟩
  let χ := secPull (algStr R T.obj.B) (algStr R T'.obj.B) q
  have hw : spMap (φ.hom.φ : T.obj.B →+* T'.obj.B) ≫ algStr R T.obj.B =
      algStr R T'.obj.B ≫ spMap (RingHom.id R) := by
    rw [spMap_id, Category.comp_id, ← spMap_comp]
    exact congrArg spMap (φ.hom.φ.comp_algebraMap)
  let χA : Sec (algStr R T.obj.B) p.1.1.1 →ₐ[R] Sec (algStr R T'.obj.B) V'.1 :=
    { χ with commutes' := (semiHom_secPull (σ := RingHom.id R) hw q).map_algebraMap }

  let c : thk T p ⟶ thk T' p' := ⟨Thick.trivHom (T := (thk T' p').obj) χA (by
    change spMap χ ≫ _ = _
    rw [← Category.assoc, secPull_affPt, Category.assoc, ← pt_comp φ])⟩
  have h1 : ∀ u, χ (secPullA T p u) = secPullA T' p' u := by
    have e : χ.comp (secPull s (algStr R T.obj.B) p) = secPull s (algStr R T'.obj.B) p' := by
      refine ringHom_eq_of_spMap_eq ?_
      rw [← cancel_mono (affPt s p.1.2), spMap_comp, Category.assoc, secPull_affPt,
        ← Category.assoc, secPull_affPt, Category.assoc, ← pt_comp φ]
      exact (secPull_affPt s (algStr R T'.obj.B) p').symm
    exact fun u ↦ RingHom.congr_fun e u
  have h2 : ∀ b, χ (toSec R T.obj.B p.1.1 b) = toSec R T'.obj.B V' (φ.hom.φ b) := by
    have e : χ.comp (toSec R T.obj.B p.1.1 : T.obj.B →+* Sec (algStr R T.obj.B) p.1.1.1) =
        (toSec R T'.obj.B V' : T'.obj.B →+* Sec (algStr R T'.obj.B) V'.1).comp
          (φ.hom.φ : T.obj.B →+* T'.obj.B) := by
      refine ringHom_eq_of_spMap_eq ?_
      rw [spMap_comp, spMap_comp, spMap_toSec, spMap_toSec]
      exact secPull_affPt (algStr R T.obj.B) (algStr R T'.obj.B) q
    exact fun b ↦ RingHom.congr_fun e b
  have e1 : fv f (aM T' p') = χ (fv f (aM T p)) + fv f c := fv_of_comp f (aM T p) c (aM T' p') h1
  have e2 : χ (fv f (bM T p)) + fv f c = toSec R T'.obj.B V' (fv f φ) + fv f (bM T' p') :=
    (fv_of_comp f (bM T p) c (φ ≫ bM T' p') h2).symm.trans (f.2 φ (bM T' p'))
  change toSec R T'.obj.B V' (fv f φ) = toSec R T'.obj.B V' (G' - φ.hom.φ G)
  rw [map_sub, ← h2, hG p, hG' p']
  simp only [hSec, map_sub, map_add, h1]
  change _ = _ - (_ + χ (fv f (aM T p)) - χ (fv f (bM T p)))
  linear_combination -e1 - e2
end GlobalTheory.CechDR.AffLoc
