-- Prove2me | solution 1 for GlobalTheory.ThickStalkEq.fromSpecStalk_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:44:54.552438+00:00
-- url     : https://prove2.me/submissions/ca89f251-09c0-42d1-92c9-17a0822c2249

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FromSpecStalkCompEqOfAgreeOnClosedThickenings
import Theorems.Thm_GlobalTheory_ThickStalkEq_eq_of_forall_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThickStalkEq
namespace GlobalTheory.ThickStalkEq
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (G : Over (Spec (CommRingCat.of R))), LocallyOfFiniteType G.hom → ∀ (b b' : G ⟶ G),
    (∀ e : ℕ, (Over.pullback (thick R (maximalIdeal R) e)).map b =
      (Over.pullback (thick R (maximalIdeal R) e)).map b') →
    ∀ x : G.left, G.hom x = closedPoint R →
      G.left.fromSpecStalk x ≫ b.left = G.left.fromSpecStalk x ≫ b'.left := by
  intro R _ _ _ G hG b b' hb x hx
  haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  let A := G.left.presheaf.stalk x
  let φ : CommRingCat.of R ⟶ A := Spec.preimage (G.left.fromSpecStalk x ≫ G.hom)
  have hφ : Spec.map φ = G.left.fromSpecStalk x ≫ G.hom := Spec.map_preimage _
  have h1 : (Spec.map φ) (closedPoint A) = closedPoint R := by
    rw [hφ]
    exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg G.hom Scheme.fromSpecStalk_closedPoint).trans hx)
  have hloc : ∀ r ∈ maximalIdeal R, φ.hom r ∈ maximalIdeal A := by
    intro r hr
    have hc : PrimeSpectrum.comap φ.hom (closedPoint A) = closedPoint R := h1
    have : r ∈ (PrimeSpectrum.comap φ.hom (closedPoint A)).asIdeal := by rw [hc]; exact hr
    exact this
  refine eq_of_forall_pow A _ _ (fun e => ?_)
  have hle : maximalIdeal R ^ (e + 1) ≤ (maximalIdeal A ^ (e + 1)).comap φ.hom := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hloc) _
  let χ : R ⧸ maximalIdeal R ^ (e + 1) →+* A ⧸ maximalIdeal A ^ (e + 1) :=
    Ideal.quotientMap _ φ.hom hle
  have hw : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A ^ (e + 1)))) ≫
      G.left.fromSpecStalk x) ≫ G.hom = Spec.map (CommRingCat.ofHom χ) ≫ thick R (maximalIdeal R) e := by
    rw [Category.assoc, ← hφ, thick, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
  have := congrArg (fun g => pullback.lift _ _ hw ≫ g.left ≫ pullback.fst _ _) (hb e)
  simp only [Over.pullback_map_left] at this
  rw [pullback.lift_fst, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst_assoc] at this
  simpa only [Category.assoc] using this
end GlobalTheory.ThickStalkEq
