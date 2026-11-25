-- Prove2me | solution 1 for GlobalTheory.NilCoord.exists_etale_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:51:41.87964+00:00
-- url     : https://prove2.me/submissions/a74b5dfb-002b-40ac-a3ef-81bb93b950f0

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NilpotentCoordinates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.NilCoord
namespace GlobalTheory.NilCoord
theorem _root_.solution {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G]
    [IsLocalRing R₀] (g : ℕ) (hG : SmoothOfRelativeDimension g G.hom) :
    ∃ (C : Chart G) (π : MvPolynomial (Fin g) R₀ →ₐ[R₀] Γ(G.left, C.U)), π.toRingHom.Etale := by
  let e0 : Spec (CommRingCat.of R₀) ⟶ G.left := (η[G]).left
  obtain ⟨U, hU, V, hV, hx, e, h⟩ :=
    hG.exists_isStandardSmoothOfRelativeDimension (e0 (IsLocalRing.closedPoint R₀))
  have hsp : ∀ p : PrimeSpectrum R₀, p ⤳ IsLocalRing.closedPoint R₀ := fun p =>
    (PrimeSpectrum.le_iff_specializes _ _).mp
      (IsLocalRing.le_maximalIdeal (p : PrimeSpectrum R₀).isPrime.ne_top)
  have hw : e0 ≫ G.hom = 𝟙 _ := Over.w (η[G])
  have hU' : U = ⊤ := by
    rw [eq_top_iff]
    intro p _
    refine (hsp p).mem_open U.isOpen ?_
    have h1 : (e0 ≫ G.hom) (IsLocalRing.closedPoint R₀) ∈ U := by
      exact (Scheme.Hom.comp_apply e0 G.hom (IsLocalRing.closedPoint R₀)).symm ▸ e hx
    rw [hw] at h1
    exact h1
  subst hU'
  let C : Chart G := ⟨V, hV, fun p _ => (hsp p).mem_open (e0 ⁻¹ᵁ V).isOpen hx⟩
  have h2 : RingHom.IsStandardSmoothOfRelativeDimension g (alg0 C) :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of R₀)).symm.commRingCatIsoToRingEquiv h
  obtain ⟨π, hπ1, hπ2⟩ := h2.exists_etale_mvPolynomial
  clear_value C
  exact ⟨C, { π with commutes' := fun r => RingHom.congr_fun hπ1 r }, hπ2⟩
end GlobalTheory.NilCoord
