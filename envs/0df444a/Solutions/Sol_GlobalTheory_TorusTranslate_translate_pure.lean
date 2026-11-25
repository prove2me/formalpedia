-- Prove2me | solution 1 for GlobalTheory.TorusTranslate.translate_pure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:20:14.583509+00:00
-- url     : https://prove2.me/submissions/1c2f94a6-1adc-402b-8754-61ab4b0270d5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPointTranslatePure
import Theorems.Thm_GlobalTheory_TorusTranslate_appLE_app
import Theorems.Thm_GlobalTheory_TorusTranslate_appLE_res
import Theorems.Thm_GlobalTheory_TorusTranslate_translate_comp_q
import Theorems.Thm_GlobalTheory_TorusTranslate_translate_le
import Theorems.Thm_GlobalTheory_TorusTranslate_translate_coord
import Theorems.Thm_GlobalTheory_splitTorusPointsEquiv_val


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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.TorusTranslate
variable {S : Scheme.{0}} {E : SplitExt S} {G : Over S} [GrpObj G] (D : E.GtDatum G) {Z : Over S}
namespace GlobalTheory.TorusTranslate
theorem _root_.solution (τ : Z ⟶ splitTorus S E.X) (x : Z ⟶ G) (j : E.ChartIdx)
    (V : E.B.left.Opens) (hV : IsAffineOpen V) (hle : V ≤ E.chart j) (α : E.X)
    (s : Γ(G.left, D.q.left ⁻¹ᵁ V)) (hs : ∀ β, β ≠ α → D.weight j V hV hle β s = 0)
    (h : ⊤ ≤ x.left ⁻¹ᵁ (D.q.left ⁻¹ᵁ V))
    (h' : ⊤ ≤ ((τ ≫ D.i) * x).left ⁻¹ᵁ (D.q.left ⁻¹ᵁ V)) :
    (((τ ≫ D.i) * x).left.appLE _ ⊤ h').hom s =
      τ.left.appTop.hom (charUnit S E.X α).val * (x.left.appLE _ ⊤ h).hom s := by
  have hsingle : (Equiv.ofBijective _ (D.coord j V hV hle)).symm s =
      AddMonoidAlgebra.single α (D.weight j V hV hle α s) := by
    apply AddMonoidAlgebra.ext
    ext β
    by_cases hβ : β = α
    · subst hβ
      simp [SplitExt.GtDatum.weight]
    · have := hs β hβ
      rw [SplitExt.GtDatum.weight] at this
      rw [this]
      simp [Ne.symm hβ]
  generalize D.weight j V hV hle α s = w at hsingle
  rw [Equiv.symm_apply_eq, Equiv.ofBijective_apply, AddMonoidAlgebra.liftNCRingHom_single] at hsingle
  let c : E.X →ₗ[ℤ] Additive Γ(G.left, D.q.left ⁻¹ᵁ V)ˣ := E.basis.constr ℤ (fun k => Additive.ofMul
            (res (Scheme.Hom.preimage_mono D.q.left hle) (D.u j k)))
  have hs' : s = (D.q.left.app V).hom w * (Additive.toMul (c α)).val := hsingle
  let f₁ : E.X →+ Additive Γ(Z.left, ⊤)ˣ :=
    (Units.map (((τ ≫ D.i) * x).left.appLE _ ⊤ h').hom.toMonoidHom).toAdditive.comp c.toAddMonoidHom
  let f₂ : E.X →+ Additive Γ(Z.left, ⊤)ˣ :=
    (Units.map (x.left.appLE _ ⊤ h).hom.toMonoidHom).toAdditive.comp c.toAddMonoidHom
  let f₀ : E.X →+ Additive Γ(Z.left, ⊤)ˣ :=
    MonoidHom.toAdditiveRight (splitTorusPointsEquiv S E.X Z τ)
  have hf : f₁.toIntLinearMap = (f₀ + f₂).toIntLinearMap := by
    refine E.basis.ext fun k => ?_
    apply Additive.toMul.injective
    apply Units.ext
    have hc : c (E.basis k) = Additive.ofMul
      (res (Scheme.Hom.preimage_mono D.q.left hle) (D.u j k)) := E.basis.constr_basis _ _ _
    change (((τ ≫ D.i) * x).left.appLE _ ⊤ h').hom (Additive.toMul (c (E.basis k))).val =
      (splitTorusPointsEquiv S E.X Z τ (Multiplicative.ofAdd (E.basis k))).val *
        (x.left.appLE _ ⊤ h).hom (Additive.toMul (c (E.basis k))).val
    have g : ⊤ ≤ x.left ⁻¹ᵁ (D.q.left ⁻¹ᵁ E.chart j) :=
      h.trans (Scheme.Hom.preimage_mono _ (Scheme.Hom.preimage_mono _ hle))
    rw [hc, toMul_ofMul, splitTorusPointsEquiv_val,
      appLE_res _ _ _ _ h' (translate_le D τ x _ g), appLE_res _ _ _ _ h g]
    exact translate_coord D τ x j k g _
  have hα : (((τ ≫ D.i) * x).left.appLE _ ⊤ h').hom (Additive.toMul (c α)).val =
      (splitTorusPointsEquiv S E.X Z τ (Multiplicative.ofAdd α)).val *
        (x.left.appLE _ ⊤ h).hom (Additive.toMul (c α)).val :=
    congrArg (fun z => (Additive.toMul z).val) (LinearMap.congr_fun hf α)
  have g : ⊤ ≤ (x.left ≫ D.q.left) ⁻¹ᵁ V := h
  rw [hs', map_mul, map_mul, hα, splitTorusPointsEquiv_val,
    appLE_app _ _ _ (translate_comp_q D τ x) V h' g, appLE_app _ _ _ rfl V h g]
  ring
end GlobalTheory.TorusTranslate
