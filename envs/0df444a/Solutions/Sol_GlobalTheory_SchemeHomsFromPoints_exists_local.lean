-- Prove2me | solution 1 for GlobalTheory.SchemeHomsFromPoints.exists_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:41:42.719827+00:00
-- url     : https://prove2.me/submissions/dfe29021-3f18-4c53-a064-bdf322035df2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_DenseClosedPoints
import Theorems.Thm_GlobalTheory_SchemeHomsFromPoints_eq_zero_of_points
import Theorems.Thm_P2M_GlobalTheory_SchemeHomsFromPoints_lift_toSpec__4f4f7e528988
import Theorems.Thm_GlobalTheory_SchemeHomsFromPoints_range_subset
import Theorems.Thm_GlobalTheory_SchemeHomsFromPoints_top_le_of_lift
import Theorems.Thm_P2M_GlobalTheory_SchemeHomsFromPoints_valAt__eq_3efc08fdb597

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp valAt valAt')
open GlobalTheory GlobalTheory.SchemeHomsFromPoints
namespace GlobalTheory.SchemeHomsFromPoints
theorem _root_.solution {X Y : Scheme.{0}} (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X]
    {Z : Type} (ex : Z → (Sp ℂ ⟶ X)) (ey : Z → (Sp ℂ ⟶ Y))
    (hex : ∀ x : Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ∃ z, ex z = x)
    (W : X.Opens) (D : Y.Opens) (hD : IsAffineOpen D)
    (hWD : ∀ w, ⊤ ≤ ex w ⁻¹ᵁ W → ⊤ ≤ ey w ⁻¹ᵁ D)
    (hf : ∀ f : Γ(Y, D), ∃ h : Γ(X, W), ∀ w, ⊤ ≤ ex w ⁻¹ᵁ W →
      valAt' (ex w) W h = valAt' (ey w) D f) :
    ∃ g : W.toScheme ⟶ Y, ∀ w (x' : Sp ℂ ⟶ W), x' ≫ W.ι = ex w → x' ≫ g = ey w := by
  choose F hF using hf
  have hF' : ∀ f w (e : ⊤ ≤ ex w ⁻¹ᵁ W),
      (ev (ex w) W e).hom (F f) = (ev (ey w) D (hWD w e)).hom f := by
    intro f w e
    rw [← valAt'_eq, ← valAt'_eq]
    exact hF f w e
  have inj : ∀ a b : Γ(X, W), (∀ w (e : ⊤ ≤ ex w ⁻¹ᵁ W),
      (ev (ex w) W e).hom a = (ev (ex w) W e).hom b) → a = b := by
    intro a b hab
    rw [← sub_eq_zero]
    refine eq_zero_of_points p W _ ?_
    intro x hx e
    obtain ⟨w, rfl⟩ := hex x hx
    change (ev (ex w) W e).hom (a - b) = 0
    rw [map_sub, hab w e, sub_self]
  let φ : Γ(Y, D) →+* Γ(X, W) :=
    { toFun := F
      map_one' := inj _ _ fun w e => by rw [hF', map_one, map_one]
      map_mul' := fun a b => inj _ _ fun w e => by rw [hF', map_mul, map_mul, hF', hF']
      map_zero' := inj _ _ fun w e => by rw [hF', map_zero, map_zero]
      map_add' := fun a b => inj _ _ fun w e => by rw [hF', map_add, map_add, hF', hF'] }
  refine ⟨W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ hD.fromSpec, ?_⟩
  intro w x' hx'
  have e := top_le_of_lift W (ex w) x' hx'
  have e' := hWD w e
  have hy' := IsOpenImmersion.lift_fac D.ι (ey w) (range_subset D (ey w) e')
  have h1 : x' ≫ W.toSpecΓ = Spec.map (ev (ex w) W e) := lift_toSpecΓ W (ex w) x' hx' e
  have h2 : _ ≫ D.toSpecΓ = Spec.map (ev (ey w) D e') := lift_toSpecΓ D (ey w) _ hy' e'
  have h3 : CommRingCat.ofHom φ ≫ ev (ex w) W e = ev (ey w) D e' := by
    ext f
    exact hF' f w e
  rw [← Category.assoc, h1, ← Category.assoc, ← Spec.map_comp, h3, ← h2, Category.assoc,
    hD.toSpecΓ_fromSpec, hy']
end GlobalTheory.SchemeHomsFromPoints
