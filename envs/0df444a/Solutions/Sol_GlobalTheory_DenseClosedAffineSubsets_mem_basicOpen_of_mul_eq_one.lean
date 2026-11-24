-- Prove2me | solution 1 for GlobalTheory.DenseClosedAffineSubsets.mem_basicOpen_of_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:10:50.791096+00:00
-- url     : https://prove2.me/submissions/7075b18a-9d91-4f85-ad68-e83cfae529e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineLeOrDisjoint

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.DenseClosedAffineSubsets
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GlobalTheory.DenseClosedAffineSubsets
theorem _root_.solution {W P X : Scheme.{0}} (U O : W.Opens) (hUO : U ≤ O)
    (φ : U.toScheme ⟶ P) (π : X ⟶ W) (q : X ⟶ P)
    (j : U.toScheme ⟶ X) [IsSchemeTheoreticallyDominant j] [QuasiCompact j]
    (h₁ : j ≫ π = U.ι) (h₂ : j ≫ q = φ) (g : Γ(O.toScheme, ⊤))
    (D : P.Opens) (r : Γ(D.toScheme, ⊤))
    (hr : ∀ (V : Scheme.{0}) (a : V ⟶ U) (b : V ⟶ D), a ≫ φ = b ≫ D.ι →
      b.appTop r * a.appTop ((W.homOfLE hUO).appTop g) = 1)
    (x : X) (hO : π x ∈ O) (hD : q x ∈ D) :
    ∃ z : D.toScheme, z ∈ D.toScheme.basicOpen r ∧ D.ι z = q x := by
  let V : X.Opens := π ⁻¹ᵁ O ⊓ q ⁻¹ᵁ D
  let α : V.toScheme ⟶ O := π.resLE O V inf_le_left
  let β : V.toScheme ⟶ D := q.resLE D V inf_le_right
  have hα : α ≫ O.ι = V.ι ≫ π := Scheme.Hom.resLE_comp_ι _ _
  have hβ : β ≫ D.ι = V.ι ≫ q := Scheme.Hom.resLE_comp_ι _ _
  have e₁ : j ∣_ V ≫ α = (j ⁻¹ᵁ V).ι ≫ W.homOfLE hUO := by
    rw [← cancel_mono O.ι, Category.assoc, hα, morphismRestrict_ι_assoc, h₁, Category.assoc,
      Scheme.homOfLE_ι]
  have e₂ := hr _ (j ⁻¹ᵁ V).ι (j ∣_ V ≫ β) (by
    rw [Category.assoc, hβ, morphismRestrict_ι_assoc, h₂])
  have e₃ : β.appTop r * α.appTop g = 1 := by
    apply (j ∣_ V).app_injective ⊤
    change (j ∣_ V).appTop _ = (j ∣_ V).appTop _
    rw [map_mul, map_one, ← e₂, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e₁, Scheme.Hom.comp_appTop (j ⁻¹ᵁ V).ι,
      CommRingCat.comp_apply]
  have e₄ : β ⁻¹ᵁ D.toScheme.basicOpen r = ⊤ := by
    rw [Scheme.preimage_basicOpen_top]
    exact Scheme.basicOpen_of_isUnit _ (IsUnit.of_mul_eq_one _ e₃)
  refine ⟨β ⟨x, hO, hD⟩, e₄.ge (Set.mem_univ (⟨x, hO, hD⟩ : V.toScheme)), ?_⟩
  exact (Scheme.Hom.comp_apply β D.ι _).symm.trans congr($hβ ⟨x, hO, hD⟩)
end GlobalTheory.DenseClosedAffineSubsets
