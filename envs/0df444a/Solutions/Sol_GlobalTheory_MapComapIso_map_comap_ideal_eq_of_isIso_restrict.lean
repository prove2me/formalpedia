-- Prove2me | solution 1 for GlobalTheory.MapComapIso.map_comap_ideal_eq_of_isIso_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:43:29.842946+00:00
-- url     : https://prove2.me/submissions/2dca7b42-568d-43ef-98e9-b7f820cf5178

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapComapFlatStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapComapIdealSheafEqOfIsIsoRestrict
import Theorems.Thm_GlobalTheory_MapComapIso_map_comap_of_isIso
import Theorems.Thm_GlobalTheory_T_map_comap_eq_comap_map_of_flat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
open GlobalTheory GlobalTheory.MapComapIso
namespace GlobalTheory.MapComapIso
theorem _root_.solution :
    ∀ (W W' : Scheme.{0}) (π : W' ⟶ W) (U : W.Opens), QuasiCompact π → IsIso (π ∣_ U) →
      ∀ (τ : W.IdealSheafData) (V : W.affineOpens), V.1 ≤ U →
        ((τ.comap π).map π).ideal V = τ.ideal V := by
  intro W W' π U hq hiso τ V hVU
  have hpb := (isPullback_morphismRestrict π U).flip
  have hres : ((τ.comap π).map π).comap U.ι = τ.comap U.ι := by
    rw [GlobalTheory.T.map_comap_eq_comap_map_of_flat W W' U (π ⁻¹ᵁ U) π U.ι (π ⁻¹ᵁ U).ι (π ∣_ U) hpb inferInstance hq (τ.comap π),
      ← Scheme.IdealSheafData.comap_comp, ← morphismRestrict_ι, Scheme.IdealSheafData.comap_comp,
      map_comap_of_isIso]
  have hle : V.1 ≤ Scheme.Hom.opensRange U.ι := by rw [Scheme.Opens.opensRange_ι]; exact hVU
  let V' : U.toScheme.affineOpens := ⟨U.ι ⁻¹ᵁ V.1, V.2.preimage_of_isOpenImmersion U.ι hle⟩
  have himg : (⟨U.ι ''ᵁ V'.1, (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion U.ι).2 V'.2⟩ :
      W.affineOpens) = V := by
    apply Subtype.ext
    change U.ι ''ᵁ U.ι ⁻¹ᵁ V.1 = V.1
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hVU
  have h1 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion ((τ.comap π).map π) U.ι V'
  have h2 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion τ U.ι V'
  rw [hres, h2] at h1
  have h3 := Ideal.comap_injective_of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.Hom.appIso U.ι V'.1).inv).2 h1
  have h4 : ∀ A B : W.affineOpens, A = B →
      ((τ.comap π).map π).ideal A = τ.ideal A → ((τ.comap π).map π).ideal B = τ.ideal B := by
    rintro A B rfl h; exact h
  exact h4 _ V himg h3.symm
end GlobalTheory.MapComapIso
