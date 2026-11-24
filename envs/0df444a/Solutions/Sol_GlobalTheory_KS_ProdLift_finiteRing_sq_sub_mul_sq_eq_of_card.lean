-- Prove2me | solution 1 for GlobalTheory.KS.ProdLift.finiteRing_sq_sub_mul_sq_eq_of_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:43:56.673812+00:00
-- url     : https://prove2.me/submissions/1fcefd62-219b-4e3e-910b-6ec83b3b8935

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueLocalDerivationAlongFibreFieldOfAffiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDerOfIsPushout
import Theorems.Thm_GlobalTheory_KS_ProdLift_exists_der_of_isPushout
import Theorems.Thm_GlobalTheory_KS_ProdLift_der_eq_of_isPushout
import Theorems.Thm_GlobalTheory_KS_ProdLift_pbT_eq
import Theorems.Thm_GlobalTheory_KS_ProdLift_appLE_constFn
import Theorems.Thm_GlobalTheory_KS_ProdLift_app_appLE
import Theorems.Thm_GlobalTheory_KS_ProdLift_preimage_le
import Theorems.Thm_GlobalTheory_LocDerExtK_exists_locDerK
import Theorems.Thm_GlobalTheory_LocDerExtK_locDerK_unique


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.ProdLift
namespace GlobalTheory.KS.ProdLift
theorem _root_.solution {K : Type} [Field K] {R : Type} [CommRing R] {Z Z₀ X Y : Scheme.{0}}
    {p q : Z ⟶ X} {s : X ⟶ Sp R} (H : IsPullback p q s s) {z : Z ⟶ Sp R} (hz : p ≫ s = z)
    {p₀ q₀ : Z₀ ⟶ Y} {s₀ : Y ⟶ Sp K} {z₀ : Z₀ ⟶ Sp K} (hp₀ : p₀ ≫ s₀ = z₀) (hq₀ : q₀ ≫ s₀ = z₀)
    {m : Y ⟶ X} {m₂ : Z₀ ⟶ Z} (hp : m₂ ≫ p = p₀ ≫ m) (hq : m₂ ≫ q = q₀ ≫ m) (D : R → K)
    {W W' : X.Opens} (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (Q : Z.Opens)
    (hQ : Q = p ⁻¹ᵁ W ⊓ q ⁻¹ᵁ W') :
    (∀ d d', LocDerK s₀ s m D W d → LocDerK s₀ s m D W' d' → ∃ d₂, LocDerK z₀ z m₂ D Q d₂ ∧
      (∀ f, d₂ Q (pbT p f Q) = pbT p₀ (d W f) _) ∧ ∀ f, d₂ Q (pbT q f Q) = pbT q₀ (d' W' f) _) ∧
    ∀ d₂ d₂', LocDerK z₀ z m₂ D Q d₂ → LocDerK z₀ z m₂ D Q d₂' →
      (∀ f : Γ(X, W), d₂ Q (pbT p f Q) = d₂' Q (pbT p f Q)) →
      (∀ f : Γ(X, W'), d₂ Q (pbT q f Q) = d₂' Q (pbT q f Q)) → ∀ O, O ≤ Q → d₂ O = d₂' O := by
  have hWQ : Q ≤ p ⁻¹ᵁ W := by rw [hQ]; exact inf_le_left
  have hW'Q : Q ≤ q ⁻¹ᵁ W' := by rw [hQ]; exact inf_le_right
  have h₁ : m₂ ⁻¹ᵁ Q ≤ p₀ ⁻¹ᵁ m ⁻¹ᵁ W := preimage_le hp hWQ
  have h₂ : m₂ ⁻¹ᵁ Q ≤ q₀ ⁻¹ᵁ m ⁻¹ᵁ W' := preimage_le hq hW'Q
  have hz' : q ≫ s = z := H.w.symm.trans hz
  have : IsAffine W.toScheme := hW
  have : IsAffine W'.toScheme := hW'
  have : IsAffine (⊤ : (Sp R).Opens).toScheme := isAffineOpen_top (Sp R)
  have hPb := Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := W') (UX := W) (by simp) (by simp) hQ
  have : IsAffine Q.toScheme := IsAffine.of_isPullback hPb
  have hQa : IsAffineOpen Q := this
  have hPo : IsPushout (s.appLE ⊤ W (by simp)) (s.appLE ⊤ W' (by simp)) (p.appLE W Q hWQ)
      (q.appLE W' Q hW'Q) :=
    (isPushout_appTop_of_isPullback hPb).of_iso (Scheme.Opens.topIso ⊤) W.topIso W'.topIso Q.topIso
      (Arrow.w (arrowResLEAppIso s ⊤ W _).hom).symm (Arrow.w (arrowResLEAppIso s ⊤ W' _).hom).symm
      (Arrow.w (arrowResLEAppIso p W Q _).hom).symm (Arrow.w (arrowResLEAppIso q W' Q _).hom).symm
  refine ⟨fun d d' hd hd' => ?_, fun d₂ d₂' e₁ e₂ ef ef' O hO => ?_⟩
  · let δ : Γ(X, W) → Γ(Z₀, m₂ ⁻¹ᵁ Q) := fun f => (p₀.appLE (m ⁻¹ᵁ W) (m₂ ⁻¹ᵁ Q) h₁).hom (d W f)
    let δ' : Γ(X, W') → Γ(Z₀, m₂ ⁻¹ᵁ Q) := fun f => (q₀.appLE (m ⁻¹ᵁ W') (m₂ ⁻¹ᵁ Q) h₂).hom (d' W' f)
    have hb : ∀ r, δ (constFn s W r) = constFn z₀ (m₂ ⁻¹ᵁ Q) (D r) := fun r => by
      simp only [δ]
      rw [hd.base W le_rfl r]
      exact appLE_constFn s₀ z₀ p₀ hp₀ h₁ (D r)
    have hb' : ∀ r, δ' (constFn s W' r) = constFn z₀ (m₂ ⁻¹ᵁ Q) (D r) := fun r => by
      simp only [δ']
      rw [hd'.base W' le_rfl r]
      exact appLE_constFn s₀ z₀ q₀ hq₀ h₂ (D r)
    have hR : ∀ r, δ ((s.appLE ⊤ W (by simp)).hom r) = δ' ((s.appLE ⊤ W' (by simp)).hom r) := by
      intro r
      obtain ⟨r', rfl⟩ : ∃ r', (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r' = r :=
        ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r, by simp⟩
      change δ (constFn s W r') = δ' (constFn s W' r')
      rw [hb, hb']
    obtain ⟨d0, hadd0, hmul0, hu0, hv0⟩ := exists_der_of_isPushout hPo (m₂.app Q).hom δ δ'
      (fun x y => by simp only [δ]; rw [hd.add W le_rfl, map_add])
      (fun x y => by
        simp only [δ]
        rw [hd.mul W le_rfl, map_add, map_mul, map_mul, app_appLE hp hWQ h₁ x, app_appLE hp hWQ h₁ y])
      (fun x y => by simp only [δ']; rw [hd'.add W' le_rfl, map_add])
      (fun x y => by
        simp only [δ']
        rw [hd'.mul W' le_rfl, map_add, map_mul, map_mul, app_appLE hq hW'Q h₂ x, app_appLE hq hW'Q h₂ y])
      hR
    have hbQ : ∀ r, d0 (constFn z Q r) = constFn z₀ (m₂ ⁻¹ᵁ Q) (D r) := fun r => by
      rw [← appLE_constFn s z p hz hWQ r, hu0, hb]
    obtain ⟨d₂, hd₂, hd₂Q⟩ := GlobalTheory.LocDerExtK.exists_locDerK K R Z₀ Z z₀ z m₂ D Q hQa d0 hadd0 hmul0 hbQ
    refine ⟨d₂, hd₂, fun f => ?_, fun f => ?_⟩
    · rw [hd₂Q, pbT_eq p f hWQ, hu0, pbT_eq p₀ _ h₁]
    · rw [hd₂Q, pbT_eq q f hW'Q, hv0, pbT_eq q₀ _ h₂]
  · refine GlobalTheory.LocDerExtK.locDerK_unique hQa d₂ d₂' e₁ e₂ ?_ O hO
    exact der_eq_of_isPushout hPo (m₂.app Q).hom (d₂ Q) (d₂' Q) (e₁.add Q le_rfl) (e₁.mul Q le_rfl)
      (e₂.add Q le_rfl) (e₂.mul Q le_rfl)
      (fun x => by rw [← pbT_eq p x hWQ]; exact ef x) (fun x => by rw [← pbT_eq q x hW'Q]; exact ef' x)
end GlobalTheory.KS.ProdLift
