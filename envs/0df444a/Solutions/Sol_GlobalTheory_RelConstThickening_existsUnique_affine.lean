-- Prove2me | solution 1 for GlobalTheory.RelConstThickening.existsUnique_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:18:02.177603+00:00
-- url     : https://prove2.me/submissions/da826526-f31c-4ee6-8cda-1fd5458fe0a4

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__DenseInterior_23def473f6482931
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualNumberSectionsUniqueDecomposition
import Theorems.Thm_GlobalTheory_RelConstThickening_existsUnique_of_isPushout
import Theorems.Thm_GlobalTheory_RelConstThickening_fromSpec_appLE_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.RelConstThickening
namespace GlobalTheory.RelConstThickening
theorem _root_.solution {X Z P : Scheme.{0}} (U : X.affineOpens) (h : Z ⟶ X)
    (p₁ : P ⟶ Sp (DualNumber Γ(X, U.1))) (p₂ : P ⟶ Z)
    (H : IsPullback p₂ p₁ h (spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) ≫ GlobalTheory.LogKS.chart U))
    {V : Z.Opens} (hV : IsAffineOpen V) (hVU : V ≤ h ⁻¹ᵁ U.1) (F : Γ(P, p₂ ⁻¹ᵁ V)) : ∃! ab : Γ(Z, V) × Γ(Z, V),
      F = (p₂.app V).hom ab.1 + constFn p₁ _ DualNumber.eps * (p₂.app V).hom ab.2 := by
  refine existsUnique_of_isPushout (K := Γ(X, U.1)) (h.appLE U.1 V hVU).hom (p₂.app V) (constHom p₁ (p₂ ⁻¹ᵁ V)) ?_ F
  have e0 : (⊤ : (Spec Γ(X, U.1)).Opens) ≤ U.2.fromSpec ⁻¹ᵁ U.1 := U.2.fromSpec_preimage_self.ge
  have e : (⊤ : (Sp (DualNumber Γ(X, U.1))).Opens) ≤
      (spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) ≫ GlobalTheory.LogKS.chart U) ⁻¹ᵁ U.1 := fun x _ =>
    e0 (Set.mem_univ (spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) x))
  have po := (isIso_pushoutSection_iff H (US := U.1) (UT := ⊤) (UX := V) (UY := p₂ ⁻¹ᵁ V) e hVU
    (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ U.2
      (isAffineOpen_top _) hV)
  refine po.of_iso (Iso.refl _) (Iso.refl _) (Scheme.ΓSpecIso (.of (DualNumber Γ(X, U.1)))) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp
  · have e1 : (spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) ≫ GlobalTheory.LogKS.chart U).appLE U.1 ⊤ e =
        U.2.fromSpec.appLE U.1 ⊤ e0 ≫ (spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1)))).appLE ⊤ ⊤ le_top :=
      (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    have e2 : (spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1)))).appLE ⊤ ⊤ le_top ≫
        (Scheme.ΓSpecIso (.of (DualNumber Γ(X, U.1)))).hom =
        (Scheme.ΓSpecIso (.of Γ(X, U.1))).hom ≫ CommRingCat.ofHom (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) := by
      rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    have e3 := fromSpec_appLE_top U.2 e0
    rw [e1, e3]
    exact (Category.assoc _ _ _).trans
      ((congrArg ((Scheme.ΓSpecIso Γ(X, U.1)).inv ≫ ·) e2).trans (Iso.inv_hom_id_assoc _ _))
  · simp [Scheme.Hom.app_eq_appLE]
  · ext x; simp [constHom]
end GlobalTheory.RelConstThickening
