-- Prove2me | solution 1 for GlobalTheory.CompRat.valAt_eq_of_finite_values_anyLevel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:28:38.096515+00:00
-- url     : https://prove2.me/submissions/e86f1a2c-046e-4d25-9f02-5b7053d2ae2a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_PermutesRefl
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsPeriodDomainParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsHolToFibPtAndCompFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearEquivLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RegularFunctionConstOfFiniteValuesAnyLevel
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_HolFibre_isHolTo_const
import Theorems.Thm_GlobalTheory_HolFibre_isHolTo_of_isPullback
import Theorems.Thm_GlobalTheory_LocLift_HasLifts_lift
import Theorems.Thm_GlobalTheory_LocLift_isHolTo_congr
import Theorems.Thm_GlobalTheory_coe_modNEquivTorsion_mk
import Theorems.Thm_GlobalTheory_exists_period_domain_param
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul
attribute [local simp] GlobalTheory.coe_modNEquivTorsion_mk



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CompRat
namespace GlobalTheory.CompRat
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (c : Coeff l) (j : c.F →+* ℂ) (f : Γ(Xo.XF c, ⊤)) (S : Set ℂ), S.Finite → (∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.snd _ _ = spMap j → valAt' x ⊤ f ∈ S) → ∀ i P P', IsPeriod (F.Di i) ty P → IsPeriod (F.Di i) ty P' → ∀ x x' : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.fst _ _ = F.u i P → x ≫ pullback.snd _ _ = spMap j → x' ≫ pullback.fst _ _ = F.u i P' → x' ≫ pullback.snd _ _ = spMap j → valAt' x ⊤ f = valAt' x' ⊤ f := by
  intro E _ _ _ H D l Xo σ g ty F _ _ hty c j f S hS hval i P P' hP hP' x x' hx1 hx2 hx1' hx2'
  classical
  have hty' : IsTypeFn H (F.Di i).p (F.Di i).q ty := by
    rw [(F.sig i).1, (F.sig i).2]
    exact hty
  obtain ⟨B, Q, hBo, hBc, hQ, huniq⟩ := GlobalTheory.exists_period_domain_param E H (F.Di i) g ty hty'
  have hcond : spMap σ = spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [← F.over_σ i P hP, ← hx1, ← hx2, Category.assoc, Category.assoc, pullback.condition]
  let y : (Fin (F.Di i).dim → ℂ) → (Sp ℂ ⟶ Xo.XF c) := fun b =>
    if hb : b ∈ B then pullback.lift (F.u i (Q b)) (spMap j) ((F.over_σ i _ (hQ.1 b hb)).trans hcond) else x
  have hy1 : ∀ b ∈ B, y b ≫ pullback.fst _ _ = F.u i (Q b) := fun b hb => by
    simp only [y, dif_pos hb, pullback.lift_fst]
  have hy2 : ∀ b ∈ B, y b ≫ pullback.snd _ _ = spMap j := fun b hb => by
    simp only [y, dif_pos hb, pullback.lift_snd]
  have hhol : IsHolTo B y :=
    GlobalTheory.HolFibre.isHolTo_of_isPullback (IsPullback.of_hasPullback _ _)
      (GlobalTheory.LocLift.isHolTo_congr (F.hol i _ B Q hBo hQ).1 hy1)
      (GlobalTheory.LocLift.isHolTo_congr (GlobalTheory.HolFibre.isHolTo_const hBo (spMap j)) hy2)
  have hcont : ContinuousOn (fun b => valAt' (y b) ⊤ f) B :=
    ((hhol ⊤ f).2.mono fun b hb => ⟨hb, le_of_eq rfl⟩).continuousOn
  have hfind : ∀ R, IsPeriod (F.Di i) ty R → ∀ z : Sp ℂ ⟶ Xo.XF c, z ≫ pullback.fst _ _ = F.u i R →
      z ≫ pullback.snd _ _ = spMap j → ∃ b ∈ B, y b = z := by
    intro R hR z hz1 hz2
    obtain ⟨b, ⟨hb, h, hh⟩, -⟩ := huniq R hR
    refine ⟨b, hb, pullback.hom_ext ?_ ?_⟩
    · rw [hy1 b hb, hz1]
      exact (F.fibre i _ _ (hQ.1 b hb) hR).2 ⟨LinearEquiv.refl _ _, h, fun _ _ => rfl,
        fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩, hh⟩
    · rw [hy2 b hb, hz2]
  obtain ⟨b, hb, e⟩ := hfind P hP x hx1 hx2
  obtain ⟨b', hb', e'⟩ := hfind P' hP' x' hx1' hx2'
  rw [← e, ← e']
  exact hBc.isPreconnected.constant_of_mapsTo hS.isDiscrete hcont (fun a ha => hval _ (hy2 a ha)) hb hb'
end GlobalTheory.CompRat
