-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.OneFormCoh.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:45:47.851535+00:00
-- url     : https://prove2.me/submissions/237fff8e-060f-4176-97de-e877b1f1089c

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExtendedFormNaturality
import Theorems.Thm_GlobalTheory_CompanionTheory_OneFormCoh_extForm_sum
import Theorems.Thm_GlobalTheory_CompanionTheory_OneFormCoh_muMap_tmul
import Theorems.Thm_GlobalTheory_CompanionTheory_OneFormCoh_extForm_muMap
import Theorems.Thm_GlobalTheory_CompanionTheory_OneFormCoh_sum_contr
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.OneFormCoh
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
namespace GlobalTheory.CompanionTheory.OneFormCoh
theorem _root_.solution (hF : Framed F) :
    ∃ mu : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F, (∀ f ω T T' φ, mu (f ⊗ₜ ω) T T' φ = f.1 T T' φ • ω.1 T') ∧
      (∀ a : A1 F, (∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''),
        a T T'' (φ ≫ ψ) = p1 F ψ (a T T' φ) + a T' T'' ψ) → ∃ t, mu t = a) ∧
      ∀ (t : Z1 F ⊗[R] Glob1 F) (β : A0 F), (∀ T T' φ, mu t T T' φ = β T' - p1 F φ (β T)) →
        (H1.mk F).rTensor (Glob1 F) t = 0 := by
  obtain ⟨-, hp, hfin, hproj⟩ := hF
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R (GlobalTheory.CechDR.Glob1 F)
  obtain ⟨w, l, hw⟩ : ∃ (w : Fin n → GlobalTheory.CechDR.Glob1 F) (l : Fin n → GlobalTheory.CechDR.Glob1 F →ₗ[R] R),
      ∀ v, ∑ i, l i v • w i = v := by
    refine ⟨fun i => f (Pi.single i 1), fun i => LinearMap.proj i ∘ₗ g, fun v => ?_⟩
    have hsum : ∑ i, g v i • (Pi.single i 1 : Fin n → R) = g v := by
      ext j
      simp [Pi.single_apply]
    calc ∑ i, (LinearMap.proj i ∘ₗ g) v • f (Pi.single i 1)
        = f (∑ i, g v i • (Pi.single i 1 : Fin n → R)) := by
          rw [map_sum]
          simp only [map_smul, LinearMap.comp_apply, LinearMap.proj_apply]
      _ = v := by
          rw [hsum]
          exact LinearMap.congr_fun hfg v
  refine ⟨GlobalTheory.CompanionTheory.OneFormCoh.muMap F, fun x ω T T' φ => GlobalTheory.CompanionTheory.OneFormCoh.muMap_tmul F x ω φ, ?_, ?_⟩
  · intro a ha
    refine ⟨∑ i, GlobalTheory.CompanionTheory.OneFormCoh.pushZ F hp (l i) a ha ⊗ₜ w i, ?_⟩
    funext T T' φ
    rw [map_sum]
    simp only [Finset.sum_apply, GlobalTheory.CompanionTheory.OneFormCoh.muMap_tmul]
    exact GlobalTheory.CompanionTheory.OneFormCoh.extForm_sum F hp w l hw T' (a T T' φ)
  · intro t β hβ
    have hzero : ∀ i, GlobalTheory.CatCoh.H1.mk F
        (GlobalTheory.CompanionTheory.OneFormCoh.contr F (l i) t) = 0 := by
      intro i
      rw [GlobalTheory.CatCoh.H1.mk_eq_zero]
      refine ⟨fun T => GlobalTheory.CompanionTheory.OneFormCoh.extForm F hp (l i) T (β T), ?_⟩
      funext T T' φ
      rw [GlobalTheory.CatCoh.amitsur_d0_apply, ← GlobalTheory.CompanionTheory.OneFormCoh.extForm_muMap F hp, hβ, map_sub,
        GlobalTheory.CompanionTheory.OneFormCoh.extended_form_naturality]
    rw [← GlobalTheory.CompanionTheory.OneFormCoh.sum_contr F w l hw t, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [LinearMap.rTensor_tmul, hzero, TensorProduct.zero_tmul]
end GlobalTheory.CompanionTheory.OneFormCoh
