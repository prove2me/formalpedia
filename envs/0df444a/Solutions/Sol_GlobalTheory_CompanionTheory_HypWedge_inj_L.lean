-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HypWedge.inj_L
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:07:23.726432+00:00
-- url     : https://prove2.me/submissions/49191f31-016d-47fd-bf3f-33edc79580cd

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FormComponentOfWedgeClassZero
import Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_key_D
import Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_Nc_spec
import Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_rT_sR
import Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_Lc_spec
import Theorems.Thm_GlobalTheory_CatCoh_commAlgFunctorCocyclesOne_eq_ker
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_toO
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
open KaehlerDifferential
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HypWedge
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}
namespace GlobalTheory.CompanionTheory.HypWedge
theorem _root_.solution (hs : Function.Surjective (toO F)) (hcl : Closed1 F = ⊤) (τ : H1 F →ₗ[R] cechDeRhamTotalCocyclesOne F)
    (hτ : ∀ v, H1.mk F (cechDeRhamTotalCocyclesOne.fn F (τ v)) = v) (mu : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F)
    (hmu : ∀ (f : Z1 F) (w : Glob1 F) (T T' : C) (φ : T ⟶ T'), mu (f ⊗ₜ w) T T' φ = f.1 T T' φ • w.1 T')
    (hmu3 : ∀ (t : Z1 F ⊗[R] Glob1 F) (β : A0 F),
      (∀ (T T' : C) (φ : T ⟶ T'), mu t T T' φ = β T' - p1 F φ (β T)) →
        (H1.mk F).rTensor (Glob1 F) t = 0)
    (nu : ⋀[R]^2 (Glob1 F) →ₗ[R] W0 F 2)
    (hnu : ∀ (a b : Glob1 F) (T : C), nu (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (u : H1 F ⊗[R] Glob1 F) (x : ⋀[R]^2 (Glob1 F)) (c : Tot1 F)
    (hc : dTot1 F c = (Lc hcl τ u + Nc hcl x).1) : u = 0 := by
  have hL := Lc_spec hcl τ mu hmu u
  have hN := Nc_spec hcl nu hnu x
  have hz : d1 F c.1 = 0 := by
    have h : d1 F c.1 = (Lc hcl τ u).1.1 + (Nc hcl x).1.1 := congrArg Prod.fst hc
    rw [h, hL.1, hN, add_zero]
  have hf : c.1 ∈ Z1 F := by rw [commAlgFunctorCocyclesOne_eq_ker]; exact hz
  obtain ⟨β, hβ, -⟩ := key_D hs c.1 hf
  have ha : ∀ (T T' : C) (φ : T ⟶ T'), mu (sR τ u) T T' φ = (c.2 - β) T' - p1 F φ ((c.2 - β) T) := by
    intro T T' φ
    have h : c.2 T' - p1 F φ (c.2 T) - D R _ (c.1 T T' φ) =
        (Lc hcl τ u).1.2.1 T T' φ + (Nc hcl x).1.2.1 T T' φ :=
      congrArg (fun y : Tot2 F ↦ y.2.1 T T' φ) hc
    rw [hL.2, hN, hβ] at h
    have h' : mu (sR τ u) T T' φ = c.2 T' - p1 F φ (c.2 T) - (β T' - p1 F φ (β T)) := by
      rw [h]; exact (add_zero _).symm
    rw [h']
    simp only [Pi.sub_apply, map_sub]
    abel
  have := hmu3 _ _ ha
  rwa [rT_sR τ hτ] at this
end GlobalTheory.CompanionTheory.HypWedge
