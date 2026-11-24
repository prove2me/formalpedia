-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeAlt.exists_of_rTensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:28:20.146866+00:00
-- url     : https://prove2.me/submissions/409a3e82-e9e1-461f-813e-ac1f2b3fd28c

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOfRTensor
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeAlt
variable {R : Type} [CommRing R] {C D : Type} [Category.{0} C] [Category.{0} D]
  {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}
namespace GlobalTheory.CompanionTheory.HodgeAlt
theorem _root_.solution (muF : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F)
    (hF : ∀ f ω T T' φ, muF (f ⊗ₜ ω) T T' φ = f.1 T T' φ • ω.1 T') (t : Z1 F ⊗[R] Glob1 F)
    (ht : (H1.mk F).rTensor (Glob1 F) t = 0) :
    ∃ β : A0 F, ∀ (T T' : C) (φ : T ⟶ T'), muF t T T' φ = β T' - p1 F φ (β T) := by
  have hex : Function.Exact ((d0 F).codRestrict (Z1 F) (commAlgFunctorCoboundaryZero_mem_cocyclesOne F)) (H1.mk F) :=
    LinearMap.exact_map_mkQ_range _
  obtain ⟨u, rfl⟩ := (rTensor_exact (Glob1 F) hex (H1.mk_surjective F) t).1 ht
  clear ht
  induction u with
  | zero => exact ⟨0, by simp⟩
  | tmul g ω =>
    refine ⟨fun T ↦ g T • ω.1 T, fun T T' φ ↦ ?_⟩
    rw [LinearMap.rTensor_tmul, hF]
    change (g T' - mp F φ (g T)) • ω.1 T' = _
    rw [oneFormsMapOfFunctorMorphism_smul, ← ω.2 φ, sub_smul]
  | add x y hx hy =>
    obtain ⟨b, hb⟩ := hx
    obtain ⟨b', hb'⟩ := hy
    refine ⟨b + b', fun T T' φ ↦ ?_⟩
    simp only [map_add, Pi.add_apply, hb, hb']
    abel
end GlobalTheory.CompanionTheory.HodgeAlt
