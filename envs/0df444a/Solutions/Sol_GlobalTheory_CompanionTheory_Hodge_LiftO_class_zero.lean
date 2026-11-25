-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Hodge.LiftO.class_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:06:23.720573+00:00
-- url     : https://prove2.me/submissions/a157d4a4-2005-4dcf-999b-b457d8f63753

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExteriorPairingIotaTwo
import Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_eq_zero_of_tprim
import Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_mu_pull
import Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_rTensor_pull
import Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_exists_prim_cochain
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hodge GlobalTheory.CompanionTheory.Hodge.LiftO
variable {R : Type} [CommRing R] {C E : Type} [Category.{0} C] [Category.{0} E]
  {F : C ⥤ CommAlgCat.{0} R} {G : E ⥤ CommAlgCat.{0} R}
namespace GlobalTheory.CompanionTheory.Hodge.LiftO
theorem _root_.solution (m p q : CoefMap (RingHom.id R) F G)
    (hH : Function.Bijective fun x : H1 F × H1 F ↦ p.pull1 x.1 + q.pull1 x.2)
    (hW : Function.Bijective fun x : Glob1 F × Glob1 F ↦ pullGlob1 p x.1 + pullGlob1 q x.2)
    (hm1 : ∀ c, m.pull1 c = p.pull1 c + q.pull1 c)
    (hmW : ∀ ω, pullGlob1 m ω = pullGlob1 p ω + pullGlob1 q ω)
    (muF : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F) (muG : Z1 G ⊗[R] Glob1 G →ₗ[R] A1 G)
    (hF : ∀ f ω T T' φ, muF (f ⊗ₜ ω) T T' φ = f.1 T T' φ • ω.1 T')
    (hG : ∀ f ω T T' φ, muG (f ⊗ₜ ω) T T' φ = f.1 T T' φ • ω.1 T')
    (hG3 : ∀ (t : Z1 G ⊗[R] Glob1 G) (β : A0 G), (∀ T T' φ, muG t T T' φ = β T' - p1 G φ (β T)) →
      (H1.mk G).rTensor (Glob1 G) t = 0)
    (f : Z1 F) (t : Z1 F ⊗[R] Glob1 F)
    (ht : ∀ T T' φ, muF t T T' φ = KaehlerDifferential.D R _ (f.1 T T' φ)) :
    (H1.mk F).rTensor (Glob1 F) t = 0 := by
  obtain ⟨g, hg⟩ := exists_prim_cochain m p q hm1 f
  have hz := hG3 (TensorProduct.map m.pullbackOneCocycle (pullGlob1 m) t - TensorProduct.map p.pullbackOneCocycle (pullGlob1 p) t -
      TensorProduct.map q.pullbackOneCocycle (pullGlob1 q) t) (fun T ↦ KaehlerDifferential.D R _ (g T)) (fun T T' φ ↦ by
    have e := congrArg (KaehlerDifferential.D R (G.obj T')) (hg φ)
    simp only [map_sub, map_add] at e
    simp only [map_sub, Pi.sub_apply, mu_pull _ muF muG hF hG, ht, cechDeRhamCoefMapOneForms_D, p1_D]
    rw [e]
    simp only [CoefMap.pullCocycleOne_apply]
    abel)
  rw [map_sub, map_sub, rTensor_pull, rTensor_pull, rTensor_pull] at hz
  have e1 : m.pull1 = p.pull1 + q.pull1 := LinearMap.ext hm1
  have e2 : pullGlob1 m = pullGlob1 p + pullGlob1 q := LinearMap.ext hmW
  rw [e1, e2] at hz
  refine eq_zero_of_tprim p.pull1 q.pull1 (pullGlob1 p) (pullGlob1 q) hH hW _ ?_
  rw [sub_sub, sub_eq_zero] at hz
  exact hz
end GlobalTheory.CompanionTheory.Hodge.LiftO
