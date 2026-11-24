-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeAlt.two_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:07:17.344012+00:00
-- url     : https://prove2.me/submissions/03dabaa7-1b20-4d8e-9c83-cecb3dab4265

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOfRTensor
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_eta_eq_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_exists_proj
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_wedge_prim
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_exists_of_prim
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_nu_pull
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_toO
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_cechDeRhamTotalCocyclesTwo_two
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
theorem _root_.solution (m p q : CoefMap (RingHom.id R) F G) [Module.Finite R (Glob1 F)]
    [Module.Projective R (Glob1 F)] (nuF : ⋀[R]^2 (Glob1 F) →ₗ[R] W0 F 2)
    (nuG : ⋀[R]^2 (Glob1 G) →ₗ[R] W0 G 2)
    (hF : ∀ a b T, nuF (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (hG : ∀ a b T, nuG (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (hinj : Function.Injective nuG)
    (hsur : ∀ w : W0 F 2, (∀ (T T' : C) (φ : T ⟶ T'), w T' = pOm F 2 φ (w T)) → ∃ t, nuF t = w)
    (hcG : Closed1 G = ⊤) (hsG : Function.Surjective (toO G))
    (hb2 : Function.Bijective fun x : Glob1 F × Glob1 F ↦ pullGlob1 p x.1 + pullGlob1 q x.2)
    (hm2 : ∀ ω, pullGlob1 m ω = pullGlob1 p ω + pullGlob1 q ω) (z : cechDeRhamTotalCocyclesTwo F) (h1 : z.1.1 = 0)
    (h2 : z.1.2.1 = 0)
    (h : pullHyp2 m (Hyp2.mk F z) = pullHyp2 p (Hyp2.mk F z) + pullHyp2 q (Hyp2.mk F z)) :
    z.1.2.2 = 0 := by
  obtain ⟨τ, hτ⟩ := hsur z.1.2.2 fun T T' φ ↦ by
    have := cechDeRhamTotalCocyclesTwo.two z φ
    rw [h2] at this
    simpa using this
  obtain ⟨e, he⟩ := exists_of_prim m p q z h1 h
  have h0 : (pullTot2 m z.1 - pullTot2 p z.1 - pullTot2 q z.1).2.1 = 0 := by
    funext T T' φ
    change (pullTot2 m z.1).2.1 T T' φ - (pullTot2 p z.1).2.1 T T' φ -
      (pullTot2 q z.1).2.1 T T' φ = 0
    simp only [pullTot2_a, h2, Pi.zero_apply, map_zero, sub_zero]
  rw [h0] at he
  have hw := eta_eq_zero hcG hsG e _ he
  have hν : nuG (exteriorPower.map 2 (pullGlob1 m) τ - exteriorPower.map 2 (pullGlob1 p) τ -
      exteriorPower.map 2 (pullGlob1 q) τ) = 0 := by
    funext T
    have := congrFun hw T
    rw [map_sub, map_sub, Pi.sub_apply, Pi.sub_apply, nu_pull m nuF nuG hF hG,
      nu_pull p nuF nuG hF hG, nu_pull q nuF nuG hF hG, hτ]
    exact this
  have hz := hinj (hν.trans (map_zero nuG).symm)
  obtain ⟨P, Q, hPp, hPq, hQp, hQq⟩ := exists_proj (pullGlob1 p) (pullGlob1 q) hb2
  have ht : τ = 0 := wedge_prim (pullGlob1 p) (pullGlob1 q) (pullGlob1 m) P Q hPp hPq hQp hQq hm2 τ
    (by rwa [sub_sub, sub_eq_zero] at hz)
  rw [← hτ, ht, map_zero]
end GlobalTheory.CompanionTheory.HodgeAlt
