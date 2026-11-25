-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Hodge.LiftO.closed_of_conn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:06:27.166967+00:00
-- url     : https://prove2.me/submissions/88f5daf6-114c-49d5-aa69-33032fb7cbbe

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExteriorPairingIotaTwo
import Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_eq_zero_of_prim
import Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_nu_pull
import Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_two_prim

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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hodge GlobalTheory.CompanionTheory.Hodge.LiftO
variable {R : Type} [CommRing R] {C E : Type} [Category.{0} C] [Category.{0} E]
  {F : C ⥤ CommAlgCat.{0} R} {G : E ⥤ CommAlgCat.{0} R}
namespace GlobalTheory.CompanionTheory.Hodge.LiftO
theorem _root_.solution (m p q : CoefMap (RingHom.id R) F G) [Module.Finite R (Glob1 F)]
    [Module.Projective R (Glob1 F)]
    (hW : Function.Bijective fun x : Glob1 F × Glob1 F ↦ pullGlob1 p x.1 + pullGlob1 q x.2)
    (hm1 : ∀ c, m.pull1 c = p.pull1 c + q.pull1 c)
    (hmW : ∀ ω, pullGlob1 m ω = pullGlob1 p ω + pullGlob1 q ω)
    (hC : Closed1 F = ⊤)
    (νF : ⋀[R]^2 (Glob1 F) →ₗ[R] W0 F 2) (νG : ⋀[R]^2 (Glob1 G) →ₗ[R] W0 G 2)
    (hF : ∀ a b T, νF (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (hG : ∀ a b T, νG (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (hinj : Function.Injective νG)
    (hsurj : ∀ w : W0 F 2, (∀ (T T' : C) (φ : T ⟶ T'), w T' = pOm F 2 φ (w T)) → ∃ t, νF t = w)
    (f : Z1 F) (β : A0 F)
    (hβ : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), β T' = p1 F φ (β T) + KaehlerDifferential.D R _ (f.1 T T' φ)) (T : C) :
    dOne R _ (β T) = 0 := by
  obtain ⟨t, ht⟩ := hsurj (fun T ↦ dOne R _ (β T)) (fun T T' φ ↦ by
    rw [hβ φ, map_add, dOne_D, add_zero, pOm_dOne])
  have h1 : exteriorPower.map 2 (pullGlob1 m) t =
      exteriorPower.map 2 (pullGlob1 p) t + exteriorPower.map 2 (pullGlob1 q) t := hinj (by
    rw [map_add]
    funext T
    rw [Pi.add_apply, nu_pull m νF νG hF hG, nu_pull p νF νG hF hG, nu_pull q νF νG hF hG, ht]
    exact two_prim m p q hW hm1 hC f β hβ T)
  have e2 : pullGlob1 m = pullGlob1 p + pullGlob1 q := LinearMap.ext hmW
  rw [e2] at h1
  have ht0 := eq_zero_of_prim (pullGlob1 p) (pullGlob1 q) hW t h1
  have := congrFun ht T
  rw [ht0, map_zero] at this
  exact this.symm
end GlobalTheory.CompanionTheory.Hodge.LiftO
