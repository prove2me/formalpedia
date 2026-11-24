-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeAlt.one_cob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:45:45.46018+00:00
-- url     : https://prove2.me/submissions/2eeb74a4-431e-422c-a8e0-86150247e515

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOfRTensor
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_exists_of_dTot1
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_exists_proj
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_tensor_prim
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_mu_pull
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_rTensor_pull
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_exists_of_rTensor
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_exists_of_prim
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_toO
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_cechDeRhamTotalCocyclesTwo_one
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
theorem _root_.solution (m p q : CoefMap (RingHom.id R) F G) (muF : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F)
    (muG : Z1 G ⊗[R] Glob1 G →ₗ[R] A1 G)
    (hF : ∀ f ω T T' φ, muF (f ⊗ₜ ω) T T' φ = f.1 T T' φ • ω.1 T')
    (hG : ∀ f ω T T' φ, muG (f ⊗ₜ ω) T T' φ = f.1 T T' φ • ω.1 T')
    (hsur : ∀ a : A1 F, (∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''),
      a T T'' (φ ≫ ψ) = p1 F ψ (a T T' φ) + a T' T'' ψ) → ∃ t, muF t = a)
    (hker : ∀ (t : Z1 G ⊗[R] Glob1 G) (β : A0 G),
      (∀ T T' φ, muG t T T' φ = β T' - p1 G φ (β T)) → (H1.mk G).rTensor (Glob1 G) t = 0)
    (hsG : Function.Surjective (toO G))
    (hb1 : Function.Bijective fun x : H1 F × H1 F ↦ p.pull1 x.1 + q.pull1 x.2)
    (hb2 : Function.Bijective fun x : Glob1 F × Glob1 F ↦ pullGlob1 p x.1 + pullGlob1 q x.2)
    (hm1 : ∀ c, m.pull1 c = p.pull1 c + q.pull1 c)
    (hm2 : ∀ ω, pullGlob1 m ω = pullGlob1 p ω + pullGlob1 q ω) (z : cechDeRhamTotalCocyclesTwo F) (hz : z.1.1 = 0)
    (h : pullHyp2 m (Hyp2.mk F z) = pullHyp2 p (Hyp2.mk F z) + pullHyp2 q (Hyp2.mk F z)) :
    ∃ β : A0 F, ∀ (T T' : C) (φ : T ⟶ T'), z.1.2.1 T T' φ = β T' - p1 F φ (β T) := by
  obtain ⟨t, ht⟩ := hsur z.1.2.1 fun T T' T'' φ ψ ↦ by
    have := cechDeRhamTotalCocyclesTwo.one z φ ψ
    rw [hz] at this
    simpa using this
  obtain ⟨e, he⟩ := exists_of_prim m p q z hz h
  obtain ⟨β, hβ, -⟩ := exists_of_dTot1 hsG e _ _ he
  let s := TensorProduct.map m.pullbackOneCocycle (pullGlob1 m) t - TensorProduct.map p.pullbackOneCocycle (pullGlob1 p) t -
    TensorProduct.map q.pullbackOneCocycle (pullGlob1 q) t
  have hs : (H1.mk G).rTensor (Glob1 G) s = 0 := hker s β fun T T' φ ↦ by
    rw [← hβ T T' φ]
    simp only [s, map_sub, Pi.sub_apply]
    rw [mu_pull m muF muG hF hG, mu_pull p muF muG hF hG, mu_pull q muF muG hF hG, ht]
    rfl
  obtain ⟨P, -, hPp, hPq, -, -⟩ := exists_proj p.pull1 q.pull1 hb1
  obtain ⟨-, Q, -, -, hQp, hQq⟩ := exists_proj (pullGlob1 p) (pullGlob1 q) hb2
  have hT := tensor_prim p.pull1 q.pull1 m.pull1 (pullGlob1 p) (pullGlob1 q) (pullGlob1 m) P Q
    hPp hPq hQp hQq hm1 hm2 ((H1.mk F).rTensor (Glob1 F) t) (by
      simp only [s, map_sub, rTensor_pull] at hs
      rwa [sub_sub, sub_eq_zero] at hs)
  obtain ⟨β', hβ'⟩ := exists_of_rTensor muF hF t hT
  exact ⟨β', fun T T' φ ↦ by rw [← ht]; exact hβ' T T' φ⟩
end GlobalTheory.CompanionTheory.HodgeAlt
