-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HypWedge.surj_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:06:23.214106+00:00
-- url     : https://prove2.me/submissions/b496588b-2e3e-42e5-a15b-9d42fe1c04a4

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FormComponentOfWedgeClassZero
import Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_Nc_spec
import Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_Lc_spec
import Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_beta_of
import Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_add_rearr
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_cechDeRhamTotalCocyclesTwo_one
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HypWedge
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}
set_option maxHeartbeats 1000000
namespace GlobalTheory.CompanionTheory.HypWedge
theorem _root_.solution (hcl : Closed1 F = ⊤) (τ : H1 F →ₗ[R] cechDeRhamTotalCocyclesOne F)
    (hτ : ∀ v, H1.mk F (cechDeRhamTotalCocyclesOne.fn F (τ v)) = v) (mu : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F)
    (hmu : ∀ (f : Z1 F) (w : Glob1 F) (T T' : C) (φ : T ⟶ T'), mu (f ⊗ₜ w) T T' φ = f.1 T T' φ • w.1 T')
    (hmu2 : ∀ a : A1 F, (∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''),
      a T T'' (φ ≫ ψ) = p1 F ψ (a T T' φ) + a T' T'' ψ) → ∃ t, mu t = a)
    (nu : ⋀[R]^2 (Glob1 F) →ₗ[R] W0 F 2)
    (hnu : ∀ (a b : Glob1 F) (T : C), nu (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (hnus : ∀ w : W0 F 2, (∀ (T T' : C) (φ : T ⟶ T'), w T' = pOm F 2 φ (w T)) → ∃ t, nu t = w)
    (c : cechDeRhamTotalCocyclesTwo F) (hc : H2.mk F (fn2 F c) = 0) :
    ∃ u x, Hyp2.mk F c = Hyp2.mk F (Lc hcl τ u) + Hyp2.mk F (Nc hcl x) := by
  obtain ⟨f, hf⟩ := H2.mk_eq_zero.1 hc
  have hf' : d1 F f = c.1.1 := hf
  let b1 : cechDeRhamTotalCocyclesTwo F := ⟨dTot1 F (f, 0), dTot1_mem F _⟩
  let c1 : cechDeRhamTotalCocyclesTwo F := c - b1
  have z1 : ∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''), c1.1.1 T T' T'' φ ψ = 0 := fun T T' T'' φ ψ ↦ by
    change c.1.1 T T' T'' φ ψ - d1 F f T T' T'' φ ψ = 0
    rw [hf']; exact sub_self _
  have ha : ∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''),
      c1.1.2.1 T T'' (φ ≫ ψ) = p1 F ψ (c1.1.2.1 T T' φ) + c1.1.2.1 T' T'' ψ := fun T T' T'' φ ψ ↦ by
    have := cechDeRhamTotalCocyclesTwo.one c1 φ ψ
    rwa [z1, map_zero, add_zero] at this
  obtain ⟨t, ht⟩ := hmu2 _ ha
  obtain ⟨β, hβ⟩ := beta_of τ hτ mu hmu t
  obtain ⟨u, hu⟩ : ∃ u, u = LinearMap.rTensor (Glob1 F) (H1.mk F) t := ⟨_, rfl⟩
  rw [← hu] at hβ
  let b2 : cechDeRhamTotalCocyclesTwo F := ⟨dTot1 F (0, β), dTot1_mem F _⟩
  let c2 : cechDeRhamTotalCocyclesTwo F := c1 - Lc hcl τ u - b2
  have hL := Lc_spec hcl τ mu hmu u
  have z2 : ∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''), c2.1.1 T T' T'' φ ψ = 0 := fun T T' T'' φ ψ ↦ by
    change c1.1.1 T T' T'' φ ψ - (Lc hcl τ u).1.1 T T' T'' φ ψ - d1 F 0 T T' T'' φ ψ = 0
    rw [z1, hL.1, map_zero]
    simp
  have a2 : ∀ (T T' : C) (φ : T ⟶ T'), c2.1.2.1 T T' φ = 0 := fun T T' φ ↦ by
    change c1.1.2.1 T T' φ - (Lc hcl τ u).1.2.1 T T' φ -
      (β T' - p1 F φ (β T) - D R _ ((0 : C1 F) T T' φ)) = 0
    rw [hL.2, ← ht, hβ]
    simp
  have g : ∀ (T T' : C) (φ : T ⟶ T'), c2.1.2.2 T' = pOm F 2 φ (c2.1.2.2 T) := fun T T' φ ↦ by
    have := cechDeRhamTotalCocyclesTwo.two c2 φ
    rwa [a2, map_zero, add_zero] at this
  obtain ⟨x, hx⟩ := hnus _ g
  have e : c2 = Nc hcl x := by
    refine Subtype.ext ?_
    rw [Nc_spec hcl nu hnu x, hx]
    exact Tot2.ext z2 a2 fun _ ↦ rfl
  refine ⟨u, x, ?_⟩
  have e1 : Hyp2.mk F b1 = 0 := Hyp2.mk_eq_zero.2 ⟨_, rfl⟩
  have e2 : Hyp2.mk F b2 = 0 := Hyp2.mk_eq_zero.2 ⟨_, rfl⟩
  have e3 : c = Nc hcl x + Lc hcl τ u + b1 + b2 := by
    rw [← e]
    exact add_rearr c b1 _ b2
  rw [e3, map_add, map_add, map_add, e1, e2, add_zero, add_zero, add_comm]
end GlobalTheory.CompanionTheory.HypWedge
