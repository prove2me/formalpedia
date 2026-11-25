-- Prove2me | solution 1 for GlobalTheory.GenExtendNormal.existsUnique_gen_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:13:52.027164+00:00
-- url     : https://prove2.me/submissions/14d1729d-68af-4098-b9c7-fb28f4d41935

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueGeneratorExtendDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueRigidifiedGeneratorExtendNormal
import Theorems.Thm_GlobalTheory_GenExtendNormal_mem_range_of_notMem
import Theorems.Thm_GlobalTheory_GenExtendNormal_unit_ext_of_isOpenImmersion
import Theorems.Thm_GlobalTheory_DvrModel_isLocallyNoetherian
import Theorems.Thm_GlobalTheory_DvrModel_wchart_comp
import Theorems.Thm_GlobalTheory_exists_germToFunctionField_eq_of_coheight_eq_one
import Theorems.Thm_GlobalTheory_forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth
import Theorems.Thm_GlobalTheory_germToFunctionField_mem_range_stalk
import Theorems.Thm_GlobalTheory_germToFunctionField_res
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.GenExtendNormal
open GlobalTheory.DvrModel
namespace GlobalTheory.GenExtendNormal
theorem _root_.solution :
    ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], Geo.Tor.IsNormalScheme S → ∀ (U H HU X : Scheme.{0}) [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j] (p : H ⟶ S) (e : S ⟶ H) (jH : HU ⟶ H) (pU : HU ⟶ U) (eU : U ⟶ HU), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → IsPullback jH pU p j → eU ≫ jH = j ≫ e → ∀ (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (H ⟶ X)) (ε : I → ℤ) (t : LB.Gen (LB.LinComb L (fun i => jH ≫ φ i) ε)) (ρ : LB.Gen (LB.LinComb L (fun i => e ≫ φ i) ε)), t.IsGen → ρ.IsGen → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eU) (LB.pullGen L _ _ ρ j) → ∃! c : LB.Gen (LB.LinComb L φ ε), c.IsGen ∧ LB.pullGen L _ _ c jH = t := by
  intro S _ _ hS U H HU X _ j _ p e jH pU eU hsm hgi he hP heU L hL I _ φ ε t ρ ht hρ hc
  have := GlobalTheory.IsNormalScheme.of_pred hS
  have : IsIntegral H := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian p
  have : IsLocallyNoetherian H := LocallyOfFiniteType.isLocallyNoetherian p
  have : GlobalTheory.IsNormalScheme H := GlobalTheory.IsNormalScheme.of_pred
    (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth p hS)
  have : IsOpenImmersion jH :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hP.flip inferInstance
  have : Nonempty HU := ⟨eU (Nonempty.some inferInstance)⟩
  have hW (a) (y : HU) : y ∈ LB.wchart L (fun i ↦ jH ≫ φ i) a ↔ jH y ∈ LB.wchart L φ a := by
    rw [wchart_comp]; rfl
  have hex (a : I → L.ι) : ∃ s : Γ(H, LB.wchart L φ a)ˣ, ∀ y, jH y ∈ LB.wchart L φ a →
      gm jH y _ s = gm (𝟙 HU) y (LB.wchart L (fun i ↦ jH ≫ φ i) a) (t.s a) := by
    by_cases hne : ∃ y, jH y ∈ LB.wchart L φ a
    swap
    · exact ⟨1, fun y hy ↦ (hne ⟨y, hy⟩).elim⟩
    obtain ⟨y₀, hy₀⟩ := hne
    let A : H.Opens := jH ''ᵁ LB.wchart L (fun i ↦ jH ≫ φ i) a
    have hA : A ≤ LB.wchart L φ a := by
      rintro _ ⟨y, hy, rfl⟩
      exact (hW a y).1 hy
    have : Nonempty A := ⟨⟨_, y₀, (hW a y₀).2 hy₀, rfl⟩⟩
    have : Nonempty (LB.wchart L φ a) := ⟨⟨_, hy₀⟩⟩
    let τ : Γ(H, A)ˣ := Units.map (jH.appIso _).inv.hom.toMonoidHom (LB.ts t a)
    have hτ : ∀ (Z : Scheme.{0}) (r : Z ⟶ HU) (z : Z), jH (r z) ∈ A →
        gm (r ≫ jH) z A τ = gm r z (LB.wchart L (fun i ↦ jH ≫ φ i) a) (t.s a) := by
      intro Z r z hz
      rw [← gm_pull r jH z A hz, ← gm_res r z (jH.preimage_image_eq _).le hz]
      exact congrArg _ (Units.ext (congrArg (fun f ↦ f.hom (LB.ts t a).val)
        (jH.appIso_inv_app (LB.wchart L (fun i ↦ jH ≫ φ i) a))))
    have hmem : ∀ x ∈ LB.wchart L φ a, Order.coheight x = 1 →
        H.germToFunctionField A τ.val ∈ (algebraMap (H.presheaf.stalk x) H.functionField).range ∧
        H.germToFunctionField A (τ⁻¹).val ∈
          (algebraMap (H.presheaf.stalk x) H.functionField).range := fun x hx h1 ↦ by
      by_cases hxU : p x ∈ Set.range j
      · obtain ⟨u, hu⟩ := hxU
        obtain ⟨y, rfl, -⟩ := Scheme.exists_preimage_of_isPullback hP x u hu.symm
        have : jH y ∈ A := ⟨y, (hW a y).2 hx, rfl⟩
        exact ⟨germToFunctionField_mem_range_stalk A _ this,
          germToFunctionField_mem_range_stalk A _ this⟩
      · exact mem_range_of_notMem he hP heU hL ht hρ hc x h1 hxU a hx A τ hτ
    obtain ⟨s₁, h₁⟩ := exists_germToFunctionField_eq_of_coheight_eq_one _ _
      fun x hx h1 ↦ (hmem x hx h1).1
    obtain ⟨s₂, h₂⟩ := exists_germToFunctionField_eq_of_coheight_eq_one _ _
      fun x hx h1 ↦ (hmem x hx h1).2
    have h₁₂ : s₁ * s₂ = 1 := H.germToFunctionField_injective _ (by
      rw [map_mul, h₁, h₂, ← map_mul, Units.mul_inv, map_one, map_one])
    let s : Γ(H, LB.wchart L φ a)ˣ := ⟨s₁, s₂, h₁₂, (mul_comm _ _).trans h₁₂⟩
    have hs : res hA s = τ := Units.ext (H.germToFunctionField_injective A
      ((germToFunctionField_res hA s₁).trans h₁))
    refine ⟨s, fun y hy ↦ ?_⟩
    have hyA : jH y ∈ A := ⟨y, (hW a y).2 hy, rfl⟩
    rw [← gm_res jH y hA hyA, hs, ← hτ _ (𝟙 HU) y hyA, Category.id_comp]
  choose s hs using hex
  have hpull (c : LB.Gen (LB.LinComb L φ ε)) (a) (y) (hy : jH y ∈ LB.wchart L φ a) :
      gm (𝟙 HU) y (LB.wchart L (fun i ↦ jH ≫ φ i) a) ((LB.pullGen L _ _ c jH).s a) =
        gm jH y (LB.wchart L φ a) (c.s a) :=
    (gm_res _ y _ ((hW a y).2 hy) _).trans ((gm_pull _ _ y _ hy _).trans
      (by rw [Category.id_comp]; rfl))
  refine ⟨⟨s⟩, ⟨fun a b ↦ unit_ext_of_isOpenImmersion jH fun y hy ↦ ?_, ?_⟩, ?_⟩
  · have := gen_trans ht (𝟙 HU) y ((hW a y).2 hy.1) ((hW b y).2 hy.2)
    rw [← hs a y hy.1, ← hs b y hy.2] at this
    refine (gm_res jH y _ hy _).trans (this.trans (Eq.symm ((map_mul _ _ _).trans ?_)))
    refine congrArg₂ (· * ·) ((gm_linComb L φ ε jH y a b hy.1 hy.2).trans ?_) (gm_res jH y _ hy _)
    simp only [trF, Category.id_comp]
  · refine congrArg LB.Gen.mk (funext fun a ↦ unit_ext fun y hy ↦ ?_)
    exact (hpull ⟨s⟩ a y ((hW a y).1 hy)).trans (hs a y ((hW a y).1 hy))
  · rintro ⟨c⟩ ⟨-, rfl⟩
    refine congrArg LB.Gen.mk (funext fun a ↦ unit_ext_of_isOpenImmersion jH fun y hy ↦ ?_)
    exact (hpull ⟨c⟩ a y hy).symm.trans (hs a y hy).symm
end GlobalTheory.GenExtendNormal
