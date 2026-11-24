-- Prove2me | solution 1 for GlobalTheory.SectionKernel.exists_sec_of_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:22:27.717093+00:00
-- url     : https://prove2.me/submissions/1f4bd429-ea6d-4d9a-b053-6bf9a2fd452a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSectionEqMulOfVanishingModElement
import Theorems.Thm_GlobalTheory_SectionKernel_app_rs
import Theorems.Thm_GlobalTheory_SectionKernel_gs_sub
import Theorems.Thm_GlobalTheory_SectionKernel_gs_of_app_eq_zero
import Theorems.Thm_GlobalTheory_SectionKernel_gs_mul_eq_zero_iff
import Theorems.Thm_GlobalTheory_SectionKernel_surjective_of_isNilpotent
import Theorems.Thm_GlobalTheory_SectionKernel_exists_sec_of_local
import Theorems.Thm_GlobalTheory_SmallExtLift_mem_of_app_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_compat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SectionKernel
variable {X Y : Scheme.{0}}
variable {A A₀ : Type} [CommRing A] [CommRing A₀] {g₀ : A →+* A₀} {a : A}
  {f : X ⟶ Spec (CommRingCat.of A)} {f₀ : Y ⟶ Spec (CommRingCat.of A₀)} {j : Y ⟶ X}
namespace GlobalTheory.SectionKernel
theorem _root_.solution : ∀ (A A₀ A' : Type) [CommRing A] [CommRing A₀] [CommRing A'] (g₀ : A →+* A₀) (g' : A →+* A') (a : A), Function.Surjective g₀ → Function.Surjective g' → IsNilpotent (RingHom.ker g₀) → RingHom.ker g' = Ideal.span {a} → a ∈ RingHom.ker g₀ → (∀ x, a * x = 0 ↔ x ∈ RingHom.ker g₀) → ∀ (X X₀ X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) (f₀ : X₀ ⟶ Spec (CommRingCat.of A₀)) (f' : X' ⟶ Spec (CommRingCat.of A')) (j₀ : X₀ ⟶ X) (β : X' ⟶ X), Flat f → IsPullback j₀ f₀ f (Spec.map (CommRingCat.ofHom g₀)) → IsPullback β f' f (Spec.map (CommRingCat.ofHom g')) → ∀ (N : LB X) (N₀ : LB X₀) (w₀ : LB.Iso N₀ (N.pull j₀)), N.IsLB → N₀.IsLB → w₀.IsGen → ∀ σ : LB.Sec N, (∀ k, (β.app (N.U k)).hom (σ.f k) = 0) → ∃ τ₀ : LB.Sec N₀, ∀ τ : LB.Sec N, (∀ z (k : (N).ι) (k' : (N₀).ι), (j₀) z ∈ (N).U k → z ∈ (N₀).U k' → gs (j₀) z _ ((τ).f k) = (Geo.Tor.gw (w₀) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((τ₀).f k')) → ∀ k, σ.f k = cst f (N.U k) a * τ.f k := by
  intro A A₀ A' _ _ _ g₀ g' a hg hg' hn hk _ ha X Y X' f f₀ f' j β _ P P' N N₀ w hN hN₀ hw σ hσ
  let I := {q : Σ (_ : N.ι) (W : X.Opens), Γ(X, W) //
    ∃ h : q.2.1 ≤ N.U q.1, rs X h (σ.f q.1) = cst f q.2.1 a * q.2.2}
  let V : I → X.Opens := fun q => q.1.2.1
  let c : I → N.ι := fun q => q.1.1
  let u : ∀ q, Γ(X, V q) := fun q => q.1.2.2
  have hc : ∀ q, V q ≤ N.U (c q) := fun q => q.2.1
  have hu : ∀ q, rs X (hc q) (σ.f (c q)) = cst f (V q) a * u q := fun q => q.2.2
  have loc : ∀ k x, x ∈ N.U k → ∃ q, c q = k ∧ x ∈ V q := by
    intro k x hx
    obtain ⟨W, hW, hxW, hle⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hx
    have h := SmallExtLift.mem_of_app_eq_zero hg' P' hW (rs X hle (σ.f k))
      (by rw [app_rs, hσ, map_zero])
    rw [hk, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at h
    obtain ⟨b, hb⟩ := h
    exact ⟨⟨⟨k, W, b⟩, hle, hb⟩, rfl, hxW⟩
  obtain ⟨τ₀, hτ₀⟩ := exists_sec_of_local w hN₀ hw V c hc (fun z => by
      obtain ⟨k, hk⟩ := exists_chart hN (j z)
      obtain ⟨q, -, hq⟩ := loc k _ hk
      exact ⟨q, hq⟩) u (fun q q' z h h' => by
      have hm : j z ∈ V q ⊓ V q' := ⟨h, h'⟩
      have e := (gs_mul_eq_zero_iff hg ha P z hm (rs X inf_le_left (u q) -
        rs X (inf_le_inf (hc q) (hc q')) (N.g (c q) (c q')).val * rs X inf_le_right (u q'))).1 (by
          refine gs_of_app_eq_zero (𝟙 X) (j z) _ hm _ ?_
          change (_ : Γ(X, V q ⊓ V q')) = 0
          have e₁ := congrArg (rs X (inf_le_left : V q ⊓ V q' ≤ _)) (hu q)
          have e₂ := congrArg (rs X (inf_le_right : V q ⊓ V q' ≤ _)) (hu q')
          have e₃ := congrArg (rs X (inf_le_inf (hc q) (hc q'))) (σ.compat (c q) (c q'))
          simp only [map_mul, rs_rs, rs_cst] at e₁ e₂ e₃
          change cst f (V q ⊓ V q') a * (_ - _ * _) = 0
          linear_combination e₃ - e₁ + rs X (inf_le_inf (hc q) (hc q')) (N.g (c q) (c q')).val * e₂)
      rw [gs_sub _ _ _ hm, gs_mul _ _ _ hm, gs_res _ _ _ hm, gs_res _ _ _ hm, gs_res _ _ _ hm,
        gs_unit j z (N.U (c q) ⊓ N.U (c q')) ⟨hc q h, hc q' h'⟩, sub_eq_zero] at e
      exact e)
  refine ⟨τ₀, fun τ hτ k => fn_ext fun x hx => ?_⟩
  obtain ⟨z, rfl⟩ := surjective_of_isNilpotent hg hn P x
  obtain ⟨q, rfl, hq⟩ := loc k _ hx
  obtain ⟨k', hk'⟩ := exists_chart hN₀ z
  have e := (gs_mul_eq_zero_iff hg ha P z hq (u q - rs X (hc q) (τ.f (c q)))).2 (by
    rw [gs_sub _ _ _ hq, gs_res _ _ _ hq, hτ z (c q) k' hx hk', hτ₀ q k' z hq hk', sub_self])
  rw [mul_sub, ← hu, ← rs_cst f (hc q), ← map_mul, gs_sub (𝟙 X) (j z) _ hq, gs_res (𝟙 X) (j z) _ hq,
    gs_res (𝟙 X) (j z) _ hq, sub_eq_zero] at e
  exact e
end GlobalTheory.SectionKernel
