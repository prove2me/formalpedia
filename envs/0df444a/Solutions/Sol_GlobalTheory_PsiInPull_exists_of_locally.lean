-- Prove2me | solution 1 for GlobalTheory.PsiInPull.exists_of_locally
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:49:59.202481+00:00
-- url     : https://prove2.me/submissions/79603fc2-52a0-422a-8e48-9aabc02606ea

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PsiInOfIsPullDeg
import Theorems.Thm_GlobalTheory_PsiInPull_jK_mem
import Theorems.Thm_GlobalTheory_PsiInPull_res_toOpen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.PsiInPull
namespace GlobalTheory.PsiInPull
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] (J : Ideal R)
    (z : Spec (CommRingCat.of (FractionRing R))) (t : (Spec (CommRingCat.of (FractionRing R))).presheaf.stalk z)
    (V : (Spec (CommRingCat.of R)).Opens) (hV : IsAffineOpen V) (hz : jK R z ∈ V)
    (H : ∀ v ∈ V, ∃ U : (Spec (CommRingCat.of R)).Opens, U ≤ V ∧ v ∈ U ∧
      ∃ s ∈ J.map (DegPre.toOpen U), gs (jK R) z U s = t) :
    ∃ r ∈ J.map (DegPre.toOpen V), gs (jK R) z V r = t := by
  let θ : Γ(Spec (CommRingCat.of R), V) →+* (Spec (CommRingCat.of (FractionRing R))).presheaf.stalk z :=
    ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ (jK R ⁻¹ᵁ V) z hz).hom.comp ((jK R).app V).hom
  have hθ : ∀ a, gs (jK R) z V a = θ a := fun a => gs_eq _ _ _ hz a
  let Q : Ideal Γ(Spec (CommRingCat.of R), V) :=
    { carrier := {a | ∃ b ∈ J.map (DegPre.toOpen V), θ b = θ a * t}
      zero_mem' := ⟨0, Ideal.zero_mem _, by simp⟩
      add_mem' := by
        rintro a a' ⟨b, hb, e⟩ ⟨b', hb', e'⟩
        exact ⟨b + b', Ideal.add_mem _ hb hb', by rw [map_add, map_add, e, e', add_mul]⟩
      smul_mem' := by
        rintro c a ⟨b, hb, e⟩
        exact ⟨c * b, Ideal.mul_mem_left _ _ hb, by rw [smul_eq_mul, map_mul, map_mul, e, _root_.mul_assoc]⟩ }
  have key : ∀ v ∈ V, ∃ f ∈ Q, v ∈ (Spec (CommRingCat.of R)).basicOpen f := by
    intro v hv
    obtain ⟨U, hUV, hvU, s, hs, e⟩ := H v hv
    obtain ⟨f, hfU, hvf⟩ := hV.exists_basicOpen_le (V := U) ⟨v, hvU⟩ hv
    have hzf : jK R z ∈ (Spec (CommRingCat.of R)).basicOpen f :=
      jK_mem z _ (fun h0 => by rw [h0] at hvf; exact hvf)
    have := hV.isLocalization_basicOpen f
    have hs' : ((Spec (CommRingCat.of R)).presheaf.map (homOfLE hfU).op).hom s ∈
        (J.map (DegPre.toOpen V)).map
          (algebraMap Γ(Spec (CommRingCat.of R), V) Γ(Spec (CommRingCat.of R), (Spec (CommRingCat.of R)).basicOpen f)) := by
      have h1 := Ideal.mem_map_of_mem ((Spec (CommRingCat.of R)).presheaf.map (homOfLE hfU).op).hom hs
      rw [Ideal.map_map] at h1 ⊢
      convert h1 using 2
      ext a
      exact (res_toOpen ((Spec (CommRingCat.of R)).basicOpen_le f) a).trans (res_toOpen hfU a).symm
    obtain ⟨⟨⟨b, hb⟩, ⟨_, n, rfl⟩⟩, e2⟩ := (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers f) _).1 hs'
    have e3 := congrArg (gs (jK R) z ((Spec (CommRingCat.of R)).basicOpen f)) e2
    rw [gs_mul _ _ _ hzf, gs_res _ _ hfU hzf, e] at e3
    have e4 : ∀ a, gs (jK R) z ((Spec (CommRingCat.of R)).basicOpen f)
        (algebraMap Γ(Spec (CommRingCat.of R), V) _ a) = θ a := fun a =>
      (gs_res _ _ ((Spec (CommRingCat.of R)).basicOpen_le f) hzf a).trans (hθ a)
    rw [e4, e4] at e3
    refine ⟨f ^ n * f, Ideal.mul_mem_right _ _ ⟨b, hb, e3.symm.trans (_root_.mul_comm _ _)⟩, ?_⟩
    rw [← pow_succ, Scheme.basicOpen_pow _ _ (Nat.succ_pos n)]
    exact hvf
  have hQ : Ideal.span (Q : Set Γ(Spec (CommRingCat.of R), V)) = ⊤ := by
    refine (hV.self_le_iSup_basicOpen_iff).1 fun v hv => ?_
    obtain ⟨f, hf, hvf⟩ := key v hv
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hf⟩, hvf⟩
  rw [Ideal.span_eq] at hQ
  obtain ⟨b, hb, e⟩ : (1 : Γ(Spec (CommRingCat.of R), V)) ∈ Q := hQ ▸ Submodule.mem_top
  exact ⟨b, hb, by rw [hθ, e, map_one, _root_.one_mul]⟩
end GlobalTheory.PsiInPull
