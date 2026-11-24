-- Prove2me | solution 1 for GlobalTheory.SmGL.IndCoinv.smInd_coinvariants
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:08:27.549331+00:00
-- url     : https://prove2.me/submissions/99a7f682-5d49-4025-8b1a-057d3423a354

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InductionContragredient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmIndCoinvariants
import Theorems.Thm_GlobalTheory_SmGL_IndCoinv_smIndMap_bump
import Theorems.Thm_GlobalTheory_SmGL_IndCoinv_mem_of_bump
import Theorems.Thm_GlobalTheory_SmGL_IndCoinv_mem_of_fixed
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_IwahoriOnto_exists_fixed_map_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.IndDual
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.IndCoinv
variable {G X U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module ℂ X]
  [AddCommGroup U] [Module ℂ U] {P : Subgroup G} {σ : Representation ℂ P X} {ρ : Representation ℂ P U}
namespace GlobalTheory.SmGL.IndCoinv
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (P K : Subgroup G), IsClosed (P : Set G) → IsCompact (K : Set G) → (∀ g : G, ∃ p ∈ P, ∃ x ∈ K, g = p * x) → (∀ U ∈ nhds (1 : G), ∃ J : Subgroup G, IsOpen (J : Set G) ∧ (J : Set G) ⊆ U ∧ J ≤ K ∧ ∀ x ∈ K, ∀ j ∈ J, x * j * x⁻¹ ∈ J) → ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (U : Type) [AddCommGroup U] [Module ℂ U] (σ : Representation ℂ P X) (ρ : Representation ℂ P U), IsSmooth σ → ∀ (α : σ.IntertwiningMap ρ) (Γ : Type) (T : Γ → σ.IntertwiningMap σ), Function.Surjective α → (∀ x, α x = 0 → x ∈ Submodule.span ℂ {y : X | ∃ γ z, y = T γ z - z}) → Function.Surjective (smIndMap α) ∧ ∀ f, smIndMap α f = 0 → f ∈ Submodule.span ℂ {y : smoothPart (ind P σ) | ∃ γ z, y = smIndMap (T γ) z - z} := by
  intro G _ _ _ _ P K hP hK hPK hb X _ _ U _ _ σ ρ hσ α Γ T hα hker
  have hc : ∀ J : Subgroup G, IsOpen (J : Set G) → J ≤ K → IsCompact (J.subgroupOf P : Set P) :=
    fun J hJ hle => hP.isClosedEmbedding_subtypeVal.isCompact_preimage
      (hK.of_isClosed_subset (J.isClosed_of_isOpen hJ) hle)
  constructor
  · intro f
    refine mem_of_bump hK hPK hb (LinearMap.range (smIndMap α).toLinearMap) ?_ ?_ f
    · rintro g _ ⟨φ, rfl⟩
      exact ⟨smInd P σ g φ, rfl⟩
    · intro J hJ hle w
      obtain ⟨x, hx⟩ := hα w
      obtain ⟨v, hv, e⟩ := IwahoriOnto.exists_fixed_map_eq hσ (hc J hJ hle) α.toLinearMap x fun h hh => by
        show α _ = α _
        rw [α.isIntertwining, hx, mem_fixed_iff.1 w.2 h hh]
      exact ⟨bump σ hJ ⟨v, hv⟩, smIndMap_bump α hJ _ _ (e.trans hx)⟩
  · intro f hf
    set Z := Submodule.span ℂ {y : smoothPart (ind P σ) | ∃ γ z, y = smIndMap (T γ) z - z} with hZ
    let N : Submodule ℂ X := LinearMap.ker α.toLinearMap
    have hN : ∀ g, ∀ v ∈ N, σ g v ∈ N := fun g v hv => by
      have hv' : α v = 0 := hv
      show α _ = 0
      rw [α.isIntertwining, hv', map_zero]
    let τ := sub σ N hN
    let j : τ.IntertwiningMap σ := { toLinearMap := N.subtype, isIntertwining' := fun _ => rfl }
    let f' : smoothPart (ind P τ) :=
      ⟨⟨fun g => ⟨f.1.1 g, congrArg (fun φ : smoothPart (ind P ρ) => φ.1.1 g) hf⟩, fun h g => Subtype.ext (f.1.2 h g)⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset (IsOpen.mem_nhds f.2 (by simp)) fun g hg => by
          have hg' : ind P σ g f.1 = f.1 := hg
          exact Subtype.ext (funext fun x => Subtype.ext (congrFun (congrArg Subtype.val hg') x)))⟩
    have hst : ∀ g, Z ≤ Z.comap (smInd P σ g) := fun g => Submodule.span_le.2 (by
      rintro _ ⟨γ, z, rfl⟩
      exact Submodule.subset_span ⟨γ, smInd P σ g z, rfl⟩)
    refine mem_of_bump hK hPK hb (Z.comap (smIndMap j).toLinearMap) (fun g φ hφ => hst g hφ) ?_ f'
    intro J hJ hle w
    have hw := map_mem_fixed j w.2
    show smIndMap j _ ∈ Z
    rw [smIndMap_bump j hJ w ⟨_, hw⟩ rfl]
    refine mem_of_fixed hσ (hc J hJ hle) T (Z.comap (bump σ hJ)) (fun γ z => ?_) _ (hker _ w.1.2)
    rw [Submodule.mem_comap, map_sub, ← smIndMap_bump (T γ) hJ z _ rfl]
    exact Submodule.subset_span ⟨γ, _, rfl⟩
end GlobalTheory.SmGL.IndCoinv
