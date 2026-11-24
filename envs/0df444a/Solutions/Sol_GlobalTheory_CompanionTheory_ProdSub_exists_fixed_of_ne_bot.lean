-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ProdSub.exists_fixed_of_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:10:52.942851+00:00
-- url     : https://prove2.me/submissions/b7d9a06a-211f-4a37-8750-b45e231b070b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsIrreducibleOfFixed
import Theorems.Thm_GlobalTheory_CompanionTheory_ProdSub_mem_fixed_iff_forall
import Theorems.Thm_GlobalTheory_CompanionTheory_ProdSub_fixed_sup_eq_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_ProdSub_inl_inr_comm
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ProdSub
variable {G H V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.ProdSub
theorem _root_.solution (ρ : Representation ℂ (G × H) V) (hi : ρ.IsIrreducible)
    (hs : IsSmooth (ρ.comp (MonoidHom.inl G H))) {K : Subgroup G} (hK : IsCompact (K : Set G))
    {v : V} (hv : v ≠ 0) (hvK : v ∈ fixed (ρ.comp (MonoidHom.inl G H)) K)
    (A : Submodule ℂ V) (hA : ∀ g, ∀ ⦃x⦄, x ∈ A → (ρ.comp (MonoidHom.inl G H)) g x ∈ A) (hA0 : A ≠ ⊥) :
    ∃ x ∈ A, x ∈ fixed (ρ.comp (MonoidHom.inl G H)) K ∧ x ≠ 0 := by
  classical
  by_contra hcon
  have hno : ∀ x ∈ A, x ∈ fixed (ρ.comp (MonoidHom.inl G H)) K → x = 0 := by
    intro x hxA hxK
    by_contra hx0
    exact hcon ⟨x, hxA, hxK, hx0⟩
  have hinl : ∀ (g : G) (x : V), (ρ.comp (MonoidHom.inl G H)) g x = ρ (g, 1) x := fun g x => rfl
  have hinv1 : ∀ (h : H) (y : V), ρ (1, h⁻¹) (ρ (1, h) y) = y := by
    intro h y
    rw [← Module.End.mul_apply, ← map_mul]
    have e : ((1, h⁻¹) * (1, h) : G × H) = 1 := Prod.ext (by simp) (by simp)
    rw [e, map_one, Module.End.one_apply]
  let T : H → Submodule ℂ V := fun h => A.map (ρ (1, h))
  have hTinv : ∀ h, ∀ g, ∀ ⦃x⦄, x ∈ T h → (ρ.comp (MonoidHom.inl G H)) g x ∈ T h := by
    rintro h g _ ⟨a, ha, rfl⟩
    rw [hinl, inl_inr_comm]
    exact ⟨ρ (g, 1) a, hA g ha, rfl⟩
  have hT0 : ∀ h, ∀ x ∈ T h, x ∈ fixed (ρ.comp (MonoidHom.inl G H)) K → x = 0 := by
    rintro h _ ⟨a, ha, rfl⟩ hxK
    have haK : a ∈ fixed (ρ.comp (MonoidHom.inl G H)) K := by
      rw [mem_fixed_iff_forall] at hxK ⊢
      intro k hk
      have e := hxK k hk
      rw [hinl, inl_inr_comm] at e
      have e2 := congrArg (ρ (1, h⁻¹)) e
      rwa [hinv1, hinv1] at e2
    show ρ (1, h) a = 0
    rw [hno a ha haK, map_zero]
  have hP : ∀ s : Finset H,
      (∀ g, ∀ ⦃x⦄, x ∈ ⨆ h ∈ s, T h → (ρ.comp (MonoidHom.inl G H)) g x ∈ ⨆ h ∈ s, T h) ∧
      (∀ x ∈ ⨆ h ∈ s, T h, x ∈ fixed (ρ.comp (MonoidHom.inl G H)) K → x = 0) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · have e : (⨆ h ∈ (∅ : Finset H), T h) = ⊥ := by simp
      rw [e]
      refine ⟨fun g x hx => ?_, fun x hx _ => (Submodule.mem_bot ℂ).mp hx⟩
      rw [(Submodule.mem_bot ℂ).mp hx, map_zero]
      exact Submodule.zero_mem _
    · intro a s _ ih
      rw [Finset.iSup_insert]
      refine ⟨?_, ?_⟩
      · intro g x hx
        obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
        rw [map_add]
        exact Submodule.add_mem_sup (hTinv a g hy) (ih.1 g hz)
      · intro x hx hxK
        exact fixed_sup_eq_zero hs hK (hTinv a) ih.1 (hT0 a) ih.2 hx hxK
  let B : Submodule ℂ V := ⨆ h, T h
  have hBinv : ∀ (gh : G × H) ⦃x : V⦄, x ∈ B → ρ gh x ∈ B := by
    intro gh x hx
    have hle : B ≤ B.comap (ρ gh) := by
      refine iSup_le fun h => ?_
      rintro _ ⟨a, ha, rfl⟩
      show ρ gh (ρ (1, h) a) ∈ B
      have e : gh * (1, h) = (1, gh.2 * h) * (gh.1, 1) := Prod.ext (by simp) (by simp)
      rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply]
      exact (le_iSup T (gh.2 * h)) ⟨ρ (gh.1, 1) a, hA gh.1 ha, rfl⟩
    exact hle hx
  have hAB : A ≤ B := by
    intro a ha
    refine (le_iSup T 1) ⟨a, ha, ?_⟩
    show ρ (1, 1) a = a
    rw [Prod.mk_one_one, map_one, Module.End.one_apply]
  haveI : IsSimpleOrder (Subrepresentation ρ) := hi
  let SB : Subrepresentation ρ := ⟨B, hBinv⟩
  have hSB : SB = ⊤ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top SB with h | h
    · exfalso
      apply hA0
      have hB : B = ⊥ := congrArg Subrepresentation.toSubmodule h
      rw [hB] at hAB
      exact le_bot_iff.mp hAB
    · exact h
  have hvB : v ∈ B := by
    have hB : B = ⊤ := congrArg Subrepresentation.toSubmodule hSB
    rw [hB]
    exact Submodule.mem_top
  obtain ⟨s, hs'⟩ := (Submodule.mem_iSup_iff_exists_finset).mp hvB
  exact hv ((hP s).2 v hs' hvK)
end GlobalTheory.CompanionTheory.ProdSub
