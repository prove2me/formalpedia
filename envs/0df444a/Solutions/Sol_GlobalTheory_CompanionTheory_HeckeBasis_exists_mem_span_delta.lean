-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeBasis.exists_mem_span_delta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:28:04.774472+00:00
-- url     : https://prove2.me/submissions/c4ec80dc-c91f-4ca1-9d84-3c7391d57eda

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithful
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBasis_IsFixed_apply_of_mem_orbit
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBasis_heckeOp_delta
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open CompanionTheory.Rg.Fl
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeBasis
variable {G : Type} [Group G] (K : Subgroup G)
variable {K}
variable (K)
variable {K}
variable (K)
variable {K}
namespace GlobalTheory.CompanionTheory.HeckeBasis
theorem _root_.solution (hK : IsHeckePair K) (n : ℕ) :
    ∀ u : (G ⧸ K) →₀ ℂ, IsFixed K u → u.support.card ≤ n →
      ∃ t ∈ Submodule.span ℂ (Set.range (heckeOp hK)),
        (t : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) = u := by
  classical
  induction n with
  | zero =>
    intro u _ hc
    have : u = 0 := by simpa using hc
    exact ⟨0, Submodule.zero_mem _, by simp [this]⟩
  | succ n ih =>
    intro u hu hc
    by_cases h0 : u = 0
    · exact ⟨0, Submodule.zero_mem _, by simp [h0]⟩
    obtain ⟨y, hy⟩ := Finsupp.support_nonempty_iff.2 h0
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    set c := u (g : G ⧸ K) with hcdef
    have hc0 : c ≠ 0 := Finsupp.mem_support_iff.1 hy
    have hfix : IsFixed K (u - c • orbitVec hK g) := by
      intro k hk
      rw [map_sub, map_smul, hu k hk, orbitVec_fixed hK g k hk]
    have hsub : (u - c • orbitVec hK g).support ⊆ u.support.erase (g : G ⧸ K) := by
      intro z hz
      have hz' := Finsupp.mem_support_iff.1 hz
      simp only [Finsupp.coe_sub, Finsupp.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        orbitVec_apply] at hz'
      refine Finset.mem_erase.2 ⟨?_, ?_⟩
      · rintro rfl
        apply hz'
        simp [MulAction.mem_orbit_self, ← hcdef]
      · refine Finsupp.mem_support_iff.2 fun hzu => hz' ?_
        have hno : z ∉ MulAction.orbit K (g : G ⧸ K) := fun hm =>
          hc0 (by rw [hcdef, ← hu.apply_of_mem_orbit hm, hzu])
        simp [hzu, hno]
    have hcard : (u - c • orbitVec hK g).support.card ≤ n := by
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hy] at this
      omega
    obtain ⟨t, ht, hte⟩ := ih _ hfix hcard
    refine ⟨t + c • heckeOp hK g,
      Submodule.add_mem _ ht (Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)), ?_⟩
    have : ((t + c • heckeOp hK g : Hk K) : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) =
        (t : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) +
          c • (heckeOp hK g : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) := rfl
    rw [this, hte, heckeOp_delta]
    abel
end GlobalTheory.CompanionTheory.HeckeBasis
