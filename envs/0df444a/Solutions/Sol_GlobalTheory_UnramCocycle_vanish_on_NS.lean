-- Prove2me | solution 1 for GlobalTheory.UnramCocycle.vanish_on_NS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:00:48.02381+00:00
-- url     : https://prove2.me/submissions/d6f35f7a-4b61-46b3-9cb9-bc3e516a0f86

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CocycleUnramifiedOutsideVanishOnKernel
import Theorems.Thm_GlobalTheory_UnramCocycle_conj_mem_ine_of_smul
import Theorems.Thm_GlobalTheory_UnramCocycle_kerSub_normal
import Theorems.Thm_GlobalTheory_UnramCocycle_kerSub_isClosed
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_ReciprocityTheory_Gal_Ine_le_Dec
import Theorems.Thm_ReciprocityTheory_Gal_exists_smul_eq_of_isPlaceOver
import Theorems.Thm_ReciprocityTheory_Gal_mem_Ine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply



set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open Pointwise
open GlobalTheory GlobalTheory.UnramCocycle
namespace GlobalTheory.UnramCocycle
theorem _root_.solution : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R (G F Ω) M), ContAction ρ → ∀ (A : Formalism.GaloisCohomology.Places F Ω) (S : Set (HeightOneSpectrum (𝓞 F))), (∀ v ∉ S, ∀ B : ValuationSubring Ω, IsPlaceOver B v → ∀ σ ∈ Ine (F := F) B, ∀ m, ρ σ m = m) → ∀ x : Z1 ρ, (∀ v ∉ S, resH1 ρ (Dec (F := F) (A.1 v)).subtype continuous_subtype_val (Submodule.Quotient.mk x) ∈ Formalism.GaloisCohomology.unrAt ρ (A.1 v)) → ∀ n ∈ NS Ω S, x.1 n = 0 ∧ ∀ m, ρ n m = m := by
  intro F Ω _ _ _ _ _ R M _ _ _ _ _ ρ hρ A S htriv x hx
  have := kerSub_normal ρ x

  have hle : NS Ω S ≤ kerSub ρ x := by
    unfold NS
    refine Subgroup.topologicalClosure_minimal _ ?_ (kerSub_isClosed ρ hρ x)
    refine Subgroup.normalClosure_le_normal ?_
    intro σ hσ
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_compl_iff, exists_prop] at hσ
    obtain ⟨v, hv, B, hB, hσB⟩ := hσ

    obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (A.2 v) hB
    have hσ' : σ ∈ Ine (F := F) (g • A.1 v) := by rw [hg, mem_Ine]; exact hσB
    have hc := conj_mem_ine_of_smul (A.1 v) g σ hσ'

    have hzero : x.1 (g⁻¹ * σ * g) = 0 := by
      have hu := hx v hv
      unfold Formalism.GaloisCohomology.unrAt H1ur at hu
      rw [LinearMap.mem_ker] at hu
      unfold resH1 at hu
      rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1] at hu
      obtain ⟨m, hm⟩ := hu
      have hmem : g⁻¹ * σ * g ∈ Dec (F := F) (A.1 v) := Ine_le_Dec _ hc
      have h := hm ⟨⟨g⁻¹ * σ * g, hmem⟩, (Subgroup.mem_subgroupOf).2 hc⟩

      have h' : x.1 (g⁻¹ * σ * g) = ρ (g⁻¹ * σ * g) m - m := h
      rw [htriv v hv (A.1 v) (A.2 v) _ hc, sub_self] at h'
      exact h'
    have hk : g⁻¹ * σ * g ∈ kerSub ρ x := ⟨hzero, htriv v hv (A.1 v) (A.2 v) _ hc⟩
    have h := (kerSub_normal ρ x).conj_mem _ hk g
    have e : g * (g⁻¹ * σ * g) * g⁻¹ = σ := by group
    rwa [e] at h
  exact fun n hn => hle hn
end GlobalTheory.UnramCocycle
