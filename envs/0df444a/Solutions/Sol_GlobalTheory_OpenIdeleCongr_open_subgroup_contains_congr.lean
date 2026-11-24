-- Prove2me | solution 1 for GlobalTheory.OpenIdeleCongr.open_subgroup_contains_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:17:53.088923+00:00
-- url     : https://prove2.me/submissions/8aea3ba0-270b-458c-8f41-5b73a0138fe1

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsOpenIdeleSubgroupContainsCongruenceUnits
import Theorems.Thm_GlobalTheory_OpenIdeleCongr_localIdele_mem_of_isOpen
import Theorems.Thm_GlobalTheory_NormCompat_locUnit_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
open GlobalTheory GlobalTheory.OpenIdeleCongr
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.OpenIdeleCongr
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (V : Subgroup (Ideles F)),
    IsOpen (V : Set (Ideles F)) → ∀ S₀ : Finset (HeightOneSpectrum (𝓞 F)),
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (M : ℕ), S₀ ⊆ S ∧
      (∀ v ∉ S, ∀ x, IsUnitAt v x → localIdele F v x ∈ V) ∧
      ∀ v ∈ S, ∀ a : Fˣ, v.valuation F ((a : F) - 1) ≤ WithZero.exp (-(M : ℤ)) → locUnit F v a ∈ V := by
  intro F _ _ V hV S₀
  classical
  obtain ⟨S₁, M₁, hS₁, key⟩ := localIdele_mem_of_isOpen V hV
  refine ⟨S₀ ∪ hS₁.toFinset, M₁ + 1, Finset.subset_union_left, fun v hv x hx => ?_, fun v _ a ha => ?_⟩
  · refine key v x hx fun hv' => absurd (Finset.mem_union_right _ (hS₁.mem_toFinset.2 hv')) hv
  · rw [locUnit_apply]
    set x := Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a with hxdef
    have hxv : (x : v.adicCompletion F) = ((a : F) : v.adicCompletion F) := rfl
    have hsub : Valued.v ((x : v.adicCompletion F) - 1) = v.valuation F ((a : F) - 1) := by
      have e : (x : v.adicCompletion F) - 1 = (((a : F) - 1 : F) : v.adicCompletion F) := by
        show algebraMap F (v.adicCompletion F) (a : F) - 1 = _
        rw [← map_one (algebraMap F (v.adicCompletion F)), ← map_sub]
        rfl
      rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have hle : Valued.v ((x : v.adicCompletion F) - 1) ≤ WithZero.exp (-(M₁ : ℤ)) := by
      rw [hsub]
      refine ha.trans ?_
      rw [WithZero.exp_le_exp]
      push_cast
      omega
    have hlt : Valued.v ((x : v.adicCompletion F) - 1) < 1 := by
      rw [hsub]
      refine lt_of_le_of_lt ha ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      push_cast
      omega
    have hunit : Valued.v (x : v.adicCompletion F) = 1 := by
      have := Valuation.map_one_add_of_lt _ hlt
      rwa [add_sub_cancel] at this
    exact key v x hunit fun _ => hle
end GlobalTheory.OpenIdeleCongr
