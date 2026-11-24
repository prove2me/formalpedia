-- Prove2me | solution 1 for GlobalTheory.OpenIdeleCongr.finiteSingle_mem_of_nhds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:45:03.757581+00:00
-- url     : https://prove2.me/submissions/c079270c-8b60-4d0b-93ff-9bfcb59bcc67

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsOpenIdeleSubgroupContainsCongruenceUnits
import Theorems.Thm_GlobalTheory_OpenIdeleCongr_exists_exp_of_nhds
import Theorems.Thm_GlobalTheory_OpenIdeleCongr_isOpen_adicIntegers

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
theorem _root_.solution (Vf : Set (FiniteAdeleRing (𝓞 F) F)) (hV : Vf ∈ nhds (1 : FiniteAdeleRing (𝓞 F) F)) :
    ∃ (S : Set (HeightOneSpectrum (𝓞 F))) (M : ℕ), S.Finite ∧ ∀ v (y : v.adicCompletion F),
      y ∈ v.adicCompletionIntegers F → (v ∈ S → Valued.v (y - 1) ≤ WithZero.exp (-(M : ℤ))) →
      finiteSingle F v y ∈ Vf := by
  classical
  have hσ := RestrictedProduct.isOpenEmbedding_structureMap (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) isOpen_adicIntegers
  have h1 : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite 1 = 1 :=
    RestrictedProduct.ext _ _ fun i => rfl
  have h2 : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite ⁻¹' Vf ∈ nhds 1 := by
    apply hσ.continuous.continuousAt.preimage_mem_nhds
    rw [h1]
    exact hV
  rw [nhds_pi, Filter.mem_pi] at h2
  obtain ⟨I, hI, t, ht, hsub⟩ := h2
  have hM : ∀ i : HeightOneSpectrum (𝓞 F), ∃ M : ℕ, ∀ (y : i.adicCompletion F) (hy : y ∈ i.adicCompletionIntegers F),
      Valued.v (y - 1) ≤ WithZero.exp (-(M : ℤ)) → (⟨y, hy⟩ : ((i.adicCompletionIntegers F : Set (i.adicCompletion F)))) ∈ t i := by
    intro i
    obtain ⟨u, hu, hut⟩ := (mem_nhds_subtype _ _ _).mp (ht i)
    obtain ⟨M, hM⟩ := exists_exp_of_nhds i u hu
    exact ⟨M, fun y hy h => hut (hM y h)⟩
  choose M hMs using hM
  refine ⟨I, hI.toFinset.sup M, hI, fun v y hy hS => ?_⟩
  have hmem : (Pi.mulSingle v (⟨y, hy⟩ : ((v.adicCompletionIntegers F : Set (v.adicCompletion F)))) :
      (i : HeightOneSpectrum (𝓞 F)) → ((i.adicCompletionIntegers F : Set (i.adicCompletion F)))) ∈ I.pi t := by
    intro i hi
    by_cases hne : i = v
    · subst hne
      rw [Pi.mulSingle_eq_same]
      refine hMs i y hy ((hS hi).trans ?_)
      rw [WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le]
      exact Finset.le_sup (hI.mem_toFinset.2 hi)
    · rw [Pi.mulSingle_eq_of_ne hne]
      exact mem_of_mem_nhds (ht i)
  have hg := hsub hmem
  have e : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite (Pi.mulSingle v ⟨y, hy⟩) =
      finiteSingle F v y := by
    apply RestrictedProduct.ext
    intro i
    rw [RestrictedProduct.structureMap_apply]
    show _ = Pi.mulSingle v y i
    by_cases hi : i = v
    · subst hi
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hi, Pi.mulSingle_eq_of_ne hi]
      rfl
  rw [← e]
  exact hg
end GlobalTheory.OpenIdeleCongr
