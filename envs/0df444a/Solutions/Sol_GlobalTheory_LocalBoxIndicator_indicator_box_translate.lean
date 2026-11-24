-- Prove2me | solution 1 for GlobalTheory.LocalBoxIndicator.indicator_box_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:08:36.620094+00:00
-- url     : https://prove2.me/submissions/03a1c0cd-e999-4770-9c99-167250c01269

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_ReciprocityTheory_GeneralLinearIntegers_AlgebraMapIntMemOint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TranslateOpenSubgroupsFinite
import Theorems.Thm_GlobalTheory_LocalBoxIndicator_indicator_mem_SB
import Theorems.Thm_ReciprocityTheory_GeneralLinearIntegers_GeneralLinearIntegersOpenCompact_isCompact_integers


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open GlobalTheory GlobalTheory.LocalBoxIndicator
namespace GlobalTheory.LocalBoxIndicator
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (B : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F)),
    (∀ v, IsOpen (B v : Set (v.adicCompletion F))) →
    (∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F) →
    (∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) →
    ∀ r : κ → FiniteAdeleRing (𝓞 F) F,
      (∀ v, Set.indicator {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
        (1 : (κ → v.adicCompletion F) → ℂ) ∈ GlobalTheory.WeilM.SB (κ → v.adicCompletion F)) ∧
      ∀ᶠ v in Filter.cofinite, Set.indicator {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
        (1 : (κ → v.adicCompletion F) → ℂ) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  intro F _ _ κ _ B hBo hBO hBcof r
  refine ⟨fun v => ?_, ?_⟩
  · set c : κ → v.adicCompletion F := fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) with hc
    have hS : {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
        = (Homeomorph.subRight c) ⁻¹' (Set.univ.pi fun _ => (B v : Set (v.adicCompletion F))) := by
      ext x
      simp [Set.mem_pi, hc]
    have hBc : IsCompact (B v : Set (v.adicCompletion F)) :=
      (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v).of_isClosed_subset
        (AddSubgroup.isClosed_of_isOpen (B v) (hBo v)) (hBO v)
    have hT : IsClopen (Set.univ.pi fun _ : κ => (B v : Set (v.adicCompletion F))) :=
      ⟨isClosed_set_pi fun _ _ => AddSubgroup.isClosed_of_isOpen (B v) (hBo v),
        isOpen_set_pi Set.finite_univ fun _ _ => hBo v⟩
    rw [hS]
    exact indicator_mem_SB (hT.preimage (Homeomorph.subRight c).continuous)
      ((Homeomorph.subRight c).isCompact_preimage.2 (isCompact_univ_pi fun _ => hBc))
  · have hr : ∀ᶠ v in Filter.cofinite, ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ v.adicCompletionIntegers F :=
      Filter.eventually_all.2 fun i => (r i).2
    filter_upwards [hr, hBcof] with v hv hBv
    congr 1
    ext x
    simp only [Set.mem_setOf_eq]
    refine forall_congr' fun i => ?_
    rw [← SetLike.mem_coe, hBv, SetLike.mem_coe]
    constructor
    · intro h
      have := (v.adicCompletionIntegers F).add_mem _ _ h (hv i)
      simpa using this
    · intro h
      exact (v.adicCompletionIntegers F).sub_mem h (hv i)
end GlobalTheory.LocalBoxIndicator
