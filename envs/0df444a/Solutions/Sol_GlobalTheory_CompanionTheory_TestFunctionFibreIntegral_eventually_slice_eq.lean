-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TestFunctionFibreIntegral.eventually_slice_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:41:29.103859+00:00
-- url     : https://prove2.me/submissions/e95fac6b-e5b3-4e25-9768-30102cffa7fa

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PartialIntegralMemSchwartzBruhat
import Theorems.Thm_PositivityTheory_PfBern_Frob_mem_SB_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TestFunctionFibreIntegral
namespace GlobalTheory.CompanionTheory.TestFunctionFibreIntegral
theorem _root_.solution {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (F : SB (A × B)) (a₀ : A) :
    ∀ᶠ a in nhds a₀, ∀ b, (F : A × B → ℂ) (a, b) = (F : A × B → ℂ) (a₀, b) := by
  obtain ⟨hF, hc⟩ := mem_SB_iff.1 F.2
  have hK : IsCompact (Prod.snd '' tsupport (F : A × B → ℂ)) := hc.isCompact.image continuous_snd
  have hopen : IsOpen {p : A × B | (F : A × B → ℂ) p = (F : A × B → ℂ) (a₀, p.2)} := by
    have h2 : IsLocallyConstant
        (fun p : A × B => (F : A × B → ℂ) p - (F : A × B → ℂ) (a₀, p.2)) :=
      hF.sub (hF.comp_continuous (by fun_prop))
    have h3 := h2.isOpen_fiber 0
    simpa [Set.preimage, sub_eq_zero] using h3
  obtain ⟨U, V, hU, -, haU, hKV, hUV⟩ := generalized_tube_lemma (isCompact_singleton (x := a₀)) hK
    hopen (by
      rintro ⟨a, b⟩ ⟨ha, -⟩
      have ha' : a = a₀ := ha
      subst ha'
      rfl)
  filter_upwards [hU.mem_nhds (haU rfl)] with a ha b
  by_cases hb : b ∈ Prod.snd '' tsupport (F : A × B → ℂ)
  · exact hUV (Set.mk_mem_prod ha (hKV hb))
  · have h1 : (a, b) ∉ tsupport (F : A × B → ℂ) := fun h => hb ⟨_, h, rfl⟩
    have h2 : (a₀, b) ∉ tsupport (F : A × B → ℂ) := fun h => hb ⟨_, h, rfl⟩
    rw [image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2]
end GlobalTheory.CompanionTheory.TestFunctionFibreIntegral
