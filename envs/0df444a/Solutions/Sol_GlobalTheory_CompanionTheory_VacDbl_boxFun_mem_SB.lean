-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.VacDbl.boxFun_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:35:33.116645+00:00
-- url     : https://prove2.me/submissions/7afc5c83-6896-4ac9-a43a-930c9ce79976

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BoxFunMemSB
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Implements_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.VacDbl
namespace GlobalTheory.CompanionTheory.VacDbl
theorem _root_.solution {R : Type} [TopologicalSpace R] [T2Space R] {κ κ' : Type} {φ₁ : (κ → R) → ℂ}
    {φ₂ : (κ' → R) → ℂ} (h₁ : φ₁ ∈ SB (κ → R)) (h₂ : φ₂ ∈ SB (κ' → R)) : boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → R) := by
  refine ⟨(h₁.1.comp_continuous (f := fun x : κ ⊕ κ' → R => x ∘ Sum.inl) (by fun_prop)).mul
    (h₂.1.comp_continuous (f := fun x : κ ⊕ κ' → R => x ∘ Sum.inr) (by fun_prop)), ?_⟩
  have hK : IsCompact ((fun p : (κ → R) × (κ' → R) => Sum.elim p.1 p.2) '' (tsupport φ₁ ×ˢ tsupport φ₂)) := by
    refine (IsCompact.prod h₁.2 h₂.2).image (continuous_pi ?_)
    rintro (i | i)
    · exact (continuous_apply i).comp continuous_fst
    · exact (continuous_apply i).comp continuous_snd
  refine HasCompactSupport.intro hK fun x hx => ?_
  by_contra hne
  obtain ⟨e₁, e₂⟩ := mul_ne_zero_iff.1 hne
  refine hx ⟨(x ∘ Sum.inl, x ∘ Sum.inr), ⟨subset_tsupport _ e₁, subset_tsupport _ e₂⟩, ?_⟩
  funext i
  rcases i with i | i <;> rfl
end GlobalTheory.CompanionTheory.VacDbl
