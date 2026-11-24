-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FrobProd.span_of_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:49:38.706461+00:00
-- url     : https://prove2.me/submissions/6bd0263b-a230-4a4a-8766-b5ceca6d92b3

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SchwartzBruhatProdSpanTensors
import Theorems.Thm_GlobalTheory_CompanionTheory_FrobProd_fiber_ind_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FrobProd
open Classical
namespace GlobalTheory.CompanionTheory.FrobProd
theorem _root_.solution {A B S T : Type} [TopologicalSpace A] [T2Space A] [TopologicalSpace B]
    [T2Space B] [Fintype S] [Fintype T] {ξ : A → S} {η : B → T}
    (hξ : IsLocallyConstant ξ) (hη : IsLocallyConstant η) (s0 : S) (t0 : T)
    (hcs : ∀ s, s ≠ s0 → IsCompact (ξ ⁻¹' {s})) (hct : ∀ t, t ≠ t0 → IsCompact (η ⁻¹' {t}))
    (f : SB (A × B))
    (hΦ : ∀ q q' : A × B, ξ q.1 = ξ q'.1 → η q.2 = η q'.2 →
      (f : A × B → ℂ) q = (f : A × B → ℂ) q')
    (h0 : ∀ q : A × B, ξ q.1 = s0 → (f : A × B → ℂ) q = 0)
    (h0' : ∀ q : A × B, η q.2 = t0 → (f : A × B → ℂ) q = 0) :
    (f : A × B → ℂ) ∈ Submodule.span ℂ {F : A × B → ℂ | ∃ a : SB A, ∃ b : SB B,
      (∀ q : A × B, (a : A → ℂ) q.1 ≠ 0 → (b : B → ℂ) q.2 ≠ 0 → (f : A × B → ℂ) q ≠ 0) ∧
        F = fun q => (a : A → ℂ) q.1 * (b : B → ℂ) q.2} := by
  have hsum : (f : A × B → ℂ) =
      ∑ p : S × T, fun q : A × B => if ξ q.1 = p.1 ∧ η q.2 = p.2 then (f : A × B → ℂ) q else 0 := by
    funext q
    rw [Finset.sum_apply, Finset.sum_eq_single (ξ q.1, η q.2)]
    · simp
    · intro p _ hp
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hp (Prod.ext h1.symm h2.symm)
    · intro h
      exact absurd (Finset.mem_univ _) h
  refine Eq.mpr (congrArg (· ∈ _) hsum) (Submodule.sum_mem _ fun p _ => ?_)
  by_cases hex : ∃ q0 : A × B, ξ q0.1 = p.1 ∧ η q0.2 = p.2 ∧ (f : A × B → ℂ) q0 ≠ 0
  · obtain ⟨q0, h1, h2, h3⟩ := hex
    have hs : p.1 ≠ s0 := fun h => h3 (h0 q0 (h1.trans h))
    have ht : p.2 ≠ t0 := fun h => h3 (h0' q0 (h2.trans h))
    let ia : SB A := ⟨_, fiber_ind_mem hξ p.1 (hcs _ hs)⟩
    let ib : SB B := ⟨_, fiber_ind_mem hη p.2 (hct _ ht)⟩
    have hia : ∀ x, (ia : A → ℂ) x = if ξ x = p.1 then 1 else 0 := fun _ => rfl
    have hib : ∀ x, (ib : B → ℂ) x = if η x = p.2 then 1 else 0 := fun _ => rfl
    refine Submodule.subset_span ⟨(f : A × B → ℂ) q0 • ia, ib, ?_, ?_⟩
    · intro q ha hb
      have e1 : ξ q.1 = p.1 := by
        by_contra h
        apply ha
        simp [hia, h]
      have e2 : η q.2 = p.2 := by
        by_contra h
        apply hb
        simp [hib, h]
      rw [hΦ q q0 (e1.trans h1.symm) (e2.trans h2.symm)]
      exact h3
    · funext q
      by_cases e1 : ξ q.1 = p.1
      · by_cases e2 : η q.2 = p.2
        · simp [hia, hib, e1, e2, hΦ q q0 (e1.trans h1.symm) (e2.trans h2.symm)]
        · simp [hia, hib, e2]
      · simp [hia, e1]
  · have hz : (fun q : A × B => if ξ q.1 = p.1 ∧ η q.2 = p.2 then (f : A × B → ℂ) q else 0) = 0 := by
      funext q
      by_cases e : ξ q.1 = p.1 ∧ η q.2 = p.2
      · rw [if_pos e]
        by_contra h
        exact hex ⟨q, e.1, e.2, h⟩
      · rw [if_neg e]
        rfl
    rw [hz]
    exact Submodule.zero_mem _
end GlobalTheory.CompanionTheory.FrobProd
