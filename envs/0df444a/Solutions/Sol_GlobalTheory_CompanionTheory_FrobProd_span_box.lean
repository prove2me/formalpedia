-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FrobProd.span_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:05:16.93233+00:00
-- url     : https://prove2.me/submissions/c1d65336-ddee-4e6b-97fb-afb03cc22f08

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SchwartzBruhatProdSpanTensors
import Theorems.Thm_GlobalTheory_CompanionTheory_FrobProd_exists_compact_clopen
import Theorems.Thm_GlobalTheory_CompanionTheory_FrobProd_isLocallyConstant_pattern
import Theorems.Thm_GlobalTheory_CompanionTheory_FrobProd_isCompact_pattern_fiber
import Theorems.Thm_GlobalTheory_CompanionTheory_FrobProd_span_of_factor
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FrobProd
open Classical
namespace GlobalTheory.CompanionTheory.FrobProd
theorem _root_.solution : ∀ (A B : Type) [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A] [TotallyDisconnectedSpace A] [TopologicalSpace B] [T2Space B] [LocallyCompactSpace B] [TotallyDisconnectedSpace B] (f : SB (A × B)), (f : A × B → ℂ) ∈ Submodule.span ℂ {F : A × B → ℂ | ∃ a : SB A, ∃ b : SB B, (∀ q : A × B, (a : A → ℂ) q.1 ≠ 0 → (b : B → ℂ) q.2 ≠ 0 → (f : A × B → ℂ) q ≠ 0) ∧ F = fun q => (a : A → ℂ) q.1 * (b : B → ℂ) q.2} := by
  intro A B _ _ _ _ _ _ _ _ f
  have hlc : IsLocallyConstant (f : A × B → ℂ) := (mem_SB_iff.1 f.2).1
  have hcs : HasCompactSupport (f : A × B → ℂ) := (mem_SB_iff.1 f.2).2
  have hbox : ∀ q : A × B, ∃ U : Set A, ∃ V : Set B, IsCompact U ∧ IsClopen U ∧ IsCompact V ∧
      IsClopen V ∧ q.1 ∈ U ∧ q.2 ∈ V ∧
      ∀ q' : A × B, q'.1 ∈ U → q'.2 ∈ V → (f : A × B → ℂ) q' = (f : A × B → ℂ) q := by
    intro q
    obtain ⟨u, v, hu, hv, hqu, hqv, huv⟩ := isOpen_prod_iff.1
      (hlc.isOpen_fiber ((f : A × B → ℂ) q)) q.1 q.2 rfl
    obtain ⟨U, hUc, hUo, hqU, hUu⟩ := exists_compact_clopen hu hqu
    obtain ⟨V, hVc, hVo, hqV, hVv⟩ := exists_compact_clopen hv hqv
    exact ⟨U, V, hUc, hUo, hVc, hVo, hqU, hqV, fun q' h1 h2 => huv ⟨hUu h1, hVv h2⟩⟩
  choose U V hUc hUo hVc hVo hqU hqV hUV using hbox
  obtain ⟨t, -, ht⟩ := hcs.isCompact.elim_nhds_subcover (fun q => U q ×ˢ V q)
    (fun q _ => ((hUo q).isOpen.prod (hVo q).isOpen).mem_nhds ⟨hqU q, hqV q⟩)
  have hcov : ∀ q : A × B, (f : A × B → ℂ) q ≠ 0 → ∃ i : t, q.1 ∈ U i ∧ q.2 ∈ V i := by
    intro q hq
    have := ht (subset_tsupport _ hq)
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, h⟩ := this
    exact ⟨⟨i, hi⟩, h.1, h.2⟩
  let ξ : A → Finset t := fun x => Finset.univ.filter (fun i : t => x ∈ U i)
  let η : B → Finset t := fun x => Finset.univ.filter (fun i : t => x ∈ V i)
  have hξm : ∀ x i, i ∈ ξ x ↔ x ∈ U i := fun x i => by simp [ξ]
  have hηm : ∀ x i, i ∈ η x ↔ x ∈ V i := fun x i => by simp [η]
  have hstep : ∀ q q' : A × B, ξ q.1 = ξ q'.1 → η q.2 = η q'.2 → (f : A × B → ℂ) q ≠ 0 →
      (f : A × B → ℂ) q = (f : A × B → ℂ) q' := by
    intro q q' e1 e2 hq
    obtain ⟨i, h1, h2⟩ := hcov q hq
    have h1' : q'.1 ∈ U i := (hξm _ _).1 (e1 ▸ (hξm _ _).2 h1)
    have h2' : q'.2 ∈ V i := (hηm _ _).1 (e2 ▸ (hηm _ _).2 h2)
    rw [hUV i q h1 h2, hUV i q' h1' h2']
  refine span_of_factor (ξ := ξ) (η := η)
    (isLocallyConstant_pattern (U := fun i : t => U i) fun i => hUo i)
    (isLocallyConstant_pattern (U := fun i : t => V i) fun i => hVo i) ∅ ∅
    (fun s hs => isCompact_pattern_fiber (U := fun i : t => U i) (fun i => hUo i) (fun i => hUc i) s hs)
    (fun s hs => isCompact_pattern_fiber (U := fun i : t => V i) (fun i => hVo i) (fun i => hVc i) s hs)
    f ?_ ?_ ?_
  · intro q q' e1 e2
    by_cases hq : (f : A × B → ℂ) q = 0
    · by_cases hq' : (f : A × B → ℂ) q' = 0
      · rw [hq, hq']
      · exact (hstep q' q e1.symm e2.symm hq').symm
    · exact hstep q q' e1 e2 hq
  · intro q hq
    by_contra h
    obtain ⟨i, h1, -⟩ := hcov q h
    have : i ∈ ξ q.1 := (hξm _ _).2 h1
    rw [hq] at this
    simp at this
  · intro q hq
    by_contra h
    obtain ⟨i, -, h2⟩ := hcov q h
    have : i ∈ η q.2 := (hηm _ _).2 h2
    rw [hq] at this
    simp at this
end GlobalTheory.CompanionTheory.FrobProd
