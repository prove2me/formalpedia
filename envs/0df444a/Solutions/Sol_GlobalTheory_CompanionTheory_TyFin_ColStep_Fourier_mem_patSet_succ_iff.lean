-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier.mem_patSet_succ_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:50:25.044838+00:00
-- url     : https://prove2.me/submissions/bef36cdc-c2b4-4bd7-8d60-4e48487f815f

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WhittakerColumnRecursion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.ColStep GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
namespace GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier
theorem _root_.solution {d j : ℕ} (hj : j < d) (u : GL (Fin d) K) :
    u ∈ patSet K (colGe d (j + 1)) ↔ u ∈ patSet K (colGe d j) ∧ colEntries hj u = 0 := by
  simp only [patSet, Set.mem_setOf_eq, colGe]
  constructor
  · intro h
    refine ⟨fun i l => ⟨(h i l).1, fun hne hn => (h i l).2 hne (fun hc => hn ⟨hc.1, by
      have h2 := hc.2; omega⟩)⟩, ?_⟩
    funext i
    have hi2 := i.2
    have hi : (⟨i, i.2.trans hj⟩ : Fin d) ≠ ⟨j, hj⟩ := by
      intro h'
      have h3 := congrArg Fin.val h'
      simp only [Fin.val_mk] at h3
      omega
    exact (h _ _).2 hi (fun hc => by
      have h2 := hc.2
      simp only [Fin.val_mk] at h2
      omega)
  · rintro ⟨h, hc⟩ i l
    refine ⟨(h i l).1, fun hne hn => ?_⟩
    by_cases hlj : (l : ℕ) = j ∧ i < l
    · have h3 : (i : ℕ) < l := hlj.2
      have hij : (i : ℕ) < j := by omega
      have h4 := congrFun hc ⟨i, hij⟩
      have hl : l = ⟨j, hj⟩ := Fin.ext hlj.1
      subst hl
      exact h4
    · apply (h i l).2 hne
      rintro ⟨h1, h2⟩
      apply hn
      refine ⟨h1, ?_⟩
      have h5 : (l : ℕ) ≠ j := fun h3 => hlj ⟨h3, h1⟩
      omega
end GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier
