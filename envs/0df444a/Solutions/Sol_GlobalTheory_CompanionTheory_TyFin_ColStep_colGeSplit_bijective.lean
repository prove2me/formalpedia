-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.ColStep.colGeSplit_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:50:27.760799+00:00
-- url     : https://prove2.me/submissions/3e75968a-db9a-42c1-be7d-37abfefe6608

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternSetCardColumnStep

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.ColStep
namespace GlobalTheory.CompanionTheory.TyFin.ColStep
theorem _root_.solution (d j : ℕ) (hj : j < d) : Function.Bijective (colGeSplit d j hj) := by
  constructor
  · rintro (a | a) (b | b) h
    · have h1 := congrArg (fun x => (x.1.1 : Fin d).1) h
      simp only [colGeSplit] at h1
      exact congrArg Sum.inl (Fin.ext h1)
    · have h1 := congrArg (fun x => (x.1.2 : Fin d).1) h
      simp only [colGeSplit] at h1
      have := b.2.2
      omega
    · have h1 := congrArg (fun x => (x.1.2 : Fin d).1) h
      simp only [colGeSplit] at h1
      have := a.2.2
      omega
    · have h1 := congrArg (fun x => x.1) h
      simp only [colGeSplit] at h1
      exact congrArg Sum.inr (Subtype.ext h1)
  · rintro ⟨⟨i, l⟩, hil, hjl⟩
    by_cases e : (l : ℕ) = j
    · have hi : (i : ℕ) < j := by
        have : (i : ℕ) < l := hil
        omega
      refine ⟨Sum.inl ⟨i, hi⟩, ?_⟩
      apply Subtype.ext
      simp only [colGeSplit]
      exact Prod.ext rfl (Fin.ext e.symm)
    · have hl : j + 1 ≤ (l : ℕ) := by
        have : j ≤ (l : ℕ) := hjl
        omega
      exact ⟨Sum.inr ⟨(i, l), hil, hl⟩, rfl⟩
end GlobalTheory.CompanionTheory.TyFin.ColStep
