-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.IsGenericFlag.of_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:43:30.334718+00:00
-- url     : https://prove2.me/submissions/de2cecc2-de77-451f-aa73-a9ffaa8c1871

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Statements_MetricStatements_AgreementIffGuarded
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_GenericBlockMatrixIsBlockDiag
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_generic_block_matrix_map
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_exists_univ_decomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
open GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder
variable {R : Type} [CommRing R] {N : ℕ} {Ψ : Type}
variable {j : ℕ} {S : Type} [CommRing S]
namespace GlobalTheory.CompanionTheory.Ar.PB
namespace IsGenericFlag
theorem _root_.solution {Ω Φ : Type} [Field Ω] [Field Φ] [Algebra Ω Φ] {g : Ψ → Matrix (Fin N) (Fin N) Φ}
    (hg : ∀ τ, IsBlockDiag j (g τ))
    (h : AlgebraicIndependent Ω fun q : inertBlockIndex Ψ N j => g q.1.1 q.1.2.1 q.1.2.2) : IsGenericFlag Ω j g := by
  obtain ⟨T, _, _, i, ψ, B, -, he, hB⟩ := exists_univ_decomp Ω Ψ N j
  obtain ⟨e, he, hei⟩ := he Φ _ h
  have h1 : ∀ τ, g τ * (B τ).map e.toRingHom = ((genericBlockMatrix Ω N j τ).map i.toRingHom * B τ).map e.toRingHom := fun τ => by
    rw [Matrix.map_mul, ← generic_block_matrix_map (e.toRingHom.comp i.toRingHom) hg (fun q => (hei _).trans (aeval_X _ q)) τ]
    rfl
  refine ⟨fun τ => (B τ).map e.toRingHom, fun τ => ⟨(hB τ).1.map _, (hB τ).2.1.map _, ?_⟩, ?_⟩
  · rw [h1]; exact (hB τ).2.2.1.map _
  · simp only [h1]
    refine AlgebraicIndependent.map' (f := e)
      (x := fun q : LowIdx Ψ N j => ((genericBlockMatrix Ω N j q.1.1).map i.toRingHom * B q.1.1) q.1.2.1 q.1.2.2) ?_ he
    refine AlgebraicIndependent.of_comp ψ ?_
    convert MvPolynomial.algebraicIndependent_X (LowIdx Ψ N j) Ω using 1
    funext q
    exact (congrFun (congrFun (hB q.1.1).2.2.2 _) _).trans (genLow_apply q)
end IsGenericFlag
end GlobalTheory.CompanionTheory.Ar.PB
