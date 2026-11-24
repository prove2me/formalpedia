-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PatGrp.patChar_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:12:15.573621+00:00
-- url     : https://prove2.me/submissions/1e4a5020-b90e-4a48-9664-9a5800d69826

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_PatGrp_pair_add
import Theorems.Thm_GlobalTheory_CompanionTheory_PatGrp_pair_one
import Theorems.Thm_GlobalTheory_CompanionTheory_PatGrp_pair_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PatGrp
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {Φ : ι → ι → Prop}
namespace GlobalTheory.CompanionTheory.PatGrp
theorem _root_.solution (h : IsPat Φ) {E : ι → ι → K} (hE : IsPatChar Φ E) (ψ₀ : AddChar K ℂ)
    {u v : GL ι K} (hu : u ∈ patSet K Φ) (hv : v ∈ patSet K Φ) :
    patChar E ψ₀ (u * v) = patChar E ψ₀ u * patChar E ψ₀ v := by
  have hu' := (mem_patSet_iff h u).1 hu
  have hv' := (mem_patSet_iff h v).1 hv
  have key : ∀ w : GL ι K, patChar E ψ₀ w = ψ₀ (pair E (w : Matrix ι ι K)) := fun w => rfl
  rw [key, key, key, ← AddChar.map_add_eq_mul]
  congr 1
  set A := (u : Matrix ι ι K) - 1 with hAdef
  set Bm := (v : Matrix ι ι K) - 1 with hBdef
  have eu : (u : Matrix ι ι K) = 1 + A := by
    rw [hAdef]
    abel
  have ev : (v : Matrix ι ι K) = 1 + Bm := by
    rw [hBdef]
    abel
  rw [Units.val_mul, eu, ev]
  have e2 : (1 + A) * (1 + Bm) = 1 + (A + Bm + A * Bm) := by noncomm_ring
  rw [e2]
  simp only [pair_add]
  rw [pair_one h hE, pair_mul hE hu' hv']
  ring
end GlobalTheory.CompanionTheory.PatGrp
