-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.Bruhat.bruhat_parab_parab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:47:34.520334+00:00
-- url     : https://prove2.me/submissions/95d41121-143d-4129-a68a-e5c26e88e7a4

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BruhatDecompositionTwoBlocks
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Bruhat_pm_eq_permGL
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Bruhat_conj_mem_parab
import Theorems.Thm_GroundTheory_Automorphic_exists_mem_doubleCoset_permGL


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin Formalism.IrreducibleCountingLemmas.TYPES GroundTheory.Automorphic
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.Bruhat
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {n : ℕ}
namespace GlobalTheory.CompanionTheory.TyFin.Bruhat
theorem _root_.solution {s s' : ℕ} (b : Fin n → Fin s) (b' : Fin n → Fin s')
    (g : GL (Fin n) K) :
    ∃ σ : Equiv.Perm (Fin n), ∃ β ∈ parab K b', ∃ α ∈ parab K b, g = β * pm K σ * α := by
  set τ := Tuple.sort b
  set τ' := Tuple.sort b'
  obtain ⟨ρ, hρ⟩ := exists_mem_doubleCoset_permGL ((pm K τ')⁻¹ * g * pm K τ)
  obtain ⟨x, hx, y, hy, hxy⟩ := DoubleCoset.mem_doubleCoset.1 hρ
  refine ⟨τ' * ρ * τ⁻¹, _, conj_mem_parab b' τ' (Tuple.monotone_sort b') hx,
    _, conj_mem_parab b τ (Tuple.monotone_sort b) hy, ?_⟩
  have hm : pm K (τ' * ρ * τ⁻¹) = pm K τ' * permGL K ρ * (pm K τ)⁻¹ := by
    simp only [pm_eq_permGL, map_mul, map_inv]
  have hg : g = pm K τ' * (x * permGL K ρ * y) * (pm K τ)⁻¹ := by
    rw [← hxy]; group
  rw [hm, hg]
  group
end GlobalTheory.CompanionTheory.TyFin.Bruhat
