-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PatGrp.exists_nat_wh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:28:01.428309+00:00
-- url     : https://prove2.me/submissions/76218850-669e-4b66-a577-91f07dab406e

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_PatGrp_coe_patSubgroup
import Theorems.Thm_GlobalTheory_CompanionTheory_PatGrp_patChar_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_PatGrp_exists_nat_avg

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
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (GL ι K) V) : ∃ m : ℕ, wh Φ E ψ₀ ρ.character = m := by
  classical
  set G' := patSubgroup (K := K) h with hG'
  have hmem : ∀ u : GL ι K, u ∈ G' ↔ u ∈ patSet K Φ := fun u => by
    rw [← coe_patSubgroup h]
    rfl
  obtain ⟨m, hm⟩ := exists_nat_avg (H := G') (V := V) (fun x => (patChar E ψ₀ (x : GL ι K))⁻¹)
    (fun a b => by
      show (patChar E ψ₀ ((a : GL ι K) * b))⁻¹ = _
      rw [patChar_mul h hE ψ₀ ((hmem _).1 a.2) ((hmem _).1 b.2), mul_inv])
    (ρ.comp G'.subtype)
  refine ⟨m, ?_⟩
  rw [← hm]
  unfold wh
  have hcard : ((patSet K Φ).ncard : ℂ) = (Fintype.card G' : ℂ) := by
    rw [← Nat.card_eq_fintype_card, ← coe_patSubgroup h]
    exact congrArg _ (Nat.card_coe_set_eq _).symm
  rw [hcard, ← Finset.sum_filter]
  congr 1
  exact Finset.sum_subtype _ (fun u => by simp [hmem]) _
end GlobalTheory.CompanionTheory.PatGrp
