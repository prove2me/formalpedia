-- Prove2me | solution 1 for GlobalTheory.SmoothRiesz.exists_eq_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:06:41.272804+00:00
-- url     : https://prove2.me/submissions/3f2915f5-ceb0-492c-8732-b33051d80b50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UnitaryAdmissibleMatrixCoefficient
import Theorems.Thm_GlobalTheory_SmoothRiesz_exists_mem_eq_on_of_finiteDimensional
import Theorems.Thm_GlobalTheory_SmoothRiesz_finite_orbit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory
open scoped Pointwise
open GlobalTheory GlobalTheory.SmoothRiesz
namespace GlobalTheory.SmoothRiesz
theorem _root_.solution {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ G V) (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hadm : IsAdmissible σ) (hpos : ∀ v, v ≠ 0 → 0 < (Bf v v).re)
    (hinv : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w) (L : V →ₗ⋆[ℂ] ℂ)
    (K : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (hL : ∀ s ∈ K, ∀ w, L (σ s w) = L w) : ∃ u : V, ∀ w, L w = Bf u w := by
  haveI : FiniteDimensional ℂ (fixed σ K) := hadm.2 K hKo hKc
  obtain ⟨u, huK, hu⟩ := exists_mem_eq_on_of_finiteDimensional Bf hpos L (fixed σ K)
  have hfix : ∀ k ∈ K, σ k u = u := fun k hk => by
    simpa using huK ⟨k, hk⟩
  refine ⟨u, fun w => ?_⟩
  have hcomp : ∀ (a b : G) (x : V), σ a (σ b x) = σ (a * b) x := fun a b x => by
    rw [map_mul, Module.End.mul_apply]
  let O : Finset V := (finite_orbit σ hadm.1 K hKc w).toFinset
  have hO : ∀ x, x ∈ O ↔ ∃ k ∈ K, σ k w = x := fun x => by simp [O]
  have hwO : w ∈ O := (hO w).2 ⟨1, K.one_mem, by simp⟩
  have hcard : ((O.card : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨w, hwO⟩)
  have heK : (∑ x ∈ O, x) ∈ fixed σ K := by
    intro k
    simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sum]
    refine Finset.sum_nbij' (fun x => σ k x) (fun x => σ (k : G)⁻¹ x) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      obtain ⟨c, hc, rfl⟩ := (hO x).1 hx
      exact (hO _).2 ⟨k * c, K.mul_mem k.2 hc, (hcomp _ _ _).symm⟩
    · intro x hx
      obtain ⟨c, hc, rfl⟩ := (hO x).1 hx
      exact (hO _).2 ⟨(k : G)⁻¹ * c, K.mul_mem (K.inv_mem k.2) hc, (hcomp _ _ _).symm⟩
    · intro x _
      rw [hcomp]; simp
    · intro x _
      rw [hcomp]; simp
    · intro x _
      rfl
  have hLO : ∀ x ∈ O, L x = L w := fun x hx => by
    obtain ⟨c, hc, rfl⟩ := (hO x).1 hx
    exact hL c hc w
  have hBO : ∀ x ∈ O, Bf u x = Bf u w := fun x hx => by
    obtain ⟨c, hc, rfl⟩ := (hO x).1 hx
    conv_lhs => rw [← hfix c hc]
    exact hinv c u w
  have key := hu _ heK
  rw [map_sum, map_sum, Finset.sum_congr rfl hLO, Finset.sum_congr rfl hBO, Finset.sum_const,
    Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul] at key
  exact mul_left_cancel₀ hcard key
end GlobalTheory.SmoothRiesz
