-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimGood.inert_case
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:50:33.026314+00:00
-- url     : https://prove2.me/submissions/64a9bbd1-b0b8-4dd7-a2bf-94c239c5c90a

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PrimitiveVectorLatticeRescaleAlmostAll
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimGood_val_norm
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimGood_coord_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimGood_repr_one
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimGood_nrm_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimGood_nrm_one
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimGood_exists_inv
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimGood_le_one_of_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PrimGood
variable {L K : Type} [Field L] [CommRing K] [Algebra L K] (B : Module.Basis (Fin 2) L K)
variable {B} {Δ : L}
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ)
namespace GlobalTheory.CompanionTheory.SW.PrimGood
theorem _root_.solution (h0 : B 0 = 1) (h1 : B 1 * B 1 = algebraMap L K Δ)
    (hsq : ∀ x : L, w (x - 1) < 1 → IsSquare x) (hΔ : w Δ = 1) (hn : ¬ IsSquare Δ)
    {M : ℕ} (y z : Fin M → K) (hz : z ⬝ᵥ y = 1) :
    ∃ (u : Kˣ) (z' : Fin M → K), (∀ k l, w (B.repr ((u : K) * y k) l) ≤ 1) ∧
      (∀ k l, w (B.repr (z' k) l) ≤ 1) ∧ ∑ k, z' k * ((u : K) * y k) = 1 := by
  have h10 : (1 : K) ≠ 0 := h0 ▸ B.ne_zero 0
  obtain ⟨i₀, hi₀⟩ : ∃ i, y i ≠ 0 := by
    by_contra! hall
    apply h10
    rw [← hz]
    simp [dotProduct, hall]
  haveI : Nonempty (Fin M) := ⟨i₀⟩
  obtain ⟨i, hi⟩ := Finite.exists_max (fun k => w (nrm B Δ (y k)))
  have hNv (x : K) : w (nrm B Δ x) = max (w (B.repr x 0)) (w (B.repr x 1)) ^ 2 :=
    val_norm w hsq hΔ hn _ _
  have hne (x : K) (hx : x ≠ 0) : nrm B Δ x ≠ 0 := by
    intro hN
    have h := hNv x
    rw [hN, map_zero] at h
    have hm := (pow_eq_zero_iff two_ne_zero).1 h.symm
    have ha : w (B.repr x 0) = 0 := le_antisymm (hm ▸ le_max_left _ _) zero_le
    have hc : w (B.repr x 1) = 0 := le_antisymm (hm ▸ le_max_right _ _) zero_le
    apply hx
    rw [coord_eq h0 x, (Valuation.zero_iff w).1 ha, (Valuation.zero_iff w).1 hc]
    simp
  have hNi : nrm B Δ (y i) ≠ 0 := by
    intro hN
    have h := hi i₀
    simp only [hN, map_zero] at h
    exact hne _ hi₀ ((Valuation.zero_iff w).1 (le_antisymm h zero_le))
  obtain ⟨x', hx'⟩ := exists_inv h0 h1 (y i) hNi
  refine ⟨⟨x', y i, by rw [mul_comm]; exact hx', hx'⟩, Pi.single i 1, ?_, ?_, ?_⟩
  · intro k l
    have hn' : w (nrm B Δ (x' * y k)) ≤ 1 := by
      have e1 : nrm B Δ x' * nrm B Δ (y i) = 1 := by
        rw [← nrm_mul h0 h1, mul_comm, hx', nrm_one h0]
      rw [nrm_mul h0 h1, map_mul]
      calc w (nrm B Δ x') * w (nrm B Δ (y k)) ≤ w (nrm B Δ x') * w (nrm B Δ (y i)) :=
            mul_le_mul' le_rfl (hi k)
        _ = 1 := by rw [← map_mul, e1, map_one]
    rw [hNv] at hn'
    have hm := le_one_of_sq hn'
    fin_cases l
    · exact (le_max_left _ _).trans hm
    · exact (le_max_right _ _).trans hm
  · intro k l
    by_cases hk : k = i
    · subst hk
      obtain ⟨e0, e1⟩ := repr_one (B := B) h0
      fin_cases l <;> simp [e0, e1]
    · simp [Pi.single_apply, hk]
  · simp only [Units.val_mk]
    simp [Pi.single_apply, mul_comm x', hx']
end GlobalTheory.CompanionTheory.SW.PrimGood
