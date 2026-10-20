-- Prove2me | solution 1 for OAI.Cotype.uniformL1_iff_cube
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:43:57.856958+00:00
-- url     : https://prove2.me/submissions/82e689a7-27eb-47db-8741-25bc535e0c6c

import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1

open OAI OAI.Cotype
open scoped BigOperators
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
theorem h50u_sum_extend {ι κ M : Type*} [Fintype ι] [Fintype κ] [AddCommMonoid M]
    {e : ι → κ} (he : Function.Injective e) (a : ι → ℝ) (F : ℝ → κ → M) (hF : ∀ k, F 0 k = 0) :
    ∑ k, F (Function.extend e a 0 k) k = ∑ i, F (a i) (e i) := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨e, he⟩))]
  · rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [he.extend_apply]
  · intro k _ hk
    have : ¬ ∃ i, e i = k := by
      rintro ⟨i, rfl⟩; exact hk (Finset.mem_map_of_mem _ (Finset.mem_univ i))
    rw [Function.extend_apply' _ _ _ this]
    simpa using hF k

theorem h50u_comp {ι κ : Type*} [Fintype ι] [Fintype κ] {x : κ → X} {c : ℝ}
    (hx : L1Family x c) {e : ι → κ} (he : Function.Injective e) : L1Family (x ∘ e) c := by
  refine ⟨fun i => hx.1 (e i), fun a => ?_⟩
  have h := hx.2 (Function.extend e a 0)
  rw [h50u_sum_extend he a (fun r _ => |r|) (fun k => abs_zero),
    h50u_sum_extend he a (fun r k => r • x k) (fun k => zero_smul _ _)] at h
  exact h

theorem t_unif : UniformL1 X ↔
    ∃ L : ℝ, 0 < L ∧ ∀ n : ℕ, ∃ x : Cube n → X, L1Family x L⁻¹ := by
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨c⁻¹, inv_pos.mpr hc, fun n => ?_⟩
    obtain ⟨x, hx⟩ := h (Fintype.card (Cube n))
    rw [inv_inv]
    exact ⟨x ∘ Fintype.equivFin (Cube n), h50u_comp hx (Fintype.equivFin _).injective⟩
  · rintro ⟨L, hL, h⟩
    refine ⟨L⁻¹, inv_pos.mpr hL, fun m => ?_⟩
    obtain ⟨x, hx⟩ := h m
    have hcard : m ≤ Fintype.card (Cube m) := by
      simp only [Cube, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      exact (Nat.lt_two_pow_self).le
    let e : Fin m → Cube m := (Fintype.equivFin (Cube m)).symm ∘ Fin.castLE hcard
    have he : Function.Injective e :=
      (Fintype.equivFin (Cube m)).symm.injective.comp (Fin.castLE_injective hcard)
    exact ⟨x ∘ e, h50u_comp hx he⟩

theorem solution : UniformL1 X ↔
    ∃ L : ℝ, 0 < L ∧ ∀ n : ℕ, ∃ x : Cube n → X, L1Family x L⁻¹ := by
  exact t_unif

