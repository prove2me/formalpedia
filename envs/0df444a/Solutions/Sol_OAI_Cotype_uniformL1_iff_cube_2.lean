-- Prove2me | solution 2 for OAI.Cotype.uniformL1_iff_cube
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:46:36.872188+00:00
-- url     : https://prove2.me/submissions/80518540-c03b-4aa1-b55f-edf8bc694417

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/UniformL1.lean:L55-L71
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.uniformL1_iff_cube. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.Analysis.Cotype.UniformL1 ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem L1Family.reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ ≃ ι) {x : ι → X} {c : ℝ} (h : L1Family x c) :
    L1Family (fun i => x (e i)) c := by
  refine ⟨fun i => h.1 (e i), fun a => ?_⟩
  have hl := h.2 (fun i => a (e.symm i))
  simpa only [← e.sum_comp, e.symm_apply_apply] using hl

theorem L1Family.restrict {ι κ : Type*} [Fintype ι] [Fintype κ]
    (j : κ ↪ ι) {x : ι → X} {c : ℝ} (h : L1Family x c) :
    L1Family (fun i => x (j i)) c := by
  classical
  refine ⟨fun i => h.1 (j i), fun a => ?_⟩
  let b : ι → ℝ := Function.extend j a (fun _ => 0)
  have hb (i : κ) : b (j i) = a i := j.injective.extend_apply _ _ _
  have hz (i : ι) (hi : i ∉ Finset.univ.image j) : b i = 0 := by
    apply Function.extend_apply'
    simpa using hi
  have hscalar : (∑ i, |b i|) = ∑ i, |a i| := by
    calc
      _ = ∑ i ∈ Finset.univ.image j, |b i| :=
        (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by rw [hz i hi, abs_zero])).symm
      _ = _ := by rw [Finset.sum_image (fun _ _ _ _ he => j.injective he)]; simp only [hb]
  have hvector : (∑ i, b i • x i) = ∑ i, a i • x (j i) := by
    calc
      _ = ∑ i ∈ Finset.univ.image j, b i • x i :=
        (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by rw [hz i hi, zero_smul])).symm
      _ = _ := by rw [Finset.sum_image (fun _ _ _ _ he => j.injective he)]; simp only [hb]
  have hl := h.2 b
  rw [hscalar, hvector] at hl
  exact hl

theorem uniformL1_iff_cube : UniformL1 X ↔
    ∃ L : ℝ, 0 < L ∧ ∀ n : ℕ, ∃ x : Cube n → X, L1Family x L⁻¹ := by
  constructor
  · rintro ⟨c,hc,h⟩
    refine ⟨c⁻¹,inv_pos.mpr hc,fun n => ?_⟩
    obtain ⟨x,hx⟩ := h (Fintype.card (Cube n))
    exact ⟨fun i => x ((Fintype.equivFin (Cube n)) i), by
      simpa using hx.reindex (Fintype.equivFin (Cube n))⟩
  · rintro ⟨L,hL,h⟩
    refine ⟨L⁻¹,inv_pos.mpr hL,fun n => ?_⟩
    obtain ⟨x,hx⟩ := h n
    have hc : Fintype.card (Fin n) ≤ Fintype.card (Cube n) := by
      simp only [Fintype.card_fin, Fintype.card_fun, Fintype.card_bool]
      have hn : n < 2^n := Nat.lt_two_pow_self
      omega
    let j : Fin n ↪ Cube n := Classical.choice (Function.Embedding.nonempty_of_card_le hc)
    exact ⟨fun i => x (j i), hx.restrict j⟩

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.uniformL1_iff_cube := @_root_.OAI.Cotype.uniformL1_iff_cube
