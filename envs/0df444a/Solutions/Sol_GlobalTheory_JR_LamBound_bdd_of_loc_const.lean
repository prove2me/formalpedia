-- Prove2me | solution 1 for GlobalTheory.JR.LamBound.bdd_of_loc_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:01:16.425591+00:00
-- url     : https://prove2.me/submissions/25797153-53c1-439e-a992-6dc901af8d7b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WhittakerBoundBigCell

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LamBound
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.LamBound
theorem _root_.solution (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    (O : Set K) (hO : IsCompact O) (Ψ : SpecialLinearGroup (Fin 2) K → ℂ) (U : Set K) (hU : U ∈ 𝓝 (0 : K))
    (hΨ : ∀ g k : SpecialLinearGroup (Fin 2) K, (∀ i j, ((k : Matrix (Fin 2) (Fin 2) K) - 1) i j ∈ U) →
      Ψ (g * k) = Ψ g) :
    ∃ C : ℝ, ∀ k : SpecialLinearGroup (Fin 2) K, (∀ i j, (k : Matrix (Fin 2) (Fin 2) K) i j ∈ O) → ‖Ψ k‖ ≤ C := by
  classical
  let T : Set (Matrix (Fin 2) (Fin 2) K) := {M | ∀ i j, M i j ∈ O} ∩ {M | M.det = 1}
  have hT : IsCompact T := by
    have h1 : IsCompact {M : Matrix (Fin 2) (Fin 2) K | ∀ i j, M i j ∈ O} := by
      have := isCompact_univ_pi (fun _ : Fin 2 => isCompact_univ_pi (fun _ : Fin 2 => hO))
      have he : {M : Matrix (Fin 2) (Fin 2) K | ∀ i j, M i j ∈ O} =
          Set.univ.pi (fun _ : Fin 2 => Set.univ.pi fun _ : Fin 2 => O) := by
        ext M
        exact ⟨fun h => Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => h i j,
          fun h i j => Set.mem_univ_pi.1 (Set.mem_univ_pi.1 h i) j⟩
      rw [he]; exact this
    exact h1.inter_right (isClosed_eq (continuous_id.matrix_det) continuous_const)
  let N : Matrix (Fin 2) (Fin 2) K → Set (Matrix (Fin 2) (Fin 2) K) := fun M =>
    {M' | ∀ i j, (M.adjugate * M' - 1) i j ∈ U}
  have hN : ∀ M ∈ T, N M ∈ 𝓝 M := by
    intro M hM
    have hc : Continuous (fun M' : Matrix (Fin 2) (Fin 2) K => M.adjugate * M' - 1) :=
      (continuous_const.matrix_mul continuous_id).sub continuous_const
    have h0 : M.adjugate * M - 1 = 0 := by
      rw [Matrix.adjugate_mul, hM.2]; simp
    have hij : ∀ i j, ∀ᶠ M' in 𝓝 M, (M.adjugate * M' - 1) i j ∈ U := by
      intro i j
      have hcij : Continuous (fun M' : Matrix (Fin 2) (Fin 2) K => (M.adjugate * M' - 1) i j) :=
        hc.matrix_elem i j
      have := hcij.tendsto M
      simp only [h0, Matrix.zero_apply] at this
      exact this hU
    exact Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hij i j
  obtain ⟨t, htT, hcov⟩ := hT.elim_nhds_subcover N hN
  let g : Matrix (Fin 2) (Fin 2) K → ℝ := fun M => if h : M.det = 1 then ‖Ψ ⟨M, h⟩‖ else 0
  refine ⟨∑ M ∈ t, g M, fun k hk => ?_⟩
  have hkT : (k : Matrix (Fin 2) (Fin 2) K) ∈ T := ⟨hk, k.2⟩
  obtain ⟨M, hMt, hkM⟩ := Set.mem_iUnion₂.1 (hcov hkT)
  have hdet : M.det = 1 := (htT M hMt).2
  let k₀ : SpecialLinearGroup (Fin 2) K := ⟨M, hdet⟩
  have he : Ψ k = Ψ k₀ := by
    have := hΨ k₀ (k₀⁻¹ * k) (by
      intro i j
      have := hkM i j
      exact this)
    simpa using this
  have hg : g M = ‖Ψ k₀‖ := by simp only [g, dif_pos hdet]; rfl
  rw [he, ← hg]
  exact Finset.single_le_sum (f := g) (fun M _ => by simp only [g]; split_ifs <;> positivity) hMt
end GlobalTheory.JR.LamBound
