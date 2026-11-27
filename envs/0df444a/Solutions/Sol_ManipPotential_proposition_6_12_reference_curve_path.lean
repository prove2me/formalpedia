-- Prove2me | solution 1 for ManipPotential.proposition_6_12_reference_curve_path
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:37:31.063215+00:00
-- url     : https://prove2.me/submissions/dc6c4bed-538f-420c-8581-7dc725e9b5c6

import Mathlib
import Definitions.Def_ManipPotential_GAxioms
import Definitions.Def_ManipPotential_TransferVectors
import Definitions.Def_ManipPotential_ell
import Definitions.Def_ManipPotential_unitVec
import Definitions.Def_ManipPotential_ExtRanking
import Definitions.Def_ManipPotential_IsCommonJunction
import Definitions.Def_ManipPotential_TransferStep
import Definitions.Def_ManipPotential_referenceCurve
import Theorems.Thm_ManipPotential_proposition_6_12_rational_transfer_approximation
import Theorems.Thm_ManipPotential_proposition_6_12_reference_curve_support
import Theorems.Thm_ManipPotential_proposition_6_12_transfer_path_assembly

open scoped NNReal Pointwise
open ManipPotential

/-- If the negative cyclic difference belongs to the closed transfer-plus-derivative cone,
the reference-curve construction gives a finite rational transfer path with forbidden endpoint
winners. -/
theorem solution {m : ℕ} [NeZero m] (hm : 3 ≤ m) (K : ℕ)
    (g : (Ranking m → ℚ) → Fin m) (hg : GAxioms K g)
    (G : ((ExtRanking m → ℝ) × ℝ) → (Ranking m → ℝ))
    (U : Set ((ExtRanking m → ℝ) × ℝ)) (hUopen : IsOpen U)
    (z₀ : ((ExtRanking m → ℝ) × ℝ)) (hzU : z₀ ∈ U)
    (hzdiff : DifferentiableAt ℝ G z₀)
    (hJ : ∀ z ∈ U, IsCommonJunction g (G z))
    (hpos : ∀ z ∈ U, ∀ r, 1 < G z r) (i j : Fin m) (hij : i ≠ j)
    (hmem :
      let D : ((ExtRanking m → ℝ) × ℝ) →ₗ[ℝ] (Ranking m → ℝ) :=
        (fderiv ℝ G z₀).toLinearMap
      let T : Submodule ℝ (Ranking m → ℝ) := LinearMap.range D
      let C : Submodule ℝ≥0 (Ranking m → ℝ) :=
        Submodule.span ℝ≥0 (TransferVectors ((K : ℝ) + 1) i j)
      (-(unitVec (ell i) - unitVec (ell j))) ∈
        closure ((C : Set (Ranking m → ℝ)) + (T : Set (Ranking m → ℝ)))) :
    ∃ (L : ℕ) (Q : ℕ → Ranking m → ℚ),
      g (Q 0) = i ∧ g (Q L) = j ∧
      (∀ k ≤ L, g (Q k) = i ∨ g (Q k) = j) ∧
      (∀ k < L, TransferStep K i j (Q k) (Q (k + 1))) := by
  dsimp only at hmem
  have hκ : 0 < kappa m K := by
    unfold kappa
    positivity
  have hη : 0 < 1 / (64 * kappa m K) := by positivity
  obtain ⟨v, q, u, β, hu, hβ, herr⟩ :=
    ManipPotential.proposition_6_12_rational_transfer_approximation
      K G z₀ i j hmem (1 / (64 * kappa m K)) hη
  obtain ⟨ρ, L, Q, hρ, hε, hline, hclose, hzero, hone, hsteps⟩ :=
    ManipPotential.proposition_6_12_transfer_path_assembly
      K G U hUopen z₀ hzU hzdiff hpos i j hij v q u β hu hβ herr
  have hρR : 0 < (ρ : ℝ) := by exact_mod_cast hρ
  have support (t : ℝ) (ht : t ∈ Set.Icc 0 1) (R : Ranking m → ℚ)
      (hR : ‖(fun r => (R r : ℝ)) - referenceCurve K G z₀ v i j (ρ : ℝ) t‖ <
        ((ρ : ℝ) / (4 * kappa m K)) / 4) :
      (g R = i ∨ g R = j) ∧ (t = 0 → g R = i) ∧ (t = 1 → g R = j) :=
    ManipPotential.proposition_6_12_reference_curve_support
      hm K g hg G z₀ v i j hij (ρ : ℝ) hρR hε t ht R
        (hJ _ (hline t ht)) (hpos _ (hline t ht)) hR
  refine ⟨L, Q, ?_, ?_, ?_, hsteps⟩
  · exact (support 0 ⟨le_rfl, zero_le_one⟩ (Q 0) hzero).2.1 rfl
  · exact (support 1 ⟨zero_le_one, le_rfl⟩ (Q L) hone).2.2 rfl
  · intro k hk
    obtain ⟨t, ht, hR⟩ := hclose k hk
    exact (support t ht (Q k) hR).1
