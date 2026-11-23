-- Prove2me | solution 1 for ManipPotential.proposition_6_12_step1_curve
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:49:19.710802+00:00
-- url     : https://prove2.me/submissions/be8b26b6-9e97-4919-a8ac-72d68e47124e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ManipPotential_GAxioms
import Definitions.Def_ManipPotential_TransferVectors
import Definitions.Def_ManipPotential_ell
import Definitions.Def_ManipPotential_unitVec
import Definitions.Def_ManipPotential_ExtRanking
import Definitions.Def_ManipPotential_IsCommonJunction
import Theorems.Thm_ManipPotential_proposition_6_12_reference_curve_path
import Theorems.Thm_ManipPotential_proposition_6_12_no_transfer_path_switch

open scoped NNReal Pointwise

open ManipPotential

/-- Proposition 6.12, Step 1, Eq. (21) (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), pp.35–36): at a differentiability point of the common-junction map, the negative cyclic difference is outside the closure of the sum of the nonnegative transfer cone and the image of the derivative. -/
theorem solution {m : ℕ} [NeZero m] (hm : 3 ≤ m) (K : ℕ)
    (g : (Ranking m → ℚ) → Fin m) (hg : GAxioms K g)
    (G : ((ExtRanking m → ℝ) × ℝ) → (Ranking m → ℝ))
    (U : Set ((ExtRanking m → ℝ) × ℝ)) (hUopen : IsOpen U)
    (z₀ : (ExtRanking m → ℝ) × ℝ) (hzU : z₀ ∈ U)
    (hzdiff : DifferentiableAt ℝ G z₀)
    (hJ : ∀ z ∈ U, IsCommonJunction g (G z))
    (hpos : ∀ z ∈ U, ∀ r, 1 < G z r) (i j : Fin m) (hij : i ≠ j) :
    let D : ((ExtRanking m → ℝ) × ℝ) →ₗ[ℝ] (Ranking m → ℝ) :=
      (fderiv ℝ G z₀).toLinearMap
    let T : Submodule ℝ (Ranking m → ℝ) := LinearMap.range D
    let C : Submodule ℝ≥0 (Ranking m → ℝ) :=
      Submodule.span ℝ≥0 (TransferVectors ((K : ℝ) + 1) i j)
    ¬ (-(unitVec (ell i) - unitVec (ell j)) ∈
      closure ((C : Set (Ranking m → ℝ)) + (T : Set (Ranking m → ℝ)))) := by
  dsimp only
  intro hmem
  obtain ⟨L, Q, hstart, hend, hwinners, hsteps⟩ :=
    ManipPotential.proposition_6_12_reference_curve_path
      hm K g hg G U hUopen z₀ hzU hzdiff hJ hpos i j hij hmem
  exact ManipPotential.proposition_6_12_no_transfer_path_switch
    K g hg.2.1 i j hij L Q hstart hend hwinners hsteps
