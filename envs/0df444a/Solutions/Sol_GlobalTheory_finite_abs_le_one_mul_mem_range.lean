-- Prove2me | solution 1 for GlobalTheory.finite_abs_le_one_mul_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:48:59.602801+00:00
-- url     : https://prove2.me/submissions/28788885-19d8-430f-8909-da89683910ea

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FiniteAbsLeOneMulMemRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology
open GlobalTheory
variable {g : ℕ} {H : Matrix (Fin g) (Fin g) ℂ → ℂ}
variable {e : Fin g} {Z : Matrix (Fin g) (Fin g) ℂ} (hZs : Z.IsSymm) (hZe : ∀ i, Z i e = 0)
  (hZ : ∀ u : Fin g → ℝ, u e = 1 → ∀ y : ℝ, 0 < y →
    (Z.map Complex.im + y • vecMulVec u u).PosDef)
namespace GlobalTheory
theorem _root_.solution {c : ℝ} (hc : c ≠ 0) :
    {x : ℝ | |x| ≤ 1 ∧ c * x ∈ (Int.castRingHom ℝ).range}.Finite := by
  refine ((Set.finite_Icc (-⌈|c|⌉) ⌈|c|⌉).image fun k : ℤ => (k : ℝ) / c).subset ?_
  rintro x ⟨hx, k, hk⟩
  have hk' : (k : ℝ) = c * x := hk
  refine ⟨k, ?_, by simp only [hk']; field_simp⟩
  have h1 : |(k : ℝ)| ≤ (⌈|c|⌉ : ℤ) := by
    rw [hk', abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg c) hx).trans (Int.le_ceil _)
  exact abs_le.1 (by exact_mod_cast h1)
end GlobalTheory
