-- Prove2me | solution 1 for GlobalTheory.eventually_eq_column
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:08:54.576322+00:00
-- url     : https://prove2.me/submissions/79da514d-3e9e-4867-9f47-ec849f920e63

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FiniteAbsLeOneMulMemRange
import Theorems.Thm_GlobalTheory_eq_on_rankOneCurve
import Theorems.Thm_GlobalTheory_posDef_sub_vecMulVec_add

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
namespace GlobalTheory
theorem _root_.solution (hol : IsHoloSiegel g H) (hH : IsSpInvariant g H)
    (hb : ∀ c : ℝ, 0 < c → ∃ K : ℝ, ∀ τ ∈ SiegelH (Fin g),
      (τ.map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef → ‖H τ‖ ≤ K)
    (e : Fin g) {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g)) :
    ∀ᶠ s in 𝓝 (0 : ℂ), H (τ + s • vecMulVec (fun i => ((τ i e).im : ℂ))
      (fun i => ((τ i e).im : ℂ))) = H τ := by
  have he : 0 < (τ e e).im := hτ.2.diag_pos (i := e)
  let u : Fin g → ℝ := fun i => (τ i e).im / (τ e e).im
  let v : Fin g → ℝ := fun i => (τ i e).re - (τ e e).re * u i
  have hu : u e = 1 := div_self he.ne'
  have hv : v e = 0 := by simp [v, hu]
  let R : Matrix (Fin g) (Fin g) ℝ := vecMulVec (Pi.single e 1) v + vecMulVec v (Pi.single e 1)
  let Z : Matrix (Fin g) (Fin g) ℂ := of fun i j => τ i j - R i j - τ e e * u i * u j
  have hZs : Z.IsSymm := by
    ext i j
    simp only [Z, R, transpose_apply, of_apply, Matrix.add_apply, vecMulVec_apply, hτ.1.apply i j]
    push_cast
    ring
  have hZe : ∀ i, Z i e = 0 := fun i => by
    apply Complex.ext
    · simp [Z, R, vecMulVec_apply, hu, v]
    · simp [Z, hu]
      simp only [u]
      field_simp
      ring
  have hZ : ∀ u : Fin g → ℝ, u e = 1 → ∀ y : ℝ, 0 < y →
      (Z.map Complex.im + y • vecMulVec u u).PosDef := fun u' hu' y hy => by
    convert posDef_sub_vecMulVec_add hτ.2 e hu' hy using 2
    ext i j
    simp [Z, vecMulVec_apply]
    simp only [u]
    field_simp
  have hc : Continuous fun s : ℂ => (τ e e + s * (τ e e).im ^ 2).im := by fun_prop
  filter_upwards [continuousAt_const.eventually_lt hc.continuousAt
    (show (0 : ℝ) < _ by simpa using he)] with s hs
  convert eq_on_rankOneCurve hZs hZe hZ hol hH hb hu hv ⟨_, hs⟩ ⟨_, he⟩ using 2
  · ext i j
    have : ((τ e e).im : ℂ) ≠ 0 := by exact_mod_cast he.ne'
    simp [rankOneCurve, Z, R, vecMulVec_apply]
    simp only [u]
    push_cast
    field_simp
    ring
  · ext i j
    simp [rankOneCurve, Z, R]
    ring
end GlobalTheory
