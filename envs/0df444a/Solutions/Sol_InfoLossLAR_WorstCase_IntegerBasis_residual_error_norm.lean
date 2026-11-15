-- Prove2me | solution 1 for InfoLossLAR.WorstCase.IntegerBasis.residual_error_norm
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T02:28:22.049121+00:00
-- url     : https://prove2.me/submissions/848857d2-0637-442e-a755-e2fcae9cba01

import Definitions.Def_InfoLossLAR_BDD_Coordinates

set_option autoImplicit false

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis

open RegevLWE.GaussConv GaussianProjection GaussianProjection.CosetGeometry

noncomputable section

variable {dimension : ℕ}

/-- Exact error contraction for one successful modular-decoding step. -/
theorem residual_error (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (q : ℕ) [NeZero q] (nearest : dual (inputLattice basis hdet)) (query : Space (dimension:=dimension)) :
    residualQuery basis hdet q query (secretCoordinates q (inputLattice basis hdet) (integerBasis basis hdet) nearest)-
      (residualNearest basis hdet q nearest : Space (dimension:=dimension))=
        (q : ℝ)⁻¹ • (query-(nearest : Space (dimension:=dimension))) := by
  simp only [residualQuery,residualNearest,smul_sub]
  abel

end

end InfoLossLAR.WorstCase.IntegerBasis



open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.IntegerBasis
open RegevLWE.GaussConv InfoLossLAR.WorstCase.GaussianProjection InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

theorem solution {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (q : ℕ) [NeZero q] (nearest : dual (inputLattice basis hdet)) (query : InfoLossLAR.WorstCase.IntegerBasis.Space (dimension:=dimension)) :
    ‖residualQuery basis hdet q query (secretCoordinates q (inputLattice basis hdet) (integerBasis basis hdet) nearest)-
      (residualNearest basis hdet q nearest : InfoLossLAR.WorstCase.IntegerBasis.Space (dimension:=dimension))‖=
        ‖query-(nearest : InfoLossLAR.WorstCase.IntegerBasis.Space (dimension:=dimension))‖/(q : ℝ) := by
  have hq : (0 : ℝ)<q := by exact_mod_cast NeZero.pos q
  rw [residual_error,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hq)]
  ring
