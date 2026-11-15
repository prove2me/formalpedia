-- Prove2me | solution 1 for InfoLossLAR.WorstCase.IntegerBasis.reconstruct_residualNearest
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T02:19:51.186036+00:00
-- url     : https://prove2.me/submissions/1c2e0738-014a-4365-bc13-73762ea68278

import Definitions.Def_InfoLossLAR_BDD_Coordinates

set_option autoImplicit false

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis

open RegevLWE.GaussConv GaussianProjection GaussianProjection.CosetGeometry

noncomputable section

variable {dimension : ℕ}

end

end InfoLossLAR.WorstCase.IntegerBasis



open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.IntegerBasis
open RegevLWE.GaussConv InfoLossLAR.WorstCase.GaussianProjection InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

theorem solution {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (q : ℕ) [NeZero q] (nearest : dual (inputLattice basis hdet)) :
    reconstructPoint basis hdet q (secretCoordinates q (inputLattice basis hdet) (integerBasis basis hdet) nearest)
      (residualNearest basis hdet q nearest : InfoLossLAR.WorstCase.IntegerBasis.Space (dimension:=dimension))=(nearest : InfoLossLAR.WorstCase.IntegerBasis.Space (dimension:=dimension)) := by
  have hq : (q : ℝ)≠0 := by exact_mod_cast NeZero.ne q
  simp only [reconstructPoint,residualNearest,smul_smul,mul_inv_cancel₀ hq,one_smul,sub_add_cancel]
