-- Prove2me | solution 1 for MassDataIdxStIm.par_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:13.845752+00:00
-- url     : https://prove2.me/submissions/8b1b8a99-5d4b-4d7d-b941-cebf9a771fa8

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_LeviEmbeddingBlock32

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open MassDataIdxStIm
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3
variable {A : Type} {r k : ℕ}
variable [CommRing A]
variable {P : Matrix (Fin k) (Fin k) A → Prop}
namespace MassDataIdxStIm
theorem _root_.solution (hP : GP P) {x : Matrix (Idx r k) (Idx r k) A} (hx : Par P x) : IsUnit x.det := by
  obtain ⟨h1, h3, h21, h31, h32, h, hPh, h22⟩ := hx
  rw [← Matrix.fromBlocks_toBlocks x]
  have hz : x.toBlocks₂₁ = 0 := by
    ext i j
    rcases i with a | a
    · exact congrFun (congrFun h21 a) j
    · exact congrFun (congrFun h31 a) j
  have hD : x.toBlocks₂₂ = Matrix.fromBlocks (b22 x) (b23 x) 0 (b33 x) := by
    ext i j
    rcases i with a | a <;> rcases j with b | b
    · rfl
    · rfl
    · exact congrFun (congrFun h32 a) b
    · rfl
  rw [hz, Matrix.det_fromBlocks_zero₂₁, hD, Matrix.det_fromBlocks_zero₂₁, h22, midEmb_det]
  exact (uni_unit h1).mul ((hP.unit hPh).mul (uni_unit h3))
end MassDataIdxStIm
