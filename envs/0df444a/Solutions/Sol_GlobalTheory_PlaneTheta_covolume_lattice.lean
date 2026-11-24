-- Prove2me | solution 1 for GlobalTheory.PlaneTheta.covolume_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:27:14.252377+00:00
-- url     : https://prove2.me/submissions/26a72262-120c-4742-af5d-08ba34a3db7d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeThetaAsymptotics

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Asymptotics
open scoped RealInnerProductSpace
open GlobalTheory GlobalTheory.PlaneTheta
namespace GlobalTheory.PlaneTheta
theorem _root_.solution (L : PeriodPair) :
    ZLattice.covolume L.lattice = |(starRingEnd ℂ L.ω₁ * L.ω₂).im| := by
  rw [ZLattice.covolume_eq_det_mul_measureReal _ _ L.latticeBasis Complex.orthonormalBasisOneI.toBasis,
    MeasureTheory.measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ _),
    MeasureTheory.Measure.real, OrthonormalBasis.coe_toBasis,
    Complex.orthonormalBasisOneI.volume_parallelepiped, ENNReal.toReal_one, _root_.mul_one]
  congr 1
  rw [Module.Basis.det_apply, Matrix.det_fin_two]
  simp [Module.Basis.toMatrix_apply]
  ring
end GlobalTheory.PlaneTheta
