-- Prove2me | solution 1 for GlobalTheory.JR.OKOpen.continuous_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:11:20.137896+00:00
-- url     : https://prove2.me/submissions/09060401-3f8e-49f0-9046-91cc76a93a66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsOpenFiniteEtaleHermitianPairOK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
namespace GlobalTheory.JR.OKOpen
private theorem contCoeff {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))
end GlobalTheory.JR.OKOpen
end

set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.OKOpen
namespace GlobalTheory.JR.OKOpen
theorem _root_.solution {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] (A : Et F E) (i : ℕ) :
    Continuous fun z : A.K => (LinearMap.charpoly (Algebra.lmul F A.K z)).coeff i := by
  let b := Module.finBasis F A.K
  have h : (fun z : A.K => (LinearMap.charpoly (Algebra.lmul F A.K z)).coeff i) =
      fun z => (LinearMap.toMatrix b b (Algebra.lmul F A.K z)).charpoly.coeff i := by
    funext z; rw [LinearMap.charpoly_toMatrix]
  rw [h]
  refine (contCoeff _ i).comp ?_
  refine continuous_pi fun r => continuous_pi fun s => ?_
  have hl : (fun z : A.K => LinearMap.toMatrix b b (Algebra.lmul F A.K z) r s) =
      fun z => (b.coord r) (z * b s) := by
    funext z; simp [LinearMap.toMatrix_apply]
  rw [hl]
  exact IsModuleTopology.continuous_of_linearMap ((b.coord r).comp (LinearMap.mulRight F (b s)))
end GlobalTheory.JR.OKOpen
