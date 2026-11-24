-- Prove2me | solution 1 for GlobalTheory.JR.OKCompact.continuous_coeff_charpoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:08:35.763954+00:00
-- url     : https://prove2.me/submissions/4af7bbae-9914-4d0f-9e5c-e8afd1539abb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCompactFiniteEtaleHermitianPairOK

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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.OKCompact
namespace GlobalTheory.JR.OKCompact
theorem _root_.solution {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] {n : ℕ}
    (k : ℕ) : Continuous fun M : Matrix (Fin n) (Fin n) A => M.charpoly.coeff k := by
  have : (fun M : Matrix (Fin n) (Fin n) A => M.charpoly.coeff k) = fun M =>
      MvPolynomial.eval (fun p : Fin n × Fin n => M p.1 p.2)
        (MvPolynomial.map (Int.castRingHom A) ((Matrix.charpoly.univ ℤ (Fin n)).coeff k)) := by
    funext M
    rw [MvPolynomial.eval_map]
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (Int.castRingHom A) (fun p => M p.1 p.2) k).symm
  rw [this]
  exact (MvPolynomial.continuous_eval _).comp (by fun_prop)
end GlobalTheory.JR.OKCompact
