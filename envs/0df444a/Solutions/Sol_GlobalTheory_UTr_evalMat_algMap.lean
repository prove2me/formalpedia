-- Prove2me | solution 1 for GlobalTheory.UTr.evalMat_algMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:43:35.602799+00:00
-- url     : https://prove2.me/submissions/b3c137d5-e359-4d63-8d2e-eac281997ba7

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix Formalism.UG
noncomputable section
open GlobalTheory GlobalTheory.UTr
variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'}
variable {s}
variable (P : Csr s)
variable {n : Type} [Fintype n] [DecidableEq n]
variable {J : Matrix n n B}
variable {P}
variable {x x' : Alg P}
namespace GlobalTheory.UTr
theorem _root_.solution {Q : Csr s'} (φ : B →+* B') (h : Q.1 ∣ P.1.map φ) {g : Matrix n n B} (hg : aeval g P.1 = 0)
    (hg' : aeval (g.map φ) Q.1 = 0) (z : Alg P) : evalMat Q _ hg' (algMap φ h z) = (evalMat P g hg z).map φ := by
  induction z using Alg.induction with
  | hC b =>
    rw [algMap_algebraMap, AlgHom.commutes, AlgHom.commutes]
    ext i j
    simp [Matrix.algebraMap_matrix_apply, apply_ite φ]
  | hr => rw [algMap_root, evalMat_root, evalMat_root]
  | hadd y z hy hz => rw [map_add, map_add, map_add, hy, hz, Matrix.map_add _ (map_add φ)]
  | hmul y z hy hz => rw [map_mul, map_mul, map_mul, hy, hz, Matrix.map_mul]
end GlobalTheory.UTr
