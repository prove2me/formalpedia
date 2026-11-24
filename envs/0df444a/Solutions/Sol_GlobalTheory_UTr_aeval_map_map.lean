-- Prove2me | solution 1 for GlobalTheory.UTr.aeval_map_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:43:11.777776+00:00
-- url     : https://prove2.me/submissions/0076021a-7741-4e21-9377-93bcf74d2db0

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
open Polynomial Matrix
variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'}
variable {s}
variable (P : _root_.GlobalTheory.UTr.Csr s)
variable {n : Type} [Fintype n] [DecidableEq n]
variable {J : Matrix n n B}
variable {P}
variable {x x' : _root_.GlobalTheory.UTr.Alg P}
namespace GlobalTheory.UTr
namespace _root_.GlobalTheory.UTr
theorem _root_.solution (φ : B →+* B') (g : Matrix n n B) (q : B[X]) :
    aeval (g.map φ) (q.map φ) = (aeval g q).map φ := by
  change _ = φ.mapMatrix (aeval g q)
  rw [aeval_def, aeval_def, eval₂_map, hom_eval₂]
  congr 1
  refine RingHom.ext fun b => ?_
  ext i j
  simp [algebraMap_matrix_apply, apply_ite φ]
end _root_.GlobalTheory.UTr
end GlobalTheory.UTr
