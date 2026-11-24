-- Prove2me | solution 1 for GlobalTheory.UTr.eq_mulMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:43:34.79386+00:00
-- url     : https://prove2.me/submissions/10ea4dc3-cee7-4c19-8a7f-ddcc1b4f7e5d

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
namespace GlobalTheory.UTr
theorem _root_.solution (i : Alg P ≃ₗ[B] (n → B)) {z : Alg P} {g : Matrix n n B} (h : ∀ y, g *ᵥ i y = i (z * y)) :
    g = mulMat i z :=
  Matrix.toLin'.injective (LinearMap.ext fun u => by
    obtain ⟨y, rfl⟩ := i.surjective u
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h, mulMat_mulVec])
end GlobalTheory.UTr
