-- Prove2me | solution 1 for GlobalTheory.SepCharpoly.charpoly_dvd_of_aeval_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:20:20.399021+00:00
-- url     : https://prove2.me/submissions/609c55fc-3e2e-4253-bd4c-f24b333540a2

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CharpolyDvdOfAevalEqZero
import Theorems.Thm_GlobalTheory_ClassParam_charpoly_dvd_of_aeval
import Theorems.Thm_GlobalTheory_UTr_IsCyc_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix Formalism.UG
open GlobalTheory GlobalTheory.SepCharpoly
namespace GlobalTheory.SepCharpoly
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R) (p : R[X]),
      M.charpoly.Separable → aeval M p = 0 → M.charpoly ∣ p := by
  intro R _ _ n M p hs hp
  classical
  let K := FractionRing R
  let f : R →+* K := algebraMap R K
  have hf : Function.Injective f := IsFractionRing.injective R K
  rw [← Polynomial.map_dvd_map f hf M.charpoly_monic, ← Matrix.charpoly_map]
  refine GlobalTheory.ClassParam.charpoly_dvd_of_aeval (M.map f) ?_ (p.map f) ?_
  · rw [Matrix.charpoly_map]; exact hs.map
  · rw [show M.map f = (f.mapMatrix : Matrix (Fin n) (Fin n) R →+* _) M from rfl]
    have := congrArg (AlgHom.mapMatrix (m := Fin n) (Algebra.ofId R K)) hp
    rw [← aeval_algHom_apply, map_zero] at this
    rw [aeval_map_algebraMap]
    exact this
end GlobalTheory.SepCharpoly
