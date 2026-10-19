-- Prove2me | solution 1 for OAI.CirculantHadamard.RamifiedLocal.exists_scalar_add_uniformizer_mul
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T09:49:52.802073+00:00
-- url     : https://prove2.me/submissions/013b1a70-38ab-473c-9d8d-985151308535

import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_DyadicRemainder
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedEisenstein
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedLocal

open OAI OAI.CirculantHadamard OAI.CirculantHadamard.RamifiedLocal
universe uA
open Polynomial
theorem solution (A : Type uA) [CommRing A] (p k : ℕ)
    (x : Extension A p k) :
    ∃ a : A, ∃ b : Extension A p k,
      x = algebraMap A (Extension A p k) a + uniformizer A p k * b := by
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective x
  obtain ⟨q, hq⟩ := X_sub_C_dvd_sub_C_eval (a := (1 : A)) (p := g)
  refine ⟨g.eval 1, AdjoinRoot.mk _ q, ?_⟩
  have : g = C (g.eval 1) + (X - C 1) * q := by rw [← hq]; ring
  conv_lhs => rw [this]
  simp [uniformizer, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]
