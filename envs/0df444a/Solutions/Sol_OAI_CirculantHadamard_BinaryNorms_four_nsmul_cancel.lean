-- Prove2me | solution 1 for OAI.CirculantHadamard.BinaryNorms.four_nsmul_cancel
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T09:49:18.984138+00:00
-- url     : https://prove2.me/submissions/6567c1ba-d4ee-4624-80e1-99f3beefb603

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
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_OrderHalving
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryBlocks
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryCoefficients
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicRings

open OAI OAI.CirculantHadamard
universe uR uA
open CyclicRing
variable {R : Type uR} [CommRing R] [IsDomain R] [CharZero R]
variable {n : ℕ}
theorem solution {f g : Elem R n}
    (h : (4 : ℕ) • f = (4 : ℕ) • g) : f = g := by
  apply AddMonoidAlgebra.coeff_injective
  ext a
  have := congrArg (fun x => AddMonoidAlgebra.coeff x a) h
  rw [AddMonoidAlgebra.coeff_smul_apply, AddMonoidAlgebra.coeff_smul_apply, nsmul_eq_mul,
    nsmul_eq_mul] at this
  exact mul_left_cancel₀ (by norm_num) this
