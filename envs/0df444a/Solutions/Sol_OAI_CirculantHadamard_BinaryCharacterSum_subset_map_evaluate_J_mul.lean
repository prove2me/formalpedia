-- Prove2me | solution 1 for OAI.CirculantHadamard.BinaryCharacterSum.subset_map_evaluate_J_mul
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:05:10.99121+00:00
-- url     : https://prove2.me/submissions/8aef130e-2ee3-4c71-82a7-4240bc4a2e43

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
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeComponents
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeCharacterEvaluations
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalizationMaps
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalization
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_AlternatingProducts
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryProductTransport

open OAI OAI.CirculantHadamard
universe uG uR uA uI uT uK uk uB
open scoped BigOperators
theorem solution
    {I : Type uI} {A : Type uA} {R : Type uR} {T : Type uT} [Fintype I] [DecidableEq I] [CommRing A]
    [CommRing R] [IsDomain R] [CommRing T] {n : ℕ} [NeZero n]
    (φ : A →+* R) (ψ : R →+* T)
    (χ : Finset I → Multiplicative (ZMod n) →* R)
    (ε d : Finset I → T) (hε : ε ∅ = 1) (htrivial : χ ∅ = 1)
    (hnonempty : ∀ S : Finset I, S.Nonempty →
      ∃ g : Multiplicative (ZMod n), χ S g ≠ 1) :
    (∑ S : Finset I, ε S * ψ (CyclicRing.evaluate φ (χ S)
      (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n)) * d S) =
      (n : T) * d ∅ := by
  have heval : ∀ S : Finset I, CyclicRing.evaluate φ (χ S)
      (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n) =
      ∑ g : Multiplicative (ZMod n), χ S g := by
    intro S
    rw [CyclicRing.evaluate_apply]
    refine Fintype.sum_equiv Multiplicative.ofAdd _ _ (fun a => ?_)
    simp [BinaryCoefficients.JOver, BinaryCoefficients.ofCoeffs_apply]
  rw [Finset.sum_eq_single (∅ : Finset I)]
  · rw [heval, htrivial, hε]
    simp
  · intro S _ hS
    have hne : χ S ≠ 1 := by
      obtain ⟨g, hg⟩ := hnonempty S (Finset.nonempty_iff_ne_empty.2 hS)
      intro h; apply hg; rw [h]; rfl
    rw [heval, sum_hom_units_eq_zero (χ S) hne, map_zero, mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h
