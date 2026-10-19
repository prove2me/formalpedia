-- Prove2me | solution 2 for OAI.CirculantHadamard.LocalComparison.comparison_induction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:43:29.442531+00:00
-- url     : https://prove2.me/submissions/b018e860-b924-43f8-bb4d-83405410c741

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/LocalComparisonInduction.lean:L132-L171
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.LocalComparison.comparison_induction. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_FirstOrderResidue
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryResidue
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalFamily
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_ResidueOneAssociation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicLocalBase
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicAwayLocal
import Theorems.Thm_OAI_CirculantHadamard_LocalComparison_comparison_base
import Theorems.Thm_OAI_CirculantHadamard_LocalComparison_comparison_step_left

-- ---- from OAI.LinearAlgebra.CirculantHadamard.LocalComparisonInduction ----
namespace OAI

universe uA uS

noncomputable section

namespace CirculantHadamard.LocalComparison

open CyclicRing

variable {A : Type uA} {S : Type uS} [CommRing A] [IsDomain A]
  [CommRing S] [domainS : IsDomain S] [IsLocalRing S]

/-- The integral induction with its projection-divisibility input exposed.
The concrete cyclotomic theorem discharges `hdivide`; it is not a definition
of the comparison conclusion. -/
theorem comparison_induction (p : ℕ) (φ : A →+* S)
    (hp : Prime (p : A)) (hpS : φ (p : A) ≠ 0)
    (v : (e : ℕ) → Elem A (p ^ (e + 1)) →+* S)
    (vscalar : ∀ e a, v e (scalar (p ^ (e + 1)) a) = φ a)
    (vres : ∀ F : Elem A (p ^ 1),
      IsLocalRing.residue S (v 0 F) =
        IsLocalRing.residue S (φ (augmentation (p ^ 1) F)))
    (vq : ∀ e F,
      v e (cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) F) = v (e + 1) F)
    (hdivide : ∀ e (b : Aˣ) (F K : Elem A (p ^ (e + 2))),
      F * K = scalar (p ^ (e + 2)) ((p : A) ^ (e + 2) * (b : A)) →
      (∃ F', cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) F =
        scalar (p ^ (e + 1)) (p : A) * F') ∨
      (∃ K', cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) K =
        scalar (p ^ (e + 1)) (p : A) * K')) :
    ∀ e (b : Aˣ) (F K : Elem A (p ^ (e + 1))),
      F * K = scalar (p ^ (e + 1)) ((p : A) ^ (e + 1) * (b : A)) →
      ResidueOneAssociated (IsLocalRing.residue S) (v e F)
        (φ (augmentation (p ^ (e + 1)) F)) ∧
      ResidueOneAssociated (IsLocalRing.residue S) (v e K)
        (φ (augmentation (p ^ (e + 1)) K)) := by
  intro e
  induction e with
  | zero =>
      intro b F K hFK
      exact comparison_base (p ^ (0 + 1)) p φ hp hpS (v 0) (vscalar 0) vres
        b F K (by simpa only [Nat.zero_add, pow_one] using hFK)
  | succ e ih =>
      intro b F K hFK
      rcases hdivide e b F K hFK with ⟨F', hF⟩ | ⟨K', hK⟩
      · exact comparison_step_left p e φ hp.ne_zero (v e) (v (e + 1))
          (vscalar e) (vq e) b F K hFK F' hF (ih b)
      · have hKF : K * F = scalar (p ^ (e + 2))
            ((p : A) ^ (e + 2) * (b : A)) := by
          simpa only [mul_comm] using hFK
        exact (comparison_step_left p e φ hp.ne_zero (v e) (v (e + 1))
          (vscalar e) (vq e) b K F hKF K' hK (ih b)).symm

end CirculantHadamard.LocalComparison

end

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard OAI.CirculantHadamard.LocalComparison
open CyclicRing


theorem solution.{uA,uS} : type_of% @_root_.OAI.CirculantHadamard.LocalComparison.comparison_induction.{uA,uS} := @_root_.OAI.CirculantHadamard.LocalComparison.comparison_induction.{uA,uS}
