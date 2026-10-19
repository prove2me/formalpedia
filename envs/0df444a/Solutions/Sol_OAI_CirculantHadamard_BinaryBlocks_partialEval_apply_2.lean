-- Prove2me | solution 2 for OAI.CirculantHadamard.BinaryBlocks.partialEval_apply
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:02:37.675545+00:00
-- url     : https://prove2.me/submissions/d4728885-74af-48ba-91e3-1052192a2b0f

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/BinaryBlocks.lean:L129-L150
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.BinaryBlocks.partialEval_apply. The node keeps its source
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

-- ---- from OAI.LinearAlgebra.CirculantHadamard.BinaryBlocks ----
namespace OAI

universe uR uS

/-!
# The actual four-block decomposition and partial evaluations

The Chinese remainder equivalence transports the actual cyclic group ring,
not just a coefficient count. Coefficients of its four slices are the original
signs. Partial evaluation is a ring homomorphism defined on the product group
algebra and intertwines coefficient conjugation with index reversal.
-/

noncomputable section

namespace CirculantHadamard.BinaryBlocks

open CyclicRing
open scoped BigOperators

section Evaluation

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] (m : ℕ)

variable [NeZero m]

/-- The four coefficients are summed, with no loss of the second coordinate. -/
theorem partialEval_apply (φ : R →+* S) (z : S) (hz : z ^ 4 = 1)
    (f : ProductElem R m) (b : ZMod m) :
    (partialEval m φ z hz f).coeff b =
      ∑ j : ZMod 4, φ (f.coeff (j, b)) * z ^ j.val := by
  classical
  have hexp : f = ∑ a : ZMod 4 × ZMod m, AddMonoidAlgebra.single a (f.coeff a) := by
    simpa only [AddMonoidAlgebra.sum_coeff_single] using
      (Finsupp.sum_fintype f.coeff AddMonoidAlgebra.single
        (fun a => AddMonoidAlgebra.single_zero a))
  calc
    (partialEval m φ z hz f).coeff b =
        (partialEval m φ z hz (∑ a : ZMod 4 × ZMod m,
          AddMonoidAlgebra.single a (f.coeff a))).coeff b :=
            congrArg (fun g => (partialEval m φ z hz g).coeff b) hexp
    _ = ∑ a : ZMod 4 × ZMod m,
        (AddMonoidAlgebra.single a.2 (φ (f.coeff a) * z ^ a.1.val)).coeff b := by
      rw [map_sum]
      simp only [partialEval_single, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

end Evaluation

section Star

variable {R : Type uR} {S : Type uS} [CommRing R] [StarRing R] [CommRing S] [StarRing S]
variable (m : ℕ) [NeZero m]

end Star

end CirculantHadamard.BinaryBlocks

end

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard OAI.CirculantHadamard.BinaryBlocks
open CyclicRing
open scoped BigOperators


theorem solution.{uR,uS} : type_of% @_root_.OAI.CirculantHadamard.BinaryBlocks.partialEval_apply.{uR,uS} := @_root_.OAI.CirculantHadamard.BinaryBlocks.partialEval_apply.{uR,uS}
