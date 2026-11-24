-- Prove2me | solution 1 for GlobalTheory.Mem.PartialZeta.normSq_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:14:37.007148+00:00
-- url     : https://prove2.me/submissions/77d5bb7b-43c9-49ac-8966-8cf32ed3ec8e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeEpsteinZetaContinuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassPartialZetaContinuation
import Theorems.Thm_GlobalTheory_Mem_PartialZeta_place_unique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.PartialZeta
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Mem.PartialZeta
theorem _root_.solution [IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) (φ : K →+* ℂ) (x : 𝓞 K) :
    ‖φ (x : K)‖ ^ 2 = (Ideal.absNorm (Ideal.span {x}) : ℝ) := by
  haveI : Subsingleton (InfinitePlace K) := ⟨place_unique h2⟩
  have hprod := InfinitePlace.prod_eq_abs_norm (x : K)
  rw [Fintype.prod_subsingleton _ (InfinitePlace.mk φ), InfinitePlace.apply,
    InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.2
      (IsTotallyComplex.isComplex _))] at hprod
  rw [hprod, Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs,
    ← Algebra.coe_norm_int]
  norm_cast
end GlobalTheory.Mem.PartialZeta
