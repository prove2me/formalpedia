-- Prove2me | solution 1 for GlobalTheory.CongTrans.series_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:29:08.72504+00:00
-- url     : https://prove2.me/submissions/20497b47-9ab0-4b53-b120-9df487594f6a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruentOneMatricesTransitiveNearHermitian
import Theorems.Thm_GlobalTheory_CongTrans_isAdicComplete_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.CongTrans
open GlobalTheory.UnramOrder
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable [IsNonarchimedeanLocalField F]
namespace GlobalTheory.CongTrans
theorem _root_.solution {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (a : ℕ → 𝒪[F]) :
    ∃ l : 𝒪[F], ∀ n, ∃ w, l = ∑ k ∈ Finset.range n, ϖ ^ k * a k + ϖ ^ n * w := by
  have hc := isAdicComplete_int (F := F)
  rw [hϖ.maximalIdeal_eq] at hc
  have key : ∀ (n : ℕ) (x y : 𝒪[F]),
      x ≡ y [SMOD (Ideal.span {ϖ} ^ n • ⊤ : Submodule 𝒪[F] 𝒪[F])] ↔ ϖ ^ n ∣ x - y := by
    intro n x y
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  obtain ⟨l, hl⟩ := hc.toIsPrecomplete.prec (f := fun n => ∑ k ∈ Finset.range n, ϖ ^ k * a k) (by
    intro m n hmn
    rw [key, ← dvd_neg, neg_sub, ← Finset.sum_Ico_eq_sub _ hmn]
    exact Finset.dvd_sum fun k hk =>
      (pow_dvd_pow _ (Finset.mem_Ico.1 hk).1).mul_right _)
  refine ⟨l, fun n => ?_⟩
  obtain ⟨w, hw⟩ := (key _ _ _).1 (hl n)
  exact ⟨-w, by linear_combination -hw⟩
end GlobalTheory.CongTrans
